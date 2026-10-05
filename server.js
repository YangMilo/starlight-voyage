// 사계절 행성 — 멀티 서버
// 게임 파일(public/index.html)을 보여 주고, WebSocket(/ws)으로 방마다 각자 상태를 주고받게 해 줍니다.
// 로그인 없음: 닉네임과 방 코드만으로 들어옵니다. 방은 메모리에만 있고, 비면 30분 뒤 사라집니다.
// 방 세계(집 · 텐트 · 밭 · 모닥불)도 방마다 서버가 들고 있다가 모두에게 나눠 줍니다.
// 방을 만든 사람 기기에도 저장되어서, 서버가 새로 켜지면 그 사람이 다시 올려 줍니다.
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = Number(process.env.PORT) || 3000;
const LIMITS = {
  rooms: 1000,          // 방 최대 개수
  perRoom: 8,           // 방 하나에 최대 인원
  connections: 600,     // 서버 전체 동시 접속
  presenceBytes: 4096,  // 한 사람 상태 최대 크기
  messageBytes: 16384,  // 메시지 하나 최대 크기
  emptyRoomMs: 30 * 60 * 1000,
};
const WORLD = { // 방 세계: 게임 쪽(WORLD_KINDS · CROPS)과 같은 규칙
  total: 60,
  kinds: ['house', 'tent', 'field', 'fire'], // 한 사람(pid)이 종류마다 하나씩
  cropSec: [60, 90, 120, 150], // 당근 · 토마토 · 옥수수 · 호박
  radius: 30,                  // 행성 반지름 (겹침 검사용)
};
const INDEX = fs.readFileSync(path.join(__dirname, 'public', 'index.html'));
const ALPHA = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; // 헷갈리는 글자(I, O, 0, 1) 뺌
const CODE_RE = /^[A-Z2-9]{4}$/;

// ── 웹 페이지 ──
const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/healthz') {
    res.writeHead(200, { 'content-type': 'text/plain; charset=utf-8' });
    res.end('ok');
    return;
  }
  if (url === '/' || url === '/index.html') {
    res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache' });
    res.end(INDEX);
    return;
  }
  res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' });
  res.end('없는 페이지예요');
});

// ── 방 ──
const rooms = new Map(); // code → { code, peers: Map(id → { ws, nick, p, pid, planet }), emptySince, worlds: Map(행성 → Map(id → item)), recreated, seeded: Set(행성), scares: Map('행성:동물' → 놀람) }
function newCode() {
  for (;;) {
    let c = '';
    for (let i = 0; i < 4; i++) c += ALPHA[crypto.randomInt(ALPHA.length)];
    if (!rooms.has(c)) return c;
  }
}
function makeRoom(code, fresh) {
  const r = { code, peers: new Map(), emptySince: 0, worlds: new Map(), recreated: !!fresh, seeded: new Set(), scares: new Map(), dinos: new Map(), devents: new Map() };
  rooms.set(code, r);
  return r;
}

// ── 방 세계 ──
const emptyCrop = () => ({ s: -1, t: 0, wt: 0 });
function cleanCrop(c) {
  if (!c || !Number.isInteger(c.s) || c.s < 0 || c.s >= WORLD.cropSec.length) return emptyCrop();
  return { s: c.s, t: Number(c.t) || 0, wt: Number(c.wt) || 0 };
}
function cleanItem(it) {
  if (!it || typeof it !== 'object' || !WORLD.kinds.includes(it.k) || typeof it.id !== 'string' || !/^[a-z0-9]{1,24}$/.test(it.id)) return null;
  if (!Array.isArray(it.d) || it.d.length !== 3 || !it.d.every(Number.isFinite)) return null;
  const len = Math.hypot(it.d[0], it.d[1], it.d[2]);
  if (len < 0.7 || len > 1.3) return null;
  const out = {
    id: it.id, k: it.k, d: it.d.map((v) => Math.round((v / len) * 1e5) / 1e5),
    r: Number.isFinite(it.r) ? Math.round((it.r % (Math.PI * 8)) * 1000) / 1000 : 0,
    c: Math.min(7, Math.max(0, it.c | 0)), t: Number(it.t) || 0,
    own: typeof it.own === 'string' && /^[a-z0-9]{1,24}$/.test(it.own) ? it.own : '', nick: cleanNick(it.nick), // 지은 사람
  };
  if (it.k === 'field') out.crops = Array.from({ length: 6 }, (_, i) => cleanCrop(Array.isArray(it.crops) ? it.crops[i] : null));
  return out;
}
const countKind = (w, pid, k) => { let n = 0; for (const it of w.values()) if (it.own === pid && it.k === k) n++; return n; };
const kindLimit = (planet, k) => (planet === 'dino' && k === 'fire' ? 6 : 1); // 공룡 행성 모닥불은 6개까지
const PLANET_R = { seasons: 30, city: 150, dino: 300 }; // 행성 반지름 (같은 자리 거절을 m로)
function putItem(w, it) {
  if (!it || w.has(it.id) || w.size >= WORLD.total) return false;
  w.set(it.id, it);
  return true;
}
const PLANET_RE = /^[a-z]{2,12}$/;
const planetOf = (m) => (typeof m.planet === 'string' && PLANET_RE.test(m.planet) ? m.planet : 'seasons'); // 별빛 항해: 같은 방, 행성마다 다른 세계
function worldOf(r, planet) { if (!r.worlds.has(planet)) r.worlds.set(planet, new Map()); return r.worlds.get(planet); }
function loadWorld(w, items) {
  for (const it of Array.isArray(items) ? items.slice(0, WORLD.total) : []) putItem(w, cleanItem(it));
}
function progress(c, now) { // 물을 준 뒤로는 두 배 빨리
  if (!c || c.s < 0) return -1;
  return ((c.wt ? c.wt - c.t + 2 * (now - c.wt) : now - c.t) / 1000) / WORLD.cropSec[c.s];
}
function worldAct(r, m, by, now, who) { // 성공하면 모두에게 보낼 op, 아니면 null (who = { pid, nick })
  const w = worldOf(r, who.planet);
  if (m.o === 'place') {
    if (!who.pid || countKind(w, who.pid, m.k) >= kindLimit(who.planet, m.k)) return null; // 한 사람이 종류마다 하나씩 (공룡 행성 모닥불은 여럿)
    const it = cleanItem({ id: crypto.randomBytes(4).toString('hex'), k: m.k, d: m.d, r: m.r, c: m.c, t: now, own: who.pid, nick: who.nick });
    if (!it) return null;
    for (const o of w.values()) { // 한가운데가 거의 같은 자리면 거절 (자세한 검사는 게임 쪽에서)
      const dx = o.d[0] - it.d[0], dy = o.d[1] - it.d[1], dz = o.d[2] - it.d[2];
      if (Math.hypot(dx, dy, dz) * (PLANET_R[who.planet] || WORLD.radius) < 1.5) return null;
    }
    if (it.k === 'field') it.crops = Array.from({ length: 6 }, emptyCrop);
    return putItem(w, it) ? { o: 'place', item: it } : null;
  }
  const e = typeof m.id === 'string' ? w.get(m.id) : null;
  if (!e) return null;
  if (m.o === 'remove') { if (!who.pid || (e.own && e.own !== who.pid)) return null; w.delete(e.id); return { o: 'remove', id: e.id }; } // 지은 사람만 (15단계에 지은 주인 없는 것은 누구나)
  if (e.k !== 'field') return null;
  const slot = m.slot | 0;
  if (slot < 0 || slot > 5) return null;
  const c = e.crops[slot];
  if (m.o === 'plant') {
    const s = m.s | 0;
    if (c.s >= 0 || s < 0 || s >= WORLD.cropSec.length) return null;
    e.crops[slot] = { s, t: now, wt: 0 };
    return { o: 'crop', id: e.id, slot, crop: e.crops[slot], by, why: 'plant' }; // 심은 사람이 씨앗을 씀
  }
  if (m.o === 'water') {
    if (c.s < 0 || c.wt || progress(c, now) >= 1) return null;
    c.wt = now;
    return { o: 'crop', id: e.id, slot, crop: c, by, why: 'water' };
  }
  if (m.o === 'harvest') {
    if (c.s < 0 || progress(c, now) < 0.97) return null; // 시계가 조금 달라도 괜찮게
    e.crops[slot] = emptyCrop();
    return { o: 'harvest', id: e.id, slot, s: c.s, by };
  }
  return null;
}
const cleanNick = (s) => String(s || '')
  .replace(/[\u0000-\u001f\u007f-\u009f\u00ad\u200b-\u200f\u2028-\u202e\u2060-\u206f\ufeff]/g, '')
  .replace(/\s+/g, ' ').trim().slice(0, 12);
function send(ws, msg) {
  if (ws.readyState === 1) ws.send(JSON.stringify(msg));
}
function broadcast(room, msg, exceptId, planet) { // planet을 주면 그 행성에 있는 사람에게만
  const text = JSON.stringify(msg);
  for (const [id, peer] of room.peers) if (id !== exceptId && peer.ws.readyState === 1 && (!planet || peer.planet === planet)) peer.ws.send(text);
}

const wss = new WebSocketServer({ server, path: '/ws', maxPayload: LIMITS.messageBytes });
wss.on('connection', (ws) => {
  if (wss.clients.size > LIMITS.connections) {
    send(ws, { t: 'error', code: 'busy' });
    ws.close();
    return;
  }
  let room = null, id = null;
  let budget = 40, lastAt = Date.now(); // 초당 30개쯤까지 (잠깐 몰리면 40개)
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });

  function leave() {
    if (!room) return;
    room.peers.delete(id);
    broadcast(room, { t: 'left', id });
    if (room.peers.size === 0) room.emptySince = Date.now();
    room = null;
    id = null;
  }

  let vBudget = 60, vLast = Date.now();
  ws.on('message', (buf, isBinary) => {
    if (isBinary) { // 마이크 목소리: 같은 방 · 같은 행성 친구에게 그대로 전함 (서버는 듣지 않고 전달만, 따로 세는 한도)
      const t2 = Date.now();
      vBudget = Math.min(60, vBudget + (t2 - vLast) * 0.06);
      vLast = t2;
      if (vBudget < 1 || !room || !Buffer.isBuffer(buf) || buf.length < 4 || buf.length > 2000 || buf[0] !== 1) return;
      vBudget -= 1;
      const meP = room.peers.get(id);
      if (!meP) return;
      const idb = Buffer.from(String(id)), out = Buffer.allocUnsafe(2 + idb.length + buf.length - 1);
      out[0] = 2; out[1] = idb.length; idb.copy(out, 2); buf.copy(out, 2 + idb.length, 1);
      for (const [pid, p] of room.peers) if (pid !== id && p.planet === meP.planet && p.ws.readyState === 1) p.ws.send(out, { binary: true });
      return;
    }
    const now = Date.now();
    budget = Math.min(40, budget + (now - lastAt) * 0.03);
    lastAt = now;
    if (budget < 1) return;
    budget -= 1;
    let m;
    try { m = JSON.parse(buf); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;

    if (m.t === 'create' || m.t === 'join') {
      leave();
      const nick = cleanNick(m.nick) || '친구';
      const asked = String(m.room || '').toUpperCase();
      let r;
      if (m.t === 'create') {
        if (rooms.size >= LIMITS.rooms) return send(ws, { t: 'error', code: 'busy' });
        r = makeRoom(newCode(), false);
        loadWorld(worldOf(r, planetOf(m)), m.world); // 방을 만든 사람의 (그 행성) 세계로 시작
      } else {
        if (!CODE_RE.test(asked)) return send(ws, { t: 'error', code: 'no_room' });
        r = rooms.get(asked);
        // 다시 잇기(recreate): 서버가 새로 켜져 방이 사라졌으면 같은 코드로 다시 만듦
        if (!r && m.recreate === true && rooms.size < LIMITS.rooms) r = makeRoom(asked, true); // 세계는 방 주인이 다시 올려 줌
        if (!r) return send(ws, { t: 'error', code: 'no_room' });
      }
      if (r.peers.size >= LIMITS.perRoom) return send(ws, { t: 'error', code: 'full' });
      const cid = typeof m.cid === 'string' && /^[a-z0-9]{10}$/.test(m.cid) && !r.peers.has(m.cid) ? m.cid : crypto.randomBytes(5).toString('hex');
      id = cid;
      room = r;
      r.emptySince = 0;
      const planet = planetOf(m);
      r.peers.set(id, { ws, nick, p: {}, pid: typeof m.pid === 'string' && /^[a-z0-9]{10}$/.test(m.pid) ? m.pid : '', planet });
      for (const [a, sc] of r.scares) if (now - sc.at > 30000) r.scares.delete(a);
      send(ws, {
        t: 'joined', room: r.code, you: id, nick,
        peers: [...r.peers].filter(([pid]) => pid !== id).map(([pid, q]) => ({ id: pid, nick: q.nick, p: q.p })),
        world: [...worldOf(r, planet).values()], now, fresh: r.recreated && !r.seeded.has(planet), planet,
        scares: [...r.scares.values()].filter((x) => x.planet === planet).map(({ a, f, at }) => ({ a, f, at })),
        dinos: [...r.dinos.values()].filter((x) => x.planet === planet && (!x.dead || now < x.respawnAt)).map(({ d, hp, dead, respawnAt }) => ({ d, hp, dead, respawnAt })),
        devents: [...r.devents.values()].filter((x) => x.planet === planet && now - x.at < 25000).map(({ d, k, f, tgt, at }) => ({ d, k, f, tgt, at })),
      });
      broadcast(r, { t: 'peer', id, nick, p: {} }, id);
    } else if (m.t === 'presence' && room) {
      const p = m.p;
      if (!p || typeof p !== 'object' || Array.isArray(p)) return;
      if (Buffer.byteLength(JSON.stringify(p)) > LIMITS.presenceBytes) return;
      room.peers.get(id).p = p;
      broadcast(room, { t: 'presence', id, p }, id);
    } else if (m.t === 'act' && room) {
      const me = room.peers.get(id);
      const op = worldAct(room, m, id, now, { pid: me.pid, nick: me.nick, planet: me.planet });
      if (op) broadcast(room, { t: 'world', op, now }, undefined, me.planet); // 같은 행성에 있는 사람 모두에게 (보낸 사람까지)
    } else if (m.t === 'rtc' && room) { // 마이크: 브라우저끼리 직접 잇기 위한 소식만 그 친구에게 (목소리는 서버를 거치지 않음)
      const to = typeof m.to === 'string' ? room.peers.get(m.to) : null;
      if (!to || to.ws.readyState !== 1 || m.to === id) return;
      const out = { t: 'rtc', from: id };
      if (m.desc && typeof m.desc === 'object' && ['offer', 'answer', 'rollback'].includes(m.desc.type) && typeof (m.desc.sdp || '') === 'string' && (m.desc.sdp || '').length < 15000) out.desc = { type: m.desc.type, sdp: m.desc.sdp || '' };
      else if (m.cand && typeof m.cand === 'object' && typeof m.cand.candidate === 'string' && m.cand.candidate.length < 1000) out.cand = { candidate: m.cand.candidate, sdpMid: typeof m.cand.sdpMid === 'string' ? m.cand.sdpMid.slice(0, 32) : null, sdpMLineIndex: Number.isInteger(m.cand.sdpMLineIndex) ? m.cand.sdpMLineIndex : null };
      else return;
      to.ws.send(JSON.stringify(out));
    } else if (m.t === 'scare' && room) { // 누가 동물을 놀라게 함 → 서버 시각을 붙여 모두에게 (늦게 온 친구도 같은 길로)
      if (!Number.isInteger(m.a) || m.a < 0 || m.a > 999 || !Array.isArray(m.f) || m.f.length !== 3 || !m.f.every(Number.isFinite)) return;
      const pl = room.peers.get(id).planet, key = `${pl}:${m.a}`;
      const old = room.scares.get(key);
      if (old && now - old.at < 1500) return; // 여럿이 동시에 다가가도 한 번만
      const sc = { a: m.a, f: m.f.map((v) => Math.round(v * 1e4) / 1e4), at: now };
      room.scares.set(key, { ...sc, planet: pl });
      for (const [a, x] of room.scares) if (now - x.at > 30000) room.scares.delete(a);
      broadcast(room, { t: 'scare', ...sc }, undefined, pl);
    } else if (m.t === 'krace' && room) { // 도시: 친구 대결 열기 → 7초 뒤 같은 시각에 출발
      if (!Number.isInteger(m.c) || m.c < 0 || m.c > 9) return;
      const pl = room.peers.get(id).planet;
      broadcast(room, { t: 'krace', c: m.c, at: now + 7000, by: id, rt: m.rt === 'item' ? 'item' : 'speed' }, undefined, pl); // 스피드전 · 아이템전
    } else if (m.t === 'lobby' && room) { // 함께 놀기 대기실 (레이스 · 공중전): 같은 행성 모두에게 (시작 시각은 서버가)
      if (!['state', 'join', 'ready', 'leave', 'start', 'cancel'].includes(m.k) || typeof m.id !== 'string' || !/^[a-z0-9]{4,16}$/.test(m.id)) return;
      const out = { t: 'lobby', k: m.k, id: m.id, by: id };
      if (m.k === 'state') { if (!['race', 'df'].includes(m.g) || !Array.isArray(m.m) || m.m.length > 8) return; out.g = m.g; out.c = Math.max(0, Math.min(9, m.c | 0)); out.rt = m.rt === 'item' ? 'item' : 'speed'; out.m = m.m.filter((x) => Array.isArray(x) && typeof x[0] === 'string' && x[0].length <= 24).map((x) => [x[0], !!x[1]]); }
      if (m.k === 'ready') out.v = !!m.v;
      if (m.k === 'start') out.at = now + 3500;
      broadcast(room, out, undefined, room.peers.get(id).planet);
    } else if (m.t === 'df' && room) { // 공중전: 맞힘 · 체력 · 격추 · 미사일
      if (!['hit', 'hp', 'down', 'shot', 'boom'].includes(m.k) || typeof m.r !== 'string' || m.r.length > 16) return;
      const vec = (a) => (Array.isArray(a) && a.length === 3 && a.every(Number.isFinite) ? a.map((v) => Math.round(v * 1e3) / 1e3) : null);
      const out = { t: 'df', k: m.k, r: m.r, by: id };
      if (typeof m.tgt === 'string' && m.tgt.length <= 24) out.tgt = m.tgt;
      if (m.k === 'hit') out.dmg = Math.max(1, Math.min(40, m.dmg | 0));
      if (m.k === 'hp') out.v = Math.max(0, Math.min(100, m.v | 0));
      if (m.k === 'shot' || m.k === 'boom') { if (typeof m.id !== 'string' || !/^[a-z0-9]{4,16}$/.test(m.id)) return; out.id = m.id; }
      if (m.k === 'shot') { out.p = vec(m.p); out.f = vec(m.f); if (!out.p || !out.f) return; }
      broadcast(room, out, undefined, room.peers.get(id).planet);
    } else if (m.t === 'kitem' && room) { // 카트 아이템전: 지뢰 · 미사일 · 유도 미사일 · 터짐을 같은 행성에 (맞았는지는 맞은 사람이 정함)
      if (!['mine', 'missile', 'homing', 'boom'].includes(m.k) || typeof m.id !== 'string' || !/^[a-z0-9]{4,16}$/.test(m.id) || !Number.isFinite(m.r)) return;
      const vec = (a) => (Array.isArray(a) && a.length === 3 && a.every(Number.isFinite) ? a.map((v) => Math.round(v * 1e5) / 1e5) : null);
      const out = { t: 'kitem', k: m.k, id: m.id, r: m.r, by: id, at: now };
      if (m.k !== 'boom') { out.p = vec(m.p); out.f = vec(m.f); if (!out.p || !out.f) return; if (typeof m.tgt === 'string' && m.tgt.length <= 24) out.tgt = m.tgt; }
      broadcast(room, out, undefined, room.peers.get(id).planet);
    } else if ((m.t === 'kjoin' || m.t === 'kfin') && room) { // 참가 · 결승 기록을 같은 행성 모두에게
      if (!Number.isFinite(m.at) || (m.t === 'kfin' && (!Number.isFinite(m.ms) || m.ms <= 0 || m.ms > 3600000))) return;
      const pl = room.peers.get(id).planet;
      broadcast(room, m.t === 'kfin' ? { t: 'kfin', at: m.at, ms: Math.round(m.ms), id } : { t: 'kjoin', at: m.at, id }, undefined, pl);
    } else if (m.t === 'dhit' && room) { // 공룡 행성: 공룡을 때림 → 서버가 체력을 들고 같은 행성 모두에게 (함께 사냥)
      if (!Number.isInteger(m.d) || m.d < 0 || m.d > 999 || !Number.isFinite(m.dmg) || !Number.isFinite(m.max)) return;
      const pl = room.peers.get(id).planet, key = `${pl}:${m.d}`;
      let e = room.dinos.get(key);
      if (e && e.dead && now >= e.respawnAt) { room.dinos.delete(key); e = null; }
      if (!e) { const max = Math.min(999, Math.max(1, m.max | 0)); e = { d: m.d, hp: max, max, dead: false, respawnAt: 0, planet: pl, hit: new Map() }; room.dinos.set(key, e); }
      if (e.dead) return;
      let dmg = m.kill === 1 ? e.hp : Math.min(40, Math.max(1, m.dmg | 0)), wake = false, coop = false; // kill: 육식 공룡이 초식 공룡을 잡아먹음
      if (e.wakeAt && now - e.wakeAt > 60000) e.wakeAt = 0; // 다음 밤엔 다시 기습할 수 있음
      if (m.asleep && !e.wakeAt) { e.wakeAt = now; e.coop = [id]; wake = true; } // 잠든 공룡 기습 → 4초 비틀거림
      else if (e.wakeAt && now - e.wakeAt < 3000 && !e.coop.includes(id)) { e.coop.push(id); dmg = Math.min(80, dmg * 2); coop = true; } // 3초 안에 다른 친구가 치면 협동 일격 (두 배)
      if (m.kill !== 1) { if (!e.hit) e.hit = new Map(); e.hit.set(id, now); } // 때린 사람 (함께 잡은 사람 = 쓰러지기 60초 안에 때린 사람)
      e.hp = Math.max(0, e.hp - dmg);
      if (e.hp <= 0) { e.dead = true; e.respawnAt = now + (e.max >= 50 ? 600000 : 240000); } // 4분 뒤 다시 나타남 (티라노사우루스 같은 보스는 10분)
      const hitters = e.dead && e.hit ? [...e.hit].filter(([, t]) => now - t < 60000).map(([k]) => k) : undefined;
      if (e.dead && e.hit) e.hit.clear();
      broadcast(room, { t: 'dino', d: e.d, hp: e.hp, dead: e.dead, respawnAt: e.respawnAt, by: id, wake, coop, hitters }, undefined, pl);
    } else if (m.t === 'revive' && room) { // 공룡 행성: 쓰러진 친구 일으키기
      if (typeof m.to !== 'string' || m.to.length > 24) return;
      broadcast(room, { t: 'revive', to: m.to, by: id }, undefined, room.peers.get(id).planet);
    } else if (m.t === 'devent' && room) { // 공룡이 쫓기 · 달아나기 시작 (서버 시각을 붙여 같은 행성 모두에게)
      if (!Number.isInteger(m.d) || m.d < 0 || m.d > 999 || !['chase', 'flee', 'hunt'].includes(m.k) || !Array.isArray(m.f) || m.f.length !== 3 || !m.f.every(Number.isFinite) || typeof m.tgt !== 'string' || m.tgt.length > 24) return;
      const pl = room.peers.get(id).planet, key = `${pl}:${m.d}`;
      const old = room.devents.get(key);
      if (old && now - old.at < 1500) return;
      const ev = { d: m.d, k: m.k, f: m.f.map((v) => Math.round(v * 1e4) / 1e4), tgt: m.tgt, at: now, planet: pl };
      room.devents.set(key, ev);
      for (const [k2, x] of room.devents) if (now - x.at > 30000) room.devents.delete(k2);
      broadcast(room, { t: 'devent', d: ev.d, k: ev.k, f: ev.f, tgt: ev.tgt, at: ev.at }, undefined, pl);
    } else if (m.t === 'seed' && room) {
      const pl = room.peers.get(id).planet;
      if (!room.recreated || room.seeded.has(pl)) return; // 서버가 새로 켜진 방에 행성마다 한 번만 (먼저 온 친구가 지은 것과 합침)
      const w = worldOf(room, pl);
      loadWorld(w, m.items);
      room.seeded.add(pl);
      broadcast(room, { t: 'world', op: { o: 'reset', items: [...w.values()] }, now }, undefined, pl);
    } else if (m.t === 'leave') {
      leave();
    }
  });
  ws.on('close', leave);
  ws.on('error', () => {});
});

// 끊긴 연결 정리(25초마다 확인) + 오래 빈 방 지우기
setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.isAlive) { ws.terminate(); continue; }
    ws.isAlive = false;
    ws.ping();
  }
  const now = Date.now();
  for (const [code, r] of rooms) if (r.peers.size === 0 && r.emptySince && now - r.emptySince > LIMITS.emptyRoomMs) rooms.delete(code);
}, 25000).unref();

server.listen(PORT, () => console.log(`별빛 항해 서버가 켜졌어요: http://localhost:${PORT}`));
