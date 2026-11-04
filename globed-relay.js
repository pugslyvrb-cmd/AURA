#!/usr/bin/env node
/*
 * Globed Web relay: a tiny multiplayer room server for the web Geometry Dash port.
 * No dependencies. Needs Node 16+.
 *
 *   node globed-relay.js                      # ws://localhost:4350
 *   PORT=8080 node globed-relay.js
 *   CERT=cert.pem KEY=key.pem node globed-relay.js    # wss:// directly
 *   ORIGINS=https://my-site.pages.dev node globed-relay.js   # only allow these web pages
 *
 * Hosted on Render/Railway etc.: the PORT it provides is used automatically, and the client IP is
 * read from the proxy's X-Forwarded-For header (set TRUST_PROXY=1 on other hosts behind a proxy).
 *
 * Pages served over https can only connect to wss:// (or ws://localhost). Put the server behind
 * a TLS tunnel/reverse proxy (cloudflared, Caddy, nginx) or pass CERT/KEY.
 *
 * This is NOT the real Globed server. It only speaks the small JSON protocol of the web mod.
 */
'use strict';
const http = require('http');
const https = require('https');
const fs = require('fs');
const crypto = require('crypto');

const PORT = parseInt(process.env.PORT || '4350', 10);
const HOST = process.env.HOST || '0.0.0.0';
const MAX_ROOM = parseInt(process.env.MAX_ROOM || '50', 10);
const MAX_ROOMS = parseInt(process.env.MAX_ROOMS || '500', 10);
const MAX_PER_IP = parseInt(process.env.MAX_PER_IP || '8', 10);
const MAX_PAYLOAD = 4096;                 // bytes per message
const RATE = 80, BURST = 160;             // messages per second sustained / burst
const CHAT_GAP_MS = 700;                  // minimum time between chat messages
const TRUST_PROXY = !!(process.env.TRUST_PROXY || process.env.RENDER);
const ORIGINS = (process.env.ORIGINS || '').split(',').map(s => s.trim()).filter(Boolean);
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

const rooms = new Map();                  // name -> { name, pass, members: Map<id, client> }
let nextId = 1;
const perIp = new Map();
const clients = new Set();

/* ---------- minimal RFC 6455 ---------- */
function frame(op, payload) {
  const len = payload.length;
  let head;
  if (len < 126) head = Buffer.from([0x80 | op, len]);
  else if (len < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | op; head[1] = 126; head.writeUInt16BE(len, 2); }
  else { head = Buffer.alloc(10); head[0] = 0x80 | op; head[1] = 127; head.writeBigUInt64BE(BigInt(len), 2); }
  return Buffer.concat([head, payload]);
}

class Client {
  constructor(sock, ip) {
    this.sock = sock; this.ip = ip; this.id = nextId++;
    this.buf = Buffer.alloc(0); this.frag = null; this.fragOp = 0;
    this.alive = true; this.closed = false;
    this.room = null; this.name = 'player' + this.id; this.icon = 0;
    this.tokens = BURST; this.lastRefill = Date.now(); this.lastChat = 0;
    this.state = null;
    sock.on('data', d => this.onData(d));
    sock.on('close', () => this.cleanup());
    sock.on('error', () => this.cleanup());
    sock.setNoDelay(true);
    clients.add(this);
    this.joinTimer = setTimeout(() => { if (!this.room) this.close(1008, 'join timeout'); }, 15000);
  }
  sendRaw(buf) { if (!this.closed && this.sock.writable) { try { this.sock.write(buf); } catch (e) { /* closing */ } } }
  send(obj) { this.sendRaw(frame(0x1, Buffer.from(JSON.stringify(obj)))); }
  close(code, reason) {
    if (this.closed) return;
    const r = Buffer.from(String(reason || '').slice(0, 100));
    const p = Buffer.alloc(2 + r.length); p.writeUInt16BE(code || 1000, 0); r.copy(p, 2);
    this.sendRaw(frame(0x8, p));
    this.cleanup();
    try { this.sock.end(); } catch (e) { /* ignore */ }
    setTimeout(() => { try { this.sock.destroy(); } catch (e) { /* ignore */ } }, 1000).unref();
  }
  cleanup() {
    if (this.closed) return;
    this.closed = true;
    clients.delete(this); clearTimeout(this.joinTimer);
    leaveRoom(this);
    const n = (perIp.get(this.ip) || 1) - 1;
    if (n <= 0) perIp.delete(this.ip); else perIp.set(this.ip, n);
  }
  onData(d) {
    if (this.closed) return;
    this.buf = this.buf.length ? Buffer.concat([this.buf, d]) : d;
    for (;;) {
      const b = this.buf;
      if (b.length < 2) return;
      const fin = (b[0] & 0x80) !== 0, rsv = b[0] & 0x70, op = b[0] & 0x0f, masked = (b[1] & 0x80) !== 0;
      let len = b[1] & 0x7f, off = 2;
      if (rsv || !masked) return this.close(1002, 'protocol error');
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
      else if (len === 127) {
        if (b.length < 10) return;
        const big = b.readBigUInt64BE(2);
        if (big > BigInt(MAX_PAYLOAD)) return this.close(1009, 'message too big');
        len = Number(big); off = 10;
      }
      if (len > MAX_PAYLOAD) return this.close(1009, 'message too big');
      if (b.length < off + 4 + len) return;
      const mask = b.subarray(off, off + 4), payload = Buffer.from(b.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i & 3];
      this.buf = b.subarray(off + 4 + len);
      if (op >= 0x8) {                                   // control frames
        if (!fin || len > 125) return this.close(1002, 'bad control frame');
        if (op === 0x8) return this.close(1000, '');
        if (op === 0x9) this.sendRaw(frame(0xA, payload));
        if (op === 0xA) this.alive = true;
        continue;
      }
      if (op === 0x0) {                                  // continuation
        if (!this.frag) return this.close(1002, 'unexpected continuation');
        this.frag.push(payload);
        if (this.frag.reduce((n, x) => n + x.length, 0) > MAX_PAYLOAD) return this.close(1009, 'message too big');
        if (!fin) continue;
        const whole = Buffer.concat(this.frag); this.frag = null;
        if (this.fragOp === 0x1) this.onMessage(whole.toString('utf8'));
        continue;
      }
      if (op !== 0x1 && op !== 0x2) return this.close(1003, 'unsupported');
      if (!fin) { this.frag = [payload]; this.fragOp = op; continue; }
      if (op === 0x1) this.onMessage(payload.toString('utf8'));
    }
  }
  onMessage(text) {
    const now = Date.now();
    this.tokens = Math.min(BURST, this.tokens + (now - this.lastRefill) * RATE / 1000); this.lastRefill = now;
    if (--this.tokens < 0) return;                       // drop floods silently
    let m; try { m = JSON.parse(text); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    handle(this, m);
  }
}

/* ---------- room logic ---------- */
const num = (v, lo, hi) => (typeof v === 'number' && isFinite(v)) ? Math.max(lo, Math.min(hi, v)) : null;
const clean = (s, n) => String(s == null ? '' : s).replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, n);
const hashPass = p => p ? crypto.createHash('sha256').update('globed-web:' + p).digest('hex') : '';
const pub = c => ({ id: c.id, name: c.name, icon: c.icon, s: c.state });

function leaveRoom(c) {
  const r = c.room; if (!r) return;
  c.room = null; r.members.delete(c.id);
  if (!r.members.size) rooms.delete(r.name);
  else broadcast(r, { t: 'leave', id: c.id }, null);
}
function broadcast(room, obj, except) {
  const buf = frame(0x1, Buffer.from(JSON.stringify(obj)));
  for (const m of room.members.values()) if (m !== except) m.sendRaw(buf);
}
function handle(c, m) {
  switch (m.t) {
    case 'join': {
      const name = clean(m.name, 20) || c.name, roomName = clean(m.room, 32).toLowerCase() || 'lobby';
      const pass = typeof m.pass === 'string' ? m.pass.slice(0, 64) : '';
      leaveRoom(c);
      let r = rooms.get(roomName);
      if (!r) {
        if (rooms.size >= MAX_ROOMS) return c.send({ t: 'err', m: 'The server has too many rooms right now.' });
        r = { name: roomName, pass: hashPass(pass), members: new Map() }; rooms.set(roomName, r);
      } else if (r.pass !== hashPass(pass)) return c.send({ t: 'err', m: 'Wrong room password.', code: 'pass' });
      if (r.members.size >= MAX_ROOM) return c.send({ t: 'err', m: 'That room is full.', code: 'full' });
      c.name = name; c.icon = num(m.icon, 0, 9999) | 0; c.state = null; c.room = r;
      c.send({ t: 'welcome', id: c.id, room: r.name, locked: !!r.pass, players: [...r.members.values()].map(pub) });
      r.members.set(c.id, c);
      broadcast(r, { t: 'join', p: pub(c) }, c);
      break;
    }
    case 's': {                                          // position / progress update
      const r = c.room; if (!r) return;
      const x = m.x, y = m.y, ok = v => typeof v === 'number' && isFinite(v) && Math.abs(v) <= 1e7;
      if (!ok(x) || !ok(y)) return;
      c.state = { x, y, r: num(m.r, -3600, 3600) || 0, p: num(m.p, 0, 100) || 0, d: m.d ? 1 : 0, l: clean(m.l, 40) };
      broadcast(r, { t: 's', id: c.id, s: c.state }, c);
      break;
    }
    case 'chat': {
      const r = c.room; if (!r) return;
      const now = Date.now(); if (now - c.lastChat < CHAT_GAP_MS) return; c.lastChat = now;
      const text = clean(m.m, 200); if (!text) return;
      broadcast(r, { t: 'chat', id: c.id, name: c.name, m: text }, null);
      break;
    }
    case 'ping': c.send({ t: 'pong', n: m.n }); break;
    default: break;
  }
}

/* ---------- http + upgrade ---------- */
const handler = (req, res) => {
  if (req.url === '/health') { res.writeHead(200, { 'content-type': 'application/json' }); return res.end(JSON.stringify({ ok: true, rooms: rooms.size })); }
  res.writeHead(426, { 'content-type': 'text/plain' }); res.end('Globed Web relay. Connect with a WebSocket.\n');
};
const server = process.env.CERT && process.env.KEY
  ? https.createServer({ cert: fs.readFileSync(process.env.CERT), key: fs.readFileSync(process.env.KEY) }, handler)
  : http.createServer(handler);

server.on('upgrade', (req, sock) => {
  const xff = String(req.headers['x-forwarded-for'] || '').split(',');
  /* behind a host's proxy (Render sets RENDER) every socket comes from the proxy, so use the client address it appends */
  const ip = (TRUST_PROXY ? xff[xff.length - 1].trim() : '') || req.socket.remoteAddress || '?';
  const key = req.headers['sec-websocket-key'], origin = req.headers.origin;
  const refuse = (code, msg) => { try { sock.end('HTTP/1.1 ' + code + ' ' + msg + '\r\nConnection: close\r\n\r\n'); } catch (e) { /* ignore */ } };
  if (String(req.headers.upgrade || '').toLowerCase() !== 'websocket' || !key || req.headers['sec-websocket-version'] !== '13') return refuse(400, 'Bad Request');
  if (ORIGINS.length && !ORIGINS.includes(origin)) return refuse(403, 'Forbidden');
  if ((perIp.get(ip) || 0) >= MAX_PER_IP) return refuse(429, 'Too Many Requests');
  perIp.set(ip, (perIp.get(ip) || 0) + 1);
  const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  const c = new Client(sock, ip);
  c.send({ t: 'hello', id: c.id, v: 1 });
});

const hb = setInterval(() => {                           // drop dead connections
  for (const c of [...clients]) {
    if (!c.alive) { c.close(1001, 'timeout'); continue; }
    c.alive = false; c.sendRaw(frame(0x9, Buffer.alloc(0)));
  }
}, 20000);
hb.unref();

if (require.main === module) {
  server.listen(PORT, HOST, () => console.log('Globed Web relay on ' + (process.env.CERT ? 'wss' : 'ws') + '://' + (HOST === '0.0.0.0' ? 'localhost' : HOST) + ':' + PORT));
}
module.exports = { server, rooms };
