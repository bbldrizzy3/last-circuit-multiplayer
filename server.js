"use strict";
const http = require("node:http");
const fs = require("node:fs");
const path = require("node:path");
const { randomBytes, randomUUID } = require("node:crypto");
const { WebSocketServer, WebSocket } = require("ws");

// ---- Big procedural map (41 x 31, was 21 x 13). Generated once when the server starts. ----
const MW = 41, MH = 31;
function build() {
 const g = Array.from({ length: MH }, () => Array(MW).fill(1));
 const st = [[1, 1]]; g[1][1] = 0;
 while (st.length) {
  const [x, y] = st[st.length - 1];
  const n = [[2, 0], [-2, 0], [0, 2], [0, -2]]
   .filter(([a, b]) => x + a > 0 && x + a < MW - 1 && y + b > 0 && y + b < MH - 1 && g[y + b][x + a] === 1)
   .sort(() => Math.random() - .5);
  if (!n.length) { st.pop(); continue; }
  const [a, b] = n[0]; g[y + b / 2][x + a / 2] = 0; g[y + b][x + a] = 0; st.push([x + a, y + b]);
 }
 // knock out some walls so there are loops to run around (no dead-end-only maze)
 for (let y = 1; y < MH - 1; y++) for (let x = 1; x < MW - 1; x++) {
  if (g[y][x] && (x + y) % 2 === 1 && Math.random() < .1) {
   if ((x % 2 === 0 && g[y][x - 1] === 0 && g[y][x + 1] === 0) || (y % 2 === 0 && g[y - 1][x] === 0 && g[y + 1][x] === 0)) g[y][x] = 0;
  }
 }
 return g.map(r => r.join(""));
}
const MAP = build();
const SPAWN = { x: 1.5, y: 1.5 };
const EXIT = { x: MW - 1.5, y: MH - 1.5 };
const rooms = new Map();
const tiles = [];
MAP.forEach((r, y) => [...r].forEach((v, x) => { if (v === "0") tiles.push({ x: x + .5, y: y + .5 }); }));
const distance = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
const wall = (x, y) => MAP[Math.floor(y)]?.[Math.floor(x)] !== "0";
function scatter(n, from, min, gap, used = []) {
 const out = [];
 for (let t = 0; t < 3000 && out.length < n; t++) {
  const c = tiles[Math.random() * tiles.length | 0];
  if (distance(c, from) >= min && [...out, ...used].every(o => distance(o, c) >= gap)) out.push({ x: c.x, y: c.y });
 }
 while (out.length < n) { const c = tiles[Math.random() * tiles.length | 0]; out.push({ x: c.x, y: c.y }); }
 return out;
}
function move(o, dx, dy) {
 const r = .18;
 if (!wall(o.x + dx + Math.sign(dx) * r, o.y - r) && !wall(o.x + dx + Math.sign(dx) * r, o.y + r)) o.x += dx;
 if (!wall(o.x - r, o.y + dy + Math.sign(dy) * r) && !wall(o.x + r, o.y + dy + Math.sign(dy) * r)) o.y += dy;
}
function visible(a, b) { const n = Math.ceil(distance(a, b) * 12); for (let i = 1; i < n; i++) if (wall(a.x + (b.x - a.x) * i / n, a.y + (b.y - a.y) * i / n)) return false; return true; }
function route(a, b) {
 const first = (a.x | 0) + "," + (a.y | 0), q = [[a.x | 0, a.y | 0]], prev = new Map([[first, null]]);
 for (let i = 0; i < q.length; i++) {
  const [x, y] = q[i], k = x + "," + y;
  if (x === (b.x | 0) && y === (b.y | 0)) {
   const result = []; let key = k;
   while (prev.get(key) !== null) { const [u, v] = key.split(",").map(Number); result.unshift({ x: u + .5, y: v + .5 }); key = prev.get(key); }
   return result;
  }
  for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) { const u = x + dx, v = y + dy, s = u + "," + v; if (!wall(u + .5, v + .5) && !prev.has(s)) { prev.set(s, k); q.push([u, v]); } }
 }
 return [];
}
function walk(o, speed, dt) { const target = o.path[0]; if (!target) return; const d = distance(o, target), step = speed * dt; if (d < step + .025) { o.x = target.x; o.y = target.y; o.path.shift(); } else move(o, (target.x - o.x) / d * step, (target.y - o.y) / d * step); }
function send(ws, data) { if (ws.readyState === WebSocket.OPEN && ws.bufferedAmount < 262144) ws.send(JSON.stringify(data)); }
function note(room, text) { room.message = text; room.messageUntil = room.time + 5; }
function collect(room, i, who) { room.cells.splice(i, 1); room.found++; for (const p of room.players.values()) p.battery = Math.min(100, p.battery + 35); note(room, who + " recovered a cell. " + (room.found === 3 ? "Exit powered. Regroup at the green door." : room.found + " / 3 secured.")); }
function reset(room) {
 room.time = 0; room.found = 0; room.follow = false; room.status = "playing";
 room.cells = scatter(3, SPAWN, 14, 12, [EXIT]);
 // Pickups lying around the maze
 room.items = []; const used = [...room.cells, EXIT]; let nid = 0;
 const place = (type, n) => { for (const q of scatter(n, SPAWN, 4, 3, used)) { used.push(q); room.items.push({ id: ++nid, type, x: q.x, y: q.y }); } };
 place("gun", 2); place("ammo", 8); place("medkit", 5); place("battery", 4); place("coin", 14);
 // TWO skinwalkers. #0 roams the whole maze, #1 lurks around the cells.
 room.monsters = scatter(2, SPAWN, 22, 14).map((p, i) => ({ i, x: p.x, y: p.y, path: [], timer: 0, alert: 0, cool: 0, hp: 3, stun: 0 }));
 room.bots = [{ id: "mara", name: "MARA", x: 1.3, y: 1.7, color: "#86c8dc", path: [], timer: 0, down: false, revive: 0 }, { id: "eli", name: "ELI", x: 1.7, y: 1.3, color: "#ddb57e", path: [], timer: 0, down: false, revive: 0 }];
 let i = 0; for (const p of room.players.values()) { Object.assign(p, { x: 1.5 + (i % 2) * .22, y: 1.5 + (i >> 1) * .22, a: 0, down: false, escaped: false, revive: 0, battery: 100, stamina: 100, light: true, input: {}, lastInput: 0, health: 100, ammo: 0, gun: false, coins: 0, medkits: 0, radar: 3, radarOn: false, lastShot: 0 }); i++; }
 note(room, "Find three cells together. Two skinwalkers are loose. Q orders the AI teammates.");
}
function snapshot(room) {
 return {
  type: "state", code: room.code, host: room.host, status: room.status, time: room.time, found: room.found, follow: room.follow, cells: room.cells, items: room.items, exit: EXIT,
  players: [...room.players.values()].map(p => ({ id: p.id, name: p.name, x: p.x, y: p.y, a: p.a, down: p.down, escaped: p.escaped, revive: p.revive, light: p.light, battery: p.battery, stamina: p.stamina, health: p.health, ammo: p.ammo, gun: p.gun, coins: p.coins, medkits: p.medkits, radar: p.radar, radarOn: p.radarOn })),
  bots: room.bots.map(b => ({ id: b.id, name: b.name, x: b.x, y: b.y, color: b.color, down: b.down, revive: b.revive, state: b.state || "WAITING" })),
  monsters: room.monsters.map((m, i) => ({ x: m.x, y: m.y, disguised: Math.sin(room.time * .45 + i * 2.1) > .2 })),
  message: room.time < room.messageUntil ? room.message : ""
 };
}
function leave(ws) { const room = rooms.get(ws.room); if (room) { room.players.delete(ws.id); if (!room.players.size) rooms.delete(room.code); else if (room.host === ws.id) room.host = room.players.keys().next().value; } ws.room = null; }
const server = http.createServer((req, res) => {
 const pathname = (req.url || "/").split("?")[0];
 if (pathname === "/health") { res.writeHead(200, { "Content-Type": "application/json" }); res.end(JSON.stringify({ ok: true, rooms: rooms.size })); return; }
 if (pathname !== "/" && pathname !== "/index.html") { res.writeHead(404); res.end("Not found"); return; }
 fs.readFile(path.join(__dirname, "index.html"), (err, data) => {
  res.writeHead(200, { "Content-Type": "text/html; charset=utf-8", "Cache-Control": "no-store", "X-Content-Type-Options": "nosniff", "Referrer-Policy": "no-referrer" });
  res.end(err ? "<!doctype html><title>The Last Circuit</title><h1>Server is running</h1><p>Upload the multiplayer index.html to finish setup. The old single-player HTML will not connect to this server.</p>" : data);
 });
});
const wss = new WebSocketServer({ server, path: "/ws", maxPayload: 4096, perMessageDeflate: false });
wss.on("connection", ws => {
 if (wss.clients.size > 100) { ws.close(1013, "Server full"); return; }
 ws.id = randomUUID(); ws.alive = true; ws.bucket = 0; ws.window = Date.now();
 ws.on("pong", () => ws.alive = true);
 send(ws, { type: "hello", id: ws.id });
 ws.on("message", raw => {
  const now = Date.now(); if (now - ws.window > 1000) { ws.window = now; ws.bucket = 0; } if (++ws.bucket > 80) { ws.close(1008, "Too many messages"); return; }
  let data; try { data = JSON.parse(raw.toString()); } catch { return; }
  if (!data || typeof data !== "object" || Array.isArray(data)) return;
  if (data.type === "create" || data.type === "join") {
   let room;
   if (data.type === "create") {
    if (rooms.size >= 30) { send(ws, { type: "error", message: "Server full. Try again later." }); return; }
    let code; do { code = randomBytes(4).toString("hex").slice(0, 6).toUpperCase(); } while (rooms.has(code));
    room = { code, host: ws.id, players: new Map() }; reset(room); room.status = "lobby"; rooms.set(code, room);
   } else {
    const code = typeof data.code === "string" ? data.code.trim().toUpperCase() : ""; room = rooms.get(code);
    if (!room) { send(ws, { type: "error", message: "Room not found. Check the code." }); return; }
    if (room.players.size >= 4) { send(ws, { type: "error", message: "Room is full (4 friends maximum)." }); return; }
    if (room.status !== "lobby") { send(ws, { type: "error", message: "Game already started. Ask the host to return to the lobby." }); return; }
   }
   leave(ws); ws.room = room.code;
   const name = (typeof data.name === "string" ? data.name : "Player").replace(/[\x00-\x1f\x7f]/g, "").trim().slice(0, 18) || "Player";
   room.players.set(ws.id, { id: ws.id, ws, name, x: 1.5, y: 1.5, a: 0, down: false, escaped: false, revive: 0, light: true, battery: 100, stamina: 100, input: {}, lastInput: 0, lastAction: 0, health: 100, ammo: 0, gun: false, coins: 0, medkits: 0, radar: 3, radarOn: false, lastShot: 0 });
   send(ws, { type: "joined", id: ws.id, code: room.code, map: MAP });
   return;
  }
  const room = rooms.get(ws.room), player = room?.players.get(ws.id); if (!room || !player) return;
  if (data.type === "leave") { leave(ws); return; }
  if (data.type === "start" && room.host === ws.id) { reset(room); return; }
  if (data.type === "lobby" && room.host === ws.id) { room.status = "lobby"; return; }
  if (data.type === "input") {
   const input = data.input && typeof data.input === "object" ? data.input : {};
   player.input = { forward: input.forward === true, back: input.back === true, left: input.left === true, right: input.right === true, sprint: input.sprint === true, revive: input.revive === true, turn: typeof input.turn === "number" && Number.isFinite(input.turn) ? Math.max(-1, Math.min(1, input.turn)) : 0 };
   if (typeof data.angle === "number" && Number.isFinite(data.angle)) player.a = Math.atan2(Math.sin(data.angle), Math.cos(data.angle));
   player.lastInput = now; return;
  }
  if (data.type !== "action" || room.status !== "playing" || player.down || player.escaped || now - player.lastAction < 180) return;
  player.lastAction = now;
  if (data.action === "light") player.light = player.battery > 0 && !player.light;
  if (data.action === "team") { room.follow = !room.follow; note(room, room.follow ? "AI teammates are following the nearest survivor." : "AI teammates are searching for cells."); }
  if (data.action === "medkit" && player.medkits > 0 && player.health < 100) { player.medkits--; player.health = Math.min(100, player.health + 50); }
  if (data.action === "radar" && (player.radar > 0 || player.radarOn)) player.radarOn = !player.radarOn && player.radar > 0;
  if (data.action === "shoot") {
   if (!player.gun || player.ammo < 1 || now - player.lastShot < 450) return;
   player.lastShot = now; player.ammo--;
   let best = null, bd = 1e9;
   for (const m of room.monsters) {
    const d = distance(player, m); if (d > 11 || d >= bd) continue;
    const df = Math.atan2(m.y - player.y, m.x - player.x) - player.a;
    if (Math.cos(df) <= 0 || Math.abs(Math.sin(df)) * d > .42 || !visible(player, m)) continue;
    best = m; bd = d;
   }
   for (const m of room.monsters) if (distance(player, m) < 14) { m.target = { x: player.x, y: player.y }; m.alert = 6; } // gunshots draw them in
   if (best) {
    best.hp--; best.stun = 2; best.path = [];
    if (best.hp <= 0) { const q = scatter(1, player, 20, 0)[0]; Object.assign(best, { x: q.x, y: q.y, hp: 3, stun: 0, alert: 0, cool: 2, path: [], target: null }); note(room, player.name + " drove a skinwalker away."); }
   }
  }
  if (data.action === "use") {
   const i = room.cells.findIndex(c => distance(player, c) < 1.1);
   if (i >= 0) collect(room, i, player.name);
   else if (distance(player, EXIT) < 1.25) { if (room.found === 3) { player.escaped = true; player.input = {}; note(room, player.name + " escaped. Other survivors can still reach the exit."); } else note(room, "The exit requires all three cells."); }
  }
 });
 ws.on("error", () => { }); ws.on("close", () => leave(ws));
});
function update(room, dt) {
 if (room.status !== "playing") return;
 room.time += dt;
 const active = [...room.players.values()].filter(p => !p.down && !p.escaped);
 for (const p of active) {
  const input = Date.now() - p.lastInput < 700 ? p.input : {};
  const f = Number(!!input.forward) - Number(!!input.back), s = Number(!!input.right) - Number(!!input.left), run = input.sprint && p.stamina > 3 && (f || s), speed = run ? 2.65 : 1.6, n = Math.max(1, Math.hypot(f, s));
  p.a += ((input.turn || 0) * 1.9 * dt);
  move(p, (Math.cos(p.a) * f - Math.sin(p.a) * s) * speed * dt / n, (Math.sin(p.a) * f + Math.cos(p.a) * s) * speed * dt / n);
  p.stamina = Math.max(0, Math.min(100, p.stamina + dt * (run ? -24 : 17)));
  if (p.light) { p.battery = Math.max(0, p.battery - dt * .6); if (!p.battery) p.light = false; }
  if (p.radarOn) { p.radar = Math.max(0, p.radar - dt / 50); if (!p.radar) p.radarOn = false; }
  for (let k = room.items.length - 1; k >= 0; k--) {
   const it = room.items[k]; if (distance(p, it) > .7) continue;
   if (it.type === "coin") p.coins++;
   else if (it.type === "ammo") { if (p.ammo >= 60) continue; p.ammo = Math.min(60, p.ammo + 8); }
   else if (it.type === "medkit") { if (p.medkits >= 3) continue; p.medkits++; }
   else if (it.type === "battery") { if (p.radar >= 3) continue; p.radar = Math.min(3, p.radar + 1); }
   else if (it.type === "gun") { p.gun = true; p.ammo = Math.min(60, p.ammo + 6); note(room, p.name + " found a gun."); }
   room.items.splice(k, 1);
  }
 }
 const downed = [...room.players.values(), ...room.bots].filter(o => o.down);
 for (const o of downed) {
  const helper = active.find(p => Date.now() - p.lastInput < 700 && p.input.revive && distance(p, o) < 1.25);
  o.revive = helper ? o.revive + dt : 0;
  if (o.revive >= 2.5) { o.down = false; o.revive = 0; o.timer = 0; if (o.ws) o.health = 40; for (const m of room.monsters) m.cool = 2.5; note(room, o.name + " was revived."); }
 }
 const reserved = new Set();
 for (const b of room.bots) {
  if (b.down) continue;
  const threat = room.monsters.filter(m => distance(b, m) < 4.3 && visible(b, m)).sort((a, c) => distance(b, a) - distance(b, c))[0], danger = !!threat;
  b.state = danger ? "FLEEING" : room.found === 3 ? "EXIT BOUND" : room.follow ? "FOLLOWING" : "SEARCHING";
  b.timer -= dt;
  if (b.timer <= 0) {
   b.timer = .85; let target;
   const near = [...active].sort((a, c) => distance(b, a) - distance(b, c))[0];
   if (danger) target = tiles.filter(v => distance(v, b) < 4).sort((a, c) => distance(c, threat) - distance(a, threat))[0] || near || b;
   else if (room.found === 3) target = EXIT;
   else if (room.follow) target = near && distance(near, b) > 1.6 ? near : b;
   else { const choices = room.cells.map((v, i) => ({ v, i, score: route(b, v).length + (reserved.has(i) ? 40 : 0) })).sort((a, c) => a.score - c.score); target = choices[0]?.v || near || b; if (choices[0]) reserved.add(choices[0].i); }
   b.path = route(b, target);
  }
  walk(b, danger ? 2.4 : 1.55, dt);
  const i = room.cells.findIndex(c => distance(b, c) < .58); if (i >= 0) collect(room, i, b.name);
 }
 for (const m of room.monsters) {
  m.cool = Math.max(0, m.cool - dt); m.stun = Math.max(0, (m.stun || 0) - dt);
  const prey = [...active, ...room.bots.filter(b => !b.down)].filter(o => {
   const d = distance(o, m); return (d < (o.ws ? (o.light ? 8.5 : 2.8) : 5.6) && visible(o, m)) || (o.ws && o.input.sprint && Date.now() - o.lastInput < 700 && d < 6.5);
  }).sort((a, b) => distance(m, a) - distance(m, b));
  if (prey.length) { m.target = { x: prey[0].x, y: prey[0].y }; m.alert = 6; } else m.alert = Math.max(0, m.alert - dt);
  m.timer -= dt;
  if (m.timer <= 0) {
   m.timer = .55;
   if (m.alert && m.target) m.path = route(m, m.target);
   else if (!m.path.length) {
    // skinwalker #1 lurks near the remaining cells; #0 wanders anywhere
    const t = m.i === 1 && room.cells.length ? room.cells[Math.random() * room.cells.length | 0] : tiles[Math.random() * tiles.length | 0];
    m.path = route(m, t);
   }
  }
  walk(m, m.stun ? 0 : m.cool ? .4 : m.alert ? 1.38 : .72, dt);
  if (!m.cool && !m.stun) {
   const victim = [...active, ...room.bots.filter(b => !b.down)].find(o => distance(o, m) < .53);
   if (victim) {
    if (victim.ws) {
     victim.health = Math.max(0, victim.health - 35); m.cool = 2.2;
     if (victim.health > 0) note(room, victim.name + " was mauled. " + victim.health + " HP left.");
     else { victim.down = true; victim.input = {}; m.cool = 3; note(room, victim.name + " is down. Hold R nearby to revive."); }
    } else { victim.down = true; victim.path = []; m.cool = 3; note(room, victim.name + " is down. Hold R nearby to revive."); }
   }
  }
 }
 if (![...room.players.values()].some(p => !p.down && !p.escaped)) room.status = [...room.players.values()].some(p => p.escaped) ? "won" : "lost";
}
let previous = Date.now();
setInterval(() => { const now = Date.now(), dt = Math.min(.1, (now - previous) / 1000); previous = now; for (const room of rooms.values()) { update(room, dt); const state = snapshot(room); for (const p of room.players.values()) send(p.ws, state); } }, 50);
setInterval(() => { for (const ws of wss.clients) { if (!ws.alive) { ws.terminate(); continue; } ws.alive = false; ws.ping(); } }, 30000);
server.listen(Number(process.env.PORT) || 3000, "0.0.0.0", () => console.log("The Last Circuit server is listening"));
