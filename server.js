"use strict";
const http = require("node:http");
const fs = require("node:fs");
const path = require("node:path");
const { randomBytes, randomUUID } = require("node:crypto");
const { WebSocketServer, WebSocket } = require("ws");

// ---- Map: 41 x 31 maze with a CONTROL CENTER in the middle (doors on its left and right) ----
const MW = 41, MH = 31;
const RX0 = 18, RX1 = 24, RY0 = 13, RY1 = 17;     // control room block (walls included); interior x19-23, y14-16
const NIGHT = 420, HOUR = NIGHT / 6;               // survive from 12 AM to 6 AM (7 real minutes)
let CUR = null;                                    // room currently being processed (closed doors count as walls)
function build() {
 const g = Array.from({ length: MH }, () => Array(MW).fill(1));
 const reserved = (x, y) => x >= RX0 && x <= RX1 && y >= RY0 && y <= RY1;
 const st = [[1, 1]]; g[1][1] = 0;
 while (st.length) {
  const [x, y] = st[st.length - 1];
  const n = [[2, 0], [-2, 0], [0, 2], [0, -2]]
   .filter(([a, b]) => x + a > 0 && x + a < MW - 1 && y + b > 0 && y + b < MH - 1 && !reserved(x + a, y + b) && g[y + b][x + a] === 1)
   .sort(() => Math.random() - .5);
  if (!n.length) { st.pop(); continue; }
  const [a, b] = n[0]; g[y + b / 2][x + a / 2] = 0; g[y + b][x + a] = 0; st.push([x + a, y + b]);
 }
 for (let y = 1; y < MH - 1; y++) for (let x = 1; x < MW - 1; x++) {
  if (g[y][x] && !reserved(x, y) && (x + y) % 2 === 1 && Math.random() < .1) {
   if ((x % 2 === 0 && g[y][x - 1] === 0 && g[y][x + 1] === 0) || (y % 2 === 0 && g[y - 1][x] === 0 && g[y + 1][x] === 0)) g[y][x] = 0;
  }
 }
 for (let y = RY0; y <= RY1; y++) for (let x = RX0; x <= RX1; x++) g[y][x] = 1;           // room walls
 for (let y = RY0 + 1; y < RY1; y++) for (let x = RX0 + 1; x < RX1; x++) g[y][x] = 0;     // room floor
 g[15][RX0] = 0; g[15][RX1] = 0;                                                            // the two doorways
 return g.map(r => r.join(""));
}
const MAP = build();
const rooms = new Map();
const tiles = [];
MAP.forEach((r, y) => [...r].forEach((v, x) => { if (v === "0") tiles.push({ x: x + .5, y: y + .5 }); }));
const distance = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
const wall = (x, y) => {
 if (MAP[Math.floor(y)]?.[Math.floor(x)] !== "0") return true;
 if (CUR) for (const d of CUR.doors) if (d.closed && Math.floor(x) === d.x && Math.floor(y) === d.y) return true;
 return false;
};
function scatter(n, from, min, gap, used = []) {
 const out = [];
 for (let t = 0; t < 3000 && out.length < n; t++) {
  const c = tiles[Math.random() * tiles.length | 0];
  if (distance(c, from) >= min && [...out, ...used].every(o => distance(o, c) >= gap)) out.push({ x: c.x, y: c.y });
 }
 while (out.length < n) { const c = tiles[Math.random() * tiles.length | 0]; out.push({ x: c.x, y: c.y }); }
 return out;
}
const freeLen = (x, y, a) => { let d = 0; while (d < 12 && !wall(x + Math.cos(a) * (d + 1), y + Math.sin(a) * (d + 1))) d++; return d; };
function viewDir(x, y, skip) {
 let best = 0, bd = -1;
 for (const a of [0, Math.PI / 2, Math.PI, -Math.PI / 2]) {
  if (skip !== undefined && Math.abs(Math.atan2(Math.sin(a - skip), Math.cos(a - skip))) < .1) continue;
  const d = freeLen(x, y, a); if (d > bd) { bd = d; best = a; }
 }
 return best;
}
const SPAWN = { x: 21.5, y: 15.5 }, CONSOLE = { x: 21.5, y: 14.45 };
const GEN = scatter(1, SPAWN, 16, 0)[0];
const DOORS_DEF = [{ id: 0, x: RX0, y: 15, out: { x: RX0 - .5, y: 15.5 } }, { id: 1, x: RX1, y: 15, out: { x: RX1 + 1.5, y: 15.5 } }];
function doorCam(door, toDoor) {            // camera a few tiles down the hallway, looking back at the door
 const a0 = viewDir(door.out.x, door.out.y, toDoor), L = Math.min(4, freeLen(door.out.x, door.out.y, a0));
 return { x: door.out.x + Math.cos(a0) * L, y: door.out.y + Math.sin(a0) * L, a: a0 + Math.PI };
}
const CAMS = [doorCam(DOORS_DEF[0], 0), doorCam(DOORS_DEF[1], Math.PI),
 ...scatter(6, SPAWN, 7, 8, [GEN]).map(p => ({ x: p.x, y: p.y, a: viewDir(p.x, p.y) }))
].map((c, i) => ({ ...c, name: "CAM " + String(i + 1).padStart(2, "0") }));

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
function makeNoise(room, pos, radius) { for (const m of room.monsters) if (distance(m, pos) < radius) { m.target = { x: pos.x, y: pos.y }; m.alert = Math.max(m.alert, 5); } }
function bump(p, amount) { p.noise = Math.min(100, p.noise + amount); }
function reset(room) {
 room.time = 0; room.hour = 0; room.follow = true; room.status = "playing";
 room.power = 100; room.gen = { cool: 0 };
 room.doors = DOORS_DEF.map(d => ({ ...d, closed: false }));
 room.cams = CAMS.map(() => ({ broken: false }));
 room.items = []; const used = [GEN, ...CAMS]; let nid = 0;
 const place = (type, n) => { for (const q of scatter(n, SPAWN, 4, 3, used)) { used.push(q); room.items.push({ id: ++nid, type, x: q.x, y: q.y }); } };
 place("gun", 2); place("ammo", 8); place("battery", 8); place("coin", 14);
 room.monsters = scatter(2, SPAWN, 18, 12).map((p, i) => ({ i, x: p.x, y: p.y, path: [], timer: 0, alert: 0, cool: 0, hp: 3, stun: 0, wait: 0 }));
 room.bots = [{ id: "mara", name: "MARA", x: 20.5, y: 14.8, color: "#86c8dc", path: [], timer: 0, down: false, dead: false, revive: 0 }, { id: "eli", name: "ELI", x: 22.5, y: 14.8, color: "#ddb57e", path: [], timer: 0, down: false, dead: false, revive: 0 }];
 const spots = [[20.5, 15.5], [22.5, 15.5], [20.5, 16.2], [22.5, 16.2]]; let i = 0;
 for (const p of room.players.values()) { const s = spots[i % 4]; Object.assign(p, { x: s[0], y: s[1], a: 0, down: false, dead: false, escaped: false, revive: 0, battery: 100, stamina: 100, light: true, input: {}, lastInput: 0, health: 100, ammo: 0, gun: false, coins: 0, medkits: 0, radar: 3, radarOn: false, lastShot: 0, noise: 0, viewing: false }); i++; }
 note(room, "Survive until 6 AM. Watch the cameras, close the doors, keep the generator running.");
}
function snapshot(room) {
 return {
  type: "state", code: room.code, host: room.host, status: room.status, time: room.time, night: NIGHT, power: room.power, follow: room.follow,
  console: CONSOLE, gen: { x: GEN.x, y: GEN.y, cool: room.gen.cool },
  doors: room.doors.map(d => ({ id: d.id, x: d.x, y: d.y, closed: d.closed })),
  cams: CAMS.map((c, i) => ({ id: i, name: c.name, x: c.x, y: c.y, a: c.a, broken: room.cams[i].broken })),
  items: room.items,
  players: [...room.players.values()].map(p => ({ id: p.id, name: p.name, x: p.x, y: p.y, a: p.a, down: p.down, dead: p.dead, escaped: p.escaped, revive: p.revive, light: p.light, battery: p.battery, stamina: p.stamina, health: p.health, ammo: p.ammo, gun: p.gun, coins: p.coins, medkits: p.medkits, radar: p.radar, radarOn: p.radarOn, noise: p.noise })),
  bots: room.bots.map(b => ({ id: b.id, name: b.name, x: b.x, y: b.y, color: b.color, down: b.down, dead: b.dead, revive: b.revive, state: b.state || "WAITING" })),
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
   room.players.set(ws.id, { id: ws.id, ws, name, x: SPAWN.x, y: SPAWN.y, a: 0, down: false, dead: false, escaped: false, revive: 0, light: true, battery: 100, stamina: 100, input: {}, lastInput: 0, lastAction: 0, health: 100, ammo: 0, gun: false, coins: 0, medkits: 0, radar: 3, radarOn: false, lastShot: 0, noise: 0, viewing: false });
   send(ws, { type: "joined", id: ws.id, code: room.code, map: MAP });
   return;
  }
  const room = rooms.get(ws.room), player = room?.players.get(ws.id); if (!room || !player) return;
  CUR = room;
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
  if (data.action === "viewon") player.viewing = true;
  if (data.action === "viewoff") player.viewing = false;
  if (data.action === "light") player.light = player.battery > 0 && !player.light;
  if (data.action === "team") { room.follow = !room.follow; note(room, room.follow ? "AI teammates are following the nearest survivor." : "AI teammates are guarding the control room."); }
  if (data.action === "medkit" && player.medkits > 0 && player.health < 100) { player.medkits--; player.health = Math.min(100, player.health + 50); }
  if (data.action === "radar" && (player.radar > 0 || player.radarOn)) player.radarOn = !player.radarOn && player.radar > 0;
  if (data.action === "shoot") {
   if (!player.gun || player.ammo < 1 || now - player.lastShot < 450) return;
   player.lastShot = now; player.ammo--; bump(player, 100);
   let best = null, bd = 1e9;
   for (const m of room.monsters) {
    const d = distance(player, m); if (d > 11 || d >= bd) continue;
    const df = Math.atan2(m.y - player.y, m.x - player.x) - player.a;
    if (Math.cos(df) <= 0 || Math.abs(Math.sin(df)) * d > .42 || !visible(player, m)) continue;
    best = m; bd = d;
   }
   makeNoise(room, player, 14);   // gunshots draw them in
   if (best) {
    best.hp--; best.stun = 2; best.path = [];
    if (best.hp <= 0) { const q = scatter(1, player, 20, 0)[0]; Object.assign(best, { x: q.x, y: q.y, hp: 3, stun: 0, alert: 0, cool: 2, path: [], target: null }); note(room, player.name + " drove a skinwalker away."); }
   }
  }
  if (data.action === "use") {
   const ci = room.cams.findIndex((c, i) => c.broken && distance(player, CAMS[i]) < 1.5);
   const door = room.doors.find(d => distance(player, { x: d.x + .5, y: d.y + .5 }) < 1.7);
   if (ci >= 0) { room.cams[ci].broken = false; bump(player, 40); makeNoise(room, player, 8); note(room, CAMS[ci].name + " repaired."); }
   else if (distance(player, GEN) < 1.6) {
    if (room.gen.cool > 0) note(room, "The generator is still warming up (" + Math.ceil(room.gen.cool) + "s).");
    else {
     const was = room.power <= 0; room.power = was ? 40 : Math.min(100, room.power + 25); room.gen.cool = 25;
     bump(player, 70); makeNoise(room, GEN, 18);
     note(room, was ? "Generator restarted. Power is back (40%) — it was LOUD." : "Generator refueled. Power " + Math.round(room.power) + "% — it was LOUD.");
    }
   } else if (door) {
    const c = { x: door.x + .5, y: door.y + .5 };
    if (room.power <= 0) note(room, "No power — the doors are stuck open.");
    else if (!door.closed && [...room.players.values(), ...room.bots, ...room.monsters].some(o => !o.down && distance(o, c) < .75)) note(room, "Something is in the doorway!");
    else { door.closed = !door.closed; bump(player, 35); makeNoise(room, c, 12); note(room, (door.id ? "Right" : "Left") + " door " + (door.closed ? "closed" : "opened") + "."); }
   }
  }
 });
 ws.on("error", () => { }); ws.on("close", () => leave(ws));
});
function update(room, dt) {
 CUR = room;
 if (room.status !== "playing") return;
 room.time += dt;
 const hour = Math.min(5, Math.floor(room.time / HOUR));
 if (hour !== room.hour) { room.hour = hour; note(room, hour + " AM"); }
 // power: drains slowly, faster with doors closed and monitors in use
 if (room.power > 0) {
  const watching = [...room.players.values()].some(p => p.viewing && !p.down);
  const before = room.power;
  room.power = Math.max(0, room.power - dt * (.1 + room.doors.filter(d => d.closed).length * .2 + (watching ? .08 : 0)));
  if (room.power <= 0) { room.doors.forEach(d => d.closed = false); for (const p of room.players.values()) p.viewing = false; note(room, "POWER OUT. Doors unlocked, cameras dead. Restart the generator!"); }
  else if (before > 20 && room.power <= 20) note(room, "Power is getting low (20%). Refuel the generator.");
 }
 room.gen.cool = Math.max(0, room.gen.cool - dt);
 const active = [...room.players.values()].filter(p => !p.down && !p.escaped);
 for (const p of active) {
  const input = Date.now() - p.lastInput < 700 && !p.viewing ? p.input : {};
  const f = Number(!!input.forward) - Number(!!input.back), s = Number(!!input.right) - Number(!!input.left), run = input.sprint && p.stamina > 3 && (f || s), speed = run ? 2.65 : 1.6, n = Math.max(1, Math.hypot(f, s));
  p.a += ((input.turn || 0) * 1.9 * dt);
  move(p, (Math.cos(p.a) * f - Math.sin(p.a) * s) * speed * dt / n, (Math.sin(p.a) * f + Math.cos(p.a) * s) * speed * dt / n);
  p.stamina = Math.max(0, Math.min(100, p.stamina + dt * (run ? -24 : 17)));
  p.noise = Math.max(0, p.noise - 22 * dt); if (f || s) p.noise = Math.min(100, p.noise + (run ? 58 : 7) * dt);   // sprinting is LOUD
  if (p.light) { p.battery = Math.max(0, p.battery - dt * .6); if (!p.battery) p.light = false; }
  if (p.radarOn) { p.radar = Math.max(0, p.radar - dt / 50); if (!p.radar) p.radarOn = false; }
  for (let k = room.items.length - 1; k >= 0; k--) {
   const it = room.items[k]; if (distance(p, it) > .7) continue;
   if (it.type === "coin") p.coins++;
   else if (it.type === "ammo") { if (p.ammo >= 60) continue; p.ammo = Math.min(60, p.ammo + 8); }
   else if (it.type === "medkit") { if (p.medkits >= 3) continue; p.medkits++; }
   else if (it.type === "battery") { if (p.radar >= 3 && p.battery >= 100) continue; p.radar = Math.min(3, p.radar + 1); p.battery = Math.min(100, p.battery + 40); }
   else if (it.type === "gun") { p.gun = true; p.ammo = Math.min(60, p.ammo + 6); note(room, p.name + " found a gun."); }
   room.items.splice(k, 1);
  }
 }
 const reserved = new Set();
 for (const b of room.bots) {
  if (b.down) continue;
  const threat = room.monsters.filter(m => distance(b, m) < 4.3 && visible(b, m)).sort((a, c) => distance(b, a) - distance(b, c))[0], danger = !!threat;
  b.state = danger ? "FLEEING" : room.follow ? "FOLLOWING" : "GUARDING";
  b.timer -= dt;
  if (b.timer <= 0) {
   b.timer = .85; let target;
   const near = [...active].sort((a, c) => distance(b, a) - distance(b, c))[0];
   if (danger) target = tiles.filter(v => distance(v, b) < 4).sort((a, c) => distance(c, threat) - distance(a, threat))[0] || near || b;
   else if (room.follow) target = near && distance(near, b) > 1.8 ? near : b;
   else target = distance(b, SPAWN) > 1.5 ? SPAWN : b;
   b.path = route(b, target);
  }
  walk(b, danger ? 2.4 : 1.55, dt);
 }
 const spd = 1 + hour * .06, aggr = .3 + hour * .08;
 for (const m of room.monsters) {
  m.cool = Math.max(0, m.cool - dt); m.stun = Math.max(0, (m.stun || 0) - dt);
  const prey = [...active, ...room.bots.filter(b => !b.down)].filter(o => {
   const d = distance(o, m); return (d < (o.ws ? (o.light ? 8.5 : 2.8) : 5.6) && visible(o, m)) || (o.ws && o.noise > 25 && d < o.noise / 100 * 14);   // they HEAR loud survivors
  }).sort((a, b) => distance(m, a) - distance(m, b));
  if (prey.length) { m.target = { x: prey[0].x, y: prey[0].y }; m.alert = 6; } else m.alert = Math.max(0, m.alert - dt);
  m.timer -= dt;
  if (m.timer <= 0) {
   m.timer = .55;
   if (m.alert && m.target) {
    let r = route(m, m.target);
    if (!r.length) { // sealed in: wait at the nearest closed door
     for (const d of room.doors.filter(d => d.closed).sort((a, b) => distance(a.out, m.target) - distance(b.out, m.target))) { r = route(m, d.out); if (r.length || distance(m, d.out) < 1) break; }
    }
    m.path = r;
   } else if (!m.path.length) {
    let t;
    if (Math.random() < aggr) { const d = room.doors[Math.random() * 2 | 0]; t = room.doors.some(x => !x.closed) && Math.random() < .5 ? SPAWN : d.out; }   // they come for the control room
    else if (m.i === 1 && Math.random() < .5) t = GEN;
    else t = tiles[Math.random() * tiles.length | 0];
    m.path = route(m, t);
   }
  }
  const door = room.doors.find(d => d.closed && distance(m, d.out) < .9);
  if (door) {
   m.wait += dt;
   if (!m.knock || room.time - m.knock > 9) { m.knock = room.time; note(room, "Something is banging on the " + (door.id ? "right" : "left") + " door!"); }
   if (m.wait > 7) { m.alert = 0; m.target = null; m.path = []; m.wait = 0; }   // gives up (for now)
  } else m.wait = 0;
  walk(m, (m.stun ? 0 : m.cool ? .4 : m.alert ? 1.38 : .72) * spd, dt);
  room.cams.forEach((c, i) => { if (!c.broken && distance(m, CAMS[i]) < 1.6 && Math.random() < .25 * dt) { c.broken = true; note(room, CAMS[i].name + " went offline! Someone has to go fix it."); } });
  if (!m.cool && !m.stun) {   // caught = dead
   const victim = [...active, ...room.bots.filter(b => !b.down)].find(o => distance(o, m) < .53);
   if (victim) { victim.down = true; victim.dead = true; victim.health = 0; victim.path = []; victim.input = {}; victim.viewing = false; m.cool = 3; note(room, victim.name + " was caught."); }
  }
 }
 if (room.time >= NIGHT) { room.status = "won"; for (const p of room.players.values()) p.escaped = !p.dead; note(room, "6 AM. You survived the night."); return; }
 if (![...room.players.values()].some(p => !p.dead)) room.status = "lost";
}
let previous = Date.now();
setInterval(() => { const now = Date.now(), dt = Math.min(.1, (now - previous) / 1000); previous = now; for (const room of rooms.values()) { update(room, dt); const state = snapshot(room); for (const p of room.players.values()) send(p.ws, state); } }, 50);
setInterval(() => { for (const ws of wss.clients) { if (!ws.alive) { ws.terminate(); continue; } ws.alive = false; ws.ping(); } }, 30000);
server.listen(Number(process.env.PORT) || 3000, "0.0.0.0", () => console.log("The Last Circuit server is listening"));
