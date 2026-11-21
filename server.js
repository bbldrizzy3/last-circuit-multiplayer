"use strict";
const http = require("node:http");
const fs = require("node:fs");
const path = require("node:path");
const { randomBytes, randomUUID } = require("node:crypto");
const { WebSocketServer, WebSocket } = require("ws");

const MAP = [
 "111111111111111111111", "100000100000000000001",
 "101110101111101110101", "101000100000100010101",
 "101011111010111010101", "100010000010001000101",
 "111010111110101110101", "100010100000100000001",
 "101110101110111111101", "100000001000000000001",
 "101111101011111110101", "100000001000000010001",
 "111111111111111111111"
];
const EXIT = {x:19.5,y:11.5};
const rooms = new Map();
const tiles = [];
MAP.forEach((r,y)=>[...r].forEach((v,x)=>{if(v==="0")tiles.push({x:x+.5,y:y+.5});}));
const distance=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
const wall=(x,y)=>MAP[Math.floor(y)]?.[Math.floor(x)]!=="0";
function move(o,dx,dy){
 const r=.18;
 if(!wall(o.x+dx+Math.sign(dx)*r,o.y-r)&&!wall(o.x+dx+Math.sign(dx)*r,o.y+r))o.x+=dx;
 if(!wall(o.x-r,o.y+dy+Math.sign(dy)*r)&&!wall(o.x+r,o.y+dy+Math.sign(dy)*r))o.y+=dy;
}
function visible(a,b){const n=Math.ceil(distance(a,b)*12);for(let i=1;i<n;i++)if(wall(a.x+(b.x-a.x)*i/n,a.y+(b.y-a.y)*i/n))return false;return true;}
function route(a,b){
 const first=(a.x|0)+","+(a.y|0),q=[[a.x|0,a.y|0]],prev=new Map([[first,null]]);
 for(let i=0;i<q.length;i++){
  const [x,y]=q[i],k=x+","+y;
  if(x===(b.x|0)&&y===(b.y|0)){
   const result=[];let key=k;
   while(prev.get(key)!==null){const [u,v]=key.split(",").map(Number);result.unshift({x:u+.5,y:v+.5});key=prev.get(key);}
   return result;
  }
  for(const [dx,dy] of [[1,0],[-1,0],[0,1],[0,-1]]){const u=x+dx,v=y+dy,s=u+","+v;if(!wall(u+.5,v+.5)&&!prev.has(s)){prev.set(s,k);q.push([u,v]);}}
 }
 return [];
}
function walk(o,speed,dt){const target=o.path[0];if(!target)return;const d=distance(o,target),step=speed*dt;if(d<step+.025){o.x=target.x;o.y=target.y;o.path.shift();}else move(o,(target.x-o.x)/d*step,(target.y-o.y)/d*step);}
function send(ws,data){if(ws.readyState===WebSocket.OPEN&&ws.bufferedAmount<262144)ws.send(JSON.stringify(data));}
function note(room,text){room.message=text;room.messageUntil=room.time+5;}
function collect(room,i,who){room.cells.splice(i,1);room.found++;for(const p of room.players.values())p.battery=Math.min(100,p.battery+35);note(room,who+" recovered a cell. "+(room.found===3?"Exit powered. Regroup at the green door.":room.found+" / 3 secured."));}
function reset(room){
 room.time=0;room.found=0;room.follow=false;room.status="playing";
 room.cells=[{x:5.5,y:3.5},{x:11.5,y:7.5},{x:3.5,y:11.5}];
 room.monster={x:17.5,y:9.5,path:[],timer:0,alert:0,cool:0};
 room.bots=[{id:"mara",name:"MARA",x:2.5,y:1.5,color:"#86c8dc",path:[],timer:0,down:false,revive:0},{id:"eli",name:"ELI",x:3.5,y:1.5,color:"#ddb57e",path:[],timer:0,down:false,revive:0}];
 let i=0;for(const p of room.players.values()){Object.assign(p,{x:1.5+i*.5,y:1.5,a:0,down:false,escaped:false,revive:0,battery:100,stamina:100,light:true,input:{},lastInput:0});i++;}
 note(room,"Find three cells together. Q orders the AI teammates.");
}
function snapshot(room){
 return {type:"state",code:room.code,host:room.host,status:room.status,time:room.time,found:room.found,follow:room.follow,cells:room.cells,exit:EXIT,
 players:[...room.players.values()].map(p=>({id:p.id,name:p.name,x:p.x,y:p.y,a:p.a,down:p.down,escaped:p.escaped,revive:p.revive,light:p.light,battery:p.battery,stamina:p.stamina})),
 bots:room.bots.map(b=>({id:b.id,name:b.name,x:b.x,y:b.y,color:b.color,down:b.down,revive:b.revive,state:b.state||"WAITING"})),
 monster:{x:room.monster.x,y:room.monster.y,disguised:Math.sin(room.time*.45)>.2},message:room.time<room.messageUntil?room.message:""};
}
function leave(ws){const room=rooms.get(ws.room);if(room){room.players.delete(ws.id);if(!room.players.size)rooms.delete(room.code);else if(room.host===ws.id)room.host=room.players.keys().next().value;}ws.room=null;}
const server=http.createServer((req,res)=>{
 const pathname=(req.url||"/").split("?")[0];
 if(pathname==="/health"){res.writeHead(200,{"Content-Type":"application/json"});res.end(JSON.stringify({ok:true,rooms:rooms.size}));return;}
 if(pathname!=="/"&&pathname!=="/index.html"){res.writeHead(404);res.end("Not found");return;}
 fs.readFile(path.join(__dirname,"index.html"),(err,data)=>{
  res.writeHead(200,{"Content-Type":"text/html; charset=utf-8","Cache-Control":"no-store","X-Content-Type-Options":"nosniff","Referrer-Policy":"no-referrer"});
  res.end(err?"<!doctype html><title>The Last Circuit</title><h1>Server is running</h1><p>Upload the multiplayer index.html to finish setup. The old single-player HTML will not connect to this server.</p>":data);
 });
});
const wss=new WebSocketServer({server,path:"/ws",maxPayload:4096,perMessageDeflate:false});
wss.on("connection",ws=>{
 if(wss.clients.size>100){ws.close(1013,"Server full");return;}
 ws.id=randomUUID();ws.alive=true;ws.bucket=0;ws.window=Date.now();
 ws.on("pong",()=>ws.alive=true);
 send(ws,{type:"hello",id:ws.id});
 ws.on("message",raw=>{
  const now=Date.now();if(now-ws.window>1000){ws.window=now;ws.bucket=0;}if(++ws.bucket>80){ws.close(1008,"Too many messages");return;}
  let data;try{data=JSON.parse(raw.toString());}catch{return;}
  if(!data||typeof data!=="object"||Array.isArray(data))return;
  if(data.type==="create"||data.type==="join"){
   let room;
   if(data.type==="create"){
    if(rooms.size>=30){send(ws,{type:"error",message:"Server full. Try again later."});return;}
    let code;do{code=randomBytes(4).toString("hex").slice(0,6).toUpperCase();}while(rooms.has(code));
    room={code,host:ws.id,players:new Map()};reset(room);room.status="lobby";rooms.set(code,room);
   }else{
    const code=typeof data.code==="string"?data.code.trim().toUpperCase():"";room=rooms.get(code);
    if(!room){send(ws,{type:"error",message:"Room not found. Check the code."});return;}
    if(room.players.size>=4){send(ws,{type:"error",message:"Room is full (4 friends maximum)."});return;}
    if(room.status!=="lobby"){send(ws,{type:"error",message:"Game already started. Ask the host to return to the lobby."});return;}
   }
   leave(ws);ws.room=room.code;
   const name=(typeof data.name==="string"?data.name:"Player").replace(/[\x00-\x1f\x7f]/g,"").trim().slice(0,18)||"Player";
   room.players.set(ws.id,{id:ws.id,ws,name,x:1.5+room.players.size*.5,y:1.5,a:0,down:false,escaped:false,revive:0,light:true,battery:100,stamina:100,input:{},lastInput:0,lastAction:0});
   send(ws,{type:"joined",id:ws.id,code:room.code,map:MAP});
   return;
  }
  const room=rooms.get(ws.room),player=room?.players.get(ws.id);if(!room||!player)return;
  if(data.type==="leave"){leave(ws);return;}
  if(data.type==="start"&&room.host===ws.id){reset(room);return;}
  if(data.type==="lobby"&&room.host===ws.id){room.status="lobby";return;}
  if(data.type==="input"){
   const input=data.input&&typeof data.input==="object"?data.input:{};
   player.input={forward:input.forward===true,back:input.back===true,left:input.left===true,right:input.right===true,sprint:input.sprint===true,revive:input.revive===true,turn:typeof input.turn==="number"&&Number.isFinite(input.turn)?Math.max(-1,Math.min(1,input.turn)):0};
   if(typeof data.angle==="number"&&Number.isFinite(data.angle))player.a=Math.atan2(Math.sin(data.angle),Math.cos(data.angle));
   player.lastInput=now;return;
  }
  if(data.type!=="action"||room.status!=="playing"||player.down||player.escaped||now-player.lastAction<180)return;
  player.lastAction=now;
  if(data.action==="light")player.light=player.battery>0&&!player.light;
  if(data.action==="team"){room.follow=!room.follow;note(room,room.follow?"AI teammates are following the nearest survivor.":"AI teammates are searching for cells.");}
  if(data.action==="use"){
   const i=room.cells.findIndex(c=>distance(player,c)<1.1);
   if(i>=0)collect(room,i,player.name);
   else if(distance(player,EXIT)<1.25){if(room.found===3){player.escaped=true;player.input={};note(room,player.name+" escaped. Other survivors can still reach the exit.");}else note(room,"The exit requires all three cells.");}
  }
 });
 ws.on("error",()=>{});ws.on("close",()=>leave(ws));
});
function update(room,dt){
 if(room.status!=="playing")return;
 room.time+=dt;
 const active=[...room.players.values()].filter(p=>!p.down&&!p.escaped);
 const m=room.monster;
 for(const p of active){
  const input=Date.now()-p.lastInput<700?p.input:{};
  const f=Number(!!input.forward)-Number(!!input.back),s=Number(!!input.right)-Number(!!input.left),run=input.sprint&&p.stamina>3&&(f||s),speed=run?2.65:1.6,n=Math.max(1,Math.hypot(f,s));
  p.a+=((input.turn||0)*1.9*dt);
  move(p,(Math.cos(p.a)*f-Math.sin(p.a)*s)*speed*dt/n,(Math.sin(p.a)*f+Math.cos(p.a)*s)*speed*dt/n);
  p.stamina=Math.max(0,Math.min(100,p.stamina+dt*(run?-24:17)));
  if(p.light){p.battery=Math.max(0,p.battery-dt*.6);if(!p.battery)p.light=false;}
 }
 const downed=[...room.players.values(),...room.bots].filter(o=>o.down);
 for(const o of downed){
  const helper=active.find(p=>Date.now()-p.lastInput<700&&p.input.revive&&distance(p,o)<1.25);
  o.revive=helper?o.revive+dt:0;
  if(o.revive>=2.5){o.down=false;o.revive=0;o.timer=0;m.cool=2.5;note(room,o.name+" was revived.");}
 }
 const reserved=new Set();
 for(const b of room.bots){
  if(b.down)continue;
  const danger=distance(b,m)<4.3&&visible(b,m);
  b.state=danger?"FLEEING":room.found===3?"EXIT BOUND":room.follow?"FOLLOWING":"SEARCHING";
  b.timer-=dt;
  if(b.timer<=0){
   b.timer=.85;let target;
   const near=[...active].sort((a,c)=>distance(b,a)-distance(b,c))[0];
   if(danger)target=tiles.filter(v=>distance(v,b)<4).sort((a,c)=>distance(c,m)-distance(a,m))[0]||near||b;
   else if(room.found===3)target=EXIT;
   else if(room.follow)target=near&&distance(near,b)>1.6?near:b;
   else {const choices=room.cells.map((v,i)=>({v,i,score:route(b,v).length+(reserved.has(i)?40:0)})).sort((a,c)=>a.score-c.score);target=choices[0]?.v||near||b;if(choices[0])reserved.add(choices[0].i);}
   b.path=route(b,target);
  }
  walk(b,danger?2.4:1.55,dt);
  const i=room.cells.findIndex(c=>distance(b,c)<.58);if(i>=0)collect(room,i,b.name);
 }
 m.cool=Math.max(0,m.cool-dt);
 const prey=[...active,...room.bots.filter(b=>!b.down)].filter(o=>{
  const d=distance(o,m);return (d<(o.ws?(o.light?8.5:2.8):5.6)&&visible(o,m))||(o.ws&&o.input.sprint&&Date.now()-o.lastInput<700&&d<6.5);
 }).sort((a,b)=>distance(m,a)-distance(m,b));
 if(prey.length){m.target={x:prey[0].x,y:prey[0].y};m.alert=6;}else m.alert=Math.max(0,m.alert-dt);
 m.timer-=dt;
 if(m.timer<=0){m.timer=.55;if(m.alert&&m.target)m.path=route(m,m.target);else if(!m.path.length)m.path=route(m,tiles[Math.random()*tiles.length|0]);}
 walk(m,m.cool?.4:m.alert?1.38:.72,dt);
 if(!m.cool){const victim=[...active,...room.bots.filter(b=>!b.down)].find(o=>distance(o,m)<.53);if(victim){victim.down=true;victim.path=[];victim.input={};m.cool=3;note(room,victim.name+" is down. Hold R nearby to revive.");}}
 if(![...room.players.values()].some(p=>!p.down&&!p.escaped))room.status=[...room.players.values()].some(p=>p.escaped)?"won":"lost";
}
let previous=Date.now();
setInterval(()=>{const now=Date.now(),dt=Math.min(.1,(now-previous)/1000);previous=now;for(const room of rooms.values()){update(room,dt);const state=snapshot(room);for(const p of room.players.values())send(p.ws,state);}},50);
setInterval(()=>{for(const ws of wss.clients){if(!ws.alive){ws.terminate();continue;}ws.alive=false;ws.ping();}},30000);
server.listen(Number(process.env.PORT)||3000,"0.0.0.0",()=>console.log("The Last Circuit server is listening"));
