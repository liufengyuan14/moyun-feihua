#!/usr/bin/env node
'use strict';
/* 墨韵飞花 · 连线对令服务（零依赖，Node.js >= 14）
 * 启动：node feihua-server.js [端口]      默认 8787
 * 页面：http://localhost:8787/feihualing.html
 * 连线：ws://localhost:8787/ws
 * 职责：静态托管页面 + 房间管理 + 陌生人匹配 + 房间内消息透传。
 *      诗句合法性、计时、回合推进全部由各客户端自行判定，服务端不介入对局规则。
 */
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const os = require('os');

const PORT = Number(process.env.PORT || process.argv[2] || 8787) || 8787;
const ROOT = __dirname;
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const ROOM_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const MAX_FRAME = 2 * 1024 * 1024;
const MIME = {'.html':'text/html; charset=utf-8','.js':'text/javascript; charset=utf-8','.css':'text/css; charset=utf-8','.json':'application/json; charset=utf-8','.png':'image/png','.svg':'image/svg+xml','.ico':'image/x-icon'};

const clients = new Set();
const rooms = new Map();
let queue = [];
let seq = 0;

function stamp(){return new Date().toTimeString().slice(0,8)}
function log(...args){console.log('[墨韵飞花 '+stamp()+']',...args)}

/* ---------- WebSocket 帧编解码（RFC 6455，仅用 Node 内置模块） ---------- */
function sendFrame(client, opcode, payload){
  if(client.socket.destroyed)return;
  const len = payload.length;
  let head;
  if(len < 126){head = Buffer.alloc(2);head[1] = len;}
  else if(len < 65536){head = Buffer.alloc(4);head[1] = 126;head.writeUInt16BE(len,2);}
  else{head = Buffer.alloc(10);head[1] = 127;head.writeBigUInt64BE(BigInt(len),2);}
  head[0] = 0x80 | opcode;
  try{client.socket.write(Buffer.concat([head,payload]));}catch(_){}
}
function send(client,obj){
  try{sendFrame(client,0x1,Buffer.from(JSON.stringify(obj),'utf8'));}catch(_){}
}
function parseFrames(client){
  let guard = 0;
  while(client.buf.length >= 2 && guard++ < 200){
    const b0 = client.buf[0], b1 = client.buf[1];
    const fin = !!(b0 & 0x80), op = b0 & 0x0f, masked = !!(b1 & 0x80);
    let len = b1 & 0x7f, off = 2;
    if(len === 126){if(client.buf.length < 4)return;len = client.buf.readUInt16BE(2);off = 4;}
    else if(len === 127){
      if(client.buf.length < 10)return;
      const big = client.buf.readBigUInt64BE(2);
      if(big > BigInt(MAX_FRAME)){client.socket.destroy();return}
      len = Number(big);off = 10;
    }
    let mask = null;
    if(masked){if(client.buf.length < off + 4)return;mask = client.buf.subarray(off,off + 4);off += 4;}
    if(client.buf.length < off + len)return;
    const payload = Buffer.from(client.buf.subarray(off,off + len));
    client.buf = client.buf.subarray(off + len);
    if(masked)for(let i = 0;i < payload.length;i++)payload[i] ^= mask[i % 4];
    if(op === 0x8){client.socket.end();return}
    if(op === 0x9){sendFrame(client,0xA,payload);continue}
    if(op === 0xA){client.alive = true;continue}
    if(op === 0x0 || op === 0x1){
      client.frag.push(payload);
      if(fin){
        const text = Buffer.concat(client.frag).toString('utf8');
        client.frag = [];
        handleMessage(client,text);
      }
    }
  }
}

/* ---------- 房间与匹配 ---------- */
function publicMember(m){return {id:m.id,name:m.name,avatar:m.avatar,ready:m.ready}}
function roomState(room){
  return {type:'room:state',room:room.code,host:room.host,
    members:Array.from(room.members.values()).map(publicMember),
    cfg:room.cfg,createdAt:room.createdAt};
}
function broadcastRoom(room){
  const state = roomState(room);
  for(const m of room.members.values())send(m,state);
}
function newRoomCode(){
  let code;
  do{code = Array.from({length:4},()=>ROOM_CHARS[Math.floor(Math.random()*ROOM_CHARS.length)]).join('');}while(rooms.has(code));
  return code;
}
function attachToRoom(client,room){
  client.room = room.code;client.ready = false;
  room.members.set(client.id,client);
}
function createRoom(host,cfg){
  const room = {code:newRoomCode(),host:host.id,members:new Map(),cfg:cfg || null,createdAt:Date.now()};
  rooms.set(room.code,room);
  attachToRoom(host,room);
  return room;
}
function leaveRoom(client,notify){
  const code = client.room;
  client.room = null;client.ready = false;
  if(!code)return;
  const room = rooms.get(code);
  if(!room)return;
  room.members.delete(client.id);
  if(!room.members.size){rooms.delete(code);return}
  if(room.host === client.id)room.host = room.members.keys().next().value;
  if(notify){
    for(const m of room.members.values())send(m,{type:'relay',from:client.id,data:{type:'peer:left',name:client.name}});
  }
  broadcastRoom(room);
}
function matchKey(cfg){
  const c = cfg && typeof cfg === 'object' ? cfg : {};
  const mode = String(c.m || 'classic');
  const tokens = Array.isArray(c.t) ? c.t.join('') : '';
  return mode + '|' + tokens;
}
function cleanQueue(){
  queue = queue.filter(q=>clients.has(q.client) && !q.client.room);
}
function joinMatch(client,cfg){
  cleanQueue();
  const key = matchKey(cfg);
  const idx = queue.findIndex(q=>q.key === key && q.client !== client);
  if(idx >= 0){
    const other = queue.splice(idx,1)[0];
    const host = other.client;
    const room = createRoom(host,other.cfg || cfg);
    attachToRoom(client,room);
    send(host,{type:'match:found',room:room.code,hostId:room.host,autoStart:true,cfg:room.cfg});
    send(client,{type:'match:found',room:room.code,hostId:room.host,autoStart:false,cfg:room.cfg});
    broadcastRoom(room);
    log('匹配成功',room.code,'·',host.name,'↔',client.name,'·',key);
  }else{
    queue.push({client,key,cfg,at:Date.now()});
    send(client,{type:'match:waiting',count:queue.length,key});
    log('匹配排队',client.name,'·',key,'· 当前',queue.length,'人');
  }
}

function handleMessage(client,raw){
  let msg;
  try{msg = JSON.parse(raw)}catch(_){return}
  if(!msg || typeof msg !== 'object')return;
  switch(msg.type){
    case 'hello':{
      client.name = String(msg.name || '诗友').slice(0,12);
      client.avatar = String(msg.avatar || '诗').slice(0,1);
      send(client,{type:'welcome',id:client.id,rooms:rooms.size,online:clients.size});
      break;
    }
    case 'room:create':{
      queue = queue.filter(q=>q.client !== client);
      leaveRoom(client,false);
      const room = createRoom(client,msg.cfg || null);
      send(client,{type:'room:created',room:room.code});
      broadcastRoom(room);
      log('开房',room.code,'·',client.name);
      break;
    }
    case 'room:join':{
      queue = queue.filter(q=>q.client !== client);
      const code = String(msg.room || '').trim().toUpperCase().slice(0,6);
      const room = rooms.get(code);
      if(!room){send(client,{type:'room:error',msg:'没有这间诗房，房号可能有误'});break}
      if(room.members.size >= 2){send(client,{type:'room:error',msg:'诗房已满，一间房限两位诗友'});break}
      leaveRoom(client,false);
      attachToRoom(client,room);
      broadcastRoom(room);
      log(client.name,'入房',code);
      break;
    }
    case 'room:leave':{
      leaveRoom(client,true);
      queue = queue.filter(q=>q.client !== client);
      break;
    }
    case 'room:ready':{
      client.ready = !!msg.ready;
      const room = rooms.get(client.room);
      if(room)broadcastRoom(room);
      break;
    }
    case 'match:join':{
      leaveRoom(client,false);
      joinMatch(client,msg.cfg || null);
      break;
    }
    case 'match:cancel':{
      queue = queue.filter(q=>q.client !== client);
      send(client,{type:'match:cancelled'});
      break;
    }
    case 'relay':{
      const room = rooms.get(client.room);
      if(!room || !msg.data || typeof msg.data !== 'object')break;
      for(const m of room.members.values()){
        if(m !== client)send(m,{type:'relay',from:client.id,data:msg.data});
      }
      break;
    }
    case 'ping':send(client,{type:'pong',at:Date.now()});break;
    default:break;
  }
}

function onClose(client){
  if(client.closed)return;
  client.closed = true;
  clients.delete(client);
  queue = queue.filter(q=>q.client !== client);
  leaveRoom(client,true);
}

/* ---------- HTTP 静态托管 ---------- */
const server = http.createServer((req,res)=>{
  let pathname;
  try{pathname = decodeURIComponent(new URL(req.url,'http://localhost').pathname);}catch(_){pathname = '/';}
  if(pathname === '/health' || pathname === '/api/health'){
    res.writeHead(200,{'Content-Type':'application/json; charset=utf-8','Access-Control-Allow-Origin':'*','Cache-Control':'no-store'});
    res.end(JSON.stringify({ok:true,service:'moyun-feihua-online',rooms:rooms.size,online:clients.size,queue:queue.length,uptime:Math.floor(process.uptime())}));
    return;
  }
  const rel = pathname === '/' ? 'feihualing.html' : pathname.replace(/^\/+/,'');
  const abs = path.resolve(ROOT,rel);
  if(abs !== ROOT && !abs.startsWith(ROOT + path.sep)){res.writeHead(403);res.end('Forbidden');return}
  fs.readFile(abs,(err,buf)=>{
    if(err){res.writeHead(404,{'Content-Type':'text/plain; charset=utf-8'});res.end('未找到：'+pathname);return}
    res.writeHead(200,{'Content-Type':MIME[path.extname(abs).toLowerCase()] || 'application/octet-stream','Cache-Control':'no-store'});
    res.end(buf);
  });
});

server.on('upgrade',(req,socket,head)=>{
  let pathname = '/';
  try{pathname = new URL(req.url,'http://localhost').pathname;}catch(_){}
  const key = req.headers['sec-websocket-key'];
  if((pathname !== '/' && pathname !== '/ws') || !key || String(req.headers.upgrade || '').toLowerCase() !== 'websocket'){
    socket.destroy();return;
  }
  const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  const client = {
    id:'p-' + (++seq).toString(36) + '-' + Date.now().toString(36),
    socket,name:'诗友',avatar:'诗',room:null,ready:false,alive:true,closed:false,
    buf:Buffer.alloc(0),frag:[]
  };
  clients.add(client);
  if(head && head.length)client.buf = Buffer.from(head);
  socket.on('data',chunk=>{
    client.buf = Buffer.concat([client.buf,chunk]);
    try{parseFrames(client)}catch(_){socket.destroy()}
  });
  socket.on('close',()=>onClose(client));
  socket.on('error',()=>onClose(client));
  send(client,{type:'welcome',id:client.id,rooms:rooms.size,online:clients.size});
  if(client.buf.length)parseFrames(client);
});

setInterval(()=>{
  for(const c of clients){
    if(!c.alive){c.socket.destroy();continue}
    c.alive = false;
    try{sendFrame(c,0x9,Buffer.alloc(0))}catch(_){}
  }
},30000).unref();

server.listen(PORT,'0.0.0.0',()=>{
  const nets = os.networkInterfaces();
  const lan = [];
  Object.keys(nets).forEach(k=>(nets[k] || []).forEach(n=>{if(n.family === 'IPv4' && !n.internal)lan.push(n.address)}));
  console.log('');
  console.log('  墨韵飞花 · 连线对令服务已启动');
  console.log('  页面    http://localhost:' + PORT + '/feihualing.html');
  console.log('  连线    ws://localhost:' + PORT + '/ws');
  console.log('  健康    http://localhost:' + PORT + '/health');
  if(lan.length)console.log('  局域网  ' + lan.map(ip=>'http://' + ip + ':' + PORT + '/feihualing.html').join('  |  '));
  console.log('  好友打开同一地址即可入房；陌生人匹配会自动结对。Ctrl+C 结束。');
  console.log('');
});
server.on('error',err=>{
  if(err.code === 'EADDRINUSE')console.error('端口 ' + PORT + ' 已被占用，请换一个：node feihua-server.js 8788');
  else console.error(err);
  process.exitCode = 1;
});
