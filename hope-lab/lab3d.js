"use strict";
/* HOPE 랩 3D 연구실 (Three.js r149, 전역 THREE 사용)
   - 기본 도형을 조합한 로우폴리 파스텔 스타일
   - API: Lab3D.init(), attach(el), detach(), sync(state), jumpPI(), onPI, onMate */
(function(){
const PI=Math.PI, TAU=PI*2;
const L=window.Lab3D={ok:false,onPI:null,onMate:null};
if(typeof THREE==="undefined") return;

let renderer=null, scene, camera, host=null, canvas=null, ro=null;
let raf=0, running=false, last=0, time=0, lost=false;
let roomG, propG, agentG, fxG, piA=null;
let R=0, sigRoom="", spots=[], anim=[], parts=[];
const agents=[], hitboxes=[];
const cam={az:.78,pol:.95,dist:16,target:16,zoom:1};
const ray=new THREE.Raycaster(), ndc=new THREE.Vector2();

/* ---------- 캐시/헬퍼 ---------- */
const GC={}, MC={};
const geo=(k,f)=>GC[k]||(GC[k]=f());
const mat=(c,o)=>{ const k=c+(o?JSON.stringify(o):""); return MC[k]||(MC[k]=new THREE.MeshLambertMaterial(Object.assign({color:c},o||{}))); };
function bx(w,h,d,c,x,y,z,o){ const m=new THREE.Mesh(geo("b"+w+","+h+","+d,()=>new THREE.BoxGeometry(w,h,d)),mat(c,o)); m.position.set(x||0,y||0,z||0); return m; }
function cy(rt,rb,h,c,x,y,z,o){ const m=new THREE.Mesh(geo("c"+rt+","+rb+","+h,()=>new THREE.CylinderGeometry(rt,rb,h,16)),mat(c,o)); m.position.set(x||0,y||0,z||0); return m; }
function sp(r,c,x,y,z,o){ const m=new THREE.Mesh(geo("s"+r,()=>new THREE.SphereGeometry(r,14,10)),mat(c,o)); m.position.set(x||0,y||0,z||0); return m; }
function tor(r,t,c,x,y,z,o){ const m=new THREE.Mesh(geo("t"+r+","+t,()=>new THREE.TorusGeometry(r,t,8,24)),mat(c,o)); m.position.set(x||0,y||0,z||0); return m; }
function put(g){ for(let i=1;i<arguments.length;i++) g.add(arguments[i]); return g; }
const GLASS={transparent:true,opacity:.35};
const rnd=(a,b)=>a+Math.random()*(b-a);

/* ---------- 캐릭터 ---------- */
const shadowMat=new THREE.MeshBasicMaterial({color:0x000000,transparent:true,opacity:.16,depthWrite:false});
function makeChar(r,isPI){
  const g=new THREE.Group(), body=new THREE.Group(); g.add(body);
  const sh=new THREE.Mesh(geo("sh",()=>new THREE.CircleGeometry(.36,16)),shadowMat); sh.rotation.x=-PI/2; sh.position.y=.012; g.add(sh);
  const leg=(sx)=>{ const p=new THREE.Group(); p.position.set(sx,.5,0); p.add(bx(.16,.5,.16,"#94a3b8",0,-.25,0)); p.add(bx(.18,.07,.25,"#f8fafc",0,-.47,.03)); body.add(p); return p; };
  const legL=leg(-.12), legR=leg(.12);
  body.add(bx(.5,.56,.3,"#ffffff",0,.78,0));
  body.add(bx(.2,.38,.02,r.shirt,0,.8,.155));
  const arm=(sx)=>{ const p=new THREE.Group(); p.position.set(sx,1.02,0); p.add(bx(.13,.46,.13,"#ffffff",0,-.23,0)); p.add(sp(.07,r.skin,0,-.5,0)); body.add(p); return p; };
  const armL=arm(-.33), armR=arm(.33);
  const head=new THREE.Group(); head.position.y=1.32; body.add(head);
  head.add(sp(.25,r.skin,0,0,0));
  head.add(sp(.035,"#222222",-.09,.02,.225), sp(.035,"#222222",.09,.02,.225));
  head.add(sp(.035,"#fca5a5",-.16,-.06,.19), sp(.035,"#fca5a5",.16,-.06,.19));
  head.add(bx(.08,.016,.01,"#b45454",0,-.1,.245));
  const hc=r.hc, cap=(c)=>{ const m=new THREE.Mesh(geo("hair",()=>new THREE.SphereGeometry(.275,16,10,0,TAU,0,PI*.56)),mat(c)); m.position.y=.01; return m; };
  switch(r.hair){
    case "short": head.add(cap(hc)); break;
    case "long": head.add(cap(hc)); head.add(bx(.5,.55,.14,hc,0,-.2,-.19)); break;
    case "bun": head.add(cap(hc)); head.add(sp(.11,hc,0,.3,-.06)); break;
    case "curly": head.add(cap(hc)); for(let i=0;i<8;i++){ const a=i/8*TAU; head.add(sp(.1,hc,Math.cos(a)*.2,.16,Math.sin(a)*.2)); } head.add(sp(.12,hc,0,.27,0)); break;
    case "bald": head.add(sp(.065,hc,-.25,0,-.02), sp(.065,hc,.25,0,-.02)); break;
    case "white": head.add(cap("#f3f4f6")); head.add(bx(.5,.3,.12,"#f3f4f6",0,-.05,-.2)); break;
    case "side": { const c=cap(hc); c.rotation.z=.22; head.add(c); break; }
  }
  if(r.acc==="glasses"){ head.add(tor(.065,.012,"#334155",-.09,.02,.236), tor(.065,.012,"#334155",.09,.02,.236), bx(.06,.012,.012,"#334155",0,.03,.24)); }
  if(r.acc==="goggles"){ const b=new THREE.Mesh(geo("gog",()=>new THREE.CylinderGeometry(.262,.262,.07,16,1,true)),new THREE.MeshLambertMaterial({color:"#60a5fa",side:THREE.DoubleSide})); b.position.y=.12; head.add(b); head.add(bx(.2,.08,.02,"#93c5fd",0,.12,.262)); }
  if(r.acc==="tie") body.add(bx(.07,.28,.02,"#dc2626",0,.78,.17));
  if(r.acc==="medal") body.add(sp(.05,"#fbbf24",.13,.92,.17));
  if(r.flask){ const f=new THREE.Group(); f.position.set(0,-.56,.1); f.add(cy(.02,.09,.16,"#5eead4",0,0,0,{emissive:"#14b8a6",emissiveIntensity:.25}), cy(.025,.025,.1,"#ccfbf1",0,.12,0)); armR.add(f); }
  const hb=new THREE.Mesh(geo("hb",()=>new THREE.BoxGeometry(.8,1.8,.8)),new THREE.MeshBasicMaterial({visible:false})); hb.position.y=.9; g.add(hb);
  const a={g,body,legL,legR,armL,armR,head,hb,roleId:r.id,isPI:!!isPI,ph:rnd(0,6),wt:0,off:rnd(0,6),state:"idle",t:rnd(.2,1.5),tx:0,tz:0,spot:null,face:null,pop:0,jump:0};
  hb.userData.who=a; hitboxes.push(hb);
  return a;
}
function animChar(a,dt,walking,working){
  const s=walking?Math.sin(a.ph):0;
  a.legL.rotation.x=s*.75; a.legR.rotation.x=-s*.75;
  if(working){ a.wt+=dt*6; a.armL.rotation.x=-1.05+Math.sin(a.wt)*.35; a.armR.rotation.x=-1.05+Math.cos(a.wt*1.1)*.35; }
  else { a.armL.rotation.x=-s*.7; a.armR.rotation.x=s*.7; }
  const bob=walking?Math.abs(Math.sin(a.ph))*.06:Math.sin(time*2+a.off)*.015;
  let jy=0; if(a.jump>0){ a.jump-=dt; jy=Math.sin(clamp01(1-a.jump/.35)*PI)*.4; if(a.jump<0) a.jump=0; }
  a.body.position.y=bob+jy;
}
const clamp01=v=>v<0?0:v>1?1:v;
function popScale(a,dt){
  if(a.pop<1){ a.pop=Math.min(1,a.pop+dt*2.2); const t=a.pop-1, k=1+2.7*t*t*t+1.7*t*t; a.g.scale.setScalar(Math.max(.01,k)); }
}
function pickTarget(a){
  if(spots.length && Math.random()<.65){
    let s=spots[Math.floor(Math.random()*spots.length)]; if(s===a.spot&&spots.length>1) s=spots[(spots.indexOf(s)+1)%spots.length];
    a.spot=s; a.tx=s.x+rnd(-.12,.12); a.tz=s.z+rnd(-.08,.08);
  } else {
    a.spot=null;
    for(let i=0;i<8;i++){ const x=rnd(-R+.9,R-.9), z=rnd(-R+1.6,R-.9); if(!(Math.abs(x)<1.7&&z<1.0&&z>-1.5)){ a.tx=x; a.tz=z; break; } }
  }
  a.state="walk"; a.face=null;
}
function stepAgent(a,dt){
  popScale(a,dt);
  const g=a.g; let walking=false, working=false, ry=g.rotation.y;
  if(a.state==="walk"){
    const dx=a.tx-g.position.x, dz=a.tz-g.position.z, d=Math.hypot(dx,dz);
    if(d<.07){ if(a.spot){ a.state="work"; a.t=rnd(4,9); a.face=a.spot.face; } else { a.state="idle"; a.t=rnd(1,2.5); a.face=null; } }
    else { const sp=1.15*dt; g.position.x+=dx/d*Math.min(sp,d); g.position.z+=dz/d*Math.min(sp,d); a.ry=Math.atan2(dx,dz); walking=true; a.ph+=dt*9; }
  } else {
    a.t-=dt; if(a.face!=null) a.ry=a.face; working=a.state==="work";
    if(a.t<=0) pickTarget(a);
  }
  if(a.ry!=null){ let da=a.ry-ry; while(da>PI) da-=TAU; while(da<-PI) da+=TAU; g.rotation.y=ry+da*Math.min(1,dt*10); }
  animChar(a,dt,walking,working);
}

/* ---------- 장비 ---------- */
const LED_ON=mat("#4ade80",{emissive:"#22c55e"}), LED_OFF=mat("#475569");
function server(col){ const g=new THREE.Group(); g.add(bx(.62,1.5,.6,col,0,.75,0)); g.add(bx(.5,1.3,.02,"#334155",0,.75,.31));
  for(let i=0;i<7;i++){ const l=bx(.34,.05,.02,"#fff",-.04,.25+i*.18,.325); l.material=LED_OFF; g.add(l); const ph=rnd(0,6)+i; anim.push((t)=>{ l.material=Math.sin(t*(3+i%3)+ph)>0?LED_ON:LED_OFF; }); g.add(bx(.06,.06,.02,"#f9a8d4",.2,.25+i*.18,.325)); }
  return g; }
const EQUIP=[
 {id:"r0_1",build(){ const g=new THREE.Group(); g.add(bx(1.1,.08,.6,"#fcd9b6",0,.72,0)); [[-.5,-.25],[.5,-.25],[-.5,.25],[.5,.25]].forEach(p=>g.add(bx(.07,.7,.07,"#d6b38c",p[0],.35,p[1])));
    g.add(bx(.3,.02,.2,"#cbd5e1",-.2,.77,0), bx(.3,.2,.02,"#1e293b",-.2,.87,-.1)); g.add(cy(.17,.17,.06,"#fbcfe8",.2,.5,.5), bx(.3,.28,.04,"#fbcfe8",.2,.7,.66), cy(.03,.03,.45,"#94a3b8",.2,.25,.5)); return g; }},
 {id:"r1_0",build(){ const g=new THREE.Group(); g.add(bx(1,.8,.7,"#c4b5fd",0,.4,0), bx(.72,.5,.55,"#ffffff",0,1.05,0), bx(.42,.3,.02,"#bae6fd",0,1.05,.285,{emissive:"#7dd3fc",emissiveIntensity:.3}));
    const t=cy(.06,.06,.5,"#94a3b8",.45,1.05,.1); t.rotation.z=PI/2; g.add(t, sp(.05,"#f87171",-.3,.84,.36)); return g; }},
 {id:"r1_1",build(){ const g=new THREE.Group(); g.add(bx(.95,.6,.7,"#99f6e4",0,.3,0), cy(.26,.3,.9,"#ffffff",0,1.05,0), cy(.16,.26,.3,"#c4b5fd",0,1.65,0), bx(.4,.28,.03,"#1e293b",.0,.7,.36), bx(.34,.22,.02,"#67e8f9",0,.7,.375,{emissive:"#22d3ee",emissiveIntensity:.5})); return g; }},
 {id:"r2_0",build(){ const g=new THREE.Group(); g.add(bx(1.25,.6,.7,"#e2e8f0",0,.3,0), bx(1.15,.7,.62,"#bae6fd",0,.95,0,GLASS), bx(1.2,.06,.66,"#94a3b8",0,1.31,0));
    [-.28,.28].forEach(x=>{ const gl=cy(.09,.09,.32,"#f9a8d4",x,.95,.34); gl.rotation.x=PI/2; g.add(gl); }); return g; }},
 {id:"r2_1",build(){ const g=new THREE.Group(); g.add(bx(.95,.5,.8,"#e2e8f0",0,.25,0), cy(.28,.3,1.4,"#c4b5fd",0,1.2,0)); [.8,1.2,1.6].forEach(y=>g.add(cy(.34,.34,.06,"#ffffff",0,y,0))); g.add(cy(.14,.2,.3,"#f9a8d4",0,2.05,0), bx(.3,.2,.03,"#1e293b",0,.55,.41)); return g; }},
 {id:"r3_0",build(){ const g=new THREE.Group(); g.add(bx(.95,1.1,.7,"#fde68a",0,.55,0), bx(.62,.72,.02,"#bae6fd",0,.6,.36,{emissive:"#7dd3fc",emissiveIntensity:.25}), bx(.3,.2,.02,"#34d399",.28,1.0,.36));
    const p=cy(.04,.04,.7,"#94a3b8",-.55,.7,0); g.add(p, cy(.04,.04,.5,"#94a3b8",-.55,1.35,0)); return g; }},
 {id:"r3_1",build(){ return server("#a5b4fc"); }},
 {id:"r4_0",build(){ const g=new THREE.Group(); g.add(bx(1.5,.05,1.2,"#bae6fd",0,.03,0), bx(1.5,.06,1.2,"#ffffff",0,1.85,0));
    [[-.72,-.57],[.72,-.57],[-.72,.57],[.72,.57]].forEach(p=>g.add(bx(.06,1.85,.06,"#ffffff",p[0],.92,p[1])));
    g.add(bx(1.44,1.7,.02,"#bae6fd",0,.9,-.58,{transparent:true,opacity:.28}), bx(.02,1.7,1.14,"#bae6fd",-.73,.9,0,{transparent:true,opacity:.28}), bx(.02,1.7,1.14,"#bae6fd",.73,.9,0,{transparent:true,opacity:.28}), bx(1.44,1.7,.02,"#bae6fd",0,.9,.58,{transparent:true,opacity:.18}));
    const f=cy(.22,.22,.05,"#cbd5e1",0,1.92,0); g.add(f); anim.push((t)=>{ f.rotation.y=t*4; }); g.add(bx(.5,.4,.3,"#e9d5ff",0,.2,-.2)); return g; }},
 {id:"r5_0",build(){ const g=new THREE.Group(); g.add(cy(.28,.34,.5,"#e2e8f0",0,.25,0)); const r=tor(.8,.11,"#fdba74",0,.8,0); r.rotation.x=PI/2; g.add(r, cy(.1,.1,.55,"#fb923c",0,.8,0));
    anim.push((t)=>{ r.rotation.z=t*.5; }); [0,1,2,3].forEach(i=>{ const a=i*PI/2; g.add(bx(.12,.12,.12,"#fef08a",Math.cos(a)*.8,.8,Math.sin(a)*.8,{emissive:"#facc15",emissiveIntensity:.5})); }); return g; }},
 {id:"r5_1",build(){ return server("#6ee7b7"); }},
 {id:"r6_0",build(){ const g=new THREE.Group(); g.add(cy(.3,.42,.6,"#e2e8f0",0,.3,0)); const o=sp(.28,"#a78bfa",0,1.15,0,{emissive:"#7c3aed",emissiveIntensity:.6}); g.add(o); const r=tor(.4,.02,"#ddd6fe",0,1.15,0,{emissive:"#a78bfa"}); g.add(r);
    anim.push((t)=>{ r.rotation.x=t*1.3; r.rotation.y=t*.8; o.scale.setScalar(1+Math.sin(t*3)*.07); }); return g; }},
 {id:"r7_0",build(){ const g=new THREE.Group(); g.add(cy(.45,.55,.5,"#fbcfe8",0,.25,0), cy(.35,.45,.6,"#c4b5fd",0,.8,0), cy(.22,.35,.7,"#99f6e4",0,1.45,0));
    const o=sp(.18,"#fde68a",0,2.0,0,{emissive:"#facc15",emissiveIntensity:.7}); const r=tor(.4,.03,"#fef08a",0,1.8,0,{emissive:"#facc15"}); r.rotation.x=PI/2; g.add(o,r); anim.push((t)=>{ r.rotation.z=t*1.5; o.position.y=2.0+Math.sin(t*2)*.05; }); return g; }}
];
const MINOR=["c1","c2","c3","k1","k2","c4","k3"];
function minor(id,benchG){
  const Y=1.01;
  switch(id){
    case "c1": [-1.05,-.9,-.76].forEach((x,i)=>{ benchG.add(cy(.07,.07,.22,"#e0f2fe",x,Y+.11,.1,GLASS), cy(.062,.062,.09,["#5eead4","#f9a8d4","#fde68a"][i],x,Y+.05,.1)); }); break;
    case "c2": benchG.add(bx(.3,.06,.24,"#e2e8f0",-.5,Y+.03,.05), cy(.1,.1,.02,"#ffffff",-.5,Y+.07,.05), bx(.1,.05,.02,"#34d399",-.5,Y+.04,.18)); break;
    case "c3": benchG.add(cy(.13,.13,.08,"#c4b5fd",-.15,Y+.04,.05), cy(.07,.07,.17,"#e0f2fe",-.15,Y+.17,.05,GLASS)); break;
    case "k1": benchG.add(bx(.34,.24,.03,"#1e293b",.35,Y+.22,-.15), bx(.3,.2,.02,"#67e8f9",.35,Y+.22,-.13,{emissive:"#22d3ee",emissiveIntensity:.5}), bx(.05,.1,.05,"#94a3b8",.35,Y+.05,-.15)); break;
    case "k2": benchG.add(bx(.34,.24,.03,"#1e293b",.78,Y+.22,-.15), bx(.3,.2,.02,"#a5b4fc",.78,Y+.22,-.13,{emissive:"#818cf8",emissiveIntensity:.5}), bx(.05,.1,.05,"#94a3b8",.78,Y+.05,-.15)); break;
    case "c4": benchG.add(bx(.3,.02,.2,"#cbd5e1",1.0,Y+.01,.15), bx(.3,.2,.02,"#1e293b",1.0,Y+.11,.05)); break;
    case "k3": { const r=tor(.28,.025,"#a5f3fc",0,1.85,0,{emissive:"#67e8f9",emissiveIntensity:.8}); r.rotation.x=PI/2; benchG.add(r, sp(.07,"#67e8f9",0,1.85,0,{emissive:"#22d3ee"})); anim.push((t)=>{ r.rotation.z=t*1.2; }); break; }
  }
}

/* ---------- 방 ---------- */
function clearG(g){ while(g.children.length) g.remove(g.children[0]); }
function floorTex(n){
  const c=document.createElement("canvas"); c.width=c.height=64; const x=c.getContext("2d");
  x.fillStyle="#a7f3d0"; x.fillRect(0,0,64,64); x.fillStyle="#d1fae5"; x.fillRect(0,0,32,32); x.fillRect(32,32,32,32);
  const t=new THREE.CanvasTexture(c); t.wrapS=t.wrapT=THREE.RepeatWrapping; t.repeat.set(n,n); t.magFilter=THREE.NearestFilter; return t;
}
function signTex(){
  const c=document.createElement("canvas"); c.width=512; c.height=128; const x=c.getContext("2d");
  x.fillStyle="#ffffff"; x.fillRect(0,0,512,128); x.fillStyle="#99f6e4"; x.fillRect(8,8,496,112);
  x.fillStyle="#0f766e"; x.font="900 64px sans-serif"; x.textAlign="center"; x.textBaseline="middle"; x.fillText("HOPE LAB",256,68);
  return new THREE.CanvasTexture(c);
}
function windowAt(g,x,z,rot){ const w=new THREE.Group(); w.add(bx(1.15,.95,.07,"#ffffff",0,0,0), bx(.98,.78,.08,"#bae6fd",0,0,0,{emissive:"#bae6fd",emissiveIntensity:.35}), bx(.04,.78,.09,"#ffffff"), bx(.98,.04,.09,"#ffffff")); w.position.set(x,1.6,z); w.rotation.y=rot; g.add(w); }
function plant(g,x,z){ g.add(cy(.22,.17,.32,"#fda4af",x,.16,z)); [[0,.55,0,.26],[.14,.45,.08,.18],[-.13,.48,-.06,.19]].forEach(p=>g.add(sp(p[3],"#86efac",x+p[0],p[1],z+p[2]))); }
function buildRoom(R_,eqIds,minIds){
  R=R_; clearG(roomG); clearG(propG); spots=[]; anim.length=0;
  const S2=2*R;
  roomG.add(bx(S2+.5,.3,S2+.5,"#e7dccb",0,-.15,0));
  const fl=new THREE.Mesh(geo("fl"+R,()=>new THREE.PlaneGeometry(S2,S2)),new THREE.MeshLambertMaterial({map:floorTex(Math.round(R*1.2))})); fl.rotation.x=-PI/2; fl.position.y=.002; roomG.add(fl);
  const H=2.7;
  roomG.add(bx(S2+.5,H,.25,"#ffe4e6",0,H/2,-R-.12), bx(.25,H,S2+.5,"#e0f2fe",-R-.12,H/2,0));
  roomG.add(bx(S2+.5,.14,.08,"#ffffff",0,.07,-R+.04), bx(.08,.14,S2,"#ffffff",-R+.04,.07,0));
  for(let x=-R+1.6;x<R-1;x+=3.4) if(Math.abs(x)>1.4) windowAt(roomG,x,-R+.03,0);
  for(let z=-R+1.8;z<R-1;z+=3.4) windowAt(roomG,-R+.03,z,PI/2);
  const sg=new THREE.Mesh(geo("sign",()=>new THREE.PlaneGeometry(2.2,.55)),new THREE.MeshBasicMaterial({map:signTex()})); sg.position.set(0,2.2,-R+.02); roomG.add(sg);
  const clk=cy(.26,.26,.05,"#ffffff",R-1.1,2.1,-R+.05); clk.rotation.x=PI/2; roomG.add(clk, bx(.03,.2,.02,"#334155",R-1.1,2.14,-R+.09), bx(.14,.03,.02,"#334155",R-1.04,2.1,-R+.09));
  roomG.add(bx(.04,1,.75,"#fef3c7",-R+.04,1.6,.6+(R>4?1.2:0)), sp(.09,"#f9a8d4",-R+.1,1.75,.45+(R>4?1.2:0)), sp(.09,"#a5b4fc",-R+.1,1.45,.75+(R>4?1.2:0)), sp(.07,"#86efac",-R+.1,1.6,.6+(R>4?1.2:0)));
  const rug=cy(1.7,1.7,.02,"#fecdd3",0,.02,.95); roomG.add(rug);
  plant(roomG,R-.55,-R+.55); plant(roomG,-R+.55,R-.55);
  // 중앙 실험대 (PI는 대 뒤에서 앞을 보고 서 있음)
  const bn=new THREE.Group(); bn.add(bx(2.7,.12,.95,"#fcd9b6",0,.95,0), bx(2.6,.08,.85,"#e7c9a5",0,.35,0)); [[-1.25,-.4],[1.25,-.4],[-1.25,.4],[1.25,.4]].forEach(p=>bn.add(bx(.1,.9,.1,"#d6b38c",p[0],.45,p[1])));
  bn.add(bx(1.4,.04,.5,"#ccfbf1",.1,1.02,.0)); // 매트
  minIds.forEach(id=>minor(id,bn)); propG.add(bn);
  [-1.0,0,1.0].forEach(x=>spots.push({x,z:.95,face:PI}));
  // 장비 배치
  const slots=[]; const step=1.5;
  for(let x=-R+1.1;x<=R-.8;x+=step) slots.push({x,z:-R+.8,rot:0});
  for(let z=-R+2.3;z<=R-1.0;z+=step) slots.push({x:-R+.8,z,rot:PI/2});
  eqIds.forEach((id,i)=>{ const s=slots[i]; if(!s) return; const e=EQUIP.find(q=>q.id===id); const g=e.build(); g.position.set(s.x,0,s.z); g.rotation.y=s.rot; propG.add(g);
    const fx=Math.sin(s.rot)*1.0, fz=Math.cos(s.rot)*1.0; spots.push({x:s.x+fx,z:s.z+fz,face:s.rot+PI}); });
  fitCam();
}

/* ---------- PI / 연구원 ---------- */
let piRole=null;
function ensurePI(role){
  if(piA) return; piRole=role; piA=makeChar(role,true); piA.g.position.set(0,0,-.85); piA.g.rotation.y=0; piA.state="pi"; piA.pop=0; agentG.add(piA.g);
}
function stepPI(dt){
  if(!piA) return; popScale(piA,dt);
  const a=piA; a.wt+=dt;
  a.armR.rotation.x=-.9+Math.sin(time*3)*.22; a.armR.rotation.z=Math.cos(time*3)*.12; a.armL.rotation.x=-.5+Math.sin(time*1.7)*.12;
  a.legL.rotation.x=a.legR.rotation.x=0;
  const bob=Math.sin(time*2)*.012; let jy=0; if(a.jump>0){ a.jump-=dt; jy=Math.sin(clamp01(1-a.jump/.35)*PI)*.45; if(a.jump<0)a.jump=0; }
  a.body.position.y=bob+jy;
}
function spawnAgent(role){
  const a=makeChar(role,false); a.g.position.set(rnd(-R+1,R-1),0,R-.8); a.g.scale.setScalar(.01); a.pop=0; agentG.add(a.g); agents.push(a); pickTarget(a); return a;
}
function removeAgent(a){ agentG.remove(a.g); const i=agents.indexOf(a); if(i>=0) agents.splice(i,1); const h=hitboxes.indexOf(a.hb); if(h>=0) hitboxes.splice(h,1); }
const CAP=[4,4,4,3,3,3,3,3], TOTAL=18;
function syncAgents(o){
  const want=o.roles.map(()=>0); let left=TOTAL;
  for(let i=o.roles.length-1;i>=0;i--){ const c=Math.min(o.owned[i]||0,CAP[i]||3,left); want[i]=c; left-=c; }
  o.roles.forEach((r,i)=>{
    const mine=agents.filter(a=>a.roleId===i);
    for(let k=mine.length;k<want[i];k++) spawnAgent(r);
    for(let k=mine.length;k>want[i];k--) removeAgent(mine[k-1]);
  });
}
L.sync=function(o){
  if(!renderer||!o) return;
  const nAll=["g1","g2","g3","g4","g5"].filter(id=>o.upg[id]).length;
  const eq=EQUIP.filter(e=>o.upg[e.id]).map(e=>e.id), mi=MINOR.filter(id=>o.upg[id]);
  const newR=Math.min(7.4,3.4+.4*nAll+.15*eq.length);
  const sig=newR.toFixed(2)+"|"+eq.join(",")+"|"+mi.join(",");
  if(sig!==sigRoom){ sigRoom=sig; buildRoom(newR,eq,mi); agents.forEach(a=>{ a.spot=null; if(a.state!=="walk") pickTarget(a); }); }
  ensurePI(o.pi);
  syncAgents(o);
};
L.jumpPI=function(){ if(piA){ piA.jump=.35; burst(0,1.9,-.85); } };

/* ---------- 효과 ---------- */
function burst(x,y,z){
  for(let i=0;i<6;i++){ const m=sp(.05,["#fde68a","#f9a8d4","#99f6e4","#c4b5fd"][i%4],x,y,z); const mm=m.clone(); fxG.add(mm); parts.push({m:mm,vx:rnd(-1,1),vy:rnd(1.5,2.6),vz:rnd(-1,1),life:.7}); }
}
function stepFx(dt){
  for(let i=parts.length-1;i>=0;i--){ const p=parts[i]; p.life-=dt; p.vy-=6*dt; p.m.position.x+=p.vx*dt; p.m.position.y+=p.vy*dt; p.m.position.z+=p.vz*dt; p.m.scale.setScalar(Math.max(.01,p.life/.7));
    if(p.life<=0){ fxG.remove(p.m); parts.splice(i,1); } }
}

/* ---------- 카메라 ---------- */
function fitCam(){
  if(!canvas||!camera) return;
  const w=canvas.clientWidth||300, h=canvas.clientHeight||360, asp=w/h, tv=Math.tan(camera.fov*PI/360);
  const dH=(R*1.5+.9)/(tv*Math.min(asp,1.6)), dV=(R*1.65*Math.cos(cam.pol)+3.4)/(2*tv)+R*.35;
  cam.target=Math.max(dH,dV)*.95;
}
function updCam(){
  const d=cam.dist*cam.zoom, sp_=Math.sin(cam.pol);
  camera.position.set(d*sp_*Math.sin(cam.az),d*Math.cos(cam.pol)+.5,d*sp_*Math.cos(cam.az));
  camera.lookAt(0,.6,0);
}
function resize(){
  if(!host||!renderer) return;
  const w=host.clientWidth, h=host.clientHeight; if(!w||!h) return;
  renderer.setSize(w,h,false); canvas.style.width=w+"px"; canvas.style.height=h+"px";
  camera.aspect=w/h; camera.updateProjectionMatrix(); fitCam();
}

/* ---------- 입력 ---------- */
const ptr=new Map(); let down=null, pinch0=0, zoom0=1;
function onDown(e){
  canvas.setPointerCapture&&canvas.setPointerCapture(e.pointerId);
  ptr.set(e.pointerId,{x:e.clientX,y:e.clientY});
  if(ptr.size===1) down={x:e.clientX,y:e.clientY,t:performance.now(),moved:0};
  else if(ptr.size===2){ const p=[...ptr.values()]; pinch0=Math.hypot(p[0].x-p[1].x,p[0].y-p[1].y); zoom0=cam.zoom; if(down) down.moved=99; }
}
function onMove(e){
  const p=ptr.get(e.pointerId); if(!p) return;
  const dx=e.clientX-p.x, dy=e.clientY-p.y; p.x=e.clientX; p.y=e.clientY;
  if(ptr.size===1){ if(down) down.moved+=Math.abs(dx)+Math.abs(dy);
    if(down&&down.moved>8){ cam.az=Math.max(.15,Math.min(1.45,cam.az-dx*.008)); cam.pol=Math.max(.55,Math.min(1.25,cam.pol-dy*.006)); fitCam(); } }
  else if(ptr.size===2){ const q=[...ptr.values()], d=Math.hypot(q[0].x-q[1].x,q[0].y-q[1].y); if(pinch0>0) cam.zoom=Math.max(.5,Math.min(1.35,zoom0*pinch0/d)); }
}
function onUp(e){
  const had=ptr.delete(e.pointerId);
  if(had&&down&&ptr.size===0){ const tap=down.moved<10&&performance.now()-down.t<600; const d=down; down=null; if(tap) doTap(e.clientX,e.clientY); }
  if(ptr.size===0) pinch0=0;
}
function doTap(cx,cy){
  const rc=canvas.getBoundingClientRect(); ndc.set(((cx-rc.left)/rc.width)*2-1,-((cy-rc.top)/rc.height)*2+1);
  ray.setFromCamera(ndc,camera); const h=ray.intersectObjects(hitboxes,false); if(!h.length) return;
  const a=h[0].object.userData.who; a.jump=.35;
  if(a.isPI){ burst(0,1.9,-.85); L.onPI&&L.onPI(cx,cy); } else { L.onMate&&L.onMate(a.roleId,cx,cy); }
}
function onWheel(e){ e.preventDefault(); cam.zoom=Math.max(.5,Math.min(1.35,cam.zoom*(e.deltaY>0?1.08:.93))); }

/* ---------- 루프 ---------- */
function frame(ts){
  if(!running) return; raf=requestAnimationFrame(frame);
  const dt=(ts-last)/1000; if(dt<1/31) return; last=ts;
  update(Math.min(dt,.1)); if(!lost) renderer.render(scene,camera);
}
function update(dt){
  time+=dt;
  for(const a of agents) stepAgent(a,dt);
  stepPI(dt); for(const f of anim) f(time,dt); stepFx(dt);
  cam.dist+=(cam.target-cam.dist)*Math.min(1,dt*3); updCam();
}

/* ---------- 공개 API ---------- */
L.init=function(){
  if(renderer) return true;
  try{
    renderer=new THREE.WebGLRenderer({antialias:true,alpha:true,powerPreference:"low-power"});
    renderer.setPixelRatio(Math.min(window.devicePixelRatio||1,2)); renderer.setClearColor(0x000000,0);
    canvas=renderer.domElement; canvas.style.display="block"; canvas.style.touchAction="none";
    canvas.addEventListener("pointerdown",onDown); canvas.addEventListener("pointermove",onMove); canvas.addEventListener("pointerup",onUp); canvas.addEventListener("pointercancel",onUp); canvas.addEventListener("wheel",onWheel,{passive:false});
    canvas.addEventListener("webglcontextlost",e=>{ e.preventDefault(); lost=true; }); canvas.addEventListener("webglcontextrestored",()=>{ lost=false; });
    scene=new THREE.Scene(); camera=new THREE.PerspectiveCamera(38,1,.5,120);
    scene.add(new THREE.AmbientLight(0xffffff,.78)); const dl=new THREE.DirectionalLight(0xffffff,.55); dl.position.set(5,10,6); scene.add(dl);
    roomG=new THREE.Group(); propG=new THREE.Group(); agentG=new THREE.Group(); fxG=new THREE.Group(); scene.add(roomG,propG,agentG,fxG);
    L.ok=true; return true;
  }catch(e){ renderer=null; L.ok=false; return false; }
};
L.attach=function(el){
  if(!L.init()) return false;
  host=el; host.appendChild(canvas); resize();
  if(ro) ro.disconnect(); if(window.ResizeObserver){ ro=new ResizeObserver(resize); ro.observe(host); }
  cam.dist=cam.target; running=true; last=performance.now(); cancelAnimationFrame(raf); raf=requestAnimationFrame(frame); return true;
};
L.detach=function(){
  running=false; cancelAnimationFrame(raf); if(ro){ ro.disconnect(); ro=null; }
  if(canvas&&canvas.parentNode) canvas.parentNode.removeChild(canvas); host=null; ptr.clear(); down=null;
};
})();
