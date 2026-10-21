// 灯影 · 原型
// 横版过关：小孩提灯行走；按 E 把灯放在地上，自己的影子投到幕布上成为大皮影。
// 放下灯以后人还能前后左右走：离灯越近影子越大，左右走影子跟着平移；拖动影子的手操作幕布上的机关。
// 规则：影子只能碰幕布上的东西。
(async function () {
'use strict';

// ---------- 常量（虚拟坐标：画面高度固定 720） ----------
const VH = 720;
const CLOTH_TOP = 34, CLOTH_FLOOR = 470;   // 幕布上下沿
const GROUND_Y = 566;                      // 人物所在的“走道”地面
const GIRL_H = 112;                        // 小人身高
const LAMP_H = 24;                         // 灯芯离地高度
// 纵深：z 为到幕布的距离。人在 [Z_BACK, Z_FRONT] 之间前后走，放下的灯总在更靠前的 Z_LAMP
const Z_BACK = 0.6, Z_FRONT = 1.3, Z_LANE = 1.0, Z_LAMP = 1.62;
const DEPTH_PX = (GROUND_Y - CLOTH_FLOOR) / Z_LANE; // 每单位纵深在画面上的下移量
const depthY = (z) => CLOTH_FLOOR + z * DEPTH_PX;
const DEPTH_SPEED = 0.85;
const PICKUP_DIST = 80;
const GRAV = 2300, JUMP_V = 790, SPEED = 235;
const LEVEL_W = 3350;
const D2R = Math.PI / 180;

// ---------- 2D 仿射矩阵 [a,b,c,d,e,f]（与 canvas setTransform 一致） ----------
const mul = (a, b) => [
  a[0] * b[0] + a[2] * b[1], a[1] * b[0] + a[3] * b[1],
  a[0] * b[2] + a[2] * b[3], a[1] * b[2] + a[3] * b[3],
  a[0] * b[4] + a[2] * b[5] + a[4], a[1] * b[4] + a[3] * b[5] + a[5]];
const inv = (m) => {
  const d = m[0] * m[3] - m[1] * m[2];
  return [m[3] / d, -m[1] / d, -m[2] / d, m[0] / d, (m[2] * m[5] - m[3] * m[4]) / d, (m[1] * m[4] - m[0] * m[5]) / d];
};
const ap = (m, p) => ({ x: m[0] * p.x + m[2] * p.y + m[4], y: m[1] * p.x + m[3] * p.y + m[5] });
const T = (x, y) => [1, 0, 0, 1, x, y];
const R = (t) => { const c = Math.cos(t), s = Math.sin(t); return [c, s, -s, c, 0, 0]; };
const S = (x, y) => [x, 0, 0, y === undefined ? x : y, 0, 0];
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const lerp = (a, b, t) => a + (b - a) * t;
const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
const wrapA = (a) => { while (a > Math.PI) a -= 2 * Math.PI; while (a < -Math.PI) a += 2 * Math.PI; return a; };

// ---------- 读取 woop 骨骼 ----------
async function loadRig(base) {
  const j = await (await fetch(base + 'woop.json')).json();
  const parts = {}, roleOf = {};
  for (const [role, id] of Object.entries(j.rigSemantics.roles)) roleOf[id] = role;
  const loads = [];
  for (const p of j.parts) {
    const asset = j.partAssets[p.id].items[j.partAssets[p.id].defaultAssetId];
    const img = new Image();
    loads.push(new Promise((ok, bad) => { img.onload = ok; img.onerror = bad; }));
    img.src = base + asset.path;
    parts[p.id] = {
      id: p.id, role: roleOf[p.id], w: p.width, h: p.height, z: p.rest.zIndex, rest: p.rest.matrix.slice(), img,
      anchors: Object.fromEntries(p.anchors.map(a => [a.id, { x: a.partPx[0], y: a.partPx[1] }])),
      parent: null, pivot: null, rel: null,
    };
  }
  for (const jt of j.joints) {
    const c = parts[jt.child.partId], pa = parts[jt.parent.partId];
    c.parent = pa.id;
    c.pivot = pa.anchors[jt.parent.anchorId];
    c.rel = mul(inv(pa.rest), c.rest);
  }
  const order = [], seen = new Set();
  const visit = (id) => { if (seen.has(id)) return; const p = parts[id]; if (p.parent) visit(p.parent); seen.add(id); order.push(id); };
  Object.keys(parts).forEach(visit);
  const byRole = {};
  for (const p of Object.values(parts)) byRole[p.role] = p;
  const drawOrder = Object.values(parts).sort((a, b) => a.z - b.z);
  await Promise.all(loads);
  const rig = { parts, order, byRole, drawOrder };
  // 静止姿态包围盒
  const W = fk(rig, {});
  let minX = 1e9, maxX = -1e9, minY = 1e9, maxY = -1e9;
  for (const p of drawOrder) for (const c of [[0, 0], [p.w, 0], [0, p.h], [p.w, p.h]]) {
    const q = ap(W[p.id], { x: c[0], y: c[1] });
    minX = Math.min(minX, q.x); maxX = Math.max(maxX, q.x); minY = Math.min(minY, q.y); maxY = Math.max(maxY, q.y);
  }
  const torso = byRole.upperTorso;
  rig.cx = ap(W[torso.id], { x: torso.w / 2, y: torso.h / 2 }).x;
  rig.footY = maxY; rig.height = maxY - minY;
  return rig;
}

// 正向运动学：angles 以角色名为键（弧度），返回每个部件的世界矩阵（骨骼空间）
function fk(rig, angles) {
  const W = {};
  for (const id of rig.order) {
    const p = rig.parts[id];
    if (!p.parent) { W[id] = p.rest; continue; }
    const pv = p.pivot, a = angles[p.role] || 0;
    W[id] = mul(W[p.parent], mul(T(pv.x, pv.y), mul(R(a), mul(T(-pv.x, -pv.y), p.rel))));
  }
  return W;
}

const rig = await loadRig('assets/hero/');
const P = rig.byRole;
const ARMS = [
  { upper: 'rightUpperArm', lower: 'rightLowerArm', hand: 'rightHand' }, // 前面的手（提灯的手）
  { upper: 'leftUpperArm', lower: 'leftLowerArm', hand: 'leftHand' },    // 后面的手
];
const handCenterLocal = (arm) => { const h = P[arm.hand]; return { x: h.w / 2, y: h.h * 0.55 }; };

// 两段骨骼 IK：让手掌中心到达 target（骨骼空间）
function solveArm(arm, target, cur) {
  const ang = Object.assign({}, cur, { [arm.upper]: 0, [arm.lower]: 0, [arm.hand]: 0 });
  const W = fk(rig, ang);
  const up = P[arm.upper], lo = P[arm.lower], ha = P[arm.hand];
  const Sh = ap(W[up.parent], up.pivot);
  const E0 = ap(W[up.id], lo.pivot);
  const Wr0 = ap(W[lo.id], ha.pivot);
  // 手掌中心相对手腕的偏移按“手跟小臂同向”近似：把手掌中心当作延长的小臂末端
  const Hc0 = ap(W[ha.id], handCenterLocal(arm));
  const L1 = dist(Sh, E0), L2 = dist(E0, Hc0);
  const dx = target.x - Sh.x, dy = target.y - Sh.y;
  const d = clamp(Math.hypot(dx, dy), Math.abs(L1 - L2) + 1, L1 + L2 - 0.5);
  const base = Math.atan2(dy, dx);
  const a = Math.acos(clamp((L1 * L1 + d * d - L2 * L2) / (2 * L1 * d), -1, 1));
  const tg = { x: Sh.x + Math.cos(base) * d, y: Sh.y + Math.sin(base) * d };
  const eA = { x: Sh.x + L1 * Math.cos(base + a), y: Sh.y + L1 * Math.sin(base + a) };
  const eB = { x: Sh.x + L1 * Math.cos(base - a), y: Sh.y + L1 * Math.sin(base - a) };
  const E = eA.y > eB.y ? eA : eB; // 手肘朝下
  const d1 = wrapA(Math.atan2(E.y - Sh.y, E.x - Sh.x) - Math.atan2(E0.y - Sh.y, E0.x - Sh.x));
  const rot = (p, c, t) => { const s = Math.sin(t), co = Math.cos(t), x = p.x - c.x, y = p.y - c.y; return { x: c.x + x * co - y * s, y: c.y + x * s + y * co }; };
  const H1 = rot(Hc0, Sh, d1);
  const d2 = wrapA(Math.atan2(tg.y - E.y, tg.x - E.x) - Math.atan2(H1.y - E.y, H1.x - E.x));
  return [d1, d2];
}

// ---------- 画布与视口 ----------
const cv = document.getElementById('c'), ctx = cv.getContext('2d');
let dpr = 1, scale = 1, viewW = 1280;
function resize() {
  dpr = Math.min(window.devicePixelRatio || 1, 2);
  const w = window.innerWidth, h = window.innerHeight;
  cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);
  cv.style.width = w + 'px'; cv.style.height = h + 'px';
  scale = cv.height / VH; viewW = cv.width / scale;
}
window.addEventListener('resize', resize);
resize();

// 幕布纹理
const clothTex = (() => {
  const c = document.createElement('canvas'); c.width = 256; c.height = 256;
  const g = c.getContext('2d');
  for (let i = 0; i < 2600; i++) {
    g.fillStyle = `rgba(${Math.random() < .5 ? '255,240,210' : '80,50,20'},${Math.random() * 0.06})`;
    g.fillRect(Math.random() * 256, Math.random() * 256, 1 + Math.random() * 2, 1 + Math.random() * 6);
  }
  return c;
})();
const clothPattern = ctx.createPattern(clothTex, 'repeat');

// ---------- 音效：WebAudio 现场合成，不需要音频素材 ----------
const sfx = (() => {
  let ac = null, master = null, noiseBuf = null, muted = false;
  const PENTA = [293.66, 349.23, 392.0, 440.0, 523.25, 587.33, 698.46]; // D 羽调式五声音阶
  function init() {
    if (ac) { if (ac.state === 'suspended') ac.resume(); return; }
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    ac = new AC();
    master = ac.createGain(); master.gain.value = 0.8; master.connect(ac.destination);
    noiseBuf = ac.createBuffer(1, ac.sampleRate * 2, ac.sampleRate);
    const d = noiseBuf.getChannelData(0);
    for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
    // 环境底噪：很轻的风声，缓慢起伏
    const src = ac.createBufferSource(); src.buffer = noiseBuf; src.loop = true;
    const f = ac.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = 380;
    const g = ac.createGain(); g.gain.value = 0.022;
    const lfo = ac.createOscillator(), lg = ac.createGain();
    lfo.frequency.value = 0.07; lg.gain.value = 0.012; lfo.connect(lg).connect(g.gain); lfo.start();
    src.connect(f).connect(g).connect(master); src.start();
  }
  const ok = () => ac && !muted && ac.state === 'running';
  function env(g, t, a, peak, dec) {
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(Math.max(peak, 0.0002), t + a);
    g.gain.exponentialRampToValueAtTime(0.0001, t + a + dec);
  }
  function noise(t, dur, freq, q, peak, type, freqTo) {
    const src = ac.createBufferSource(); src.buffer = noiseBuf;
    const f = ac.createBiquadFilter(); f.type = type || 'bandpass'; f.frequency.setValueAtTime(freq, t); f.Q.value = q;
    if (freqTo) f.frequency.exponentialRampToValueAtTime(freqTo, t + dur);
    const g = ac.createGain(); env(g, t, 0.004, peak, dur);
    src.connect(f).connect(g).connect(master);
    src.start(t, Math.random() * 1.5); src.stop(t + dur + 0.1);
  }
  function tone(t, freq, dur, peak, type, freqTo, attack) {
    const o = ac.createOscillator(); o.type = type || 'triangle';
    o.frequency.setValueAtTime(freq, t);
    if (freqTo) o.frequency.exponentialRampToValueAtTime(freqTo, t + dur);
    const g = ac.createGain(); env(g, t, attack || 0.005, peak, dur);
    o.connect(g).connect(master); o.start(t); o.stop(t + dur + 0.1);
  }
  // 拨弦（像古筝/琵琶的一下）：基音 + 泛音 + 一点拨片噪声
  function pluck(t, freq, peak, dur) {
    peak = peak || 0.16; dur = dur || 1.3;
    tone(t, freq, dur, peak, 'triangle');
    tone(t, freq * 2, dur * 0.45, peak * 0.35, 'sine');
    tone(t, freq * 3.01, dur * 0.2, peak * 0.15, 'sine');
    noise(t, 0.025, freq * 5, 3, peak * 0.4);
  }
  function melody(notes, gap, peak) {
    const t = ac.currentTime + 0.02;
    notes.forEach((n, i) => pluck(t + i * gap, PENTA[n], peak || 0.14, 1.4));
  }
  let lastCreak = 0;
  const api = {
    init,
    toggleMute() { muted = !muted; if (master) master.gain.value = muted ? 0 : 0.8; return muted; },
    get muted() { return muted; },
    step(z) { if (!ok()) return; const t = ac.currentTime; const v = 0.07 + 0.05 * (z || 1);
      noise(t, 0.07, 260 + Math.random() * 120, 1.2, v, 'lowpass'); tone(t, 110 + Math.random() * 20, 0.05, v * 0.5, 'sine'); },
    jump() { if (!ok()) return; const t = ac.currentTime;
      noise(t, 0.18, 700, 1.5, 0.06, 'bandpass', 1800); tone(t, 260, 0.14, 0.05, 'sine', 420); },
    land() { if (!ok()) return; const t = ac.currentTime;
      noise(t, 0.14, 220, 1, 0.22, 'lowpass'); tone(t, 90, 0.1, 0.12, 'sine', 60); },
    lampDown() { if (!ok()) return; const t = ac.currentTime;
      noise(t, 0.05, 1500, 2, 0.08);                          // 灯落地
      noise(t + 0.04, 0.5, 300, 0.8, 0.12, 'lowpass', 900);   // 火苗腾起
      pluck(t + 0.08, PENTA[3], 0.12, 1.6); pluck(t + 0.2, PENTA[5], 0.08, 1.6); },
    lampUp() { if (!ok()) return; const t = ac.currentTime;
      noise(t, 0.3, 900, 0.8, 0.07, 'lowpass', 250); pluck(t, PENTA[5], 0.07, 0.8); pluck(t + 0.1, PENTA[3], 0.06, 0.8); },
    deny() { if (!ok()) return; const t = ac.currentTime; pluck(t, PENTA[0] / 2, 0.12, 0.5); pluck(t + 0.09, PENTA[0] / 2 * 0.94, 0.1, 0.5); },
    grab() { if (!ok()) return; const t = ac.currentTime; noise(t, 0.03, 2600, 4, 0.06); pluck(t, PENTA[2] * 2, 0.04, 0.4); },
    creak() { if (!ok()) return; const t = ac.currentTime; if (t - lastCreak < 0.07) return; lastCreak = t;
      tone(t, 95 + Math.random() * 50, 0.07, 0.05, 'sawtooth'); noise(t, 0.06, 500 + Math.random() * 300, 6, 0.05); },
    clunk() { if (!ok()) return; const t = ac.currentTime;
      noise(t, 0.3, 240, 1, 0.35, 'lowpass'); tone(t, 85, 0.25, 0.25, 'sine', 50); noise(t, 0.04, 2000, 3, 0.08); },
    rumble() { if (!ok()) return; const t = ac.currentTime + 0.15;
      noise(t, 1.3, 160, 1, 0.16, 'lowpass', 90); for (let i = 0; i < 6; i++) noise(t + i * 0.18, 0.05, 700, 4, 0.04); },
    keyGrab() { if (!ok()) return; const t = ac.currentTime;
      [2400, 3150, 2800].forEach((f, i) => tone(t + i * 0.05, f, 0.35, 0.035, 'sine')); },
    lock() { if (!ok()) return; const t = ac.currentTime; noise(t, 0.03, 3500, 5, 0.12); noise(t + 0.08, 0.05, 1800, 4, 0.1); },
    success() { if (!ok()) return; melody([0, 2, 3, 5], 0.13); },
    fall() { if (!ok()) return; const t = ac.currentTime; tone(t, 520, 0.7, 0.08, 'triangle', 110); },
    endTune() { if (!ok()) return; melody([3, 4, 5, 3, 2, 0, 2, 3], 0.22, 0.13); },
    crackle(amt) { if (!ok()) return; const t = ac.currentTime;
      noise(t, 0.012 + Math.random() * 0.02, 1500 + Math.random() * 2500, 3, 0.02 + 0.03 * amt * Math.random()); },
  };
  return api;
})();

// ---------- 关卡 ----------
const GROUNDS = [[-200, 1660], [1860, LEVEL_W + 200]];
const BOXES = [
  { x: 470, y: GROUND_Y - 44, w: 64, h: 44 },
  { x: 680, y: GROUND_Y - 84, w: 64, h: 84 },
  { x: 2050, y: GROUND_Y - 50, w: 70, h: 50 },
];
const gateA = { x: 1170, w: 30, h: 270, open: 0 };
const gateB = { x: 2640, w: 30, h: 270, open: 0 };
const realBridge = { x: 1660, len: 200 };

// 幕布上的机关：h 为离幕布下沿的高度
const lever = { kind: 'lever', x: 1060, h: 215, len: 88, a0: -140 * D2R, a1: -45 * D2R, angle: -140 * D2R, done: false, attached: -1 };
const shadowBridge = { kind: 'bridge', x: 1600, h: 150, len: 160, a0: -90 * D2R, a1: 0, angle: -90 * D2R, done: false, attached: -1 };
const rotators = [lever, shadowBridge];
const key = { home: { x: 2260, y: CLOTH_FLOOR - 360 }, x: 2260, y: CLOTH_FLOOR - 360, held: -1, locked: false };
const lock = { x: 2500, y: CLOTH_FLOOR - 150 };

const solids = () => {
  const s = GROUNDS.map(g => ({ x: g[0], y: GROUND_Y, w: g[1] - g[0], h: 400 }));
  s.push(...BOXES);
  for (const g of [gateA, gateB]) if (g.open < 0.6) s.push({ x: g.x, y: GROUND_Y - g.h, w: g.w, h: g.h });
  if (shadowBridge.angle > -0.12) s.push({ x: realBridge.x - 10, y: GROUND_Y, w: realBridge.len + 20, h: 14 });
  return s;
};

// ---------- 状态 ----------
const girl = { x: 120, y: GROUND_Y, z: Z_LANE, vx: 0, vy: 0, onGround: true, facing: 1, phase: 0, walkAmt: 0 };
let checkpoint = 120;
const sc = GIRL_H / rig.height;
let lit = false, litAmt = 0;
const lamp = { x: 0 };
let pickupHintT = 0, lastStep = 0;
let started = false, litSince = 0;                   // 开场“请打开声音”，点一下才开始（同时解锁音频）
let cur = {}, tgt = {};
const armTargets = [null, null];       // 骨骼空间中的手掌目标
const armDrag = [null, null];          // 正在拖动这只手的 pointerId
const pointers = new Map();            // pointerId -> {x,y} 世界坐标
let camX = 0, time = 0, ended = false, everDraggedHand = false;
let touchMode = false;
const keys = {};
const btn = { jump: false };
const stick = { id: null, x: 0, y: 0 };  // 触屏摇杆，x/y 为 -1..1
const btnOwner = new Map();            // pointerId -> 按钮名

const lampGap = () => Z_LAMP - girl.z;                 // 灯到人的距离
const shadowScale = () => Z_LAMP / lampGap();
// 走道坐标 -> 幕布坐标：以灯芯为中心的均匀放大（人的纵深只影响放大倍数）
function shadowMat() {
  const s = shadowScale();
  return [s, 0, 0, s, (1 - s) * lamp.x, CLOTH_FLOOR - LAMP_H - s * (GROUND_Y - LAMP_H)];
}
function rootMat(bob) {
  return mul(T(girl.x, girl.y + (bob || 0)), mul(S(sc * girl.facing, sc), T(-rig.cx, -rig.footY)));
}
// 走道坐标 -> 画面：按纵深下移，并以脚底为中心做一点近大远小
const persp = (z) => 0.7 + 0.3 * z;
function depthMat() {
  const p = persp(girl.z), fy = girl.y + depthY(girl.z) - GROUND_Y;
  return mul(T(girl.x, fy), mul(S(p), T(-girl.x, -girl.y)));
}

// 放灯 / 拿灯。force：掉坑、通关时直接把灯收回手里
function setLit(on, force) {
  if (on === lit) return;
  if (on) {
    if (!girl.onGround || ended) return;
    lit = true;
    lamp.x = girl.x + girl.facing * 24;
    litSince = time;
    sfx.lampDown();
  } else {
    if (!force && Math.abs(girl.x - lamp.x) > PICKUP_DIST) { pickupHintT = 2.2; sfx.deny(); return; }
    lit = false;
    if (!force) sfx.lampUp();
    armTargets[0] = armTargets[1] = null;
    armDrag[0] = armDrag[1] = null;
    if (key.held >= 0) key.held = -1;
    for (const r of rotators) r.attached = -1;
  }
}

// ---------- 输入 ----------
addEventListener('keydown', (e) => {
  sfx.init();
  if (!started) { started = true; e.preventDefault(); return; }
  const k = e.key.toLowerCase();
  if (!keys[k] && k === 'm') sfx.toggleMute();
  if (!keys[k] && (k === 'e' || k === 'f' || k === 'shift')) setLit(!lit);
  if (!keys[k] && k === ' ') tryJump();
  keys[k] = true;
  if ([' ', 'arrowup', 'arrowdown', 'arrowleft', 'arrowright'].includes(k)) e.preventDefault();
});
addEventListener('keyup', (e) => { keys[e.key.toLowerCase()] = false; });

function toVirtual(e) {
  const r = cv.getBoundingClientRect();
  return { x: (e.clientX - r.left) * dpr / scale, y: (e.clientY - r.top) * dpr / scale };
}
function buttons() {
  const pad = 110;
  return [
    { id: 'jump', x: viewW - pad - 60, y: VH - 120, r: 62, label: '跳' },
    { id: 'lamp', x: viewW - pad - 205, y: VH - 95, r: 52, label: lit ? '拿灯' : '放灯' },
  ];
}
// 触屏摇杆：平时停在左下（离边缘留足空间）；手指按在左半屏下方任意位置，就以按下点为中心
const STICK_HOME = { x: 250, y: VH - 160 };
const STICK = { x: STICK_HOME.x, y: STICK_HOME.y, r: 105 };
function setStick(v) {
  let dx = (v.x - STICK.x) / STICK.r, dy = (v.y - STICK.y) / STICK.r;
  const m = Math.hypot(dx, dy);
  if (m > 1) { dx /= m; dy /= m; }
  stick.x = dx; stick.y = dy;
}
function handPositions() {
  if (!lit) return [];
  const M0 = mul(shadowMat(), rootMat());
  const W = fk(rig, cur);
  return ARMS.map(a => ap(mul(M0, W[P[a.hand].id]), handCenterLocal(a)));
}

cv.addEventListener('pointerdown', (e) => {
  sfx.init();
  if (e.pointerType === 'touch') touchMode = true;
  try { cv.setPointerCapture(e.pointerId); } catch (_) { /* 合成事件没有真实指针 */ }
  tryFullscreen();
  if (!started) { started = true; return; }
  const v = toVirtual(e);
  if (touchMode) {
    for (const b of buttons()) if (Math.hypot(v.x - b.x, v.y - b.y) < b.r + 16) {
      if (b.id === 'lamp') setLit(!lit);
      else if (b.id === 'jump') { tryJump(); btn.jump = true; }
      btnOwner.set(e.pointerId, b.id);
      return;
    }
  }
  if (ended) { restart(); return; }
  const w = { x: v.x + camX, y: v.y };
  // 先看是不是抓影子的手
  if (lit) {
    const hp = handPositions();
    let best = -1, bd = 70;
    hp.forEach((h, i) => { const d = dist(h, w); if (d < bd && armDrag[i] === null) { bd = d; best = i; } });
    if (best >= 0) { pointers.set(e.pointerId, w); armDrag[best] = e.pointerId; everDraggedHand = true; sfx.grab(); return; }
  }
  // 再看是不是摇杆：左半屏下方任意位置都行
  if (touchMode && stick.id === null && v.x < viewW * 0.45 && v.y > CLOTH_FLOOR - 40) {
    stick.id = e.pointerId;
    STICK.x = clamp(v.x, STICK.r + 40, viewW * 0.45 - 20);
    STICK.y = clamp(v.y, CLOTH_FLOOR + 20, VH - STICK.r - 20);
    setStick(v);
  }
});
cv.addEventListener('pointermove', (e) => {
  const v = toVirtual(e);
  if (stick.id === e.pointerId) { setStick(v); return; }
  if (!pointers.has(e.pointerId)) return;
  pointers.set(e.pointerId, { x: v.x + camX, y: v.y });
});
function endPointer(e) {
  const b = btnOwner.get(e.pointerId);
  if (b) { if (b in btn) btn[b] = false; btnOwner.delete(e.pointerId); }
  pointers.delete(e.pointerId);
  for (let i = 0; i < 2; i++) if (armDrag[i] === e.pointerId) armDrag[i] = null;
  if (stick.id === e.pointerId) { stick.id = null; stick.x = stick.y = 0; STICK.x = STICK_HOME.x; STICK.y = STICK_HOME.y; }
}
cv.addEventListener('pointerup', endPointer);
cv.addEventListener('pointercancel', endPointer);
cv.addEventListener('contextmenu', (e) => e.preventDefault());

let fsTried = false;
function tryFullscreen() {
  if (fsTried || !touchMode) return;
  fsTried = true;
  const el = document.documentElement;
  const req = el.requestFullscreen || el.webkitRequestFullscreen;
  if (req) Promise.resolve(req.call(el)).then(() => screen.orientation && screen.orientation.lock && screen.orientation.lock('landscape').catch(() => {})).catch(() => {});
}

function tryJump() {
  if (ended) return;
  if (girl.onGround) { girl.vy = -JUMP_V; girl.onGround = false; sfx.jump(); }
}
function restart() {
  ended = false; girl.x = 120; girl.y = GROUND_Y; girl.z = Z_LANE; girl.vx = girl.vy = 0; checkpoint = 120;
  gateA.open = gateB.open = 0;
  for (const r of rotators) { r.angle = r.a0; r.done = false; r.attached = -1; }
  Object.assign(key, { x: key.home.x, y: key.home.y, held: -1, locked: false });
  setLit(false, true);
}

// ---------- 姿态 ----------
function poseWalk(p, k) {
  const s = Math.sin(p);
  return {
    rightUpperLeg: -s * 30 * k * D2R, leftUpperLeg: s * 30 * k * D2R,
    rightLowerLeg: Math.max(0, Math.sin(p + Math.PI / 2)) * 40 * k * D2R,
    leftLowerLeg: Math.max(0, Math.sin(p - Math.PI / 2)) * 40 * k * D2R,
    rightFoot: 0, leftFoot: 0,
    leftUpperArm: (80 + s * 20 * k) * D2R, leftLowerArm: -10 * D2R, leftHand: 0,
    rightUpperArm: (-72 - s * 8 * k) * D2R, rightLowerArm: 22 * D2R, rightHand: 0,
    head: Math.sin(p * 2) * 2 * k * D2R, lowerTorso: 0,
  };
}
function poseJump() {
  return {
    rightUpperLeg: -35 * D2R, leftUpperLeg: 18 * D2R, rightLowerLeg: 45 * D2R, leftLowerLeg: 30 * D2R,
    rightFoot: 0, leftFoot: 0, leftUpperArm: 55 * D2R, leftLowerArm: -20 * D2R, leftHand: 0,
    rightUpperArm: -90 * D2R, rightLowerArm: 30 * D2R, rightHand: 0, head: -4 * D2R, lowerTorso: 0,
  };
}
function poseLit() {
  const b = Math.sin(time * 1.8) * 2 * D2R;
  return {
    rightUpperLeg: 0, leftUpperLeg: 0, rightLowerLeg: 0, leftLowerLeg: 0, rightFoot: 0, leftFoot: 0,
    leftUpperArm: 76 * D2R + b, leftLowerArm: -6 * D2R, leftHand: 0,
    rightUpperArm: -18 * D2R - b, rightLowerArm: 6 * D2R, rightHand: 0, head: -5 * D2R, lowerTorso: 0,
  };
}

// ---------- 更新 ----------
function update(dt) {
  time += dt;
  const dead = (v) => Math.abs(v) < 0.25 ? 0 : v;
  let move = (keys['d'] || keys['arrowright'] ? 1 : 0) - (keys['a'] || keys['arrowleft'] ? 1 : 0);
  let fwd = (keys['s'] || keys['arrowdown'] ? 1 : 0) - (keys['w'] || keys['arrowup'] ? 1 : 0); // +1 朝灯 / 镜头
  if (stick.id !== null) { move = dead(stick.x); fwd = dead(stick.y); }
  if (ended || !started) move = fwd = 0;

  girl.vx = move * SPEED;
  if (move !== 0) girl.facing = Math.sign(move);
  const z0 = girl.z;
  girl.z = clamp(girl.z + fwd * DEPTH_SPEED * dt, Z_BACK, Z_FRONT);
  const zMoving = Math.abs(girl.z - z0) > 1e-4;
  girl.vy += GRAV * dt;
  pickupHintT = Math.max(0, pickupHintT - dt);

  // 碰撞（人物盒：宽 26，高 100）
  const hw = 13, hh = 100, sol = solids();
  girl.x += girl.vx * dt;
  for (const s of sol) if (girl.x + hw > s.x && girl.x - hw < s.x + s.w && girl.y > s.y && girl.y - hh < s.y + s.h) {
    if (girl.vx > 0) girl.x = s.x - hw; else if (girl.vx < 0) girl.x = s.x + s.w + hw;
  }
  girl.x = clamp(girl.x, 20, LEVEL_W - 20);
  girl.y += girl.vy * dt;
  const wasGround = girl.onGround, fallV = girl.vy;
  girl.onGround = false;
  for (const s of sol) if (girl.x + hw > s.x && girl.x - hw < s.x + s.w && girl.y > s.y && girl.y - hh < s.y + s.h) {
    if (girl.vy > 0) { girl.y = s.y; girl.vy = 0; girl.onGround = true; }
    else if (girl.vy < 0) { girl.y = s.y + s.h + hh; girl.vy = 0; }
  }
  if (!wasGround && girl.onGround && fallV > 250) sfx.land();
  if (girl.y > VH + 200) { sfx.fall(); setLit(false, true); girl.x = checkpoint; girl.y = GROUND_Y - 40; girl.vy = 0; }
  if (girl.onGround) for (const c of [120, 1260, 1900, 2720]) if (girl.x > c) checkpoint = Math.max(checkpoint, c);
  if (girl.x > 3020 && !ended) { ended = true; setLit(false, true); sfx.endTune(); }

  litAmt = clamp(litAmt + (lit ? 2.5 : -3.5) * dt, 0, 1);
  const walking = Math.abs(girl.vx) > 1 || zMoving;
  girl.walkAmt = lerp(girl.walkAmt, girl.onGround && walking ? 1 : 0, 1 - Math.exp(-10 * dt));
  girl.phase += dt * 11 * (walking ? 1 : 0.3);
  const stepIdx = Math.floor(girl.phase / Math.PI);
  if (girl.onGround && walking && stepIdx !== lastStep) sfx.step(girl.z);
  lastStep = stepIdx;
  if (litAmt > 0.5 && Math.random() < dt * 7) sfx.crackle(litAmt);

  // 目标姿态：放下灯后双手空着
  tgt = !girl.onGround ? poseJump() : (lit && girl.walkAmt < 0.3) ? poseLit() : poseWalk(girl.phase, girl.walkAmt);
  const toRig = lit ? inv(mul(shadowMat(), rootMat())) : null;
  ARMS.forEach((a, i) => {
    if (!lit) return;
    if (armDrag[i] !== null && pointers.has(armDrag[i])) armTargets[i] = ap(toRig, pointers.get(armDrag[i]));
    if (armTargets[i]) { const [u, l] = solveArm(a, armTargets[i], cur); tgt[a.upper] = u; tgt[a.lower] = l; tgt[a.hand] = 0; }
  });
  const k = 1 - Math.exp(-18 * dt);
  for (const r in tgt) cur[r] = (cur[r] || 0) + wrapA(tgt[r] - (cur[r] || 0)) * k;

  // 影子与幕布机关的互动
  const hp = handPositions();
  for (const r of rotators) {
    const piv = { x: r.x, y: CLOTH_FLOOR - r.h };
    const tip = { x: piv.x + Math.cos(r.angle) * r.len, y: piv.y + Math.sin(r.angle) * r.len };
    if (r.done) { r.attached = -1; r.angle = r.a1; continue; }
    if (r.attached < 0) for (let i = 0; i < 2; i++) if (armDrag[i] !== null && hp[i] && dist(hp[i], tip) < 52) r.attached = i;
    if (r.attached >= 0) {
      const h = hp[r.attached];
      if (!h || armDrag[r.attached] === null || dist(h, tip) > 80) r.attached = -1;
      else {
        let a = Math.atan2(h.y - piv.y, h.x - piv.x);
        if (r.kind === 'lever' && a > Math.PI / 2) a -= 2 * Math.PI;
        const before = r.angle;
        r.angle = clamp(a, r.a0, r.a1);
        if (Math.abs(r.angle - before) > 0.004) sfx.creak();
        if ((r.angle - r.a0) / (r.a1 - r.a0) > 0.94) {
          r.done = true; r.angle = r.a1;
          sfx.clunk(); sfx.success();
          if (r === lever) sfx.rumble();
        }
      }
    }
    if (r.attached < 0 && !r.done) r.angle = lerp(r.angle, r.a0, 1 - Math.exp(-2.5 * dt));
  }
  gateA.open = lever.done ? Math.min(1, gateA.open + dt * 0.8) : clamp((lever.angle - lever.a0) / (lever.a1 - lever.a0), 0, 1) * 0.35;

  if (!key.locked) {
    if (key.held < 0 && lit) for (let i = 0; i < 2; i++) if (armDrag[i] !== null && hp[i] && dist(hp[i], key) < 42) { key.held = i; sfx.keyGrab(); }
    if (key.held >= 0 && hp[key.held]) { key.x = hp[key.held].x; key.y = hp[key.held].y + 6; }
    else { key.held = -1; key.x = lerp(key.x, key.home.x, 1 - Math.exp(-4 * dt)); key.y = lerp(key.y, key.home.y, 1 - Math.exp(-4 * dt)); }
    if (key.held >= 0 && dist(key, lock) < 40) { key.locked = true; key.held = -1; sfx.lock(); sfx.clunk(); sfx.success(); sfx.rumble(); }
  } else { key.x = lock.x; key.y = lock.y; }
  if (key.locked) gateB.open = Math.min(1, gateB.open + dt * 0.8);

  // 镜头
  const want = clamp(girl.x - viewW * 0.38, 0, Math.max(0, LEVEL_W - viewW));
  camX = lerp(camX, want, 1 - Math.exp(-6 * dt));
}

// ---------- 绘制 ----------
const SIL = (a) => `rgba(46,24,12,${a})`;
const flick = () => 1 + 0.035 * Math.sin(time * 13) + 0.025 * Math.sin(time * 7.3);

function drawCloth() {
  const x0 = camX - 10, x1 = camX + viewW + 10;
  // 幕布后面一直有一层暖色的底光（戏台的常亮灯），不点灯也看得清
  const base = ctx.createLinearGradient(0, CLOTH_TOP, 0, CLOTH_FLOOR);
  base.addColorStop(0, '#5e4329'); base.addColorStop(0.6, '#7a5733'); base.addColorStop(1, '#5a3e24');
  ctx.fillStyle = base;
  ctx.fillRect(x0, CLOTH_TOP, x1 - x0, CLOTH_FLOOR - CLOTH_TOP);
  // 手里提着的小灯也在幕布上照出一团微光
  if (litAmt < 1) {
    const cx = girl.x, cy = CLOTH_FLOOR - 110, f = flick();
    const g = ctx.createRadialGradient(cx, cy, 10, cx, cy, 380 * f);
    g.addColorStop(0, `rgba(255,214,150,${0.32 * (1 - litAmt)})`); g.addColorStop(1, 'rgba(255,190,120,0)');
    ctx.fillStyle = g; ctx.fillRect(x0, CLOTH_TOP, x1 - x0, CLOTH_FLOOR - CLOTH_TOP);
  }
  if (litAmt > 0) {
    const cx = lamp.x, cy = CLOTH_FLOOR - 150, f = flick();
    const rad = 420 + lampGap() * 240;
    const g = ctx.createRadialGradient(cx, cy, 10, cx, cy, rad * f);
    g.addColorStop(0, `rgba(255,232,180,${0.98 * litAmt})`);
    g.addColorStop(0.45, `rgba(240,190,120,${0.85 * litAmt})`);
    g.addColorStop(1, `rgba(150,90,40,${0.0})`);
    ctx.fillStyle = g;
    ctx.fillRect(x0, CLOTH_TOP, x1 - x0, CLOTH_FLOOR - CLOTH_TOP);
  }
  ctx.save(); ctx.globalAlpha = 0.9; ctx.fillStyle = clothPattern;
  ctx.fillRect(x0, CLOTH_TOP, x1 - x0, CLOTH_FLOOR - CLOTH_TOP); ctx.restore();
}

function drawClothFrame() {
  const x0 = camX - 10, x1 = camX + viewW + 10;
  ctx.fillStyle = '#3b2414';
  ctx.fillRect(x0, CLOTH_TOP - 16, x1 - x0, 18);
  ctx.fillStyle = '#5a361c';
  ctx.fillRect(x0, CLOTH_TOP - 16, x1 - x0, 4);
  for (let x = Math.floor(x0 / 560) * 560; x < x1; x += 560) {
    ctx.fillStyle = '#2e1b0f'; ctx.fillRect(x - 7, CLOTH_TOP - 24, 14, CLOTH_FLOOR - CLOTH_TOP + 30);
    ctx.fillStyle = '#6b4020'; ctx.beginPath(); ctx.arc(x, CLOTH_TOP - 22, 9, 0, 7); ctx.fill();
  }
}

function drawClothProps() {
  const a = 0.6 + 0.3 * litAmt;
  ctx.save();
  ctx.globalCompositeOperation = 'multiply';
  ctx.fillStyle = SIL(a); ctx.strokeStyle = SIL(a);
  // 拉杆
  {
    const px = lever.x, py = CLOTH_FLOOR - lever.h;
    ctx.beginPath(); ctx.arc(px, py + 6, 28, Math.PI, 0); ctx.closePath(); ctx.fill();
    ctx.fillRect(px - 36, py + 4, 72, 10);
    ctx.lineWidth = 10; ctx.lineCap = 'round';
    const tx = px + Math.cos(lever.angle) * lever.len, ty = py + Math.sin(lever.angle) * lever.len;
    ctx.beginPath(); ctx.moveTo(px, py); ctx.lineTo(tx, ty); ctx.stroke();
    ctx.lineWidth = 6; ctx.beginPath(); ctx.arc(tx, ty, 13, 0, 7); ctx.stroke();
    // 云纹装饰
    ctx.lineWidth = 3;
    for (let i = -1; i <= 1; i += 2) { ctx.beginPath(); ctx.arc(px + i * 18, py - 4, 8, 0, Math.PI * 1.5); ctx.stroke(); }
  }
  // 影子吊桥
  {
    const r = shadowBridge, px = r.x, py = CLOTH_FLOOR - r.h;
    ctx.fillRect(px - 10, py - 4, 20, r.h + 4);
    ctx.save(); ctx.translate(px, py); ctx.rotate(r.angle);
    ctx.fillRect(0, -9, r.len, 18);
    ctx.globalCompositeOperation = 'source-over';
    ctx.fillStyle = 'rgba(255,230,190,0.18)';
    for (let i = 14; i < r.len - 6; i += 22) ctx.fillRect(i, -7, 3, 14);
    ctx.restore();
    ctx.lineWidth = 6;
    const tx = px + Math.cos(r.angle) * r.len, ty = py + Math.sin(r.angle) * r.len;
    ctx.beginPath(); ctx.arc(tx, ty, 13, 0, 7); ctx.stroke();
    ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(px, py - 40); ctx.lineTo(tx, ty); ctx.stroke();
    ctx.beginPath(); ctx.arc(px, py - 40, 6, 0, 7); ctx.fill();
  }
  // 挂钩、锁、钥匙
  {
    const hx = key.home.x, hy = key.home.y - 28;
    ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(hx, CLOTH_TOP); ctx.lineTo(hx, hy); ctx.stroke();
    ctx.beginPath(); ctx.arc(hx, hy + 8, 8, -Math.PI / 2, Math.PI); ctx.stroke();
    ctx.fillRect(lock.x - 30, lock.y - 30, 60, 74);
    ctx.lineWidth = 7; ctx.beginPath(); ctx.arc(lock.x, lock.y - 30, 20, Math.PI, 0); ctx.stroke();
    ctx.globalCompositeOperation = 'source-over';
    ctx.fillStyle = `rgba(255,236,200,${0.25 + 0.35 * litAmt})`;
    ctx.beginPath(); ctx.arc(lock.x, lock.y + 2, 7, 0, 7); ctx.fill();
    ctx.fillRect(lock.x - 3, lock.y + 2, 6, 18);
    ctx.globalCompositeOperation = 'multiply';
    ctx.fillStyle = SIL(a);
    ctx.save(); ctx.translate(key.x, key.y); ctx.rotate(key.locked ? -Math.PI / 2 : Math.PI / 2);
    ctx.lineWidth = 6; ctx.beginPath(); ctx.arc(0, -22, 12, 0, 7); ctx.stroke();
    ctx.fillRect(-3, -10, 6, 44); ctx.fillRect(3, 22, 10, 5); ctx.fillRect(3, 30, 8, 5);
    ctx.restore();
  }
  ctx.restore();
}

// 离屏图层：影子（下半身渐隐）和台前的黑色皮影都先画到这里再合成
const layer = document.createElement('canvas'), lctx = layer.getContext('2d');
function prepLayer() {
  if (layer.width !== cv.width || layer.height !== cv.height) { layer.width = cv.width; layer.height = cv.height; }
  lctx.setTransform(1, 0, 0, 1, 0, 0);
  lctx.globalCompositeOperation = 'source-over'; lctx.globalAlpha = 1;
  lctx.clearRect(0, 0, layer.width, layer.height);
  lctx.setTransform(scale, 0, 0, scale, -camX * scale, 0);
}
function blitLayer(alpha, comp) {
  ctx.save();
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.globalAlpha = alpha;
  if (comp) ctx.globalCompositeOperation = comp;
  ctx.drawImage(layer, 0, 0);
  ctx.restore();
}

function drawRig(c, M0) {
  const W = fk(rig, cur);
  c.save();
  const base = c.getTransform();
  for (const p of rig.drawOrder) {
    const m = mul(M0, W[p.id]);
    c.setTransform(base.a * m[0] + base.c * m[1], base.b * m[0] + base.d * m[1],
      base.a * m[2] + base.c * m[3], base.b * m[2] + base.d * m[3],
      base.a * m[4] + base.c * m[5] + base.e, base.b * m[4] + base.d * m[5] + base.f);
    c.drawImage(p.img, 0, 0);
  }
  c.restore();
  return W;
}

function drawShadow() {
  if (litAmt <= 0) return;
  const SM = shadowMat(), M0 = mul(SM, rootMat());
  prepLayer();
  const W = drawRig(lctx, M0);
  // 下半身渐隐：从腰部往下淡出到脚
  const yTop = ap(SM, { x: 0, y: GROUND_Y - GIRL_H * 0.55 }).y;
  const yBot = Math.min(ap(SM, { x: 0, y: GROUND_Y - 4 }).y, CLOTH_FLOOR);
  const g = lctx.createLinearGradient(0, Math.min(yTop, yBot - 30), 0, yBot);
  g.addColorStop(0, 'rgba(0,0,0,1)'); g.addColorStop(0.55, 'rgba(0,0,0,0.45)'); g.addColorStop(1, 'rgba(0,0,0,0)');
  lctx.globalCompositeOperation = 'destination-in';
  lctx.fillStyle = g;
  lctx.fillRect(camX - 10, -10, viewW + 20, VH + 20);
  ctx.save();
  ctx.beginPath(); ctx.rect(camX - 10, CLOTH_TOP, viewW + 20, CLOTH_FLOOR - CLOTH_TOP); ctx.clip();
  blitLayer(0.93 * litAmt, 'multiply');
  ctx.restore();
  // 可拖动提示
  if (lit) {
    ARMS.forEach((a, i) => {
      const h = ap(mul(M0, W[P[a.hand].id]), handCenterLocal(a));
      const active = armDrag[i] !== null;
      const pulse = everDraggedHand ? 0.22 : 0.45 + 0.3 * Math.sin(time * 4);
      ctx.strokeStyle = active ? 'rgba(255,250,220,0.85)' : `rgba(255,245,215,${pulse})`;
      ctx.lineWidth = 2.5;
      ctx.beginPath(); ctx.arc(h.x, h.y, active ? 22 : 28, 0, 7); ctx.stroke();
    });
    drawDragTutorial(ap(mul(M0, W[P[ARMS[0].hand].id]), handCenterLocal(ARMS[0])));
  }
}

function drawFloor() {
  const x0 = camX - 10, x1 = camX + viewW + 10;
  ctx.fillStyle = '#060403'; ctx.fillRect(x0, CLOTH_FLOOR, x1 - x0, VH - CLOTH_FLOOR);
  for (const [a, b] of GROUNDS) {
    const g = ctx.createLinearGradient(0, CLOTH_FLOOR, 0, VH);
    g.addColorStop(0, '#4a3019'); g.addColorStop(0.45, '#5e3d20'); g.addColorStop(1, '#2e1d0f');
    ctx.fillStyle = g; ctx.fillRect(a, CLOTH_FLOOR, b - a, VH - CLOTH_FLOOR);
    ctx.strokeStyle = 'rgba(0,0,0,0.25)'; ctx.lineWidth = 1;
    for (let y = CLOTH_FLOOR + 14; y < VH; y += 18 + (y - CLOTH_FLOOR) * 0.12) {
      ctx.beginPath(); ctx.moveTo(a, y); ctx.lineTo(b, y); ctx.stroke();
    }
  }
  // 可走动的纵深范围
  ctx.fillStyle = 'rgba(255,220,170,0.035)';
  ctx.fillRect(x0, depthY(Z_BACK), x1 - x0, depthY(Z_FRONT) - depthY(Z_BACK));
  if (litAmt < 1) {
    const gy = depthY(girl.z), g = ctx.createRadialGradient(girl.x, gy, 4, girl.x, gy, 200 * flick());
    g.addColorStop(0, `rgba(255,200,120,${0.25 * (1 - litAmt)})`); g.addColorStop(1, 'rgba(255,170,90,0)');
    ctx.fillStyle = g; ctx.fillRect(girl.x - 220, CLOTH_FLOOR, 440, VH - CLOTH_FLOOR);
  }
  if (litAmt > 0) {
    const ly = depthY(Z_LAMP);
    const g = ctx.createRadialGradient(lamp.x, ly, 4, lamp.x, ly, 260 * flick());
    g.addColorStop(0, `rgba(255,200,120,${0.45 * litAmt})`); g.addColorStop(1, 'rgba(255,170,90,0)');
    ctx.fillStyle = g; ctx.fillRect(lamp.x - 280, CLOTH_FLOOR, 560, VH - CLOTH_FLOOR);
  }
}

// 台上的物件都横跨整个可走的纵深：正面在 Z_FRONT，顶面一直延伸到 Z_BACK
const YB = () => depthY(Z_BACK) - 6, YF = () => depthY(Z_FRONT) + 6;
function drawWorldObjects() {
  const yb = YB(), yf = YF();
  for (const b of BOXES) {
    const h = b.h;
    ctx.fillStyle = '#7a4f2b';                                   // 顶面
    ctx.fillRect(b.x, yb - h, b.w, yf - yb);
    ctx.fillStyle = '#5b3a20'; ctx.fillRect(b.x, yf - h, b.w, h); // 正面
    ctx.strokeStyle = '#2e1c0e'; ctx.lineWidth = 3; ctx.strokeRect(b.x + 1.5, yf - h + 1.5, b.w - 3, h - 3);
    ctx.beginPath(); ctx.moveTo(b.x, yf - h); ctx.lineTo(b.x + b.w, yf); ctx.stroke();
    ctx.lineWidth = 1.5; ctx.strokeRect(b.x + 0.75, yb - h + 0.75, b.w - 1.5, yf - yb - 1.5);
  }
  for (const g of [gateA, gateB]) {
    const lift = g.open * g.h * 0.92;
    ctx.fillStyle = '#2b190d';
    ctx.fillRect(g.x - 14, CLOTH_FLOOR - 10, 8, yf - CLOTH_FLOOR + 10);
    ctx.fillRect(g.x + g.w + 6, CLOTH_FLOOR - 10, 8, yf - CLOTH_FLOOR + 10);
    ctx.save(); ctx.beginPath(); ctx.rect(g.x - 20, 0, g.w + 40, yf); ctx.clip();
    const top = yb - g.h - lift, bot = yf - lift;
    ctx.fillStyle = '#6a3f1f'; ctx.fillRect(g.x, top, g.w, bot - top);
    ctx.strokeStyle = '#3a210f'; ctx.lineWidth = 3;
    for (let y = top + 20; y < bot; y += 26) { ctx.beginPath(); ctx.moveTo(g.x, y); ctx.lineTo(g.x + g.w, y); ctx.stroke(); }
    ctx.strokeRect(g.x + 1.5, top + 1.5, g.w - 3, bot - top - 3);
    ctx.restore();
  }
  // 真实吊桥：跟影子吊桥同步，桥面横跨整个纵深
  {
    const a = shadowBridge.angle, x = realBridge.x, L = realBridge.len;
    const tx = Math.cos(a) * L, ty = Math.sin(a) * L;
    ctx.fillStyle = '#6a4322';
    ctx.beginPath();
    ctx.moveTo(x, yb); ctx.lineTo(x + tx, yb + ty); ctx.lineTo(x + tx, yf + ty); ctx.lineTo(x, yf);
    ctx.closePath(); ctx.fill();
    ctx.strokeStyle = '#3a220f'; ctx.lineWidth = 3;
    for (let i = 18; i < L; i += 26) {
      const px = Math.cos(a) * i, py = Math.sin(a) * i;
      ctx.beginPath(); ctx.moveTo(x + px, yb + py); ctx.lineTo(x + px, yf + py); ctx.stroke();
    }
    ctx.fillStyle = '#5a3a1e'; ctx.fillRect(x + Math.min(0, tx), yf + Math.min(0, ty), Math.abs(tx) + 1, 10);
    ctx.fillStyle = '#2b190d'; ctx.fillRect(x - 10, yb - 80, 10, yf - yb + 80);
    ctx.strokeStyle = 'rgba(200,170,120,0.5)'; ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.moveTo(x - 5, yb - 80); ctx.lineTo(x + tx, yb + ty); ctx.stroke();
  }
  // 终点：一串灯笼
  for (let i = 0; i < 5; i++) {
    const x = 3060 + i * 60, y = 300 + Math.sin(i * 1.7) * 30;
    drawLantern(x, y, 1.1, 1, true);
  }
}

function drawLantern(x, y, s, glow, hangLine) {
  const f = flick();
  if (glow > 0) {
    const g = ctx.createRadialGradient(x, y, 2, x, y, 60 * s * f);
    g.addColorStop(0, `rgba(255,190,90,${0.55 * glow})`); g.addColorStop(1, 'rgba(255,150,60,0)');
    ctx.fillStyle = g; ctx.beginPath(); ctx.arc(x, y, 60 * s * f, 0, 7); ctx.fill();
  }
  if (hangLine) { ctx.strokeStyle = '#2a170b'; ctx.lineWidth = 1.5; ctx.beginPath(); ctx.moveTo(x, y - 14 * s); ctx.lineTo(x, CLOTH_TOP); ctx.stroke(); }
  ctx.fillStyle = glow > 0.2 ? '#e0582a' : '#7a2d16';
  ctx.beginPath(); ctx.ellipse(x, y, 10 * s, 12 * s, 0, 0, 7); ctx.fill();
  ctx.fillStyle = `rgba(255,220,140,${0.25 + 0.6 * glow})`;
  ctx.beginPath(); ctx.ellipse(x, y, 5 * s, 9 * s, 0, 0, 7); ctx.fill();
  ctx.fillStyle = '#2a170b';
  ctx.fillRect(x - 6 * s, y - 14 * s, 12 * s, 3 * s); ctx.fillRect(x - 6 * s, y + 11 * s, 12 * s, 3 * s);
  ctx.fillRect(x - 1 * s, y + 14 * s, 2 * s, 6 * s);
}

function drawGirl() {
  const bob = girl.onGround ? -Math.abs(Math.sin(girl.phase)) * 3 * girl.walkAmt : 0;
  // 皮影本体偏黑：先画到图层，再盖一层墨色，只透出一点花纹
  prepLayer();
  const M0 = mul(depthMat(), rootMat(bob));
  const W = drawRig(lctx, M0);
  lctx.globalCompositeOperation = 'source-atop';
  lctx.fillStyle = `rgba(16,9,5,${0.86 - 0.12 * litAmt})`;
  lctx.fillRect(camX - 10, -10, viewW + 20, VH + 20);
  blitLayer(1);
  if (litAmt < 1) {
    // 手里提着的小灯
    const h = ap(mul(M0, W[P.rightHand.id]), handCenterLocal(ARMS[0]));
    ctx.save(); ctx.globalAlpha = 1 - litAmt;
    ctx.strokeStyle = '#2a170b'; ctx.lineWidth = 1.2;
    ctx.beginPath(); ctx.moveTo(h.x, h.y); ctx.lineTo(h.x, h.y + 8); ctx.stroke();
    drawLantern(h.x, h.y + 20 * persp(girl.z), 0.75 * persp(girl.z), 0.35, false);
    ctx.restore();
  }
}

function drawLamp() {
  if (litAmt <= 0) return;
  const p = persp(Z_LAMP), ly = depthY(Z_LAMP);
  ctx.save(); ctx.globalAlpha = litAmt;
  ctx.fillStyle = 'rgba(0,0,0,0.35)';
  ctx.beginPath(); ctx.ellipse(lamp.x, ly + 2, 16 * p, 4 * p, 0, 0, 7); ctx.fill();
  drawLantern(lamp.x, ly - 16 * p, p, 1, false);
  if (lit && Math.abs(girl.x - lamp.x) < PICKUP_DIST) {   // 走回灯旁边时提示可以拿起
    ctx.strokeStyle = `rgba(255,240,200,${0.25 + 0.2 * Math.sin(time * 4)})`; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.arc(lamp.x, ly - 14 * p, 30 * p, 0, 7); ctx.stroke();
  }
  ctx.restore();
}

function hintText() {
  if (ended) return '';
  const x = girl.x;
  const tc = touchMode;
  if (pickupHintT > 0) return '离灯太远了，走回灯旁边再拿';
  if (x < 420) return tc ? '左边摇杆：左右走、前后走　「跳」跳跃' : 'A / D 左右走　W / S 前后走　空格 跳跃　M 静音';
  if (x < 820) return '';
  if (!lever.done && x < 1180) {
    if (!lit) return tc ? '门打不开……按「放灯」把灯放下' : '门打不开……按 E 把灯放下';
    return tc ? '往前走靠近灯，影子变大；左右走，影子跟着挪　·　拖影子的手去拉机关'
      : 'S 靠近灯影子变大，W 远离变小；左右走影子跟着挪　·　拖影子的手去拉机关';
  }
  if (!shadowBridge.done && x > 1350 && x < 1700) return lit ? '把影子吊桥拉下来' : '前面断了。幕布上好像有座吊桥';
  if (!key.locked && x > 1900 && x < 2660) {
    if (!lit) return '门上了锁。钥匙挂得好高';
    if (key.held >= 0) return '拿着钥匙走动，把它送进锁里';
    return '钥匙挂得好高——走近灯，把影子变大';
  }
  return '';
}

function drawHUD() {
  ctx.setTransform(scale, 0, 0, scale, 0, 0);
  const t = hintText();
  if (t) {
    ctx.font = '22px "Songti SC","STSong","Noto Serif SC",serif';
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    const w = ctx.measureText(t).width + 40;
    ctx.fillStyle = 'rgba(20,10,5,0.55)'; ctx.fillRect(viewW / 2 - w / 2, 54, w, 40);
    ctx.fillStyle = '#f1dcb0'; ctx.fillText(t, viewW / 2, 75);
  }
  if (lit) {
    ctx.font = '16px "Songti SC",serif'; ctx.textAlign = 'right'; ctx.textBaseline = 'top';
    ctx.fillStyle = 'rgba(241,220,176,0.7)';
    ctx.fillText(`影子 ×${shadowScale().toFixed(1)}`, viewW - 24, CLOTH_FLOOR + 10);
  }
  if (touchMode) {
    ctx.fillStyle = 'rgba(255,220,160,0.1)'; ctx.strokeStyle = 'rgba(255,225,170,0.45)'; ctx.lineWidth = 2.5;
    ctx.beginPath(); ctx.arc(STICK.x, STICK.y, STICK.r, 0, 7); ctx.fill(); ctx.stroke();
    ctx.fillStyle = stick.id !== null ? 'rgba(255,225,170,0.55)' : 'rgba(255,225,170,0.3)';
    ctx.beginPath(); ctx.arc(STICK.x + stick.x * STICK.r * 0.72, STICK.y + stick.y * STICK.r * 0.72, 44, 0, 7); ctx.fill();
    for (const b of buttons()) {
      const on = b.id === 'jump' && btn.jump;
      ctx.fillStyle = on ? 'rgba(255,220,160,0.35)' : 'rgba(255,220,160,0.14)';
      ctx.strokeStyle = 'rgba(255,225,170,0.5)'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(b.x, b.y, b.r, 0, 7); ctx.fill(); ctx.stroke();
      ctx.fillStyle = '#f6e3bd'; ctx.font = `${b.r * 0.62}px "Songti SC",serif`;
      ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(b.label, b.x, b.y + 2);
    }
  }
  if (!started) {
    ctx.fillStyle = 'rgba(10,5,2,0.72)'; ctx.fillRect(0, 0, viewW, VH);
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillStyle = '#f3d9a4'; ctx.font = '64px "Songti SC","STSong","Noto Serif SC",serif';
    ctx.fillText('灯 影', viewW / 2, VH / 2 - 90);
    ctx.font = '26px "Songti SC","STSong","Noto Serif SC",serif';
    ctx.fillText('请打开声音　·　戴上耳机更好', viewW / 2, VH / 2 + 5);
    ctx.font = '20px "Songti SC",serif'; ctx.fillStyle = `rgba(243,217,164,${0.5 + 0.3 * Math.sin(time * 3)})`;
    ctx.fillText(touchMode || matchMedia('(pointer: coarse)').matches ? '轻触屏幕开始' : '点击或按任意键开始', viewW / 2, VH / 2 + 70);
  }
  if (ended) {
    ctx.fillStyle = 'rgba(10,5,2,0.6)'; ctx.fillRect(0, 0, viewW, VH);
    ctx.fillStyle = '#f3d9a4'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.font = '52px "Songti SC","STSong",serif'; ctx.fillText('第一幕 · 完', viewW / 2, VH / 2 - 20);
    ctx.font = '20px "Songti SC",serif'; ctx.fillStyle = 'rgba(243,217,164,0.7)';
    ctx.fillText('点击重新开始', viewW / 2, VH / 2 + 40);
  }
}

// ---------- 前景：只留一圈暗角 ----------
function drawForeground() {
  ctx.save();
  ctx.setTransform(scale, 0, 0, scale, 0, 0);
  const vg = ctx.createRadialGradient(viewW / 2, VH * 0.45, VH * 0.3, viewW / 2, VH * 0.45, Math.max(viewW, VH) * 0.72);
  vg.addColorStop(0, 'rgba(0,0,0,0)'); vg.addColorStop(1, 'rgba(0,0,0,0.4)');
  ctx.fillStyle = vg; ctx.fillRect(0, 0, viewW, VH);
  ctx.restore();
}

// 手形图标：指尖在 (x, y)
function drawHandIcon(x, y, s, a) {
  ctx.save();
  ctx.translate(x, y); ctx.scale(s, s); ctx.rotate(-0.25);
  ctx.globalAlpha = a;
  ctx.beginPath();
  ctx.moveTo(-7, 34); ctx.lineTo(-7, 6); ctx.arc(0, 6, 7, Math.PI, 0); ctx.lineTo(7, 30); // 食指
  ctx.arc(13, 32, 6, Math.PI, 0); ctx.arc(25, 35, 6, Math.PI, 0); ctx.arc(35, 39, 5.5, Math.PI, 0); // 指节
  ctx.lineTo(40.5, 62); ctx.quadraticCurveTo(40, 82, 20, 84); ctx.lineTo(4, 84);          // 手掌
  ctx.quadraticCurveTo(-10, 82, -16, 66);
  ctx.lineTo(-24, 50); ctx.quadraticCurveTo(-26, 42, -18, 42); ctx.lineTo(-7, 52);        // 拇指
  ctx.closePath();
  ctx.fillStyle = '#fbefd6'; ctx.fill();
  ctx.lineWidth = 3; ctx.lineJoin = 'round'; ctx.strokeStyle = '#3a2210'; ctx.stroke();
  ctx.restore();
}

// 第一次出现影子时：手形图标按住影子的手，往上拖一下，循环演示，直到玩家自己拖过
function drawDragTutorial(handPos) {
  if (!lit || everDraggedHand || litAmt < 0.6) return;
  const T = 2.2, t = ((time - litSince) % T) / T;
  const from = handPos, to = { x: from.x + 70, y: from.y - 120 };
  let k, press, a;
  if (t < 0.18) { k = 0; press = t / 0.18; a = t / 0.18; }          // 落下、按住
  else if (t < 0.7) { k = (t - 0.18) / 0.52; press = 1; a = 1; }   // 拖动
  else { k = 1; press = 1 - (t - 0.7) / 0.3; a = 1 - (t - 0.7) / 0.3; } // 抬起、淡出
  const e = k * k * (3 - 2 * k);
  const x = lerp(from.x, to.x, e), y = lerp(from.y, to.y, e);
  ctx.save();
  if (press > 0.5 && a > 0.05) {
    ctx.strokeStyle = `rgba(255,248,225,${0.7 * a})`; ctx.lineWidth = 3;
    ctx.beginPath(); ctx.arc(x, y, 16 + 10 * (1 - press), 0, 7); ctx.stroke();
  }
  // 拖过的轨迹
  if (k > 0) {
    ctx.strokeStyle = `rgba(255,248,225,${0.35 * a})`; ctx.lineWidth = 4; ctx.setLineDash([6, 8]);
    ctx.beginPath(); ctx.moveTo(from.x, from.y); ctx.lineTo(x, y); ctx.stroke(); ctx.setLineDash([]);
  }
  ctx.restore();
  drawHandIcon(x + 4, y + 6, 0.85 - 0.08 * press, a);
  ctx.save();
  ctx.globalAlpha = 0.9;
  ctx.font = '20px "Songti SC","STSong","Noto Serif SC",serif'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
  const label = '按住影子的手拖动', lx = from.x + 50, ly = from.y + 40;
  const w = ctx.measureText(label).width + 20;
  ctx.fillStyle = 'rgba(20,10,5,0.6)'; ctx.fillRect(lx - 10, ly - 17, w, 34);
  ctx.fillStyle = '#f6e3bd'; ctx.fillText(label, lx, ly);
  ctx.restore();
}

function render() {
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.fillStyle = '#0d0806'; ctx.fillRect(0, 0, cv.width, cv.height);
  ctx.setTransform(scale, 0, 0, scale, -camX * scale, 0);
  drawCloth();
  drawClothProps();
  drawShadow();
  drawClothFrame();
  drawFloor();
  drawWorldObjects();
  drawGirl();
  drawLamp();
  drawForeground();
  drawHUD();
}

let last = performance.now();
function frame(now) {
  if (Math.round(window.innerWidth * dpr) !== cv.width || Math.round(window.innerHeight * dpr) !== cv.height) resize();
  const dt = Math.min(0.033, (now - last) / 1000); last = now;
  update(dt); render();
  requestAnimationFrame(frame);
}
document.getElementById('loading').remove();
window.__game = { sfx, keys, btn, get lit() { return lit; }, girl, lamp, lever, shadowBridge, key, setLit, armTargets, pointers, armDrag, handPositions, get camX() { return camX; } };
requestAnimationFrame(frame);
})().catch(err => {
  const el = document.getElementById('loading');
  if (el) el.textContent = '载入失败：' + err.message + '（需要通过本地服务器打开，而不是直接双击文件）';
  console.error(err);
});
