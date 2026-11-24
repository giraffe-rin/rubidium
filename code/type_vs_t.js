/*
 * type_vs_t.js — 類 m ≡ B (mod A) の中で、型（ブロックの間隔の周期）が t（m = A t + B）のどんな量で決まるかを調べる
 *
 * 何を計算するか:
 *   指定した類について、t = 0, …, TMAX の m の型（(p, L) と周期部分の 0/1 列）を、ブロック漸化式で 300 ブロック計算して推測する。
 *   ブロック漸化式は h から必要な (j, d) だけ遅延評価する（規則は block_rule.js の nextBlock と同じ。小さい m で一致を確かめる）。
 *   次の 2 つを調べる。
 *     (a) k = 0, 1, …, 5 について、型が t mod 2^k だけで決まるか（同じ t mod 2^k で型が違う組があるか）
 *     (b) c = 0, 1, …, 2^6 − 1 と s ∈ {1, 3} について、型が v2(s t + c)（の値。6 以上はまとめる）だけで決まるか
 *     (c) k = 1, …, 8 について、t mod 2^k の剰余類のうち、t ≤ TMAX の中で型が 1 つだけの剰余類の割合
 *   出力：類ごとの型の列（型に番号を付けたもの）と、(a)(b) で決まると判定された最小の k、または (s, c) の一覧。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/type_vs_t.js 4095 105855:2097152 29055:2097152 1087871:2097152 7551:2097152 > data/type_vs_t_v7.txt
 */
'use strict';
module.exports = { gapsLazy, guessLazy, typeOf };
if (require.main !== module) return;
if (process.argv[2] === 'selftest') { const { nextBlock } = require('./block_rule'); let bad = 0; for (let m = 2; m <= 400; m++) { let pv = null; const g = gapsLazy(m, 60); for (let j = 0; j < 60; j++) { pv = nextBlock(m, pv); if (pv.g - m - 1 !== g[j]) { bad++; break; } } } console.log('m = 2..400、60 ブロックで nextBlock と食い違う m の個数: ' + bad); process.exit(0); }
const [tm, ...cls] = process.argv.slice(2); const TMAX = +tm;
const v2 = x => { if (x === 0) return 99; let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
// ブロック漸化式 R を、h から必要な (j, d) だけ遅延評価する（block_rule.js の nextBlock と同じ規則）
function gapsLazy(m, J) {
  const h = (m + 1) / 2, memo = new Map(), gm = new Map();
  const gap = j => { if (gm.has(j)) return gm.get(j); const r = (m % 2 === 1 && S(j, h)) ? m + 2 : m + 1; gm.set(j, r); return r; };
  function S(j, d) {
    const k = j * (m + 2) + d; if (memo.has(k)) return memo.get(k);
    let r = !(d % 2 === 0 && S(j, d / 2));
    if (r && j > 0) { const g = gap(j - 1), s = g + d; if (s % 2 === 0 && s / 2 <= m && S(j - 1, s / 2)) r = false; if (r && g === m + 2 && d === h - 1) r = false; }
    memo.set(k, r); return r;
  }
  const g = []; for (let j = 0; j < J; j++) g.push(gap(j) - m - 1); return g;
}
function guessLazy(m, J) {
  const g = gapsLazy(m, J);
  for (let L = 1; L <= Math.max(120, Math.floor(J / 3)); L++) for (let p = 0; p <= Math.max(150, Math.floor(J / 2)); p++) {
    if (g.length - p < 3 * L) break;
    let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; }
    if (ok) return [p, L, g];
  }
  return null;
}
function typeOf(m, blocks = 300) {
  const pl = guessLazy(m, blocks); if (!pl) return '?'; const g = pl[2];
  // 周期部分は巡回の最小表示にしない（p の位置から書く）
  return (g.slice(0, pl[0]).join('') || '-') + '|' + g.slice(pl[0], pl[0] + pl[1]).join('');
}
const out = ['# 類の中で型が t のどんな量で決まるか', `# 生成: node --stack-size=65500 code/type_vs_t.js ${process.argv.slice(2).join(' ')}`];
for (const c of cls) {
  const [B, A] = c.split(':').map(Number);
  const ty = []; for (let t = 0; t <= TMAX; t++) ty.push(typeOf(A * t + B));
  const names = [...new Set(ty)]; const id = ty.map(x => names.indexOf(x));
  const det = f => { const mp = new Map(); for (let t = 0; t <= TMAX; t++) { const k = f(t); if (mp.has(k) && mp.get(k) !== id[t]) return false; mp.set(k, id[t]); } return true; };
  let kmin = null; for (let k = 0; k <= 5; k++) if (det(t => t % 2 ** k)) { kmin = k; break; }
  const vs = []; for (const s of [1, 3]) for (let c0 = 0; c0 < 64; c0++) if (det(t => Math.min(6, v2(s * t + c0)))) vs.push(`v2(${s}t+${c0})`);
  out.push('', `## m ≡ ${B} (mod ${A})`, `型の種類: ${names.length}`);
  names.forEach((n, i) => out.push(`  型 ${i}: ${n.length > 60 ? n.slice(0, 60) + '…' : n}`));
  out.push(`t = 0..${Math.min(TMAX, 63)} の型の番号: ${id.slice(0, 64).join(' ')}`);
  out.push(`(a) t mod 2^k で決まる最小の k（k ≤ 5）: ${kmin === null ? 'なし' : kmin}`);
  const fr = []; for (let k = 1; k <= 8; k++) { let c1 = 0; for (let r = 0; r < 2 ** k; r++) { const seen = new Set(); for (let t = r; t <= TMAX; t += 2 ** k) seen.add(id[t]); if (seen.size === 1) c1++; } fr.push(`${k}:${(c1 / 2 ** k).toFixed(3)}`); }
  out.push(`(c) t mod 2^k で型が 1 つだけの剰余類の割合: ${fr.join(' ')}`);
  out.push(`(b) 型を決める v2(s t + c)（6 以上はまとめる）: ${vs.length ? vs.slice(0, 8).join('、') + (vs.length > 8 ? ' ほか' : '') : 'なし'}`);
}
console.log(out.join('\n'));
