/*
 * w_even_family.js — 族 q·a + r = s·2^N（q = 2^v − 2^ρ + 1、r = (2^ρ − 1)/3、ρ 偶数 < v）、m = 3a − 2 の w と、m+2 の間隔の連の伸び方を調べる（予想 K46）
 *
 * 何を計算するか:
 *   奇数 v = 5..VMAX と偶数 ρ = 2..v−1 のそれぞれで、q | s·2^N − r かつ a 奇数となる最小の奇数 s（≤ 1023）を探し、
 *   N ∈ [40, NMAX] の解のうち最初の 6 個について、v2(m+1)、w = v2(u+1)（u = (m+1)/2^v）と、
 *   BigInt 版の遅延評価 gapsBig（lazy_bigint.js）で J = max(600, 5N) ブロックまで計算したときの、ブロック 100 以降の m+2 の間隔（1）の連の最大を出す。
 *   判定：6 個すべてで v2(m+1) = v、w = ρ で、連の最大が N とともに真に増えるか。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/w_even_family.js 11 400 > data/w_even_family.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const VMAX = +(process.argv[2] || 11), NMAX = +(process.argv[3] || 400);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 族 q·a + r = s·2^N、q = 2^v − 2^ρ + 1、r = (2^ρ − 1)/3、m = 3a − 2 の w と m+2 の連の最大', '# 生成: node --stack-size=65500 code/w_even_family.js ' + VMAX + ' ' + NMAX,
  'v | ρ | q | r | s | N : (v2(m+1), w, 連の最大) の列 | 判定'];
let allOk = true;
for (let v = 5; v <= VMAX; v += 2) for (let rho = 2; rho < v; rho += 2) {
  const q = 2n ** BigInt(v) - 2n ** BigInt(rho) + 1n, r = (2n ** BigInt(rho) - 1n) / 3n;
  let s = null, Ns = [];
  for (let s0 = 1n; s0 <= 1023n && !s; s0 += 2n) { const L = []; for (let N = 40; N <= NMAX && L.length < 6; N++) { const t = s0 * 2n ** BigInt(N) - r; if (t % q === 0n && (t / q) % 2n === 1n) L.push(N); } if (L.length >= 3) { s = s0; Ns = L; } }
  if (!s) { out.push(`${v} | ${rho} | ${q} | ${r} | - | N ≤ ${NMAX} に 3 個以上の解がない | -`); continue; }
  const cells = []; let ok = true, prev = -1;
  for (const N of Ns) {
    const a = (s * 2n ** BigInt(N) - r) / q, m = 3n * a - 2n, u = (m + 1n) / 2n ** BigInt(v);
    const J = Math.max(600, 5 * N), g = gapsBig(m, J, 5e7).gaps.slice(100);
    const mx = Math.max(...g.split('0').map(x => x.length));
    if (v2(m + 1n) !== v || v2(u + 1n) !== rho || mx <= prev) ok = false; prev = mx;
    cells.push(`${N}: (${v2(m + 1n)}, ${v2(u + 1n)}, ${mx})`);
  }
  if (!ok) allOk = false;
  out.push(`${v} | ${rho} | ${q} | ${r} | ${s} | ${cells.join(' ')} | ${ok ? '増える' : '増えない'}`);
}
out.push('', allOk ? 'すべての (v, ρ) で w = ρ、連の最大は N とともに増える' : '成り立たないものがある');
console.log(out.join('\n'));
