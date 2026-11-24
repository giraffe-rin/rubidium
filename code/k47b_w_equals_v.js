/*
 * k47b_w_equals_v.js — 定理 K47b（ρ = v + 1、w = v の類）の間隔の列の先頭の m+2 の連を数値で確かめる
 *
 * 何を計算するか:
 *   奇数 v = 3..VMAX、ρ = v + 1、Q = 2^v − 1（q = −Q）、r = (2^{v+1} − 1)/3 と、偶数 N = 2v+2..NMAX のそれぞれについて、
 *   Q | σ·2^N + r となる最小の奇数 σ > 0 をとり、a = (σ·2^N + r)/Q、m = 3a − 2 とする（q·a + r = s·2^N で s = −σ）。
 *   v2(m+1)、w = v2(u+1)（u = (m+1)/2^v）と、間隔の列の先頭の m+2 の連の長さ R（g_0 = … = g_{R−1} = m+2、g_R = m+1）を
 *   BigInt 版の遅延評価 gapsBig（lazy_bigint.js）で求め、定理 K47b の主張 v2(m+1) = v、w = v、R = ⌈(N − v)/(v + 1)⌉ と一致するかを調べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k47b_w_equals_v.js 21 240 > data/k47b_w_equals_v.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const VMAX = +(process.argv[2] || 21), NMAX = +(process.argv[3] || 240);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 定理 K47b：w = v の類の間隔の列の先頭の m+2 の連の長さ', '# 生成: node --stack-size=65500 code/k47b_w_equals_v.js ' + VMAX + ' ' + NMAX,
  'v | Q = 2^v − 1 | r | 一致 / 個数（N 偶数） | 例（N: σ, R）'];
let bad = 0, total = 0;
for (let v = 3; v <= VMAX; v += 2) {
  const rho = v + 1, Q = 2n ** BigInt(v) - 1n, r = (2n ** BigInt(rho) - 1n) / 3n;
  let ok = 0, cnt = 0; const ex = [];
  for (let N = 2 * v + 2; N <= NMAX; N += 2) {
    let sg = 1n; while ((sg * 2n ** BigInt(N) + r) % Q !== 0n) sg += 2n;
    const a = (sg * 2n ** BigInt(N) + r) / Q, m = 3n * a - 2n, u = (m + 1n) / 2n ** BigInt(v);
    const want = Math.ceil((N - v) / rho);
    const g = gapsBig(m, want + 8, 5e7).gaps; const R = g.indexOf('0') < 0 ? Infinity : g.indexOf('0');
    cnt++; total++;
    if (a % 2n === 1n && v2(m + 1n) === v && v2(u + 1n) === v && R === want) ok++; else { bad++; out.push(`  不一致: v = ${v}, N = ${N}, σ = ${sg}, R = ${R}, 主張 ${want}`); }
    if (ex.length < 3) ex.push(`${N}: ${sg}, ${R}`);
  }
  out.push(`${v} | ${Q} | ${r} | ${ok} / ${cnt} | ${ex.join('; ')}`);
}
out.push('', `${total} 個中 ${total - bad} 個で一致`);
console.log(out.join('\n'));
