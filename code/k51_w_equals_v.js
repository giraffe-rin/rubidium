/*
 * k51_w_equals_v.js — 定理 K47b の族（w = v の類）で、間隔の列のすべての m+2 の極大な連の長さが R になる (R, e) を調べる（予想 K51）
 *
 * 何を計算するか:
 *   奇数 v = 3..VMAX、ρ = v + 1、Q = 2^v − 1、r = (2^{v+1} − 1)/3 と、R = 3..RMAX、e ∈ {1, 3, …, ρ − 1} について、
 *   N = v + ρ(R − 1) + e（偶数、⌈(N−v)/ρ⌉ = R）、σ は Q | σ·2^N + r となる最小の奇数、a = (σ·2^N + r)/Q、m = 3a − 2 とし、
 *   gapsBig（lazy_bigint.js）で J = 4(R + v) + 60 ブロックの間隔を求め、中で完結する m+2 の連がすべて長さ R か（2 個以上あること）を調べる。
 *   出力：v と e ごとに、成り立つ R の一覧。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k51_w_equals_v.js 9 61 > data/k51_w_equals_v.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const VMAX = +(process.argv[2] || 9), RMAX = +(process.argv[3] || 61);
const out = ['# 予想 K51：w = v の類（定理 K47b の族）で、すべての m+2 の連の長さが R になる R', '# 生成: node --stack-size=65500 code/k51_w_equals_v.js ' + VMAX + ' ' + RMAX, 'v | e | 成り立つ R（3 ≤ R ≤ ' + RMAX + '）'];
for (let v = 3; v <= VMAX; v += 2) {
  const rho = v + 1, Q = 2n ** BigInt(v) - 1n, r = (2n ** BigInt(rho) - 1n) / 3n;
  for (let e = 1; e < rho; e += 2) {
    const okR = [];
    for (let R = 3; R <= RMAX; R++) {
      const N = v + rho * (R - 1) + e; let sg = 1n; while ((sg * 2n ** BigInt(N) + r) % Q !== 0n) sg += 2n;
      const a = (sg * 2n ** BigInt(N) + r) / Q, m = 3n * a - 2n;
      const J = 4 * (R + v) + 60, g = gapsBig(m, J, 5e7).gaps; const ones = []; let i = 0;
      while (i < J) { let j = i; while (j < J && g[j] === g[i]) j++; if (j < J && g[i] === '1') ones.push(j - i); i = j; }
      if (ones.length >= 2 && ones.every(x => x === R)) okR.push(R);
    }
    out.push(`${v} | ${e} | ${okR.join(' ') || '-'}`);
  }
}
console.log(out.join('\n'));
