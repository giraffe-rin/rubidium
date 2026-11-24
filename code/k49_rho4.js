/*
 * k49_rho4.js — 定理 K49（ρ = 4、R 奇数で、間隔の列のすべての m+2 の極大な連の長さが R、各連の後に m+1 が 2 個以上）を数値で確かめる
 *
 * 何を計算するか:
 *   奇数 v = 5..VMAX、q = 2^v − 15、r = 5（定理 K47 の ρ = 4）、偶数 N = v+17..NMAX で R = ⌈(N − v)/4⌉ が奇数のものについて、
 *   q·a + r = s·2^N（s は最小の正の奇数で a が奇数）、m = 3a − 2 とし、gapsBig（lazy_bigint.js）で J = max(400, 10N) ブロックの間隔を求める。
 *   ブロック 0..J−1 の中で完結する m+2 の極大な連の長さがすべて R か、m+1 の極大な連の長さがすべて 2 以上 ⌈v/2⌉ 以下かを調べる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k49_rho4.js 15 200 > data/k49_rho4.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const VMAX = +(process.argv[2] || 15), NMAX = +(process.argv[3] || 200);
const out = ['# 定理 K49：ρ = 4、R 奇数の族の間隔の列の連', '# 生成: node --stack-size=65500 code/k49_rho4.js ' + VMAX + ' ' + NMAX,
  'v | q | N の個数 | m+2 の連がすべて R | m+1 の連がすべて 2..⌈v/2⌉ | m+1 の連の長さの範囲 | 例外'];
let tot = 0, totBad = 0;
for (let v = 5; v <= VMAX; v += 2) {
  const q = 2n ** BigInt(v) - 15n, r = 5n; let n = 0, ok1 = 0, ok0 = 0, zmin = Infinity, zmax = 0; const bad = [];
  for (let N = v + 17; N <= NMAX; N += 2) {   // v は奇数なので N は偶数
    const R = Math.ceil((N - v) / 4); if (R % 2 === 0) continue;
    let s = 1n; while ((s * 2n ** BigInt(N) - r) % q !== 0n) s += 2n;
    const a = (s * 2n ** BigInt(N) - r) / q, m = 3n * a - 2n; n++;
    const J = Math.max(400, 10 * N), g = gapsBig(m, J, 5e7).gaps;
    const ones = [], zeros = []; let i = 0;
    while (i < J) { let j = i; while (j < J && g[j] === g[i]) j++; if (j < J) (g[i] === '1' ? ones : zeros).push(j - i); i = j; }
    const a1 = ones.length > 0 && ones.every(x => x === R), a0 = zeros.length > 0 && zeros.every(x => x >= 2 && x <= Math.ceil(v / 2));
    for (const z of zeros) { zmin = Math.min(zmin, z); zmax = Math.max(zmax, z); }
    if (a1) ok1++; if (a0) ok0++; if (!a1 || !a0) bad.push(`N = ${N}`);
  }
  tot += n; totBad += bad.length;
  out.push(`${v} | ${q} | ${n} | ${ok1} | ${ok0} | ${zmin}..${zmax} | ${bad.join('; ') || '-'}`);
}
out.push('', `${tot} 個中 ${tot - totBad} 個で成り立つ`);
console.log(out.join('\n'));
