/*
 * k47_first_run.js — 定理 K47（間隔の列の先頭の m+2 の連）を数値で確かめる
 *
 * 何を計算するか:
 *   奇数 v = 3..VMAX、偶数 ρ = 2..v−1、q = 2^v − 2^ρ + 1、r = (2^ρ − 1)/3 と、N = v+ρ+1..NMAX のそれぞれについて、
 *   q | s·2^N − r となる最小の奇数 s（1 ≤ s < 2q）をとり、a = (s·2^N − r)/q、m = 3a − 2 とする。
 *   v2(m+1)、w = v2(u+1)（u = (m+1)/2^v）と、間隔の列の先頭の m+2 の連の長さ R（g_0 = … = g_{R−1} = m+2、g_R = m+1）を
 *   BigInt 版の遅延評価 gapsBig（lazy_bigint.js）で求め、
 *   N が偶数のとき、定理 K47 の主張 v2(m+1) = v、w = ρ、R = ⌈(N − v)/ρ⌉ と一致するかを調べる。N が奇数のときは R を出すだけにする（主張の対象外）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k47_first_run.js 11 120 > data/k47_first_run.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const VMAX = +(process.argv[2] || 11), NMAX = +(process.argv[3] || 120);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 定理 K47：間隔の列の先頭の m+2 の連の長さ', '# 生成: node --stack-size=65500 code/k47_first_run.js ' + VMAX + ' ' + NMAX,
  '# 各行：v, ρ, q, r と、N 偶数で主張と一致した個数 / 調べた個数、N 奇数での R − ⌈(N−v)/ρ⌉ の値の分布（「8 以上」は計算した ⌈(N−v)/ρ⌉ + 8 ブロックに m+1 がなかったもの）', 'v | ρ | q | r | N 偶数：一致 / 個数 | N 奇数：R − ⌈(N−v)/ρ⌉ の値（個数）'];
let bad = 0, total = 0;
for (let v = 3; v <= VMAX; v += 2) for (let rho = 2; rho < v; rho += 2) {
  const q = 2n ** BigInt(v) - 2n ** BigInt(rho) + 1n, r = (2n ** BigInt(rho) - 1n) / 3n;
  let ok = 0, cnt = 0; const oddDist = {};
  for (let N = v + rho + 1; N <= NMAX; N++) {
    let s = 1n; while ((s * 2n ** BigInt(N) - r) % q !== 0n) s += 2n;
    const a = (s * 2n ** BigInt(N) - r) / q, m = 3n * a - 2n, u = (m + 1n) / 2n ** BigInt(v);
    const want = Math.ceil((N - v) / rho);
    const g = gapsBig(m, want + 8, 5e7).gaps; const R = g.indexOf('0') < 0 ? Infinity : g.indexOf('0');
    if (N % 2 === 0) { cnt++; total++; if (v2(m + 1n) === v && v2(u + 1n) === rho && R === want) ok++; else { bad++; out.push(`  不一致: v = ${v}, ρ = ${rho}, N = ${N}, s = ${s}, R = ${R}, 主張 ${want}`); } }
    else { const k = R === Infinity ? '8 以上' : String(R - want); oddDist[k] = (oddDist[k] || 0) + 1; }
  }
  out.push(`${v} | ${rho} | ${q} | ${r} | ${ok} / ${cnt} | ${Object.entries(oddDist).map(([k, c]) => k + '（' + c + '）').join(' ')}`);
}
out.push('', `N 偶数：${total} 個中 ${total - bad} 個で一致`);
console.log(out.join('\n'));
