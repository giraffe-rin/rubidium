/*
 * w_class_v7_family.js — v = 7、w = 4 の類の族 a = (2^N − 4641)/29、m = 3a − 2 の型と、m+2 の間隔の連の最大を求める
 *
 * 何を計算するか:
 *   N ≡ 0 (mod 28)、56 ≤ N ≤ NMAX のそれぞれで、v2(m+1)、w = v2(u+1)（u = (m+1)/2^7）を出し、
 *   BigInt 版の遅延評価 gapsBig（lazy_bigint.js）で J = 400, 800, 1600, 3200 ブロックまで計算して型（前周期 p、周期 L）を推測する
 *   （前周期は列の半分以下、周期が 4 回以上見えるもの）。周期の中の m+2 の間隔（1）の連の最大の長さ（巡回して数える）を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/w_class_v7_family.js 616 > data/w_class_v7_family.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const NMAX = +(process.argv[2] || 616);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
function guess(g) {
  for (let L = 1; 3 * L <= g.length; L++) for (let p = 0; 2 * p <= g.length && p + 3 * L <= g.length; p++) {
    let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; }
    if (ok) return [p, L];
  }
  return null;
}
const out = ['# v = 7、w = 4 の族 a = (2^N − 4641)/29、m = 3a − 2', '# 生成: node --stack-size=65500 code/w_class_v7_family.js ' + NMAX,
  'N | v2(m+1) | w | p | L | 周期の中の 1 の連の最大 | 周期の中の 1 の連の長さ（現れる順）'];
for (let N = 56; N <= NMAX; N += 28) {
  const a = (2n ** BigInt(N) - 4641n) / 29n, m = 3n * a - 2n, u = (m + 1n) / 128n;
  let res = null;
  for (const J of [400, 800, 1600, 3200]) { const g = gapsBig(m, J, 5e7).gaps; const pl = guess(g); if (pl && pl[0] + 4 * pl[1] <= J) { res = [pl[0], pl[1], g.slice(pl[0], pl[0] + pl[1])]; break; } }
  if (!res) { out.push(`${N} | ${v2(m + 1n)} | ${v2(u + 1n)} | ? | ? | ? | 型を推測できない`); continue; }
  const per = res[2], k = per.indexOf('0'); const rot = per.slice(k) + per.slice(0, k);   // 0 から始まるように回す
  const runs = rot.split('0').filter(x => x.length).map(x => x.length);
  out.push(`${N} | ${v2(m + 1n)} | ${v2(u + 1n)} | ${res[0]} | ${res[1]} | ${Math.max(...runs)} | ${runs.join(' ')}`);
}
console.log(out.join('\n'));
