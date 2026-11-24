/*
 * one_runs.js — m+2 の間隔の連（型の周期の列の 1 の連）の最大の長さが、m とともにどう増えるかを調べる
 *
 * 何を計算するか:
 *   v2(m+1) が奇数の 3 ≤ m ≤ 2^KMAX について、type_vs_t.js の gapsLazy で最初の BLOCKS ブロックの間隔を求め、
 *   ブロック BSKIP 以降に現れる m+2 の連（前周期・周期を区別しない）の最大の長さ R(m) を求める。
 *   出力：k ごとに、2^{k−1} < m ≤ 2^k での R(m) の最大と、それを実現する最小の m（2 進表示と v2(m+1)、u mod 64 も）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/one_runs.js 22 300 20 > data/one_runs_22.txt
 */
'use strict';
const { gapsLazy } = require('./type_vs_t');
const [ks, bs, ss] = process.argv.slice(2); const KMAX = +(ks || 22), BLOCKS = +(bs || 200), BSKIP = +(ss || 20);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# m+2 の間隔の連の最大の長さ', `# 生成: node --stack-size=65500 code/one_runs.js ${KMAX} ${BLOCKS} ${BSKIP}`,
  `# R(m)：ブロック ${BSKIP}〜${BLOCKS - 1} の間隔の列での、m+2 の連の最大の長さ（v2(m+1) が奇数の m のみ）`,
  'k | 2^{k−1} < m ≤ 2^k での R の最大 | 実現する最小の m | v2(m+1) | u mod 64 | m+1 の 2 進表示'];
for (let k = 3; k <= KMAX; k++) {
  let best = -1, bm = 0;
  for (let m = 2 ** (k - 1) + 1; m <= 2 ** k; m++) {
    if (v2(m + 1) % 2 === 0) continue;
    const g = gapsLazy(m, BLOCKS); let run = 0, R = 0;
    for (let j = BSKIP; j < BLOCKS; j++) { if (g[j] === 1) { run++; if (run > R) R = run; } else run = 0; }
    if (R > best) { best = R; bm = m; }
  }
  const v = v2(bm + 1);
  out.push(`${k} | ${best} | ${bm} | ${v} | ${((bm + 1) / 2 ** v) % 64} | ${(bm + 1).toString(2)}`);
}
console.log(out.join('\n'));
