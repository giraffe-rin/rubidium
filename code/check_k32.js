/*
 * check_k32.js — 定理 K32（m+1 の間隔の連は (v+1)/2 以下）とその補題 Q_n をブロック漸化式で確かめる
 *
 * 何を計算するか:
 *   v = v2(m+1) が奇数の 3 ≤ m ≤ MMAX について、block_rule.js の nextBlock で J ブロック計算し、次を調べる。
 *     - 補題 Q_n：m+1 の間隔の直後から数えて n 個目の E 型ブロック（g_{j} = … = g_{j+n−1} = m+1 のときのブロック j+n）で、
 *       v2(d) = b ≤ min(2n−1, v−1) の 1 ≤ d ≤ m について「d ∈ S ⇔ b が偶数」が成り立つか（違反の個数）
 *     - 定理 K32：m+1 の間隔の連の長さの最大が (v+1)/2 以下か（違反の個数）、最大がちょうど (v+1)/2 の m の個数
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k32.js 3000 60 > data/k32_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const MMAX = +(process.argv[2] || 3000), J = +(process.argv[3] || 60);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const byV = {}; let qViol = 0, qChecked = 0, kViol = 0;
for (let m = 3; m <= MMAX; m += 2) {
  const v = v2(m + 1); if (v % 2 === 0) continue;
  let pv = null, run = 0, maxRun = 0;
  for (let j = 0; j < J; j++) {
    const cur = nextBlock(m, pv);
    if (j >= 1 && pv.g === m + 1) {   // ブロック j は E 型。run は直前までの m+1 の連の長さ（ブロック j は run 個目の E 型ブロック）
      const n = run, bmax = Math.min(2 * n - 1, v - 1);
      for (let d = 1; d <= m; d++) { const b = v2(d); if (b > bmax) continue; qChecked++; if ((cur.S[d] === 1) !== (b % 2 === 0)) qViol++; }
    }
    if (cur.g === m + 1) { run++; if (run > maxRun) maxRun = run; } else run = 0;
    pv = cur;
  }
  const s = (byV[v] = byV[v] || { n: 0, atMax: 0, viol: 0 }); s.n++;
  if (maxRun > (v + 1) / 2) { s.viol++; kViol++; } if (maxRun === (v + 1) / 2) s.atMax++;
}
const out = ['# 定理 K32 と補題 Q_n の確認（ブロック漸化式）', `# 生成: node code/check_k32.js ${MMAX} ${J}`,
  `補題 Q_n：調べた (ブロック, d) ${qChecked} 個、違反 ${qViol} 個`, `定理 K32：違反 ${kViol} 個`, '', 'v | m の個数 | 連の最大が (v+1)/2 に等しい m | 違反'];
for (const [v, s] of Object.entries(byV)) out.push(`${v} | ${s.n} | ${s.atMax} | ${s.viol}`);
console.log(out.join('\n'));
