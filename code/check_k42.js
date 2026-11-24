/*
 * check_k42.js — 定理 K42 の証明の 2 つの段階をブロック漸化式で確かめる
 *
 * 何を計算するか:
 *   v ∈ {2, 4, 6}、奇数 u（3 ≤ u ≤ UMAX）で m = 2^v u − 1、m' = u − 1 とし、block_rule.js の nextBlock でブロック 0〜J−1 を作って、
 *     (補題) v2(d) ≤ v − 1 の距離 d は、どのブロックでも「v2(d) が偶数 ⇔ 入る」で、間隔はいつも m+1
 *     (Φ) 1 ≤ d' ≤ m' について、[2^v d' ∈ S_j(m)] = [d' ∈ S_j(m')]
 *   の違反の個数を数える。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k42.js 61 40 > data/k42_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const [UMAX, J] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
let bad1 = 0, bad2 = 0, tot = 0, facts = 0;
for (const v of [2, 4, 6]) for (let u = 3; u <= UMAX; u += 2) {
  const m = 2 ** v * u - 1, mp = u - 1; let pv = null, pq = null;
  for (let j = 0; j < J; j++) {
    pv = nextBlock(m, pv); pq = nextBlock(mp, pq); tot++; if (pv.g !== m + 1) bad1++;
    for (let d = 1; d <= m; d++) { const t = v2(d); facts++;
      if (t <= v - 1) { if ((pv.S[d] === 1) !== (t % 2 === 0)) bad1++; }
      else { const dp = d / 2 ** v; if (Number.isInteger(dp) && dp <= mp && (pv.S[d] === 1) !== (pq.S[dp] === 1)) bad2++; } }
  }
}
console.log(['# 定理 K42 の証明の段階の確認', `# 生成: node code/check_k42.js ${UMAX} ${J}`, `調べた (m, ブロック): ${tot}、事実: ${facts}`, `補題（v2 ≤ v−1 の距離と間隔）の違反: ${bad1}`, `Φ の部分（2^v d′ と m′ の d′）の違反: ${bad2}`].join(String.fromCharCode(10)));
