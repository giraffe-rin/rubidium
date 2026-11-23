/*
 * check_k29_v5.js — 定理 K29.1（v2(m+1) = 5、u ≡ 1 (mod 4) なら g_0 = g_3 = m+2、g_1 = g_2 = m+1）の証明の中の事実の確認
 *
 * 何を計算するか:
 *   31 ≤ m ≤ MMAX で v2(m+1) = 5、u = (m+1)/32 ≡ 1 (mod 4) のすべての m について、block_rule.js の nextBlock で S_0〜S_3 を求め、
 *   証明（notes/2026-11-23-claude-1-k29-v5-first.md）で使う次の事実を確かめる。
 *     S_1：u ∉、2u ∈、4u ∉、8u ∈、16u ∉、5u ∉、9u ∉、10u ∈、18u ∈、20u ∉、24u について 22u ∈ S_1 ⇒ 28u ∈ S_1
 *     S_2：4u ∉、8u ∈、16u ∉、18u ∉、24u ∉
 *     S_3：4u ∈、8u ∉、16u ∈
 *     間隔：g_0 = m+2、g_1 = g_2 = m+1、g_3 = m+2
 *   あわせて、ブロック 4 以降も 1 0 0 の繰り返しか（最初の 12 ブロック）を数える（周期性は証明していない部分）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_k29_v5.js 300000 > data/k29_v5_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const MMAX = +(process.argv[2] || 300000);
let n = 0, bad = [], per = 0;
for (let m = 31; m <= MMAX; m += 128) {   // m ≡ 31 (mod 128) ⇔ v2(m+1) = 5 かつ u ≡ 1 (mod 4)
  const u = (m + 1) / 32; const S = []; const g = []; let pv = null;
  for (let j = 0; j < 12; j++) { pv = nextBlock(m, pv); S.push(pv.S); g.push(pv.g - m - 1); }
  const has = (j, c) => !!S[j][c * u];
  const ok =
    g[0] === 1 && g[1] === 0 && g[2] === 0 && g[3] === 1 &&
    !has(1, 1) && has(1, 2) && !has(1, 4) && has(1, 8) && !has(1, 16) && !has(1, 5) && !has(1, 9) && has(1, 10) && has(1, 18) && !has(1, 20) &&
    (!has(1, 22) || has(1, 28)) &&
    !has(2, 4) && has(2, 8) && !has(2, 16) && !has(2, 18) && !has(2, 24) &&
    has(3, 4) && !has(3, 8) && has(3, 16);
  n++; if (!ok) bad.push(m);
  if (g.join('') === '100'.repeat(4)) per++;
}
console.log([
  '# 定理 K29.1 の証明の中の事実の確認（v2(m+1) = 5、u ≡ 1 (mod 4)）',
  `# 生成: node --stack-size=65500 code/check_k29_v5.js ${MMAX}`,
  `調べた m: ${n} 個（31 ≤ m ≤ ${MMAX}、m ≡ 31 (mod 128)）。証明の中の事実との食い違い: ${bad.length ? bad.slice(0, 30).join(', ') : 'なし'}`,
  `最初の 12 ブロックが 100 の繰り返しの m: ${per} 個（周期性は証明していない部分）`].join('\n'));
