/*
 * check_k14.js — 定理 K14（k ≥ 2 で v2(Q_k) が偶数のときの g₀〜g₄）をブロック漸化式で確かめる
 *
 * 何を計算するか:
 *   v2(m+1) = 1、v2(3h+1) = 2k（k ≥ 2）、w = (3h+1)/2^{2k}、Q_k = (m+2+w)/2 で、v2(Q_k) が偶数の各 m（m ≤ M）について、
 *   ブロック漸化式（code/block_rule.js の nextBlock）でブロック 0〜4 の間隔 g₀〜g₄ を求める。
 *   定理 K14 の主張「g₀ g₁ g₂ g₃ g₄ − (m+1) = 1 1 0 1 x、x = 1 ⇔ v2(Q_k) ≥ 2」との食い違いを数える。
 *   さらに (k, v2(Q_k)) ごとの個数を出す。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k14.js 200000 > data/k14_check.txt
 */
'use strict';

const { nextBlock } = require('./block_rule');
const M = +(process.argv[2] || 200000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };

const tab = {}; const fails = []; let n = 0;
for (let m = 5; m <= M; m += 4) {
  const h = (m + 1) / 2;
  const a = v2(3 * h + 1);
  if (a % 2 === 1 || a < 4) continue;
  const k = a / 2;
  const w = (3 * h + 1) / 2 ** a;
  const q = v2((m + 2 + w) / 2);
  if (q % 2 === 1) continue;
  let p = null; const g = [];
  for (let j = 0; j < 5; j++) { p = nextBlock(m, p); g.push(p.g - m - 1); }
  if (g.join('') !== '1101' + (q >= 2 ? 1 : 0)) fails.push(m);
  const key = `k=${k} v2(Q_k)=${q >= 4 ? '4 以上' : q} g0..g4=${g.join('')}`;
  tab[key] = (tab[key] || 0) + 1; n++;
}
const out = ['# 定理 K14 の検証（v2(m+1) = 1、v2(3h+1) = 2k ≥ 4、v2(Q_k) が偶数の m、ブロック漸化式による）',
  `# 生成: node code/check_k14.js ${M}`,
  `調べた m: ${n} 個。K14 との食い違い: ${fails.length === 0 ? 'なし' : fails.slice(0, 20).join(', ')}`,
  '集計（k、v2(Q_k)、g₀〜g₄ − (m+1)）:'];
for (const key of Object.keys(tab).sort()) out.push(`  ${key}: ${tab[key]}`);
process.stdout.write(out.join('\n') + '\n');
