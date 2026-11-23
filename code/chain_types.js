/*
 * chain_types.js — v2(m+1) = V の m について、E = m + 2 − 3u（u = (m+1)/2^V）の付値と型の表を作る
 *
 * 何を計算するか:
 *   K19（V = 1、E = −(h−1)）と K20（V = 3、E = 5u+1）に共通する数 E = m + 2 − 3u の付値 ℓ = v2(E) ごとに、
 *   m ≤ MMAX、ℓ ≥ LMIN の m の型（前周期|周期）を block_rule.js の nextBlock で 500 ブロック求め、
 *   affine_certificate.js の guess で前周期と周期を推測して数える。
 *   出力: ℓ ごとに、型と個数（多い順）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/chain_types.js 5 120000 5 > data/chain_types_v5.txt
 *   （引数: V MMAX LMIN）
 */
'use strict';
const { guess } = require('./affine_certificate');
const { nextBlock } = require('./block_rule');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const V = +process.argv[2], MMAX = +process.argv[3], LMIN = +process.argv[4];
const by = {};
for (let m = 2 ** V - 1; m <= MMAX; m += 2 ** (V + 1)) {
  if (m < 5) continue;
  const u = (m + 1) / 2 ** V, E = m + 2 - 3 * u; if (E === 0) continue;
  const l = v2(Math.abs(E)); if (l < LMIN) continue;
  let pv = null; const g = []; for (let j = 0; j < 500; j++) { pv = nextBlock(m, pv); g.push(pv.g - m - 1); }
  const pl = guess(m, 500);
  const t = pl ? (g.slice(0, pl[0]).join('') || '-') + '|' + g.slice(pl[0], pl[0] + pl[1]).join('') : '?';
  (by[l] = by[l] || {})[t] = (by[l][t] || 0) + 1;
}
const out = [`# E = m + 2 − 3u の付値ごとの型（v2(m+1) = ${V}、m ≤ ${MMAX}、ℓ ≥ ${LMIN}）`, `# 生成: node --stack-size=65500 code/chain_types.js ${V} ${MMAX} ${LMIN}`];
for (const l of Object.keys(by).sort((a, b) => a - b)) {
  const e = Object.entries(by[l]).sort((a, b) => b[1] - a[1]);
  out.push(`ℓ=${l}（${e.reduce((s, x) => s + x[1], 0)} 個、型 ${e.length} 種類）: ` + e.slice(0, 8).map(([t, c]) => `${t} ×${c}`).join('、') + (e.length > 8 ? '、…' : ''));
}
console.log(out.join('\n'));
