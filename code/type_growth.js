/*
 * type_growth.js — 型（ブロックの間隔の前周期と周期）の種類の数が、m とともにどう増えるかを数える
 *
 * 何を計算するか:
 *   2 ≤ m ≤ 2^KMAX のすべての m について、type_vs_t.js の typeOf（遅延評価のブロック漸化式、300 ブロックから推測）で型を求める。
 *   型は「前周期の列 | 周期の列」で、周期の列は巡回させて辞書順最小にそろえる（前周期を含めた同一視はしない）。
 *   出力：k = 4, …, KMAX ごとに、m ≤ 2^k での型の種類の数（全体と、v2(m+1) = 0, 1, 2, 3, 4, 5 以上ごと）、
 *         2^{k−1} < m ≤ 2^k で初めて現れた型の個数、推測できなかった m の個数、L の最大値。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/type_growth.js 18 > data/type_growth_18.txt
 */
'use strict';
const { typeOf } = require('./type_vs_t');
const KMAX = +(process.argv[2] || 18);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const canon = ty => { if (ty === '?') return ty; const [pre, per] = ty.split('|'); let best = per; for (let i = 1; i < per.length; i++) { const r = per.slice(i) + per.slice(0, i); if (r < best) best = r; } return pre + '|' + best; };
const all = new Set(), byV = [0, 1, 2, 3, 4, 5].map(() => new Set());
let unk = 0, Lmax = 0, prevSize = 0;
const out = ['# 型の種類の数の m による増え方', `# 生成: node --stack-size=65500 code/type_growth.js ${KMAX}`,
  'k | m ≤ 2^k の型の種類 | 2^{k−1} < m ≤ 2^k で初めて現れた型 | v2(m+1) = 0, 1, 2, 3, 4, ≥5 ごとの種類 | 推測できなかった m（累計）| L の最大（累計）'];
let m = 2;
for (let k = 2; k <= KMAX; k++) {
  for (; m <= 2 ** k; m++) {
    const ty = canon(typeOf(m)); if (ty === '?') { unk++; continue; }
    all.add(ty); byV[Math.min(5, v2(m + 1))].add(ty); const L = ty.split('|')[1].length; if (L > Lmax) Lmax = L;
  }
  if (k >= 4) out.push(`${k} | ${all.size} | ${all.size - prevSize} | ${byV.map(s => s.size).join(', ')} | ${unk} | ${Lmax}`);
  prevSize = all.size;
}
console.log(out.join('\n'));
