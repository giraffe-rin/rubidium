/*
 * check_k22.js — 定理 K22（v2(m+1) が奇数の m の、型の始まりの 1 の個数）の確認
 *
 * 何を計算するか:
 *   v = v2(m+1) が奇数、u = (m+1)/2^v、E = m + 2 − 3u、ℓ = v2(E) とする。n₁ を「g_0, g_1, … のうち最初に m+1 になるまでの m+2 の個数」とする。
 *   K22 の主張：
 *     ℓ が奇数なら n₁ = (ℓ+1)/2（K21）。
 *     ℓ が偶数なら、μ := v2(m + 2 − E/2^ℓ) として、μ が奇数なら n₁ = ℓ/2、μ が偶数なら n₁ ≥ ℓ/2 + 1。
 *   5 ≤ m ≤ MMAX で v2(m+1) が奇数のすべての m について、block_rule.js の nextBlock で間隔を求め、主張と照合する。
 *   出力: 場合ごとの個数と食い違い、μ が偶数の場合の n₁ − ℓ/2 の分布。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_k22.js 300000 > data/k22_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const MMAX = +(process.argv[2] || 300000);
const cnt = { odd: 0, evenMuOdd: 0, evenMuEven: 0 }, extra = {}; let bad = 0; const badList = [];
for (let m = 5; m <= MMAX; m += 2) {
  const v = v2(m + 1); if (v % 2 === 0) continue;
  const u = (m + 1) / 2 ** v, E = m + 2 - 3 * u; if (E === 0) continue;
  const l = v2(Math.abs(E));
  let pv = null, n1 = 0;
  for (let j = 0; j < l + 4; j++) { pv = nextBlock(m, pv); if (pv.g === m + 2) n1++; else break; }
  let ok;
  if (l % 2) { cnt.odd++; ok = n1 === (l + 1) / 2; }
  else {
    const Ep = m + 2 - E / 2 ** l, mu = v2(Math.abs(Ep));
    if (mu % 2) { cnt.evenMuOdd++; ok = n1 === l / 2; }
    else { cnt.evenMuEven++; ok = n1 >= l / 2 + 1; const d = n1 - l / 2; extra[d] = (extra[d] || 0) + 1; }
  }
  if (!ok) { bad++; if (badList.length < 30) badList.push(m); }
}
console.log([
  '# 定理 K22 の確認（v2(m+1) が奇数の m の、型の始まりの m+2 の個数 n₁）',
  `# 生成: node --stack-size=65500 code/check_k22.js ${MMAX}`,
  `ℓ が奇数（n₁ = (ℓ+1)/2）: ${cnt.odd} 個`,
  `ℓ が偶数・μ が奇数（n₁ = ℓ/2）: ${cnt.evenMuOdd} 個`,
  `ℓ が偶数・μ が偶数（n₁ ≥ ℓ/2 + 1）: ${cnt.evenMuEven} 個。n₁ − ℓ/2 の分布: ${Object.entries(extra).map(([d, c]) => `${d}: ${c}`).join('、')}`,
  `食い違い: ${bad ? bad + ' 個（' + badList.join(', ') + '）' : 'なし'}`].join('\n'));
