/*
 * check_k23.js — 予想 K23（型の始まりの 1 の個数 n₁ の再帰式）の確認
 *
 * 何を計算するか:
 *   v = v2(m+1) が奇数の m について、u = (m+1)/2^v から次の再帰で F(u) を計算し、n₁ と比べる。
 *     F(x)：E = m + 2 − 3x、ℓ = v2(E)。
 *       ℓ が奇数なら (ℓ+1)/2。
 *       ℓ が偶数なら c = (m + 2 − E/2^ℓ)/3、μ = v2(c)。μ が奇数なら ℓ/2、偶数なら ℓ/2 + F(|c|/2^μ)。
 *   n₁ は、g_0 から数えて最初に m+1 になるまでの m+2 の個数（block_rule.js の nextBlock で求める）。
 *   出力: 再帰の深さごとの個数、食い違った m の一覧。
 *   定理 K23 は「m ≠ 9 なら n₁ = F(u)」（再帰が有限回で終わるとき）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_k23.js 300000 > data/k23_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const MMAX = +(process.argv[2] || 300000);
function F(m, x, depth) {
  const E = m + 2 - 3 * x; if (E === 0) return [Infinity, depth];
  const l = v2(Math.abs(E)); if (l % 2) return [(l + 1) / 2, depth];
  const c = (m + 2 - E / 2 ** l) / 3; if (c === 0) return [Infinity, depth];
  const mu = v2(Math.abs(c)); if (mu % 2) return [l / 2, depth];
  const [r, d] = F(m, Math.abs(c) / 2 ** mu, depth + 1); return [l / 2 + r, d];
}
const byDepth = {}; let bad = 0; const badList = [], undef = [];
for (let m = 5; m <= MMAX; m += 2) {
  const v = v2(m + 1); if (v % 2 === 0) continue;
  const u = (m + 1) / 2 ** v;
  const [pred, depth] = F(m, u, 0);
  if (!Number.isFinite(pred)) { undef.push(m); continue; }
  let pv = null, n1 = 0;
  for (let j = 0; j < pred + 3; j++) { pv = nextBlock(m, pv); if (pv.g === m + 2) n1++; else break; }
  byDepth[depth] = (byDepth[depth] || 0) + 1;
  if (n1 !== pred) { bad++; if (badList.length < 30) badList.push(`${m}（n₁ = ${n1}、F = ${pred}）`); }
}
console.log([
  '# 定理 K23 の確認（v2(m+1) が奇数の m で、型の始まりの 1 の個数 n₁ = F(u)）',
  `# 生成: node --stack-size=65500 code/check_k23.js ${MMAX}`,
  `調べた m: ${Object.values(byDepth).reduce((a, b) => a + b, 0)} 個（再帰の深さごと: ${Object.entries(byDepth).map(([d, c]) => `${d}: ${c}`).join('、')}）`,
  `F が定義できない m（E = 0 または c = 0）: ${undef.length ? undef.join(', ') : 'なし'}`,
  `食い違い: ${bad ? bad + ' 個: ' + badList.join(', ') : 'なし'}`].join('\n'));
