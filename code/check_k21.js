/*
 * check_k21.js — 予想 K21 の確認
 *   v = v2(m+1) が奇数、u = (m+1)/2^v、E = m + 2 − 3u、ℓ = v2(E) が奇数なら、
 *   最初の間隔は g_0 = … = g_{(ℓ−1)/2} = m+2、g_{(ℓ+1)/2} = m+1（型の始まりが 1^{(ℓ+1)/2}0）。
 *
 * 何を計算するか:
 *   5 ≤ m ≤ MMAX で v2(m+1) が奇数（v ≤ VMAX）、ℓ が奇数のすべての m について、
 *   block_rule.js の nextBlock で最初の (ℓ+3)/2 ブロックの間隔を求め、予想と照合する。
 *   出力: (v, ℓ) ごとの個数と、食い違い。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_k21.js 300000 15 > data/k21_check.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const MMAX = +(process.argv[2] || 300000), VMAX = +(process.argv[3] || 15);
const cnt = {}; let bad = 0; const badList = [];
for (let m = 5; m <= MMAX; m += 2) {
  const v = v2(m + 1); if (v % 2 === 0 || v > VMAX) continue;
  const u = (m + 1) / 2 ** v, E = m + 2 - 3 * u; if (E === 0) continue;
  const l = v2(Math.abs(E)); if (l % 2 === 0) continue;
  const n1 = (l + 1) / 2; let pv = null, ok = true;
  for (let J = 0; J <= n1; J++) { pv = nextBlock(m, pv); if ((pv.g === m + 2) !== (J < n1)) { ok = false; break; } }
  const k = `v=${v} ℓ=${l}`; cnt[k] = (cnt[k] || 0) + 1;
  if (!ok) { bad++; if (badList.length < 30) badList.push(m); }
}
const out = ['# 予想 K21 の確認（v2(m+1) = v が奇数、ℓ = v2(m + 2 − 3u) が奇数なら、型の始まりが 1^{(ℓ+1)/2}0）',
  `# 生成: node --stack-size=65500 code/check_k21.js ${MMAX} ${VMAX}`,
  `調べた m: ${Object.values(cnt).reduce((a, b) => a + b, 0)} 個。食い違い: ${bad ? bad + ' 個（' + badList.join(', ') + (bad > 30 ? ', …' : '') + '）' : 'なし'}`, '## (v, ℓ) ごとの個数'];
for (const k of Object.keys(cnt).sort((a, b) => { const p = s => s.match(/\d+/g).map(Number); const [x1, y1] = p(a), [x2, y2] = p(b); return x1 - x2 || y1 - y2; })) out.push(`${k}: ${cnt[k]}`);
console.log(out.join('\n'));
