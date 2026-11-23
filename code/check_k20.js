/*
 * check_k20.js — 予想 K20（v2(m+1) = 3、ℓ = v2(5m+13) が 6 以上の偶数なら、ℓ = 2i として「1^{i−1}0」（i が奇数）
 *                 または「1^{i−1}00」（i が偶数）型）の確認
 *
 * 何を計算するか:
 *   (1) 証明書：ℓ = 6, 8, …, LMAX（偶数）について、類 {m : v2(5m+13) = ℓ}（= m ≡ (2^ℓ − 13)/5 (mod 2^{ℓ+1})。
 *       ℓ ≥ 4 なら自動的に m ≡ 7 (mod 16)、つまり v2(m+1) = 3）に、affine_certificate.js の certify を
 *       前周期 0・周期（型の長さ）で当て、型と M_min を出す。
 *   (2) ブロック漸化式：m ≤ MMAX で v2(m+1) = 3、v2(5m+13) が 6 以上の偶数のすべての m について、
 *       block_rule.js の nextBlock で最初の 3 周期分のブロックの間隔を求め、型と一致するか確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_k20.js 34 300000 > data/k20_check.txt
 */
'use strict';
const { certify } = require('./affine_certificate');
const { nextBlock } = require('./block_rule');
const LMAX = +(process.argv[2] || 34), MMAX = +(process.argv[3] || 300000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const want = l => { const i = l / 2; return '1'.repeat(i - 1) + (i % 2 ? '0' : '00'); };
const out = ['# 予想 K20 の確認（v2(m+1) = 3、ℓ = v2(5m+13) = 2i ≥ 6 なら 1^{i−1}0（i 奇数）/ 1^{i−1}00（i 偶数）型）',
  `# 生成: node --stack-size=65500 code/check_k20.js ${LMAX} ${MMAX}`, '', '## (1) 証明書: ℓ | 類 | 型 | M_min | 事実の個数'];
let certOk = true;
for (let l = 6; l <= LMAX; l += 2) {
  const M = 2n ** BigInt(l + 1); let inv = 1n; for (let x = 1n; ; x += 2n) if ((5n * x) % M === 1n) { inv = x; break; }
  const B = Number((((2n ** BigInt(l) - 13n) % M + M) % M * inv) % M), A = 2 ** (l + 1), w = want(l);
  let line;
  try { const r = certify(A, B, 0, w.length, 1e6); const g = r.gaps.join(''); if (g !== w) certOk = false;
    line = `ℓ=${l} | m ≡ ${B} (mod 2^${l + 1}) | ${g}${g === w ? '' : ' （型が違う）'} | ${A * r.tmin + B} | ${r.n}`; }
  catch (e) { certOk = false; line = `ℓ=${l} | 失敗: ${e.message || e.constructor.name}`; }
  out.push(line);
}
out.push(`証明書: ${certOk ? 'すべて成功（型は予想のとおり）' : '失敗あり'}`, '', '## (2) ブロック漸化式による確認');
let cnt = 0, bad = 0; const byL = {};
for (let m = 7; m <= MMAX; m += 16) {
  const l = v2(5 * m + 13); if (l < 6 || l % 2) continue;
  const w = want(l), L = w.length; let pv = null, ok = true;
  for (let J = 0; J < 3 * L; J++) { pv = nextBlock(m, pv); if (String(pv.g - m - 1) !== w[J % L]) { ok = false; break; } }
  cnt++; byL[l] = (byL[l] || 0) + 1; if (!ok) { bad++; out.push(`食い違い: m = ${m}`); }
}
out.push(`調べた m: ${cnt} 個（ℓ ごと: ${Object.entries(byL).map(([l, c]) => `ℓ=${l}: ${c}`).join('、')}）。食い違い: ${bad ? bad + ' 個' : 'なし'}`);
console.log(out.join('\n'));
