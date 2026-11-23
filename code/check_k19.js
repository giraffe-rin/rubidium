/*
 * check_k19.js — 定理 K19（v2(m+1) = 1、r = v2(h−1) が奇数なら「1^{j+1}0」型、r = 2j+1）の確認
 *
 * 何を計算するか:
 *   (1) 証明書：r = 1, 3, …, RMAX（奇数）について、類 m ≡ 2^{r+1}+1 (mod 2^{r+2})（= v2(m+1) = 1 かつ v2(h−1) = r）に
 *       affine_certificate.js の certify を前周期 0・周期 j+2 で当て、型が 1^{j+1}0 で M_min を出す。
 *   (2) ブロック漸化式：5 ≤ m ≤ MMAX で v2(m+1) = 1、v2(h−1) が奇数のすべての m について、
 *       block_rule.js の nextBlock で最初の 3(j+2) ブロックの間隔を求め、型と一致するか確かめる。
 *       さらに、証明の階段（ログの補題）：ブロック n（0 ≤ n ≤ j）で a_i ∈ S_n ⇔ i+n ≤ j（1 ≤ i ≤ min(j, j−n+1)）、
 *       b_i ∈ S_n ⇔ i = j−n（0 ≤ i ≤ j−n）も、ブロック 0〜j と j+2〜2j+2 で確かめる。
 *       a_i = h − D(4^i−1)/(3·4^i)、b_i = h + 1 + D(2·4^i+1)/(3·2^{2i+1})、D = h − 1。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_k19.js 41 200000 > data/k19_check.txt
 */
'use strict';
const { certify } = require('./affine_certificate');
const { nextBlock } = require('./block_rule');
const RMAX = +(process.argv[2] || 41), MMAX = +(process.argv[3] || 200000);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = [`# 定理 K19 の確認（v2(m+1) = 1、r = v2(h−1) = 2j+1 なら 1^{j+1}0 型）`,
  `# 生成: node --stack-size=65500 code/check_k19.js ${RMAX} ${MMAX}`, '', '## (1) 証明書: r | 型 | M_min | 事実の個数'];
let certOk = true;
for (let r = 1; r <= RMAX; r += 2) {
  const j = (r - 1) / 2, A = 2 ** (r + 2), B = 2 ** (r + 1) + 1;
  let line;
  try {
    const res = certify(A, B, 0, j + 2, 1e6); const g = res.gaps.join('');
    const want = '1'.repeat(j + 1) + '0'; if (g !== want) certOk = false;
    line = `r=${r} | ${g}${g === want ? '' : ' （型が違う）'} | ${A * res.tmin + B} | ${res.n}`;
  } catch (e) { certOk = false; line = `r=${r} | 失敗: ${e.message || e.constructor.name}`; }
  out.push(line);
}
out.push(`証明書: ${certOk ? 'すべて成功（型は 1^{j+1}0）' : '失敗あり'}`, '', '## (2) ブロック漸化式による確認');
let cnt = 0, bad = 0; const byR = {};
for (let m = 5; m <= MMAX; m += 4) {
  const h = (m + 1) / 2, D = h - 1, r = v2(D); if (r % 2 === 0) continue;
  const j = (r - 1) / 2, L = j + 2;
  const a = i => h - D / 4 ** i * (4 ** i - 1) / 3, b = i => h + 1 + D / 2 ** (2 * i + 1) * (2 * 4 ** i + 1) / 3;
  let pv = null, ok = true;
  for (let J = 0; J < 3 * L && ok; J++) {
    pv = nextBlock(m, pv); const n = J % L;
    if ((pv.g === m + 2) !== (n <= j)) ok = false;
    if (n <= j && J < 2 * L) {
      for (let i = 1; i <= Math.min(j, j - n + 1); i++) if (!!pv.S[a(i)] !== (i + n <= j)) ok = false;
      for (let i = 0; i <= j - n; i++) if (!!pv.S[b(i)] !== (i === j - n)) ok = false;
    }
  }
  cnt++; byR[r] = (byR[r] || 0) + 1; if (!ok) { bad++; out.push(`食い違い: m = ${m}`); }
}
out.push(`調べた m: ${cnt} 個（r ごと: ${Object.entries(byR).map(([r, c]) => `r=${r}: ${c}`).join('、')}）。食い違い: ${bad ? bad + ' 個' : 'なし'}`);
console.log(out.join('\n'));
