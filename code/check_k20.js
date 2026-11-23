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
 *       さらに、証明（notes/2026-11-23-claude-1-proof-k20.md）の主張 Q(n) と最後のブロックの事実を、最初の 2 周期で確かめる。
 *       u = (m+1)/8、E = 5u+1、λ = v2(E)、K = (λ−1)/2、c_k = (4^k(8u+1) − E)/(3·4^k)、d_k = 2c_k、f_r = 8u+1 − E/2^r。
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
  const w = want(l), L = w.length, i = l / 2; let pv = null, ok = true;
  const u = (m + 1) / 8, E = 5 * u + 1, K = (l - 3 - 1) / 2;
  const c = k => (4 ** k * (8 * u + 1) - E) / (3 * 4 ** k), d = k => 2 * c(k), f = r => 8 * u + 1 - E / 2 ** r;
  const has = (S, x) => { if (!Number.isInteger(x) || x < 1 || x > m) throw new Error('範囲外 ' + x); return !!S[x]; };
  for (let J = 0; J < 3 * L; J++) {
    pv = nextBlock(m, pv); if (String(pv.g - m - 1) !== w[J % L]) { ok = false; break; }
    const n = J % L; if (J >= 2 * L) continue;
    try {
      if (n <= i - 2) {   // 主張 Q(n)
        if (!has(pv.S, u) || has(pv.S, 2 * u) || !has(pv.S, 4 * u)) ok = false;
        for (let k = 1; k <= Math.min(K, K - n + 1); k++) if (has(pv.S, c(k)) !== (k <= K - n)) ok = false;
        for (let k = 1; k <= K + 1 - n; k++) if (has(pv.S, d(k)) !== (k === K + 1 - n)) ok = false;
        if (has(pv.S, f(i - 1 - n)) !== (n % 2 === 0)) ok = false;
      } else if (n === i - 1) {   // 最初の間隔 m+1 のブロック
        if (has(pv.S, u) || !has(pv.S, 2 * u) || has(pv.S, 4 * u)) ok = false;
        if (has(pv.S, 3 * u) !== (i % 2 === 1) || has(pv.S, 6 * u) !== (i % 2 === 0)) ok = false;
      } else {   // i が偶数のときの 2 つ目の間隔 m+1 のブロック（E 型）
        if (!has(pv.S, u) || has(pv.S, 2 * u) || !has(pv.S, 3 * u) || has(pv.S, 4 * u) || has(pv.S, 6 * u)) ok = false;
      }
    } catch (e) { ok = false; }
  }
  cnt++; byL[l] = (byL[l] || 0) + 1; if (!ok) { bad++; out.push(`食い違い: m = ${m}`); }
}
out.push(`調べた m: ${cnt} 個（ℓ ごと: ${Object.entries(byL).map(([l, c]) => `ℓ=${l}: ${c}`).join('、')}）。食い違い: ${bad ? bad + ' 個' : 'なし'}`);
console.log(out.join('\n'));
