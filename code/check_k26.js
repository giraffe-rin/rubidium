/*
 * check_k26.js — 予想 K26（v2(m+1) = 3、ℓ = v2(5u+1) = 1 の m の型）の確認
 *   u = (m+1)/8、p := v2((11u+1)/2)（ℓ = 1 なら p ≥ 1）。予想：m ≠ 7 で、p = 1 なら「10」型、p が偶数なら「100」型（どちらも前周期なし）。
 *
 * 何を計算するか:
 *   (1) 証明書：p = 1, 2, …, PMAX について、類 {m : v2(m+1) = 3, ℓ = 1, v2((11u+1)/2) = p}
 *       （= m ≡ 8u₀ − 1 (mod 2^{p+5})、11u₀ + 1 ≡ 2^{p+1} (mod 2^{p+2})）に affine_certificate.js の certify を
 *       前周期 0・周期 2（p 奇数）/ 3（p 偶数）で当てる。p が奇数（≥ 3）の類は型が 1 つに決まらないので、失敗が期待どおり。
 *   (2) ブロック漸化式：m ≤ MMAX で v2(m+1) = 3、ℓ = 1、p = 1 または p が偶数のすべての m について、
 *       block_rule.js の nextBlock で最初の 12 ブロックの間隔を求め、予想と照合する。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_k26.js 30 300000 > data/k26_check.txt
 */
'use strict';
const { certify } = require('./affine_certificate');
const { nextBlock } = require('./block_rule');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const PMAX = +(process.argv[2] || 30), MMAX = +(process.argv[3] || 300000);
const inv = (c, M) => { for (let x = 1n; ; x += 2n) if ((BigInt(c) * x) % M === 1n) return x; };
const out = ['# 予想 K26 の確認（v2(m+1) = 3、v2(5u+1) = 1 の m。p = v2((11u+1)/2) が 1 なら 10 型、偶数なら 100 型）',
  `# 生成: node --stack-size=65500 code/check_k26.js ${PMAX} ${MMAX}`, '', '## (1) 証明書: p | 類 | 結果 | M_min | 事実の個数'];
for (let p = 1; p <= PMAX; p++) {
  const M = 2n ** BigInt(p + 2), u0 = (((2n ** BigInt(p + 1) - 1n) % M + M) % M * inv(11, M)) % M;
  const A = 8 * 2 ** (p + 2), B = 8 * Number(u0) - 1, L = p % 2 ? 2 : 3;
  let line;
  try { const r = certify(A, B, 0, L, 1e6); line = `p=${p} | m ≡ ${B} (mod 2^${p + 5}) | ${r.gaps.join('')} | ${A * r.tmin + B} | ${r.n}`; }
  catch (e) { line = `p=${p} | m ≡ ${B} (mod 2^${p + 5}) | 失敗（${e.message || '偶奇が t による'}）${p % 2 && p > 1 ? '：予想の対象外' : '：予想に反する'}`; }
  out.push(line);
}
out.push('', '## (2) ブロック漸化式による確認');
let cnt = { one: 0, even: 0 }, bad = [];
for (let m = 23; m <= MMAX; m += 16) {
  const u = (m + 1) / 8; if (v2(5 * u + 1) !== 1) continue;
  const p = v2((11 * u + 1) / 2); if (p !== 1 && p % 2) continue;
  const want = p === 1 ? '10' : '100'; let pv = null, ok = true;
  for (let J = 0; J < 12; J++) { pv = nextBlock(m, pv); if (String(pv.g - m - 1) !== want[J % want.length]) { ok = false; break; } }
  if (p === 1) cnt.one++; else cnt.even++; if (!ok) bad.push(m);
}
out.push(`p = 1 の m: ${cnt.one} 個、p が偶数の m: ${cnt.even} 個（23 ≤ m ≤ ${MMAX}）。食い違い: ${bad.length ? bad.slice(0, 30).join(', ') : 'なし'}`);
console.log(out.join('\n'));
