/*
 * check_u_class2.js — u_class_symbolic2.js の証明書を、実際の m の型（遅延評価のブロック漸化式）と照合する
 *
 * 何を計算するか:
 *   v = VMIN, VMIN+2, …, VMAX、K について、u_class_symbolic2.js の run(v, K, u₀) が型を返した各 u₀ について、
 *   u = u₀ + 2^K t（t = 0, …, T − 1）の m = 2^v u − 1 の型を lazy_bigint.js の gapsBig（300 ブロック）で求め、
 *   証明書の型（前周期なし、周期 = 証明書の列）の 3 回分と、ブロック 0 からの間隔の列が一致するかを調べる。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_u_class2.js 5 21 6 20 > data/u_class_symbolic2_check.txt
 */
'use strict';
const { run } = require('./u_class_symbolic2');
const { gapsBig } = require('./lazy_bigint');
const [VMIN, VMAX, K, TT] = process.argv.slice(2).map(Number);
let n = 0, bad = 0; const out = ['# u_class_symbolic2.js の証明書の照合', `# 生成: node code/check_u_class2.js ${VMIN} ${VMAX} ${K} ${TT}`];
for (let v = VMIN; v <= VMAX; v += 2) for (let u0 = 1; u0 < 2 ** K; u0 += 2) {
  const t = run(v, K, u0); if (!t) continue;
  for (let s = 0; s < TT; s++) { const u = BigInt(u0 + 2 ** K * s), m = 2n ** BigInt(v) * u - 1n; if (m < 3n) continue;
    n++; if (gapsBig(m, 3 * t.length, 5000000).gaps !== t.repeat(3)) { bad++; out.push(`食い違い: v=${v} u₀=${u0} u=${u}`); } }
}
out.push(`調べた m: ${n}、食い違い: ${bad}`);
console.log(out.join(String.fromCharCode(10)));
