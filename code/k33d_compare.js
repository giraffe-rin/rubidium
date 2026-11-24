/*
 * k33d_compare.js — 周期についての帰納法（prove3）で、補題 K33d の選択肢（opts.k33d）の有無による仮定の数と確定の違いを比べる
 *
 * 何を計算するか:
 *   M0 < m ≤ M1 で v2(m+1) = 1 の奇数 m のそれぞれについて、gapsLazy（type_vs_t.js）で型を推測し（400 ブロック）、
 *   coverage_pi.js と同じ試し方（c = 1, 2, 4, …, 32、k = 1..4）で prove3 を k33d なしとありで実行する。
 *   出力：確定した個数、最初に確定した (c, k) での仮定の数 A の合計と最大、k33d ありでだけ確定した m と、なしでだけ確定した m の個数。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k33d_compare.js 4 65536 > data/k33d_compare.txt
 */
'use strict';
const { prove3 } = require('./period_induction');
const { guessLazy } = require('./type_vs_t');
const [M0, M1] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
function tryAll(m, pre, w, opts) {
  for (const c of [1, 2, 4, 8, 16, 32]) for (let k = 1; k <= 4; k++) { const r = prove3(BigInt(m), pre + w.repeat(c - 1), w.repeat(k), 20000, 3000000, opts); if (r.ok) return r; }
  return null;
}
let n = 0, ok0 = 0, ok1 = 0, only0 = 0, only1 = 0, sumA0 = 0, sumA1 = 0, maxA0 = 0, maxA1 = 0, noGuess = 0;
for (let m = M0 + 1; m <= M1; m++) {
  if (m % 2 === 0 || v2(m + 1) !== 1 || m < 5) continue;
  const pl = guessLazy(m, 400); if (!pl) { noGuess++; continue; } n++;
  const g = pl[2], pre = g.slice(0, pl[0]).join(''), w = g.slice(pl[0], pl[0] + pl[1]).join('');
  const r0 = tryAll(m, pre, w, {}), r1 = tryAll(m, pre, w, { k33d: true });
  if (r0) { ok0++; sumA0 += r0.A; maxA0 = Math.max(maxA0, r0.A); }
  if (r1) { ok1++; sumA1 += r1.A; maxA1 = Math.max(maxA1, r1.A); }
  if (r0 && !r1) only0++; if (r1 && !r0) only1++;
}
console.log(['# 補題 K33d の選択肢の有無による prove3 の比較（v2(m+1) = 1）', `# 生成: node --stack-size=65500 code/k33d_compare.js ${M0} ${M1}`,
  `範囲：${M0} < m ≤ ${M1}、v2(m+1) = 1、型を推測できた m：${n}（推測できない ${noGuess}）`,
  `k33d なし：確定 ${ok0}、仮定の数の合計 ${sumA0}、最大 ${maxA0}`, `k33d あり：確定 ${ok1}、仮定の数の合計 ${sumA1}、最大 ${maxA1}`,
  `なしでだけ確定：${only0}、ありでだけ確定：${only1}`].join('\n'));
