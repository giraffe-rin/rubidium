/*
 * check_period_induction.js — period_induction.js の健全性の確認
 *
 * 何を計算するか:
 *   (1) 予想 K33（e 奇数）の族に、わざと誤った周期の列（最初の 1 の連を 1 つ短くしたもの）を与え、「確定」と出ないことを確かめる（e = 7..21）
 *   (2) 奇数 5 ≤ m ≤ MMAX について、block_rule.js の nextBlock で 200 ブロックの間隔の列を求め、ブロック 0 から周期 L（≤ 60、
 *       末尾が 0）でくり返していれば、その周期の列 w で prove を呼ぶ。「確定」した m で、200 ブロックの列が w のくり返しと一致するかを数える
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_period_induction.js 3000 > data/check_period_induction.txt
 */
'use strict';
const { prove } = require('./period_induction'); const { nextBlock } = require('./block_rule');
const MMAX = +(process.argv[2] || 3000);
let falseOk = 0; for (let e = 7; e <= 21; e += 2) { const m = 9n * 2n ** BigInt(e) + 1n; const w = '1'.repeat(e - 2) + '0' + '1'.repeat((e - 1) / 2) + '0'; if (prove(m, w).ok) falseOk++; }
let tried = 0, okc = 0, contra = 0;
for (let m = 5; m <= MMAX; m += 2) {
  let pv = null, s = ''; for (let j = 0; j < 200; j++) { pv = nextBlock(m, pv); s += pv.g === m + 2 ? 1 : 0; }
  let L = null; for (let l = 1; l <= 60; l++) if (s.slice(0, 180).split('').every((c, i) => c === s[i % l])) { L = l; break; }
  if (!L) continue; const w = s.slice(0, L); if (w[L - 1] !== '0') continue; tried++;
  const r = prove(BigInt(m), w); if (r.ok) { okc++; if (s !== w.repeat(Math.ceil(200 / L)).slice(0, 200)) contra++; }
}
console.log(['# period_induction.js の健全性の確認', `# 生成: node --stack-size=65500 code/check_period_induction.js ${MMAX}`, `(1) 誤った周期の列で「確定」と出た数: ${falseOk}（8 個中）`, `(2) 試した m: ${tried}、確定: ${okc}、確定したのに直接の計算と食い違う: ${contra}`].join(String.fromCharCode(10)));
