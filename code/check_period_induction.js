/*
 * check_period_induction.js — period_induction.js の健全性の確認
 *
 * 何を計算するか:
 *   prove と prove2（出発点をブロック L にとる版）の両方について（(1)(2)）、prove3（前周期あり・末尾が 1 の型も扱う版）について（(3)、ファイルの末尾）：
 *   (1) 予想 K33（e 奇数）の族に、わざと誤った周期の列（最初の 1 の連を 1 つ短くしたもの）を与え、「確定」と出ないことを確かめる（e = 7..21）
 *   (2) 奇数 5 ≤ m ≤ MMAX について、block_rule.js の nextBlock で 200 ブロックの間隔の列を求め、ブロック 0 から周期 L（≤ 60、
 *       末尾が 0）でくり返していれば、その周期の列 w で prove を呼ぶ。「確定」した m で、200 ブロックの列が w のくり返しと一致するかを数える
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/check_period_induction.js 3000 > data/check_period_induction.txt
 */
'use strict';
const { prove, prove2 } = require('./period_induction'); const { nextBlock } = require('./block_rule');
const MMAX = +(process.argv[2] || 3000);
let falseOk = 0, falseOk2 = 0; for (let e = 7; e <= 21; e += 2) { const m = 9n * 2n ** BigInt(e) + 1n; const w = '1'.repeat(e - 2) + '0' + '1'.repeat((e - 1) / 2) + '0'; if (prove(m, w).ok) falseOk++; if (prove2(m, w).ok) falseOk2++; }
let tried = 0, okc = 0, contra = 0, okc2 = 0, contra2 = 0;
for (let m = 5; m <= MMAX; m += 2) {
  let pv = null, s = ''; for (let j = 0; j < 200; j++) { pv = nextBlock(m, pv); s += pv.g === m + 2 ? 1 : 0; }
  let L = null; for (let l = 1; l <= 60; l++) if (s.slice(0, 180).split('').every((c, i) => c === s[i % l])) { L = l; break; }
  if (!L) continue; const w = s.slice(0, L); if (w[L - 1] !== '0') continue; tried++;
  const r = prove(BigInt(m), w); if (r.ok) { okc++; if (s !== w.repeat(Math.ceil(200 / L)).slice(0, 200)) contra++; }
  const r2 = prove2(BigInt(m), w); if (r2.ok) { okc2++; if (s !== w.repeat(Math.ceil(200 / L)).slice(0, 200)) contra2++; }
}
console.log(['# period_induction.js の健全性の確認', `# 生成: node --stack-size=65500 code/check_period_induction.js ${MMAX}`, `(1) 誤った周期の列で「確定」と出た数: prove ${falseOk}、prove2 ${falseOk2}（8 個中）`, `(2) 試した m: ${tried}。prove：確定 ${okc}、食い違い ${contra}。prove2：確定 ${okc2}、食い違い ${contra2}`].join(String.fromCharCode(10)));
// (3) prove3（前周期あり、または末尾が 1 の型も扱う版）：奇数 5 ≤ m ≤ MMAX で、200 ブロックの列から前周期 p と周期 L（≤ 60、p ≤ 80）を
//     推測し、prove3（周期の列を k = 1..4 回くり返したもので試す）で確定した m で、200 ブロックの列と食い違わないかを数える。
//     あわせて、確定した m で、周期の最後の 1 文字を反転させた誤った型を与え、「確定」と出ないことを確かめる。
{
  const { prove3 } = require('./period_induction');
  let t3 = 0, ok3 = 0, c3 = 0, f3 = 0;
  for (let m = 5; m <= MMAX; m += 2) {
    let pv = null, s = ''; for (let j = 0; j < 200; j++) { pv = nextBlock(m, pv); s += pv.g === m + 2 ? 1 : 0; }
    let pl = null; for (let L = 1; L <= 60 && !pl; L++) for (let p = 0; p <= 80; p++) { if (200 - p < 3 * L) break; let ok = true; for (let i = p; i + L < 200; i++) if (s[i] !== s[i + L]) { ok = false; break; } if (ok) { pl = [p, L]; break; } }
    if (!pl) continue; t3++; const pre = s.slice(0, pl[0]), w = s.slice(pl[0], pl[0] + pl[1]);
    let r = null, kk = 0; for (let k = 1; k <= 4; k++) { r = prove3(BigInt(m), pre, w.repeat(k)); if (r.ok) { kk = k; break; } }
    if (r.ok) { ok3++; const exp = pre + w.repeat(Math.ceil(200 / pl[1])); if (s !== exp.slice(0, 200)) c3++;
      const wf = w.slice(0, -1) + (w[w.length - 1] === '0' ? '1' : '0'); if (prove3(BigInt(m), pre, wf.repeat(kk)).ok) f3++; }
  }
  console.log(`(3) prove3：試した m: ${t3}、確定: ${ok3}、確定したのに直接の計算と食い違う: ${c3}、誤った型（周期の最後を反転）で確定と出た数: ${f3}`);
}
