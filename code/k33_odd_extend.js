/*
 * k33_odd_extend.js — 予想 K33（e 奇数、m = 9·2^e + 1）の型 1^{e−1} 0 1^{(e−1)/2} 0 を、周期についての帰納法（period_induction.js の prove3、
 *                     補題 K33d の選択肢 opts.k33d つき）で確定させる
 *
 * 何を計算するか:
 *   奇数 e = E0..E1 のそれぞれで、prove3(m, '', w, …, { k33d: true })（前周期なし、周期 w を 1 回）を実行し、確定したか、仮定の集合 A の大きさと中身
 *   （X = 2^e として 6X + 8 だけか）、評価した事実の数を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k33_odd_extend.js 9 399 > data/k33_odd_extend.txt
 */
'use strict';
const { prove3 } = require('./period_induction');
const [E0, E1] = process.argv.slice(2).map(Number);
const out = ['# 予想 K33（e 奇数）の型の確定（prove3、補題 K33d つき）', '# 生成: node --stack-size=65500 code/k33_odd_extend.js ' + E0 + ' ' + E1, 'e | m の桁数 | 結果 | |A| | A = {6X + 8} か | 評価した事実'];
let ok = 0, ng = 0, only8 = 0;
for (let e = E0 % 2 ? E0 : E0 + 1; e <= E1; e += 2) {
  const X = 2n ** BigInt(e), m = 9n * X + 1n, w = '1'.repeat(e - 1) + '0' + '1'.repeat((e - 1) / 2) + '0';
  const r = prove3(m, '', w, 20000, 20000000, { k33d: true });
  const is8 = r.ok && r.Aset && r.Aset.length === 1 && BigInt(r.Aset[0][0]) === 6n * X + 8n && r.Aset[0][1] === false;
  if (r.ok) ok++; else ng++; if (is8) only8++;
  out.push(`${e} | ${m.toString().length} | ${r.ok ? '確定' : '失敗（' + r.why + '）'} | ${r.A} | ${is8 ? 'はい' : 'いいえ'} | ${r.facts ?? '-'}`);
}
out.push('', `確定 ${ok}、失敗 ${ng}、A = {6X + 8} だったもの ${only8}`);
console.log(out.join('\n'));
