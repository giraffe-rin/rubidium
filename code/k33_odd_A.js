/*
 * k33_odd_A.js — 予想 K33（e 奇数、m = 9·2^e + 1）の周期についての帰納法（period_induction.js の prove）が使う仮定の集合 A を、e の式と比べる
 *
 * 何を計算するか:
 *   奇数 e = 9..EMAX について、prove(m, w)（w = 1^{e−1} 0 1^{(e−1)/2} 0）を実行し、返された仮定の集合 A（距離と値）を、
 *   予想した式（X = 2^e）
 *     7X − 2^{e−2} + 2、5X − 2^{e−3} + 2、6X + 6·4^j + 2（0 ≤ j ≤ (e−5)/2）、6X − 9·4^{j+1} + 2（0 ≤ j ≤ (e−7)/2）、6X + 1442
 *   の集合と比べる。値はすべて「入らない」（ブロック 0 で v2 が奇数）と予想する。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k33_odd_A.js 199 > data/k33_odd_A.txt
 */
'use strict';
const { prove } = require('./period_induction');
const EMAX = +(process.argv[2] || 199);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 予想 K33（e 奇数）の帰納法の仮定の集合 A と予想した式の比較', '# 生成: node --stack-size=65500 code/k33_odd_A.js ' + EMAX, 'e | 帰納法 | |A| | 式の集合と一致 | 値がすべて「入らない」 | v2 の値'];
let allOk = true;
for (let e = 9; e <= EMAX; e += 2) {
  const X = 2n ** BigInt(e), m = 9n * X + 1n, w = '1'.repeat(e - 1) + '0' + '1'.repeat((e - 1) / 2) + '0';
  const r = prove(m, w);
  const want = new Set([7n * X - 2n ** BigInt(e - 2) + 2n, 5n * X - 2n ** BigInt(e - 3) + 2n, 6n * X + 1442n]);
  for (let j = 0; j <= (e - 5) / 2; j++) want.add(6n * X + 6n * 4n ** BigInt(j) + 2n);
  for (let j = 0; j <= (e - 7) / 2; j++) want.add(6n * X - 9n * 4n ** BigInt(j + 1) + 2n);
  const got = new Set((r.Aset || []).map(([d]) => BigInt(d)));
  const same = got.size === want.size && [...want].every(d => got.has(d));
  const allNo = (r.Aset || []).every(([, val]) => val === false);
  const vs = [...new Set((r.Aset || []).map(([d]) => v2(BigInt(d))))].sort((a, b) => a - b);
  if (!r.ok || !same || !allNo) allOk = false;
  out.push(`${e} | ${r.ok ? '確定' : '失敗'} | ${r.A} | ${same ? 'はい' : 'いいえ（式 ' + want.size + ' 個）'} | ${allNo ? 'はい' : 'いいえ'} | {${vs.join(', ')}}`);
}
out.push('', allOk ? 'すべての e で A は式の集合に一致し、値はすべて「入らない」' : '一致しないものがある');
console.log(out.join('\n'));
