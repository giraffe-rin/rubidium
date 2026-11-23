/*
 * one_runs_family.js — 族 m = 9·2^e + 1 で、m+2 の間隔の連の最大の長さ R(m) を e ごとに求める
 *
 * 何を計算するか:
 *   e = 3, …, EMAX について m = 9·2^e + 1 とし、type_vs_t.js の gapsLazy で最初の BLOCKS ブロックの間隔を求める。
 *   ブロック 0〜BLOCKS−1 の間隔の列での m+2 の連の最大の長さ R と、その連の始まりのブロック番号、型の推測（guessLazy）を出す。
 *   さらに、型（typeOf）が予想 K33 の形と一致するかを調べる（e ≥ 7）。
 *     e が偶数：前周期なし、周期 1^{e/2} 0
 *     e が奇数：前周期なし、周期 1^{e−1} 0 1^{(e−1)/2} 0
 *   m は 2^53 未満、かつ BLOCKS·(m+2) < 2^53 の範囲だけ扱う（遅延評価の表のキーが正確な整数であるため）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/one_runs_family.js 40 300 > data/one_runs_family_9.txt
 */
'use strict';
const { gapsLazy, guessLazy, typeOf } = require('./type_vs_t');
const pred = e => '-|' + (e % 2 === 0 ? '1'.repeat(e / 2) + '0' : '1'.repeat(e - 1) + '0' + '1'.repeat((e - 1) / 2) + '0');
let nOk = 0, nNg = 0;
const [es, bs] = process.argv.slice(2); const EMAX = +(es || 40), BLOCKS = +(bs || 300);
const out = ['# 族 m = 9·2^e + 1 の m+2 の間隔の連の最大の長さ', `# 生成: node --stack-size=65500 code/one_runs_family.js ${EMAX} ${BLOCKS}`,
  'e | m | R（ブロック 0〜' + (BLOCKS - 1) + '）| 最長の連の始まりのブロック | 推測した (p, L) | R − e | 型が K33 の形か'];
for (let e = 3; e <= EMAX; e++) {
  const m = 9 * 2 ** e + 1; if (BLOCKS * (m + 2) >= 2 ** 53) break;
  const g = gapsLazy(m, BLOCKS); let run = 0, R = 0, at = -1;
  for (let j = 0; j < BLOCKS; j++) { if (g[j] === 1) { run++; if (run > R) { R = run; at = j - run + 1; } } else run = 0; }
  const pl = guessLazy(m, BLOCKS);
  out.push(`${e} | ${m} | ${R} | ${at} | ${pl ? '(' + pl[0] + ', ' + pl[1] + ')' : '?'} | ${R - e} | ${e < 7 ? '-' : typeOf(m, BLOCKS) === pred(e) ? (nOk++, '一致') : (nNg++, '不一致：' + typeOf(m, BLOCKS))}`);
}
out.push('', `K33 の形との照合（e ≥ 7）：一致 ${nOk}、不一致 ${nNg}`);
console.log(out.join(String.fromCharCode(10)));
