/*
 * k7_periods_odd.js — lo ≤ m ≤ hi のうち v2(m+1) が奇数の m について、code/block_rule.js periods m m を 1 つずつ実行し、出力の行を集める
 *                     （v2(m+1) が偶数の m は定理 K4 より開始局面列が純周期（周期 m+1）なので計算しない。偶数の m を一度に回すと周期が大きくメモリが足りない）
 *
 * 何を計算するか: 漸化式 R（K8）の状態の繰り返しから求めた開始局面列の前周期・周期（block_rule.js と同じ列）。
 * 実行方法（リポジトリのルートで）:
 *   node code/k7_periods_odd.js 201 400 > data/k7_periods_201-400.txt
 */
'use strict';
const { execFileSync } = require('child_process'), path = require('path');
const [lo, hi] = process.argv.slice(2).map(Number);
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = [`# 漸化式 R の状態の繰り返しから求めた開始局面列 (n,0) の前周期・周期（${lo} ≤ m ≤ ${hi} のうち v2(m+1) が奇数の m）`,
  '# 生成: node code/k7_periods_odd.js ' + lo + ' ' + hi + '（m ごとに node code/block_rule.js periods m m）。列は data/block_periods_m2-200.txt と同じ'];
for (let m = lo; m <= hi; m++) {
  if (v2(m + 1) % 2 === 0) continue;
  const s = execFileSync(process.execPath, ['--max-old-space-size=3000', path.join(__dirname, 'block_rule.js'), 'periods', String(m), String(m)], { encoding: 'utf8', maxBuffer: 1 << 26 });
  const line = s.split(/\r?\n/).find(x => x.startsWith('m='));
  out.push(line || `m=${m} | 失敗`);
}
console.log(out.join('\n'));
