/*
 * k65_obs.js — v2(m+1) = 1、v2(3h+1) = 2k（k ≥ 2）、Q = (m+2+w)/2 が偶数のときの型を調べる（観察 K65）
 *
 * 何を計算するか: 3h+1 = 4^k w。X₀ = Q、X_{t+1} = (m+2+X_t/2)/2 を v2(X_t) = 1 の間たどり、X_j が奇数で止まる m（j ≥ 1）について、
 *   漸化式 R（code/block_rule.js periods）の型を求める。型が 1^{j+1}(10)^r（前周期なし）なら r を記録し、(k, j, X_j mod 8) ごとに数える。
 * 実行方法（リポジトリのルートで）: node code/k65_obs.js 60000 > data/k65_obs.txt
 */
'use strict';
const { execFileSync } = require('child_process'), path = require('path');
const MMAX = +process.argv[2];
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const tab = {}, other = {};
for (let m = 9; m <= MMAX; m += 4) {
  const h = (m + 1) / 2, t2 = v2(3 * h + 1); if (t2 < 4 || t2 % 2) continue;
  const k = t2 / 2, w = (3 * h + 1) / 4 ** k; let X = (m + 2 + w) / 2, j = 0;
  while (v2(X) === 1) { X = (m + 2 + X / 2) / 2; j++; }
  if (v2(X) !== 0 || j === 0) continue;
  const line = execFileSync(process.execPath, [path.join(__dirname, 'block_rule.js'), 'periods', String(m), String(m)], { encoding: 'utf8' }).split(/\r?\n/).find(l => l.startsWith('m='));
  const f = line.split('|'), t = +f[4].split(',')[0], word = f[5].trim();
  const pre = '1'.repeat(j + 1), rest = word.slice(j + 1);
  const ok = t === 0 && word.startsWith(pre) && rest.length >= 2 && rest.length % 2 === 0 && /^(10)+$/.test(rest);
  const key = `k=${k} j=${j} X_j mod 8=${X % 8}`;
  tab[key] = tab[key] || {}; const r = ok ? 'r=' + rest.length / 2 : 'ほかの型';
  tab[key][r] = (tab[key][r] || 0) + 1;
  if (!ok) other[word + (t > 0 ? '（前周期あり）' : '')] = (other[word] || 0) + 1;
}
const out = ['# v2(m+1) = 1、k ≥ 2、Q 偶数のときの型（m ≤ ' + MMAX + '、漸化式 R による）', '# 生成: node code/k65_obs.js ' + MMAX, '(k, j, X_j mod 8) | 型 1^{j+1}(10)^r の r ごとの個数'];
for (const k of Object.keys(tab).sort()) out.push(k + ' | ' + Object.entries(tab[k]).map(([r, n]) => `${r}: ${n}`).join('、'));
out.push('', '1^{j+1}(10)^r の形でない型：' + Object.entries(other).map(([w, n]) => `${w} ${n}`).join('、'));
console.log(out.join('\n'));
