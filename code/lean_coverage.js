/*
 * lean_coverage.js — Lean で示した定理（sorry なし）で開始局面 (n, 0) の P の集合（型）が決まる m の割合を、v2(m+1) ごとに数える
 *
 * 何を計算するか: 1 ≤ m ≤ MMAX の各 m について、次の Lean の定理の仮定を満たすかを調べ、どれかを満たせば「Lean で型が決まる」と数える。
 *   K4（v2(m+1) 偶数）、K9（v2(m+1) = 1、m ≥ 5、v2(3h+1) 奇数）、K12a（v2(m+1) = 1、m ≥ 5、v2(3h+1) = 2、(11h+5)/8 奇数）、
 *   K64（v2(m+1) = 1、v2(3h+1) = 2、X_t ≡ 2 (mod 4)（t < j）、X_j 奇数）、K15（v2(m+1) = 1、v2(3h+1) = 2k ≥ 4、(3h+1)/4^k ≡ 3 (mod 4)）、K10a（m % 64 = 7、m ≥ 71）、K13（m % 8 = 7、{v2(9u+1), v2(11u+1)} = {1, 3}、u = (m+1)/8）、
 *   K66（(m+1) % 128 = 88、つまり m+1 = 8u、u ≡ 11 (mod 16)）、K67_19（(m+1) % 512 = 152）、K67_61（(m+1) % 512 = 488）、K29_v5（m % 128 = 31）、K29_gen（v2(m+1) = v ≥ 5 奇数、u ≡ 1 (mod 4)）、
 *   K38（v ≥ 5 奇数、u ≡ 3 (mod 4)、w = v2(u+1) が奇数で 3 ≤ w ≤ v−2 または w ≥ v+1）。
 * 実行方法（リポジトリのルートで）: node code/lean_coverage.js 1000000 > data/lean_coverage.txt
 */
'use strict';
const MMAX = +process.argv[2];
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const stat = {}, byThm = {};
for (let m = 1; m <= MMAX; m++) {
  const v = v2(m + 1), u = (m + 1) / 2 ** v, h = (m + 1) / 2;
  const thms = [];
  if (v % 2 === 0) thms.push('K4');
  if (v === 1 && m >= 5) { const t = v2(3 * h + 1); if (t % 2 === 1) thms.push('K9'); if (t === 2 && ((11 * h + 5) / 8) % 2 === 1) thms.push('K12a'); if (t === 2 && m >= 9) { const w = (3 * h + 1) / 4; let X = (m + 2 + w) / 2, j = 0; while (X % 4 === 2) { X = (m + 2 + X / 2) / 2; j++; } if (j >= 1 && X % 2 === 1) thms.push('K64'); } if (t >= 4 && t % 2 === 0 && ((3 * h + 1) / 2 ** t) % 4 === 3) thms.push('K15'); }
  if (m % 64 === 7 && m >= 71) thms.push('K10a');
  if (m % 8 === 7) { const U = (m + 1) / 8, a = v2(9 * U + 1), b = v2(11 * U + 1); if ((a === 1 && b === 3) || (a === 3 && b === 1)) thms.push('K13'); }
  if ((m + 1) % 128 === 88) thms.push('K66');
  if ((m + 1) % 512 === 152) thms.push('K67_19');
  if ((m + 1) % 512 === 488) thms.push('K67_61');
  if (m % 128 === 31) thms.push('K29_v5');
  if (v >= 5 && v % 2 === 1 && u % 4 === 1) thms.push('K29_gen');
  if (v >= 5 && v % 2 === 1 && u % 4 === 3) { const w = v2(u + 1); if ((w % 2 === 1 && w >= 3 && w <= v - 2) || w >= v + 1) thms.push('K38'); }
  const key = v % 2 === 0 ? '偶数' : String(v);
  stat[key] = stat[key] || [0, 0]; stat[key][0]++; if (thms.length) stat[key][1]++;
  for (const t of thms) byThm[t] = (byThm[t] || 0) + 1;
}
const out = ['# Lean で型が決まる m の割合（1 ≤ m ≤ ' + MMAX + '）', '# 生成: node code/lean_coverage.js ' + MMAX, 'v2(m+1) | m の数 | Lean で型が決まる数 | 割合'];
let tot = 0, cov = 0;
for (const k of ['偶数', ...Object.keys(stat).filter(k => k !== '偶数').sort((a, b) => a - b)]) {
  const [n, c] = stat[k]; tot += n; cov += c; out.push(`${k} | ${n} | ${c} | ${(100 * c / n).toFixed(2)}%`);
}
out.push(`合計 | ${tot} | ${cov} | ${(100 * cov / tot).toFixed(2)}%`, '', '定理ごとの該当数（重なりあり）：' + Object.entries(byThm).map(([k, n]) => `${k} ${n}`).join('、'));
console.log(out.join('\n'));
