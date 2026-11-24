/*
 * coverage.js — どの m の開始局面の型が、既存の定理（[非形式証明]）で決まっているかの集計
 *
 * 何を計算するか:
 *   5 ≤ m ≤ MMAX の各 m について、次のどれかで型が決まっているかを調べる（どれも [非形式証明]、未査読）。
 *     K4  : v2(m+1) が偶数（m が偶数を含む。m+1 の倍数が開始局面）
 *     K16 : data/affine_certificates_v*_T*.txt と data/affine_refine_v*.txt の「証明できた類」で、m ≥ M_min
 *     K19 : v2(m+1) = 1 で v2(h−1) が奇数（notes/2026-11-23-claude-1-proof-k19.md）
 *     K20 : v2(m+1) = 3 で v2(5m+13) が 6 以上の偶数（notes/2026-11-23-claude-1-proof-k20.md）
 *     K26 : v2(m+1) = 3、v2(5u+1) = 1、p = v2((11u+1)/2) が 1 または 30 以下の偶数、m ≥ M_min（証明書の部分）
 *     K27/K28 : m = 9, 7（手での証明）
 *   m が偶数のときの扱い：問題の m は 2 以上の整数で、偶数の m は v2(m+1) = 0 で K4 に入る。
 *   出力: v2(m+1) ごとの、決まっている m の割合と、決まっていない最小の m の一覧。
 * 実行方法（リポジトリのルートで）:
 *   node code/coverage.js 20000 > data/coverage.txt
 */
'use strict';
const fs = require('fs');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const MMAX = +(process.argv[2] || 20000);
const classes = [];
for (const f of fs.readdirSync('data').filter(f => /^affine_(certificates_v\d+_T\d+|refine_v\d+_T\d+)\.txt$/.test(f))) {
  let sec = '';
  for (const l of fs.readFileSync('data/' + f, 'utf8').split(/\r?\n/)) {
    if (/^## (証明できた類|新しく証明できた類)/.test(l)) { sec = 'ok'; continue; }
    if (l.startsWith('##')) { sec = ''; continue; }
    const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\) \| (\d+) \|/);
    if (sec === 'ok' && mm) classes.push([+mm[2], +mm[1], +mm[3]]);
  }
}
function k26(m) {
  if (v2(m + 1) !== 3) return false; const u = (m + 1) / 8; if (v2(5 * u + 1) !== 1) return false;
  const p = v2((11 * u + 1) / 2); if (p === 1) return m >= 71; return p % 2 === 0 && p <= 30;
}
const by = {}; const uncovered = {};
for (let m = 5; m <= MMAX; m++) {
  const v = v2(m + 1); let why = null;
  if (v % 2 === 0) why = 'K4';
  else if (m === 7 || m === 9) why = 'K27/K28';
  else if (v === 1 && v2((m + 1) / 2 - 1) % 2 === 1) why = 'K19';
  else if (v === 3 && v2(5 * m + 13) >= 6 && v2(5 * m + 13) % 2 === 0) why = 'K20';
  else if (k26(m)) why = 'K26';
  else if (classes.some(([A, B, Mmin]) => m % A === B % A && m >= Mmin)) why = 'K16';
  const k = v % 2 === 0 ? '偶数' : String(v);
  by[k] = by[k] || { n: 0, ok: 0, src: {} }; by[k].n++;
  if (why) { by[k].ok++; by[k].src[why] = (by[k].src[why] || 0) + 1; }
  else (uncovered[k] = uncovered[k] || []).push(m);
}
const out = ['# 既存の定理で開始局面の型が決まる m の集計', `# 生成: node code/coverage.js ${MMAX}`, `# K16 の類: ${classes.length} 個`, '', '## v2(m+1) ごと: 区分 | m の個数 | 決まっている個数（割合）| 内訳'];
for (const k of Object.keys(by).sort((a, b) => (a === '偶数' ? -1 : b === '偶数' ? 1 : a - b))) {
  const s = by[k]; out.push(`v2(m+1) = ${k} | ${s.n} | ${s.ok}（${(s.ok / s.n).toFixed(4)}）| ${Object.entries(s.src).map(([w, c]) => `${w}: ${c}`).join('、')}`);
}
out.push('', '## 決まっていない m（v2(m+1) ごとに小さい順に最大 40 個）');
for (const k of Object.keys(uncovered).sort((a, b) => a - b)) out.push(`v2(m+1) = ${k}（${uncovered[k].length} 個）: ${uncovered[k].slice(0, 40).join(', ')}`);
console.log(out.join('\n'));
