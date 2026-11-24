/*
 * table_summary_compare.js — 全局面 (r, p) の勝敗表を JavaScript の DP（このファイルで独立に書いたもの）で計算し、m ごとの要約を
 *                            Lean の DP（lean/check/TableSummary.lean）の出力と比べる
 *
 * 何を計算するか:
 *   (r, p) が P ⇔ 1 ≤ k ≤ min(m, r)、k ≠ p のどの手 k でも (r − k, k) が P でない（PROBLEM.md の定義）。r の小さい順に埋める。
 *   m ごとに、P 局面の数、チェックサム Σ (r(m+1) + p + 1)² mod (10^9 + 7)（P 局面についての和）、P の開始局面 (n, 0)（n ≥ 1）の最初の 20 個を出し、
 *   Lean の出力の同じ行と比べる。
 * 実行方法（リポジトリのルートで）:
 *   (cd lean && lake env lean --run check/TableSummary.lean 100 3000) > data/lean_table_summary.txt
 *   node code/table_summary_compare.js data/lean_table_summary.txt 100 3000 > data/table_summary_compare.txt
 */
'use strict';
const fs = require('fs');
const [file, MM, RM] = process.argv.slice(2); const MMAX = +MM, RMAX = +RM, MD = 1000000007;
const lean = new Map(); for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) { const mm = l.match(/^(\d+) (.*)$/); if (mm) lean.set(+mm[1], mm[2].trim()); }
const out = ['# Lean の DP と JavaScript の DP の照合（m ごとの要約、1 ≤ m ≤ ' + MMAX + '、0 ≤ r ≤ ' + RMAX + '）', '# 生成: node code/table_summary_compare.js ' + process.argv.slice(2).join(' '), 'm | P の数 | チェックサム | 一致'];
let ok = 0, cells = 0;
for (let m = 1; m <= MMAX; m++) {
  const W = m + 1, T = new Uint8Array((RMAX + 1) * W);
  let cnt = 0, sum = 0; const starts = [];
  for (let r = 0; r <= RMAX; r++) {
    for (let p = 0; p <= m; p++) {
      let isP = 1;
      for (let k = 1; k <= Math.min(m, r); k++) if (k !== p && T[(r - k) * W + k]) { isP = 0; break; }
      T[r * W + p] = isP;
      if (isP) { cnt++; const x = r * W + p + 1; sum = (sum + (x * x) % MD) % MD; }
    }
    if (r >= 1 && T[r * W] && starts.length < 20) starts.push(r);
  }
  cells += (RMAX + 1) * W;
  const mine = `${cnt} ${sum} [${starts.join(', ')}]`, l = lean.get(m), same = l === mine;
  if (same) ok++;
  out.push(`${m} | ${cnt} | ${sum} | ${same ? 'はい' : 'いいえ（Lean: ' + l + '）'}`);
}
out.push('', `${MMAX} 個の m のうち ${ok} 個で要約が一致（局面の数の合計 ${cells}）`);
console.log(out.join('\n'));
