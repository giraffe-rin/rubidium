/*
 * lean_crosscheck.js — Lean の計算できる版 isPb（lean/Rubidium/Decide.lean、IsP と同値と証明済み）による後手必勝の開始局面の一覧を、
 *                      PROBLEM.md の定義を直接たどる全探索と照合する
 *
 * 何を計算するか:
 *   m = 1..MMAX、1 ≤ n ≤ NMAX について、開始局面 (n, 0) が後手必勝かを、局面 (r, p) の勝敗のメモ化した全探索で求める
 *   （合法手 k：1 ≤ k ≤ min(m, r)、k ≠ p、移った先 (r − k, k)。合法手がなければ手番の負け）。
 *   lean/check/PStarts.lean の出力（「m = …: [n, …]」の行）をファイルから読み、同じ形の一覧と行ごとに比べる。
 * 実行方法（リポジトリのルートで）:
 *   (cd lean && lake env lean --run check/PStarts.lean) > data/lean_pstarts.txt
 *   node code/lean_crosscheck.js data/lean_pstarts.txt 10 24 > data/lean_crosscheck.txt
 */
'use strict';
const fs = require('fs');
const [file, MM, NM] = process.argv.slice(2); const MMAX = +MM, NMAX = +NM;
const lean = new Map(); for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) { const mm = l.match(/^m = (\d+): \[(.*)\]$/); if (mm) lean.set(+mm[1], mm[2].trim() ? mm[2].split(',').map(x => +x.trim()) : []); }
const out = ['# Lean の isPb と全探索の照合（後手必勝の開始局面 (n, 0)、1 ≤ n ≤ ' + NMAX + '）', '# 生成: node code/lean_crosscheck.js ' + process.argv.slice(2).join(' '), 'm | 全探索 | Lean | 一致'];
let ok = 0;
for (let m = 1; m <= MMAX; m++) {
  const memo = new Map();
  const P = (r, p) => { const key = r * 1000 + p; if (memo.has(key)) return memo.get(key); let res = true; for (let k = 1; k <= Math.min(m, r); k++) if (k !== p && P(r - k, k)) { res = false; break; } memo.set(key, res); return res; };
  const brute = []; for (let n = 1; n <= NMAX; n++) if (P(n, 0)) brute.push(n);
  const l = lean.get(m), same = l !== undefined && l.join(',') === brute.join(',');
  if (same) ok++;
  out.push(`${m} | ${brute.join(' ') || '-'} | ${l === undefined ? '（なし）' : l.join(' ') || '-'} | ${same ? 'はい' : 'いいえ'}`);
}
out.push('', `${MMAX} 個の m のうち ${ok} 個で一致`);
console.log(out.join('\n'));
