/*
 * lean_tables_compare.js — Lean の DP（lean/check/Tables.lean）で出した全局面の勝敗表を、data/tables/mXX.txt（JavaScript の
 *                          solver_dp.js と solver_retro.js が一致したもの、code/generate_tables.js が出力）と 1 文字ずつ比べる
 *
 * 何を計算するか:
 *   Lean の出力の各行「m r 文字列」と、data/tables/mXX.txt の各行「r 文字列」を、(m, r) ごとに比べる。
 *   m ごとに、比べた局面 (r, p) の数と一致しなかった数を出す。
 * 実行方法（リポジトリのルートで）:
 *   (cd lean && lake env lean --run check/Tables.lean 30 2000) > data/lean_tables.txt
 *   node code/lean_tables_compare.js data/lean_tables.txt data/tables > data/lean_tables_compare.txt
 *   （data/tables はコミット 1c8eb7e で加えたもので、まだ ruca-logic にない。ないブランチでは、git show でそのコミット以降の版を取り出したディレクトリを渡す）
 */
'use strict';
const fs = require('fs'), path = require('path');
const [leanFile, dir] = process.argv.slice(2);
const lean = new Map();
for (const l of fs.readFileSync(leanFile, 'utf8').split(/\r?\n/)) { const t = l.trim().split(' '); if (t.length === 3) lean.set(t[0] + ':' + t[1], t[2]); }
const out = ['# Lean の DP と data/tables の勝敗表の照合（1 ≤ m ≤ 30、0 ≤ r ≤ 2000、0 ≤ p ≤ m）', '# 生成: node code/lean_tables_compare.js ' + leanFile + ' data/tables', 'm | 比べた局面の数 | 一致しなかった局面の数 | Lean にない行'];
let totAll = 0, badAll = 0;
for (let m = 1; m <= 30; m++) {
  const f = path.join(dir, 'm' + String(m).padStart(2, '0') + '.txt');
  let tot = 0, bad = 0, miss = 0;
  for (const l of fs.readFileSync(f, 'utf8').split(/\r?\n/)) {
    if (!l || l.startsWith('#')) continue;
    const [r, s] = l.trim().split(' '); const t = lean.get(m + ':' + r);
    if (t === undefined) { miss++; continue; }
    for (let p = 0; p < Math.max(s.length, t.length); p++) { tot++; if (s[p] !== t[p]) bad++; }
  }
  totAll += tot; badAll += bad;
  out.push(`${m} | ${tot} | ${bad} | ${miss}`);
}
out.push('', `合計 ${totAll} 局面のうち、一致しなかったもの ${badAll}`);
console.log(out.join('\n'));
