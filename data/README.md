# data

計算結果を置く場所です。手で編集しないでください。

ファイルを追加したら、下の表に 1 行追記してください。

| ファイル | 生成したスクリプトと引数 | 作成者 | 日付 |
|---|---|---|---|
| `lean_pstarts.txt` | `(cd lean && lake env lean --run check/PStarts.lean)`（Lean の isPb による後手必勝の開始局面、m ≤ 10、n ≤ 24） | claude-1 | 2026-11-25 |
| `lean_crosscheck.txt` | `node code/lean_crosscheck.js data/lean_pstarts.txt 10 24`（Lean の出力と JavaScript の全探索の照合） | claude-1 | 2026-11-25 |
| `lean_tables.txt` | `(cd lean && lake env lean --run check/Tables.lean 30 2000)`（Lean の Array による DP での全局面の勝敗表、1 ≤ m ≤ 30、0 ≤ r ≤ 2000） | claude-1 | 2026-11-25 |
| `lean_tables_compare.txt` | `node code/lean_tables_compare.js data/lean_tables.txt data/tables`（Lean の表と data/tables の照合。data/tables はコミット 1c8eb7e の版） | claude-1 | 2026-11-25 |
| `lean_table_summary.txt` | `(cd lean && lake env lean --run check/TableSummary.lean 100 3000)`（Lean の DP による勝敗表の m ごとの要約、1 ≤ m ≤ 100、0 ≤ r ≤ 3000。約 8 分） | claude-1 | 2026-11-25 |
| `table_summary_compare.txt` | `node code/table_summary_compare.js data/lean_table_summary.txt 100 3000`（Lean と JavaScript の DP の要約の照合） | claude-1 | 2026-11-25 |
| `k38_hyp_check.txt` | `node code/k38_hyp_check.js`（Lean の K38_gen の仮定ともとの K38 の仮定が一致することの確認、5 ≤ v ≤ 15、u < 2^16） | claude-1 | 2026-11-25 |
