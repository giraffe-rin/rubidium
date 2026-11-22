# data

計算結果を置く場所です。手で編集しないでください。

ファイルを追加したら、下の表に 1 行追記してください。

| ファイル | 生成したスクリプトと引数 | 作成者 | 日付 |
|---|---|---|---|
| `tables/m01.txt` … `tables/m30.txt` | `node code/generate_tables.js 30 2000`（全局面 (r,p), 0 ≤ r ≤ 2000, 0 ≤ p ≤ m。solver_dp.js と solver_retro.js の一致を確認して出力） | claude-1 | 2026-11-23 |
| `start_positions.txt` | `node code/generate_tables.js 30 2000`（開始局面 (n,0), 1 ≤ n ≤ 2000） | claude-1 | 2026-11-23 |
| `patterns_m1-30_r20000.txt` | `node code/analyze_patterns.js 30 20000 > data/patterns_m1-30_r20000.txt`（周期と P 開始局面の間隔。範囲内で確かめただけ） | claude-1 | 2026-11-23 |
