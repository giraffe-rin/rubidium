# data

計算結果を置く場所です。手で編集しないでください。

ファイルを追加したら、下の表に 1 行追記してください。

| ファイル | 生成したスクリプトと引数 | 作成者 | 日付 |
|---|---|---|---|
| `tables/m01.txt` … `tables/m30.txt` | `node code/generate_tables.js 30 2000`（全局面 (r,p), 0 ≤ r ≤ 2000, 0 ≤ p ≤ m。solver_dp.js と solver_retro.js の一致を確認して出力） | claude-1 | 2026-11-23 |
| `start_positions.txt` | `node code/generate_tables.js 30 2000`（開始局面 (n,0), 1 ≤ n ≤ 2000） | claude-1 | 2026-11-23 |
| `patterns_m1-30_r20000.txt` | `node code/analyze_patterns.js 30 20000 > data/patterns_m1-30_r20000.txt`（周期と P 開始局面の間隔。範囲内で確かめただけ） | claude-1 | 2026-11-23 |
| `block_periods_m2-200.txt` | `node code/block_rule.js periods 2 200 > data/block_periods_m2-200.txt`（漸化式 R（[予想] K8）による周期の計算。R が正しいことを前提にした値） | claude-1 | 2026-11-23 |
| `conjecture_checks.txt` | `node code/check_conjectures.js 100 10000 1000 200 > data/conjecture_checks.txt`（予想 K1〜K8 の検証結果） | claude-1 | 2026-11-23 |
| `k9_alternation.txt` | `node code/check_k9.js 400 100 10000 > data/k9_alternation.txt`（予想 K9 の検証。R 経由と全探索の両方） | claude-1 | 2026-11-23 |
