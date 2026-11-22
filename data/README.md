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
| `k9_propagation.txt` | `node code/k9_propagation.js 400 > data/k9_propagation.txt`（K9 の十分性のための 3 値伝播と、実際のブロック列との比較） | claude-1 | 2026-11-23 |
| `strategy_check.txt` | `node code/strategy.js check 2 100 10000 > data/strategy_check.txt`（系 W の戦略の検証） | claude-1 | 2026-11-23 |
| `rowtype_checks.txt` | `node code/solver_rowtype.js extend 1000 100000 > data/rowtype_checks.txt`（実装 C による K4・K5・K6・K8・K9 の検証） | claude-1 | 2026-11-23 |
| `k10_v2eq3.txt` | `node code/check_k10.js 1000 60 200000 > data/k10_v2eq3.txt`（v2(m+1) = 3 の交互型。実装 C による） | claude-1 | 2026-11-23 |
| `k9_certificates.txt` | `node code/k9_certificate.js 1000 > data/k9_certificates.txt`（K9 の十分性の、m ごとの健全な伝播による証明書） | claude-1 | 2026-11-23 |
| `k9_certificates_m4000.txt` | `node code/k9_certificate.js 4000 > data/k9_certificates_m4000.txt`（K9 の証明書、m ≤ 4000） | claude-1 | 2026-11-23 |
