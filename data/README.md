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
| `gap_types_m2000.txt` | `node code/gap_types.js 2000 300 3000000 > data/gap_types_m2000.txt`（開始局面の P の間隔の周期の型） | claude-1 | 2026-11-23 |
| `k12_check.txt` | `node code/check_k12.js 6000 200 3000000 > data/k12_check.txt`（定理 K12 の検証） | claude-1 | 2026-11-23 |
| `k13_check.txt` | `node code/check_k13.js 8000 100 2000000 > data/k13_check.txt`（定理 K13 の検証） | claude-1 | 2026-11-23 |
| `k12_general_check.txt` | `node code/check_k12_general.js 8000 12 1500000 > data/k12_general_check.txt`（定理 K12″・予想 K12′ の検証） | claude-1 | 2026-11-23 |
| `k14_check.txt` | `node code/check_k14.js 200000 > data/k14_check.txt`（定理 K14 の検証） | claude-1 | 2026-11-23 |
| `k12_symbolic.txt` | `node --stack-size=65500 code/k12_symbolic.js 2 16 crosscheck > data/k12_symbolic.txt`（定理 K15 の記号の証明書） | claude-1 | 2026-11-23 |
| `affine_certificates_v1.txt` | `node --stack-size=65500 code/affine_certificate.js 1 14 > data/affine_certificates_v1.txt`（定理 K16 の類ごとの証明書、v2(m+1) = 1） | claude-1 | 2026-11-23 |
| `affine_certificates_v3.txt` | `node --stack-size=65500 code/affine_certificate.js 3 14 > data/affine_certificates_v3.txt`（定理 K16 の類ごとの証明書、v2(m+1) = 3） | claude-1 | 2026-11-23 |
| `affine_certificates_v5.txt` | `node --stack-size=65500 code/affine_certificate.js 5 14 > data/affine_certificates_v5.txt`（定理 K16 の類ごとの証明書、v2(m+1) = 5） | claude-1 | 2026-11-23 |
| `affine_check_v1.txt` | `node code/check_affine.js data/affine_certificates_v1.txt 2 40000 2000000 > data/affine_check_v1.txt`（K16 の実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_check_v3.txt` | `node code/check_affine.js data/affine_certificates_v3.txt 2 40000 2000000 > data/affine_check_v3.txt`（K16 の実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_check_v5.txt` | `node code/check_affine.js data/affine_certificates_v5.txt 2 40000 2000000 > data/affine_check_v5.txt`（K16 の実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_certificates_v1_T18.txt` | `node --stack-size=65500 code/affine_certificate.js 1 18 > data/affine_certificates_v1_T18.txt`（K16 の範囲の拡大、v2(m+1) = 1） | claude-1 | 2026-11-23 |
| `affine_certificates_v3_T17.txt` | `node --stack-size=65500 code/affine_certificate.js 3 17 > data/affine_certificates_v3_T17.txt`（K16 の範囲の拡大、v2(m+1) = 3） | claude-1 | 2026-11-23 |
| `affine_certificates_v5_T17.txt` | `node --stack-size=65500 code/affine_certificate.js 5 17 > data/affine_certificates_v5_T17.txt`（K16 の範囲の拡大、v2(m+1) = 5） | claude-1 | 2026-11-23 |
| `affine_certificates_v7_T17.txt` | `node --stack-size=65500 code/affine_certificate.js 7 17 > data/affine_certificates_v7_T17.txt`（K16 の範囲の拡大、v2(m+1) = 7） | claude-1 | 2026-11-23 |
| `affine_check_v1_T18.txt` | `node code/check_affine.js data/affine_certificates_v1_T18.txt 1 40000 1000000 > data/affine_check_v1_T18.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_check_v3_T17.txt` | `node code/check_affine.js data/affine_certificates_v3_T17.txt 1 40000 1000000 > data/affine_check_v3_T17.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_check_v5_T17.txt` | `node code/check_affine.js data/affine_certificates_v5_T17.txt 1 40000 1000000 > data/affine_check_v5_T17.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_check_v7_T17.txt` | `node code/check_affine.js data/affine_certificates_v7_T17.txt 1 40000 1000000 > data/affine_check_v7_T17.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `unresolved_structure_v1_T18.txt` | `node code/analyze_unresolved.js data/affine_certificates_v1_T18.txt > data/unresolved_structure_v1_T18.txt`（証明できた類・できなかった類の s、w、q による分類） | claude-1 | 2026-11-23 |
| `affine_refine_v1_T20.txt` | `node --stack-size=65500 code/affine_refine.js data/affine_certificates_v1_T18.txt 1 20 > data/affine_refine_v1_T20.txt`（決まらなかった類の再分割、A ≤ 2^20） | claude-1 | 2026-11-23 |
| `affine_refine_check_v1_T20.txt` | `node code/check_affine.js data/affine_refine_v1_T20.txt 1 40000 1000000 > data/affine_refine_check_v1_T20.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_refine_v3_T19.txt` | `node --stack-size=65500 code/affine_refine.js data/affine_certificates_v3_T17.txt 3 19 > data/affine_refine_v3_T19.txt`（決まらなかった類の再分割、v2(m+1) = 3、A ≤ 2^19） | claude-1 | 2026-11-23 |
| `affine_refine_check_v3_T19.txt` | `node code/check_affine.js data/affine_refine_v3_T19.txt 1 40000 1000000 > data/affine_refine_check_v3_T19.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_refine_v5_T19.txt` | `node --stack-size=65500 code/affine_refine.js data/affine_certificates_v5_T17.txt 5 19 > data/affine_refine_v5_T19.txt`（決まらなかった類の再分割、v2(m+1) = 5、A ≤ 2^19） | claude-1 | 2026-11-23 |
| `affine_refine_check_v5_T19.txt` | `node code/check_affine.js data/affine_refine_v5_T19.txt 1 40000 1000000 > data/affine_refine_check_v5_T19.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_refine_v7_T19.txt` | `node --stack-size=65500 code/affine_refine.js data/affine_certificates_v7_T17.txt 7 19 > data/affine_refine_v7_T19.txt`（決まらなかった類の再分割、v2(m+1) = 7、A ≤ 2^19） | claude-1 | 2026-11-23 |
| `affine_refine_check_v7_T19.txt` | `node code/check_affine.js data/affine_refine_v7_T19.txt 1 40000 1000000 > data/affine_refine_check_v7_T19.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
