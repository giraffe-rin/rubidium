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
| `affine_certificates_v9_T17.txt` | `node --stack-size=65500 code/affine_certificate.js 9 17 > data/affine_certificates_v9_T17.txt`（K16、v2(m+1) = 9） | claude-1 | 2026-11-23 |
| `affine_certificates_v11_T17.txt` | `node --stack-size=65500 code/affine_certificate.js 11 17 > data/affine_certificates_v11_T17.txt`（K16、v2(m+1) = 11） | claude-1 | 2026-11-23 |
| `affine_check_v9_T17.txt` | `node code/check_affine.js data/affine_certificates_v9_T17.txt 1 40000 1000000 > data/affine_check_v9_T17.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `affine_check_v11_T17.txt` | `node code/check_affine.js data/affine_certificates_v11_T17.txt 1 40000 1000000 > data/affine_check_v11_T17.txt`（実装 C による照合） | claude-1 | 2026-11-23 |
| `coverage.txt` | `node code/coverage.js 20000 > data/coverage.txt`（既存の定理で型が決まる m の集計） | claude-1 | 2026-11-23 |
| `k29_check.txt` | `node --stack-size=65500 code/check_k29.js 15 14 300000 > data/k29_check.txt`（予想 K29 の分割つき証明書と、ブロック漸化式による確認） | claude-1 | 2026-11-23 |
| `k29_v5_check.txt` | `node --stack-size=65500 code/check_k29_v5.js 300000 > data/k29_v5_check.txt`（定理 K29.1・K29.2 の証明の中の事実の確認） | claude-1 | 2026-11-23 |
| `k29_symbolic.txt` | `node --max-old-space-size=4096 code/k29_symbolic.js 27 > data/k29_symbolic.txt`（定理 K29.3 の 3 値の証明書） | claude-1 | 2026-11-23 |
| `k29_cone.txt` | `node --stack-size=65500 code/k29_cone.js 17 > data/k29_cone.txt`（K29.3 の 3 値の計算の依存の範囲） | claude-1 | 2026-11-23 |
| `k29_lemmas.txt` | `node code/check_k29_lemmas.js 21 > data/k29_lemmas.txt`（定理 K29 の証明の補題の確認） | claude-1 | 2026-11-23 |
| `u_class_symbolic.txt` | `node code/u_class_symbolic.js 5 9 6 > data/u_class_symbolic.txt`（u の合同類ごとの 3 値の証明書） | claude-1 | 2026-11-23 |
| `affine3_v3_T19.txt` | `node --stack-size=65500 code/affine3.js data/affine_refine_v3_T19.txt 3 > data/affine3_v3_T19.txt`（3 値の証明書、v2(m+1) = 3） | claude-1 | 2026-11-23 |
| `affine3_check_v3_T19.txt` | `node code/check_affine_blockrule.js data/affine3_v3_T19.txt 3 400000 > data/affine3_check_v3_T19.txt`（ブロック漸化式による照合） | claude-1 | 2026-11-23 |
| `affine3_v5_T19.txt` | `node --stack-size=65500 code/affine3.js data/affine_refine_v5_T19.txt 5 > data/affine3_v5_T19.txt`（3 値の証明書、v2(m+1) = 5） | claude-1 | 2026-11-23 |
| `affine3_check_v5_T19.txt` | `node code/check_affine_blockrule.js data/affine3_v5_T19.txt 3 400000 > data/affine3_check_v5_T19.txt`（ブロック漸化式による照合） | claude-1 | 2026-11-23 |
| `affine3_v7_T19.txt` | `node --stack-size=65500 code/affine3.js data/affine_refine_v7_T19.txt 7 > data/affine3_v7_T19.txt`（3 値の証明書、v2(m+1) = 7） | claude-1 | 2026-11-23 |
| `affine3_check_v7_T19.txt` | `node code/check_affine_blockrule.js data/affine3_v7_T19.txt 3 400000 > data/affine3_check_v7_T19.txt`（ブロック漸化式による照合） | claude-1 | 2026-11-23 |
| `affine3_v1_T20.txt` | `node --stack-size=65500 code/affine3.js data/affine_refine_v1_T20.txt 1 > data/affine3_v1_T20.txt`（3 値の証明書、v2(m+1) = 1） | claude-1 | 2026-11-23 |
| `affine3_check_v1_T20.txt` | `node code/check_affine_blockrule.js data/affine3_v1_T20.txt 3 400000 > data/affine3_check_v1_T20.txt`（ブロック漸化式による照合） | claude-1 | 2026-11-23 |
| `affine3_refine_v7.txt` | `node --stack-size=65500 code/affine3_refine.js data/affine_refine_v7_T19.txt data/affine3_v7_T19.txt 7 2 > data/affine3_refine_v7.txt`（3 値の証明書の再分割、v2(m+1) = 7） | claude-1 | 2026-11-23 |
| `affine3_refine_check_v7.txt` | `node code/check_affine_blockrule.js data/affine3_refine_v7.txt 3 3000000 > data/affine3_refine_check_v7.txt`（ブロック漸化式による照合） | claude-1 | 2026-11-23 |
| `affine3_refine_v5.txt` | `node --stack-size=65500 code/affine3_refine.js data/affine_refine_v5_T19.txt data/affine3_v5_T19.txt 5 2 > data/affine3_refine_v5.txt`（3 値の証明書の再分割、v2(m+1) = 5） | claude-1 | 2026-11-23 |
| `affine3_refine_check_v5.txt` | `node code/check_affine_blockrule.js data/affine3_refine_v5.txt 3 3000000 > data/affine3_refine_check_v5.txt`（ブロック漸化式による照合） | claude-1 | 2026-11-23 |
| `affine3_refine_v3.txt` | `node --stack-size=65500 code/affine3_refine.js data/affine_refine_v3_T19.txt data/affine3_v3_T19.txt 3 2 > data/affine3_refine_v3.txt`（3 値の証明書の再分割、v2(m+1) = 3） | claude-1 | 2026-11-23 |
| `affine3_refine_check_v3.txt` | `node code/check_affine_blockrule.js data/affine3_refine_v3.txt 3 3000000 > data/affine3_refine_check_v3.txt`（ブロック漸化式による照合） | claude-1 | 2026-11-23 |
| `affine3_refine_v1.txt` | `node --stack-size=65500 code/affine3_refine.js data/affine_refine_v1_T20.txt data/affine3_v1_T20.txt 1 1 > data/affine3_refine_v1.txt`（3 値の証明書の再分割、v2(m+1) = 1） | claude-1 | 2026-11-24 |
| `affine3_refine_check_v1.txt` | `node code/check_affine_blockrule.js data/affine3_refine_v1.txt 3 3000000 > data/affine3_refine_check_v1.txt`（ブロック漸化式による照合） | claude-1 | 2026-11-24 |
| `affine3_diag_v7.txt` | `node --stack-size=65500 code/affine3_diag.js data/affine3_refine_v7.txt > data/affine3_diag_v7.txt`（3 値の証明書で間隔が不明になる原因の分類、v2(m+1) = 7） | claude-1 | 2026-11-24 |
| `meet_preperiod_v7.txt` | `node --stack-size=65500 code/meet_preperiod.js data/affine3_refine_v7.txt 80 3 > data/meet_preperiod_v7.txt`（meet で止まる類の (p, L) の t による変化） | claude-1 | 2026-11-24 |
| `cause_type_variation_v7.txt` | `node --stack-size=65500 code/meet_preperiod.js data/affine3_refine_v7.txt 120 5 all > data/cause_type_variation_v7.txt`（止まる類の (p, L) の t による変化、原因ごと） | claude-1 | 2026-11-24 |
| `type_vs_t_v7.txt` | `node --stack-size=65500 code/type_vs_t.js 4095 105855:2097152 29055:2097152 1087871:2097152 7551:2097152 > data/type_vs_t_v7.txt`（止まる類の中での型の分布） | claude-1 | 2026-11-24 |
| `type_growth_22.txt` | `node --stack-size=65500 code/type_growth.js 22 > data/type_growth_22.txt`（m ≤ 2^22 の型の種類の数） | claude-1 | 2026-11-24 |
| `type_growth_20_b600.txt` | `node --stack-size=65500 code/type_growth.js 20 600 > data/type_growth_20_b600.txt`（型の種類の数、600 ブロックからの推測） | claude-1 | 2026-11-24 |
| `type_runs_20.txt` | `node --stack-size=65500 code/type_runs.js 20 > data/type_runs_20.txt`（型の周期の列の連の長さ、v2(m+1) が奇数） | claude-1 | 2026-11-24 |
| `k32_check.txt` | `node code/check_k32.js 3000 60 > data/k32_check.txt`（定理 K32 と補題 Q_n のブロック漸化式による確認） | claude-1 | 2026-11-24 |
| `one_runs_22.txt` | `node --stack-size=65500 code/one_runs.js 22 300 20 > data/one_runs_22.txt`（m+2 の間隔の連の最大の長さ、m ≤ 2^22） | claude-1 | 2026-11-24 |
| `one_runs_family_9.txt` | `node --stack-size=65500 code/one_runs_family.js 40 300 > data/one_runs_family_9.txt`（族 m = 9·2^e + 1 の型と予想 K33 の照合） | claude-1 | 2026-11-24 |
| `family_v3.txt` | `node --stack-size=65500 code/family_v3.js 300 > data/family_v3.txt`（族 m = 8(36·16^k − 1)/5 − 1 の型と予想 K34 の照合） | claude-1 | 2026-11-24 |
| `k33a_check.txt` | `node code/check_k33a.js 20 > data/k33a_check.txt`（定理 K33a の証明の各段階のブロック漸化式による確認） | claude-1 | 2026-11-24 |
| `k33_bigint.txt` | `node code/lazy_bigint.js k33 200 > data/k33_bigint.txt`（予想 K33 の BigInt 版の遅延評価による照合） | claude-1 | 2026-11-24 |
| `k34_bigint.txt` | `node code/lazy_bigint.js k34 50 > data/k34_bigint.txt`（予想 K34 の BigInt 版の遅延評価による照合） | claude-1 | 2026-11-24 |
| `k33_odd_cone.txt` | `node --stack-size=65500 code/k33_odd_cone.js 9 11 13 15 > data/k33_odd_cone.txt`（m = 9·2^e + 1（e 奇数）で参照される距離の分類） | claude-1 | 2026-11-24 |
| `k35_check.txt` | `node code/check_k35.js 6 > data/k35_check.txt`（定理 K35 の証明の各段階のブロック漸化式による確認） | claude-1 | 2026-11-24 |
| `k35_bigint.txt` | `node code/lazy_bigint.js k35 60 > data/k35_bigint.txt`（定理 K35 の型の BigInt 版の遅延評価による照合） | claude-1 | 2026-11-24 |
| `family_search_v3.txt`, `family_search_v5.txt`, `family_search_v7.txt` | `node --stack-size=65500 code/family_search.js V > data/family_search_vV.txt`（V = 3, 5, 7。周期が伸び続ける族 m = 3a − 2 の探索） | claude-1 | 2026-11-24 |
| `k36_check.txt` | `node code/check_k36.js 13 400 > data/k36_check.txt`（定理 K36 の確認：m+2 の連の長さと性質 (Z)） | claude-1 | 2026-11-24 |
| `k36_s.txt` | `node --stack-size=65500 code/k36_s.js 3:4 3:6 3:8 5:14 5:28 5:42 7:50 7:100 9:254 11:102 11:204 13:387 13:774 15:234 > data/k36_s.txt`（K36 の族の m+1 の連の長さ） | claude-1 | 2026-11-24 |
| `u_class_symbolic2.txt` | `node code/u_class_symbolic2.js 5 21 6 > data/u_class_symbolic2.txt`（u の合同類ごとの 3 値の証明書、K3 と補題 Q_s を使う版） | claude-1 | 2026-11-24 |
| `u_class_symbolic2_check.txt` | `node code/check_u_class2.js 5 21 6 20 > data/u_class_symbolic2_check.txt`（上の証明書と実際の m の型の照合） | claude-1 | 2026-11-24 |
| `u_class_symbolic2_k9.txt` | `node code/u_class_symbolic2.js 7 15 9 > data/u_class_symbolic2_k9.txt`（上の証明書を K ≤ 9 で） | claude-1 | 2026-11-24 |
| `u_w_table.txt` | `node --stack-size=65500 code/u_w_table.js 5 15 4096 > data/u_w_table.txt`（w = v2(u+1) ごとの型の分布） | claude-1 | 2026-11-24 |
| `k38_check.txt` | `node code/check_k38.js 2048 > data/k38_check.txt`（定理 K38 の証明の各段階のブロック漸化式による確認） | claude-1 | 2026-11-24 |
| `coverage2.txt` | `node code/coverage2.js 200000 > data/coverage2.txt`（既存の定理で型が決まる m の集計、更新版） | claude-1 | 2026-11-24 |
| `deep_classes.txt` | `node --stack-size=65500 code/deep_classes.js 16384 200000 > data/deep_classes.txt`（型が簡単な規則で決まらない類の調査） | claude-1 | 2026-11-24 |
| `renormalize.txt` | `node --stack-size=65500 code/renormalize.js 120000 > data/renormalize.txt`（m ≡ 9 (mod 32) の型が f(m) の型の関数になるか） | claude-1 | 2026-11-24 |
| `class9_family.txt` | `node --stack-size=65500 code/class9_family.js 23 146 > data/class9_family.txt`（m ≡ 9 (mod 32) の m+2 の連と、周期が伸び続ける族） | claude-1 | 2026-11-24 |
| `class9_clean.txt` | `node --stack-size=65500 code/class9_clean.js 242 240 > data/class9_clean.txt`（m ≡ 9 (mod 32) の前周期のない族と予想 K40 の照合） | claude-1 | 2026-11-24 |
| `k40_chains.txt` | `node --stack-size=65500 code/k40_chains.js 22 44 66 88 > data/k40_chains.txt`（予想 K40 の証明に必要な鎖） | claude-1 | 2026-11-24 |
| `k40_start_state.txt` | `node --stack-size=65500 code/k40_start_state.js 22 44 66 88 110 132 220 > data/k40_start_state.txt`（予想 K40 の各周期の始まりで参照される事実の比較） | claude-1 | 2026-11-24 |
| `k40_closure.txt` | `node --stack-size=65500 code/k40_closure.js 22 44 66 88 110 132 176 220 > data/k40_closure.txt`（予想 K40 の各周期の始まりで参照される事実の分類） | claude-1 | 2026-11-24 |
| `k40_skeleton.txt` | `node code/k40_skeleton.js 440 > data/k40_skeleton.txt`（予想 K40 の証明の骨格で使う鎖の段数と終わり） | claude-1 | 2026-11-24 |
| `coverage_r_20000.txt` | `node code/coverage_r.js 20000 > data/coverage_r_20000.txt`（既存の定理と R の状態の繰り返しで型が決まる m の集計） | claude-1 | 2026-11-24 |
| `coverage_r_200000.txt` | `node code/coverage_r.js 200000 > data/coverage_r_200000.txt`（同上、m ≤ 200000） | claude-1 | 2026-11-24 |
| `check_k29_k38_r.txt` | `node code/check_k29_k38_r.js 200000 > data/check_k29_k38_r.txt`（K29・K38 の型と R の状態の繰り返しで求めた型の照合） | claude-1 | 2026-11-24 |
| `check_k19_k20_k26_r.txt` | `node code/check_k19_k20_k26_r.js 20000 > data/check_k19_k20_k26_r.txt`（K19・K20・K26 の型と R の状態の繰り返しで求めた型の照合） | claude-1 | 2026-11-24 |
| `check_k19_k20_k26_r_200000.txt` | `node code/check_k19_k20_k26_r.js 200000 > data/check_k19_k20_k26_r_200000.txt`（同上、m ≤ 200000） | claude-1 | 2026-11-24 |
| `state_period_even.txt` | `node code/state_period_even.js 300 4000000 > data/state_period_even.txt`（v2(m+1) が偶数の m の R の状態の前周期と周期） | claude-1 | 2026-11-24 |
| `state_period_psi.txt` | `node code/state_period_psi.js data/state_period_even.txt > data/state_period_psi.txt`（m 偶数の状態の周期と ψ の巡回の比較） | claude-1 | 2026-11-24 |
| `k41_orbit.txt` | `node code/k41_orbit.js data/state_period_psi.txt > data/k41_orbit.txt`（定理 K41 の P：軌道による式と ψ の巡回による値の比較） | claude-1 | 2026-11-24 |
| `k42_renorm.txt` | `node code/k42_renorm.js 101 3000000 > data/k42_renorm.txt`（λ(2^v u − 1) と λ(u − 1) の比較） | claude-1 | 2026-11-24 |
| `k42_check.txt` | `node code/check_k42.js 61 40 > data/k42_check.txt`（定理 K42 の証明の段階の確認） | claude-1 | 2026-11-24 |
| `k43_state_gap.txt` | `node code/k43_state_gap.js 3000 2000000 > data/k43_state_gap.txt`（v2(m+1) が奇数の m の状態の周期と型の周期） | claude-1 | 2026-11-24 |
| `k43_start_structure.txt` | `node code/k43_start_structure.js 5:5 5:7 5:9 5:23 5:39 7:5 7:7 7:23 > data/k43_start_structure.txt`（v2(m+1) ≥ 5 の m の周期の始まりの状態の構造） | claude-1 | 2026-11-24 |
| `k41_exact.txt` | `node code/k41_exact.js data/state_period_even.txt > data/k41_exact.txt`（定理 K41c の式と Brent の方法の λ の比較） | claude-1 | 2026-11-24 |
| `k36d_check.txt` | `node code/check_k36d.js 5:14 5:28 5:42 7:50 7:100 9:254 11:102 13:387 13:774 15:234 > data/k36d_check.txt`（定理 K36d′ の鎖の確認） | claude-1 | 2026-11-24 |
| `k36d_even.txt` | `node code/k36d_even.js 7:50 7:100 7:150 11:102 11:204 11:306 13:387 15:234 > data/k36d_even.txt`（予想 K36d の K 偶数の場合の帰納法の閉じ方） | claude-1 | 2026-11-24 |
| `k40_induction.txt` | `node code/k40_induction.js 440 > data/k40_induction.txt`（予想 K40 の N ごとの帰納法の閉じ方） | claude-1 | 2026-11-24 |
| `period_induction_k33odd.txt` | `node --stack-size=65500 code/period_induction.js k33odd 199 > data/period_induction_k33odd.txt`（予想 K33（e 奇数）の型の確定） | claude-1 | 2026-11-24 |
| `period_induction_k34.txt` | `node --stack-size=65500 code/period_induction.js k34 30 > data/period_induction_k34.txt`（予想 K34 の型の確定） | claude-1 | 2026-11-24 |
| `period_induction_k40odd.txt` | `node --stack-size=65500 code/period_induction.js k40odd 429 > data/period_induction_k40odd.txt`（a = (2^N−1)/23 の族の N 奇数の型の確定） | claude-1 | 2026-11-24 |
| `check_period_induction.txt` | `node --stack-size=65500 code/check_period_induction.js 3000 > data/check_period_induction.txt`（period_induction.js の健全性の確認） | claude-1 | 2026-11-24 |
| `period_induction_random.txt` | `node --stack-size=65500 code/period_induction_random.js 40 200 1 > data/period_induction_random.txt`（大きい m の型の確定、無作為抽出） | claude-1 | 2026-11-24 |
| `coverage_pi.txt` | `node --stack-size=65500 code/coverage_pi.js 200000 1048576 > data/coverage_pi.txt`（200000 < m ≤ 2^20 の型の確定） | claude-1 | 2026-11-24 |
| `coverage_pi_small.txt` | `node --stack-size=65500 code/coverage_pi.js 4 200000 > data/coverage_pi_small.txt`（4 < m ≤ 200000 の型の確定） | claude-1 | 2026-11-24 |
| `coverage_pi_22.txt` | `node --stack-size=65500 code/coverage_pi.js 1048576 4194304 > data/coverage_pi_22.txt`（2^20 < m ≤ 2^22 の型の確定） | claude-1 | 2026-11-24 |
| `type_count_certified.txt` | `node --stack-size=65500 code/type_count_certified.js 22 > data/type_count_certified.txt`（確定した型の種類の数、m ≤ 2^22） | claude-1 | 2026-11-24 |
| `cross_check_pi.txt` | `node --stack-size=65500 code/cross_check_pi.js 2097152 4194304 30 7 > data/cross_check_pi.txt`（prove3 で確定した型と R の状態の繰り返しによる型の照合） | claude-1 | 2026-11-24 |
| `k40a_check.txt` | `node code/check_k40a.js 440 > data/k40a_check.txt`（定理 K40a の証明の鎖の確認） | claude-1 | 2026-11-24 |
| `chain_forms_v7.txt` | `node code/chain_forms.js 7 50 100 150 > data/chain_forms_v7.txt`（K36d（K 偶数）の評価がたどる鎖の形、v = 7） | claude-1 | 2026-11-24 |
| `chain_forms_v11.txt`, `chain_forms_v13.txt`, `chain_forms_v15.txt` | `node code/chain_forms.js 11 102 204 306 > data/chain_forms_v11.txt` など（v = 13 は 387 1161、v = 15 は 234 468） | claude-1 | 2026-11-24 |
| `chain_forms_compare.txt` | `node code/chain_forms_compare.js data/chain_forms_v7.txt data/chain_forms_v11.txt data/chain_forms_v13.txt data/chain_forms_v15.txt > data/chain_forms_compare.txt`（鎖の形が N によらないかの比較） | claude-1 | 2026-11-24 |
| `k36_w_class.txt` | `node code/k36_w_class.js 15 > data/k36_w_class.txt`（K36 の族の w = v2(u+1)） | claude-1 | 2026-11-24 |
| `k36d_even_2.txt` | `node code/k36d_even.js 11:102 11:204 11:306 13:387 13:1161 15:234 15:468 > data/k36d_even_2.txt`（K36d の K 偶数の帰納法の閉じ方、追加の組） | claude-1 | 2026-11-24 |
| `k44_family.txt` | `node --stack-size=65500 code/k44_family.js 1006 > data/k44_family.txt`（予想 K44 の族の照合） | claude-1 | 2026-11-24 |
| `w_class_family_v5_w4_a.txt` | `node --stack-size=65500 code/w_class_family_search.js 5 4 63 4096 a any > data/w_class_family_v5_w4_a.txt`（v = 5、w = 4 の類で型が N で変わる族の探索） | claude-1 | 2026-11-24 |
| `w_class_family_v5_w4_m.txt` | `node --stack-size=65500 code/w_class_family_search.js 5 4 63 4096 m any > data/w_class_family_v5_w4_m.txt`（v = 5、w = 4 の類で型が N で変わる族の探索） | claude-1 | 2026-11-24 |
| `w_class_family_v5_w5_a.txt` | `node --stack-size=65500 code/w_class_family_search.js 5 5 63 4096 a any > data/w_class_family_v5_w5_a.txt`（v = 5、w = 5 の類で型が N で変わる族の探索） | claude-1 | 2026-11-24 |
| `w_class_family_v5_w5_m.txt` | `node --stack-size=65500 code/w_class_family_search.js 5 5 63 4096 m any > data/w_class_family_v5_w5_m.txt`（v = 5、w = 5 の類で型が N で変わる族の探索） | claude-1 | 2026-11-24 |
