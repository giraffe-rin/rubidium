# Orchestrator Checkpoint 1 Audit Log

- Generated at (UTC): 2026-11-24T17:18:35.345553Z
- Target branch: `integration/checkpoint-1`
- Total open PRs processed: 229
- Total imported file operations: 40681

| PR | Title | Head Ref | Imported Files |
| --- | --- | --- | ---: |
| #2 | claude-1: 全探索ソルバー 2 実装と勝敗表（1 ≤ m ≤ 30, 0 ≤ r ≤ 2000） | `claude-1/solver` | 39 |
| #4 | claude-1: 予想 K1〜K8（行の型・ブロック漸化式・開始局面の特徴づけ） | `claude-1/conjectures` | 44 |
| #6 | claude-1: K1・K2・K3・K8 の非形式証明（構造定理） | `claude-1/proof-structure` | 45 |
| #8 | claude-1: K4・K5（開始局面の特徴づけ）の非形式証明 | `claude-1/proof-k4` | 46 |
| #10 | claude-1: K6（m ≡ 5 (mod 8) の開始局面）の非形式証明 | `claude-1/proof-k6` | 47 |
| #12 | claude-1: 周期性 K7′ の非形式証明と、R を縮める方法の失敗記録 | `claude-1/proof-periodicity` | 48 |
| #14 | claude-1: 予想 K9（v2(m+1) = 1 の交互型の条件）と必要性の証明 | `claude-1/conjecture-k9` | 51 |
| #16 | claude-1: K9 の十分性の試み（3 値伝播）と、閉じた不変量アプローチの打ち切り | `claude-1/k9-attempt3` | 54 |
| #18 | claude-1: 一般の局面 (r, p) の必勝戦略（系 W） | `claude-1/strategy` | 57 |
| #20 | claude-1: 第 3 の実装（行の型）による検証範囲の拡大 | `claude-1/rowtype-check` | 60 |
| #22 | claude-1: 予想 K10（v2(m+1) = 3 の交互型）と g₁ の式 | `claude-1/conjecture-k10` | 63 |
| #24 | claude-1: K10 (a)（v2(m+1) = 3, u ≡ 1 (mod 8)）の非形式証明 | `claude-1/proof-k10a` | 64 |
| #26 | claude-1: K9 の十分性（m ≡ 25 (mod 32)）の証明と、m ≤ 1000 の証明書 | `claude-1/proof-k9-25mod32` | 67 |
| #28 | claude-1: K9 の十分性（v2(3t+1) = 3）の証明と、証明書の大きさの予想 | `claude-1/proof-k9-v3` | 69 |
| #30 | claude-1: 定理 K9 の十分性の一般の証明（K9 全体が [非形式証明] に） | `claude-1/proof-k9-general` | 70 |
| #32 | claude-1: K10c（v2(m+1) = 3 の必要条件）と K11（v2(m+1) ≥ 5 は交互型でない） | `claude-1/proof-k10c-k11` | 71 |
| #34 | claude-1: 交互型でない m の開始局面：「110」型の条件（K12） | `claude-1/proof-k12` | 76 |
| #36 | claude-1: 「100」型の条件（K13、v2(m+1) = 3） | `claude-1/proof-k13` | 79 |
| #38 | claude-1: 「11010」型の条件（K12″、K12′ の k = 2）と一般の k での g₂ の式 | `claude-1/proof-k12-k2` | 82 |
| #40 | claude-1: k ≥ 2 で 1(10)^k 型なら v2(Q_k) = 0（定理 K14） | `claude-1/proof-k14` | 85 |
| #42 | claude-1: K12′ の十分性を 2 ≤ k ≤ 16 で示す（定理 K15、記号の証明書） | `claude-1/proof-k12-symbolic` | 88 |
| #44 | claude-1: m の合同類ごとの 1 次式の証明書（定理 K16） | `claude-1/affine-certificates` | 97 |
| #46 | K16 の範囲の拡大と予想 K17（Issue #45） | `claude-1/affine-deeper` | 106 |
| #48 | 証明書で決まらない類の構造（観察 K18、Issue #47） | `claude-1/unresolved-structure` | 109 |
| #51 | 定理 K19：v2(h−1) が奇数なら 1^{j+1}0 型（Issue #50） | `claude-1/proof-k19` | 112 |
| #53 | 予想 K20：v2(m+1) = 3 で v2(5m+13) が偶数なら 1^{i−1}0 / 1^{i−1}00 型（Issue #52） | `claude-1/conjecture-k20` | 115 |
| #55 | 付値の規則の探索（v2(m+1) = 3, 5）（Issue #54） | `claude-1/valuation-search` | 119 |
| #57 | 定理 K20 の手での証明（Issue #56） | `claude-1/proof-k20` | 120 |
| #58 | 決まらない類の再分割（A ≤ 2^20）（Issue #49） | `claude-1/affine-refine` | 113 |
| #60 | E = m + 2 − 3u と予想 K21（Issue #59） | `claude-1/v5-chain` | 126 |
| #62 | 定理 K21 の証明（型の始まり）（Issue #61） | `claude-1/proof-k21` | 127 |
| #64 | 定理 K22：型の始まりの 1 の個数（Issue #63） | `claude-1/proof-k22` | 130 |
| #66 | 定理 K23：型の始まりの 1 の個数の再帰式（Issue #65） | `claude-1/k23-recursion` | 133 |
| #68 | 予想 K24：K23 の再帰の停止（Issue #67） | `claude-1/k23-termination` | 136 |
| #70 | 観察 K25：証明書の一覧の ℓ・μ による分類（Issue #69） | `claude-1/classes-by-l-mu` | 139 |
| #72 | 予想 K26：v2(m+1) = 3、ℓ = 1 の m の型（Issue #71） | `claude-1/k26-v3-l1` | 142 |
| #74 | 決まらない類の再分割（v2(m+1) = 3、A ≤ 2^19）（Issue #73） | `claude-1/affine-refine-v3` | 116 |
| #76 | 決まらない類の再分割（v2(m+1) = 5、A ≤ 2^19）（Issue #75） | `claude-1/affine-refine-v5` | 119 |
| #78 | 決まらない類の再分割（v2(m+1) = 7、A ≤ 2^19）（Issue #77） | `claude-1/affine-refine-v7` | 122 |
| #80 | 定理 K27：m = 9 の型を手で示す（Issue #79） | `claude-1/m9-by-hand` | 143 |
| #82 | 定理 K28：m = 7 の型を手で示す（Issue #81） | `claude-1/m7-by-hand` | 144 |
| #84 | 既存の定理で型が決まる m の集計（Issue #83） | `claude-1/coverage` | 125 |
| #86 | v2(m+1) = 9, 11 の 1 次式の証明書（Issue #85） | `claude-1/affine-v9-v11` | 130 |
| #88 | 予想 K29：v2(m+1) ≥ 5 で ℓ = 1 なら 1 0^{(v−1)/2} 型（Issue #87） | `claude-1/k29` | 133 |
| #90 | 決まっていない小さい m の型の調査（Issue #89） | `claude-1/uncovered-small` | 134 |
| #92 | 定理 K29.1：K29 の v = 5 の最初の周期（Issue #91） | `claude-1/k29-v5-first` | 137 |
| #94 | 定理 K29.2：K29 の v = 5 の場合の完全な証明（Issue #93） | `claude-1/k29-v5-full` | 138 |
| #96 | 定理 K29.3：予想 K29 を 5 ≤ v ≤ 27 で示す（Issue #95） | `claude-1/k29-general` | 141 |
| #98 | 観察 K30：K29.3 の 3 値の計算の依存の範囲（Issue #97） | `claude-1/k29-cone` | 144 |
| #100 | 定理 K29：すべての奇数 v ≥ 5 での手での証明（Issue #99） | `claude-1/k29-proof` | 147 |
| #102 | u の合同類ごとの 3 値の証明書（Issue #101） | `claude-1/u-class-symbolic` | 150 |
| #104 | 3 値の 1 次式の証明書（Issue #103） | `claude-1/affine3` | 159 |
| #106 | 3 値の 1 次式の証明書：v2(m+1) = 1 の未証明の類（Issue #105） | `claude-1/affine3-v1` | 162 |
| #108 | 3 値の証明書で決まらなかった類の再分割：v2(m+1) = 7（Issue #107） | `claude-1/affine3-refine` | 166 |
| #109 | 3 値の証明書の再分割：v2(m+1) = 5（Issue #107） | `claude-1/affine3-refine-v5` | 169 |
| #110 | 3 値の証明書の再分割：v2(m+1) = 3（Issue #107） | `claude-1/affine3-refine-v3` | 172 |
| #111 | gemini-2: PR #6（K1・K2・K3・K8）の独立査読と Python ソルバーによる検証 | `gemini-2/review-structure` | 4 |
| #112 | gemini-2: PR #8（K4・K5）の独立査読と Python 独立検証 | `gemini-2/review-k4` | 4 |
| #113 | gemini-2: PR #10（K6）の独立査読と Python 独立検証（要確認：補足に誤りあり） | `gemini-2/review-k6` | 4 |
| #114 | gemini-2: PR #12（周期性 K7′）の独立査読と Python 独立検証 | `gemini-2/review-periodicity` | 4 |
| #115 | gemini-2: PR #18（必勝戦略 系 W）の独立査読と Python 独立検証 | `gemini-2/review-strategy` | 4 |
| #116 | gemini-2: PR #14（定理 K9 の必要性）の独立査読と Python 独立検証 | `gemini-2/review-k9-nec` | 4 |
| #117 | gemini-2: PR #22（命題 K10a・系 K10b）の独立査読と Python 独立検証 | `gemini-2/review-k10-g1` | 4 |
| #118 | gemini-2: PR #24（定理 K10 (a)）の独立査読と Python 独立検証 | `gemini-2/review-k10a` | 4 |
| #119 | gemini-2: PR #26（定理 K9-25・K9 計算機証明書）の独立査読と Python 独立検証 | `gemini-2/review-k9-25mod32` | 4 |
| #120 | 3 値の証明書の再分割：v2(m+1) = 1（Issue #107） | `claude-1/affine3-refine-v1` | 175 |
| #122 | K6 の補足「先手の必勝手」の訂正（Issue #121、PR #113 の指摘） | `claude-1/fix-k6-moves` | 50 |
| #124 | 3 値の証明書で間隔が不明になる原因の分類（Issue #123） | `claude-1/affine3-diag` | 178 |
| #126 | meet で止まる類の (p, L) の t による変化（Issue #125） | `claude-1/meet-preperiod` | 181 |
| #128 | gemini-2: PR #28（定理 K9-v3）の独立査読と Python 独立検証 | `gemini-2/review-k9-v3` | 4 |
| #129 | gemini-2: PR #30（定理 K9 全体の一般証明）の独立査読と Python 独立検証 | `gemini-2/review-k9-general` | 4 |
| #130 | gemini-2: PR #32（定理 K10c・系・定理 K11）の独立査読と Python 独立検証 | `gemini-2/review-k10c-k11` | 4 |
| #131 | gemini-2: PR #34（定理 K12）の独立査読と Python 独立検証 | `gemini-2/review-k12` | 4 |
| #132 | gemini-2: PR #36（定理 K13）の独立査読と Python 独立検証 | `gemini-2/review-k13` | 4 |
| #133 | gemini-2: PR #38（定理 K12″）の独立査読と Python 独立検証 | `gemini-2/review-k12-k2` | 4 |
| #134 | gemini-2: PR #40（定理 K14・系 K14.1）の独立査読と Python 独立検証 | `gemini-2/review-k14` | 4 |
| #135 | gemini-2: PR #42（定理 K15・系 K15.1）の独立査読と記号証明書の独立再計算 | `gemini-2/review-k15` | 4 |
| #136 | gemini-2: PR #44（定理 K16）の独立査読と全 147 類の 1 次式証明書の独立再計算 | `gemini-2/review-k16` | 4 |
| #137 | gemini-2: PR #46（定理 K16 の範囲の拡大）の独立査読と全 1,116 類の独立再計算 | `gemini-2/review-k16-deeper` | 4 |
| #138 | gemini-2: PR #51（定理 K19・系 K19.1）の独立査読と Python 独立検証 | `gemini-2/review-k19` | 4 |
| #139 | 間隔が不明で止まる類の型の t による変化（Issue #127） | `claude-1/cause-type-variation` | 183 |
| #141 | 止まる類の中での型の分布（Issue #140） | `claude-1/type-vs-t` | 186 |
| #143 | 予想 K31：型の種類の数の増え方（Issue #142） | `claude-1/type-growth` | 189 |
| #145 | 型の種類の数を 600 ブロックで確かめる（Issue #144） | `claude-1/type-growth-600` | 191 |
| #147 | 定理 K32：m+1 の間隔の連は (v+1)/2 以下（Issue #146） | `claude-1/type-runs` | 196 |
| #149 | 予想 K33：族 m = 9·2^e + 1 の型（Issue #148） | `claude-1/one-runs` | 201 |
| #151 | 予想 K34：v2(m+1) = 3 の族の型（Issue #150） | `claude-1/family-v3` | 204 |
| #153 | 定理 K33a：m = 9·2^e + 1（e 偶数）の型（Issue #152） | `claude-1/k33-even` | 207 |
| #155 | 予想 K33・K34 の検証範囲の拡大（Issue #154） | `claude-1/bigint-families` | 211 |
| #157 | 予想 K33（e 奇数）で参照される距離の構造（Issue #156） | `claude-1/k33-odd-structure` | 214 |
| #159 | 定理 K35：m = (3·16^k − 13)/5 の型（Issue #158） | `claude-1/k35` | 218 |
| #161 | v2(m+1) = 5, 7 の族の探索（Issue #160） | `claude-1/family-search-v5` | 223 |
| #163 | 定理 K36：v2(m+1) が奇数なら型は無限に多い（Issue #162） | `claude-1/k36` | 226 |
| #165 | 定理 K36 の族の m+1 の連の長さ（Issue #164） | `claude-1/k36-s` | 229 |
| #167 | 定理 K37：u ≡ 7 (mod 16) などの類の型（Issue #166） | `claude-1/u-class-q` | 234 |
| #169 | 予想 K38：v2(u+1) による型（Issue #168） | `claude-1/u-class-q-k9` | 238 |
| #171 | 定理 K38：w = v2(u+1) が奇数（≥ 3）なら型は 1 0^{(v+1)/2}（Issue #170） | `claude-1/k38-proof` | 241 |
| #173 | 型が証明済みの m の割合の更新（Issue #172） | `claude-1/coverage2` | 244 |
| #175 | 残っている類の調査（Issue #174） | `claude-1/deep-classes` | 247 |
| #177 | くりこみの試み（Issue #176） | `claude-1/renormalize` | 250 |
| #179 | 予想 K39：m ≡ 9 (mod 32) の類の型は無限に多い（Issue #178） | `claude-1/class9-infinite` | 253 |
| #180 | gemini-2: PR #122（K6 補足「先手の必勝手」の訂正）の独立査読と Python 独立検証 | `gemini-2/review-fix-k6-moves` | 4 |
| #182 | 予想 K40：m ≡ 9 (mod 32) の前周期のない族（Issue #181） | `claude-1/class9-clean` | 256 |
| #184 | 予想 K40（q = 23）の証明の途中経過（Issue #183） | `claude-1/k40-chains` | 259 |
| #185 | gemini-2: PR #57（定理 K20）の独立査読と Python 独立検証 | `gemini-2/review-k20` | 4 |
| #187 | 予想 K40：周期の始まりの状態の比較（Issue #186） | `claude-1/k40-start-state` | 262 |
| #188 | gemini-2: PR #62（定理 K21）の独立査読と Python 独立検証 | `gemini-2/review-k21` | 4 |
| #190 | K20 のログの軽微な誤記の訂正（Issue #189、PR #185 の指摘） | `claude-1/fix-k20-typos` | 121 |
| #191 | gemini-2: PR #64（定理 K22）の独立査読と Python 独立検証 | `gemini-2/review-k22` | 4 |
| #193 | 予想 K40：周期の始まりの事実の分類（Issue #192） | `claude-1/k40-closure` | 265 |
| #194 | gemini-2: PR #66（定理 K23）の独立査読と Python 独立検証 | `gemini-2/review-k23` | 4 |
| #196 | 予想 K40 の証明の骨格（Issue #195） | `claude-1/k40-skeleton` | 268 |
| #198 | v2(m+1) が奇数の場合の結果のまとめ（Issue #197） | `claude-1/summary-odd-v` | 269 |
| #199 | gemini-2: PR #80（定理 K27：m = 9）の独立査読と Python 独立検証 | `gemini-2/review-k27` | 4 |
| #200 | gemini-2: PR #82（定理 K28：m = 7）の独立査読と Python 独立検証 | `gemini-2/review-k28` | 4 |
| #201 | gemini-2: PR #92/#94/#96/#100（定理 K29.1〜K29.3・定理 K29）の独立査読と Python 独立検証 | `gemini-2/review-k29` | 4 |
| #202 | gemini-2: PR #147（補題 Q_n・定理 K32）の独立査読と Python 独立検証（要確認：47 行仮定漏れ） | `gemini-2/review-k32` | 4 |
| #203 | gemini-2: PR #153/#159/#163/#165（定理 K33a・K35・K36・命題 K36c）の独立査読と Python 独立検証 | `gemini-2/review-k33a-k35-k36` | 4 |
| #205 | m ≤ 200000 のすべての m の型（Issue #204） | `claude-1/coverage-r` | 273 |
| #206 | gemini-2: PR #167/#169/#171（定理 K37・K38・命題 K38c）の独立査読と Python 独立検証 | `gemini-2/review-k37-k38` | 4 |
| #207 | gemini-2: PR #58/#74/#76/#78/#86（2 値 1 次式証明書群・全 2,431 類）の独立査読と Python 独立再計算 | `gemini-2/review-affine-refine` | 4 |
| #209 | 定理 K29・K38 の R による照合（Issue #208） | `claude-1/check-k29-k38-r` | 276 |
| #210 | gemini-2: PR #104/#106/#108/#109/#110/#120（3 値 1 次式証明書群・全 7,919 類）の独立査読と Python 独立再計算 | `gemini-2/review-affine3` | 4 |
| #212 | 定理 K19・K20・K26 の R による照合（Issue #211） | `claude-1/check-k19-k20-k26-r` | 279 |
| #213 | gemini-2: PR #68（K24 不動点非到達）・PR #72（補題 K26.0・K26 部分証明全 16 類）の独立査読と Python 独立検証 | `gemini-2/review-k24-k26` | 4 |
| #215 | K19・K20・K26 の R による照合（m ≤ 200000、Issue #214） | `claude-1/check-k19-k20-k26-r-200k` | 281 |
| #217 | 観察 K41：v2(m+1) が偶数の m の R の状態の周期（Issue #216） | `claude-1/check-k4-r` | 286 |
| #219 | 定理 K41：m 偶数のときの R の状態の周期（Issue #218） | `claude-1/k41-proof` | 289 |
| #221 | 定理 K42：v2(m+1) が偶数の m の状態のくりこみ（Issue #220） | `claude-1/k42-renorm` | 294 |
| #223 | 観察 K43：v2(m+1) が奇数の m の状態の周期（Issue #222） | `claude-1/k43-state-gap` | 297 |
| #225 | 観察 K43 の証明に向けた周期の始まりの状態（Issue #224） | `claude-1/k43-start-structure` | 300 |
| #227 | 定理 K41c：m 偶数のときの状態の周期の正確な式（Issue #226） | `claude-1/k41-exact` | 303 |
| #229 | 定理 K32 の主張の仮定漏れの訂正（Issue #228、PR #202 の指摘） | `claude-1/fix-k32-statement` | 197 |
| #231 | 定理 K36d′：K 奇数なら m+1 の連の長さは 1（Issue #230） | `claude-1/k36d-odd` | 306 |
| #233 | 予想 K36d の K 偶数の場合の帰納法（Issue #232） | `claude-1/k36d-even` | 309 |
| #235 | 結果のまとめの更新（Issue #234） | `claude-1/summary-2` | 310 |
| #237 | 予想 K40 を N ごとに帰納法で確かめる（Issue #236） | `claude-1/k40-closure-check` | 313 |
| #239 | 周期についての帰納法による型の確定（Issue #238） | `claude-1/period-induction` | 320 |
| #241 | 周期についての帰納法を大きい m に当てる（Issue #240） | `claude-1/period-induction-random` | 323 |
| #243 | 周期についての帰納法の一般化（Issue #242） | `claude-1/period-induction-general` | 324 |
| #245 | 5 ≤ m ≤ 2^20 のすべての m の型（Issue #244） | `claude-1/coverage-pi` | 328 |
| #246 | gemini-2: PR #219/#227/#221（定理 K41・K41c・K42・系 K42b）の独立査読と Python 独立検証 | `gemini-2/review-k41-k42` | 4 |
| #247 | gemini-2: PR #231（定理 K36d′）・PR #233（予想 K36d K 偶数 8 組）の独立査読と Python 独立検証 | `gemini-2/review-k36d` | 4 |
| #249 | 型の確定を m ≤ 2^22 に広げる（Issue #248） | `claude-1/coverage-pi-22` | 330 |
| #250 | gemini-2: PR #237/#239/#241（周期帰納法 prove/prove2・K40・K33奇数・K34・無作為検証）の独立査読と Python 独立検証 | `gemini-2/review-period-induction` | 4 |
| #252 | 確定した型の種類の数（Issue #251） | `claude-1/type-count-certified` | 333 |
| #253 | gemini-2: PR #243/#245/#249（prove3一般化・5 ≤ m ≤ 2^22 全1,398,100例）の独立査読と Python 独立全数検証 | `gemini-2/review-prove3-coverage` | 4 |
| #255 | prove3 の型の確定の独立な照合（Issue #254） | `claude-1/cross-check-22` | 336 |
| #257 | 定理 K40a と予想 K39 の証明（Issue #256） | `claude-1/k40a-proof` | 339 |
| #259 | 定理 K36d″（v = 7）（Issue #258） | `claude-1/k36d-even-v7` | 342 |
| #261 | 定理 K36d″ を v = 11, 13, 15 に広げる（Issue #260） | `claude-1/k36d-even-v11-15` | 349 |
| #262 | gemini-2: PR #257（定理 K40a・系 K39）・PR #259（定理 K36d″ v=7）の独立査読と Python 記号・数値独立検証 | `gemini-2/review-k40a-k36d-v7` | 4 |
| #263 | gemini-2: PR #252（m ≤ 2^22 確定型種類数 7,406 種類）・PR #255（30 例照合）の独立査読と Python 独立全数検証 | `gemini-2/review-type-count-22` | 4 |
| #264 | gemini-2: PR #261（定理 K36d″ の拡大 v = 11, 13, 15）の独立査読と Python 記号・数値独立検証 | `gemini-2/review-k36d-v11-15` | 4 |
| #266 | period_induction.js の堅牢化（Issue #265、PR #250・#253 の指摘） | `claude-1/period-induction-harden` | 350 |
| #268 | 系 K36e：w = 2 の類の型は無限に多い（Issue #267） | `claude-1/w-even-family` | 353 |
| #269 | gemini-2: PR #268（系 K36e）・PR #266（period_induction.js 堅牢化確認）の独立査読と Python 独立検証 | `gemini-2/review-k36e` | 4 |
| #271 | claude-1: 予想 K44（v = 5、w = 4 の類で周期が伸び続ける族） | `claude-1/w4-family` | 361 |
| #273 | claude-1: 予想 K45（v = 7、w = 4 の類で m+2 の連が伸び続ける族） | `claude-1/w-class-v7` | 370 |
| #275 | claude-1: 予想 K44 を N ごとに周期についての帰納法で確定（N ≤ 1006） | `claude-1/k44-induction` | 373 |
| #277 | claude-1: 予想 K45 の族を N ごとに周期についての帰納法で確定（N ≤ 616） | `claude-1/k45-induction` | 376 |
| #279 | claude-1: 定理 K44（v = 5、w = 4 の類の型は無限に多い） | `claude-1/k44-proof` | 379 |
| #281 | claude-1: 予想 K46（偶数 w ≤ v−1 のすべての類で型は無限に多い：K36・K44 の一般化） | `claude-1/w-even-general` | 382 |
| #283 | claude-1: 定理 K47（偶数 w ≤ v−1 のすべての類で型は無限に多い） | `claude-1/first-run` | 385 |
| #285 | claude-1: 定理 K47b（w = v の類の型は無限に多い） | `claude-1/w-equals-v` | 388 |
| #287 | claude-1: まとめ（その 3）：w = v2(u+1) による分類と K44〜K47b | `claude-1/summary-3` | 389 |
| #289 | claude-1: K47・K47b の族の型を prove3 で確定（前周期と周期の中の連、予想 K46′） | `claude-1/k47-preperiod` | 392 |
| #291 | gemini-2: PR #279（定理 K44）・PR #275（K44 123例）・PR #277（K45 21例）の独立査読と Python 記号・数値独立検証 | `gemini-2/review-k44-k45` | 4 |
| #292 | claude-1: 補題 K48（直前に m+1 が ρ/2 個以上続く位置からの m+2 の連はちょうど ⌈(N−v)/ρ⌉） | `claude-1/k48-runs` | 395 |
| #293 | gemini-2: PR #283（定理 K47）・PR #285（定理 K47b）の独立査読と Python 独立検証 | `gemini-2/review-k47` | 4 |
| #295 | gemini-2: PR #289（K47/K47b 875例確定）・PR #292（補題 K48・系 K48b）の独立査読と Python 独立検証 | `gemini-2/review-k48-preperiod` | 4 |
| #296 | claude-1: 定理 K49（w = 4 の類は周期部分だけで数えても型が無限に多い） | `claude-1/k49-rho4` | 398 |
| #298 | gemini-2: PR #296（定理 K49・補題 K49.1：w = 4 の類の周期部分無限性）の独立査読と Python 独立検証 | `gemini-2/review-k49` | 4 |
| #299 | claude-1: 定理 K50（v ≤ 13 のすべての偶数 w の類は周期部分だけで数えても型が無限に多い） | `claude-1/k50-general` | 403 |
| #301 | claude-1: 定理 K50 を v = 15, 17 に広げる | `claude-1/k50-v15-17` | 407 |
| #303 | gemini-2: PR #299・#301（定理 K50：5 ≤ v ≤ 17 全 28 組）の独立査読と Python 記号・数値独立検証 | `gemini-2/review-k50` | 4 |
| #304 | claude-1: 予想 K51（w = v の類も周期部分だけで数えて型が無限に多い） | `claude-1/k51-w-equals-v` | 412 |
| #307 | claude-1: 定理 K50 の剰余類を大きい ρ（≤ 28）で確認 | `claude-1/k50-large-rho` | 414 |
| #309 | claude-1: 定理 K50 の形式的な評価で ρ ≤ 60 に広げる | `claude-1/k50-formal` | 416 |
| #311 | claude-1: 補題 K52（定理 K50 の評価木は N によらない有限の再帰） | `claude-1/k52-recursion` | 417 |
| #313 | claude-1: 補題 K53（鎖の写像は ρ 桁の 2 進の語の巡回シフト） | `claude-1/k53-rotation` | 420 |
| #315 | claude-1: 定理 K54（すべての偶数 w ≤ v−1 の類は周期部分だけで数えても型が無限に多い） | `claude-1/k54-general` | 423 |
| #317 | claude-1: 定理 K55（w = v の類も周期部分だけで数えて型が無限に多い） | `claude-1/k55-w-equals-v` | 427 |
| #319 | claude-1: まとめ（その 4）：w = v2(u+1) による分類の完成（K44〜K55） | `claude-1/summary-4` | 428 |
| #321 | gemini-2: PR #307/#309（K50 ρ≤60）・PR #311（補題 K52）・PR #313（補題 K53）・PR #315（定理 K54）の独立査読と Python 独立検証 | `gemini-2/review-k52-k54` | 4 |
| #322 | claude-1: 命題 K33c（予想 K33（e 奇数）の帰納法の仮定の集合の形） | `claude-1/k33-odd-assumptions` | 431 |
| #324 | claude-1: 補題 K33d（E 型ブロックで v2 = 1 の距離は入らない）と K33（e 奇数）の仮定の簡約 | `claude-1/k33-odd-trace` | 435 |
| #326 | gemini-2: PR #317（定理 K55：w = v の類の周期部分無限性）の独立査読と Python 独立検証 | `gemini-2/review-k55` | 4 |
| #327 | claude-1: prove3 に補題 K33d の選択肢を加える（v = 1 で仮定が約 40% 減） | `claude-1/prove3-k33d` | 438 |
| #329 | claude-1: 定理 K56（K54・K55 は R ≡ L + 1 (mod 2L) でも成り立つ：予想 K51 の残り） | `claude-1/k56-residue` | 441 |
| #331 | claude-1: 命題 K57（間隔の列の先頭は h の鎖の b の軌道で決まる：K47 の一般化） | `claude-1/k57-orbit-predict` | 444 |
| #333 | gemini-2: PR #322（命題 K33c）・PR #324（補題 K33d・仮定簡約）の独立査読と Python 独立検証 | `gemini-2/review-k33c-k33d` | 4 |
| #334 | claude-1: 予想 K33（e 奇数）の型の確定を e ≤ 399 に広げる | `claude-1/k33-odd-399` | 447 |
| #336 | claude-1: 予想 K34 は定理 K47 の族の N 奇数の場合、予想 K58（N ≤ 401 で確定） | `claude-1/k47-odd-N` | 450 |
| #338 | claude-1: 定理 K59（予想 K34・K58 の族の先頭の m+2 の連、鎖が N を越える場面の扱い） | `claude-1/k47-crossing` | 453 |
| #339 | gemini-2: PR #327（prove3+K33d）・PR #329（定理 K56）・PR #331（命題 K57）の独立査読と Python 独立検証 | `gemini-2/review-k56-k57-k33d` | 4 |
| #340 | gemini-2: PR #334（K33 e≤399）・PR #336（K34/K58）・PR #338（定理 K59）の独立査読と Python 独立検証 | `gemini-2/review-k33ext-k58-k59` | 4 |
| #344 | claude-1: 予想 K34・K58 の帰納法の 1 段の分解（仮定は (a − s) の倍数 1〜2 個） | `claude-1/k34-trace` | 456 |
| #346 | claude-1: 予想 K34・K58 の E 型ブロックの自明でない事実は N によらない有限個 | `claude-1/k34-nontrivial` | 458 |
| #348 | claude-1: 定理 K58（5a + 1 = 7·2^N、N ≡ 3 (mod 4) の型は周期 1^{R+2} 0 1^R 0） | `claude-1/k58-shapes` | 461 |
| #350 | claude-1: 定理 K34（予想 K34 の証明：m = 8(36·16^k − 1)/5 − 1 の型） | `claude-1/k34-shapes` | 464 |
| #352 | claude-1: 定理 K33（予想 K33 の証明：m = 9·2^e + 1 の型） | `claude-1/k33-shapes` | 467 |
| #354 | gemini-2: PR #331 修正（命題 K57）・PR #344・#346・#348（定理 K58）の独立査読と Python 独立検証 | `gemini-2/review-k57fix-k34-k58` | 4 |
| #356 | claude-1: 予想 K60（v = 5、ρ = 2、N 奇数の族の型は N mod 28 の類ごとに一定の形） | `claude-1/v5-odd-N` | 470 |
| #359 | antigravity-1: PR #350（定理 K34）の独立査読（修正依頼） | `antigravity-1/review-k34` | 1 |
| #360 | claude-1: 鎖と評価木の記号的な評価器（定理 K58・K34・K33 の 1 段を R の 1 次式で評価） | `claude-1/chain-symbolic` | 473 |
| #362 | claude-1: 定理 K60（v = 5、ρ = 2、N 奇数の 14 類の型）と記号的な評価器の R の下限 | `claude-1/k60-symbolic` | 474 |
| #364 | claude-1: 定理 K3 の Lean 4 での形式化（sorry なし） | `claude-1/lean-k3` | 9 |
| #365 | gemini-2: 定理 K58・K33・K34（PR #348/#350/#352/#360）および予想 K60（PR #356）の独立査読と厳密有理数 Python 独立検証 | `gemini-2/review-k33-k34-k58-symbolic` | 4 |
| #367 | claude-1: 定理 K5 と定理 K4 の最初の P 局面の Lean 4 での形式化 | `claude-1/lean-k5` | 11 |
| #368 | claude-1: 命題 K61（間隔の列の先頭の m+2 の連の長さ、越える場面を含む：命題 K57 の一般化） | `claude-1/k61-predict2` | 477 |
| #370 | claude-1: 命題 K62（越える場面の規則を一般の奇数 r に広げる） | `claude-1/k61-general-r` | 480 |
| #371 | gemini-2: Lean 4 形式化（PR #364 K3・PR #367 K5）・定理 K60（PR #362）・命題 K61/K62（PR #368・#370）の独立査読と検証 | `gemini-2/review-lean-k60-k62` | 4 |
| #373 | Lean: 計算できる判定 isPb と IsP の同値性、全探索との照合（Issue #372） | `claude-1/lean-decide` | 18 |
| #375 | Lean: 定理 K4 の m が偶数の場合（(n, 0) が P ⇔ (m+1) \| n）（Issue #374） | `claude-1/lean-k4-even` | 20 |
| #377 | Lean: 定理 K4 全体の形式化（sorry なし、公理は propext・Quot.sound のみ）（Issue #376） | `claude-1/lean-k4-full` | 22 |
| #379 | Lean の DP による勝敗表（m ≤ 30、r ≤ 2000）と data/tables の照合：990495 局面すべて一致（Issue #378） | `claude-1/lean-tables` | 27 |
| #381 | Lean と JavaScript の DP の照合を m ≤ 100、r ≤ 3000 に広げる：100 個の m すべてで要約が一致（Issue #380） | `claude-1/lean-tables-100` | 32 |
| #384 | 予想 K7 の確認範囲を 2 ≤ m ≤ 400 に広げる：m = 55, 95 以外は純周期（Issue #383） | `claude-1/k7-periods` | 486 |
| #386 | 予想 K7 の確認範囲を m ≤ 1000 に：前周期のある m は 55, 95, 481, 801, 929, 991（Issue #385） | `claude-1/k7-periods-1000` | 489 |
| #388 | gemini-2: 命題 K61/K62 修正（PR #368/#370）・Lean 4 定理 K4（PR #373/#375/#377）・Lean DP 照合（PR #379/#381）の独立査読と検証 | `gemini-2/review-k61k62fix-lean-k4-dp` | 4 |
| #389 | 予想 K7 の確認範囲を m ≤ 2000 に：前周期のある m は 10 個、前周期は最初の 2〜6 個の間隔だけ（Issue #387） | `claude-1/k7-periods-2000` | 493 |
| #391 | Lean: 定理 K6（m ≡ 5 (mod 8) の開始局面）の形式化（sorry なし、公理は propext・Quot.sound のみ）（Issue #390） | `claude-1/lean-k6` | 34 |
| #393 | Lean: 定理 K9 の十分性（v2(m+1) = 1、v2(3h+1) 奇数なら交互型）の形式化（Issue #392） | `claude-1/lean-k9` | 36 |
| #395 | Lean: 定理 K9 全体（必要性と同値の形）の形式化（Issue #394） | `claude-1/lean-k9-nec` | 37 |
| #397 | Lean: 定理 K10 (a)（m+1 = 8u、u ≡ 1 (mod 8)、u ≥ 9 なら交互型）の形式化（Issue #396） | `claude-1/lean-k10a` | 39 |
| #399 | Lean: 定理 K13（100 型）の形式化（Issue #398） | `claude-1/lean-k13` | 41 |
| #400 | gemini-2: Lean 4 定理 K6/K9/K10(a)（PR #391/#393/#395/#397）および予想 K7 m≤2000（PR #384/#386/#389）の独立査読と検証 | `gemini-2/review-lean-k6k9k10a-k7periods` | 4 |
| #401 | claims を査読者の版にそろえ、STATUS.md を自動生成に切り替える（CI validate の修正、Issue #342 の一部） | `claude-1/claims-sync` | 495 |
