# lean

Lean 4 による形式化を置く場所です。
`sorry` が残っている定理は `[Lean検証済み]` と呼びません。

## Lake プロジェクト

- Lean：`leanprover/lean4:v4.36.0`（`lean-toolchain`）
- Mathlib：使っていない（Lean の core だけ）
- ビルド方法（このディレクトリで）：`lake build`
- 使っている公理の確認：`lake env lean` で `#print axioms Rubidium.K3` を実行すると、`propext` と `Quot.sound` だけが出る（`sorryAx` が出ない）。`Rubidium.K5` は背理法のため `Classical.choice` も使う。

## 中身

| ファイル | 内容 |
|---|---|
| `Rubidium/Game.lean` | ゲームの定義。`IsP m r p`：局面 (r, p) が後手必勝（P 局面）。`ev2 r`：v2(r) が偶数（r ≥ 1）。 |
| `Rubidium/K3.lean` | 定理 K3：1 ≤ r ≤ m なら、`IsP m r p ↔ p = r ∧ ev2 r = true`。 |
| `Rubidium/K4Even.lean` | 定理 K4 の m が偶数の場合 `K4_even`：m が偶数なら `IsP m n 0 ↔ n % (m+1) = 0`。補題 `row_all`（m が偶数なら行 j(m+1) はすべての p で P）、`not_isP_of_row`（P の行 r から d 先の (r+d, p) は p ≠ d なら N）。公理は `propext`・`Quot.sound` だけ。 |
| `Rubidium/K4Full.lean` | **定理 K4 全体** `K4`：m ≥ 1 のとき `(∀ n, IsP m n 0 ↔ n % (m+1) = 0) ↔ ev2 (m+1) = true`。2 の付値 `v2` と補題 `v2_add`（v2 x < v2 y なら v2(x+y) = v2 x）、`ev2_iff_v2`、m が奇数の場合の `row_all_odd`・`blk_step`・`K4_odd`。公理は `propext`・`Quot.sound` だけ。 |
| `Rubidium/K6.lean` | **定理 K6** `K6`：m % 8 = 5 なら `IsP m n 0 ↔ (n % (2m+3) = 0 ∨ n % (2m+3) = m+2)`。補題 `odd_of_rows`（P の行の後の奇数 d の (r+d, d) は P）、`row_long`、`k6_rows`。公理は `propext`・`Quot.sound` だけ。 |
| `Rubidium/K9.lean` | **定理 K9 の十分性** `K9_suff`：m % 4 = 1、m ≥ 5、v2(3h+1) が奇数なら `IsP m n 0 ↔ (n % (2m+3) = 0 ∨ n % (2m+3) = m+2)`。不変量 `Blk`（偶数番目のブロック）と `BlkO`（奇数番目）、`blkE_step`、`blkO_of_blk`、`k9_rows`。公理は `propext`・`Quot.sound` だけ。 |
| `Rubidium/K9.lean`（追加） | **定理 K9 全体** `K9`：m % 4 = 1、m ≥ 5 のとき `(∀ n, IsP m n 0 ↔ (n % (2m+3) = 0 ∨ n % (2m+3) = m+2)) ↔ v2(3h+1) % 2 = 1`。必要性 `K9_nec`（v2(3h+1) が偶数なら (2m+3, 0) は N）。公理は `propext`・`Quot.sound` だけ。 |
| `Rubidium/K10.lean` | **定理 K10 (a)** `K10a`：m % 64 = 7、m ≥ 71（m+1 = 8u、u ≡ 1 (mod 8)、u ≥ 9）なら `IsP m n 0 ↔ (n % (2m+3) = 0 ∨ n % (2m+3) = m+2)`。補題 `not_isP_near`、`k10_E_h`、`k10_O`、`k10_rows`。公理は `propext`・`Quot.sound` だけ。 |
| `Rubidium/K13.lean` | **定理 K13** `K13`：m % 8 = 7、{v2(9u+1), v2(11u+1)} = {1, 3}（u = (m+1)/8）なら `IsP m n 0 ↔ n % (3m+4) ∈ {0, m+2, 2m+3}`（100 型）。補題 `not_isP_move`、`p_four`（D = 4z の (a+D, D) は P）、`p_two`（(b+2z, 2z) は P）、`k13_step`、`k13_rows`。公理は `propext`・`Quot.sound` だけ。 |
| `Rubidium/K12.lean` | **定理 K12 (a)** `K12a`：m % 4 = 1、m ≥ 5、v2(3h+1) = 2、Q = (11h+5)/8 が奇数なら `IsP m n 0 ↔ n % (3m+5) ∈ {0, m+2, 2m+4}`（110 型）。`k12_step`・`k12_rows`（h, w, Q を変数にして 1 次の関係で扱う）。公理は `propext`・`Quot.sound` だけ。 |
| `Rubidium/K10c.lean` | 交互型 `Alt m` の定義。**定理 K10c** `K10c`：m+1 = 8u（u 奇数、u ≥ 3）で交互型なら v2(9u+1) は奇数・v2(11u+1) は偶数。**系 K10 (b)** `K10b`：u ≡ 3, 7 (mod 8) なら交互型でない。補題 `blk1_even`・`blk1_odd`（行 m+2 のブロックの所属）。公理は `propext`・`Classical.choice`・`Quot.sound`。 |
| `Rubidium/K11.lean` | **定理 K11** `K11`：m+1 = 2^v·u（v ≥ 5 奇数、u 奇数）なら `¬ Alt m`。行 m+2 のブロックの一般の補題 `g_even`・`g_odd`、偶数の規則のくり返し `g_iter`（指数 i の帰納法）、行 2m+3 の `g_blk2_even`。公理は `propext`・`Classical.choice`・`Quot.sound`。 |
| `Rubidium/K11.lean`（追加） | `not_alt_seven`：m = 7 は交互型でない。**定理 K10c（完全な形）** `K10c_full`：m+1 = 8u（u 奇数）で交互型なら u ≥ 3、v2(9u+1) 奇数、v2(11u+1) 偶数。 |
| `Rubidium/K7.lean` | **定理 K7′**（周期性）`K7'`：すべての m で `∃ N₀ T, 0 < T ∧ ∀ r ≥ N₀, ∀ p, (IsP m (r+T) p ↔ IsP m r p)`。窓（直前の m 行）の一致から先が決まる `window_step`・`window_all`、鳩の巣原理 `pigeon`、窓の 2 進の符号 `enc`・`win`。公理は `propext`・`Classical.choice`・`Quot.sound`。 |
| `Rubidium/K29.lean` | **定理 K29.2** `K29_v5`：m % 128 = 31（v2(m+1) = 5、u ≡ 1 (mod 4)）なら `IsP m n 0 ↔ n % (3m+4) ∈ {0, m+2, 2m+3}`（100 型）。汎用の補題 `p_oddb`（O 型のブロックの奇数）、`e_even`（E 型のブロックの偶数）。公理は `propext`・`Classical.choice`・`Quot.sound`。 |
| `Rubidium/K38.lean` | **定理 K38（v = 5）** `K38_v5`：m % 512 = 223 または m % 2048 = 2015 なら `IsP m n 0 ↔ n % (4m+5) ∈ {0, m+2, 2m+3, 3m+4}`（1000 型）。補題 `blk1_direct`（Blk m 1）、`blk_step2`（Blk の範囲を E 型のブロックごとに伸ばす）、`blk_zero`。公理は `propext`・`Classical.choice`・`Quot.sound`。 |
| `Rubidium/K38v7.lean` | **定理 K38（v = 7）** `K38_v7`：m+1 = 128u で u ≡ 7 (mod 16)、31 (mod 64)、255 (mod 256) のどれかなら `IsP m n 0 ↔ n % (5m+6) ∈ {0, m+2, 2m+3, 3m+4, 4m+5}`（10000 型）。公理は `propext`・`Classical.choice`・`Quot.sound`。 |
| `Rubidium/K38gen.lean` | **定理 K38（すべての奇数 v ≥ 5）** `K38_gen`：m+1 = 2^v·u、u ≡ 3 (mod 4)、v2((m+2+u)/2) が偶数で v−1 以下なら、型は 1 0^{(v+1)/2}。O 型のブロックの `o_half`・`o_iter`、E 型の `e_iff`、補題 Inh′ の 1 段 `k38_istep`（b の強い帰納法）、3H/2 の `k38_K`・`k38_N`、ブロックについての帰納法 `k38g_step`。公理は `propext`・`Classical.choice`・`Quot.sound`。 |
| `Rubidium/K38w.lean` | **定理 K38（もとの形）** `K38`：v ≥ 5 奇数、m+1 = 2^v·u、u ≡ 3 (mod 4)、w = v2(u+1) が奇数で 3 ≤ w ≤ v−2 または w ≥ v+1 なら、型は 1 0^{(v+1)/2}。仮定の書き換え `k38_hyp`、`v2_decomp`（x = 2^{v2 x}·奇数）。 |
| `Rubidium/K29gen.lean` | **定理 K29（すべての奇数 v ≥ 5）** `K29_gen`：m+1 = 2^v·u、u ≡ 1 (mod 4) なら型は 1 0^{(v−1)/2}（u = 1 を含む）。行 b の `k29_S0`（よい q：q ≡ 1 (mod 4) か qu ≡ 3 (mod 8)）、Inh の 1 段 `k29_istep`、`k29_eD`、ブロックの帰納法 `k29g_step`。公理は `propext`・`Classical.choice`・`Quot.sound`。 |
| `Rubidium/Decide.lean` | 計算できる判定 `isPb m r p : Bool`（`Nat.all` による再帰）と、`isPb_iff`：`isPb m r p = true ↔ IsP m r p`。 |
| `check/PStarts.lean` | `isPb` を実行して、m ≤ 10 の後手必勝の開始局面 (n, 0)（n ≤ 24）を出すスクリプト。出力は `data/lean_pstarts.txt`、JavaScript の全探索との照合は `data/lean_crosscheck.txt`。 |
| `check/Tables.lean` | Array による DP で全局面 (r, p) の勝敗表を出すスクリプト（証明はない、別言語の実装による照合用）。出力は `data/lean_tables.txt`、`data/tables` との照合は `data/lean_tables_compare.txt`。 |
| `check/TableSummary.lean` | `check/Tables.lean` と同じ DP で、m ごとの要約（P 局面の数・チェックサム・最初の P の開始局面）を出すスクリプト（m ≤ 100、r ≤ 3000）。照合は `data/table_summary_compare.txt`。 |
| `Rubidium/K5.lean` | 定理 K4 の一部 `K4_first`：(m+1, 0) が P ⇔ v2(m+1) が偶数。定理 K5：m ≥ 2 で v2(m+1) が奇数なら (m+2, 0) は P、1 ≤ n ≤ m+1 の (n, 0) は N（`K5_before`）。 |

`IsP` は PROBLEM.md の定義どおり、「1 ≤ k ≤ m、k ≤ r、k ≠ p のどの手 k で移った先 (r − k, k) も P 局面でない」として、r についての整礎な再帰で定めている。
