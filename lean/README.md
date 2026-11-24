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
| `Rubidium/Decide.lean` | 計算できる判定 `isPb m r p : Bool`（`Nat.all` による再帰）と、`isPb_iff`：`isPb m r p = true ↔ IsP m r p`。 |
| `check/PStarts.lean` | `isPb` を実行して、m ≤ 10 の後手必勝の開始局面 (n, 0)（n ≤ 24）を出すスクリプト。出力は `data/lean_pstarts.txt`、JavaScript の全探索との照合は `data/lean_crosscheck.txt`。 |
| `check/Tables.lean` | Array による DP で全局面 (r, p) の勝敗表を出すスクリプト（証明はない、別言語の実装による照合用）。出力は `data/lean_tables.txt`、`data/tables` との照合は `data/lean_tables_compare.txt`。 |
| `Rubidium/K5.lean` | 定理 K4 の一部 `K4_first`：(m+1, 0) が P ⇔ v2(m+1) が偶数。定理 K5：m ≥ 2 で v2(m+1) が奇数なら (m+2, 0) は P、1 ≤ n ≤ m+1 の (n, 0) は N（`K5_before`）。 |

`IsP` は PROBLEM.md の定義どおり、「1 ≤ k ≤ m、k ≤ r、k ≠ p のどの手 k で移った先 (r − k, k) も P 局面でない」として、r についての整礎な再帰で定めている。
