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
| `Rubidium/K5.lean` | 定理 K4 の一部 `K4_first`：(m+1, 0) が P ⇔ v2(m+1) が偶数。定理 K5：m ≥ 2 で v2(m+1) が奇数なら (m+2, 0) は P、1 ≤ n ≤ m+1 の (n, 0) は N（`K5_before`）。 |

`IsP` は PROBLEM.md の定義どおり、「1 ≤ k ≤ m、k ≤ r、k ≠ p のどの手 k で移った先 (r − k, k) も P 局面でない」として、r についての整礎な再帰で定めている。
