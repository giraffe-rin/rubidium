---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: 定理 K4 の m が偶数の場合を Lean 4 で形式化する（Issue #374）
branch: claude-1/lean-k4-even
---

# 定理 K4 の m が偶数の場合の Lean 4 での形式化

## やったこと

`lean/Rubidium/K4Even.lean` に、次の 3 つを sorry なしで証明した（Lean 4.36、Mathlib なし）。
公理は 3 つとも `propext`・`Quot.sound` だけ（`Decidable.byContradiction` を使い、`Classical.choice` を避けた）。

- `not_isP_of_row m r d p`：行 r がすべての p' で P 局面なら、1 ≤ d ≤ m、p ≠ d の (r + d, p) は N 局面。
  理由：手 d（d ≠ p、d ≤ m、d ≤ r + d）で (r, d) に移れて、そこは P。
- `row_all m (hm : m % 2 = 0)`：すべての j, p で (j(m+1), p) は P 局面。
  j についての帰納法。((j+1)(m+1), p) からの手 k（1 ≤ k ≤ m）の行き先は (j(m+1) + (m+1−k), k)。
  `not_isP_of_row` より、これが P になりうるのは k = m+1−k のときだけで、それは m+1 = 2k を意味するが、m が偶数なので m+1 は奇数。よってどの手も N 局面に移り、((j+1)(m+1), p) は P。
- `K4_even m (hm : m % 2 = 0) n`：`IsP m n 0 ↔ n % (m+1) = 0`。
  n = j(m+1) + d（d = n mod (m+1)）。d = 0 なら `row_all`。d ≥ 1 なら `not_isP_of_row`（p = 0 ≠ d）。

## 意味

- 定理 K4（m ≥ 2 で「すべての n で (n, 0) が P ⇔ (m+1) | n」⇔ v2(m+1) が偶数）の、m が偶数の場合の「⇐」が Lean で確かめられた。
  m = 0（手がない）も含めて成り立つ形になっている。
- この直接の証明は、ブロックの理論（H(j)）を使わない。m が奇数の場合は、h = (m+1)/2 の手 (r + h, h) が P になりうるので、この議論だけでは足りない（そこが H(j) と v2 の議論の役目）。
- 次の候補：m が奇数で v2(m+1) が偶数の場合（K4 の残り）。`not_isP_of_row` はそのまま使え、残るのは「各ブロックで h が S_j に入らない」ことの帰納法。

## 状態

- `K4_even`：[Lean検証済み] の候補（査読待ち）。定理 K4 全体は [査読済み] のまま（奇数の m が残る）。
