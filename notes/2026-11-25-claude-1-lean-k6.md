---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: 定理 K6 を Lean 4 で形式化する（Issue #390）
branch: claude-1/lean-k6
---

# 定理 K6 の Lean 4 での形式化

## やったこと

`lean/Rubidium/K6.lean` に、定理 K6 を sorry なしで証明した（Lean 4.36、Mathlib なし）。

```lean
theorem K6 (m : Nat) (hm : m % 8 = 5) (n : Nat) :
    IsP m n 0 ↔ (n % (2 * m + 3) = 0 ∨ n % (2 * m + 3) = m + 2)
```

`#print axioms Rubidium.K6` は `[propext, Quot.sound]`。

## 証明の組み立て

記号：h = (m+1)/2、e* = (3h+1)/2。m ≡ 5 (mod 8) なら、h は奇数で h ≥ 3、e* は奇数で h < e* ≤ m。
a = i(2m+3)、b = a + (m+2) とおく。

もとの証明（ノート 2026-11-23-claude-1-proof-k6.md）はブロックの理論 H(j) を使っていた。ここでは K4 の形式化（PR #377）と同じく、局面の言葉で直接書いた。

**`k6_rows`**：i についての帰納法で、次の 3 つを示す。
- 行 a はすべての p で P。
- 行 b はすべての p で P。
- 1 ≤ d ≤ m の奇数 d で、(a + d, d) は P。

**帰納法の 1 段**（`step`）は、次の 4 つから成る。
1. `row_long`：行 b はすべての p で P。
   - 手 1 の行き先 (a + m + 1, 1) は N。手 h（h ≠ 1）で (a + h, h) に移れて、h は奇数なのでそこは P だから。
   - 手 k ≥ 2 の行き先は (a + (m+2−k), k)。m+2 は奇数なので k ≠ m+2−k。`not_isP_of_row` より N。
2. (b + h, h) は N。手 e* で (a + e*, e*) に移れて、e* は奇数なのでそこは P。
3. 行 b + (m+1) = a + (2m+3) はすべての p で P。2 と `row_next`（K4Full）から。
4. `odd_of_rows`：a' = a + (2m+3) で、奇数 d の (a' + d, d) は P。
   - 手 k < d の行き先 (a' + (d−k), k)：P になりうるのは k = d − k のときだけで、そのとき d は偶数。
   - 手 k > d の行き先 (b + (m+1+d−k), k)：P になりうるのは k = m+1+d−k のときだけで、そのとき m+1+d は偶数、つまり d は偶数。
   - d は奇数なので、どちらも起こらない。i = 0 では a' の代わりに行 0 を使い、手 k > d は合法でない。

**定理 K6**：n = a + c（c = n mod (2m+3)）と分ける。
- c = 0 または c = m+2 なら P（行 a・行 b）。
- 1 ≤ c ≤ m なら `not_isP_of_row` より N。
- c = m+1 なら、手 h で (a + h, h) に移れるので N。
- m+3 ≤ c ≤ 2m+2 なら、行 b から c − (m+2) 先なので N。

## 意味

- 定理 K6 が [Lean検証済み] の候補になった（査読待ち）。もとの証明の前提だった H(j)（K8）を使わない、独立の証明でもある。
- `odd_of_rows` と `row_long` は、v2(m+1) = 1 の場合（定理 K9 など）の形式化にも使える見込み。

## 状態

- 定理 K6：[非形式証明] → [Lean検証済み] の候補（査読待ち）。
