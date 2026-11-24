---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: 定理 K4 全体を Lean 4 で形式化する（Issue #376）
branch: claude-1/lean-k4-full
---

# 定理 K4 全体の Lean 4 での形式化

## やったこと

`lean/Rubidium/K4Full.lean` に、定理 K4 全体を sorry なしで証明した（Lean 4.36、Mathlib なし）。

```lean
theorem K4 (m : Nat) (hm : 1 ≤ m) :
    (∀ n, IsP m n 0 ↔ n % (m + 1) = 0) ↔ ev2 (m + 1) = true
```

`#print axioms Rubidium.K4` は `[propext, Quot.sound]`（`Classical.choice` も `sorryAx` も使わない）。

## 証明の組み立て

- **⇒**：n = m+1 とおくと、(m+1, 0) が P なので `K4_first`（PR #367）より v2(m+1) が偶数。
- **⇐、m が偶数**：`K4_even`（PR #375）。
- **⇐、m が奇数**：h = (m+1)/2、s = v2(h)。v2(m+1) = s + 1 が偶数なので s は奇数。
  各行 r = j(m+1) について、次の 2 つを j の帰納法で同時に示す（`row_all_odd`）。
  - Row r：すべての p で (r, p) は P。
  - Blk r：1 ≤ d ≤ m、v2(d) ≤ s なら、(r + d, d) が P ⇔ v2(d) が偶数。

  **Blk r の証明**（`blk_step`）。d についての強い帰納法。
  - v2(d) が奇数のとき：手 d/2 で (r + d/2, d/2) に移れる。v2(d/2) は偶数なので、帰納法の仮定よりそこは P。よって (r + d, d) は N。
  - v2(d) が偶数のとき：どの手 k（1 ≤ k ≤ m、k ≠ d）の行き先も N であることを示す。
    - k < d の場合：行き先は (r + (d−k), k)。`not_isP_of_row`（Row r）より、P になりうるのは k = d − k のときだけ。そのとき d = 2k で、v2(k) = v2(d) − 1 は奇数なので、帰納法の仮定より N。
    - k > d の場合：r = 0 なら合法手でない（k ≤ r + d）。r = r' + (m+1) なら、行き先は (r' + (m+1+d−k), k)。Row r' より、P になりうるのは k = m+1+d−k のときだけ。そのとき d は偶数で、k = h + d/2。v2(d/2) = v2(d) − 1 ≤ s − 1 < v2(h) なので、`v2_add` より v2(k) = v2(d/2) は奇数。よって Blk r' より N。

  **次の行**（`row_next`）。h は v2(h) = s が奇数なので、Blk r より (r + h, h) は N。行 r + (m+1) から手 k で移った先は (r + (m+1−k), k)。これが P になりうるのは k = h のときだけで、そこは N。よって Row (r + (m+1))。
- 最後に、n = j(m+1) + d と分けて、`K4_even` と同じように `K4_odd` を得る。

v2 については、`v2 : Nat → Nat` を定め、次を証明した。
- `v2_odd`、`v2_even`、`even_of_v2_pos`
- `ev2_iff_v2`：ev2 n = true ⇔ v2 n が偶数
- `v2_add`：v2 x < v2 y なら v2(x+y) = v2 x

## 意味

- 定理 K4 が [Lean検証済み] の候補になった（査読待ち）。これで、K3・K4・K5 の 3 つがそろって Lean で確かめられたことになる。
- 証明は、ノート 2026-11-23-claude-1-proof-k4.md の主張 Q(j)（Q1・Q2）を、ブロックの理論 H(j) を経由せずに、局面の言葉で直接書き直したもの。H(j) のうち使ったのは「P の行から d 先の局面は p = d のときしか P になりえない」（`not_isP_of_row`）だけ。

## 状態

- 定理 K4：[査読済み] → [Lean検証済み] の候補（このログと PR の査読待ち）。
