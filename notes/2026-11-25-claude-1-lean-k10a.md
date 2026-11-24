---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: 定理 K10 (a) を Lean 4 で形式化する（Issue #396）
branch: claude-1/lean-k10a
---

# 定理 K10 (a) の Lean 4 での形式化

## やったこと

`lean/Rubidium/K10.lean` に、定理 K10 (a) を sorry なしで証明した（公理は `[propext, Quot.sound]`）。

```lean
theorem K10a (m : Nat) (hm : m % 64 = 7) (hm71 : 71 ≤ m) (n : Nat) :
    IsP m n 0 ↔ (n % (2 * m + 3) = 0 ∨ n % (2 * m + 3) = m + 2)
```

条件 m % 64 = 7、m ≥ 71 は、「m + 1 = 8u、u ≡ 1 (mod 8)、u ≥ 9」と同じ。

## 証明の組み立て

もとの証明（ノート 2026-11-23-claude-1-proof-k10a.md）が追っていた有限個の事実を、ブロックの理論 H(j) を使わずに局面の言葉で示した。
記号：h = 4u、e₁ = (9u+1)/2（奇数）、w = (11u+1)/2（u ≡ 1 (mod 8) より w/2 は奇数）。a = i(2m+3)、b = a + (m+2) とする。

- 新しい補題 **`not_isP_near`**：(a + h, h) が P なら、p ≠ h の (a + (m+1), p) は N（手 h で移れる）。
- **偶数番目のブロック a**（`k10_E_h`、`odd_of_rows`）：
  - 奇数 d の (a + d, d) は P（`odd_of_rows`）。
  - (a + h, h) は P。手 k < h の行き先が P になりうるのは k = 2u のときだけで、そこ (a + 2u, 2u) は手 u で P に移れるので N。
    手 k > h の行き先が P になりうるのは k = 6u のときだけで、(b' + 6u, 6u) は N（b' は 1 つ前の奇数番目のブロック）。
- **奇数番目のブロック b**（`k10_O`）：
  - (b + u, u) は N。手 e₁ で (a + e₁, e₁) に移れる（m + 2 + u = 2e₁）。
  - (b + 2u, 2u) は P。手 u の行き先 (b + u, u) は N。手 2u + 1 の行き先 (a + m + 1, 2u+1) は `not_isP_near` より N。そのほかの手は `not_isP_of_row` で N（2k = 10u + 1 は奇数なので起こらない）。
  - (b + 3u, 3u) は P。手 k < 3u は 3u が奇数なので N。手 3u + 1 は `not_isP_near` より N。手 w の行き先 (a + w, w) は、手 w/2 で P に移れるので N。そのほかの手は `not_isP_of_row` で N。
  - (b + 6u, 6u) は N（手 3u）。(b + h, h) は N（手 2u）。
- **`k10_rows`**：i についての帰納法。1 段は K6・K9 と同じ形で、`row_long` → `k10_O` → `row_next` → `odd_of_rows`・`k10_E_h` の順に使う。

## 意味

- 定理 K10 (a) が [Lean検証済み] の候補になった（査読待ち）。これで Lean にあるのは K3・K4・K5・K6・K9・K10 (a)。
- どれも H(j)（K8）を使わない。
- 「有限個の事実を追う」型の証明（K12・K13 など）も、同じやり方で Lean にできる見込み。

## 状態

- 定理 K10 (a)：[非形式証明] → [Lean検証済み] の候補（査読待ち）。
