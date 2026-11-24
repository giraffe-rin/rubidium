---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: 定理 K10c と系 K10 (b) を Lean 4 で形式化する（Issue #405）
branch: claude-1/lean-k10c
---

# 定理 K10c と系 K10 (b) の Lean 4 での形式化

## やったこと

`lean/Rubidium/K10c.lean` に、次を sorry なしで証明した。

```lean
def Alt (m : Nat) : Prop := ∀ n, IsP m n 0 ↔ (n % (2m+3) = 0 ∨ n % (2m+3) = m+2)
theorem K10c (m u) (hmu : m + 1 = 8u) (hu : u % 2 = 1) (hu3 : 3 ≤ u) (halt : Alt m) :
    v2 (9u+1) % 2 = 1 ∧ v2 (11u+1) % 2 = 0
theorem K10b (m u) (hmu : m + 1 = 8u) (hu8 : u % 8 = 3 ∨ u % 8 = 7) : ¬ Alt m
```

公理は `[propext, Classical.choice, Quot.sound]`。`Classical.choice` は `simp` から入った。`sorryAx` はない。

## 証明の組み立て

h = 4u、b = m+2、c = 2m+3、X₁ = (9u+1)/2、X₃ = (11u+1)/2 とおく。もとの証明（ノート 2026-11-23-claude-1-proof-k10c-k11.md）の補題 O・E2 を、局面の言葉で直接示した。

- 行 b はすべての p で P。`row_long` を a = 0 に使う。(h, h) は K3 より P（v2(4u) = 2）。
- **`blk1_even`**：偶数 d（d + 1 ≠ h）について、(b + d, d) が P ⇔ (b + d/2, d/2) が N。
  - 手 k < d：P になりうるのは k = d/2 だけ。
  - 手 d + 1：行き先 (m+1, d+1) は N（手 h で (h, h) に移れる）。
  - 手 k ≥ d + 2：行き先は K3 の範囲で、P になるには 2k = m+2+d（奇数）が必要なので N。
- **`blk1_odd`**：奇数 d（d + 1 ≠ h、X = (m+2+d)/2 ≤ m）について、(b + d, d) が P ⇔ ev2(X) = false。
  P になりうる行き先は、手 X の行き先 (X, X) だけ（K3）。
- **`k10c_X1`**：ev2(X₁) = false なら、交互型でない。
  - (b + u, u) は P、(b + 2u, 2u) は N、(b + h, h) は P。
  - よって (2m+3, 0) から手 h で (b + h, h) に移れるので、(2m+3, 0) は N。交互型なら P のはずなので矛盾。
- **`k10c_X3`**：ev2(X₁) = true かつ ev2(X₃) = true なら、交互型でない。
  - (b + h, h) は N。よって行 c はすべての p で P（`row_next`）。
  - (b + 3u, 3u) は N、(b + 6u, 6u) は P。(c + h, h) は N（手 6u で (b + 6u, 6u) に移れる）。
  - よって行 c + (m+1) = 3m+4 はすべての p で P。とくに (3m+4, 0) は P。
  - 一方、3m+4 ≡ m+1 (mod 2m+3) なので、交互型なら N のはず。矛盾。
- **K10c**：交互型なら、ev2(X₁) = true かつ ev2(X₃) = false。v2(9u+1) = v2(X₁) + 1 などで書き直す。
- **K10b**：u ≡ 3 (mod 8) なら v2(9u+1) = 2（偶数）、u ≡ 7 (mod 8) なら v2(11u+1) = 1（奇数）。どちらも K10c に反する。

もとの証明は u ≥ 3 を「3u ≠ h − 1」（(iii) の対象）のために使っていた。ここでは、`blk1_odd` を d = 3u に使うときの条件 d + 1 ≠ h のために使っている。
u = 1（m = 7）が交互型でないこと（もとの (c)）は、この PR には入れていない。

## 状態

- 定理 K10c（u ≥ 3 の部分）・系 K10 (b)：[非形式証明] → [Lean検証済み] の候補（査読待ち）。
- 次の候補：定理 K11（v2(m+1) ≥ 5 の奇数なら交互型でない）。2^{v−1} の形の距離を、指数についての帰納法で扱う必要がある。
