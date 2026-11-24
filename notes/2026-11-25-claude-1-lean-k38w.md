---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: 定理 K38 の仮定を w の形で Lean 4 に入れる（Issue #430）
branch: claude-1/lean-k38w
---

# 定理 K38（もとの形）の Lean 4 での形式化

## やったこと

PR #429 の `K38_gen` は、仮定を e₁ = (m+2+u)/2 の付値で書いていた。もとの仮定（w = v2(u+1) の条件）からその仮定が出ることを、Lean で示した（`lean/Rubidium/K38w.lean`、sorry なし）。

```lean
theorem K38 (m v u : Nat) (hv5 : 5 ≤ v) (hvo : v % 2 = 1) (hmu : m + 1 = 2 ^ v * u) (hu : u % 4 = 3)
    (hw : (v2 (u+1) % 2 = 1 ∧ 3 ≤ v2 (u+1) ∧ v2 (u+1) ≤ v - 2) ∨ v + 1 ≤ v2 (u+1)) (n : Nat) :
    IsP m n 0 ↔ (n % L = 0 ∨ (m + 2 ≤ n % L ∧ (n % L - (m + 2)) % (m + 1) = 0))   -- L = (m+2) + ((v+1)/2)(m+1)
```

公理は `[propext, Classical.choice, Quot.sound]`。

## 証明

- `v2_decomp`：x ≥ 1 なら、x = 2^{v2 x}·t（t は奇数）。強い帰納法で示す。
- `k38_hyp`：u + 1 = 2^w·t（t は奇数）と書くと、m + 2 + u = 2^v·u + 2^w·t。
  - w ≤ v − 2 のとき：m + 2 + u = 2^w·(2^{v−w}·u + t) で、括弧の中は奇数。よって v2(m+2+u) = w で、v2(e₁) = w − 1。w は奇数なので、これは偶数で v − 1 以下。
  - w ≥ v + 1 のとき：m + 2 + u = 2^v·(u + 2^{w−v}·t) で、括弧の中は奇数。よって v2(e₁) = v − 1 で、これも偶数。
- `K38` は `K38_gen` と `k38_hyp` を合わせたもの。

PR #429 で「数で確かめた」と書いた仮定の同値のうち、定理に必要な向き（w の条件 ⇒ e₁ の条件）が、これで Lean で示された。

## 状態

- 定理 K38（もとの形、すべての奇数 v ≥ 5）：[非形式証明] → [Lean検証済み] の候補（査読待ち）。
