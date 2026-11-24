---
agent: gemini-2
date: 2026-11-25
problem: restricted-stone-game
task: PR #429（Lean 4 定理 K38 一般の奇数 v ≥ 5：`Rubidium.K38_gen`）の独立査読と検証
branch: gemini-2/review-lean-k38gen
---

# 独立査読・検証ログ：Lean 4 定理 K38（すべての奇数 v ≥ 5）（PR #429）

## 対象
- **PR #429**（`claude-1/lean-k38gen`, コミット `d463f71`, Issue #427）：`lean/Rubidium/K38gen.lean`（`Rubidium.K38_gen`）

## 独立検証結果
1. **ローカル Lean 4.36.0 ビルドおよび公理検査**（分離 worktree クリーンビルド）：
   - `lake build`：**40/40 ジョブ成功（終了コード 0）**（`Rubidium.K38gen` 単体 14s）。
   - 全 `.lean` ファイル禁止語検索（`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`）：**0 件**。
   - `Game.lean` ほか既証明モジュールへの改変なし。
   - `#print axioms`：
     - `Rubidium.K38_gen` / `k38g_rows` / `k38g_step` / `k38_S0` / `k38_istep` / `o_iter`：`[propext, Classical.choice, Quot.sound]`
     - `Rubidium.k38_K` / `k38_N` / `e_iff` / `v2_pow_mul`：`[propext, Quot.sound]`
2. **仮定の厳密同値性（代数監査＋全数検査）**：
   - `m + 1 = 2^v u`（`v ≥ 5` 奇数、`u` 奇数）、`u + 1 = 2^w t`（`t` 奇数）より `m + 2 + u = 2^v u + 2^w t`、`e₁ = (m + 2 + u)/2`。
     - `w < v`：`v2(e₁) = w - 1` → 偶数かつ `≤ v - 1` ⇔ `w` 奇数かつ `3 ≤ w ≤ v - 2`（`u ≡ 3 mod 4` より `w ≥ 2`）。
     - `w > v`：`v2(e₁) = v - 1` → `v` 奇数より常に偶数かつ `≤ v - 1`。
     - `w = v`：`u + t` は偶数なので `v2(m + 2 + u) = v + v2(u + t) ≥ v + 1`、よって `v2(e₁) ≥ v > v - 1` となり正確に除外される。
   - したがって Lean 仮定 `u % 4 = 3 ∧ v2(e₁) % 2 = 0 ∧ v2(e₁) ≤ v - 1` は元の定理 K38 の仮定「`w` が奇数で `3 ≤ w ≤ v - 2` または `w ≥ v + 1`」とすべての奇数 `v ≥ 5`・奇数 `u` に対して厳密同値（Python で `5 ≤ v ≤ 19` 奇数・全奇数 `u < 2^16` の **262,144/262,144** 一致も確認）。
3. **独立 Python 3 直接 DP クロスチェック**（漸化式 R / K8 不使用）：
   - `v = 5, 7, 9, 11, 13` の各奇数 `w ≤ v - 2` および `w = v + 1` 枝（最大 `m = 523,775`）の **23/23 ケース**すべてで `0 ≤ n ≤ 2L + 10` において型 `1 0^{(v+1)/2}` と完全一致。

## ラベル更新
- `claims/K38.yaml`（`id: K38`）：**`[Lean検証済み]`**（`lean/Rubidium/K38gen.lean (Rubidium.K38_gen)`）
