---
agent: gemini-2
date: 2026-11-25
problem: restricted-stone-game
task: PR #420（Lean 4 定理 K29.2：`Rubidium.K29_v5`）の独立査読と検証
branch: gemini-2/review-lean-k29-v5
---

# 独立査読・検証ログ：Lean 4 定理 K29.2（PR #420）

## 対象
- **PR #420**（`claude-1/lean-k29`, コミット `8ac13f3`, Issue #419）：`lean/Rubidium/K29.lean`

## 独立検証結果
1. **ローカル Lean 4.36.0 ビルド検証**（分離 worktree でクリーンビルド）：
   - `lake build Rubidium.K29`：**27/27 ジョブ成功**（`K29.lean` 単体 8.0s）、全体 `lake build`：**34/34 ジョブ成功（終了コード 0）**。
   - 全 `.lean` ファイル禁止語検索（`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`）：**0 件**。
   - `Game.lean` ほか既証明モジュールへの改変なし。
   - `#print axioms`：
     - `Rubidium.K29_v5` / `Rubidium.k29_rows` / `Rubidium.k29_step`：`[propext, Classical.choice, Quot.sound]`
     - `Rubidium.p_oddb` / `Rubidium.e_even`：`[propext, Quot.sound]`
2. **主張の忠実性および数学的監査**：
   - 定理型 `Rubidium.K29_v5 : ∀ (m : Nat), m % 128 = 31 → ∀ (n : Nat), Rubidium.IsP m n 0 ↔ n % (3 * m + 4) = 0 ∨ n % (3 * m + 4) = m + 2 ∨ n % (3 * m + 4) = 2 * m + 3` は定理 K29.2 の条件 `m + 1 = 32u, u ≡ 1 (mod 4)`（`u = 1` の `m = 31` を含む）と厳密に同値。
   - H(j)（K8）を使わず、汎用補題 `p_oddb`・`e_even` と `u mod 8` による (★) の統一的扱いにより局面の言葉で直接帰納法を完結させている。
3. **独立 Python 3 直接 DP クロスチェック**：
   - `PROBLEM.md` の定義のみに基づく O(N) 厳密 DP で、`m % 128 = 31, m ≤ 2000` の全 **16 ケース**（`m = 31 .. 1951`）について `0 ≤ n ≤ 6(3m+4) + 10` で 100 型と **16/16 完全一致**を確認。

## 判定・ラベル更新
- `claims/K29_2.yaml`（`id: K29.2`）：**`[Lean検証済み]`**（`lean/Rubidium/K29.lean (Rubidium.K29_v5)`）
