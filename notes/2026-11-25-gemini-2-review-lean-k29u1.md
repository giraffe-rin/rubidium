---
agent: gemini-2
date: 2026-11-25
problem: restricted-stone-game
task: PR #437（Lean 4 定理 K29_gen の u ≥ 5 仮定除去・m = 2^v - 1 含む完全版および被覆率更新）の独立査読と検証
branch: gemini-2/review-lean-k29u1
---

# 独立査読・検証ログ：Lean 4 定理 K29 完全版（u = 1 含む）（PR #437）

## 対象
- **PR #437**（`claude-1/lean-k29u1`, コミット `4a5e017`, Issue #436）：`lean/Rubidium/K29gen.lean`（`Rubidium.K29_gen`）・`code/lean_coverage.js`・`data/lean_coverage.txt`

## 独立検証結果
1. **ローカル Lean 4.36.0 ビルドおよび公理検査**（分離 worktree クリーンビルド）：
   - `lake build`：**44/44 ジョブ成功（終了コード 0）**（`Rubidium.K29gen` 単体 11s）。
   - 全 `.lean` ファイル禁止語検索（`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`）：**0 件**。
   - `Game.lean` ほか既証明モジュールへの改変なし。
   - `#print axioms Rubidium.K29_gen`：`[propext, Classical.choice, Quot.sound]`（標準古典公理のみ、`sorryAx` なし）。
   - 定理型から `5 ≤ u` が完全に外れ、すべての奇数 `v ≥ 5` とすべての `u ≡ 1 (mod 4)`（`u = 1` すなわち `m = 2^v - 1` を含む）に対して型 `1 0^{(v-1)/2}` が証明されたことを確認。
2. **独立 Python 3 直接 DP クロスチェックおよび被覆率更新検証**：
   - `m = 2^v - 1`（`u = 1`）について `v = 5, 7, 9, 11, 13, 15`（`m = 31, 127, 511, 2047, 8191, 32767`）の **6/6 件**すべてで `0 ≤ n ≤ 2L + 10` において型 `1 0^{(v-1)/2}` と完全一致。
   - 更新版 `data/lean_coverage.txt` を Python 整数演算で `1 ≤ m ≤ 1,000,000` 全数再計算し、全行一致・合計 **909,546 / 1,000,000（90.95%）**・`K29_gen = 10,419`（`v = 5..19` の `u = 1` 8 件増加、うち `v = 7..19` の 7 件が新規被覆）を確認。

## ラベル更新
- `claims/K29.yaml`（`id: K29`）：完全版（`u = 1` 含む）として **`[Lean検証済み]`**（`lean/Rubidium/K29gen.lean (Rubidium.K29_gen)`）
