---
agent: gemini-2
date: 2026-11-25
problem: restricted-stone-game
task: PR #424（Lean 4 定理 K38 v=5）・PR #426（Lean 4 定理 K38 v=7）の独立査読と検証
branch: gemini-2/review-lean-k38
---

# 独立査読・検証ログ：Lean 4 定理 K38（v = 5・v = 7）（PR #424・PR #426）

## 対象
1. **PR #424**（`claude-1/lean-k38`, コミット `d2aec60`, Issue #423）：`lean/Rubidium/K38.lean`（`Rubidium.K38_v5`）
2. **PR #426**（`claude-1/lean-k38v7`, コミット `184470c`, Issue #425）：`lean/Rubidium/K38v7.lean`（`Rubidium.K38_v7`）

## 独立検証結果
### 1. ローカル Lean 4.36.0 ビルドおよび公理検査（分離 worktree クリーンビルド）
| PR | コミット | `lake build` | 禁止語 | 検証定理と `#print axioms` | 判定 |
|---|---|---|---|---|---|
| **#424** | `d2aec60` | 36/36 成功（`K38` 8.6s） | 0 件 | `Rubidium.K38_v5`, `k38_rows`, `k38_step`, `blk1_direct` → `[propext, Classical.choice, Quot.sound]`; `blk_step2`, `blk_zero` → `[propext, Quot.sound]` | **`[Lean検証済み]`** |
| **#426** | `184470c` | 38/38 成功（`K38v7` 10s） | 0 件 | `Rubidium.K38_v7` → `[propext, Classical.choice, Quot.sound]` | **`[Lean検証済み]`** |

- 全 `.lean` ファイルの禁止語検索（`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`）：0 件。
- `Game.lean` ほか既証明モジュールへの改変なし。

### 2. 主張の忠実性・数学的監査
- **PR #424（`K38_v5`）**：`m % 512 = 223 ∨ m % 2048 = 2015` は `m + 1 = 32u` かつ `w = v2(u+1) = 3` または `w ≥ 6` と厳密に同値であり、定理 K38 の `v = 5` の全条件（`w` 奇数 `3 ≤ w ≤ v - 2` または `w ≥ v + 1`）を忠実に形式化している。
- **PR #426（`K38_v7`）**：`(m + 1) % 128 = 0` かつ `u % 16 = 7 ∨ u % 64 = 31 ∨ u % 256 = 255`（`u = (m+1)/128`）は `v2(m+1) = 7` かつ `w = v2(u+1) ∈ {3, 5}` または `w ≥ 8` と厳密に同値であり、定理 K38 の `v = 7` の全条件を忠実に形式化している。
- いずれも H(j)（K8）を使わず、`blk_step2` による E 型ブロックでの `Blk` 拡張と O 型ブロックの半減鎖のみで局面の言葉から直接完結している。

### 3. 独立 Python 3 直接 DP クロスチェック（漸化式 R / K8 不使用）
- **`K38_v5`**（`m ≤ 10000`）：該当全 **24/24 ケース**（`m = 223 .. 9951`）で `0 ≤ n ≤ 4(4m+5) + 10` において 1000 型と完全一致。
- **`K38_v7`**（`m ≤ 40000`）：`w ≥ 8` 枝の `u = 255`（`m = 32639`）を含む該当全 **26/26 ケース**（`m = 895 .. 39807`）で `0 ≤ n ≤ 3(5m+6) + 10` において 10000 型と完全一致。

## ラベル更新（`claims/*.yaml`）
- `claims/K38_v5.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K38.lean (Rubidium.K38_v5)`）
- `claims/K38_v7.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K38v7.lean (Rubidium.K38_v7)`）
