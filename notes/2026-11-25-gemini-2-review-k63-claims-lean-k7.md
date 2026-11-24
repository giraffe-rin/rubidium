---
agent: gemini-2
date: 2026-11-25
problem: restricted-stone-game
task: PR #414（予想 K63）・PR #415（claims 追加）・PR #418（Lean 4 定理 K7′）の独立査読と検証
branch: gemini-2/review-k63-claims-lean
---

# 独立査読・検証ログ：Lean 4 定理 K7′（PR #418）・予想 K63（PR #414）・claims 同期（PR #415）

## 取りかかったタスク

以下の 3 件の未査読 PR を担当宣言のうえ独立に査読・検証した。

1. **PR #418**（`claude-1/lean-k7`, コミット `06e2991`）：Lean 4 定理 K7′（すべての `m` で全局面の勝敗表が周期的）
2. **PR #414**（`claude-1/k63-alt3`, コミット `fa3ca1a`）：予想 K63（`v2(m+1) = 3, v2(11u+1) ≥ 4` 偶数、`u ≤ 20000`）
3. **PR #415**（`claude-1/claims-lean-k6-k13`, コミット `b092272`）：査読済み 4 定理（`K6, K9, K10a, K13`）の `claims/*.yaml` 追加

---

## 1. PR #418（Lean 4 定理 K7′）の独立検証

分離 worktree にコミット `06e2991` をチェックアウトし、ローカルの **Lean 4.36.0** で検証した。

- `lake build Rubidium.K7`：**7/7 ジョブ成功（1.6s）**、全体 `lake build`：**32/32 ジョブ成功（終了コード 0）**。
- 全 `.lean` ファイルの禁止語検索（`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`）：**0 件**。
- `Game.lean`・`Decide.lean` ほか既証明モジュールへの改変なし。
- `#print axioms`：
  - `Rubidium.K7'` / `Rubidium.pigeon` / `Rubidium.enc_inj`：`[propext, Classical.choice, Quot.sound]`
  - `Rubidium.window_all` / `Rubidium.window_step` / `Rubidium.isP_big` / `Rubidium.win_eq`：`[propext, Quot.sound]`
- 主張の忠実性：`theorem K7' (m : Nat) : ∃ N₀ T, 0 < T ∧ ∀ r, N₀ ≤ r → ∀ p, (IsP m (r + T) p ↔ IsP m r p)` は、K8（H(j)）に依存せず、`m = 0` および `p > m` を含む全局面について最終的周期性を無条件に証明している。
- 判定：**定理 K7′ を `[Lean検証済み]` に昇格**（`claims/K7p.yaml`）。

---

## 2. PR #414（予想 K63）の独立 Python 3 直接 DP 検証

`code/gemini2_verify_k63.py`（出力：`data/gemini2_verify_k63.txt`）により、`PROBLEM.md` の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）で `u ≤ 20000`（`m ≤ 159,999`）の **全 835 ケース**を独立再計算した（実行時間 79.82s）。

- 対象 `u` 網羅性：**835/835** 一致。
- `data/k63_check_dp.txt`（`u ≤ 1200`）：判定および最初に外れる `n` が **52/52 完全一致**。
- `data/k63_alt3.txt`（`u ≤ 20000`, R による判定）との照合：**不一致 0 件（835/835 一致）**、全 11 類の集計値（`313/313`, `116/312`, `12/79`, `0/78`, `3/19`, `0/20`, `1/5`, `0/5`, `0/1`, `0/2`, `0/1`）も完全一致。
- ノート追記の観察検証：
  - `u = 77`（`m = 615, 4Y = 212`）：偶数ブロック `i = 0..7`（`a_i = i(2m+3)`）で `(a_i + 4Y, 4Y) ∈ P` が `i = 1` のみ `False`（他は `True`）であることを確認。
  - `(2)` `e ≥ 3, Y ≡ 3 (mod 4)` の **全 105 ケース（105/105）** すべてで最初に交互から外れる `n` が `2(2m+3) + (m+1) = 5m + 7` であることを新たに全件確認した。
- 分離 worktree で `uv run python code/generate_status.py --check` 通過（終了コード 0）。ラベル `[予想]` 維持。

---

## 3. PR #415（`claims/K6, K9, K10a, K13` 追加）の監査

- 収録 4 件がすべて査読者（`K6, K9, K10a`: `gemini-2`、`K13`: `antigravity-1`）の既判定に忠実であり、自己昇格がないことを確認。
- 分離 worktree で `uv run python code/generate_status.py --check` および `node code/generate_status.js --check` がともに終了コード 0 で通過。

---

## ラベル更新（`claims/*.yaml`）

- `claims/K7p.yaml`（`id: "K7'"`）：**`[Lean検証済み]`**（`lean/Rubidium/K7.lean (Rubidium.K7')`）
