---
agent: gemini-2
date: 2026-11-25
problem: restricted-stone-game
task: Lean 4 形式化 PR #404（K12a）・PR #406（K10c/K10b）・PR #408（K11）・PR #410（not_alt_seven / K10c_full）および PR #401（claims-sync）の独立査読と検証
branch: gemini-2/review-lean-k12-k10c-k11-claims
---

# 独立査読・検証ログ：Lean 4 定理 K12 (a)・K10c・系 K10 (b)・K11 および PR #401

## 取りかかったタスク

以下の 5 件の未査読 PR を担当宣言のうえ独立に査読・検証した（なお PR #399 の Lean 定理 K13 は `antigravity-1` により PR #411 で査読済みのため重複を回避）。

1. **PR #404**（`claude-1/lean-k12`, コミット `69da0f8`）：Lean 4 定理 K12 (a)（110 型）
2. **PR #406**（`claude-1/lean-k10c`, コミット `a56bf13`）：Lean 4 定理 K10c（`u ≥ 3`）・系 K10 (b)
3. **PR #408**（`claude-1/lean-k11`, コミット `bbf61a8`）：Lean 4 定理 K11（`v2(m+1) ≥ 5` の奇数なら非交互型）
4. **PR #410**（`claude-1/lean-k10c-u1`, コミット `3dc8d57`）：Lean 4 `not_alt_seven`・定理 K10c 完全な形 `K10c_full`
5. **PR #401**（`claude-1/claims-sync`, コミット `63b6a67`）：`claims/*.yaml` 同期・`STATUS.md` 自動生成化・`code/generate_status.js`

---

## 1. Lean 4 形式化 PR（#404, #406, #408, #410）の独立検証

各 PR のコミットを分離 worktree（`git worktree add --detach`）でチェックアウトし、ローカルの **Lean 4.36.0** で `lake build`・全ファイル禁止語検索（`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`）・`#print axioms`・`Game.lean` ほか既証明モジュールの非改変を確認した。

| PR | コミット | `lake build` | 禁止語 | 検証定理と `#print axioms` | 判定 |
|---|---|---|---|---|---|
| **#404** | `69da0f8` | 26/26 成功 | 0 件 | `Rubidium.K12a`, `k12_rows`, `k12_step` → `[propext, Quot.sound]` | **`[Lean検証済み]`** |
| **#406** | `a56bf13` | 28/28 成功 | 0 件 | `Rubidium.K10c`, `Rubidium.K10b` → `[propext, Classical.choice, Quot.sound]`; `blk1_even`, `blk1_odd` → `[propext, Quot.sound]` | **`[Lean検証済み]`** |
| **#408** | `bbf61a8` | 30/30 成功 | 0 件 | `Rubidium.K11`, `g_iter` → `[propext, Classical.choice, Quot.sound]`; `g_even`, `g_odd`, `g_blk2_even` → `[propext, Quot.sound]` | **`[Lean検証済み]`** |
| **#410** | `3dc8d57` | 30/30 成功 | 0 件 | `Rubidium.not_alt_seven` → `[propext, Quot.sound]`; `Rubidium.K10c_full` → `[propext, Classical.choice, Quot.sound]` | **`[Lean検証済み]`** |

### 主張の忠実性に関する補足
- **K10c の表記同値性**：旧 `STATUS.md` の K10c は「`v2(9u+1) = 1` かつ `v2(11u+1)` 偶数」と記していたが、奇数 `u` に対し `v2(9u+1) ≥ 3 ⇒ 8 | (9u+1) ⇒ u ≡ 7 (mod 8) ⇒ 11u+1 ≡ 6 (mod 8) ⇒ v2(11u+1) = 1`（奇数）となるため、`K10c` / `K10c_full` の結論「`v2(9u+1)` 奇数かつ `v2(11u+1)` 偶数」は元の主張と厳密に同値である。

---

## 2. 独立 Python 3 直接 DP クロスチェックおよび PR #401 監査

`code/gemini2_verify_lean_k12_k10c_k11.py`（出力：`data/gemini2_verify_lean_k12_k10c_k11.txt`）により、`PROBLEM.md` の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）で以下を確認した。

- **定理 K12 (a)**（`5 ≤ m ≤ 2000`）：該当全 **62 ケース**（`m = 17 .. 1969`）すべてで `0 ≤ n ≤ 6(3m+5) + 10` において 110 型と一致（**62/62**）。
- **定理 K10c / `K10c_full`・系 K10 (b)・`not_alt_seven`**（`m + 1 = 8u`, `u` 奇数, `m ≤ 2000`）：全 **125 ケース**（交互型 37、非交互型 88）で `K10c_full` 違反 0 件、K10b 該当 **62/62** 非交互型、条件不成立 **83/83** すべてで Lean 証明の反例位置（`2m+3 ∈ N` または `3m+4 ∈ P`）を確認。`m = 7` で `(25, 0) ∈ P`（`25 mod 17 = 8`）、奇数 `u < 10000` すべてで `v2(9u+1)` 奇数 ⇔ `= 1`（`v2(11u+1)` 偶数の下）を確認。
- **定理 K11**（`v2(m+1) ≥ 5` 奇数、`m ≤ 2000`）：全 **41 ケース**すべて非交互型（Lean 証明の反例位置 `2m+3 ∈ N` が 15 件、`3m+4 ∈ P` が 26 件）。
- **PR #401（`claude-1/claims-sync`, コミット `63b6a67`）**：
  - 収録された全 12 件の `claims/*.yaml`（`K3, K4, K5, K33, K33d, K34, K57, K58, K59, K60, K61, K62`）が `gemini-2` の既存査読 PR 群と **12/12 バイト単位で完全一致**（自己昇格・改変 0 件）。
  - 分離 worktree 上で `uv run python code/generate_status.py --check` および `node code/generate_status.js --check` がともに終了コード 0 で通過。
  - 旧 `STATUS.md` の置換対象 2 節の全項目が `notes/2026-11-25-claude-1-status-archive.md` に欠落なく保全されていることを確認。

---

## ラベル更新（`claims/*.yaml`）

- `claims/K12a.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K12.lean (Rubidium.K12a)`）
- `claims/K10b.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K10c.lean (Rubidium.K10b)`）
- `claims/K10c.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K10c.lean (Rubidium.K10c)`, `lean/Rubidium/K11.lean (Rubidium.not_alt_seven, Rubidium.K10c_full)`）
- `claims/K11.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K11.lean (Rubidium.K11)`）
