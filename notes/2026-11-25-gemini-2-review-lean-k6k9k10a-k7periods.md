---
agent: gemini-2
date: 2026-11-25
problem: restricted-stone-game
task: Lean 4 形式化 PR #391（K6）・PR #393/#395（K9）・PR #397（K10a）および予想 K7 周期確認 PR #384/#386/#389（m ≤ 2000）の独立査読と検証
branch: gemini-2/review-lean-k6k9k10a-k7periods
---

# 独立査読・検証ログ：Lean 4 定理 K6・K9・K10 (a) および予想 K7（m ≤ 2000）

## 取りかかったタスク

以下の 7 件のオープン PR を独立に査読・検証した。

1. **PR #391**（`claude-1/lean-k6`, コミット `60533e5`）：Lean 4 定理 K6
2. **PR #393**（`claude-1/lean-k9`, コミット `f883a85`）：Lean 4 定理 K9（十分性）
3. **PR #395**（`claude-1/lean-k9-nec`, コミット `360b0b3`）：Lean 4 定理 K9（必要性・同値）
4. **PR #397**（`claude-1/lean-k10a`, コミット `d86c644`）：Lean 4 定理 K10 (a)
5. **PR #384**（`claude-1/k7-periods`）：予想 K7 確認 `2 ≤ m ≤ 400`
6. **PR #386**（`claude-1/k7-periods-1000`）：予想 K7 確認 `401 ≤ m ≤ 1000`（`codex-1` 査読への数値再計算補足）
7. **PR #389**（`claude-1/k7-periods-2000`）：予想 K7 確認 `1001 ≤ m ≤ 2000` および前周期 10 例の解析

---

## 1. Lean 4 形式化 PR（#391, #393, #395, #397）の独立検証

各 PR のコミットを分離 worktree（`git worktree add --detach`）にチェックアウトし、ローカルの **Lean 4.36.0** で `lake build`・全ファイル禁止語検索（`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`）・`#print axioms`・`Game.lean` ほか既証明モジュールの非改変確認を実施した。

| PR | コミット | `lake build` | 禁止語 | 検証定理と `#print axioms` | 判定 |
|---|---|---|---|---|---|
| **#391** | `60533e5` | 18/18 成功 | 0 件 | `Rubidium.K6`, `k6_rows`, `row_long`, `odd_of_rows` → `[propext, Quot.sound]` | **`[Lean検証済み]`** |
| **#393** | `f883a85` | 20/20 成功 | 0 件 | `Rubidium.K9_suff`, `k9_rows`, `blkE_step`, `blkO_of_blk` → `[propext, Quot.sound]` | **`[Lean検証済み]`** |
| **#395** | `360b0b3` | 20/20 成功 | 0 件 | `Rubidium.K9_nec`, `Rubidium.K9` → `[propext, Quot.sound]` | **`[Lean検証済み]`** |
| **#397** | `d86c644` | 22/22 成功 | 0 件 | `Rubidium.K10a`, `k10_rows`, `k10_O`, `k10_E_h`, `not_isP_near` → `[propext, Quot.sound]` | **`[Lean検証済み]`** |

### 数学的主張の忠実性チェック
- **定理 K6（`Rubidium.K6`）**：`m % 8 = 5`（`Nat` 上で自動的に `m ≥ 5`）のもと `IsP m n 0 ↔ n % (2m+3) ∈ {0, m+2}`。H(j) を使わずに直接帰納法で完結。
- **定理 K9（`Rubidium.K9`）**：`m % 4 = 1 ∧ 5 ≤ m`（`m ≥ 3` かつ `v2(m+1) = 1` と厳密に同値）のもと、交互型 ⇔ `v2(3h+1)` 奇数。十分性は二分木 `T` を `Blk` / `BlkO` に置換した簡潔な証明、必要性は `K3` と `row_long` のみから `(2m+3, 0) ∈ N` を直接導出。
- **定理 K10 (a)（`Rubidium.K10a`）**：`m % 64 = 7 ∧ 71 ≤ m`（`m + 1 = 8u, u ≡ 1 (mod 8), u ≥ 9` と厳密に同値、`m = 7` を正確に除外）のもと交互型。H(j) を使わず 7 距離の不変量を直接証明。
- **直接 DP クロスチェック**（`code/gemini2_verify_k7_periods.py`）：`5 ≤ m ≤ 200` で K6（25/25）・K9 同値および `K9_nec`（49/49）を独立の直接 DP と照合し全件一致。

---

## 2. 予想 K7 周期確認 PR（#384, #386, #389）の独立 Python 3 検証

独立スクリプト `code/gemini2_verify_k7_periods.py` を作成し、出力を `data/gemini2_verify_k7_periods.txt` に保存した。

1. **アルゴリズム妥当性**：`PROBLEM.md` の定義のみに基づく O(N) 厳密 DP（漸化式 R / K8 不使用）を、素朴な O(N·m²) 2 次元ミニマックス DP と `2 ≤ m ≤ 30, 0 ≤ r ≤ 300`（**148,393 局面**）で照合し、不一致 **0 件**を確認。
2. **全 4 データ組（計 798 ケース、延べ 8,928,926 行の直接 DP）の全数検証**：
   - `2..200` 全数（PR #384）：**199/199** 一致（最大周期 `m=169, L=1365`、前周期あり `55, 95`）
   - `201..400` の `v2(m+1)` 奇数（PR #384）：**66/66** 一致（最大周期 `m=353, L=2483`、前周期なし）
   - `401..1000` の `v2(m+1)` 奇数（PR #386）：**201/201** 一致（最大周期 `m=919, L=29464`、前周期あり `481, 801, 929, 991`）
   - `1001..2000` の `v2(m+1)` 奇数（PR #389）：**332/332** 一致（最大周期 `m=1577, L=71047`、前周期あり `1185, 1463, 1503, 1953`）
   - すべてのケースで、ファイル間整合性・`n ≥ t+1` の周期性・**`t = 0` 時の境界 `n = 0`（`S(0) = S(L)`；`k7_check_dp.js` 未検査）**・`t > 0` 時の前周期最小性 `S(t) ≠ S(t+L)`・**`L` の全真約数 `d | L` に対する最小周期性（`k7_check_dp.js` 未検査）**・間隔 `∈ {0, 1}` および純周期時の間隔語一致を確認。前周期あり 10 件は `n ≤ t + 6L + 10` まで拡張確認。
3. **PR #389 の前周期 10 例の表・観察検証**：
   - `55, 95, 481, 801, 929, 991, 1185, 1463, 1503, 1953` の全 10 行について、`v, u`, 前周期の間隔, 周期の語, `t, L`, `t` の表示式、`v=1` 類の `u ≡ 17 (mod 32)`（`m ≤ 2000` で 31 個中 5 個）・`u mod 128 = [113, 17, 81, 81, 81]`、`1185` と `1953` の間隔列一致まで全項目一致を確認。

---

## ラベル更新（`claims/*.yaml`）

- `claims/K6.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K6.lean (Rubidium.K6)`）
- `claims/K9.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K9.lean (Rubidium.K9, Rubidium.K9_suff, Rubidium.K9_nec)`）
- `claims/K10a.yaml`：**`[Lean検証済み]`**（`lean/Rubidium/K10.lean (Rubidium.K10a)`）
- 予想 K7：確認範囲 `m ≤ 2000` の独立検証完了（ラベルは `[予想]` 維持）。
