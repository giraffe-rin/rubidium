# 2026-11-25 claude-1：Lean の計算できる判定 isPb と全探索との照合（Issue #372）

## やったこと

- `lean/Rubidium/Decide.lean` に、計算できる判定 `isPb m r p : Bool` を定めた。
  `Nat.all r` で手 k = i + 1（i < r）をすべて調べ、「k ≤ m かつ k ≠ p なら、移った先 (r − k, k) で isPb が false」を求める。r についての整礎な再帰。
- 定理 `isPb_iff`：すべての r, p で `isPb m r p = true ↔ IsP m r p`。r についての強い帰納法で証明した（補題 `nat_all_iff`：`Nat.all n f = true ↔ ∀ i < n, f i = true`）。`sorry` なし。
- `lean/check/PStarts.lean` で isPb を実行し、m = 1..10、1 ≤ n ≤ 24 の後手必勝の開始局面 (n, 0) を出した（data/lean_pstarts.txt、数秒）。
- `code/lean_crosscheck.js`：PROBLEM.md の定義をそのままたどるメモ化した全探索で同じ一覧を作り、Lean の出力と比べた（data/lean_crosscheck.txt）。**10 個の m すべてで一致**。

## 結果（後手必勝の開始局面 n ≤ 24）

| m | n |
|---|---|
| 1 | なし |
| 2 | 3 6 9 12 15 18 21 24 |
| 3 | 4 8 12 16 20 24 |
| 4 | 5 10 15 20 |
| 5 | 7 13 20 |
| 6 | 7 14 21 |
| 7 | 9 17 |
| 8 | 9 18 |
| 9 | 11 22 |
| 10 | 11 22 |

最初の P の開始局面は、K4（v2(m+1) が偶数なら m+1）と K5（奇数なら m+2）に合っている（m = 2: 3、m = 3: 4（v2(4) = 2）、m = 5: 7、m = 7: 9 など）。

## 意味

- `isPb_iff` により、`isPb` を `decide` 的に評価した結果は `IsP` の証明に使える。今後、小さい m の具体的な主張（例：周期の最初の数項）を Lean で確かめる足がかりになる。
- 異なる言語（Lean と JavaScript）での照合（PR #341 で推奨）。

## 状態

- `isPb_iff`：[Lean検証済み]（査読待ち）。
- 一覧の値：計算結果（2 つの実装で一致）。
