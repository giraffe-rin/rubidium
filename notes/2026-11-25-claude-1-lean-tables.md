---
agent: claude-1
date: 2026-11-25
problem: restricted-stone-game
task: Lean の DP による勝敗表と data/tables の照合（Issue #378）
branch: claude-1/lean-tables
---

# Lean の DP による勝敗表と data/tables の照合

## 取りかかった理由

未査読の証明 PR が 5 件（#368・#370・#373・#375・#377）になり、WIP 上限に達した。
ほかのエージェントの証明 PR で査読待ちのものもないので、証明ではない検証の作業として、別の言語での照合（PR #341 で推奨されている）をした。

## やったこと

- `lean/check/Tables.lean`：Lean 4 の Array による DP で、全局面 (r, p)（1 ≤ m ≤ 30、0 ≤ r ≤ 2000、0 ≤ p ≤ m）の P/N を計算した。
  規則は PROBLEM.md の定義（`Rubidium.IsP` と同じ形）。インタプリタで約 10 秒。出力は `data/lean_tables.txt`。
- `code/lean_tables_compare.js`：この出力を `data/tables/m01..m30.txt` と 1 文字ずつ比べた。
  data/tables は JavaScript の 2 つの実装（solver_dp.js と solver_retro.js）が一致したもの（2026-11-23、コミット 1c8eb7e）。
- 結果（`data/lean_tables_compare.txt`）：**合計 990495 局面のうち、一致しなかったもの 0**。

## 意味

- 勝敗表の土台が、言語の違う 3 つの実装（JavaScript の前向き DP、JavaScript の後退解析、Lean の DP）で一致した。
- Lean の DP には証明がない（`isPb_iff` で IsP と同値と証明したのは、遅い再帰版の `isPb` のほう）。DP 版と IsP の同値性の証明は、WIP が下がってから取り組む候補。

## 状態

計算による照合（ラベルの変化なし）。
