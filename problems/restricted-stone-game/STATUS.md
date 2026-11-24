# STATUS — 制限付き石取りゲーム

チーム全体で「今わかっていること」をまとめる場所です。
更新ルールは `AGENTS.md` 第 4・5 節を参照してください。各項目には根拠のログファイル名を書きます。

最終更新：2026-11-23（初期化）

## 確立した結果
（`[査読済み]` または `[Lean検証済み]` のものだけをここに書く）

- **K10b** [Lean検証済み] 系 K10 (b)：m + 1 = 8u、u ≡ 3 または 7 (mod 8) のとき交互型でない（¬ Alt m）（Lean 4.36.0 sorry なし、標準公理 propext・Classical.choice・Quot.sound のみ検証済み）（根拠: notes/2026-11-25-claude-1-lean-k10c.md, notes/2026-11-25-gemini-2-review-lean-k12-k10c-k11-claims.md）
- **K10c** [Lean検証済み] 定理 K10c（完全な形）：m + 1 = 8u（u 奇数）が交互型（Alt m）なら u ≥ 3、v2(9u+1) 奇数（= 1 と同値）、v2(11u+1) 偶数（m = 7 の非交互型 not_alt_seven 含む；Lean 4.36.0 sorry なし検証済み）（根拠: notes/2026-11-25-claude-1-lean-k10c.md, notes/2026-11-25-claude-1-lean-k10c-u1.md, notes/2026-11-25-gemini-2-review-lean-k12-k10c-k11-claims.md）
- **K11** [Lean検証済み] 定理 K11：m + 1 = 2^v·u（v ≥ 5 の奇数、u は奇数）なら交互型でない（¬ Alt m）（Lean 4.36.0 sorry なし、標準公理 propext・Classical.choice・Quot.sound のみ検証済み）（根拠: notes/2026-11-25-claude-1-lean-k11.md, notes/2026-11-25-gemini-2-review-lean-k12-k10c-k11-claims.md）
- **K12a** [Lean検証済み] 定理 K12 (a)：v2(m+1) = 1（m % 4 = 1、m ≥ 5）、v2(3h+1) = 2、Q = (11h+5)/8 が奇数のとき「110」型（(n, 0) が P ⇔ n mod (3m+5) ∈ {0, m+2, 2m+4}）（Lean 4.36.0 sorry なし、公理 propext・Quot.sound のみ検証済み）（根拠: notes/2026-11-25-claude-1-lean-k12.md, notes/2026-11-25-gemini-2-review-lean-k12-k10c-k11-claims.md）

## 予想・未査読の結果
（`[予想]` には確かめた範囲を、`[非形式証明]` には証明の場所を書く）

- まだなし

## 未解決の問い

- 各 `m` について、開始局面 `(n, 0)` が先手必勝となる `n` の特徴づけ（主目標）
- 一般の局面 `(r, p)` の勝敗
- 必勝戦略の記述

## 試して駄目だった方法
（同じ失敗を繰り返さないために、理由とともに書く）

- まだなし

## 最初に取りかかるべきタスク

1. 全探索ソルバーを 2 つの独立な実装で作り、結果の一致を確認する（`code/`）。
2. `1 ≤ m ≤ 30`、`1 ≤ n ≤ 2000` 程度の勝敗表を `data/` に出力する。開始局面だけでなく、すべての `(r, p)` について出す。
3. 勝敗表から周期性などの規則を探し、予想としてまとめる。
4. 小さな `m`（`m = 2, 3`）から順に証明を試みる。
5. ゲームの定義と勝敗判定を Lean 4 で形式化する（`lean/`）。
