---
agent: antigravity-1
date: 2026-11-25
problem: restricted-stone-game
task: PR #399（定理 K13 の Lean 4 での形式化、Issue #398）の独立査読
branch: antigravity-1/review-lean-k13
---

# 査読ログ：PR #399（定理 K13（100 型）の Lean 4 での形式化）

## やったこと

- 対象：`claude-1/lean-k13`（56c41e7）の `lean/Rubidium/K13.lean`、`lean/Rubidium.lean`、`lean/README.md`、`notes/2026-11-25-claude-1-lean-k13.md`。
- ローカルで `lake build` を実行した（Lean `leanprover/lean4:v4.36.0`、elan 経由）。
- `#print axioms` で公理を確かめた（`Rubidium.K13`、`Rubidium.p_four`、`Rubidium.p_two`）。
- `lean/Rubidium/*.lean` 全体を `sorry`、`admit`、`axiom`、`native_decide`、`implemented_by`、`unsafe` で検索した。
- 主張が PROBLEM.md と定理 K13 に忠実かを、`Game.lean` の `IsP` と `K4Full.lean` の `v2` の定義まで読んで確かめた。
- 主張そのものを、PROBLEM.md の定義だけから書いた独立な全探索（JavaScript、`code/` は読んでいない）で確かめた。

## 結果

- **ビルド**：`lake build` は `Build completed successfully (24 jobs)`。エラーも `sorry` の警告もない。
- **公理**：3 つの定理とも `[propext, Quot.sound]` だけ（`Classical.choice` もない）。
- **禁止語の検索**：`sorry`、`admit`、`axiom`、`native_decide`、`implemented_by`、`unsafe` はどこにもない。
- **定義の忠実性**：
  - `IsP m r p := ∀ k, 1 ≤ k → k ≤ m → k ≤ r → k ≠ p → ¬ IsP m (r − k) k`（r についての整礎な再帰）。これは PROBLEM.md の合法手（1 ≤ k ≤ min(m, r)、k ≠ p）、遷移 (r − k, k)、正規形の勝敗と一致する。
  - `v2 n`：n ≠ 0 かつ偶数なら v2(n/2) + 1、それ以外は 0。n ≥ 1 では通常の 2 進付値。引数の 9u + 1、11u + 1 は 1 以上なので問題ない。
- **主張の忠実性**：`#check` の結果は次のとおり。

  ```
  K13 : ∀ m, m % 8 = 7 →
    (v2 (9u+1) = 1 ∧ v2 (11u+1) = 3) ∨ (v2 (9u+1) = 3 ∧ v2 (11u+1) = 1) →   -- u = (m+1)/8
    ∀ n, IsP m n 0 ↔ n % (3m+4) ∈ {0, m+2, 2m+3}
  ```

  - 定理 K13（m + 1 = 8u、{v2(9u+1), v2(11u+1)} = {1, 3} なら「100 型」）と同じ。
  - u が偶数なら 9u + 1 は奇数で v2 = 0 になり、仮定は成り立たない。したがって v2(m+1) = 3 は仮定に含まれている。
  - n = 0 も含む形で、もとの主張より少し強い（n ≥ 1 の開始局面も当然含む）。
- **独立な全探索**：m ≤ 700 で仮定を満たす m の 11 個（39, 119, 167, 247, 295, 375, 423, 503, 551, 631, 679）すべてで、0 ≤ n ≤ 6(3m+4) + m の範囲で (n, 0) が P ⇔ n mod (3m+4) ∈ {0, m+2, 2m+3} が成り立った（失敗 0）。
  - スクリプト：`code/antigravity1_k13_check.js`。実行方法：`node code/antigravity1_k13_check.js 700 6`。
- 証明の組み立て（`p_four`、`p_two`、`k13_step`、`k13_rows`、n mod L の場合分け）はログの説明と対応している。Lean の型検査が通っているので、各段の正しさはカーネルが保証している。

## うまくいかなかったこと

- なし。

## 査読

- 対象：PR #399。
- 確認した範囲：上の「結果」のすべて。
- 見つけた問題点：なし。
- 小さな提案：`v2` は `K4Full.lean` で定義されているが、`Game.lean` か専用のファイルに移すと、主張を読む人が定義を見つけやすい（必須ではない）。
- **結論：定理 K13 は `[Lean検証済み]` の条件（`sorry` なしで型検査が通る、主張が忠実）を満たす。** ファイルは `lean/Rubidium/K13.lean`、定理名は `Rubidium.K13`。
  - `claims/K13.yaml` は `ruca-logic` にまだないため（PR #401 で claims を移行中）、この PR では claims と STATUS.md を変えていない。PR #401 のマージ後に、`[Lean検証済み]`（lean: `lean/Rubidium/K13.lean`、`Rubidium.K13`）に更新してほしい。
- 自分は K13 と、その Lean 形式化の著者ではない。

## 次にやるべきこと

- PR #404（K12 (a)）、#406（K10c・K10 (b)）、#408（K11）、#410（m = 7・K10c の完全な形）の Lean 形式化の査読。

## 要確認

- なし（未マージの PR の滞留は前回のログ `2026-11-24-antigravity-1-review-k34.md` に書いたとおり）。
