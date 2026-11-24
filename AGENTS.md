# AGENTS.md — 研究エージェント向け指示書

## 1. 研究テーマ

複数の AI と人間による数学の共同研究リポジトリです。現在の主題は **制限付き石取りゲーム（Restricted Stone Game）** の必勝条件の完全な特徴づけであり、問題定義は `problems/restricted-stone-game/PROBLEM.md`、Lean 4 上の厳密な定義は `lean/Rubidium/Game.lean`（`Rubidium.IsP`）にあります。最終目標は全 $m \ge 1$ に対する開始局面 $(n, 0)$ の特徴づけ定理 `MainTheorem` を `sorry` なしで証明することです。

## 2. 不変コア（Immutable Core）と保護ルール

完全自律パイプラインでは、`config/autonomous.json` の `immutable_globs` に列挙されたファイルを **不変コア** として凍結しています。エージェントの PR が以下のいずれかを変更した場合、`autonomous-gatekeeper.yml` によって人間レビュー待ちにせず **即座に `immutable-violation` ラベル付与・クローズ・ブランチ削除** されます。

- `problems/*/PROBLEM.md`, `problems/*/STATUS.md`（`STATUS.md` はオーケストレーターが決定論的に再生成）
- `lean/Rubidium/Game.lean`, `lean/lakefile.toml`, `lean/lean-toolchain`
- `claims/proved/**`（`claims/proved/index.json` は自動生成）
- `AGENTS.md`, `CLAUDE.md`, `GEMINI.md`, `.github/**`, `.claude/**`
- `config/autonomous.json`, `scripts/autonomous_ops.py`
- `data/dead_ends.jsonl`, `data/state.json`

また、`config/autonomous.json` の `allowed_globs` に含まれないファイルへの変更も拒否されます。

## 3. 作業を始めるとき（毎回この順で）

1. `problems/restricted-stone-game/STATUS.md` と `data/dag.json` を読み、現在の証明済み定理・未解決サブゴール・`needs_decomposition: true` の項目を確認する。
2. **`data/dead_ends.jsonl` を必ず参照する**。過去に未マージクローズまたは Red Team により反証されたアプローチと同じ失敗を繰り返さないこと。
3. オープン PR 数を確認し、**WIP 上限（`max_open_prs: 3`、日次上限 `max_daily_prs: 24`）** を超えている場合は新規 PR を作成しない。
4. 取り組むサブゴールを 1 つ選び、**PR のタイトルまたは本文に必ず `SG-xxx` タグ（例: `SG-004`）を含める**。3 回失敗したサブゴールは自動的に `needs_decomposition: true` へ昇格するため、より小さい補題へ分解してから再挑戦する。

## 4. Prover / Red Team 分離ルール

自己確認バイアスを防ぐため、証明・予想提案（Prover）と反例探索（Red Team）を明確に分離します。

- **Prover の責務**:
  - 新しい予想は `claims/conjectures/<id>.json` に登録する（必須フィールド: `id`, `subgoal_id`, `statement`）。
  - Lean 4 証明は `lean/Rubidium/` 配下へ追加し、`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` を一切含めないこと（`verify-lean-static`・`lean-action` の `axiom-audit`・`leanchecker` で厳密検証される）。
- **Red Team の責務**:
  - 予想や計算ルールに対する反例探索テストを `code/redteam/test_*.py` として実装する（1 テストあたり制限時間 60 秒）。
  - テストが反例を検出して非 0 終了した場合、ゲートキーパーは PR に `falsified-by-redteam` ラベルを付与して即時クローズ・ブランチ削除する。反例発見は健全な探索成果であるため、`data/state.json` の `stagnation_cycles` は加算されない。

## 5. 共有のルール（Git / PR / 自動マージ）

- `ruca-logic` への直接 push は禁止。すべての変更は PR 経由で提出する（書き込み権限のない外部 AI は Fork 経由の PR 作成を使用）。
- Branch Protection の必須チェックは `finalize-pr` に一本化されている。`immutable-core-guard`・`verify-lean`・`verify-code-and-redteam` をすべて通過した非 Draft PR は、ゲートキーパーが `gh pr merge --auto --squash --delete-branch` で自動マージを予約する。
- `ci-failed` のまま 24 時間放置された PR、および 72 時間更新のない Stale PR は `autonomous-orchestrator.yml` により自動クローズされ、`data/dead_ends.jsonl` へ記録される。

## 6. 既存ワークフローとの整理・統合方針

- **`auto-merge.yml`（旧）**: `autonomous-gatekeeper.yml` の `finalize-pr` と自動マージ処理が競合するため、自律パイプライン有効化時は `auto-merge.yml` を無効化または削除して `finalize-pr` に一本化すること。
- **`rubidium-ci.yml`（旧）**: PR 検証を `autonomous-gatekeeper.yml` に統合するため、重複する Branch Protection 必須チェックから外し、`finalize-pr` のみを必須チェックとして設定すること。
- **`pages.yml`**: GitHub Pages 公開用の独立ワークフローのためそのまま維持可能。
