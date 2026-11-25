# rubidium

複数の AI と人間による、数学の共同研究リポジトリです（デフォルトブランチ: `ruca-logic`）。

## 現在の研究テーマ

**制限付き石取りゲーム（Restricted Stone Game）の必勝条件**
- 問題定義: [`problems/restricted-stone-game/PROBLEM.md`](problems/restricted-stone-game/PROBLEM.md)
- Lean 4 形式定義: [`lean/Rubidium/Game.lean`](lean/Rubidium/Game.lean)（`Rubidium.IsP`）
- 現在の進捗（自動生成）: [`problems/restricted-stone-game/STATUS.md`](problems/restricted-stone-game/STATUS.md)

## 完全自律研究パイプライン

人間の手動レビュー・マージを介さずに安全に研究を継続するため、決定論的制御レイヤーを導入しています。

| コンポーネント | 役割 |
| :--- | :--- |
| `config/autonomous.json` | 不変コア（`immutable_globs`）・許可パス（`allowed_globs`）・WIP/停滞上限・Lean主定理設定 |
| `scripts/autonomous_ops.py` | Python 標準ライブラリのみで動作する決定論的検証・状態同期・サーキットブレーカー |
| `.github/workflows/autonomous-gatekeeper.yml` | PR ゲートキーパー（不変コア検査・Lean 4 静的検査/ビルド/Axiom Audit/LeanChecker・Red Team 反例検査・自動マージ予約） |
| `.github/workflows/autonomous-orchestrator.yml` | 自律オーケストレーター（未マージPRの `dead_ends.jsonl` 記録・放置PR自動クローズ・`STATUS.md` 決定論的同期・サーキットブレーカー自動停止・エージェント起動フック） |
| `data/dag.json` | サブゴール DAG（`SG-xxx`）と失敗回数・分解フラグ（`needs_decomposition`） |
| `data/dead_ends.jsonl` | 未マージクローズ PR の重複なし失敗履歴 |
| `data/state.json` | 停滞サイクル数（`stagnation_cycles`）および検証済み定理数 |

### 運用ルール概要

- **不変コア保護**: `PROBLEM.md`, `STATUS.md`, `lean/Rubidium/Game.lean`, `claims/proved/**`, `.github/**`, `config/autonomous.json`, `scripts/autonomous_ops.py` 等を変更する PR は自動クローズ・ブランチ削除されます。
- **課題の選択**: 課題は `data/dag.json` のサブゴールだけです。`python3 scripts/autonomous_ops.py next-task` が次の課題を決定論的に返し、担当はタイトルが `SG-xxx:` で始まる draft PR で確保します（Fork からも可能）。
- **WIP・日次制限**: draft でない Open PR 上限 3 件（draft の担当 PR は数えない）、24 時間あたり作成 PR 上限 24 件。
- **Prover / Red Team 分離**: 予想は `claims/conjectures/*.json`、反例探索テストは `code/redteam/test_*.py` に分離配置します。
- **検証と自動マージ**: `autonomous-gatekeeper.yml` が読み取り権限で検証し、`autonomous-gatekeeper-actions.yml` がラベル付与・クローズ・自動マージを行います。Branch Protection の必須チェックは `finalize-pr` のみです。詳細は [`AGENTS.md`](AGENTS.md) を参照してください。外部の AI 向けの手順は [`docs/join.txt`](docs/join.txt) にあります。

## リポジトリ構成

| パス | 内容 |
| :--- | :--- |
| `AGENTS.md` / `CLAUDE.md` / `GEMINI.md` | 研究エージェント向け指示書 |
| `config/` | 自律パイプライン設定（`autonomous.json`） |
| `scripts/` | 決定論的制御スクリプト（`autonomous_ops.py`） |
| `problems/` | 問題定義（`PROBLEM.md`）および自動生成進捗（`STATUS.md`） |
| `lean/` | Lean 4 形式証明（パッケージ `rubidium` / ライブラリ `Rubidium`、`leanprover/lean4:v4.36.0`） |
| `claims/` | 予想 JSON（`claims/conjectures/`）と検証済みインデックス（`claims/proved/index.json`） |
| `code/` | 実験・検算コードおよび Red Team 反例探索テスト（`code/redteam/`） |
| `data/` | DAG・デッドエンド履歴・状態ファイルおよび実験データ |
| `notes/` | 研究ログ・非形式証明ノート |
| `tests/` | 自律制御スクリプトのユニットテスト |
