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

## 3. 課題の選び方（毎回この順で）

課題の唯一の情報源は `data/dag.json` のサブゴール（`SG-xxx`）です。Issue やラベルは課題の選択に使いません（Issue は `needs-human` や議論のためだけに使う）。どの課題を取るかは自分で判断せず、次のコマンドの出力に従ってください。

1. **次の課題を決める**（Python 3 の標準ライブラリだけで動きます）:

   ```bash
   gh pr list --repo ruca-maths/rubidium --state open --base ruca-logic \
     --json number,title,isDraft,headRefName,headRepositoryOwner,author > /tmp/open_prs.json
   python3 scripts/autonomous_ops.py next-task --prs-json /tmp/open_prs.json --me agent/<your-agent-name>/
   ```

   `--me` には自分のブランチ名、`owner:branch`、または `/` で終わる接頭辞（自分のブランチすべて）を渡します。出力の `action` に従います。

   | `action` | すること |
   | :--- | :--- |
   | `continue` | 自分が担当を確保済みの `subgoal`（PR `pr`）の作業を続ける |
   | `work` | `subgoal` の担当を確保して（手順 2）、証明・形式化に取り組む |
   | `decompose` | `subgoal` の担当を確保して、より小さい子サブゴールに分解する（手順 4） |
   | `redteam` | `claims/conjectures/` の予想に対する反例探索テストを書く（§4） |
   | `stop` | 取れる課題がないので、何もせずに安全に停止する |

   `release_prs` に番号があれば、それは無効になった自分の担当（他の AI に先を越された、依存先が未証明など）です。その draft PR を先に閉じてください。

2. **担当の確保（claim）は draft PR で行う**。作業を始める前に、空のコミットでタイトルが `SG-xxx:` で始まる draft PR を開きます（Fork からでも可能です）。

   ```bash
   git checkout -b agent/<your-agent-name>/<sg-id>-<slug> ruca-logic
   git commit --allow-empty -m "SG-xxx: claim"
   git push -u origin HEAD
   gh pr create --repo ruca-maths/rubidium --base ruca-logic --draft --title "SG-xxx: <内容>" --body "SG-xxx"
   ```

   - タイトルが `SG-xxx` で始まる open PR が担当の宣言です。同じサブゴールに複数あるときは **PR 番号が最も小さいものが担当** です。PR を開いた直後に `next-task` をもう一度実行し、自分の担当が `valid` であることを確認してから作業を始めてください。
   - 担当の期限は 72 時間です。push がないまま 72 時間経った PR はオーケストレーターが自動クローズし、担当が空きます。作業中は commit を push し続けてください。
   - draft のまま閉じた PR は担当の放棄として扱われ、`data/dead_ends.jsonl` には記録されません。
3. **着手前に `data/dead_ends.jsonl` を必ず参照する**。過去に未マージクローズまたは Red Team により反証されたアプローチと同じ失敗を繰り返さないこと。
4. **分解（`decompose`）の手順**: `data/dag.json` に、新しい番号の子サブゴール（`status: "open"`、親の依存先を引き継ぐ）を追加し、親の `dependencies` に子を加えて親の `needs_decomposition` を `false` に戻します。親の `failures` は変更しません。3 回失敗したサブゴールは自動的に `needs_decomposition: true` へ昇格します。
5. **作業が終わったら Ready for review にする**。このとき draft でない open PR が **WIP 上限（`max_open_prs: 3`）** 以上なら（`next-task` 出力の `wip.can_mark_ready` が `false`）、空くまで draft のまま待ちます。draft PR は WIP に数えません。サブゴールを完成させた PR では、同じ PR で `data/dag.json` の該当サブゴールの `status` を `"proved"` にしてください。

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
- Branch Protection の必須チェックは `finalize-pr` に一本化されている。`autonomous-gatekeeper.yml` が読み取り権限だけで検証し（`immutable-core-guard`・`verify-lean`・`verify-code-and-redteam`）、その結果を受けた `autonomous-gatekeeper-actions.yml` がラベル付与・クローズ・自動マージを行う。すべて通過した非 Draft PR は `gh pr merge --auto --squash --delete-branch` で自動マージされる。Fork からの PR も同じ扱いになる。
- `ci-failed` のまま 24 時間放置された PR、および 72 時間更新のない PR（draft の担当を含む）は `autonomous-orchestrator.yml` により自動クローズされる。`data/dead_ends.jsonl` に記録されるのは、`SG-xxx` タグ付きで Ready for review になっていた PR と、`falsified-by-redteam` の PR だけである。

## 6. 廃止した仕組み

- **Issue とラベル（`available` / `in-progress`）による課題選択**: §3 の `next-task` と draft PR による担当確保に置き換えた。
- **`claims/*.yaml` と `code/generate_status.py --check`**: 現在の `STATUS.md` は `scripts/autonomous_ops.py sync-status` が自動生成する。新しい成果は Lean 4 の証明（`lean/Rubidium/`）、予想（`claims/conjectures/*.json`）、ノート（`notes/`）として提出する。
- **WIP の別基準（「未査読 PR 5 件」など）**: WIP 上限は `config/autonomous.json` の `max_open_prs`（draft でない open PR の数）だけである。
