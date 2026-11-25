# PR 移行アーカイブ（WIP リセット, 2026-11-25）

自律パイプライン再稼働のため、2026-11-25 時点の Open PR（全 70 件）をすべてクローズした。
クローズ前に「`.lean` ファイルを含み、`sorry` / `admit` を含まない」有望 PR を抽出して記録する。

## 抽出方法

- 各 PR の head（`refs/pull/<n>/head`）と `ruca-logic` の merge-base 間で追加・変更された `*.lean` を列挙
- 該当ファイルの head 版に対し `sorry` / `admit`（単語一致）を検索
- 参考として `axiom` / `native_decide` / `implemented_by` / `extern` / `unsafe` も検索

## 有望 PR（1 件）

| PR | タイトル | head ブランチ / SHA | 状態 |
|---|---|---|---|
| #459 | SG-005: checkpoint-1 以降の claude-1 の Lean 4 の結果をまとめる（K7′〜K69、被覆率 94.82%） | `claude-1/sg005-lean-batch` @ `d894779864e86ef4badcd4f6224d6708454dd4ea` | `ci-failed` ラベル付き |

### #459 の詳細

- 15 コミット、48 ファイル、+38,575 行（削除なし）。merge-base 以降 `ruca-logic` は進んでいないため、そのまま再提出可能。
- 追加 Lean ファイル（すべて新規。`sorry` / `admit` / 禁止トークンなし）:
  `lean/Rubidium.lean`（import 追加）, `K7`, `K10c`, `K11`, `K12`, `K15gen`, `K29`, `K29gen`,
  `K38`, `K38gen`, `K38v7`, `K38w`, `K64`, `K66`, `K67b`, `K67c`, `K68a`〜`K68e`,
  `K68f1`〜`K68f7`, `K69a`, `K69b1`（いずれも `lean/Rubidium/` 配下）
- その他: `claims/conjectures/K67-13.json`, `claims/conjectures/K68.json`, `code/k67_*.js`, `code/k68_*.js`,
  `code/k69_*.js`, `code/lean_coverage.js`, `data/k68_scan.txt`, `data/lean_coverage.txt`, `notes/2026-11-2[56]-claude-1-*.md`
- CI 結果: `Immutable Core Guard` ✅ / `Verify Lean 4` ✅ / `Verify Code & Red Team` ✅ / `validate` ✅ / `finalize-pr` ❌
- `finalize-pr` の失敗原因は PR の内容ではなく、ワークフロー側で `gh pr merge` が checkout なしで実行されていること
  （`fatal: not a git repository`）。`.github/**` は不変コアのため、人間による修正が必要。
- **再提出手順**: ブランチ `claude-1/sg005-lean-batch`（またはコミット `d894779`）から新規 PR を作成する。
  ワークフローを修正するまでは、他の PR と同様に `finalize-pr` で失敗する見込み。

## クローズした他の PR（69 件、`.lean` 変更なし）

いずれも gemini-2 / antigravity-1 による査読・Python 独立検証の PR（notes / code のみ）:

#456, #454, #448, #439, #438, #433, #428, #422, #421, #416, #411, #400, #388, #371, #365, #359,
#354, #340, #339, #333, #326, #321, #303, #298, #295, #293, #291, #269, #264, #263, #262, #253,
#250, #247, #246, #213, #210, #207, #206, #203, #202, #201, #200, #199, #194, #191, #188, #185,
#180, #138, #137, #136, #135, #134, #133, #132, #131, #130, #129, #128, #119, #118, #117, #116,
#115, #114, #113, #112, #111

head ブランチは削除していないため、必要に応じて復元可能。
