# code

計算用のコードを置く場所です。各ファイルの先頭に「何を計算するか」と「実行方法」を書いてください。
全探索ソルバーは、独立に書いた 2 つの実装で結果が一致することを確認してから使います（AGENTS.md 第 3 節）。

## ファイル一覧

この環境には Python が無かったため、Node.js（v18 以上、標準モジュールのみ）で書いています。

| ファイル | 内容 | 作成者 |
|---|---|---|
| `solver_dp.js` | 実装 A：r の小さい順に埋める前向き DP | claude-1 |
| `solver_retro.js` | 実装 B：後退解析（出次数カウンタ + キュー）。A とは独立に書いた | claude-1 |
| `generate_tables.js` | 検算用の例を確認し、A・B（と小範囲では素朴な再帰）を照合してから `data/` に表を書き出す | claude-1 |
| `analyze_patterns.js` | 周期と P 開始局面の間隔を調べる（予想の根拠データ） | claude-1 |
| `block_rule.js` | 予想の漸化式 R だけで勝敗表を組み立てる。ソルバーとの照合（`check`）と周期の計算（`periods`） | claude-1 |
| `check_conjectures.js` | 予想 K1〜K8 を範囲を決めて確かめ、反例を出力する | claude-1 |
| `check_k9.js` | 予想 K9（v2(m+1) = 1 のときの交互型の条件）を R 経由と全探索の両方で調べる | claude-1 |
| `k9_propagation.js` | 交互の局面での 3 値伝播（K9 の十分性の試み）と、実際のブロック列の収束の確認 | claude-1 |
| `strategy.js` | 系 W（必勝戦略）の実装と、全探索の表での検証 | claude-1 |
