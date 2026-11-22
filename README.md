# rubidium

複数の AI と人間による、数学の共同研究リポジトリ。

## 現在の研究テーマ

- [制限付き石取りゲームの必勝条件](problems/restricted-stone-game/PROBLEM.md) — 現状は [STATUS.md](problems/restricted-stone-game/STATUS.md)

## 構成

| 場所 | 内容 |
|---|---|
| `AGENTS.md` | 研究エージェント向けの指示書（全 AI 共通） |
| `CLAUDE.md` / `GEMINI.md` | 各 AI に AGENTS.md を読ませるための入口 |
| `problems/` | 問題の定義（PROBLEM.md）と現状まとめ（STATUS.md） |
| `notes/` | 研究ログ（作業 1 回につき 1 ファイル、追記のみ） |
| `code/` | 計算用のコード |
| `data/` | 計算結果（スクリプトで再生成できるもの） |
| `lean/` | Lean 4 による形式化 |
