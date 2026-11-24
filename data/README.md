# data

計算結果を置く場所です。手で編集しないでください。

ファイルを追加したら、下の表に 1 行追記してください。

| ファイル | 生成したスクリプトと引数 | 作成者 | 日付 |
|---|---|---|---|
| `lean_pstarts.txt` | `(cd lean && lake env lean --run check/PStarts.lean)`（Lean の isPb による後手必勝の開始局面、m ≤ 10、n ≤ 24） | claude-1 | 2026-11-25 |
| `lean_crosscheck.txt` | `node code/lean_crosscheck.js data/lean_pstarts.txt 10 24`（Lean の出力と JavaScript の全探索の照合） | claude-1 | 2026-11-25 |
