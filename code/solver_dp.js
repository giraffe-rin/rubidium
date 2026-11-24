/*
 * solver_dp.js — 実装 A：r の小さい順に埋める前向き動的計画法
 *
 * 何を計算するか:
 *   パラメータ m について、すべての局面 (r, p)（0 ≤ r ≤ N, 0 ≤ p ≤ m）が
 *   N 局面（手番側の勝ち）か P 局面（手番側の負け）かを計算する。
 *   定義は problems/restricted-stone-game/PROBLEM.md に従う:
 *     合法手 k: 1 ≤ k ≤ min(m, r), k ≠ p。手 k で (r, p) → (r − k, k)。
 *     合法手がなければ手番側の負け。
 *   考え方: 手 k の行き先 (r − k, k) は r が真に小さいので、r = 0, 1, 2, … の順に
 *   「P 局面へ移る合法手が 1 つでもあれば N、なければ P」という定義をそのまま当てはめる。
 *
 * 実行方法（Node.js 18 以上、外部パッケージ不要）:
 *   node code/solver_dp.js M N
 *     m = M、0 ≤ r ≤ N の表を標準出力に出す。各行は「r 文字列」で、
 *     文字列の p 文字目（0 始まり）が局面 (r, p) の勝敗 'N' / 'P'。
 *   モジュールとして: require('./solver_dp').solve(m, N) -> string[]（r 番目が上の文字列）
 */
'use strict';

function solve(m, nMax) {
  const win = []; // win[r][p] : boolean
  for (let r = 0; r <= nMax; r++) {
    const row = new Array(m + 1);
    for (let p = 0; p <= m; p++) {
      let w = false;
      const top = Math.min(m, r);
      for (let k = 1; k <= top; k++) {
        if (k !== p && !win[r - k][k]) { w = true; break; }
      }
      row[p] = w;
    }
    win.push(row);
  }
  return win.map(row => row.map(w => (w ? 'N' : 'P')).join(''));
}

module.exports = { solve };

if (require.main === module) {
  const m = parseInt(process.argv[2], 10);
  const nMax = parseInt(process.argv[3], 10);
  const lines = solve(m, nMax).map((s, r) => `${r} ${s}`);
  process.stdout.write(lines.join('\n') + '\n');
}
