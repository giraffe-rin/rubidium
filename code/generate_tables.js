/*
 * generate_tables.js — 2 つのソルバーを照合してから勝敗表を data/ に書き出す
 *
 * 何を計算するか:
 *   1. PROBLEM.md「検算用の小さな例」を solver_dp.js と solver_retro.js の両方で確認する。
 *   2. 小さな範囲（m ≤ 6, r ≤ 14）では、メモ化しない素朴なゲーム木の再帰（第 3 の実装）とも照合する。
 *   3. 1 ≤ m ≤ M、0 ≤ r ≤ N のすべての局面 (r, p) について 2 つのソルバーの結果が
 *      1 文字残らず一致することを確認する。1 つでも食い違えば何も書かずに異常終了する。
 *   4. 一致したら次を書き出す:
 *        data/tables/mXX.txt    … m = XX の全局面の表（行 = r、列 = p）
 *        data/start_positions.txt … 各 m の開始局面 (n, 0)（1 ≤ n ≤ N）の勝敗
 *
 * 実行方法（リポジトリのルートで。Node.js 18 以上、外部パッケージ不要）:
 *   node code/generate_tables.js 30 2000
 *   引数を省略すると M = 30, N = 2000。
 */
'use strict';

const fs = require('fs');
const path = require('path');
const A = require('./solver_dp');
const B = require('./solver_retro');

const M = parseInt(process.argv[2] || '30', 10);
const N = parseInt(process.argv[3] || '2000', 10);

function fail(msg) {
  console.error('エラー: ' + msg);
  process.exit(1);
}

// 第 3 の実装: 定義どおりの素朴な再帰（メモなし、指数時間なので小さい範囲だけ）
function naiveWins(m, r, p) {
  for (let k = 1; k <= Math.min(m, r); k++) {
    if (k !== p && !naiveWins(m, r - k, k)) return true;
  }
  return false;
}

// 1. 検算用の小さな例
for (const [name, S] of [['solver_dp', A], ['solver_retro', B]]) {
  const t1 = S.solve(1, 200);
  for (let n = 1; n <= 200; n++) {
    if (t1[n][0] !== 'N') fail(`${name}: m=1, n=${n} が先手必勝になっていない`);
  }
  if (S.solve(2, 3)[3][0] !== 'P') fail(`${name}: m=2, n=3 が後手必勝になっていない`);
}
console.log('検算用の小さな例: 両実装とも OK（m=1 は 1 ≤ n ≤ 200 で確認）');

// 2. 素朴な再帰との照合
for (let m = 1; m <= 6; m++) {
  const ta = A.solve(m, 14), tb = B.solve(m, 14);
  for (let r = 0; r <= 14; r++) {
    for (let p = 0; p <= m; p++) {
      const c = naiveWins(m, r, p) ? 'N' : 'P';
      if (ta[r][p] !== c || tb[r][p] !== c) fail(`素朴な再帰と不一致: m=${m}, r=${r}, p=${p}`);
    }
  }
}
console.log('素朴な再帰との照合: OK（1 ≤ m ≤ 6, 0 ≤ r ≤ 14, 全 p）');

// 3. 全範囲での 2 実装の照合
const tables = [];
let positions = 0;
for (let m = 1; m <= M; m++) {
  const ta = A.solve(m, N), tb = B.solve(m, N);
  if (ta.length !== N + 1 || tb.length !== N + 1) fail(`m=${m}: 行数が違う`);
  for (let r = 0; r <= N; r++) {
    if (ta[r].length !== m + 1) fail(`m=${m}, r=${r}: 列数が違う`);
    if (ta[r] !== tb[r]) {
      for (let p = 0; p <= m; p++) {
        if (ta[r][p] !== tb[r][p]) fail(`2 実装が不一致: m=${m}, r=${r}, p=${p}（dp=${ta[r][p]}, retro=${tb[r][p]}）`);
      }
    }
  }
  positions += (N + 1) * (m + 1);
  tables.push(ta);
}
console.log(`2 実装の照合: 完全一致（1 ≤ m ≤ ${M}, 0 ≤ r ≤ ${N}, 0 ≤ p ≤ m、計 ${positions} 局面）`);

// 4. 書き出し
const root = path.join(__dirname, '..', 'data');
const tdir = path.join(root, 'tables');
fs.mkdirSync(tdir, { recursive: true });
const pad = String(M).length;
for (let m = 1; m <= M; m++) {
  const head = [
    `# restricted-stone-game 勝敗表 m=${m}, 0<=r<=${N}`,
    '# 生成: node code/generate_tables.js ' + `${M} ${N}` + '（solver_dp.js と solver_retro.js の一致を確認済み）',
    '# 各行: r <文字列>。文字列の p 文字目（0 始まり, p=0..m）が局面 (r,p) の勝敗。',
    '# N = 手番側（これから指す側）の勝ち、P = 手番側の負け。',
  ];
  const body = tables[m - 1].map((s, r) => `${r} ${s}`);
  fs.writeFileSync(path.join(tdir, `m${String(m).padStart(pad, '0')}.txt`), head.concat(body).join('\n') + '\n');
}
const startLines = [
  `# restricted-stone-game 開始局面 (n,0) の勝敗, 1<=m<=${M}, 1<=n<=${N}`,
  '# 生成: node code/generate_tables.js ' + `${M} ${N}`,
  '# 各行: m <文字列>。文字列の (n-1) 文字目が開始局面 (n,0) の勝敗（N = 先手必勝, P = 後手必勝）。',
];
for (let m = 1; m <= M; m++) {
  let s = '';
  for (let n = 1; n <= N; n++) s += tables[m - 1][n][0];
  startLines.push(`${m} ${s}`);
}
fs.writeFileSync(path.join(root, 'start_positions.txt'), startLines.join('\n') + '\n');
console.log(`書き出し: data/tables/m01..m${String(M).padStart(pad, '0')}.txt, data/start_positions.txt`);
