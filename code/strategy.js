/*
 * strategy.js — 必勝戦略（系 W）を実装し、全探索の表で確かめる
 *
 * 何を計算するか:
 *   notes/2026-11-23-claude-1-strategy.md の系 W に従って、局面 (r, p) の必勝手を返す関数 move(r, p) を作る。
 *   必勝手がない（P 局面と判定した）ときは 0 を返す。
 *   使うのは漸化式 R（code/block_rule.js の nextBlock）で求めたブロックの情報（a_j, g_j, S_j）だけで、ゲームの手は読まない。
 *   check モードでは、全探索の表（solver_dp.js と solver_retro.js の一致を確認）と比べて次を確かめる。
 *     - move(r, p) = 0 ⇔ (r, p) が P
 *     - move(r, p) = k > 0 なら、k は合法手（1 ≤ k ≤ min(m, r), k ≠ p）で、(r − k, k) は P
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/strategy.js check 2 100 10000
 *   モジュールとして: require('./strategy').makeStrategy(m, N) -> (r, p) => k
 */
'use strict';

const R = require('./block_rule');

function makeStrategy(m, nMax) {
  const h = (m + 1) / 2;
  // 各行 r について、属するブロックの番号 blk[r] と距離 dist[r] を記録する
  const blocks = []; // { a, g, S }
  const blk = new Int32Array(nMax + 1), dist = new Int32Array(nMax + 1);
  let a = 0, prev = null;
  while (a <= nMax) {
    const b = R.nextBlock(m, prev);
    blocks.push({ a, g: b.g, S: b.S });
    for (let d = 0; d < b.g && a + d <= nMax; d++) { blk[a + d] = blocks.length - 1; dist[a + d] = d; }
    a += b.g;
    prev = b;
  }
  return function move(r, p) {
    const j = blk[r], d = dist[r], B = blocks[j];
    if (d === 0) return 0;                       // A 行: 勝ち手なし
    if (d === m + 1) return p !== h ? h : 0;     // 距離 m+1 の行: 勝ち手は h だけ
    if (p !== d) return d;                       // 直前の A 行へ動く
    // p = d のとき: (i)(ii)(iii) で生じる勝ち手を探す
    if (d % 2 === 0 && B.S[d / 2]) return d / 2;                                   // (i)
    if (j >= 1) {
      const P = blocks[j - 1];
      if ((P.g + d) % 2 === 0 && (P.g + d) / 2 <= m && P.S[(P.g + d) / 2]) return (P.g + d) / 2;  // (ii)
      if (P.g === m + 2 && d === h - 1) return h;                                  // (iii)
    }
    return 0;
  };
}

module.exports = { makeStrategy };

if (require.main === module && process.argv[2] === 'check') {
  const A = require('./solver_dp');
  const B = require('./solver_retro');
  const m0 = +process.argv[3], m1 = +process.argv[4], N = +process.argv[5];
  let count = 0;
  for (let m = m0; m <= m1; m++) {
    const t = A.solve(m, N), tb = B.solve(m, N);
    const move = makeStrategy(m, N);
    for (let r = 0; r <= N; r++) {
      if (t[r] !== tb[r]) { console.error(`ソルバー不一致 m=${m} r=${r}`); process.exit(1); }
      for (let p = 0; p <= m; p++) {
        const k = move(r, p);
        const isP = t[r][p] === 'P';
        if (k === 0) {
          if (!isP) { console.error(`N 局面で手なしと判定: m=${m} (${r},${p})`); process.exit(1); }
        } else {
          if (isP) { console.error(`P 局面で手を返した: m=${m} (${r},${p}) k=${k}`); process.exit(1); }
          if (!(k >= 1 && k <= Math.min(m, r) && k !== p)) { console.error(`非合法手: m=${m} (${r},${p}) k=${k}`); process.exit(1); }
          if (t[r - k][k] !== 'P') { console.error(`行き先が P でない: m=${m} (${r},${p}) k=${k}`); process.exit(1); }
        }
        count++;
      }
    }
  }
  console.log(`# 生成: node code/strategy.js check ${m0} ${m1} ${N}`);
  console.log(`系 W の戦略: 反例なし（${m0} ≤ m ≤ ${m1}, 0 ≤ r ≤ ${N}, 全 p、${count} 局面）`);
}
