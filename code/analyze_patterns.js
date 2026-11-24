/*
 * analyze_patterns.js — 勝敗表から周期と負け位置（P 局面）の形を調べる
 *
 * 何を計算するか（solver_dp.js と solver_retro.js の両方で表を作り、一致を確認してから調べる）:
 *   各 m（1 ≤ m ≤ M）について、0 ≤ r ≤ N の範囲で
 *   1. 開始局面 (n, 0) のうち P（後手必勝）になる n の一覧と、隣り合う P の間隔の列。
 *      その間隔の列が純周期的かどうかと、その周期ブロック（範囲内で確認）。
 *      P がちょうど m+1 の倍数になっているかどうか。
 *   2. 表全体（すべての p）を「r についての行の列」とみなしたときの前周期と最小周期。
 *      周期 L を 1 から順に試し、r ≥ pre で row(r) = row(r+L) が範囲内すべてで成り立つ
 *      最小の pre を求める。pre ≤ N/2 になる最初の L を採用する（L ≤ N/4 の範囲で探す）。
 *   ここで求めた周期はすべて「範囲内で確かめた」だけで、証明ではない。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/analyze_patterns.js 30 20000 > data/patterns_m1-30_r20000.txt
 */
'use strict';

const A = require('./solver_dp');
const B = require('./solver_retro');

const M = parseInt(process.argv[2] || '30', 10);
const N = parseInt(process.argv[3] || '20000', 10);

const out = [];
out.push(`# restricted-stone-game パターン解析 1<=m<=${M}, 0<=r<=${N}`);
out.push(`# 生成: node code/analyze_patterns.js ${M} ${N}`);
out.push('# 周期はすべて上の範囲内で確かめただけ（[予想] の根拠データ）。');
out.push('# 列: m | 開始局面の P が m+1 の倍数か | 開始局面の P の間隔列の 前周期 / 周期ブロック（n での周期）| 表全体の 前周期, 周期 | 最初の P 開始局面');

for (let m = 1; m <= M; m++) {
  const t = A.solve(m, N);
  const tb = B.solve(m, N);
  for (let r = 0; r <= N; r++) {
    if (t[r] !== tb[r]) { console.error(`2 実装が不一致: m=${m}, r=${r}`); process.exit(1); }
  }

  const P = [];
  for (let n = 1; n <= N; n++) if (t[n][0] === 'P') P.push(n);
  let mult = true;
  for (let n = 1; n <= N; n++) if ((t[n][0] === 'P') !== (n % (m + 1) === 0)) { mult = false; break; }

  const gaps = P.map((x, i) => x - (i ? P[i - 1] : 0));
  let gres = 'P なし';
  if (gaps.length > 0) {
    gres = '周期なし（範囲内）';
    search:
    for (let L = 1; L <= 200; L++) {
      for (let pre = 0; pre <= 60; pre++) {
        if (gaps.length - pre < 3 * L) break;
        let ok = true;
        for (let i = pre; i + L < gaps.length; i++) if (gaps[i] !== gaps[i + L]) { ok = false; break; }
        if (ok) {
          const block = gaps.slice(pre, pre + L);
          const sum = block.reduce((a, b) => a + b, 0);
          gres = `前周期 ${pre} 個 [${gaps.slice(0, pre).join(',')}] / ブロック [${block.join(',')}]（n での周期 ${sum}）`;
          break search;
        }
      }
    }
  }

  let tres = '周期なし（範囲内）';
  for (let L = 1; L <= N / 4; L++) {
    let last = -1;
    for (let r = N - L; r >= 0; r--) if (t[r] !== t[r + L]) { last = r; break; }
    if (last + 1 <= N / 2) { tres = `前周期 ${last + 1}, 周期 ${L}`; break; }
  }

  out.push(`m=${m} | ${mult ? 'はい' : 'いいえ'} | ${gres} | ${tres} | ${P.slice(0, 6).join(',')}${P.length > 6 ? ',…' : ''}`);
}

process.stdout.write(out.join('\n') + '\n');
