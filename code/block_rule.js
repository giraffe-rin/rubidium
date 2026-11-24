/*
 * block_rule.js — 予想「ブロック漸化式」で勝敗表を作り、全探索ソルバーと照合する
 *
 * 何を計算するか:
 *   notes/2026-11-23-claude-1-conjectures.md の [予想] R（ブロック漸化式）だけを使って
 *   勝敗表を組み立てる。ゲームの手は一切読まない。
 *   その表が solver_dp.js / solver_retro.js の表と一致するかを確かめる。
 *   また、漸化式の状態（直前ブロックの集合とギャップ）の繰り返しから、
 *   開始局面の列の前周期と周期を求める。
 *
 *   用語（m ≥ 2）:
 *     A 行   … すべての p で (r, p) が P になる行 r。a_0 = 0 < a_1 < a_2 < …
 *     ブロック j … a_j < r < a_{j+1} の行。d = r − a_j を距離と呼ぶ。g_j = a_{j+1} − a_j をギャップと呼ぶ。
 *     S_j    … ブロック j で、P 局面をちょうど 1 つ持つ行の距離 d の集合（d ≤ m）。
 *              距離 d の行の P 局面は (a_j + d, d) だけ。
 *     h      … m が奇数のとき h = (m+1)/2。
 *   漸化式 R:
 *     d ∈ S_j（1 ≤ d ≤ m）⇔ 次の (i)〜(iii) がどれも起きない。
 *       (i)   d が偶数で d/2 ∈ S_j
 *       (ii)  j ≥ 1、g_{j−1} + d が偶数、e = (g_{j−1} + d)/2 ≤ m、e ∈ S_{j−1}
 *       (iii) j ≥ 1、g_{j−1} = m + 2、d = h − 1
 *     g_j = m + 2（m が奇数で h ∈ S_j のとき）、そうでなければ m + 1。
 *     g_j = m + 2 のとき、距離 m + 1 の行の P 局面は (a_j + m + 1, h) だけ。
 *     その他の行には P 局面がない。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/block_rule.js check 2 100 10000
 *       2 ≤ m ≤ 100、0 ≤ r ≤ 10000 で漸化式の表とソルバーの表を照合する
 *   node code/block_rule.js periods 2 200
 *       各 m について、漸化式の状態が繰り返すまで回し、開始局面列の前周期と周期を出す
 *   モジュールとして: require('./block_rule').table(m, N) -> string[]（solver と同じ形式）
 */
'use strict';

// ブロックを 1 つ進める。prev = { S: Uint8Array(m+2), g } または null（ブロック 0）
function nextBlock(m, prev) {
  const S = new Uint8Array(m + 2);
  const odd = m % 2 === 1;
  const h = (m + 1) / 2;
  for (let d = 1; d <= m; d++) {
    let inS = true;
    if (d % 2 === 0 && S[d / 2]) inS = false;                                  // (i)
    if (inS && prev) {
      const s = prev.g + d;
      if (s % 2 === 0 && s / 2 <= m && prev.S[s / 2]) inS = false;             // (ii)
      if (inS && prev.g === m + 2 && d === h - 1) inS = false;                 // (iii)
    }
    if (inS) S[d] = 1;
  }
  const g = odd && S[h] ? m + 2 : m + 1;
  return { S, g };
}

function table(m, nMax) {
  const rows = [];
  const allP = 'P'.repeat(m + 1);
  const noneP = 'N'.repeat(m + 1);
  const single = p => noneP.slice(0, p) + 'P' + noneP.slice(p + 1);
  let a = 0, prev = null;
  rows.push(allP);
  while (rows.length <= nMax) {
    const blk = nextBlock(m, prev);
    for (let d = 1; d < blk.g && rows.length <= nMax; d++) {
      if (d <= m) rows.push(blk.S[d] ? single(d) : noneP);
      else rows.push(single((m + 1) / 2)); // d = m + 1（g = m + 2 のときだけ）
    }
    if (rows.length <= nMax) rows.push(allP);
    a += blk.g;
    prev = blk;
  }
  return rows;
}

function key(blk) { return blk.g + ':' + Array.from(blk.S).join(''); }

// 開始局面列 (n,0) の P は A 行 a_1, a_2, … の位置。漸化式の状態が初めて繰り返すところを探す。
function periods(m) {
  const seen = new Map();
  let prev = null, j = 0, a = 0;
  const as = [0];
  for (;;) {
    const blk = nextBlock(m, prev);
    if (prev !== null) {
      const k = key(blk);
      if (seen.has(k)) {
        const j0 = seen.get(k);
        // ブロック j0 以降はブロック j 以降と同じ列になる
        return { preBlocks: j0, periodBlocks: j - j0, preRows: as[j0], periodRows: a - as[j0], gaps: [] };
      }
      seen.set(k, j);
    }
    a += blk.g; as.push(a); j++;
    prev = blk;
  }
}

module.exports = { table, nextBlock, periods };

if (require.main === module) {
  const mode = process.argv[2];
  if (mode === 'check') {
    const A = require('./solver_dp');
    const B = require('./solver_retro');
    const m0 = +process.argv[3], m1 = +process.argv[4], N = +process.argv[5];
    let count = 0;
    for (let m = m0; m <= m1; m++) {
      const t = table(m, N), ta = A.solve(m, N), tb = B.solve(m, N);
      for (let r = 0; r <= N; r++) {
        if (ta[r] !== tb[r]) { console.error(`ソルバー同士が不一致: m=${m}, r=${r}`); process.exit(1); }
        if (t[r] !== ta[r]) { console.error(`漸化式とソルバーが不一致: m=${m}, r=${r}: rule=${t[r]} solver=${ta[r]}`); process.exit(1); }
      }
      count += (N + 1) * (m + 1);
    }
    console.log(`一致: ${m0} ≤ m ≤ ${m1}, 0 ≤ r ≤ ${N}, 全 p（${count} 局面）`);
  } else if (mode === 'periods') {
    const m0 = +process.argv[3], m1 = +process.argv[4];
    console.log(`# 漸化式 R の状態の繰り返しから求めた開始局面列 (n,0) の前周期・周期（${m0} ≤ m ≤ ${m1}）`);
    console.log(`# 生成: node code/block_rule.js periods ${m0} ${m1}`);
    console.log('# 列: m | v2(m+1) | ブロックの前周期, 周期 | 表全体の前周期の上界（ブロック単位で数えた値。行単位の最小の前周期はこれより小さいことがある）, 周期（行） | 開始局面列の前周期（n ≤ この値の部分が周期に乗らない。0 なら純周期）, 周期（n） | 開始局面の間隔列の周期ブロック（ギャップ − (m+1) を 0/1 で）');
    for (let m = m0; m <= m1; m++) {
      const res = periods(m);
      let v = 0, x = m + 1; while (x % 2 === 0) { x /= 2; v++; }
      // ギャップ列（前周期 + 周期 2 回分）から、開始局面列の最小の前周期と周期を求める
      let prev = null; const gs = [];
      for (let j = 0; j < res.preBlocks + 2 * res.periodBlocks; j++) { prev = nextBlock(m, prev); gs.push(prev.g - (m + 1)); }
      let best = null;
      for (let L = 1; L <= res.periodBlocks && !best; L++) {
        if (res.periodBlocks % L !== 0) continue;
        for (let p0 = 0; p0 <= res.preBlocks; p0++) {
          let ok = true;
          for (let i = p0; i + L < gs.length; i++) if (gs[i] !== gs[i + L]) { ok = false; break; }
          if (ok) { best = [p0, L]; break; }
        }
      }
      const [p0, L] = best;
      const per = gs.slice(p0, p0 + L).reduce((t, e) => t + e + m + 1, 0);
      // n 単位の最小の前周期: s(n) ≠ s(n+per) となる最後の n（なければ 0）
      const T = gs.reduce((t, e) => t + e + m + 1, 0);
      const isP = new Uint8Array(T + 1);
      { let a = 0; for (const e of gs) { a += e + m + 1; isP[a] = 1; } }
      let rowsBefore = 0;
      for (let n = 1; n + per <= T; n++) if (isP[n] !== isP[n + per]) rowsBefore = n;
      console.log(`m=${m} | ${v} | ${res.preBlocks}, ${res.periodBlocks} | ${res.preRows}, ${res.periodRows} | ${rowsBefore}, ${per} | ${gs.slice(p0, p0 + L).join('')}`);
    }
  } else {
    console.error('使い方: node code/block_rule.js check M0 M1 N | periods M0 M1');
    process.exit(2);
  }
}
