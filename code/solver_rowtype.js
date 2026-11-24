/*
 * solver_rowtype.js — 実装 C：各行の「型」だけを持つ解法（補題 1・系 1.2 による）
 *
 * 何を計算するか:
 *   各行 r の型 type[r] を求める。型は次の 3 つ。
 *     0     … A 行（すべての p で P）
 *     t > 0 … S(t) 行（P は (r, t) だけ）
 *     −1    … E 行（P なし）
 *   勝ち手集合 T(r) = { k : 1 ≤ k ≤ min(m, r)、行 r−k が A 行か S(k) 行 } の大きさで型が決まる
 *   （notes/2026-11-23-claude-1-proof-structure.md の補題 1・定理 K1・系 1.2。[非形式証明]）。
 *     |T| = 0 なら A、|T| = 1 なら S(その要素)、|T| ≥ 2 なら E。
 *   1 行あたり O(m) で、表全体（(m+1) 列）を持たないので、大きな m, r まで計算できる。
 *   漸化式 R（ブロックの考え方）は使わない。
 *
 * 実行方法（リポジトリのルートで）:
 *   node code/solver_rowtype.js verify 60 5000
 *       実装 A・B（全探索）と照合する（1 ≤ m ≤ 60, r ≤ 5000）
 *   node code/solver_rowtype.js extend 300 30000 > data/rowtype_checks.txt
 *       2 ≤ m ≤ 300, r ≤ 30000 で、R（block_rule.js）の行の型と照合し、K4・K5・K6・K9 を直接確かめる
 *   モジュールとして: require('./solver_rowtype').types(m, N) -> Int32Array
 */
'use strict';

function types(m, nMax) {
  const ty = new Int32Array(nMax + 1);
  ty[0] = 0;
  for (let r = 1; r <= nMax; r++) {
    let cnt = 0, last = 0;
    const top = Math.min(m, r);
    for (let k = 1; k <= top; k++) {
      const u = ty[r - k];
      if (u === 0 || u === k) { cnt++; last = k; if (cnt >= 2) break; }
    }
    ty[r] = cnt === 0 ? 0 : cnt === 1 ? last : -1;
  }
  return ty;
}

function rowString(m, u) {
  if (u === 0) return 'P'.repeat(m + 1);
  if (u === -1) return 'N'.repeat(m + 1);
  return 'N'.repeat(u) + 'P' + 'N'.repeat(m - u);
}

module.exports = { types, rowString };

if (require.main === module) {
  const mode = process.argv[2];
  const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
  if (mode === 'verify') {
    const A = require('./solver_dp'), B = require('./solver_retro');
    const M = +process.argv[3], N = +process.argv[4];
    for (let m = 1; m <= M; m++) {
      const ta = A.solve(m, N), tb = B.solve(m, N), ty = types(m, N);
      for (let r = 0; r <= N; r++) {
        if (ta[r] !== tb[r]) { console.error(`A と B が不一致 m=${m} r=${r}`); process.exit(1); }
        if (rowString(m, ty[r]) !== ta[r]) { console.error(`C と全探索が不一致 m=${m} r=${r}`); process.exit(1); }
      }
    }
    console.log(`実装 C は全探索（A・B）と一致: 1 ≤ m ≤ ${M}, 0 ≤ r ≤ ${N}, 全 p`);
  } else if (mode === 'extend') {
    const R = require('./block_rule');
    const M = +process.argv[3], N = +process.argv[4];
    const fails = { K8: [], K4: [], K5: [], K6: [], K9: [] };
    let k6n = 0, k9n = 0;
    for (let m = 2; m <= M; m++) {
      const ty = types(m, N);
      const h = (m + 1) / 2;
      // K8: R の行の型と一致
      {
        let a = 0, prev = null, r = 0;
        while (r <= N) {
          const b = R.nextBlock(m, prev);
          for (let d = 0; d < b.g && r <= N; d++, r++) {
            const want = d === 0 ? 0 : d <= m ? (b.S[d] ? d : -1) : h;
            if (ty[r] !== want) { fails.K8.push(`m=${m} r=${r}`); r = N + 1; break; }
          }
          a += b.g; prev = b;
        }
      }
      // 開始局面 (n,0) が P ⇔ 行 n が A 行
      const isA = n => ty[n] === 0;
      const ev = v2(m + 1) % 2 === 0;
      let mult = true; for (let n = 1; n <= N; n++) if (isA(n) !== (n % (m + 1) === 0)) { mult = false; break; }
      if (mult !== ev) fails.K4.push(`m=${m}`);
      if (!ev) { let f = 0; for (let n = 1; n <= N; n++) if (isA(n)) { f = n; break; } if (f !== m + 2) fails.K5.push(`m=${m} 最初=${f}`); }
      let alt = true; for (let n = 1; n <= N; n++) { const q = n % (2 * m + 3); if (isA(n) !== (q === 0 || q === m + 2)) { alt = false; break; } }
      if (m % 8 === 5) { k6n++; if (!alt) fails.K6.push(`m=${m}`); }
      if (v2(m + 1) === 1) { k9n++; if (alt !== (v2(3 * h + 1) % 2 === 1)) fails.K9.push(`m=${m}`); }
    }
    const res = k => (fails[k].length === 0 ? '反例なし' : '反例 ' + fails[k].slice(0, 20).join(', '));
    console.log(`# 実装 C（行の型）による検証、2 ≤ m ≤ ${M}, 0 ≤ r ≤ ${N}`);
    console.log(`# 生成: node code/solver_rowtype.js extend ${M} ${N}`);
    console.log(`K8（R の行の型と C の一致）: ${res('K8')}`);
    console.log(`K4（倍数型 ⇔ v2(m+1) 偶数、n ≤ ${N}）: ${res('K4')}`);
    console.log(`K5（v2(m+1) 奇数なら最初の P 開始局面は m+2）: ${res('K5')}`);
    console.log(`K6（m ≡ 5 mod 8 の交互型、${k6n} 個、n ≤ ${N}）: ${res('K6')}`);
    console.log(`K9（v2(m+1) = 1 の交互型 ⇔ v2(3h+1) 奇数、${k9n} 個、n ≤ ${N}）: ${res('K9')}`);
  } else {
    console.error('使い方: node code/solver_rowtype.js verify M N | extend M N');
    process.exit(2);
  }
}
