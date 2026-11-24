/*
 * k47_preperiod.js — 定理 K47・K47b の族の各 m の型を推測して周期についての帰納法（prove3）で確定させ、前周期が空か、周期の中の m+2 の連の最大を調べる
 *
 * 何を計算するか:
 *   奇数 v = 3..VMAX と、ρ ∈ {2, 4, …, v−1, v+1} のそれぞれで、q = 2^v − 2^ρ + 1、r = (2^ρ − 1)/3 とし、
 *   偶数 N = v+ρ+1..NMAX（ρ = v+1 では 2v+2..NMAX）について、q·a + r = s·2^N（s は |s| 最小の奇数で、a が正の奇数になるもの）、m = 3a − 2 をとる。
 *   gapsBig（lazy_bigint.js）で J = 400, 800, 1600 ブロックまで計算して型（前周期 pre、周期 w）を推測し
 *   （前周期は列の半分以下、周期が 4 回以上見えるもの）、prove3(m, pre + 周期を c−1 回, 周期を k 回)（c = 1, 2, 4, 8、k = 1..4）で確定させる。
 *   出力：(v, ρ) ごとに、確定した個数、前周期が空だった個数、周期の中の 1 の連の最大（巡回して数える）が R = ⌈(N−v)/ρ⌉ 以上だった個数と、R 未満だった N の一覧。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k47_preperiod.js 11 100 > data/k47_preperiod.txt
 */
'use strict';
const { prove3 } = require('./period_induction');
const { gapsBig } = require('./lazy_bigint');
const VMAX = +(process.argv[2] || 11), NMAX = +(process.argv[3] || 100);
function guess(g) {
  for (let L = 1; 3 * L <= g.length; L++) for (let p = 0; 2 * p <= g.length && p + 3 * L <= g.length; p++) {
    let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; }
    if (ok) return [p, L];
  }
  return null;
}
const out = ['# 定理 K47・K47b の族の型（prove3 で確定）', '# 生成: node --stack-size=65500 code/k47_preperiod.js ' + VMAX + ' ' + NMAX,
  'v | ρ | w | 個数 | 確定 | 前周期が空 | 周期の中の連の最大 ≥ R | 前周期が空でない例（N: p, L） | 周期の中の連の最大が R 未満の N（最大 < R）'];
let T = { n: 0, ok: 0, p0: 0, run: 0 };
for (let v = 3; v <= VMAX; v += 2) {
  const rhos = []; for (let x = 2; x <= v - 1; x += 2) rhos.push(x); rhos.push(v + 1);
  for (const rho of rhos) {
    const q = 2n ** BigInt(v) - 2n ** BigInt(rho) + 1n, r = (2n ** BigInt(rho) - 1n) / 3n;
    let n = 0, ok = 0, p0 = 0, run = 0; const ex = [], short = [];
    for (let N = (rho === v + 1 ? 2 * v + 2 : v + rho + 1); N <= NMAX; N++) {
      if (N % 2) continue;
      const X = 2n ** BigInt(N); let a = null;
      for (let s = 1n; a === null; s += 2n) for (const ss of [s, -s]) { const num = ss * X - r; if (num % q === 0n) { const aa = num / q; if (aa > 0n && aa % 2n === 1n) { a = aa; break; } } }
      const m = 3n * a - 2n, R = Math.ceil((N - v) / rho); n++;
      let ty = null;
      for (const J of [400, 800, 1600]) { const g = gapsBig(m, J, 5e7).gaps; const pl = guess(g); if (pl && pl[0] + 4 * pl[1] <= J) { ty = [g.slice(0, pl[0]), g.slice(pl[0], pl[0] + pl[1])]; break; } }
      if (!ty) { ex.push(`${N}: 推測できない`); continue; }
      const [pre, w] = ty; let hit = false;
      for (const c of [1, 2, 4, 8]) { for (let k = 1; k <= 4 && !hit; k++) hit = prove3(m, pre + w.repeat(c - 1), w.repeat(k)).ok; if (hit) break; }
      if (!hit) { ex.push(`${N}: 確定せず (${pre.length}, ${w.length})`); continue; }
      ok++; if (pre.length === 0) p0++; else if (ex.length < 4) ex.push(`${N}: (${pre.length}, ${w.length})`);
      const k0 = w.indexOf('0'), rot = w.slice(k0) + w.slice(0, k0); const mx = Math.max(...rot.split('0').map(x => x.length));
      if (mx >= R) run++; else short.push(`${N}: ${mx} < ${R}`);
    }
    T.n += n; T.ok += ok; T.p0 += p0; T.run += run;
    out.push(`${v} | ${rho} | ${Math.min(rho, v)} | ${n} | ${ok} | ${p0} | ${run} | ${ex.join('; ') || '-'} | ${short.join('; ') || '-'}`);
  }
}
out.push('', `合計：${T.n} 個、確定 ${T.ok}、前周期が空 ${T.p0}、周期の中の連の最大 ≥ R ${T.run}`);
console.log(out.join('\n'));
