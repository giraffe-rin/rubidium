/*
 * w_class_family_search.js — 予想 K38 で型が決まらない類（w = v2(u+1) が偶数で w ≤ v−1、または w = v）で、周期が伸び続ける族を探す
 *
 * 何を計算するか:
 *   奇数 v と目標の w について、族 a = (c·2^N + b)/q、m = 3a − 2（q は奇数 3..QMAX、c ∈ {1, 3, …, 15}、|b| ≤ BMAX）を調べる。
 *   N ≥ 30 では a mod 2^30 は b/q で決まるので、b は 3a − 1 ≡ 2^v(2^w − 1) (mod 2^{v+w+1}) となる剰余類から選ぶ。
 *   第 5 引数を m にすると、m = (c·2^N + b)/q の形の族を調べる（b は m + 1 ≡ 2^v(2^w − 1) (mod 2^{v+w+1}) の剰余類から選ぶ）。
 *   N は q | c·2^N + b となる N のうち 30 ≤ N ≤ 160 の最初の 4 個（4 個ないものは飛ばす）。
 *   4 個すべてで v2(m+1) = v かつ w = 目標値のものについて、BigInt 版の遅延評価 gapsBig（lazy_bigint.js）で型（前周期 p、周期 L）を推測し、
 *   L が 4 個で真に増え、差が一定のものを「周期が伸び続ける族の候補」として出す。
 *   第 6 引数を any にすると、4 個の N の型が 1 つでも違う族をすべて出す（周期の伸び方を問わない）。
 *   同じ m の列を与える (q, c, b) は、最初の 1 つだけ残す（m の列の最初の値で区別する）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/w_class_family_search.js <v> <w> [QMAX] [BMAX] [a|m] [lin|any] > data/w_class_family_v<v>_w<w>.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const [V, W, QM, BM] = process.argv.slice(2, 6).map(Number); const FORM = process.argv[6] || 'a', CRIT = process.argv[7] || 'lin'; const QMAX = QM || 99, BMAX = BigInt(BM || 4096);
const KK = BigInt(V + W + 1), MOD = 2n ** KK, inv3 = (() => { for (let x = 1n; ; x += 2n) if (3n * x % MOD === 1n) return x; })();
const R = FORM === 'm' ? (2n ** BigInt(V) * (2n ** BigInt(W) - 1n) - 1n) % MOD   // m ≡ R (mod 2^{v+w+1})
  : ((2n ** BigInt(V) * (2n ** BigInt(W) - 1n) + 1n) * inv3) % MOD;   // a ≡ R (mod 2^{v+w+1})
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
function guess(g) {   // 文字列 g の (p, L)。前周期は列の半分以下、周期が 3 回以上見えるものだけ
  for (let L = 1; 3 * L <= g.length; L++) for (let p = 0; 2 * p <= g.length && p + 3 * L <= g.length; p++) {
    let ok = true; for (let i = p; i + L < g.length; i++) if (g[i] !== g[i + L]) { ok = false; break; }
    if (ok) return [p, L];
  }
  return null;
}
function type(m) {
  for (const J of [200, 400, 800]) {
    let r; try { r = gapsBig(m, J, 3e6); } catch (e) { return null; }
    const pl = guess(r.gaps); if (pl && pl[0] + 4 * pl[1] <= J) return { p: pl[0], L: pl[1], per: r.gaps.slice(pl[0], pl[0] + pl[1]), pre: r.gaps.slice(0, pl[0]) };
  }
  return null;
}
const out = ['# w = v2(u+1) の類で周期が伸び続ける族の候補（v = ' + V + '、w = ' + W + '）', '# 生成: node --stack-size=65500 code/w_class_family_search.js ' + V + ' ' + W + ' ' + QMAX + ' ' + BMAX + ' ' + FORM + ' ' + CRIT,
  (FORM === 'm' ? '# m = (c·2^N + b)/q。' : '# a = (c·2^N + b)/q、m = 3a − 2。') + '各族で 30 ≤ N ≤ 160 の最初の 4 個の N の型 (p, L) を出す', 'q | c | b | N の列 | (p, L) の列 | 最大の N の周期'];
const seen = new Set(); let found = 0;
for (let q = 3n; q <= BigInt(QMAX); q += 2n) {
  let o = 1, x = 2n % q; while (x !== 1n) { x = x * 2n % q; o++; }
  for (let c = 1n; c <= 15n; c += 2n) for (let b = ((q * R) % MOD) - MOD * ((BMAX + (q * R) % MOD) / MOD); b <= BMAX; b += MOD) {
    const Ns = []; for (let N = 30; Ns.length < 4 && N <= 160; N++) if ((c * 2n ** BigInt(N) + b) % q === 0n) Ns.push(N);
    if (Ns.length < 4) continue;
    const ms = Ns.map(N => { const t = (c * 2n ** BigInt(N) + b) / q; return FORM === 'm' ? t : 3n * t - 2n; });
    if (!ms.every(m => m > 0n && v2(m + 1n) === V && v2((m + 1n) / 2n ** BigInt(V) + 1n) === W)) continue;
    const id = ms[0].toString(); if (seen.has(id)) continue; seen.add(id);
    const ts = []; for (const m of ms) { const t = type(m); if (!t) break; ts.push(t); }
    if (ts.length < 4) continue;
    const d = ts.slice(1).map((t, i) => t.L - ts[i].L);
    if (CRIT === 'any' ? new Set(ts.map(t => t.pre + '|' + t.per)).size < 2 : !(d[0] > 0 && d.every(x => x === d[0]))) continue;
    found++; const last = ts[3];
    out.push(`${q} | ${c} | ${b} | ${Ns.join(', ')} | ${ts.map(t => '(' + t.p + ', ' + t.L + ')').join(' ')} | ${(last.pre || '-')}|${last.per}`);
  }
}
out.push('', '候補: ' + found + ' 個（条件: ' + (CRIT === 'any' ? '型が N で変わる' : '周期の長さが等差で増える') + '）');
console.log(out.join('\n'));
