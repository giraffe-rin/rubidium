/*
 * check_k23_termination.js — 定理 K23 の再帰 F が有限回で終わるか（予想 K24）を調べる
 *
 * 何を計算するか:
 *   v2(m+1) が奇数の m について、x₀ = u = (m+1)/2^v から K23 の再帰 x ↦ x′ = c/2^μ（ℓ, μ が偶数の間）をたどり、
 *   (1) 5 ≤ m ≤ MMAX のすべての m と、(2) 1 ≤ m < 10^15 から線形合同法（種 12345、乱数 N 回）で選んだ奇数の m について、
 *   再帰が終わるか（同じ x が 2 度出たら循環）と、段の数（深さ）の分布を出す。数は BigInt で正確に扱う。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k23_termination.js 1000000 2000000 > data/k23_termination.txt
 *   （第 1 引数 MMAX、第 2 引数 N）
 */
'use strict';
const v2 = x => { let c = 0n; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const MMAX = BigInt(process.argv[2] || 1000000), N = +(process.argv[3] || 2000000);
function depthOf(m) {
  const v = v2(m + 1n); if (v % 2n === 0n) return null;
  let x = (m + 1n) / 2n ** v; const seen = new Set(); let d = 0;
  for (;;) {
    if (seen.has(x)) return 'cycle'; seen.add(x);
    const E = m + 2n - 3n * x; if (E === 0n) return 'E0';
    const l = v2(E < 0n ? -E : E); if (l % 2n === 1n) return d;
    const c = (m + 2n - E / 2n ** l) / 3n; if (c === 0n) return 'c0';
    const mu = v2(c < 0n ? -c : c); if (mu % 2n === 1n) return d;
    x = (c < 0n ? -c : c) / 2n ** mu; d++;
  }
}
function survey(gen) {
  const hist = {}; const odd = []; let n = 0;
  for (const m of gen) { const d = depthOf(m); if (d === null) continue; n++;
    if (typeof d === 'string') { if (odd.length < 20) odd.push(`${m}（${d}）`); continue; } hist[d] = (hist[d] || 0) + 1; }
  return { n, hist, odd };
}
function* all() { for (let m = 5n; m <= MMAX; m += 2n) yield m; }
function* rand() { let s = 12345n; for (let i = 0; i < N; i++) { s = (s * 6364136223846793005n + 1442695040888963407n) % (2n ** 64n); const m = s % (10n ** 15n) + 5n; if (m % 2n === 1n) yield m; } }
const out = ['# 定理 K23 の再帰が有限回で終わるか（予想 K24）', `# 生成: node code/check_k23_termination.js ${MMAX} ${N}`];
for (const [name, g] of [[`(1) 5 ≤ m ≤ ${MMAX} のすべて`, all()], [`(2) m < 10^15 の乱数 ${N} 回（奇数の m のみ）`, rand()]]) {
  const r = survey(g);
  out.push(`${name}: v2(m+1) が奇数の m ${r.n} 個。循環・未定義: ${r.odd.length ? r.odd.join(', ') : 'なし'}。深さの分布: ${Object.entries(r.hist).map(([d, c]) => `${d}: ${c}`).join('、')}`);
}
console.log(out.join('\n'));
