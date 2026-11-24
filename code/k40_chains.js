/*
 * k40_chains.js — 予想 K40（a = (2^N − 1)/23、m = 3a − 2、N 偶数）の証明に必要な鎖を、BigInt でたどって表示する
 *
 * 何を計算するか:
 *   指定した N（11 の倍数の偶数）について、周期 P = N/2、M = m + 2 = 3a とする。最後の O 型ブロック P − 1 から、次の 2 つの距離を、
 *   「偶数なら同じブロックで半分、奇数なら 1 つ前のブロックで (M + d)/2」の規則でブロック 0 までたどり、各段で
 *   M − d、2a − d、a − d の 2 進の形（奇数・2^t）を出す。
 *     f = h + d₁/4 = (33a − 9)/16、g = h + d₁/2 = (21a − 5)/8（d₁ = (9a − 1)/4）
 *   あわせて、遅延評価で E 型ブロック P での d₁、d₁/2 と、ブロック P − 1 での f、g の所属を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k40_chains.js 22 44 66 88 > data/k40_chains.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const shape = x => { if (x <= 0n) return '−'; const t = v2(x); return (x >> BigInt(t)).toString() + '·2^' + t; };
const out = ['# 予想 K40（q = 23）の証明に必要な鎖', `# 生成: node --stack-size=65500 code/k40_chains.js ${process.argv.slice(2).join(' ')}`];
for (const N of process.argv.slice(2).map(Number)) {
  const a = (2n ** BigInt(N) - 1n) / 23n, m = 3n * a - 2n, M = m + 2n, h = (m + 1n) / 2n, P = N / 2, d1 = (9n * a - 1n) / 4n;
  // 遅延評価（BigInt、再帰）
  const memo = new Map(), gm = new Map();
  const gap = j => { if (gm.has(j)) return gm.get(j); const r = S(j, h) ? m + 2n : m + 1n; gm.set(j, r); return r; };
  function S(j, d) { const k = j + ':' + d; if (memo.has(k)) return memo.get(k); let r;
    if (j === 0) r = v2(d) % 2 === 0;
    else { r = !(d % 2n === 0n && S(j, d / 2n)); if (r) { const g = gap(j - 1), s = g + d; if (s % 2n === 0n && s / 2n <= m && S(j - 1, s / 2n)) r = false; if (r && g === m + 2n && d === h - 1n) r = false; } }
    memo.set(k, r); return r; }
  const gs = []; for (let j = 0; j <= P; j++) gs.push(gap(j) === m + 2n ? 1 : 0);
  const f = (33n * a - 9n) / 16n, g = (21n * a - 5n) / 8n;
  out.push('', `## N = ${N}（N/2 mod 2 = ${P % 2}）`, `間隔（ブロック 0〜${P}）: ${gs.join('')}`,
    `ブロック ${P}（E 型）: d₁ ${S(P, d1) ? '入る' : '入らない'}、d₁/2 ${S(P, d1 / 2n) ? '入る' : '入らない'}。ブロック ${P - 1}: f ${S(P - 1, f) ? '入る' : '入らない'}、g ${S(P - 1, g) ? '入る' : '入らない'}`);
  for (const [name, d0] of [['f', f], ['g', g]]) {
    out.push(`### ${name} からの鎖（ブロック | 偶奇 | M − d | 2a − d | a − d）`);
    let d = d0, j = P - 1, lines = [];
    for (let s = 0; s < 4 * N && j >= 0; s++) { const odd = d % 2n === 1n; lines.push(`${j} | ${odd ? '奇' : '偶'} | ${shape(M - d)} | ${shape(2n * a - d)} | ${shape(a - d)}`); if (j === 0 && odd) break; if (!odd) d /= 2n; else { d = (M + d) / 2n; j--; } }
    out.push(...(lines.length > 16 ? [...lines.slice(0, 8), '…', ...lines.slice(-8)] : lines));
  }
}
console.log(out.join(String.fromCharCode(10)));
