/*
 * k43_start_structure.js — v2(m+1) = v ≥ 5（奇数）の m で、周期の始まりのブロックの状態の構造と、1 周期の計算の依存先を調べる
 *
 * 何を計算するか:
 *   指定した (v, u) について m = 2^v u − 1 とし、block_rule.js の nextBlock で 40 ブロックを作る。
 *   「間隔 m+1 の直後で間隔が m+2 のブロック」を周期の始まり s_0 < s_1 < … とし、次を出す。
 *     (a) 各 s_k で、v2 ≤ v − 1 の距離がすべて「v2 偶数 ⇔ 入る」（K3 型）か
 *     (b) 各 s_k での 2^v d′（1 ≤ d′ ≤ u − 1）の値の列（k ごとに同じか）
 *     (c) ブロック s_1 の全距離の値を、R をさかのぼってたどったとき、ブロック s_0 で参照される距離のうち v2 ≥ v のもの（d′ と値）
 * 実行方法（リポジトリのルートで）:
 *   node code/k43_start_structure.js 5:5 5:7 5:9 5:23 5:39 7:5 7:7 7:23 > data/k43_start_structure.txt
 */
'use strict';
const { nextBlock } = require('./block_rule');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const out = ['# v2(m+1) ≥ 5 の m の周期の始まりの状態の構造', `# 生成: node code/k43_start_structure.js ${process.argv.slice(2).join(' ')}`];
for (const arg of process.argv.slice(2)) {
  const [v, u] = arg.split(':').map(Number), m = 2 ** v * u - 1; let pv = null; const B = [];
  for (let j = 0; j < 40; j++) { pv = nextBlock(m, pv); B.push(pv); }
  const g = B.map(b => (b.g === m + 2 ? 1 : 0)); const st = []; for (let j = 1; j < 40; j++) if (g[j - 1] === 0 && g[j] === 1) st.push(j);
  const k3 = j => { for (let d = 1; d <= m; d++) { const t = v2(d); if (t <= v - 1 && (B[j].S[d] === 1) !== (t % 2 === 0)) return false; } return true; };
  const hi = j => { let s = ''; for (let dp = 1; dp <= u - 1; dp++) s += B[j].S[2 ** v * dp] ? '1' : '0'; return s || '−'; };
  const [s0, s1] = st; const seen = new Set(), at = new Set(); const stack = []; for (let d = 1; d <= m; d++) stack.push([s1, d]);
  while (stack.length) { const [j, d] = stack.pop(); const k = j + ':' + d; if (seen.has(k)) continue; seen.add(k); if (j === s0) { at.add(d); continue; } if (d % 2 === 0) stack.push([j, d / 2]); const s = B[j - 1].g + d; if (s % 2 === 0 && s / 2 <= m) stack.push([j - 1, s / 2]); }
  const refHi = [...at].filter(d => v2(d) >= v).sort((a, b) => a - b).map(d => `${d / 2 ** v}:${B[s0].S[d] ? 'T' : 'F'}`);
  out.push('', `## v = ${v}、u = ${u}（m = ${m}、u mod 4 = ${u % 4}）`, `間隔（ブロック 0〜15）: ${g.slice(0, 16).join('')}、周期の始まり: ${st.slice(0, 4).join(', ')}`,
    `(a) K3 型か: ${st.slice(0, 4).map(k3).map(x => (x ? 'はい' : 'いいえ')).join(', ')}`,
    `(b) 2^v d′ の値（d′ = 1..u−1）: ${st.slice(0, 4).map(hi).join(' / ')}`,
    `(c) s₁ の計算で s₀ から参照される v2 ≥ v の距離（d′:値）: ${refHi.join(' ') || 'なし'}（参照される距離は全部で ${at.size} 個）`);
}
console.log(out.join(String.fromCharCode(10)));
