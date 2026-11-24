/*
 * k53_rotation.js — 補題 K53（鎖の写像 T(b) = (b + 2^ρ − 1)/2^{v2(b + 2^ρ − 1)} は ρ 桁の 2 進の語の「次の奇数の巡回シフト」）を確かめる
 *
 * 何を計算するか:
 *   偶数 ρ = 2..RMAX と、0 < b < 2^ρ − 1 のすべての奇数 b について、次を確かめる。
 *     (1) T(b) は、b の ρ 桁の 2 進表示を右に t = v2(b + 2^ρ − 1) 桁回転したものに等しく、t は b の最下位の 1 から次の 1 までの距離（b = 1 なら ρ）。
 *     (2) 軌道は純周期的（b に戻る）。
 *     (3) 閉路の長さ ℓ は、b の語の基本周期 d の中の 1 の個数に等しく、閉路 1 周での t の和は d に等しい。
 *     (4) t の平均 d/ℓ が ρ になるのは b = 1 だけ。
 * 実行方法（リポジトリのルートで）:
 *   node code/k53_rotation.js 22 > data/k53_rotation.txt
 */
'use strict';
const RMAX = +(process.argv[2] || 22);
const out = ['# 補題 K53：鎖の写像 T は ρ 桁の 2 進の語の次の奇数の巡回シフト', '# 生成: node code/k53_rotation.js ' + RMAX, 'ρ | 調べた b の個数 | (1) | (2) | (3) | (4) | 閉路の長さの集合'];
let allOk = true;
for (let rho = 2; rho <= RMAX; rho += 2) {
  const M = 2 ** rho - 1; let n = 0, ok1 = true, ok2 = true, ok3 = true, ok4 = true; const lens = new Set();
  const rot = (x, t) => ((x >>> t) | (x << (rho - t))) & M;   // ρ 桁で右に t 回転（ρ ≤ 30）
  const T = b => { let x = b + M, t = 0; while (x % 2 === 0) { x /= 2; t++; } return [x, t]; };
  for (let b = 1; b < M; b += 2) {
    n++;
    const [tb, t] = T(b);
    let t2 = 1; if (b === 1) t2 = rho; else { while (((b >>> t2) & 1) === 0) t2++; }
    if (tb !== rot(b, t) || t !== t2) ok1 = false;
    // 基本周期 d と、その中の 1 の個数
    let d = rho; for (let dd = 1; dd <= rho; dd++) if (rho % dd === 0 && rot(b, dd) === b) { d = dd; break; }
    let ones = 0; for (let i = 0; i < d; i++) ones += (b >>> i) & 1;
    let x = b, l = 0, sum = 0; do { const [y, tt] = T(x); sum += tt; x = y; l++; } while (x !== b && l <= rho);
    if (x !== b) ok2 = false;
    if (l !== ones || sum !== d) ok3 = false;
    if ((sum === rho * l) !== (b === 1)) ok4 = false;
    lens.add(l);
  }
  if (!(ok1 && ok2 && ok3 && ok4)) allOk = false;
  out.push(`${rho} | ${n} | ${ok1 ? 'はい' : 'いいえ'} | ${ok2 ? 'はい' : 'いいえ'} | ${ok3 ? 'はい' : 'いいえ'} | ${ok4 ? 'はい' : 'いいえ'} | {${[...lens].sort((a, b) => a - b).join(', ')}}`);
}
out.push('', allOk ? 'すべての ρ で (1)〜(4) が成り立つ' : '成り立たないものがある');
console.log(out.join('\n'));
