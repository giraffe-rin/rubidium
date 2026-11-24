/*
 * k38_hyp_check.js — Lean の定理 K38_gen の仮定（e₁ = (m+2+u)/2 の v2 が偶数で v − 1 以下）が、
 *                    もとの定理 K38 の仮定（w = v2(u+1) が奇数で 3 ≤ w ≤ v−2、または w ≥ v+1）と同じであることを、数で確かめる
 *
 * 何を計算するか: 奇数 v（5 ≤ v ≤ 15）と u ≡ 3 (mod 4)、u < 2^16 について、m + 1 = 2^v·u とし、2 つの仮定が一致するかを数える。
 * 実行方法（リポジトリのルートで）: node code/k38_hyp_check.js > data/k38_hyp_check.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# K38_gen の仮定（v2(e₁) 偶数かつ ≤ v−1）ともとの仮定（w 奇数で 3 ≤ w ≤ v−2、または w ≥ v+1）の比較', '# 生成: node code/k38_hyp_check.js', 'v | 調べた u の数 | 一致した数'];
for (let v = 5; v <= 15; v += 2) {
  let tot = 0, ok = 0;
  for (let u = 3n; u < 65536n; u += 4n) {
    const m1 = (2n ** BigInt(v)) * u, e1 = (m1 + 1n + u) / 2n, w = v2(u + 1n), ve = v2(e1);
    const a = ve % 2 === 0 && ve <= v - 1, b = (w % 2 === 1 && w >= 3 && w <= v - 2) || w >= v + 1;
    tot++; if (a === b) ok++;
  }
  out.push(`${v} | ${tot} | ${ok}`);
}
console.log(out.join('\n'));
