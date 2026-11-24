/*
 * family_v3.js — 族 m = 8·u − 1、u = (36·16^k − 1)/5（v2(m+1) = 3）の型を求め、予想 K34 の形と照合する
 *
 * 何を計算するか:
 *   k = 1, 2, … について（BLOCKS·(m+2) < 2^53 の範囲）、type_vs_t.js の typeOf と gapsLazy で、
 *   型と、m+2 の間隔の連の最大の長さ R（ブロック 0〜BLOCKS−1）を求める。
 *   k ≥ 4 では、型が「前周期なし、周期 1^{4k+2} 0 (1^{2k+1} 0 0)^2」と一致するかを調べる。
 *   u の 2 進表示は 111 の後に 0011 が k 個続く形（k ≥ 1）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/family_v3.js 300 > data/family_v3.txt
 */
'use strict';
const { typeOf, gapsLazy } = require('./type_vs_t');
const BLOCKS = +(process.argv[2] || 300);
const pred = k => '-|' + '1'.repeat(4 * k + 2) + '0' + ('1'.repeat(2 * k + 1) + '00').repeat(2);
const out = ['# 族 m = 8(36·16^k − 1)/5 − 1 の型', `# 生成: node --stack-size=65500 code/family_v3.js ${BLOCKS}`, 'k | m | u の 2 進表示 | R | 型 | K34 の形か'];
let ok = 0, ng = 0;
for (let k = 1; ; k++) {
  const u = (36 * 16 ** k - 1) / 5, m = 8 * u - 1; if (BLOCKS * (m + 2) >= 2 ** 53) break;
  const ty = typeOf(m, BLOCKS), g = gapsLazy(m, BLOCKS); let run = 0, R = 0; for (const x of g) { if (x === 1) { run++; if (run > R) R = run; } else run = 0; }
  const c = k < 4 ? '-' : ty === pred(k) ? (ok++, '一致') : (ng++, '不一致');
  out.push(`${k} | ${m} | ${u.toString(2)} | ${R} | ${ty} | ${c}`);
}
out.push('', `K34 の形との照合（k ≥ 4）：一致 ${ok}、不一致 ${ng}`);
console.log(out.join(String.fromCharCode(10)));
