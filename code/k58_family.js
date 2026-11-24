/*
 * k58_family.js — 定理 K47 の族の v = 3、ρ = 2（q = 5、r = 1）で N が奇数の場合の型を、周期についての帰納法（prove3）で確定させる（予想 K34 と予想 K58）
 *
 * 何を計算するか:
 *   奇数 N = N0..N1 について、s は 5 | s·2^N − 1 となる最小の正の奇数（N ≡ 1 (mod 4) で 3、N ≡ 3 (mod 4) で 7）、a = (s·2^N − 1)/5、m = 3a − 2、
 *   R = (N − 3)/2 とし、予想した周期
 *     N ≡ 1 (mod 4)：1^{2R} 0 (1^R 0 0)^2（予想 K34、N = 4k + 5、k ≥ 4）
 *     N ≡ 3 (mod 4)：1^{R+2} 0 1^R 0（予想 K58）
 *   について prove3(m, '', w) が成功するか（前周期なし）を調べる。成功すれば、その m の型は確定する。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k58_family.js 21 401 > data/k58_family.txt
 */
'use strict';
const { prove3 } = require('./period_induction');
const [N0, N1] = process.argv.slice(2).map(Number);
const out = ['# 定理 K47 の族（v = 3、ρ = 2）の N 奇数の型の確定（予想 K34・K58）', '# 生成: node --stack-size=65500 code/k58_family.js ' + N0 + ' ' + N1, 'N | N mod 4 | s | 予想した周期 | 結果 | 仮定の数'];
let ok = 0, ng = 0;
for (let N = N0 % 2 ? N0 : N0 + 1; N <= N1; N += 2) {
  let s = 1n; while ((s * 2n ** BigInt(N) - 1n) % 5n !== 0n) s += 2n;
  const a = (s * 2n ** BigInt(N) - 1n) / 5n, m = 3n * a - 2n, R = (N - 3) / 2;
  const w = N % 4 === 1 ? '1'.repeat(2 * R) + '0' + ('1'.repeat(R) + '00').repeat(2) : '1'.repeat(R + 2) + '0' + '1'.repeat(R) + '0';
  const desc = N % 4 === 1 ? `1^${2 * R} 0 (1^${R} 0 0)^2` : `1^${R + 2} 0 1^${R} 0`;
  const r = prove3(m, '', w, 20000, 20000000);
  if (r.ok) ok++; else ng++;
  out.push(`${N} | ${N % 4} | ${s} | ${desc} | ${r.ok ? '確定' : '失敗（' + r.why + '）'} | ${r.A}`);
}
out.push('', `確定 ${ok}、失敗 ${ng}`);
console.log(out.join('\n'));
