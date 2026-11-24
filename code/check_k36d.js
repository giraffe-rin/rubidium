/*
 * check_k36d.js — 予想 K36d の K 奇数の場合の証明（定理 K36d′）で使う鎖を、各段の形まで確かめる
 *
 * 何を計算するか:
 *   (v, N)（v ≥ 5 奇数、q = 2^v − 3、q | 4^N − 1）について a = (4^N − 1)/q、m = 3a − 2、M = 3a、h = (m+1)/2、K = N − (v+1)/2 とし、
 *   最後の O 型ブロック（相対位置 K+1）の 5h/4 から始まりのブロック（相対位置 0）まで、O 型ブロックの一本道の規則でたどって、次を確かめる。
 *     (1) 5h/4 を v − 3 回半分にすると奇数 5h′（h′ = h/2^{v−1}）になる
 *     (2) e₁ = (M + 5h′)/2（ブロック K）を半分にすると 2a − 5·2^{2K−1}
 *     (3) ブロック j（K ≥ j ≥ 2）で 2a − 5·2^{2j−1} →（半分）a − 5·2^{2j−2}（奇数）→ ブロック j−1 で 2a − 5·2^{2j−3}
 *     (4) ブロック 1 で 2a − 10 → a − 5（偶数）→ (a − 5)/2（奇数）→ ブロック 0 で (7a − 5)/4、その付値は 1
 *     (5) 段数の合計が 2K + v（奇数）、途中に h − 1 や (M + d)/2 > m の段がない
 *   あわせて、a mod 32 を出す（11 のはず）。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k36d.js 5:14 5:28 5:42 7:50 7:100 9:254 11:102 13:387 13:774 15:234 > data/k36d_check.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 定理 K36d′ の鎖の確認', `# 生成: node code/check_k36d.js ${process.argv.slice(2).join(' ')}`, 'v | N | K | a mod 32 | (1)〜(4) | 段数（2K+v）| 例外の段'];
let allOk = true;
for (const arg of process.argv.slice(2)) {
  const [v, N] = arg.split(':').map(Number); const q = 2n ** BigInt(v) - 3n, a = (4n ** BigInt(N) - 1n) / q, m = 3n * a - 2n, M = m + 2n, h = (m + 1n) / 2n, K = N - (v + 1) / 2;
  let d = 5n * h / 4n, j = K + 1, steps = 0, bad = false; const ok = [];
  for (let i = 0; i < v - 3; i++) { if (d % 2n) ok.push(false); d /= 2n; steps++; }
  ok.push(d === 5n * (h >> BigInt(v - 1)) && d % 2n === 1n);   // (1)
  let e = (M + d) / 2n; if (e > m) bad = true; j--; steps++; d = e;
  ok.push(d % 2n === 0n && d / 2n === 2n * a - 5n * 2n ** BigInt(2 * K - 1)); d /= 2n; steps++;   // (2)
  for (; j >= 2; j--) { const y = 2n * a - 5n * 2n ** BigInt(2 * j - 1); if (d !== y) ok.push(false); const z = d / 2n; steps++; if (z % 2n !== 1n || z !== a - 5n * 2n ** BigInt(2 * j - 2)) ok.push(false); if (z === h - 1n) bad = true; e = (M + z) / 2n; if (e > m) bad = true; d = e; steps++; }
  ok.push(d === 2n * a - 10n);   // (3) の終わり
  d /= 2n; steps++; ok.push(d === a - 5n && d % 2n === 0n); d /= 2n; steps++; ok.push(d % 2n === 1n); if (d === h - 1n) bad = true;
  e = (M + d) / 2n; steps++; ok.push(e === (7n * a - 5n) / 4n && v2(e) === 1);   // (4)
  const good = ok.every(Boolean) && steps === 2 * K + v && !bad; if (!good) allOk = false;
  out.push(`${v} | ${N} | ${K} | ${a % 32n} | ${ok.every(Boolean) ? 'すべて成り立つ' : '成り立たない段あり'} | ${steps}（${2 * K + v}）| ${bad ? 'あり' : 'なし'}`);
}
out.push('', allOk ? 'すべての (v, N) で鎖の形と段数が成り立つ' : '成り立たない (v, N) がある');
console.log(out.join(String.fromCharCode(10)));
