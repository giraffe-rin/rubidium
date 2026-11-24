/*
 * check_k40a.js — 定理 K40a（a = (2^N − 1)/23、m = 3a − 2、N ≡ 0 (mod 22)、型 1^{N/2−1} 0）の証明で使う 6 本の鎖の各段を、BigInt で確かめる
 *
 * 何を計算するか:
 *   N = 22, 44, …, NMAX について P = N/2、M = 3a、h = (3a−1)/2、X = (13a−5)/8 とし、O 型ブロックの一本道の規則
 *   （奇数 d → 1 つ前のブロックで (M+d)/2、偶数 d → 同じブロックで d/2）で、次の鎖をブロック 0 までたどり、証明に書いた
 *   (i) 入口の各段の値、(ii) 幾何的な部分の形（2a − c·2^t は 2 段で 1 ブロック、t は 2 減る／M − c·2^t は 1 段で 1 ブロック、t は 1 減る）、
 *   (iii) 終わりの各段の値と、ブロック 0 での距離、(iv) 段数、(v) 途中に h − 1 や (M+d)/2 > m の段がないこと、を確かめる。
 *     h（ブロック n、1 ≤ n ≤ P−1）、g = (21a−5)/8、f = (33a−9)/16、h + X/8 = (109a−37)/64、h + X/4 = (61a−21)/32、h + X/2 = (37a−13)/16
 *     （g 以下はブロック P−1 から）
 *   あわせて a mod 4096 = 2137、v2(13a − 5) = 7 を確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node code/check_k40a.js 440 > data/k40a_check.txt
 */
'use strict';
const NMAX = +(process.argv[2] || 440);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 定理 K40a の鎖の確認', `# 生成: node code/check_k40a.js ${NMAX}`, 'N | a mod 4096 | v2(13a−5) | h の鎖（n = 1..P−1）| g | f | h+X/8 | h+X/4 | h+X/2 | 判定'];
let all = true;
for (let N = 22; N <= NMAX; N += 22) {
  const a = (2n ** BigInt(N) - 1n) / 23n, m = 3n * a - 2n, M = 3n * a, h = (3n * a - 1n) / 2n, P = N / 2, X = (13n * a - 5n) / 8n;
  const walk = (j, d0) => { let d = d0, s = 0; const tr = []; while (j > 0) { if (d === h - 1n) return { bad: true }; tr.push([j, d]); if (d % 2n === 0n) d /= 2n; else { const e = (M + d) / 2n; if (e > m) return { bad: true }; d = e; j--; } s++; } return { d, s, tr }; };
  const res = [];
  // h の鎖：段数 2n+1、ブロック 0 で n = 1 なら d₁ = (9a−1)/4、2 ≤ n ≤ P−2 なら 2a − 2^{N−2n−2}（v2 = 1）、n = P−1 なら 2a − 1
  let okh = true; for (let n = 1; n <= P - 1; n++) { const r = walk(n, h); if (r.bad) { okh = false; break; } const want = n === 1 ? (9n * a - 1n) / 4n : 2n * a - 2n ** BigInt(N - 2 * n - 2); if (r.s !== (n === 1 ? 1 : 2 * n + 1) || r.d !== want) okh = false; } res.push(okh);
  const chk = (d0, steps, endTest, entry) => { const r = walk(P - 1, d0); if (r.bad || r.s !== steps || !endTest(r.d)) return false; for (const [i, val] of entry) if (r.tr[i] === undefined || r.tr[i][1] !== val) return false; return true; };
  res.push(chk((21n * a - 5n) / 8n, N, d => d === X, [[1, (45n * a - 5n) / 16n], [3, (141n * a - 5n) / 64n], [4, 2n * a - 5n * 2n ** BigInt(N - 7)]]));
  res.push(chk((33n * a - 9n) / 16n, P, d => d === M - 9n * 2n ** BigInt(P - 4), [[1, (81n * a - 9n) / 32n], [2, (177n * a - 9n) / 64n], [3, M - 9n * 2n ** BigInt(N - 7)]]));
  res.push(chk((109n * a - 37n) / 64n, P, d => d === M - 37n * 2n ** BigInt(P - 6), [[2, (685n * a - 37n) / 256n], [3, M - 37n * 2n ** BigInt(N - 9)]]));
  res.push(chk((61n * a - 21n) / 32n, N, d => d === (61n * a - 21n) / 32n, [[3, (541n * a - 21n) / 256n], [4, 2n * a - 21n * 2n ** BigInt(N - 9)]]));
  res.push(chk((37n * a - 13n) / 16n, P + 1, d => d === M - 13n * 2n ** BigInt(P - 5), [[1, (85n * a - 13n) / 32n], [3, M - 13n * 2n ** BigInt(N - 7)]]));
  const good = res.every(Boolean) && a % 4096n === 2137n && v2(13n * a - 5n) === 7; if (!good) all = false;
  out.push(`${N} | ${a % 4096n} | ${v2(13n * a - 5n)} | ${res.map(x => (x ? '○' : '×')).join(' | ')} | ${good ? '成り立つ' : '成り立たない'}`);
}
out.push('', all ? 'すべての N で証明の各段が成り立つ' : '成り立たない N がある');
console.log(out.join(String.fromCharCode(10)));
