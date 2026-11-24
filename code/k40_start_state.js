/*
 * k40_start_state.js — 予想 K40（a = (2^N − 1)/23、m = 3a − 2、N 偶数）で、各周期の始まりのブロック B = qP（P = N/2、q = 0, 1, 2）で
 *                     参照される事実の集合と値を比べる
 *
 * 何を計算するか:
 *   ブロック 0〜3P の間隔を、h から必要な (j, d) だけ遅延評価で求め（BigInt）、ブロック B = 0, P, 2P で参照された距離の個数と、
 *   ブロック 0 と P の両方で参照された距離のうち、値が違うものの個数を出す。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k40_start_state.js 22 44 66 88 110 132 220 > data/k40_start_state.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 予想 K40 の各周期の始まりで参照される事実', `# 生成: node --stack-size=65500 code/k40_start_state.js ${process.argv.slice(2).join(' ')}`,
  'N | 間隔の列が (1^{N/2−1} 0)^3 か | 参照された距離の個数（B = 0 / P / 2P）| B = 0 と P の両方で参照された距離 | そのうち値が違うもの'];
for (const N of process.argv.slice(2).map(Number)) {
  const a = (2n ** BigInt(N) - 1n) / 23n, m = 3n * a - 2n, h = (m + 1n) / 2n, P = N / 2;
  const memo = new Map(), gm = new Map();
  const gap = j => { if (gm.has(j)) return gm.get(j); const r = S(j, h) ? m + 2n : m + 1n; gm.set(j, r); return r; };
  function S(j, d) { const k = j + ':' + d; if (memo.has(k)) return memo.get(k); let r;
    if (j === 0) r = v2(d) % 2 === 0;
    else { r = !(d % 2n === 0n && S(j, d / 2n)); if (r) { const g = gap(j - 1), s = g + d; if (s % 2n === 0n && s / 2n <= m && S(j - 1, s / 2n)) r = false; if (r && g === m + 2n && d === h - 1n) r = false; } }
    memo.set(k, r); return r; }
  const gs = []; for (let j = 0; j < 3 * P; j++) gs.push(gap(j) === m + 2n ? 1 : 0);
  const at = B => new Map([...memo.entries()].filter(([k]) => +k.split(':')[0] === B).map(([k, v]) => [k.split(':')[1], v]));
  const s0 = at(0), s1 = at(P), s2 = at(2 * P); let common = 0, diff = 0;
  for (const [d, v] of s0) if (s1.has(d)) { common++; if (s1.get(d) !== v) diff++; }
  out.push(`${N} | ${gs.join('') === ('1'.repeat(P - 1) + '0').repeat(3) ? 'はい' : 'いいえ'} | ${s0.size} / ${s1.size} / ${s2.size} | ${common} | ${diff}`);
}
console.log(out.join(String.fromCharCode(10)));
