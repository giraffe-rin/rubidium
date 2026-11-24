/*
 * k40_closure.js — 予想 K40（a = (2^N − 1)/23、m = 3a − 2、N 偶数）の帰納法の形の確認：
 *                  各周期の始まりのブロック B で参照される事実を分類する
 *
 * 何を計算するか:
 *   ブロック 0〜3P（P = N/2）を遅延評価で求め（BigInt）、B = 0, P, 2P で参照された (d, 値) を次に分類する。
 *     奇数：d が奇数（K3 でも E 型ブロックでも「入る」）
 *     v2=1：v2(d) = 1（d/2 は奇数。K3 でも E 型ブロックでも「入らない」）
 *     d₁ 系：d = (9a − 1)/4 または (9a − 1)/8
 *     その他：上のどれでもない（B = 0 では K3、B ≥ 1 では E 型ブロックの規則でしか値が決まらないもの）
 *   さらに、奇数のものがすべて「入る」、v2=1 のものがすべて「入らない」かを確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k40_closure.js 22 44 66 88 110 132 176 220 > data/k40_closure.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 予想 K40 の各周期の始まりで参照される事実の分類', `# 生成: node --stack-size=65500 code/k40_closure.js ${process.argv.slice(2).join(' ')}`,
  'N | B | 奇数（すべて入る？）| v2=1（すべて入らない？）| d₁ 系（値）| その他（v2: 値）'];
for (const N of process.argv.slice(2).map(Number)) {
  const a = (2n ** BigInt(N) - 1n) / 23n, m = 3n * a - 2n, h = (m + 1n) / 2n, P = N / 2, d1 = (9n * a - 1n) / 4n;
  const memo = new Map(), gm = new Map();
  const gap = j => { if (gm.has(j)) return gm.get(j); const r = S(j, h) ? m + 2n : m + 1n; gm.set(j, r); return r; };
  function S(j, d) { const k = j + ':' + d; if (memo.has(k)) return memo.get(k); let r;
    if (j === 0) r = v2(d) % 2 === 0;
    else { r = !(d % 2n === 0n && S(j, d / 2n)); if (r) { const g = gap(j - 1), s = g + d; if (s % 2n === 0n && s / 2n <= m && S(j - 1, s / 2n)) r = false; if (r && g === m + 2n && d === h - 1n) r = false; } }
    memo.set(k, r); return r; }
  for (let j = 0; j < 3 * P; j++) gap(j);
  for (const B of [0, P, 2 * P]) {
    let odd = 0, oddOk = true, one = 0, oneOk = true; const d1s = [], other = [];
    for (const [k, v] of memo) { const [js, ds] = k.split(':'); if (+js !== B) continue; const d = BigInt(ds), t = v2(d);
      if (d === d1 || d === d1 / 2n) d1s.push((d === d1 ? 'd₁' : 'd₁/2') + '=' + (v ? 'T' : 'F'));
      else if (t === 0) { odd++; if (!v) oddOk = false; }
      else if (t === 1) { one++; if (v) oneOk = false; }
      else other.push(t + ':' + (v ? 'T' : 'F')); }
    out.push(`${N} | ${B} | ${odd}（${oddOk ? 'はい' : 'いいえ'}）| ${one}（${oneOk ? 'はい' : 'いいえ'}）| ${d1s.sort().join(' ') || '−'} | ${other.join(' ') || 'なし'}`);
  }
}
console.log(out.join(String.fromCharCode(10)));
