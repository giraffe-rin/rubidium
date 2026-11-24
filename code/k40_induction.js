/*
 * k40_induction.js — 予想 K40（a = (2^N − 1)/23、m = 3a − 2、N 偶数、型 1^{N/2−1} 0）を、N ごとに周期についての帰納法の閉じ方として確かめる
 *
 * 何を計算するか:
 *   周期 P = N/2。周期の始まり B（ブロック 0、または E 型ブロック）の事実として次を仮定する（帰納法の仮定）。
 *     奇数の距離は入る。v2 = 1 の距離は入らない。d₁ = (9a − 1)/4 は入らない。N/2 が偶数なら X は入る
 *     （X は g = (21a − 5)/8 の一本道の鎖の終わり。notes/2026-11-24-claude-1-k40-skeleton.md）。
 *   (1) O 型ブロック n = 1..P−1 での h の値を、一本道の鎖で B までたどって求め、n ≤ P−2 で入り、n = P−1 で入らないことを確かめる。
 *   (2) E 型ブロック E = P で、d₁ と（N/2 が偶数なら）X の値を、E 型の規則（偶数の d：¬[d/2 ∈ S_E] ∧ ¬[h + d/2 ∈ S_{P−1}]、
 *       奇数は入る）と、ブロック P−1 の一本道の鎖で求め、仮定と同じ値になることを確かめる。h は奇数なので E で入り、間隔は m+2。
 *   (3) 途中で、仮定で値が決まらない事実（B での v2 ≥ 2 の距離で、d₁、X 以外）が出ないこと。
 *   すべて成り立てば、その N では帰納法が閉じ、型が確定する（ブロック 0 で仮定が成り立つことは K3 による：v2(d₁) = 3、v2(X) = 4）。
 * 実行方法（リポジトリのルートで）:
 *   node code/k40_induction.js 440 > data/k40_induction.txt
 */
'use strict';
const NMAX = +(process.argv[2] || 440);
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 予想 K40（q = 23、N 偶数）の帰納法の閉じ方の確認', `# 生成: node code/k40_induction.js ${NMAX}`, 'N | N/2 mod 2 | (1) h の値 | (2) E での d₁、X | (3) 決まらない事実 | 判定'];
let all = true;
for (let N = 22; N <= NMAX; N += 22) {
  const a = (2n ** BigInt(N) - 1n) / 23n, m = 3n * a - 2n, M = m + 2n, h = (m + 1n) / 2n, P = N / 2, d1 = (9n * a - 1n) / 4n, even = P % 2 === 0;
  const walk = (j, d0) => { let d = d0, s = 0; while (j > 0) { if (d === h - 1n) return { bad: true }; if (d % 2n === 0n) d /= 2n; else { const e = (M + d) / 2n; if (e > m) return { bad: true }; d = e; j--; } s++; } return { d, s }; };
  const X = walk(P - 1, (21n * a - 5n) / 8n).d;
  let unknown = 0;
  const startVal = d => { if (d === d1) return false; if (d === X && even) return true; const t = v2(d); if (t === 0) return true; if (t === 1) return false; unknown++; return null; };
  const valO = (j, d0) => { const r = walk(j, d0); if (r.bad) { unknown++; return null; } const b = startVal(r.d); return b === null ? null : (r.s % 2 === 0 ? b : !b); };
  // (1)
  let ok1 = true; for (let n = 1; n <= P - 1; n++) { const val = valO(n, h); if (val !== (n <= P - 2)) ok1 = false; }
  // (2) E 型ブロック P
  const memo = new Map();
  const valE = d => { const k = d.toString(); if (memo.has(k)) return memo.get(k); let r; if (d % 2n === 1n) r = true; else { const a1 = valE(d / 2n); if (a1 === true) r = false; else { const e = h + d / 2n; const b = e <= m ? valO(P - 1, e) : false; r = b === true ? false : (a1 === null || b === null) ? null : true; } } memo.set(k, r); return r; };
  const e1 = valE(d1), eX = even ? valE(X) : null; const ok2 = e1 === false && (!even || eX === true);
  const good = ok1 && ok2 && unknown === 0; if (!good) all = false;
  out.push(`${N} | ${P % 2} | ${ok1 ? '型どおり' : '違う'} | d₁ ${e1}${even ? '、X ' + eX : ''} | ${unknown} | ${good ? '閉じる' : '閉じない'}`);
}
out.push('', all ? 'すべての N で帰納法が閉じた' : '閉じない N がある');
console.log(out.join(String.fromCharCode(10)));
