/*
 * u_class_symbolic.js — 距離 c·u だけを使う 3 値の証明書を、u の合同類ごとに自動で作る（K29 の方法の一般化）
 *
 * 何を計算するか:
 *   v2(m+1) = v（奇数）、u = (m+1)/2^v ≡ u₀ (mod 2^K)（u₀ は奇数）の m について、距離 c·u（1 ≤ c ≤ 2^v − 1）の所属を
 *   3 値（入る T／入らない F／不明 U）で計算する。h = 2^{v−1}u。
 *     O 型のブロック（1 つ前の間隔 m+2）：
 *       偶数の c：S[c] = ¬S[c/2]。
 *       奇数の c：e = ((2^v + c)u + 1)/2。1 つ前のブロックが K3（ブロック 0）か E 型のとき：
 *         v2(c·u₀ + 1) = 1（mod 2^K で決まる）なら e は奇数で必ず入るので F。
 *         v2(c·u₀ + 1) = 2 なら e/2 が奇数で e は入らない（K3：v2(e) = 1、E 型：(i)）ので T。ただし c·u = h − 1 となりうる場合（u = 1）は U。
 *         それ以外（v2 ≥ 3、または K で決まらない）は U。
 *       1 つ前のブロックが O 型のときは、奇数の c はすべて U。
 *     E 型のブロック（1 つ前の間隔 m+1）：奇数の c は T、偶数の c は ¬S[c/2] ∧ ¬S_prev[2^{v−1} + c/2]。
 *   ブロックの種類は h の値で決める（h が U になったら失敗）。
 *   「E 型の直後の O 型のブロック」はいつも同じ計算になる（1 つ前のブロックから使う事実が、K3 と E 型で同じ）。
 *   ブロック 0 の直後のブロック 1 も同じ計算になる。よって、ブロック 1 から始めて、再び「E 型の直後の O 型」に戻ったら周期が閉じる。
 *   出力: v、K ごとに、u₀ の類のうち型が決まった類の割合と、型の一覧。
 * 実行方法（リポジトリのルートで）:
 *   node code/u_class_symbolic.js 5 9 6 > data/u_class_symbolic.txt   （v を 5..9、K を 3..6）
 */
'use strict';
const T = 1, F = 0, U = 2;
const not = x => (x === U ? U : 1 - x);
const and = (x, y) => (x === F || y === F ? F : x === T && y === T ? T : U);
const v2n = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
function run(v, K, u0) {
  const N = 2 ** v, H = N / 2, MOD = 2 ** K;
  const oddRule = c => { const r = (c * u0 + 1) % MOD; const t = r === 0 ? K : v2n(r); if (t === 1) return F; if (t === 2 && t < K) return (c === H - 1 && u0 % MOD === 1 % MOD) ? U : T; if (t === 2) return (c === H - 1) ? U : T; return U; };
  let prev = null, prevO = null;   // prevO: 1 つ前のブロックが O 型か（ブロック 0 は K3 なので false 扱い）
  let gaps = [1];                  // g_0 = m+2（h ∈ S_0）
  let kindO = true; prevO = false;
  for (let n = 1; n <= 4 * v + 8; n++) {
    const S = new Uint8Array(N);
    for (let c = 1; c < N; c++) {
      if (kindO) S[c] = c % 2 === 1 ? (prevO ? U : oddRule(c)) : not(S[c / 2]);
      else S[c] = c % 2 === 1 ? T : and(not(S[c / 2]), not(prev[H + c / 2]));
    }
    if (S[H] === U) return null;
    const g = S[H] === T ? 1 : 0;
    if (n > 1 && kindO && !prevO) return gaps.join('').slice(0, n - 1);   // 周期が閉じた（ブロック 1〜n−1 が 1 周期、ブロック 0 を含めて gaps[0..n−2]）
    gaps.push(g); prevO = kindO; kindO = g === 1; prev = S;
  }
  return null;
}
const [VMIN, VMAX, KMAX] = process.argv.slice(2).map(Number);
const out = ['# 距離 c·u だけを使う 3 値の証明書（u の合同類ごと）', `# 生成: node code/u_class_symbolic.js ${VMIN} ${VMAX} ${KMAX}`, 'v | K | 型が決まった類（u₀ mod 2^K の奇数のうち）| 型ごとの類の数'];
for (let v = VMIN; v <= VMAX; v += 2) for (let K = 3; K <= KMAX; K++) {
  const types = {}; let ok = 0, tot = 0;
  for (let u0 = 1; u0 < 2 ** K; u0 += 2) { tot++; const t = run(v, K, u0); if (t) { ok++; types[t] = (types[t] || 0) + 1; } }
  out.push(`v=${v} | K=${K} | ${ok}/${tot} | ${Object.entries(types).map(([t, c]) => `${t}: ${c}`).join('、')}`);
}
console.log(out.join('\n'));
