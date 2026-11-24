/*
 * u_class_symbolic2.js — u_class_symbolic.js の改良版：O 型ブロックの奇数の距離に、K3 と補題 Q_s を使う
 *
 * 何を計算するか:
 *   v2(m+1) = v（奇数）、u = (m+1)/2^v ≡ u₀ (mod 2^K) の m について、距離 c·u（1 ≤ c ≤ 2^v − 1）の所属を 3 値で計算する。
 *   u_class_symbolic.js との違いは、O 型ブロックの奇数の c の扱いだけ。
 *     e := ((2^v + c)u + 1)/2（(ii) の距離）。t := v2(c·u₀ + 1) が 2^K で決まり（t < K）、t < v のとき、v2(e) = t − 1。
 *     1 つ前のブロックがブロック 0（K3）か、E 型ブロックが s 個続いた最後のブロック（補題 Q_s：v2 ≤ min(2s−1, v−1) で
 *     「入る ⇔ v2 が偶数」）で、t − 1 がその範囲にあり、e ≤ m なら、e ∈ S_prev ⇔ t − 1 が偶数。よって S[c] = T ⇔ t が偶数。
 *     c·u = h − 1 になりうる場合（u₀ ≡ 1 で c = 2^{v−1} − 1）と、範囲の外は U。
 *     1 つ前のブロックが O 型なら U。
 *   ブロック 1 から計算を始め、「E 型ブロックが s 個続いた直後の O 型ブロック」に戻ったとき、その s が、
 *   それまでに使った t − 1 の最大値 τ について 2s − 1 ≥ τ を満たせば、周期が閉じたとする（使った事実がブロック 0 と同じになるため）。
 *   出力：v、K ごとに、u₀ の類のうち型が決まった類と、型の一覧。
 * 実行方法（リポジトリのルートで）:
 *   node code/u_class_symbolic2.js 5 21 6 > data/u_class_symbolic2.txt
 */
'use strict';
const T = 1, F = 0, U = 2;
const not = x => (x === U ? U : 1 - x);
const and = (x, y) => (x === F || y === F ? F : x === T && y === T ? T : U);
const v2n = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
function run(v, K, u0) {
  const N = 2 ** v, H = N / 2, MOD = 2 ** K;
  let tau = 0;   // 使った t − 1 の最大値
  const oddRule = (c, bound) => {
    const r = (c * u0 + 1) % MOD; if (r === 0) return U; const t = v2n(r);
    if (t >= v || t - 1 > bound) return U;   // t < v なら v2(e) = t − 1
    if (c === H - 1 && u0 % MOD === 1) return U;
    if (c >= N - 2) return U;   // e ≤ m を確かめない範囲
    if (t - 1 > tau) tau = t - 1;
    return t % 2 === 0 ? T : F;
  };
  let prev = null, prevKind = 'K3', eRun = 0; const gaps = [1];
  for (let n = 1; n <= 6 * v + 10; n++) {
    const kindO = gaps[gaps.length - 1] === 1;
    if (n > 1 && kindO && prevKind === 'E') { if (2 * eRun - 1 >= tau) return gaps.slice(0, n - 1).join(''); }
    const bound = prevKind === 'K3' ? Infinity : prevKind === 'E' ? 2 * eRun - 1 : -1;
    const S = new Uint8Array(N);
    for (let c = 1; c < N; c++) {
      if (kindO) S[c] = c % 2 === 1 ? (prevKind === 'O' ? U : oddRule(c, bound)) : not(S[c / 2]);
      else S[c] = c % 2 === 1 ? T : and(not(S[c / 2]), not(prev[H + c / 2]));
    }
    if (S[H] === U) return null;
    if (kindO) eRun = 0; else eRun++;
    gaps.push(S[H] === T ? 1 : 0); prevKind = kindO ? 'O' : 'E'; prev = S;
  }
  return null;
}
module.exports = { run };
if (require.main === module) {
  const [VMIN, VMAX, KMAX] = process.argv.slice(2).map(Number);
  const out = ['# 距離 c·u だけを使う 3 値の証明書（u の合同類ごと、K3 と補題 Q_s を使う版）', `# 生成: node code/u_class_symbolic2.js ${VMIN} ${VMAX} ${KMAX}`, 'v | K | 型が決まった類（u₀ mod 2^K の奇数のうち）| 型ごとの u₀ の一覧'];
  for (let v = VMIN; v <= VMAX; v += 2) for (let K = 3; K <= KMAX; K++) {
    const types = {}; let ok = 0, tot = 0;
    for (let u0 = 1; u0 < 2 ** K; u0 += 2) { tot++; const t = run(v, K, u0); if (t) { ok++; (types[t] = types[t] || []).push(u0); } }
    out.push(`v=${v} | K=${K} | ${ok}/${tot} | ${Object.entries(types).map(([t, us]) => `${t}: ${us.length <= 8 ? us.join(',') : us.length + ' 類'}`).join('、')}`);
  }
  console.log(out.join(String.fromCharCode(10)));
}
