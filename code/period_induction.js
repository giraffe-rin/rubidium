/*
 * period_induction.js — 個々の m について、予想される型（前周期なしの周期の列 w、末尾は 0）を、周期についての帰納法が閉じることで確定させる
 *
 * 何を計算するか:
 *   m（BigInt）、v = v2(m+1)、周期の列 w（長さ L、w の末尾は 0 で、末尾の 0 の連の長さを s とする）について：
 *   周期の始まり B（ブロック 0、または w の 1 周期の後のブロック）の事実として、次を仮定する（帰納法の仮定）。
 *     (G) 奇数の距離は入る。v2(d) ≤ min(2s − 1, v − 1) の距離は「v2 偶数 ⇔ 入る」
 *         （ブロック 0 では K3。E 型の始まりでは補題 Q_s：直前に m+1 の間隔が s 個続いているため）
 *     (A) 有限個の距離の集合 A と、その値（初めは空）
 *   ブロック B+1, …, B+L を、間隔 g_{B+i} = w[i]（m+2 なら 1）として R で遅延評価する（B の事実は (G)(A) から）。
 *   (G)(A) で決まらない B の事実が出たら、その距離をブロック 0 での値（K3：v2 偶数 ⇔ 入る）とともに A に加え、やり直す。
 *   評価できたら、次を確かめる。
 *     (1) 各ブロック B+i（1 ≤ i ≤ L）で h が入るかが w[i mod L] と一致する（i = L は次の始まり、w[0]）
 *     (2) A の各距離のブロック B+L での値が、A の値と一致する
 *     (0) ブロック 0 の間隔（K3 による）が w[0] と一致する
 *   (0)(1)(2) が成り立てば、ブロック 0 は (G)(A) を満たし（K3）、ブロック B が (G)(A) を満たせばブロック B+L も満たすので、
 *   帰納法により、すべての周期で間隔の列は w のくり返しになり、型が確定する。
 * 使い方（モジュール）: require('./period_induction').prove(m, w) → { ok, why, A, facts }
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/period_induction.js k33odd 199 > data/period_induction_k33odd.txt
 *   node --stack-size=65500 code/period_induction.js k34 30 > data/period_induction_k34.txt
 *   node --stack-size=65500 code/period_induction.js k40odd 429 > data/period_induction_k40odd.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
function prove(m, w, maxRounds = 5000, maxFacts = 3000000) {
  if (m % 2n === 0n) return { ok: false, why: 'm が偶数' };
  const L = w.length, v = v2(m + 1n), h = (m + 1n) / 2n; let s = 0; while (s < L && w[L - 1 - s] === '0') s++;
  if (s === 0) return { ok: false, why: '周期の列の末尾が 0 でない' };
  // ブロック 0 の間隔：m が奇数なら g_0 = m+2 ⇔ h ∈ S_0 ⇔ v2(h) が偶数（K3）。m が偶数なら g_0 = m+1。w[0] と一致すること
  const g0 = (m % 2n === 1n && v2(h) % 2 === 0) ? '1' : '0'; if (g0 !== w[0]) return { ok: false, why: 'ブロック 0 の間隔が w[0] と違う' };
  const bound = Math.min(2 * s - 1, v - 1); const A = new Map();
  for (let round = 0; round < maxRounds; round++) {
    const memo = new Map(); let unknown = null, tooMany = false;
    const gapOf = i => (w[((i % L) + L) % L] === '1' ? m + 2n : m + 1n);   // ブロック B+i の間隔（i ≥ 0）
    const S = (i, d) => {   // ブロック B+i での d の所属（i ≥ 0）
      if (unknown || tooMany) return false;
      const key = i + ':' + d; if (memo.has(key)) return memo.get(key);
      if (memo.size > maxFacts) { tooMany = true; return false; }
      let r;
      if (i === 0) { const t = v2(d); if (t === 0) r = true; else if (t <= bound) r = t % 2 === 0; else if (A.has(d.toString())) r = A.get(d.toString()); else { unknown = d; return false; } }
      else { r = !(d % 2n === 0n && S(i, d / 2n)); if (r) { const g = gapOf(i - 1), sm = g + d; if (sm % 2n === 0n && sm / 2n <= m && S(i - 1, sm / 2n)) r = false; if (r && g === m + 2n && d === h - 1n) r = false; } }
      if (unknown || tooMany) return false; memo.set(key, r); return r;
    };
    let ok1 = true; for (let i = 1; i <= L; i++) { const inH = S(i, h); if (unknown || tooMany) break; if ((inH ? '1' : '0') !== w[i % L]) { ok1 = false; break; } }
    if (tooMany) return { ok: false, why: '事実が多すぎる', A: A.size };
    if (unknown) { A.set(unknown.toString(), v2(unknown) % 2 === 0); continue; }
    if (!ok1) return { ok: false, why: '間隔が w と違う', A: A.size };
    for (const [ds, val] of A) { const got = S(L, BigInt(ds)); if (unknown) break; if (got !== val) return { ok: false, why: 'A の値が次の始まりで再現されない', A: A.size }; }
    if (tooMany) return { ok: false, why: '事実が多すぎる', A: A.size };
    if (unknown) { A.set(unknown.toString(), v2(unknown) % 2 === 0); continue; }
    return { ok: true, A: A.size, facts: memo.size, Aset: [...A.entries()] };   // Aset：仮定の距離と値（調べる用）
  }
  return { ok: false, why: '仮定の集合が収束しない', A: A.size };
}
// prove2：帰納法の出発点をブロック L（1 番目の周期の後の始まり）にとる版。
//   (0′) ブロック 0〜L を K3 から R で計算し、間隔が w（ブロック 0 の分も含めて）と一致する
//   (A) の値は、ブロック L での実際の値（ブロック 0 から計算したもの）とする
//   (1)(2) はブロック L を始まりとして確かめる（ブロック L+1〜2L の間隔が w、(A) がブロック 2L で再現される）
//   これで、ブロック L 以降は帰納法により w のくり返しになる。ブロック 0〜L は (0′) で直接確かめている。
function prove2(m, w, maxRounds = 5000, maxFacts = 3000000) {
  if (m % 2n === 0n) return { ok: false, why: 'm が偶数' };
  const L = w.length, v = v2(m + 1n), h = (m + 1n) / 2n; let s = 0; while (s < L && w[L - 1 - s] === '0') s++;
  if (s === 0) return { ok: false, why: '周期の列の末尾が 0 でない' };
  const g0 = (m % 2n === 1n && v2(h) % 2 === 0) ? '1' : '0'; if (g0 !== w[0]) return { ok: false, why: 'ブロック 0 の間隔が w[0] と違う' };
  const gapOf = i => (w[((i % L) + L) % L] === '1' ? m + 2n : m + 1n);
  // ブロック 0 から（K3）の実際の値
  const base = new Map(); let over = false;
  const T = (j, d) => { if (over) return false; const key = j + ':' + d; if (base.has(key)) return base.get(key); if (base.size > maxFacts) { over = true; return false; } let r;
    if (j === 0) r = v2(d) % 2 === 0; else { r = !(d % 2n === 0n && T(j, d / 2n)); if (r) { const g = gapOf(j - 1), sm = g + d; if (sm % 2n === 0n && sm / 2n <= m && T(j - 1, sm / 2n)) r = false; if (r && g === m + 2n && d === h - 1n) r = false; } }
    if (over) return false; base.set(key, r); return r; };
  for (let j = 1; j <= L; j++) { const x = T(j, h); if (over) return { ok: false, why: '事実が多すぎる' }; if ((x ? '1' : '0') !== w[j % L]) return { ok: false, why: '最初の周期の間隔が w と違う' }; }
  const bound = Math.min(2 * s - 1, v - 1); const A = new Map();
  for (let round = 0; round < maxRounds; round++) {
    const memo = new Map(); let unknown = null, tooMany = false;
    const S = (i, d) => { if (unknown || tooMany) return false; const key = i + ':' + d; if (memo.has(key)) return memo.get(key); if (memo.size > maxFacts) { tooMany = true; return false; } let r;
      if (i === 0) { const t = v2(d); if (t === 0) r = true; else if (t <= bound) r = t % 2 === 0; else if (A.has(d.toString())) r = A.get(d.toString()); else { unknown = d; return false; } }
      else { r = !(d % 2n === 0n && S(i, d / 2n)); if (r) { const g = gapOf(i - 1), sm = g + d; if (sm % 2n === 0n && sm / 2n <= m && S(i - 1, sm / 2n)) r = false; if (r && g === m + 2n && d === h - 1n) r = false; } }
      if (unknown || tooMany) return false; memo.set(key, r); return r; };
    let ok1 = true; for (let i = 1; i <= L; i++) { const x = S(i, h); if (unknown || tooMany) break; if ((x ? '1' : '0') !== w[i % L]) { ok1 = false; break; } }
    if (tooMany) return { ok: false, why: '事実が多すぎる', A: A.size };
    if (unknown) { A.set(unknown.toString(), T(L, unknown)); if (over) return { ok: false, why: '事実が多すぎる' }; continue; }
    if (!ok1) return { ok: false, why: '間隔が w と違う', A: A.size };
    for (const [ds, val] of A) { const got = S(L, BigInt(ds)); if (unknown) break; if (got !== val) return { ok: false, why: 'A の値が次の始まりで再現されない', A: A.size }; }
    if (tooMany) return { ok: false, why: '事実が多すぎる', A: A.size };
    if (unknown) { A.set(unknown.toString(), T(L, unknown)); if (over) return { ok: false, why: '事実が多すぎる' }; continue; }
    return { ok: true, A: A.size, facts: memo.size + base.size };
  }
  return { ok: false, why: '仮定の集合が収束しない', A: A.size };
}
// prove3：前周期 pre（長さ p）と周期 w（長さ L）の型を扱う版。出発点を b = p + L にとる。
//   (0″) ブロック 0〜b を K3 から R で計算し、間隔が pre + w と一致する（ブロック 0 の間隔は K3 から、ブロック i の間隔は h ∈ S_i で確かめる）
//   周期の列 w の末尾が 0 なら、ブロック b の事実として (G)（奇数は入る、v2 ≤ min(2s−1, v−1) は偶奇、補題 Q_s）を使い、
//   末尾が 1 なら (G) は使わない（b の事実はすべて (A) に入れる）。(A) の値はブロック b での実際の値とする。
//   ブロック b からの 1 周期で、間隔が w と一致し、(A) がブロック b + L で再現されることを確かめる。
function prove3(m, pre, w, maxRounds = 20000, maxFacts = 3000000) {
  if (m % 2n === 0n) return { ok: false, why: 'm が偶数' };
  const p = pre.length, L = w.length, v = v2(m + 1n), h = (m + 1n) / 2n, full = pre + w; let s = 0; while (s < L && w[L - 1 - s] === '0') s++;
  const word = i => (i < p ? pre[i] : w[(i - p) % L]);
  const g0 = (m % 2n === 1n && v2(h) % 2 === 0) ? '1' : '0'; if (g0 !== word(0)) return { ok: false, why: 'ブロック 0 の間隔が違う' };
  const gapAbs = j => (word(j) === '1' ? m + 2n : m + 1n); const b = p + L;
  const base = new Map(); let over = false;
  const T = (j, d) => { if (over) return false; const key = j + ':' + d; if (base.has(key)) return base.get(key); if (base.size > maxFacts) { over = true; return false; } let r;
    if (j === 0) r = v2(d) % 2 === 0; else { r = !(d % 2n === 0n && T(j, d / 2n)); if (r) { const g = gapAbs(j - 1), sm = g + d; if (sm % 2n === 0n && sm / 2n <= m && T(j - 1, sm / 2n)) r = false; if (r && g === m + 2n && d === h - 1n) r = false; } }
    if (over) return false; base.set(key, r); return r; };
  for (let j = 1; j <= b; j++) { const x = T(j, h); if (over) return { ok: false, why: '事実が多すぎる' }; if ((x ? '1' : '0') !== word(j)) return { ok: false, why: '最初の部分の間隔が違う' }; }
  const bound = s > 0 ? Math.min(2 * s - 1, v - 1) : -1; const useG = s > 0; const A = new Map();
  const gapRel = i => gapAbs(b + i);
  for (let round = 0; round < maxRounds; round++) {
    const memo = new Map(); let unknown = null, tooMany = false;
    const S = (i, d) => { if (unknown || tooMany) return false; const key = i + ':' + d; if (memo.has(key)) return memo.get(key); if (memo.size > maxFacts) { tooMany = true; return false; } let r;
      if (i === 0) { const t = v2(d); if (useG && t === 0) r = true; else if (useG && t <= bound) r = t % 2 === 0; else if (A.has(d.toString())) r = A.get(d.toString()); else { unknown = d; return false; } }
      else { r = !(d % 2n === 0n && S(i, d / 2n)); if (r) { const g = gapRel(i - 1), sm = g + d; if (sm % 2n === 0n && sm / 2n <= m && S(i - 1, sm / 2n)) r = false; if (r && g === m + 2n && d === h - 1n) r = false; } }
      if (unknown || tooMany) return false; memo.set(key, r); return r; };
    let ok1 = true; for (let i = 1; i <= L; i++) { const x = S(i, h); if (unknown || tooMany) break; if ((x ? '1' : '0') !== w[i % L]) { ok1 = false; break; } }
    if (tooMany) return { ok: false, why: '事実が多すぎる', A: A.size };
    if (unknown) { A.set(unknown.toString(), T(b, unknown)); if (over) return { ok: false, why: '事実が多すぎる' }; continue; }
    if (!ok1) return { ok: false, why: '間隔が w と違う', A: A.size };
    for (const [ds, val] of A) { const got = S(L, BigInt(ds)); if (unknown) break; if (got !== val) return { ok: false, why: 'A の値が次の始まりで再現されない', A: A.size }; }
    if (tooMany) return { ok: false, why: '事実が多すぎる', A: A.size };
    if (unknown) { A.set(unknown.toString(), T(b, unknown)); if (over) return { ok: false, why: '事実が多すぎる' }; continue; }
    return { ok: true, A: A.size, facts: memo.size + base.size };
  }
  return { ok: false, why: '仮定の集合が収束しない', A: A.size };
}
module.exports = { prove, prove2, prove3 };
if (require.main === module) {
  const [mode, lim] = process.argv.slice(2); const N = +lim; const out = [`# 周期についての帰納法による型の確定（${mode}）`, `# 生成: node code/period_induction.js ${mode} ${N}`, 'パラメータ | m の桁数 | 周期 | 結果 | 仮定 A の大きさ | 評価した事実']; let ok = 0, ng = 0;
  for (let n = mode === 'k33odd' ? 7 : mode === 'k34' ? 4 : mode === 'k40odd' ? 33 : 1; n <= N; n += mode === 'k33odd' ? 2 : mode === 'k40odd' ? 22 : 1) {
    let m, w;
    if (mode === 'k33odd') { m = 9n * 2n ** BigInt(n) + 1n; w = '1'.repeat(n - 1) + '0' + '1'.repeat((n - 1) / 2) + '0'; }
    else if (mode === 'k34') { m = 8n * (36n * 16n ** BigInt(n) - 1n) / 5n - 1n; w = '1'.repeat(4 * n + 2) + '0' + ('1'.repeat(2 * n + 1) + '00').repeat(2); }
    else if (mode === 'k40odd') { const a = (2n ** BigInt(n) - 1n) / 23n; m = 3n * a - 2n; w = '1'.repeat((n - 3) / 2) + '0'; }
    const r = prove(m, w); r.ok ? ok++ : ng++;
    out.push(`${n} | ${m.toString().length} | ${w.length} | ${r.ok ? '確定' : '失敗（' + r.why + '）'} | ${r.A} | ${r.facts || '−'}`);
  }
  out.push('', `確定 ${ok}、失敗 ${ng}`); console.log(out.join(String.fromCharCode(10)));
}
