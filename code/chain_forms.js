/*
 * chain_forms.js — 族 a = (4^N − 1)/q（q = 2^v − 3）、m = 3a − 2 で、K36d（K 偶数）の評価がたどる O 型ブロックの一本道の鎖を集め、
 *                  各鎖を「入口（(αa+β)/2^k の形）」「幾何的な部分（2a − c·2^t または M − c·2^t）」「終わり」「段数」に分けて出す
 *
 * 何を計算するか:
 *   k36d_even.js と同じ評価（E₁ と E₂ での h、E₂ での Y = 2a − 22）をし、その中で呼ばれた鎖（ブロック K+1 の距離 d₀ から周期の始まりまで）を集める。
 *   各鎖について、d₀ を (αa+β)/2^k で表し（α は割り算で求め、|β| < 2^40 となる最小の k をとる）、一本道の規則を記号的に進める（奇数 → ((3·2^k + α)a + β)/2^{k+1}、
 *   偶数 → (αa+β)/2^{k+1}）。2·2^k − α = qc かつ β = −c なら 2a − c·4^N/2^k、3·2^k − α = qc かつ β = −c なら M − c·4^N/2^k
 *   （qa + 1 = 4^N による）に入ったとして、そこで入口を終える。
 *   出力：鎖ごとに、d₀、入口の段数と入ったブロック、幾何的な形（2a − c·2^t か M − c·2^t、t を N で表す）、全体の段数（N, K の 1 次式で）、
 *   ブロック 0 での距離の形と v2。複数の N で比べ、形が N によらないかを確かめる。
 * 実行方法（リポジトリのルートで）:
 *   node code/chain_forms.js 7 50 100 150 > data/chain_forms_v7.txt
 */
'use strict';
const [vs, ...Ns] = process.argv.slice(2); const v = +vs; const q = 2n ** BigInt(v) - 3n;
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# K36d（K 偶数）の評価がたどる鎖の形', `# 生成: node code/chain_forms.js ${v} ${Ns.join(' ')}`];
const perN = {};
for (const Ns1 of Ns) {
  const N = +Ns1, a = (4n ** BigInt(N) - 1n) / q, m = 3n * a - 2n, M = 3n * a, h = (m + 1n) / 2n, K = N - (v + 1) / 2, Y = 2n * a - 22n;
  const starts = [];
  const startVal = d => { const t = v2(d); if (t <= 3) return t % 2 === 0; if (d === Y) return true; return null; };
  const valO = (j, d0) => { starts.push(d0); let d = d0, s = 0; while (j > 0) { if (d % 2n === 0n) d /= 2n; else { d = (M + d) / 2n; j--; } s++; } const b = startVal(d); return b === null ? null : (s % 2 === 0 ? b : !b); };
  const memo = new Map();
  const valE = (k, d) => { const key = k + ':' + d; if (memo.has(key)) return memo.get(key); let r; if (d % 2n === 1n) r = true; else { const a1 = valE(k, d / 2n); if (a1 === true) r = false; else { const e = h + d / 2n; let b = false; if (e <= m) b = k === 1 ? valO(K + 1, e) : valE(1, e); r = b === true ? false : (a1 === null || b === null) ? null : true; } } memo.set(key, r); return r; };
  valE(1, h); valE(2, h); valE(2, Y);
  const rows = [];
  for (const d0 of starts) {
    // (αa+β)/2^k で表す
    let al = null, be = null, kk = null; for (let k = 0; k <= 40 && al === null; k++) { const D = d0 * 2n ** BigInt(k); const x = (D + a / 2n) / a; const y = D - x * a; if (y > -(2n ** 40n) && y < 2n ** 40n) { al = x; be = y; kk = k; } }   // α は割り算で求める（β が小さくなる最小の k）
    if (al === null) { rows.push('（d₀ を小さい係数で表せない）'); continue; }
    const name = `(${al}a${be >= 0n ? '+' : ''}${be})/2^${kk}`;
    let A = al, Bt = be, k = kk, j = K + 1, steps = 0, geo = null, d = d0;
    for (let s = 0; s < 20 && j > 0; s++) {
      const c2 = 2n * 2n ** BigInt(k) - A, c3 = 3n * 2n ** BigInt(k) - A;
      if (c2 % q === 0n && Bt === -(c2 / q)) { geo = `2a − ${c2 / q}·2^{2N−${k}}（ブロック ${j}、入口 ${steps} 段）`; break; }
      if (c3 % q === 0n && Bt === -(c3 / q)) { geo = `M − ${c3 / q}·2^{2N−${k}}（ブロック ${j}、入口 ${steps} 段）`; break; }
      if (d % 2n === 1n) { A = 3n * 2n ** BigInt(k) + A; k++; d = (M + d) / 2n; j--; } else { k++; d /= 2n; } steps++;
    }
    // 全体の段数と終わり
    let dd = d0, jj = K + 1, s = 0; while (jj > 0) { if (dd % 2n === 0n) dd /= 2n; else { dd = (M + dd) / 2n; jj--; } s++; }
    let endF = '?'; for (let k2 = 0; k2 <= 40 && endF === '?'; k2++) { const D = dd * 2n ** BigInt(k2); const x = (D + a / 2n) / a; const y = D - x * a; if (y > -(2n ** 40n) && y < 2n ** 40n && x >= -4000n && x <= 4000n && (y > -1000000n && y < 1000000n)) endF = `(${x}a${y >= 0n ? '+' : ''}${y})/2^${k2}`; }
    if (endF === '?') { const r1 = M - dd, r2 = 2n * a - dd; const t1 = r1 > 0n ? v2(r1) : -1, t2 = r2 > 0n ? v2(r2) : -1; if (r1 > 0n && (r1 >> BigInt(t1)) < 100000n) endF = `M − ${r1 >> BigInt(t1)}·2^${t1}`; else if (r2 > 0n && (r2 >> BigInt(t2)) < 100000n) endF = `2a − ${r2 >> BigInt(t2)}·2^${t2}`; }
    rows.push(`${name} | ${geo || '幾何的な形を検出できない'} | 全体 ${s} 段（N = ${N}、K = ${K}：s − 2K = ${s - 2 * K}、s − K = ${s - K}）| 終わり ${endF}（v2 = ${v2(dd)}）`);
  }
  perN[N] = rows; out.push('', `## N = ${N}（K = ${K}）：鎖 ${rows.length} 本`, ...rows);
}
console.log(out.join(String.fromCharCode(10)));
