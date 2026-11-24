/*
 * k61_first_run.js — 命題 K61（命題 K57 の一般化）：族 q·a + r = s·2^N（r = ±1）、m = 3a − 2 の間隔の列の先頭の m+2 の連の長さを、
 *                    ブロック 0（K3）からの h の鎖の b の軌道と、鎖が N を越える場面の規則（補題 K59.1 の r = ±1 版）で予測する
 *
 * 何を計算するか:
 *   ブロック i（g_0..g_{i−1} = m+2 と仮定）の h の鎖：入口 h = (3a − 1)/2（α = 3、c = 1、K = 1）、β = rα + qc、奇数の点で b = β/2^K、
 *   T(b) = (b + 3r)/2^{t(b)}。奇数の段の後の E = K + t が N + v2(c) 未満なら通常の段、等しいか越えたら補題 K59.1（c を c/2^{v2(c)} に置き換え）：
 *     E = N + γ：u = v2(r b′ + q c_o s)、新しい c = r c_o s、K = u、β = b′ + q r c_o s。
 *     E > N + γ（E − N − γ = o）：新しい c = r c_o s、K = 0、β = 2^o b′ + q r c_o s。
 *   ブロック 0 に着いたら、終点の距離の v2 の偶奇（K3）で値を決め、段数の偶奇で反転する。奇数の点で d = h − 1 なら、そこで「入らない」として決める。
 *   (M + d)/2 > m は、奇数の点で d = (ba − c s·2^{N−K})/r を厳密に計算して確かめる（具体的な N なので、そのまま数で比べる）。
 *   予測：g_i = m+2 となる i を 1, 2, … と求め、最初に m+1 になる i（先頭の連の長さ R）を出す。gapsBig（lazy_bigint.js）による実際の列と比べる。
 *   引数：q:r:s:N の並び。enum:Nlo:Nhi:qmax:smax は、Nlo ≤ N ≤ Nhi、q ≤ qmax、s ≤ smax の奇数、r = ±1 の族をすべて並べる。k47rand:個数:種 は、定理 K47 の形の族（v ∈ {3..11}、偶数 ρ ≤ v + 1、r = (2^ρ − 1)/3）を無作為に作る（r = ±1 でない族も含む）。random:個数:種[:N の下限:N の上限] は、q は 3..255 の奇数、r = ±1、s は 1..63 の奇数、N は 30..119（または指定した範囲）の無作為な族（a が正の奇数のもの）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k61_first_run.js 5:1:3:41 5:1:7:43 29:1:15:85 1:-1:3:21 17:5:3:46 random:300:2026 > data/k61_first_run.txt
 *   node --stack-size=65500 code/k61_first_run.js 5:1:3:41 5:1:7:43 29:1:15:85 1:-1:3:21 1:-1:3:23 5:1:83:5 5:1:243:5 k47rand:300:7 random:200:2026 enum:5:12:31:511 > data/k61_first_run.txt
 */
'use strict';
const { gapsBig } = require('./lazy_bigint');
const v2 = x => { x = x < 0n ? -x : x; if (x === 0n) return Infinity; let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const args = []; for (const x of process.argv.slice(2)) {
  if (x.startsWith('enum:')) {   // 小さい族の全列挙：Nlo ≤ N ≤ Nhi、3 ≤ q ≤ qmax の奇数、1 ≤ s ≤ smax の奇数、r = ±1（a が正の奇数のもの）
    const [, nlo, nhi, qmax, smax] = x.split(':').map(Number);
    for (let N = nlo; N <= nhi; N++) for (let q = 3n; q <= BigInt(qmax); q += 2n) for (let t = 1n; t <= BigInt(smax); t += 2n) for (const r of [1n, -1n]) {
      const X = 2n ** BigInt(N); if ((t * X - r) % q !== 0n) continue; const a = (t * X - r) / q; if (a > 0n && a % 2n === 1n) args.push(q + ':' + r + ':' + t + ':' + N); }
    continue;
  }
  if (x.startsWith('k47rand:')) {   // 定理 K47 の形の族：v ∈ {3, 5, 7, 9, 11}、偶数 ρ ≤ v + 1、q = 2^v − 2^ρ + 1、r = (2^ρ − 1)/3、N は 20..139、s は最小の正の奇数（q < 0 なら負の奇数）
    const [, cnt, sd] = x.split(':').map(Number); let seed = sd; const rnd = n => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; }; let k = 0;
    while (k < cnt) { const v = 3 + 2 * rnd(5), rho = 2 + 2 * rnd((v + 1) / 2), q = 2n ** BigInt(v) - 2n ** BigInt(rho) + 1n, r = (2n ** BigInt(rho) - 1n) / 3n, N = 20 + rnd(120), X = 2n ** BigInt(N);
      let found = null; for (let t = 1n; t < 4n * (q < 0n ? -q : q) + 4n && !found; t += 2n) for (const sg of [t, -t]) { if ((sg * X - r) % q === 0n) { const a = (sg * X - r) / q; if (a > 0n && a % 2n === 1n) { found = sg; break; } } }
      if (!found) continue; args.push(q + ':' + r + ':' + found + ':' + N); k++; }
    continue;
  }
  if (!x.startsWith('random:')) { args.push(x); continue; }
  const [, cnt, sd, nlo = 30, nhi = 119] = x.split(':').map(Number); let seed = sd; const rnd = n => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; }; let k = 0;
  while (k < cnt) { const q = BigInt(2 * rnd(127) + 3), r = rnd(2) ? 1n : -1n, s = BigInt(2 * rnd(32) + 1), N = nlo + rnd(nhi - nlo + 1), X = 2n ** BigInt(N);
    if ((s * X - r) % q !== 0n) continue; const a = (s * X - r) / q; if (a <= 0n || a % 2n === 0n) continue; args.push(q + ':' + r + ':' + s + ':' + N); k++; } }
const out = ['# 命題 K61：間隔の列の先頭の m+2 の連の長さの予測（越える場面を含む）', '# 生成: node --stack-size=65500 code/k61_first_run.js ' + process.argv.slice(2).join(' '),
  'q | r | s | N | v | 予測した先頭の連の長さ | 実際 | 越える場面を通った鎖 | 一致'];
let tot = 0, ok = 0, crossUsed = 0, guarded = 0;
for (const arg of args) {
  const [q, r, s] = arg.split(':').slice(0, 3).map(BigInt), N = +arg.split(':')[3], X = 2n ** BigInt(N);
  if ((s * X - r) % q !== 0n) { out.push(arg + '：割り切れない'); continue; }
  const a = (s * X - r) / q, m = 3n * a - 2n, M = 3n * a, h = (m + 1n) / 2n;
  const beta0 = 3n * r + q, v = v2(beta0);
  if (beta0 === 0n || v >= N || a % 2n === 0n) { out.push(`${q} | ${r} | ${s} | ${N} | ${v} | 対象外 | - | - | -`); continue; }
  // ブロック i の h の鎖の値（g_0..g_{i−1} = m+2 を仮定）
  let usedCross = false, why = '';
  const hIn = i => {
    let c = 1n, K = 1, beta = beta0, steps = 0;
    const vb = v2(beta); steps += vb - K; K = vb; let b = beta / 2n ** BigInt(K);
    for (let j = 1; j <= i; j++) {
      // 奇数の点：d = (b a − c s 2^{N−K})/r（K ≤ N のとき整数。そうでなければ有理数で比べる）
      const num = b * a * 2n ** BigInt(Math.max(0, K - N)) - c * s * 2n ** BigInt(Math.max(0, N - K)), den = r * 2n ** BigInt(Math.max(0, K - N));
      if (num % den === 0n) { const d = num / den; if (d === h - 1n) return steps % 2 === 0 ? false : true; if ((M + d) / 2n > m) return steps % 2 === 0 ? true : false; }
      const gam = v2(c), co = c / 2n ** BigInt(gam);
      let x = b + 3n * r; if (x === 0n) { why = 'b + 3r = 0'; return null; } let t = 0; while (x % 2n === 0n) { x /= 2n; t++; } const b2 = x; const E = K + t;
      steps += 1;
      if (E < N + gam) { if (j === i) { const vend = t - 1; const inB = vend % 2 === 0; return steps % 2 === 0 ? inB : !inB; } steps += t - 1; K = E; b = b2; continue; }
      usedCross = true;
      const nk1 = N + gam - K - 1;
      if (E === N + gam) { const inner = r * b2 + q * co * s; const u = v2(inner); if (u === Infinity || u >= N) { why = u === Infinity ? 'inner = 0' : 'u ≥ N'; return null; }   // u ≥ N では v2(b′a − c_o s) = u が言えない（q(b′a − c_o s) = b′s·2^N − inner）
        if (j === i) { const vend = nk1 + u; const inB = vend % 2 === 0; return steps % 2 === 0 ? inB : !inB; }
        steps += nk1 + u; c = r * co * s; K = u; b = (b2 + q * r * co * s) / 2n ** BigInt(u); continue; }
      const o = E - N - gam;
      if (j === i) { const vend = nk1; const inB = vend % 2 === 0; return steps % 2 === 0 ? inB : !inB; }
      steps += nk1; c = r * co * s; K = 0; b = 2n ** BigInt(o) * b2 + q * r * co * s; if (b % 2n === 0n) { why = 'b が偶数'; return null; } continue;
    }
  };
  if ((v - 1) % 2 !== 0) { out.push(`${q} | ${r} | ${s} | ${N} | ${v} | 0（g_0 = m+1） | - | - | -`); continue; }
  let R = null; const IMAX = 4 * N + 20; for (let i = 1; i <= IMAX; i++) { const x = hIn(i); if (x === null) { R = '不明（' + why + '）'; break; } if (!x) { R = i; break; } }
  if (R === null) R = '>' + IMAX;   // 上限まで m+2 が続くと予測
  const g = gapsBig(m, (typeof R === "number" ? R : 4 * N + 20) + 3, 5e7).gaps, real = g.indexOf('0') < 0 ? '>' + g.length : g.indexOf('0');
  const same = typeof R === 'number' ? R === real : (R.startsWith('>') && typeof real === 'string' && real.startsWith('>')); if (typeof R === 'number' || R.startsWith('>')) { tot++; if (same) ok++; if (usedCross) crossUsed++; } else guarded++;
  out.push(`${q} | ${r} | ${s} | ${N} | ${v} | ${R} | ${real} | ${usedCross ? 'あり' : 'なし'} | ${typeof R !== 'number' && !R.startsWith('>') ? '-' : same ? 'はい' : 'いいえ'}`);
}
out.push('', `予測できた ${tot} 個中 ${ok} 個で一致（越える場面を通ったもの ${crossUsed} 個）。条件（b + 3r ≠ 0、inner ≠ 0、u < N）に当たり「不明」で止めたもの ${guarded} 個`);
console.log(out.join('\n'));
