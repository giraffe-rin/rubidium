/*
 * k62_general_r.js — 命題 K62（命題 K61 の一般の奇数 r への拡張）：族 q·a + r = s·2^N（q, r, s 奇数）、m = 3a − 2 の間隔の列の先頭の m+2 の連の長さを、
 *                    b と c を「奇数を分母にもつ有理数」として扱う鎖の記述で予測する
 *
 * 何を計算するか:
 *   恒等式 r(αa − c) = βa − cs·2^N（α, β, c は奇数を分母にもつ有理数でよい）。奇数の点で β = 2^K b、d = (ba − cs·2^{N−K})/r。
 *   T(b) = (b + 3r)/2^{v2(b+3r)}（v2 は分子の 2 の付値）。奇数の段の後の E = K + t が N + γ（γ = v2(c)）に達したら：
 *     E = N + γ：u = v2(b′ + q c_o s / r)、新しい c = c_o s / r、K = u、b = (b′ + q c_o s / r)/2^u。
 *     E > N + γ（o = E − N − γ）：新しい c = c_o s / r、K = 0、b = 2^o b′ + q c_o s / r（奇数の有理数）。
 *   r = ±1 なら 1/r = r で、命題 K61（code/k61_first_run.js）の規則と同じになる。
 *   ブロック i の h の値をブロック 0（K3）から求め、最初に m+1 になる i を予測し、gapsBig（lazy_bigint.js）による実際の列と比べる。
 *   あわせて、命題 K61 の整数の規則（1/r の代わりに r を使う）での予測も出し、一般の r でどちらが正しいかを比べる。
 *   条件：鎖の各奇数点で b + 3r ≠ 0、各 E = N + γ で inner = b′ + q c_o s / r ≠ 0 かつ u < N（u ≥ N では v2 = u が言えないので「不明」で止める）。
 *   引数：q:r:s:N の並び。enum:Nlo:Nhi:qmax:rmax:smax（小さい族の全列挙）、k47rand:個数:種（定理 K47 の形）、random:個数:種（q は 3..255、r は |r| ≤ 4999 の奇数、s は 1..63 の奇数、N は 30..119）。
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k62_general_r.js 29:4641:1:56 29:4641:1:112 497:5:839:109 k47rand:3000:13 random:5000:17 5:1:83:5 5:1:243:5 enum:5:12:31:15:255 > data/k62_general_r.txt
 */
'use strict';
let why = '';   // 「不明」で止めた理由
const { gapsBig } = require('./lazy_bigint');
// 奇数を分母にもつ有理数（分母は正の奇数）
const gcd = (x, y) => { x = x < 0n ? -x : x; y = y < 0n ? -y : y; while (y) [x, y] = [y, x % y]; return x; };
const F = (n, d = 1n) => { if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; return { n: n / g, d: d / g }; };
const fadd = (x, y) => F(x.n * y.d + y.n * x.d, x.d * y.d), fmulI = (x, k) => F(x.n * k, x.d), fdivI = (x, k) => F(x.n, x.d * k);
const fdiv2 = (x, e) => F(x.n / 2n ** BigInt(e), x.d);   // x.n が 2^e で割り切れるとき
const v2b = x => { x = x < 0n ? -x : x; if (x === 0n) return Infinity; let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const v2 = x => v2b(x.n);   // 分母は奇数
function parse(argv) {
  const args = [];
  for (const x of argv) {
    const mk = (cnt, sd, gen) => { let seed = sd; const rnd = n => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n; }; let k = 0, guard = 0; while (k < cnt && guard++ < 100000) { const t = gen(rnd); if (t) { args.push(t); k++; } } };
    if (x.startsWith('k47rand:')) { const [, c, sd] = x.split(':').map(Number); mk(c, sd, rnd => { const v = 3 + 2 * rnd(5), rho = 2 + 2 * rnd((v + 1) / 2), q = 2n ** BigInt(v) - 2n ** BigInt(rho) + 1n, r = (2n ** BigInt(rho) - 1n) / 3n, N = 20 + rnd(120), X = 2n ** BigInt(N);
      for (let t = 1n; t < 4n * (q < 0n ? -q : q) + 4n; t += 2n) for (const sg of [t, -t]) if ((sg * X - r) % q === 0n) { const a = (sg * X - r) / q; if (a > 0n && a % 2n === 1n) return q + ':' + r + ':' + sg + ':' + N; } return null; }); continue; }
    if (x.startsWith('enum:')) {   // 小さい族の全列挙：Nlo ≤ N ≤ Nhi、3 ≤ q ≤ qmax の奇数、|r| ≤ rmax の奇数、1 ≤ s ≤ smax の奇数（a が正の奇数のもの）
      const [, nlo, nhi, qmax, rmax, smax] = x.split(':').map(Number);
      for (let N = nlo; N <= nhi; N++) for (let q = 3n; q <= BigInt(qmax); q += 2n) for (let r0 = 1n; r0 <= BigInt(rmax); r0 += 2n) for (const r of [r0, -r0]) for (let s = 1n; s <= BigInt(smax); s += 2n) {
        const X = 2n ** BigInt(N); if ((s * X - r) % q !== 0n) continue; const a = (s * X - r) / q; if (a > 0n && a % 2n === 1n) args.push(q + ':' + r + ':' + s + ':' + N); }
      continue; }
    if (x.startsWith('random:')) { const [, c, sd] = x.split(':').map(Number); mk(c, sd, rnd => { const q = BigInt(2 * rnd(127) + 3), r = BigInt(2 * rnd(2500) + 1) * (rnd(2) ? 1n : -1n), s = BigInt(2 * rnd(32) + 1), N = 30 + rnd(90), X = 2n ** BigInt(N);
      if ((s * X - r) % q !== 0n) return null; const a = (s * X - r) / q; if (a <= 0n || a % 2n === 0n) return null; return q + ':' + r + ':' + s + ':' + N; }); continue; }
    args.push(x);
  }
  return args;
}
// ブロック i の h の値。rational = true なら有理数の規則、false なら命題 K61 の整数の規則（1/r の代わりに r）
function hIn(fam, i, rational) {
  const { q, r, s, N, a, m, M, h } = fam;
  const inv = x => (rational ? fdivI(x, r) : fmulI(x, r));   // ·/r（整数の規則では ·r）
  let c = F(1n), K = 1, steps = 0; const beta = F(3n * r + q); const vb = v2(beta); steps += vb - K; K = vb; let b = fdiv2(beta, K);
  for (let j = 1; j <= i; j++) {
    // 奇数の点の d = (b a − c s 2^{N−K})/r（有理数として計算し、整数なら例外を確かめる）
    const e = N - K; const term = e >= 0 ? fmulI(c, s * 2n ** BigInt(e)) : F(c.n * s, c.d * 2n ** BigInt(-e));
    const dd = F((b.n * a * term.d - term.n * b.d), b.d * term.d * r);
    if (dd.d === 1n) { const d = dd.n; if (d === h - 1n) return steps % 2 === 0 ? false : true; if ((M + d) / 2n > m) return steps % 2 === 0 ? true : false; }
    const gam = v2(c), co = fdiv2(c, gam === Infinity ? 0 : gam);
    const x = fadd(b, F(3n * r)); if (x.n === 0n) { why = 'b + 3r = 0'; return null; } const t = v2(x); const b2 = fdiv2(x, t); const E = K + t;
    steps += 1;
    if (E < N + gam) { if (j === i) { const ib = (t - 1) % 2 === 0; return steps % 2 === 0 ? ib : !ib; } steps += t - 1; K = E; b = b2; continue; }
    const nk1 = N + gam - K - 1, cs = inv(fmulI(co, s));   // c_o s / r
    if (E === N + gam) { const inner = fadd(b2, fmulI(cs, q)); const u = v2(inner); if (u === Infinity || u >= N) { why = u === Infinity ? 'inner = 0' : 'u ≥ N'; return null; }   // q(b′a − c_o s) = b′s·2^N − r·inner なので、v2 = u は u < N のときだけ
      if (j === i) { const ib = (nk1 + u) % 2 === 0; return steps % 2 === 0 ? ib : !ib; }
      steps += nk1 + u; c = cs; K = u; b = fdiv2(inner, u); continue; }
    const o = E - N - gam;
    if (j === i) { const ib = nk1 % 2 === 0; return steps % 2 === 0 ? ib : !ib; }
    steps += nk1; c = cs; K = 0; b = fadd(fmulI(b2, 2n ** BigInt(o)), fmulI(cs, q)); if (v2(b) !== 0) { why = 'b が偶数'; return null; } continue;
  }
}
const out = ['# 命題 K62：一般の奇数 r での先頭の m+2 の連の長さの予測（b, c を奇数を分母にもつ有理数として扱う）', '# 生成: node --stack-size=65500 code/k62_general_r.js ' + process.argv.slice(2).join(' '),
  'q | r | s | N | 有理数の規則での予測 | 整数の規則（命題 K61 の式）での予測 | 実際 | 一致（有理数） | 一致（整数）'];
let tot = 0, okR = 0, okI = 0, pm1 = 0, unk = 0; const unkWhy = {};
for (const arg of parse(process.argv.slice(2))) {
  const [q, r, s] = arg.split(':').slice(0, 3).map(BigInt), N = +arg.split(':')[3], X = 2n ** BigInt(N);
  if ((s * X - r) % q !== 0n) continue; const a = (s * X - r) / q; if (a <= 0n || a % 2n === 0n) continue;
  const m = 3n * a - 2n, fam = { q, r, s, N, a, m, M: 3n * a, h: (m + 1n) / 2n };
  const beta0 = 3n * r + q, v = v2b(beta0); if (beta0 === 0n || v >= N || (v - 1) % 2 !== 0) continue;
  const pred = rational => { for (let i = 1; i <= 4 * N + 20; i++) { const x = hIn(fam, i, rational); if (x === null) return '不明（' + why + '）'; if (!x) return i; } return '>' + (4 * N + 20); };
  const pR = pred(true), pI = pred(false);
  const lenOf = x => (typeof x === 'number' ? x : String(x).startsWith('>') ? 4 * N + 20 : 0), L = Math.max(lenOf(pR), lenOf(pI), 4) + 3, g = gapsBig(m, L, 5e7).gaps, real = g.indexOf('0') < 0 ? '>' + g.length : g.indexOf('0');
  const isU = x => typeof x === 'string' && x.startsWith('不明');
  const sm = x => x === real || (String(x).startsWith('>') && String(real).startsWith('>'));   // 上限より長いと予測し、実際も上限より長い
  if (isU(pR)) { unk++; unkWhy[pR] = (unkWhy[pR] || 0) + 1; } else { tot++; if (sm(pR)) okR++; if (sm(pI)) okI++; if (r === 1n || r === -1n) pm1++; }
  out.push(`${q} | ${r} | ${s} | ${N} | ${pR} | ${pI} | ${real} | ${isU(pR) ? '-' : sm(pR) ? 'はい' : 'いいえ'} | ${isU(pI) ? '-' : sm(pI) ? 'はい' : 'いいえ'}`);
}
out.push('', `有理数の規則で予測できた ${tot} 個（うち r = ±1 が ${pm1} 個）：有理数の規則で一致 ${okR}、整数の規則で一致 ${okI}`);
out.push(`有理数の規則が条件（b + 3r ≠ 0、inner ≠ 0、u < N）に当たり「不明」で止めたもの ${unk} 個：` + Object.entries(unkWhy).map(([k, n]) => k + ' ' + n + ' 個').join('、'));
console.log(out.join('\n'));
