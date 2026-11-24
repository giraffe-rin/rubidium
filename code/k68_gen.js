/*
 * k68_gen.js — m + 1 = 8u、u ≡ r (mod 512) で型が語 w（1 = 間隔 m+2、0 = 間隔 m+1、最後は 00）のとき、
 *   始まりの行の不変量 Blk m 3 で閉じる場合の Lean の証明を生成する。
 * 使い方（lean/ で）: node ../code/k68_gen.js Rubidium/K67b.lean <出力 .lean> <w> <r> [<w> <r> ...]
 * 使う規則（どれも Lean の補題）:
 *   始まりの行 a：Blk m 3。O 型の行 o = p + (m+2)：x 偶数は o_half'、x 奇数は o_odd_iff（行 p の (m+2+x)/2 へ）。
 *   E 型の行 c = p + (m+1)：v2(x) ≤ 1 は blk1_direct（Blk m 1）、v2(x) ≥ 2 は e_iff（(c + x/2) と (p + 4u + x/2)）。
 * u = r + 512t（t = 0..7）で証明の形が同じことを確かめてから出力する。
 */
'use strict';
const fs = require('fs');
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const [tmplF, outF, MODs, ...args] = process.argv.slice(2); const MOD = +MODs;
const tmpl = fs.readFileSync(tmplF, 'utf8');
const blkT = tmpl.slice(tmpl.indexOf("theorem k67b_blk"), tmpl.indexOf('theorem k67b_step'));
const pr = e => e.D === 1 ? (e.B === 0 ? `${e.A} * u` : `${e.A} * u + ${e.B}`) : `(${e.A} * u + ${e.B}) / ${e.D}`;
const ev = (e, u) => (e.A * u + e.B) / e.D;
const half = e => ({ A: e.A, B: e.B, D: e.D * 2 });
const oddUp = e => ({ A: e.A + 8 * e.D, B: e.B + e.D, D: e.D * 2 });
const plus4u = e => ({ A: e.A + 4 * e.D, B: e.B, D: e.D });
const key = e => `${e.A},${e.B},${e.D}`;
const H = { A: 4, B: 0, D: 1 };

function analyse(w, u) {
  const n = w.length, kind = i => i === 0 ? 'S' : (w[i - 1] === '1' ? 'O' : 'E');
  const facts = new Map(), order = [];
  function val(i, e) {
    const k = `${i}|${key(e)}`; if (facts.has(k)) return facts.get(k);
    const x = ev(e, u); if (!Number.isInteger(x) || x < 1) throw new Error('bad x');
    let f; const K = kind(i);
    if (K === 'S') { const t = v2(x); f = { how: 'S', t, val: t > 3 ? null : t % 2 === 0 }; }
    else if (K === 'O') { const c = x % 2 === 0 ? val(i, half(e)) : val(i - 1, oddUp(e)); f = { how: x % 2 === 0 ? 'Oh' : 'Oo', c, val: c.val === null ? null : !c.val }; }
    else { const t = v2(x);
      if (t <= 1) f = { how: 'E1', t, val: t === 0 };
      else { const c1 = val(i, half(e)), c2 = val(i - 1, plus4u(half(e))); f = { how: 'Ee', c1, c2, val: (c1.val === true || c2.val === true) ? false : (c1.val === false && c2.val === false) ? true : null }; f.pick = f.val === false ? (c1.val === true ? 1 : 2) : 0; } }
    f.i = i; f.e = e; f.name = `F${order.length}`; facts.set(k, f); order.push(f); return f;
  }
  const trans = []; for (let i = 0; i < n; i++) trans.push(val(i, H));
  return { order, trans, kind };
}
const usedOf = A => { const U = new Set(); const go = f => { if (U.has(f) ) return; U.add(f); if (f.val === null) { U.add({bad:1}); return; } const kids = f.how === 'Ee' ? (f.pick === 0 ? [f.c1, f.c2] : [f.pick === 1 ? f.c1 : f.c2]) : (f.c ? [f.c] : []); kids.forEach(go); }; A.trans.forEach(go); return A.order.filter(f => U.has(f)); };
const sig = A => usedOf(A).map(f => `${f.i}:${key(f.e)}:${f.how}:${f.val}:${f.pick ?? ''}:${f.t ?? ''}`).join(';');

let out = '';
for (let j = 0; j < args.length; j += 2) {
  const w = args[j], r = +args[j + 1], n = w.length, S = `k68g${r}`;
  if (!w.endsWith('00')) throw new Error('word must end with 00');
  const A = analyse(w, r), s0 = sig(A);
  for (let t = 1; t < 8; t++) if (sig(analyse(w, r + MOD * t)) !== s0) throw new Error(`shape varies: r=${r}, t=${t}`);
  A.trans.forEach((f, i) => { if (f.val !== (w[i] === '1')) throw new Error(`row ${i}: (row + 4u) has the wrong sign`); });
  const R = ['a']; for (let i = 0; i < n; i++) R.push(R[i] + (w[i] === '1' ? ' + (m + 2)' : ' + (m + 1)'));
  const ones = [0]; for (let i = 0; i < n; i++) ones.push(ones[i] + (w[i] === '1' ? 1 : 0));
  const off = i => i === 0 ? '0' : `${i} * m + ${i + ones[i]}`; // R_i - a
  const P = off(n);
  const stmt = f => `${f.val ? '' : '¬ '}IsP m (${R[f.i]} + ${pr(f.e)}) (${pr(f.e)})`;
  const emitted = new Set(), lines = [];
  const T = i => A.trans[i].name;
  const proof = f => {
    const X = pr(f.e);
    if (f.how === 'S' || f.how === 'E1') {
      const B = f.how === 'S' ? 'hblk' : `hb${f.i}`, t = f.t;
      const steps = Array.from({ length: t }, (_, j) => `v2_even (${X}${' / 2'.repeat(j)}) (by omega) (by omega)`).concat([`v2_odd (${X}${' / 2'.repeat(t)}) (by omega)`]).join(',\n        ');
      return `    have hv : v2 (${X}) = ${t} := by\n      have : (${X}) % ${2 ** (t + 1)} = ${2 ** t} := by omega\n      rw [${steps}]\n    ` +
        (f.val ? `exact (${B} _ (by omega) (by omega) (by omega)).mpr (by omega)` : `intro h; have := (${B} _ (by omega) (by omega) (by omega)).mp h; omega`);
    }
    const p = `(${R[f.i - 1]})`;
    if (f.how === 'Oh') { const Z = pr(half(f.e)), L = `o_half' m (4 * u) ${p} (${Z}) hmh hr${f.i - 1} hr${f.i} ${T(f.i - 1)} (by omega) (by omega) (by omega)`;
      return `    rw [show ${X} = 2 * (${Z}) by omega]\n    ` + (f.val ? `exact (${L}).mpr ${f.c.name}` : `exact fun h => (${L}).mp h ${f.c.name}`); }
    if (f.how === 'Oo') { const Y = pr(oddUp(f.e)), L = `o_odd_iff m (4 * u) ${p} (${X}) hmh hr${f.i - 1} hr${f.i} ${T(f.i - 1)} (by omega) (by omega) (by omega) (by omega)`;
      return f.val ? `    refine (${L}).mpr ?_\n    rw [show (m + 2 + ${X}) / 2 = ${Y} by omega]; exact ${f.c.name}`
                   : `    intro h; apply (${L}).mp h\n    rw [show (m + 2 + ${X}) / 2 = ${Y} by omega]; exact ${f.c.name}`; }
    const Z1 = pr(half(f.e)), Z2 = pr(plus4u(half(f.e))), L = `e_iff m (4 * u) ${p} (${X}) hmh hr${f.i - 1} hr${f.i} (by omega) (by omega) (by omega)`;
    const g1 = `rw [show ${X} / 2 = ${Z1} by omega]; exact ${f.c1.name}`, g2 = `rw [show 4 * u + ${X} / 2 = ${Z2} by omega]; exact ${f.c2.name}`;
    if (f.val) return `    refine (${L}).mpr ⟨?_, ?_⟩\n    · ${g1}\n    · ${g2}`;
    return f.pick === 1 ? `    intro h; apply ((${L}).mp h).1\n    ${g1}` : `    intro h; apply ((${L}).mp h).2\n    ${g2}`;
  };
  const emit = f => { if (emitted.has(f.name)) return; if (f.val === null) throw new Error('undetermined fact needed'); const kids = f.how === 'Ee' ? (f.pick === 0 ? [f.c1, f.c2] : [f.pick === 1 ? f.c1 : f.c2]) : [f.c]; for (const c of kids) if (c) emit(c); emitted.add(f.name); lines.push(`  have ${f.name} : ${stmt(f)} := by\n${proof(f)}`); };
  const body = [`  have hmh : m + 1 = 2 * (4 * u) := by omega`, `  have hmo : m % 2 = 1 := by omega`, `  have hh : (m + 1) / 2 = 4 * u := by omega`,
    `  have hv4u : v2 (4 * u) = 2 := by\n    rw [show 4 * u = 2 * (2 * u) by omega, v2_two_mul _ (by omega), v2_two_mul _ (by omega), v2_odd u (by omega)]`, `  have hr0 := hrow`];
  for (let i = 0; i < n; i++) {
    lines.length = 0; emit(A.trans[i]); body.push(...lines);
    body.push(`  have hr${i + 1} : ∀ p, IsP m (${R[i + 1]}) p := ${w[i] === '1' ? `row_long m (${R[i]}) hmo (by omega) hr${i}` : `row_next m (${R[i]}) hr${i}`} (by rw [hh]; exact ${T(i)})`);
    if (w[i] === '0' && i + 1 < n) body.push(`  have hb${i + 1} := blk1_direct m _ hr${i + 1} (odd_of_rows m _ hmo hr${i + 1} (Or.inr ⟨_, rfl, hr${i}⟩))`);
  }
  body.push(`  have hblk' := ${S}_blk m u hmu hu _ hr${n - 1} hb${n - 1} hr${n}`);
  const onesIdx = [...w].map((c, i) => c === '1' ? i : -1).filter(i => i >= 0);
  const stepTy = [...Array.from({ length: n - 1 }, (_, k) => `(∀ p, IsP m (${R[k + 1]}) p)`), `(∀ p, IsP m (a + (${P})) p)`, `Blk m 3 (a + (${P}))`, ...onesIdx.map(i => `IsP m (${R[i]} + 4 * u) (4 * u)`)].join(' ∧\n    ');
  body.push(`  rw [show a + (${P}) = ${R[n]} by omega]`);
  body.push(`  exact ⟨${[...Array.from({ length: n }, (_, k) => `hr${k + 1}`), `hblk'`, ...onesIdx.map(T)].join(', ')}⟩`);
  // final theorem
  const mem = Array.from({ length: n }, (_, i) => `n % (${P}) = ${off(i)}`).join(' ∨ ');
  const nm = Array.from({ length: n - 1 }, (_, k) => `hq${k + 1}`).concat(['_', '_'], onesIdx.map(i => `ht${i}`));
  let dir = '', close = '';
  for (let i = 0; i < n; i++) {
    const hi = i === 0 ? 'hrow' : `hq${i}`;
    dir += `${'  '.repeat(i * (1) )}`;
  }
  // build nested by_cases
  const lines2 = []; let ind = '    ';
  for (let i = 0; i < n; i++) {
    const hi = i === 0 ? 'hrow' : `hq${i}`, o = off(i);
    const last = i === n - 1 && w[i] === '0';
    if (!last) { lines2.push(`${ind}by_cases c${i} : c ≤ ${o} + m`); lines2.push(`${ind}· rw [show a + c = ${R[i]} + (c - (${o})) by omega] at hP`); lines2.push(`${ind}  exact not_isP_of_row m _ (c - (${o})) 0 ${hi} (by omega) (by omega) (by omega) hP`); lines2.push(`${ind}· `); }
    else { lines2.push(`${ind}rw [show a + c = ${R[i]} + (c - (${o})) by omega] at hP`); lines2.push(`${ind}exact not_isP_of_row m _ (c - (${o})) 0 ${hi} (by omega) (by omega) (by omega) hP`); }
    if (!last) ind += '  ';
    if (w[i] === '1') {
      lines2[lines2.length - 1] += `by_cases d${i} : c = ${o} + (m + 1)`;
      lines2.push(`${ind}· rw [d${i}, show a + (${o} + (m + 1)) = ${R[i]} + (m + 1) by omega] at hP`);
      lines2.push(`${ind}  exact not_isP_near m _ _ 0 hmh (by omega) (by omega) ht${i} (by omega) hP`);
      lines2.push(`${ind}· `); ind += '  ';
    }
  }
  // fix dangling "· " lines: merge with next line
  const fin = [];
  for (let k = 0; k < lines2.length; k++) { if (lines2[k].trimEnd().endsWith('·')) { fin.push(lines2[k].replace(/·\s*$/, '· ' + lines2[k + 1].trimStart())); k++; } else fin.push(lines2[k]); }
  const rev = Array.from({ length: n }, (_, i) => i === 0 ? `    · rw [h, Nat.add_zero]; exact hrow 0` : `    · rw [h, show a + (${off(i)}) = ${R[i]} by omega]; exact hq${i} 0`).join('\n');
  out += `
section K68g${r}

variable (m u : Nat) (hmu : m + 1 = 8 * u) (hu : u % ${MOD} = ${r})
include hmu hu

${blkT.replace(/k67b_blk/g, S + '_blk')}theorem ${S}_step (a : Nat) (hrow : ∀ p, IsP m a p) (hblk : Blk m 3 a) :
    ${stepTy} := by
${body.join('\n')}

theorem ${S}_rows : ∀ i, (∀ p, IsP m (i * (${P})) p) ∧ Blk m 3 (i * (${P})) := by
  intro i
  induction i with
  | zero => rw [Nat.zero_mul]; exact ⟨isP_zero m, blk_zero m 3⟩
  | succ i ih =>
    obtain ⟨hrow, hblk⟩ := ih
    obtain ⟨${Array.from({ length: n - 1 }, () => '_').concat(['ha', 'hb']).join(', ')}, _⟩ := ${S}_step m u hmu hu _ hrow hblk
    rw [Nat.succ_mul]; exact ⟨ha, hb⟩

end K68g${r}

/-- 予想 K68 の u ≡ ${r} (mod ${MOD})（${w} 型）：(n, 0) が P ⇔ n mod (${P}) が各行の始まり。-/
theorem K68_${r} (m : Nat) (hm : (m + 1) % ${8 * MOD} = ${8 * r}) (n : Nat) :
    IsP m n 0 ↔ (${mem}) := by
  have hmu : m + 1 = 8 * ((m + 1) / 8) := by omega
  obtain ⟨hrow, hblk⟩ := ${S}_rows m _ hmu (by omega) (n / (${P}))
  obtain ⟨${nm.join(', ')}⟩ := ${S}_step m _ hmu (by omega) _ hrow hblk
  have hdiv : n = (n / (${P})) * (${P}) + n % (${P}) := by
    have := Nat.div_add_mod n (${P})
    rw [Nat.mul_comm] at this; omega
  have hlt : n % (${P}) < ${P} := Nat.mod_lt n (by omega)
  generalize hcc : n % (${P}) = c at hdiv hlt
  generalize ha : n / (${P}) * (${P}) = a at hdiv hrow ${nm.filter(x => x !== '_').join(' ')}
  subst hdiv
  have hmh : m + 1 = 2 * (4 * ((m + 1) / 8)) := by omega
  constructor
  · intro hP
    apply Decidable.byContradiction
    intro hne
${fin.join('\n')}
  · intro h
    rcases h with ${Array.from({ length: n }, () => 'h').join(' | ')}
${rev}
`;
}
fs.writeFileSync(outF, out);
console.log('ok');
