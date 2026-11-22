/*
 * k12_symbolic.js — 予想 K12′ の十分性（Q_k が奇数 ⇒ 1(10)^k 型）を、k ごとに w によらない記号の証明書で確かめる
 *
 * 何を計算するか:
 *   v2(m+1) = 1、h = (m+1)/2、3h+1 = 4^k w（w 奇数）、Q_k = (m+2+w)/2 が奇数（⇔ w ≡ 7 (mod 12)、w ≥ 7）とする。
 *   1(10)^k 型を仮定したときのブロックの種類（周期 L = 2k+1 の剰余 r ごとに E 型か O 型か）のもとで、
 *   「剰余 r のブロックに距離 x が入るか」を、ブロック漸化式 R だけから記号的に求める。
 *   距離 x は次の 3 種類の形に限る（c, b は整数）。
 *     W(c) = c·w、H(c) = h + c·w、Q(b) = Q_k + b·w
 *   範囲の条件は w ≥ 7 なら w によらない（notes/2026-11-23-claude-1-proof-k12-general.md の補題 B）:
 *     W(c) ≤ m ⇔ c ≤ (2·4^k − 2)/3、H(c) ≤ m ⇔ c ≤ (4^k − 1)/3。
 *   偶奇も w によらない（w, Q_k, h は奇数）。W(c) は c の偶奇、H(c) は c+1 の偶奇、Q(b) は b+1 の偶奇。
 *   各 r で h が入るかを求め、1(10)^k 型が要求する値と一致するかを見る。
 *   r = 0 の事実はブロック 0（定理 K3）とも一致する必要があるので、それも確かめる。
 *   途中で上の 3 種類の形にならない値が出たり、依存が循環したりしたら「失敗」とする。
 *   出力: k ごとに、成功か失敗か、使った事実の個数。
 *
 * 実行方法（リポジトリのルートで）:
 *   node --stack-size=65500 code/k12_symbolic.js 2 16 crosscheck > data/k12_symbolic.txt
 *   （crosscheck を付けると、各 k で実際の m（m ≤ 3·10^6、最大 3 個）でブロック漸化式を回し、記号の値と照合する）
 */
'use strict';

const K0 = +(process.argv[2] || 2), K1 = +(process.argv[3] || 10);
const cross = process.argv[4] === 'crosscheck';
const v2b = x => { let c = 0n; while (x % 2n === 0n) { x /= 2n; c++; } return c; };

function certify(k) {
  const K = BigInt(k), L = 2 * k + 1;
  const P = 4n ** K;                     // 4^k
  const Wmax = (2n * P - 2n) / 3n, Hmax = (P - 1n) / 3n;
  // ブロックの種類: r = 0 は E（j ≥ L）、r = 1 は O、r が 2 以上の偶数なら O、3 以上の奇数なら E
  const isE = r => r === 0 || (r >= 3 && r % 2 === 1);
  // 1(10)^k 型での g_r（1 = m+2）。h ∈ S_r ⇔ g_r = m+2
  const wantH = r => (r === 0 || r % 2 === 1);
  const memo = new Map(), busy = new Set();
  let fail = null;
  const parity = o => o.t === 'W' ? o.c & 1n : o.t === 'H' ? (o.c + 1n) & 1n : (o.c + 1n) & 1n; // 1 = 奇数
  const valid = o => o.t === 'W' ? (o.c >= 1n && o.c <= Wmax) : o.t === 'H' ? (o.c >= 0n && o.c <= Hmax) : null;
  const name = o => `${o.t}(${o.c})`;
  // 剰余 r のブロックに o が入るか
  function mem(r, o) {
    const key = r + ':' + name(o);
    if (memo.has(key)) return memo.get(key);
    if (busy.has(key)) { fail = fail || `循環 ${key}`; return false; }
    busy.add(key);
    let res;
    const odd = parity(o) === 1n;
    if (o.t === 'Q') {
      if (isE(r) && odd) res = true; else { fail = fail || `Q 型の値を ${isE(r) ? 'E' : 'O'} 型・${odd ? '奇' : '偶'}数で使った r=${r} ${name(o)}`; res = false; }
    } else if (isE(r) && odd) res = true;               // E 型の奇数は入る
    else {
      // (i)
      let i = false;
      if (!odd) {
        if (o.t === 'W') i = mem(r, { t: 'W', c: o.c / 2n });
        else { fail = fail || `(i) で形の外 r=${r} ${name(o)}`; }
      }
      if (i) res = false;
      else {
        // (ii)
        const pr = (r - 1 + L) % L;
        let e = null;
        if (isE(r)) { // g = m+1 = 2h: x 偶数なら e = h + x/2
          if (!odd) { if (o.t === 'W') e = { t: 'H', c: o.c / 2n }; else fail = fail || `(ii)E で形の外 r=${r} ${name(o)}`; }
        } else {      // g = m+2: x 奇数なら e = (m+2+x)/2
          if (odd) {
            if (o.t === 'W') e = { t: 'Q', c: (o.c - 1n) / 2n };          // (m+2+cw)/2 = Q + (c−1)/2·w
            else e = { t: 'W', c: (P + o.c) / 2n };                         // (3h+1+cw)/2 = (4^k+c)/2·w
          }
        }
        let ii = false;
        if (e) {
          const ok = e.t === 'Q' ? (e.c * 2n + 1n <= Wmax) : valid(e);    // Q(b) ≤ m ⇔ (2b+1) ≤ Wmax（補題 B）
          if (ok) ii = mem(pr, e);
        }
        res = !ii;  // (iii) は h−1 で、どの形とも等しくない（補題 C）
      }
    }
    busy.delete(key); memo.set(key, res);
    return res;
  }
  const hs = [];
  for (let r = 0; r < L; r++) { const v = mem(r, { t: 'H', c: 0n }); hs.push(v); if (v !== wantH(r)) fail = fail || `h の所属が型と合わない r=${r}`; }
  // r = 0 の事実と定理 K3 の一致
  for (const [key, v] of memo) {
    const [r, nm] = key.split(':'); if (r !== '0') continue;
    const t = nm[0], c = BigInt(nm.slice(2, -1));
    let k3;
    if (t === 'W') k3 = v2b(c) % 2n === 0n;                  // v2(cw) = v2(c)
    else { const o = { t, c }; if (parity(o) === 1n) k3 = true; else { fail = fail || `r=0 の偶数 ${nm} の K3 の値が w によらず決まらない`; continue; } }
    if (k3 !== v) fail = fail || `r=0 の ${nm} が K3 と合わない`;
  }
  return { k, ok: !fail, fail, n: memo.size, memo };
}

// 照合用：実際の m でブロック漸化式を回し、記号の値と比べる
function crosscheck(res) {
  const { nextBlock } = require('./block_rule');
  const k = res.k, L = 2 * k + 1; let done = 0, bad = 0;
  for (let w = 7; done < 3; w += 12) {
    const P = 4 ** k; if ((P * w - 1) % 3) continue;
    const h = (P * w - 1) / 3, m = 2 * h - 1; if (m > 3e6) break;
    const Q = (m + 2 + w) / 2;
    let p = null; const B = []; for (let j = 0; j < 3 * L; j++) { p = nextBlock(m, p); B.push(p.S); }
    for (const [key, v] of res.memo) {
      const [r, nm] = key.split(':'); const t = nm[0], c = Number(nm.slice(2, -1));
      const x = t === 'W' ? c * w : t === 'H' ? h + c * w : Q + c * w;
      for (let j = +r; j < 3 * L; j += L) if (!!B[j][x] !== v) bad++;
    }
    done++;
  }
  return { done, bad };
}

const out = ['# K12′ の十分性の記号の証明書（k ごと、w ≡ 7 (mod 12) のすべての w について有効）', `# 生成: node --stack-size=65500 code/k12_symbolic.js ${K0} ${K1}${cross ? " crosscheck" : ""}`];
for (let k = K0; k <= K1; k++) {
  const res = certify(k);
  let line = `k=${k}: ${res.ok ? '成功' : '失敗（' + res.fail + '）'}、事実 ${res.n} 個`;
  if (cross && res.ok) { const c = crosscheck(res); line += `、照合 m ${c.done} 個で食い違い ${c.bad}`; }
  out.push(line);
}
process.stdout.write(out.join('\n') + '\n');
