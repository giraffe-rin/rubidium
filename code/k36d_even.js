/*
 * k36d_even.js — 予想 K36d の K 偶数の場合（m+1 の連の長さ s = 2）を、(v, N) ごとに、周期についての帰納法の閉じ方として計算機で確かめる
 *
 * 何を計算するか:
 *   (v, N)（K36 の族、v ≥ 5）について a、m、M、h、K を K36 のとおりとし、周期の始まり B の事実として次を仮定する（帰納法の仮定）。
 *     (A) 奇数の距離は入る。v2 ≤ 3 の距離は「v2 偶数 ⇔ 入る」（ブロック 0 では K3、E 型の始まりでは補題 Q_2）
 *     (B) Y := 2a − 22 は入る
 *   O 型ブロック 1..K+1 の値は、一本道の規則で B までたどり、段数の偶奇と B での値（(A)(B)）から求める。
 *   E 型ブロック E₁ = K+2、E₂ = K+3 の値は、E 型の規則（奇数は入る、偶数の d は ¬[d/2 ∈ S_E] ∧ ¬[h + d/2 ∈ S_{E−1}]）で求める（短絡評価）。
 *   出力：E₁ で h（入らないはず）、E₂ で h（入るはず）、E₂ で Y（入るはず＝次の始まりで (B)）、途中で (A)(B) で決まらない事実があったか。
 *   すべて期待どおりなら、その (v, N) では帰納法が閉じ、型は前周期なし・周期 1^{K+1} 0 0（s = 2）と確定する。
 * 実行方法（リポジトリのルートで）:
 *   node code/k36d_even.js 7:50 7:100 7:150 11:102 11:204 11:306 13:387 15:234 > data/k36d_even.txt
 */
'use strict';
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
const out = ['# 予想 K36d（K 偶数）の帰納法の閉じ方の確認', `# 生成: node code/k36d_even.js ${process.argv.slice(2).join(' ')}`, 'v | N | K | E₁ で h | E₂ で h | E₂ で Y | (A)(B) で決まらない事実 | O 型の鎖の本数 | 判定'];
let all = true;
for (const arg of process.argv.slice(2)) {
  const [v, N] = arg.split(':').map(Number); const q = 2n ** BigInt(v) - 3n, a = (4n ** BigInt(N) - 1n) / q, m = 3n * a - 2n, M = m + 2n, h = (m + 1n) / 2n, K = N - (v + 1) / 2;
  const Y = 2n * a - 22n; let unknown = 0, chains = 0;
  const startVal = d => { const t = v2(d); if (t <= 3) return t % 2 === 0; if (d === Y) return true; unknown++; return null; };
  const valO = (j, d0) => { chains++; let d = d0, s = 0; while (j > 0) { if (d % 2n === 0n) d /= 2n; else { d = (M + d) / 2n; j--; } s++; } const b = startVal(d); return b === null ? null : (s % 2 === 0 ? b : !b); };
  const memo = new Map();
  const valE = (k, d) => { const key = k + ':' + d; if (memo.has(key)) return memo.get(key); let r;
    if (d % 2n === 1n) r = true; else { const a1 = valE(k, d / 2n); if (a1 === true) r = false; else { const e = h + d / 2n; let b = false; if (e <= m) b = k === 1 ? valO(K + 1, e) : valE(1, e); r = b === true ? false : (a1 === null || b === null) ? null : true; } }
    memo.set(key, r); return r; };
  const h1 = valE(1, h), h2 = valE(2, h), y2 = valE(2, Y); const good = h1 === false && h2 === true && y2 === true && unknown === 0 && K % 2 === 0; if (!good) all = false;
  out.push(`${v} | ${N} | ${K} | ${h1} | ${h2} | ${y2} | ${unknown} | ${chains} | ${good ? '閉じる' : '閉じない'}`);
}
out.push('', all ? 'すべての (v, N) で帰納法が閉じた' : '閉じない (v, N) がある');
console.log(out.join(String.fromCharCode(10)));
