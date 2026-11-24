/*
 * solver_retro.js — 実装 B：後退解析（retrograde analysis）
 *
 * 何を計算するか:
 *   solver_dp.js と同じく、パラメータ m のすべての局面 (r, p)（0 ≤ r ≤ N, 0 ≤ p ≤ m）
 *   の勝敗（N / P）を計算する。定義は problems/restricted-stone-game/PROBLEM.md に従う。
 *   solver_dp.js とは独立に書いた、考え方の違う実装:
 *     1. 各局面の合法手の数（出次数）を数える。
 *     2. 出次数 0 の局面（合法手なし）を P と確定し、キューに入れる。
 *     3. キューから取り出した確定局面 Q の「親」（Q へ 1 手で移れる局面）を逆向きにたどる:
 *        - Q が P なら、親は N と確定。
 *        - Q が N なら、親の「まだ N と確定していない子」の数を 1 減らし、
 *          0 になったら（どの手も N 局面へ行く）親は P と確定。
 *     4. ゲームは有限なので全局面が確定するはず。未確定が残れば例外を投げる。
 *   親の列挙: 局面 (r', k)（k ≥ 1）へ移る手は「手 k」だけで、その親は (r' + k, p)
 *   （p ≠ k、r' + k ≤ N）。k ≤ m と k ≤ r' + k は自動的に満たされる。
 *   p = 0 の局面へ移る手は存在しないので、p = 0 の局面には親がない。
 *   r ≤ N の局面の子はすべて r ≤ N に入るので、範囲を N で切っても結果は正しい。
 *   状態は 1 次元の型付き配列で持ち、添字は r·(m+1) + p。
 *
 * 実行方法（Node.js 18 以上、外部パッケージ不要）:
 *   node code/solver_retro.js M N     # 出力形式は solver_dp.js と同じ
 *   モジュールとして: require('./solver_retro').solve(m, N) -> string[]
 */
'use strict';

const UNKNOWN = 0, NWIN = 1, PLOSE = 2;

function solve(m, nMax) {
  const width = m + 1;
  const size = (nMax + 1) * width;
  const remaining = new Int32Array(size);
  const status = new Uint8Array(size);
  const queue = new Int32Array(size);
  let head = 0, tail = 0;

  for (let r = 0; r <= nMax; r++) {
    const top = Math.min(m, r);
    for (let p = 0; p < width; p++) {
      const deg = top - (p >= 1 && p <= top ? 1 : 0);
      const i = r * width + p;
      remaining[i] = deg;
      if (deg === 0) { status[i] = PLOSE; queue[tail++] = i; }
    }
  }

  while (head < tail) {
    const child = queue[head++];
    const k = child % width;
    const rc = (child - k) / width;
    if (k === 0) continue;
    const rp = rc + k;
    if (rp > nMax) continue;
    for (let p = 0; p < width; p++) {
      if (p === k) continue;
      const parent = rp * width + p;
      if (status[parent] !== UNKNOWN) continue;
      if (status[child] === PLOSE) {
        status[parent] = NWIN;
        queue[tail++] = parent;
      } else if (--remaining[parent] === 0) {
        status[parent] = PLOSE;
        queue[tail++] = parent;
      }
    }
  }

  if (tail !== size) throw new Error('未確定の局面が残った（定義上ありえない）');
  const out = [];
  for (let r = 0; r <= nMax; r++) {
    let s = '';
    for (let p = 0; p < width; p++) s += status[r * width + p] === NWIN ? 'N' : 'P';
    out.push(s);
  }
  return out;
}

module.exports = { solve };

if (require.main === module) {
  const m = parseInt(process.argv[2], 10);
  const nMax = parseInt(process.argv[3], 10);
  const lines = solve(m, nMax).map((s, r) => `${r} ${s}`);
  process.stdout.write(lines.join('\n') + '\n');
}
