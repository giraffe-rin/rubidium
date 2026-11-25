// 使い方（lean/ で）: node ../code/k68_search.js 2048 ../code/k68_gen.js Rubidium/K67b.lean ../code/block_rule.js
// search.js MOD : v2(m+1)=3 の未被覆の u mod MOD の各類で、u = r の型の語を漸化式 R で求め、k68_gen が通るか試す
const { execFileSync } = require('child_process');
const MOD = +process.argv[2], gen = process.argv[3], tmpl = process.argv[4], br = process.argv[5];
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
const covered = u => { const m = 8 * u - 1; if (m % 64 === 7 && m >= 71) return true; const a = v2(9 * u + 1), b = v2(11 * u + 1); if ((a === 1 && b === 3) || (a === 3 && b === 1)) return true;
  const k = (m + 1); return k % 128 === 88 || k % 512 === 152 || k % 512 === 488 || k % 2048 === 1768 || k % 2048 === 824 || [1560, 1944, 1976].includes(k % 2048) || k % 4096 === 3256; };
const ok = [];
for (let r = 1; r < MOD; r += 2) {
  if (covered(r) || covered(r + MOD)) continue;
  let u = r; while (u < 64) u += MOD;
  const line = execFileSync(process.execPath, [br, 'periods', String(8 * u - 1), String(8 * u - 1)], { encoding: 'utf8' }).split(/\r?\n/).find(l => l.startsWith('m='));
  const f = line.split('|'), t = +f[4].split(',')[0], w = f[5].trim();
  if (t !== 0 || !w.endsWith('00')) continue;
  try { const o = execFileSync(process.execPath, [gen, tmpl, 'NUL', String(MOD), w, String(r)], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }); if (o.includes('ok')) { ok.push([w, r]); console.log('OK', w, r); } } catch (e) {}
}
console.log('TOTAL', ok.length, JSON.stringify(ok));
