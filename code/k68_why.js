// k68_why.js — v2(m+1) = 3 で未被覆の u mod MOD の類が k68_gen.js で通らない理由を数える
// 使い方（lean/ で）: node ../code/k68_why.js 2048 ../code/k68_gen.js Rubidium/K67b.lean ../code/block_rule.js ../code/k68_search.js
const { execFileSync } = require('child_process');
const [MOD, gen, tmpl, br, srch] = process.argv.slice(2);
const src = require('fs').readFileSync(srch, 'utf8'); const covSrc = src.slice(src.indexOf('const covered'), src.indexOf('const ok'));
const v2 = x => { let c = 0; while (x % 2 === 0) { x /= 2; c++; } return c; };
eval(covSrc.replace('const covered', 'global.covered'));
const cnt = {}, ex = {};
for (let r = 1; r < +MOD; r += 2) { if (covered(r) || covered(r + +MOD)) continue;
  let u = r; while (u < 64) u += +MOD;
  const line = execFileSync(process.execPath, [br, 'periods', String(8 * u - 1), String(8 * u - 1)], { encoding: 'utf8' }).split(/\r?\n/).find(l => l.startsWith('m='));
  const f = line.split('|'), t = +f[4].split(',')[0], w = f[5].trim(); let k;
  if (t !== 0) k = 'preperiod'; else if (!w.endsWith('00')) k = 'ends-' + w.slice(-2);
  else { try { execFileSync(process.execPath, [gen, tmpl, 'NUL', MOD, w, String(r)], { stdio: ['ignore', 'pipe', 'pipe'] }); k = 'ok?'; } catch (e) { const m = String(e.stderr).match(/Error: ([^\n:]*)/); k = m ? m[1].replace(/r=\d+.*/, '') : 'err'; } }
  cnt[k] = (cnt[k] || 0) + 1; (ex[k] = ex[k] || []).length < 3 && ex[k].push(r + ':' + w); }
console.log(cnt); console.log(ex);
