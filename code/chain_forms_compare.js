/*
 * chain_forms_compare.js — chain_forms.js の出力で、鎖の形（入口、入口の段数、幾何的な形、段数の定数 c₀、終わりの形と v2）が
 *                          すべての N で同じかを調べる
 *
 * 何を計算するか:
 *   各 N の鎖の行を、次の組に直す。鎖の始めの距離 d₀ の形、幾何的な形（ブロック番号を除く）、入口の段数、
 *   型（M − c·2^t なら c₀ = s − K、2a − c·2^t なら c₀ = s − 2K）、終わりの距離の形（指数を除く）と v2。
 *   N ごとの組の集合がすべて同じか、各 N の K の偶奇を出す。
 * 実行方法（リポジトリのルートで）:
 *   node code/chain_forms_compare.js data/chain_forms_v7.txt data/chain_forms_v11.txt data/chain_forms_v13.txt data/chain_forms_v15.txt > data/chain_forms_compare.txt
 */
'use strict';
const fs = require('fs');
const out = ['# 鎖の形が N によらないかの比較', `# 生成: node code/chain_forms_compare.js ${process.argv.slice(2).join(' ')}`, 'ファイル | N | 鎖の本数 | 形がすべての N で同じ | K の偶奇'];
for (const file of process.argv.slice(2)) {
  const by = {}; let cur = null;
  for (const l of fs.readFileSync(file, 'utf8').split(/\r?\n/)) { const mm = l.match(/^## N = (\d+)/); if (mm) { cur = mm[1]; by[cur] = []; continue; } if (cur && l.includes(' | ')) by[cur].push(l); }
  const norm = l => { const name = l.split(' | ')[0]; const geo = (l.match(/\| ([^|]*)（ブロック/) || [])[1]; const ent = (l.match(/入口 (\d+) 段/) || [])[1]; const s = +(l.match(/全体 (\d+) 段/) || [])[1]; const K = +(l.match(/K = (\d+)：/) || [])[1];
    const end = ((l.match(/終わり (.*)$/) || [])[1] || '').replace(/·2\^\d+/, '·2^?'); const kind = geo && geo.startsWith('M') ? 'M' : '2a'; return [name, geo, ent, kind, kind === 'M' ? s - K : s - 2 * K, end].join(' / '); };
  const keys = Object.keys(by); const sets = keys.map(k => by[k].map(norm).sort().join('\n'));
  out.push(`${file} | ${keys.join(', ')} | ${keys.map(k => by[k].length).join(', ')} | ${sets.every(x => x === sets[0]) ? 'はい' : 'いいえ'} | ${keys.map(k => (+by[k][0].match(/K = (\d+)：/)[1]) % 2).join(', ')}`);
}
console.log(out.join(String.fromCharCode(10)));
