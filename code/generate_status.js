/*
 * generate_status.js — code/generate_status.py と同じ規則で、claims/*.yaml から problems/restricted-stone-game/STATUS.md の
 *                      「確立した結果」「予想・未査読の結果」の 2 節を作る（Python のない環境用の移植。結果は Python 版と同じになるように書いた）
 *
 * 何を計算するか:
 *   claims/*.yaml（TEMPLATE.yaml を除く）を簡単な YAML として読み、depends_on の検査（存在すること、[査読済み] 以上であること）をする。
 *   id の順に並べ、status が [査読済み] 以上なら「確立した結果」、それ以外は「予想・未査読の結果」に「- **id** status title（根拠: notes）」と書く。
 * 実行方法（リポジトリのルートで）:
 *   node code/generate_status.js          # STATUS.md を書き換える
 *   node code/generate_status.js --check  # 検査だけ（違いがあれば終了コード 1）
 */
'use strict';
const fs = require('fs'), path = require('path');
const ROOT = path.resolve(__dirname, '..'), CLAIMS = path.join(ROOT, 'claims'), STATUS = path.join(ROOT, 'problems', 'restricted-stone-game', 'STATUS.md');
const LEVEL = { '[予想]': 0, '[非形式証明]': 1, '[査読済み]': 2, '[Lean検証済み]': 3 }, REVIEWED = 2;
const stripComment = line => { let sq = false, dq = false, esc = false; for (let i = 0; i < line.length; i++) { const ch = line[i];
  if (esc) { esc = false; continue; } if (ch === '\\' && dq) { esc = true; continue; }
  if (ch === "'" && !dq) sq = !sq; else if (ch === '"' && !sq) dq = !dq; else if (ch === '#' && !sq && !dq) return line.slice(0, i); } return line; };
const unquote = v => { v = v.trim(); if (v.length >= 2 && ((v[0] === '"' && v.at(-1) === '"') || (v[0] === "'" && v.at(-1) === "'"))) return v.slice(1, -1); return v; };
const inlineList = v => { const inner = v.trim().slice(1, -1).trim(); if (!inner) return []; return inner.split(',').map(unquote).filter(x => x); };
function parse(text) {
  const data = {}; let cur = null;
  for (const raw of text.split(/\r\n|\n|\r/)) {
    const cleaned = stripComment(raw).replace(/\s+$/, ''); if (!cleaned.trim()) continue;
    const st = cleaned.replace(/^\s+/, '');
    if (st.startsWith('- ') && cur !== null) { if (Array.isArray(data[cur])) data[cur].push(unquote(st.slice(2))); continue; }
    const i = st.indexOf(':');
    if (i >= 0) { const key = st.slice(0, i).trim(), rest = st.slice(i + 1).trim(); cur = null;
      if (rest === '') { data[key] = []; cur = key; } else if (rest.startsWith('[') && rest.endsWith(']')) data[key] = inlineList(rest); else data[key] = unquote(rest); }
  }
  return data;
}
const claims = {}, errors = [];
for (const f of fs.readdirSync(CLAIMS).filter(f => f.endsWith('.yaml')).sort()) {
  if (f === 'TEMPLATE.yaml') continue;
  const d = parse(fs.readFileSync(path.join(CLAIMS, f), 'utf8')); const id = String(d.id ?? '').trim();
  if (!id) { errors.push(`${f}: missing 'id'`); continue; } if (claims[id]) { errors.push(`${f}: duplicate id '${id}'`); continue; }
  const s = String(d.status ?? '').trim(); if (!(s in LEVEL)) errors.push(`${f} (${id}): invalid status '${s}'`);
  claims[id] = d;
}
const ids = Object.keys(claims).sort();
for (const id of ids) { const deps = claims[id].depends_on ?? []; if (!Array.isArray(deps)) { errors.push(`${id}: 'depends_on' must be a list`); continue; }
  for (const dep0 of deps) { const dep = String(dep0).trim(); if (!dep) continue; if (dep === id) { errors.push(`${id}: cannot depend on itself`); continue; }
    if (!claims[dep]) { errors.push(`${id}: depends_on '${dep}' does not exist in claims/`); continue; }
    const ds = String(claims[dep].status ?? '').trim(); if ((LEVEL[ds] ?? -1) < REVIEWED) errors.push(`${id}: depends_on '${dep}' has status '${ds}' (< [査読済み])`); } }
if (errors.length) { for (const e of errors) console.error('ERROR: ' + e); process.exit(1); }
const line = c => { const notes = Array.isArray(c.notes) && c.notes.length ? c.notes.join(', ') : ''; let l = `- **${c.id ?? ''}** ${c.status ?? ''} ${c.title ?? ''}`; if (notes) l += `（根拠: ${notes}）`; return l; };
const est = [], unv = []; for (const id of ids) ((LEVEL[String(claims[id].status ?? '').trim()] ?? -1) >= REVIEWED ? est : unv).push(line(claims[id]));
const estSec = '## 確立した結果\n（`[査読済み]` または `[Lean検証済み]` のものだけをここに書く）\n\n' + (est.length ? est.join('\n') : '- まだなし') + '\n';
const unvSec = '## 予想・未査読の結果\n（`[予想]` には確かめた範囲を、`[非形式証明]` には証明の場所を書く）\n\n' + (unv.length ? unv.join('\n') : '- まだなし') + '\n';
const existing = fs.readFileSync(STATUS, 'utf8').split('\r\n').join('\n');
let gen = existing.replace(/## 確立した結果\n[\s\S]*?(?=\n## 予想・未査読の結果\n)/, () => estSec);
gen = gen.replace(/## 予想・未査読の結果\n[\s\S]*?(?=\n## 未解決の問い\n)/, () => unvSec);
if (process.argv.includes('--check')) { if (gen !== existing) { console.error('ERROR: STATUS.md is out of date. Run: node code/generate_status.js'); process.exit(1); } console.log('OK: claims and STATUS.md are valid and up to date.'); }
else { fs.writeFileSync(STATUS, gen); console.log(`Updated ${STATUS} (${ids.length} claims).`); }
