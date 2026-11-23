// 何を計算するか：affine_certificate.js の出力（v2(m+1) = 1 の場合）を読み、
//   証明できた類・できなかった類を、h = (m+1)/2 についての 2 進の量
//   s := v2(3h+1) と、3h+1 = 2^s·w としたときの w mod 8 で分類して、自然密度を集計する。
//   s が類の法で決まらない類（A が小さく s を決めきれない類）は「s ≥ (決まる上限)」にまとめる。
// 実行：node code/analyze_unresolved.js data/affine_certificates_v1_T18.txt
const fs = require("fs");
const lines = fs.readFileSync(process.argv[2], "utf8").split(/\r?\n/);
let sec = "";
const rows = [];
for (const l of lines) {
  if (l.startsWith("## 証明できた類")) { sec = "ok"; continue; }
  if (l.startsWith("## 証明できなかった類")) { sec = "ng"; continue; }
  if (l.startsWith("##")) { sec = ""; continue; }
  const mm = l.match(/^m ≡ (\d+) \(mod (\d+)\) \| (.*)$/);
  if (!mm || !sec) continue;
  const B = BigInt(mm[1]), A = BigInt(mm[2]);
  let type = "";
  if (sec === "ok") { const p = mm[3].split("|").map(s => s.trim()); type = p[1] + "|" + p[2]; }
  rows.push({ ok: sec === "ok", A, B, type });
}
const v2 = x => { let c = 0; while (x % 2n === 0n) { x /= 2n; c++; } return c; };
// m = A t + B, h = (A/2) t + (B+1)/2, 3h+1 = (3A/2) t + (3B+5)/2
const stat = {};
const typesByS = {};
for (const r of rows) {
  const a = 3n * r.A / 2n, b = (3n * r.B + 5n) / 2n;
  const va = v2(a), vb = v2(b);
  let key, w8 = "?";
  if (vb < va) {
    key = "s=" + vb;
    // w = (3h+1)/2^s ; w mod 8 は va - vb ≥ 3 なら決まる
    if (va - vb >= 3) w8 = String(((b >> BigInt(vb)) % 8n));
  } else key = "s≥" + va;
  const dens = 1 / Number(r.A / 4n); // v2(m+1)=1 の m（m≡1 mod 4）の中の密度
  const k = key + " w≡" + w8;
  stat[key] = stat[key] || { ok: 0, ng: 0 };
  stat[key][r.ok ? "ok" : "ng"] += dens;
  if (r.ok) { typesByS[key] = typesByS[key] || {}; typesByS[key][r.type] = (typesByS[key][r.type] || 0) + dens; }
  stat[k] = stat[k] || { ok: 0, ng: 0 };
  stat[k][r.ok ? "ok" : "ng"] += dens;
}
console.log("# " + process.argv[2] + " の分類（s = v2(3h+1)、w = (3h+1)/2^s、密度は v2(m+1)=1 の m の中）");
console.log("# 生成: node code/analyze_unresolved.js " + process.argv[2]);
const keys = Object.keys(stat).sort((x, y) => {
  const n = s => parseInt(s.match(/\d+/)[0]); return n(x) - n(y) || x.localeCompare(y);
});
console.log("## s ごと: 区分 | 証明できた密度 | できなかった密度 | できなかった割合");
for (const k of keys.filter(k => !k.includes("w"))) {
  const s = stat[k]; console.log(`${k} | ${s.ok.toFixed(6)} | ${s.ng.toFixed(6)} | ${(s.ng / (s.ok + s.ng)).toFixed(4)}`);
}
console.log("## s と w mod 8 ごと");
for (const k of keys.filter(k => k.includes("w"))) {
  const s = stat[k]; console.log(`${k} | ${s.ok.toFixed(6)} | ${s.ng.toFixed(6)} | ${(s.ng / (s.ok + s.ng)).toFixed(4)}`);
}
console.log("## s ごとの証明できた型（密度の大きい順に最大 6 個）");
for (const k of keys.filter(k => typesByS[k])) {
  const t = Object.entries(typesByS[k]).sort((x, y) => y[1] - x[1]).slice(0, 6);
  console.log(k + ": " + t.map(([ty, d]) => `${ty} (${d.toFixed(5)})`).join(", "));
}
// 追加の分類：s = 2k が偶数の類について、w mod 4 と q := v2(Q_k)（Q_k = h + (w+1)/2）で分ける。
{
  const st = {};
  for (const r of rows) {
    const a = 3n * r.A / 2n, b = (3n * r.B + 5n) / 2n;
    const va = v2(a), vb = v2(b);
    if (!(vb < va) || vb % 2 === 1) continue;
    const s = BigInt(vb);
    const aw = a >> s, bw = b >> s; // w = aw t + bw（aw は 2^(va-vb)）
    let key = "s=" + vb;
    if (va - vb < 2) key += " w mod 4 不定";
    else if (bw % 4n === 3n) key += " w≡3(4)";
    else {
      // Q = h + (w+1)/2
      if (aw % 2n !== 0n) { key += " w≡1(4) q 不定"; }
      else {
        const aQ = r.A / 2n + aw / 2n, bQ = (r.B + 1n) / 2n + (bw + 1n) / 2n;
        const vaQ = v2(aQ), vbQ = bQ === 0n ? 999 : v2(bQ);
        key += " w≡1(4) " + (vbQ < vaQ ? "q=" + vbQ : "q≥" + vaQ);
      }
    }
    const dens = 1 / Number(r.A / 4n);
    st[key] = st[key] || { ok: 0, ng: 0 }; st[key][r.ok ? "ok" : "ng"] += dens;
  }
  console.log("## s が偶数の類：w mod 4 と q = v2(Q_k) ごと（証明できた密度 | できなかった密度 | できなかった割合）");
  for (const k of Object.keys(st).sort((x, y) => parseInt(x.slice(2)) - parseInt(y.slice(2)) || x.localeCompare(y))) {
    const s = st[k]; console.log(`${k} | ${s.ok.toFixed(6)} | ${s.ng.toFixed(6)} | ${(s.ng / (s.ok + s.ng)).toFixed(4)}`);
  }
}
