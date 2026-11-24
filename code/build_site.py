#!/usr/bin/env python3
"""Build docs/data/snapshot.json from claims/*.yaml and GitHub REST API."""

import datetime
import json
import os
from pathlib import Path
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
CLAIMS_DIR = ROOT / "claims"
OUTPUT_PATH = ROOT / "docs" / "data" / "snapshot.json"

DEFAULT_REPO = "ruca-maths/rubidium"

BASELINE_CLAIMS = [
    {"id": "K1-K3", "title": "Baseline claims K1-K3", "status": "[査読済み]", "author": "baseline", "reviewer": "", "depends_on": [], "notes": [], "code": [], "lean": ""},
    {"id": "K4-K5", "title": "Baseline claims K4-K5", "status": "[査読済み]", "author": "baseline", "reviewer": "", "depends_on": ["K1-K3"], "notes": [], "code": [], "lean": ""},
    {"id": "K6", "title": "Baseline claim K6", "status": "[査読済み]", "author": "baseline", "reviewer": "", "depends_on": ["K4-K5"], "notes": [], "code": [], "lean": ""},
    {"id": "K7'", "title": "Baseline claim K7'", "status": "[査読済み]", "author": "baseline", "reviewer": "", "depends_on": ["K6"], "notes": [], "code": [], "lean": ""},
    {"id": "W", "title": "Baseline claim W", "status": "[非形式証明]", "author": "baseline", "reviewer": "", "depends_on": ["K7'"], "notes": [], "code": [], "lean": ""},
    {"id": "K20", "title": "Baseline claim K20", "status": "[非形式証明]", "author": "baseline", "reviewer": "", "depends_on": [], "notes": [], "code": [], "lean": ""},
    {"id": "K32", "title": "Baseline claim K32", "status": "[非形式証明]", "author": "baseline", "reviewer": "", "depends_on": [], "notes": [], "code": [], "lean": ""},
    {"id": "K48", "title": "Baseline claim K48", "status": "[予想]", "author": "baseline", "reviewer": "", "depends_on": [], "notes": [], "code": [], "lean": ""},
    {"id": "K49", "title": "Baseline claim K49", "status": "[予想]", "author": "baseline", "reviewer": "", "depends_on": [], "notes": [], "code": [], "lean": ""},
    {"id": "K50", "title": "Baseline claim K50", "status": "[予想]", "author": "baseline", "reviewer": "", "depends_on": [], "notes": [], "code": [], "lean": ""},
]

BASELINE_GRAVEYARD = [
    {"type": "pr", "number": 12, "title": "PR #12 (archived/rejected baseline)", "state": "closed"},
    {"type": "pr", "number": 16, "title": "PR #16 (archived/rejected baseline)", "state": "closed"},
    {"type": "pr", "number": 113, "title": "PR #113 (archived/rejected baseline)", "state": "closed"},
    {"type": "issue", "number": 228, "title": "Issue #228 (archived/closed baseline)", "state": "closed"},
    {"type": "issue", "number": 265, "title": "Issue #265 (archived/closed baseline)", "state": "closed"},
]


def _strip_quotes(val: str) -> str:
    val = val.strip()
    if len(val) >= 2 and ((val[0] == '"' and val[-1] == '"') or (val[0] == "'" and val[-1] == "'")):
        return val[1:-1]
    return val


def parse_simple_yaml(text: str) -> dict:
    data: dict = {}
    current_key = None
    for raw_line in text.splitlines():
        line = raw_line.split("#", 1)[0].rstrip()
        if not line.strip():
            continue
        stripped = line.lstrip()
        if stripped.startswith("- ") and current_key is not None:
            if not isinstance(data.get(current_key), list):
                data[current_key] = []
            data[current_key].append(_strip_quotes(stripped[2:]))
            continue
        if ":" in line:
            key, rest = line.split(":", 1)
            key = key.strip()
            rest = rest.strip()
            current_key = key
            if rest == "" or rest == "[]":
                data[key] = [] if rest == "[]" else ""
            elif rest.startswith("[") and rest.endswith("]"):
                inner = rest[1:-1].strip()
                data[key] = [_strip_quotes(x) for x in inner.split(",") if x.strip()] if inner else []
            else:
                data[key] = _strip_quotes(rest)
    return data


def load_claims() -> list:
    claims_by_id = {c["id"]: dict(c) for c in BASELINE_CLAIMS}
    if CLAIMS_DIR.is_dir():
        for path in sorted(CLAIMS_DIR.glob("*.yaml")):
            if path.name == "TEMPLATE.yaml":
                continue
            parsed = parse_simple_yaml(path.read_text(encoding="utf-8"))
            cid = parsed.get("id") or path.stem
            parsed["id"] = cid
            claims_by_id[cid] = parsed
    return list(claims_by_id.values())


def github_get(url: str, token: str):
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "rubidium-observatory-builder",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read().decode("utf-8"))


def fetch_github_data(repo: str, token: str) -> dict:
    base = f"https://api.github.com/repos/{repo}"
    try:
        repo_info = github_get(base, token)
        pulls = github_get(f"{base}/pulls?state=all&per_page=50", token)
        issues = github_get(f"{base}/issues?state=all&per_page=50", token)
        open_prs = [
            {"number": p["number"], "title": p["title"], "user": p["user"]["login"], "url": p["html_url"]}
            for p in pulls if p.get("state") == "open"
        ]
        graveyard = [
            {"type": "pr", "number": p["number"], "title": p["title"], "state": p["state"], "url": p["html_url"]}
            for p in pulls if p.get("state") == "closed" and not p.get("merged_at")
        ]
        pure_issues = [i for i in issues if "pull_request" not in i]
        open_issues = [
            {"number": i["number"], "title": i["title"], "labels": [l["name"] for l in i.get("labels", [])], "url": i["html_url"]}
            for i in pure_issues if i.get("state") == "open"
        ]
        for i in pure_issues:
            if i.get("state") == "closed":
                graveyard.append({"type": "issue", "number": i["number"], "title": i["title"], "state": i["state"], "url": i["html_url"]})
        if not graveyard:
            graveyard = list(BASELINE_GRAVEYARD)
        return {
            "source": "github_api",
            "repo": repo_info.get("full_name", repo),
            "default_branch": repo_info.get("default_branch", "ruca-logic"),
            "open_prs": open_prs,
            "open_issues": open_issues,
            "graveyard": graveyard,
        }
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError, json.JSONDecodeError) as exc:
        return {
            "source": "baseline_fallback",
            "error": str(exc),
            "repo": repo,
            "default_branch": "ruca-logic",
            "open_prs": [],
            "open_issues": [],
            "graveyard": list(BASELINE_GRAVEYARD),
        }


def main() -> None:
    repo = os.environ.get("GITHUB_REPOSITORY") or DEFAULT_REPO
    token = os.environ.get("GITHUB_TOKEN", "")
    claims = load_claims()
    gh = fetch_github_data(repo, token)
    snapshot = {
        "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "repository": gh["repo"],
        "default_branch": gh["default_branch"],
        "data_source": gh["source"],
        "claims": claims,
        "open_prs": gh["open_prs"],
        "open_issues": gh["open_issues"],
        "graveyard": gh["graveyard"],
    }
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {OUTPUT_PATH} ({len(claims)} claims, source={gh['source']})")


if __name__ == "__main__":
    main()
