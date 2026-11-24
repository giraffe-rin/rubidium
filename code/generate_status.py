#!/usr/bin/env python3
"""Generate and validate problems/restricted-stone-game/STATUS.md from claims/*.yaml."""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS_DIR = ROOT / "claims"
STATUS_PATH = ROOT / "problems" / "restricted-stone-game" / "STATUS.md"

STATUS_LEVELS = {
    "[予想]": 0,
    "[非形式証明]": 1,
    "[査読済み]": 2,
    "[Lean検証済み]": 3,
}
REVIEWED_LEVEL = STATUS_LEVELS["[査読済み]"]


def strip_comment(line: str) -> str:
    in_single = False
    in_double = False
    escaped = False
    for i, ch in enumerate(line):
        if escaped:
            escaped = False
            continue
        if ch == "\\" and in_double:
            escaped = True
            continue
        if ch == "'" and not in_double:
            in_single = not in_single
        elif ch == '"' and not in_single:
            in_double = not in_double
        elif ch == "#" and not in_single and not in_double:
            return line[:i]
    return line


def unquote(val: str) -> str:
    val = val.strip()
    if len(val) >= 2 and ((val[0] == '"' and val[-1] == '"') or (val[0] == "'" and val[-1] == "'")):
        return val[1:-1]
    return val


def parse_inline_list(val: str) -> list[str]:
    inner = val.strip()[1:-1].strip()
    if not inner:
        return []
    return [unquote(item) for item in inner.split(",") if unquote(item)]


def parse_simple_yaml(text: str) -> dict[str, object]:
    data: dict[str, object] = {}
    current_list_key: str | None = None
    for raw_line in text.splitlines():
        cleaned = strip_comment(raw_line).rstrip()
        if not cleaned.strip():
            continue
        stripped = cleaned.lstrip()
        if stripped.startswith("- ") and current_list_key is not None:
            lst = data.setdefault(current_list_key, [])
            if isinstance(lst, list):
                lst.append(unquote(stripped[2:]))
            continue
        if ":" in stripped:
            key, _, rest = stripped.partition(":")
            key = key.strip()
            rest = rest.strip()
            current_list_key = None
            if rest == "":
                data[key] = []
                current_list_key = key
            elif rest.startswith("[") and rest.endswith("]"):
                data[key] = parse_inline_list(rest)
            else:
                data[key] = unquote(rest)
    return data


def load_claims() -> tuple[dict[str, dict[str, object]], list[str]]:
    claims: dict[str, dict[str, object]] = {}
    errors: list[str] = []
    if not CLAIMS_DIR.exists():
        return claims, errors
    for path in sorted(CLAIMS_DIR.glob("*.yaml")):
        if path.name == "TEMPLATE.yaml":
            continue
        try:
            data = parse_simple_yaml(path.read_text(encoding="utf-8"))
        except OSError as exc:
            errors.append(f"{path.name}: failed to read ({exc})")
            continue
        cid = str(data.get("id", "")).strip()
        if not cid:
            errors.append(f"{path.name}: missing 'id'")
            continue
        if cid in claims:
            errors.append(f"{path.name}: duplicate id '{cid}'")
            continue
        status = str(data.get("status", "")).strip()
        if status not in STATUS_LEVELS:
            errors.append(f"{path.name} ({cid}): invalid status '{status}'")
        data["_file"] = path.name
        claims[cid] = data
    return claims, errors


def validate_dependencies(claims: dict[str, dict[str, object]]) -> list[str]:
    errors: list[str] = []
    for cid, claim in sorted(claims.items()):
        deps = claim.get("depends_on", [])
        if not isinstance(deps, list):
            errors.append(f"{cid}: 'depends_on' must be a list")
            continue
        for dep in deps:
            dep_id = str(dep).strip()
            if not dep_id:
                continue
            if dep_id == cid:
                errors.append(f"{cid}: cannot depend on itself")
                continue
            if dep_id not in claims:
                errors.append(f"{cid}: depends_on '{dep_id}' does not exist in claims/")
                continue
            dep_status = str(claims[dep_id].get("status", "")).strip()
            dep_level = STATUS_LEVELS.get(dep_status, -1)
            if dep_level < REVIEWED_LEVEL:
                errors.append(
                    f"{cid}: depends_on '{dep_id}' has status '{dep_status}' (< [査読済み])"
                )
    return errors


def format_claim_line(claim: dict[str, object]) -> str:
    cid = str(claim.get("id", ""))
    title = str(claim.get("title", ""))
    status = str(claim.get("status", ""))
    notes = claim.get("notes", [])
    notes_str = ", ".join(str(n) for n in notes) if isinstance(notes, list) and notes else ""
    line = f"- **{cid}** {status} {title}"
    if notes_str:
        line += f"（根拠: {notes_str}）"
    return line


def render_status_md(existing_text: str, claims: dict[str, dict[str, object]]) -> str:
    established: list[str] = []
    unverified: list[str] = []
    for cid in sorted(claims):
        claim = claims[cid]
        status = str(claim.get("status", "")).strip()
        level = STATUS_LEVELS.get(status, -1)
        line = format_claim_line(claim)
        if level >= REVIEWED_LEVEL:
            established.append(line)
        else:
            unverified.append(line)

    est_body = "\n".join(established) if established else "- まだなし"
    unv_body = "\n".join(unverified) if unverified else "- まだなし"

    est_section = (
        "## 確立した結果\n"
        "（`[査読済み]` または `[Lean検証済み]` のものだけをここに書く）\n\n"
        f"{est_body}\n"
    )
    unv_section = (
        "## 予想・未査読の結果\n"
        "（`[予想]` には確かめた範囲を、`[非形式証明]` には証明の場所を書く）\n\n"
        f"{unv_body}\n"
    )

    text = re.sub(
        r"## 確立した結果\n.*?(?=\n## 予想・未査読の結果\n)",
        est_section,
        existing_text,
        count=1,
        flags=re.DOTALL,
    )
    text = re.sub(
        r"## 予想・未査読の結果\n.*?(?=\n## 未解決の問い\n)",
        unv_section,
        text,
        count=1,
        flags=re.DOTALL,
    )
    return text


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate and check STATUS.md from claims/*.yaml")
    parser.add_argument("--check", action="store_true", help="Check dependencies and STATUS.md diff without writing")
    args = parser.parse_args()

    claims, load_errors = load_claims()
    dep_errors = validate_dependencies(claims)
    all_errors = load_errors + dep_errors
    if all_errors:
        for err in all_errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1

    if not STATUS_PATH.exists():
        print(f"ERROR: {STATUS_PATH} does not exist", file=sys.stderr)
        return 1

    existing_text = STATUS_PATH.read_text(encoding="utf-8")
    generated_text = render_status_md(existing_text, claims)

    if args.check:
        if generated_text != existing_text:
            diff = difflib.unified_diff(
                existing_text.splitlines(keepends=True),
                generated_text.splitlines(keepends=True),
                fromfile=str(STATUS_PATH),
                tofile="generated",
            )
            sys.stderr.writelines(diff)
            print("ERROR: STATUS.md is out of date. Run: python3 code/generate_status.py", file=sys.stderr)
            return 1
        print("OK: claims and STATUS.md are valid and up to date.")
        return 0

    STATUS_PATH.write_text(generated_text, encoding="utf-8")
    print(f"Updated {STATUS_PATH} ({len(claims)} claims).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
