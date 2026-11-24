#!/usr/bin/env python3
"""Deterministic control plane for autonomous research in ruca-maths/rubidium.

Uses Python standard library only (compatible with Python 3.11 / 3.12).
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


DEFAULT_CONFIG_PATH = "config/autonomous.json"
FORBIDDEN_LEAN_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "native_decide",
    "implemented_by",
    "extern",
    "unsafe",
)
FORBIDDEN_LEAN_RE = re.compile(
    r"\b(" + "|".join(FORBIDDEN_LEAN_TOKENS) + r")\b"
)
SUBGOAL_ID_RE = re.compile(r"\b(SG-\d+)\b", re.IGNORECASE)
DECL_RE = re.compile(
    r"^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
    r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)
TOP_LEVEL_DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped|@\[[^\]]*\]\s*)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example|namespace|section|end)\b)",
    re.MULTILINE,
)


def load_config(repo_root: Path, config_path: str = DEFAULT_CONFIG_PATH) -> dict[str, Any]:
    path = Path(config_path)
    if not path.is_absolute():
        path = repo_root / path
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def normalize_rel_path(path_str: str) -> str:
    cleaned = path_str.replace("\\", "/").strip()
    while cleaned.startswith("./"):
        cleaned = cleaned[2:]
    return cleaned.lstrip("/")


def glob_to_regex(pattern: str) -> re.Pattern[str]:
    """Convert a POSIX-style glob with ** support into a compiled regex."""
    pattern = normalize_rel_path(pattern)
    regex_parts: list[str] = ["^"]
    i = 0
    n = len(pattern)
    while i < n:
        ch = pattern[i]
        if ch == "*":
            if i + 1 < n and pattern[i + 1] == "*":
                # Handle **/ or /** or **
                if i + 2 < n and pattern[i + 2] == "/":
                    regex_parts.append("(?:.*/)?")
                    i += 3
                else:
                    regex_parts.append(".*")
                    i += 2
            else:
                regex_parts.append("[^/]*")
                i += 1
        elif ch == "?":
            regex_parts.append("[^/]")
            i += 1
        else:
            regex_parts.append(re.escape(ch))
            i += 1
    regex_parts.append("$")
    return re.compile("".join(regex_parts))


def matches_any_glob(path_str: str, globs: list[str]) -> bool:
    norm = normalize_rel_path(path_str)
    return any(glob_to_regex(g).match(norm) is not None for g in globs)


def load_files_json(files_json_arg: str) -> list[str]:
    """Load file list from a JSON file path or an inline JSON array string."""
    raw_text: str
    if files_json_arg == "-":
        raw_text = sys.stdin.read()
    else:
        candidate = Path(files_json_arg)
        if candidate.is_file():
            raw_text = candidate.read_text(encoding="utf-8")
        else:
            raw_text = files_json_arg

    data = json.loads(raw_text)
    if not isinstance(data, list):
        raise ValueError("--files-json must resolve to a JSON array of file paths")

    result: list[str] = []
    for item in data:
        if isinstance(item, str):
            result.append(normalize_rel_path(item))
        elif isinstance(item, dict) and "filename" in item:
            result.append(normalize_rel_path(str(item["filename"])))
        else:
            raise ValueError(f"Unsupported file entry in --files-json: {item!r}")
    return result


def write_github_output(outputs: dict[str, str]) -> None:
    output_path = os.environ.get("GITHUB_OUTPUT")
    if not output_path:
        return
    with open(output_path, "a", encoding="utf-8") as f:
        for key, value in outputs.items():
            if "\n" in value:
                delimiter = "EOF_AUTONOMOUS_OPS"
                f.write(f"{key}<<{delimiter}\n{value}\n{delimiter}\n")
            else:
                f.write(f"{key}={value}\n")


def strip_lean_comments_and_strings(source: str) -> str:
    """Strip Lean 4 line comments (-- ...), nested block comments (/- ... -/),
    and string literals while preserving newlines for accurate line numbers.
    """
    out: list[str] = []
    i = 0
    n = len(source)
    block_depth = 0
    in_string = False

    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            # Line comment until newline
            while i < n and source[i] != "\n":
                out.append(" ")
                i += 1
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1

    return "".join(out)


def cmd_check_immutable(args: argparse.Namespace) -> int:
    repo_root = Path(args.repo_root).resolve()
    cfg = load_config(repo_root, args.config)
    files = load_files_json(args.files_json)

    immutable_globs: list[str] = cfg.get("immutable_globs", [])
    allowed_globs: list[str] = cfg.get("allowed_globs", [])
    lean_dir = normalize_rel_path(cfg.get("lean_dir", "lean"))
    conjectures_dir = normalize_rel_path(cfg.get("conjectures_dir", "claims/conjectures"))

    violations: list[str] = []
    for fpath in files:
        if matches_any_glob(fpath, immutable_globs):
            violations.append(fpath)
        elif allowed_globs and not matches_any_glob(fpath, allowed_globs):
            violations.append(fpath)

    if violations:
        write_github_output(
            {
                "violation": "true",
                "violation_files": ",".join(violations),
            }
        )
        print(
            json.dumps(
                {"violation": True, "violation_files": violations},
                ensure_ascii=False,
            )
        )
        return 2

    has_lean = any(
        fpath.startswith(f"{lean_dir}/") and fpath.endswith(".lean") for fpath in files
    )
    has_code = any(fpath.startswith("code/") for fpath in files)
    has_conjecture = any(
        fpath.startswith(f"{conjectures_dir}/") or fpath.startswith("claims/")
        for fpath in files
    )
    has_notes = any(fpath.startswith("notes/") for fpath in files)

    outputs = {
        "violation": "false",
        "violation_files": "",
        "has_lean": str(has_lean).lower(),
        "has_code": str(has_code).lower(),
        "has_conjecture": str(has_conjecture).lower(),
        "has_notes": str(has_notes).lower(),
    }
    write_github_output(outputs)
    print(json.dumps(outputs, ensure_ascii=False))
    return 0


def cmd_verify_lean_static(args: argparse.Namespace) -> int:
    repo_root = Path(args.repo_root).resolve()
    files = load_files_json(args.files_json)

    findings: list[dict[str, Any]] = []
    for rel_path in files:
        if not rel_path.endswith(".lean"):
            continue
        full_path = repo_root / rel_path
        if not full_path.is_file():
            continue
        raw = full_path.read_text(encoding="utf-8")
        cleaned = strip_lean_comments_and_strings(raw)
        for line_no, line in enumerate(cleaned.splitlines(), start=1):
            for match in FORBIDDEN_LEAN_RE.finditer(line):
                findings.append(
                    {
                        "file": rel_path,
                        "line": line_no,
                        "token": match.group(1),
                    }
                )

    if findings:
        print(
            json.dumps(
                {"ok": False, "findings": findings},
                ensure_ascii=False,
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1

    print(json.dumps({"ok": True, "checked_lean_files": [f for f in files if f.endswith(".lean")]}))
    return 0


def validate_conjecture_json(path: Path) -> list[str]:
    errors: list[str] = []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        return [f"{path}: invalid JSON ({exc})"]

    if not isinstance(data, dict):
        return [f"{path}: top-level value must be a JSON object"]

    for key in ("id", "subgoal_id", "statement"):
        val = data.get(key)
        if not isinstance(val, str) or not val.strip():
            errors.append(f"{path}: missing or empty string field '{key}'")
    return errors


def cmd_redteam_check(args: argparse.Namespace) -> int:
    repo_root = Path(args.repo_root).resolve()
    cfg = load_config(repo_root, args.config)
    files = load_files_json(args.files_json)

    conjectures_dir = normalize_rel_path(cfg.get("conjectures_dir", "claims/conjectures"))
    redteam_dir = repo_root / normalize_rel_path(cfg.get("redteam_dir", "code/redteam"))
    timeout_sec = int(cfg.get("limits", {}).get("redteam_timeout_seconds", 60))

    schema_errors: list[str] = []
    checked_conjectures: set[Path] = set()
    for rel_path in files:
        if rel_path.startswith(f"{conjectures_dir}/") and rel_path.endswith(".json"):
            full_path = repo_root / rel_path
            if full_path.is_file():
                checked_conjectures.add(full_path)

    conjectures_root = repo_root / conjectures_dir
    if conjectures_root.is_dir():
        for p in sorted(conjectures_root.rglob("*.json")):
            checked_conjectures.add(p)

    for conj_file in sorted(checked_conjectures):
        schema_errors.extend(validate_conjecture_json(conj_file))

    if schema_errors:
        write_github_output({"counterexample_found": "false"})
        print(
            json.dumps({"ok": False, "schema_errors": schema_errors}, ensure_ascii=False),
            file=sys.stderr,
        )
        return 1

    redteam_tests = sorted(redteam_dir.glob("test_*.py")) if redteam_dir.is_dir() else []
    for test_file in redteam_tests:
        try:
            proc = subprocess.run(
                [sys.executable, str(test_file)],
                cwd=str(repo_root),
                capture_output=True,
                text=True,
                timeout=timeout_sec,
            )
        except subprocess.TimeoutExpired:
            write_github_output({"counterexample_found": "false"})
            print(
                f"Red team test timed out after {timeout_sec}s: {test_file.relative_to(repo_root)}",
                file=sys.stderr,
            )
            return 1

        if proc.returncode != 0:
            rel_test = normalize_rel_path(str(test_file.relative_to(repo_root)))
            write_github_output(
                {
                    "counterexample_found": "true",
                    "counterexample_test": rel_test,
                }
            )
            print(
                json.dumps(
                    {
                        "counterexample_found": True,
                        "test": rel_test,
                        "returncode": proc.returncode,
                        "stdout": proc.stdout[-2000:],
                        "stderr": proc.stderr[-2000:],
                    },
                    ensure_ascii=False,
                )
            )
            return 3

    write_github_output({"counterexample_found": "false", "counterexample_test": ""})
    print(
        json.dumps(
            {
                "ok": True,
                "counterexample_found": False,
                "checked_conjectures": len(checked_conjectures),
                "executed_redteam_tests": len(redteam_tests),
            },
            ensure_ascii=False,
        )
    )
    return 0


def load_json_or_default(path: Path, default: Any) -> Any:
    if not path.is_file():
        return default
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def save_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.write("\n")


def load_dead_ends(path: Path) -> list[dict[str, Any]]:
    if not path.is_file():
        return []
    entries: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        entries.append(json.loads(line))
    return entries


def extract_subgoal_ids(text: str) -> list[str]:
    seen: list[str] = []
    for m in SUBGOAL_ID_RE.finditer(text or ""):
        sg = m.group(1).upper()
        if sg not in seen:
            seen.append(sg)
    return seen


def cmd_record_dead_end(args: argparse.Namespace) -> int:
    repo_root = Path(args.repo_root).resolve()
    cfg = load_config(repo_root, args.config)

    dead_ends_path = repo_root / cfg.get("dead_ends_file", "data/dead_ends.jsonl")
    dag_path = repo_root / cfg.get("dag_file", "data/dag.json")
    state_path = repo_root / cfg.get("state_file", "data/state.json")
    decompose_threshold = int(
        cfg.get("limits", {}).get("subgoal_failure_decompose_threshold", 3)
    )

    pr_number = int(args.pr_number)
    existing = load_dead_ends(dead_ends_path)
    if any(int(item.get("pr_number", -1)) == pr_number for item in existing):
        print(
            json.dumps(
                {"recorded": False, "reason": "duplicate_pr", "pr_number": pr_number},
                ensure_ascii=False,
            )
        )
        return 0

    labels_raw = (args.labels or "").strip()
    if labels_raw.startswith("["):
        labels = [str(x).strip() for x in json.loads(labels_raw) if str(x).strip()]
    else:
        labels = [x.strip() for x in labels_raw.split(",") if x.strip()]

    title = args.title or ""
    body = args.body or ""
    subgoals = extract_subgoal_ids(f"{title}\n{body}")
    closed_at = args.closed_at or dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    entry = {
        "pr_number": pr_number,
        "title": title,
        "labels": labels,
        "subgoals": subgoals,
        "url": args.url or "",
        "head_ref": args.head_ref or "",
        "closed_at": closed_at,
    }
    dead_ends_path.parent.mkdir(parents=True, exist_ok=True)
    with dead_ends_path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")

    # Update DAG failure counts
    dag = load_json_or_default(dag_path, {"problem": "restricted-stone-game", "subgoals": []})
    subgoal_list = dag.get("subgoals", [])
    by_id = {str(sg.get("id", "")).upper(): sg for sg in subgoal_list}
    updated_subgoals: list[str] = []
    for sg_id in subgoals:
        sg = by_id.get(sg_id)
        if sg is None:
            sg = {
                "id": sg_id,
                "title": f"Auto-tracked subgoal {sg_id}",
                "status": "open",
                "dependencies": [],
                "failures": 0,
                "needs_decomposition": False,
            }
            subgoal_list.append(sg)
            by_id[sg_id] = sg
        sg["failures"] = int(sg.get("failures", 0)) + 1
        if sg["failures"] >= decompose_threshold:
            sg["needs_decomposition"] = True
        updated_subgoals.append(sg_id)

    dag["subgoals"] = subgoal_list
    save_json(dag_path, dag)

    # Update state stagnation_cycles unless falsified-by-redteam
    state = load_json_or_default(
        state_path,
        {
            "stagnation_cycles": 0,
            "proved_theorem_count": 0,
            "status": "active",
        },
    )
    incremented_stagnation = "falsified-by-redteam" not in labels
    if incremented_stagnation:
        state["stagnation_cycles"] = int(state.get("stagnation_cycles", 0)) + 1
    save_json(state_path, state)

    print(
        json.dumps(
            {
                "recorded": True,
                "pr_number": pr_number,
                "subgoals": updated_subgoals,
                "incremented_stagnation": incremented_stagnation,
                "stagnation_cycles": state["stagnation_cycles"],
            },
            ensure_ascii=False,
        )
    )
    return 0


def scan_proved_lean_theorems(repo_root: Path, lean_dir: str) -> list[dict[str, Any]]:
    """Scan Lean files for theorem/lemma declarations with no sorry/admit."""
    lean_root = repo_root / lean_dir
    if not lean_root.is_dir():
        return []

    proved: list[dict[str, Any]] = []
    for lean_file in sorted(lean_root.rglob("*.lean")):
        rel = normalize_rel_path(str(lean_file.relative_to(repo_root)))
        parts = rel.split("/")
        if ".lake" in parts or "build" in parts:
            continue

        raw = lean_file.read_text(encoding="utf-8")
        cleaned = strip_lean_comments_and_strings(raw)

        # Find all top-level declaration boundaries to slice each theorem/lemma body
        top_starts = [m.start() for m in TOP_LEVEL_DECL_RE.finditer(cleaned)]
        for match in DECL_RE.finditer(cleaned):
            kind = match.group(1)
            name = match.group(2)
            start_pos = match.start()
            next_starts = [pos for pos in top_starts if pos > start_pos]
            end_pos = next_starts[0] if next_starts else len(cleaned)
            body_slice = cleaned[start_pos:end_pos]

            if re.search(r"\b(sorry|admit)\b", body_slice):
                continue

            line_no = cleaned.count("\n", 0, start_pos) + 1
            proved.append(
                {
                    "name": name,
                    "kind": kind,
                    "file": rel,
                    "line": line_no,
                }
            )

    proved.sort(key=lambda item: (item["file"], item["line"], item["name"]))
    return proved


def render_status_md(
    proved_theorems: list[dict[str, Any]],
    dag: dict[str, Any],
    dead_ends: list[dict[str, Any]],
    state: dict[str, Any],
    cfg: dict[str, Any],
) -> str:
    main_thm = cfg.get("main_theorem_name", "MainTheorem")
    proved_names = {t["name"] for t in proved_theorems}
    goal_achieved = main_thm in proved_names
    stagnation = int(state.get("stagnation_cycles", 0))
    stagnation_limit = int(cfg.get("limits", {}).get("stagnation_threshold", 20))

    lines: list[str] = [
        "# Restricted Stone Game — Research Status",
        "",
        "<!-- Auto-generated deterministically by scripts/autonomous_ops.py sync-status. Do not edit manually. -->",
        "",
        "## Overview",
        "",
        f"- **Main Theorem Target**: `{main_thm}` ({'PROVED' if goal_achieved else 'OPEN'})",
        f"- **Lean-Verified Theorems & Lemmas**: {len(proved_theorems)}",
        f"- **Recorded Dead Ends**: {len(dead_ends)}",
        f"- **Stagnation Cycles**: {stagnation} / {stagnation_limit}",
        "",
        "## Lean-Verified Results (`claims/proved/index.json`)",
        "",
    ]

    if proved_theorems:
        lines.append("| Kind | Name | File | Line |")
        lines.append("| :--- | :--- | :--- | ---: |")
        for item in proved_theorems:
            lines.append(
                f"| `{item['kind']}` | `{item['name']}` | `{item['file']}` | {item['line']} |"
            )
    else:
        lines.append("_No Lean-verified theorems or lemmas found yet._")

    lines.extend(["", "## Subgoal DAG (`data/dag.json`)", ""])
    subgoals = dag.get("subgoals", [])
    if subgoals:
        lines.append("| ID | Title | Status | Failures | Needs Decomposition |")
        lines.append("| :--- | :--- | :--- | ---: | :--- |")
        for sg in subgoals:
            needs_dec = "YES" if sg.get("needs_decomposition") else "no"
            lines.append(
                f"| `{sg.get('id', '')}` | {sg.get('title', '')} | `{sg.get('status', 'open')}` "
                f"| {int(sg.get('failures', 0))} | {needs_dec} |"
            )
    else:
        lines.append("_No subgoals registered._")

    lines.extend(["", "## Recent Dead Ends (`data/dead_ends.jsonl`)", ""])
    if dead_ends:
        lines.append("| PR | Title | Subgoals | Labels |")
        lines.append("| ---: | :--- | :--- | :--- |")
        for entry in dead_ends[-15:]:
            sgs = ", ".join(f"`{s}`" for s in entry.get("subgoals", [])) or "-"
            lbls = ", ".join(f"`{l}`" for l in entry.get("labels", [])) or "-"
            title_safe = str(entry.get("title", "")).replace("|", "\\|")
            lines.append(f"| #{entry.get('pr_number', '')} | {title_safe} | {sgs} | {lbls} |")
    else:
        lines.append("_No dead ends recorded yet._")

    lines.append("")
    return "\n".join(lines)


def cmd_sync_status(args: argparse.Namespace) -> int:
    repo_root = Path(args.repo_root).resolve()
    cfg = load_config(repo_root, args.config)

    lean_dir = cfg.get("lean_dir", "lean")
    proved_index_path = repo_root / cfg.get("proved_index_file", "claims/proved/index.json")
    dag_path = repo_root / cfg.get("dag_file", "data/dag.json")
    dead_ends_path = repo_root / cfg.get("dead_ends_file", "data/dead_ends.jsonl")
    state_path = repo_root / cfg.get("state_file", "data/state.json")
    status_path = repo_root / cfg.get("status_file", f"{cfg.get('problem_dir', 'problems/restricted-stone-game')}/STATUS.md")

    proved_theorems = scan_proved_lean_theorems(repo_root, lean_dir)
    proved_index = {
        "count": len(proved_theorems),
        "theorems": proved_theorems,
    }
    save_json(proved_index_path, proved_index)

    state = load_json_or_default(
        state_path,
        {
            "stagnation_cycles": 0,
            "proved_theorem_count": 0,
            "status": "active",
        },
    )
    prev_count = int(state.get("proved_theorem_count", 0))
    new_count = len(proved_theorems)
    stagnation_reset = False
    if new_count > prev_count:
        state["stagnation_cycles"] = 0
        stagnation_reset = True
    state["proved_theorem_count"] = new_count
    save_json(state_path, state)

    dag = load_json_or_default(dag_path, {"problem": "restricted-stone-game", "subgoals": []})
    dead_ends = load_dead_ends(dead_ends_path)

    status_md = render_status_md(proved_theorems, dag, dead_ends, state, cfg)
    status_path.parent.mkdir(parents=True, exist_ok=True)
    status_path.write_text(status_md, encoding="utf-8")

    print(
        json.dumps(
            {
                "proved_count": new_count,
                "stagnation_reset": stagnation_reset,
                "stagnation_cycles": state["stagnation_cycles"],
                "status_file": normalize_rel_path(str(status_path.relative_to(repo_root))),
            },
            ensure_ascii=False,
        )
    )
    return 0


def cmd_check_circuit_breaker(args: argparse.Namespace) -> int:
    repo_root = Path(args.repo_root).resolve()
    cfg = load_config(repo_root, args.config)

    main_thm = cfg.get("main_theorem_name", "MainTheorem")
    lean_dir = cfg.get("lean_dir", "lean")
    state_path = repo_root / cfg.get("state_file", "data/state.json")
    proved_index_path = repo_root / cfg.get("proved_index_file", "claims/proved/index.json")

    limits = cfg.get("limits", {})
    max_open_prs = int(limits.get("max_open_prs", 3))
    max_daily_prs = int(limits.get("max_daily_prs", 24))
    stagnation_threshold = int(limits.get("stagnation_threshold", 20))

    # Verify main theorem from Lean files directly (fallback to index if lean_dir missing)
    if (repo_root / lean_dir).is_dir():
        proved = scan_proved_lean_theorems(repo_root, lean_dir)
    else:
        idx = load_json_or_default(proved_index_path, {"theorems": []})
        proved = idx.get("theorems", [])

    goal_achieved = any(t.get("name") == main_thm for t in proved)
    state = load_json_or_default(state_path, {"stagnation_cycles": 0})
    stagnation_cycles = int(state.get("stagnation_cycles", 0))

    open_prs = int(args.open_prs)
    daily_prs = int(args.daily_prs)

    halt_now = False
    halt_reason = ""
    can_dispatch = True
    skip_reason = ""

    if goal_achieved:
        halt_now = True
        halt_reason = "goal_achieved"
        can_dispatch = False
        skip_reason = "goal_achieved"
    elif stagnation_cycles >= stagnation_threshold:
        halt_now = True
        halt_reason = "stagnation_threshold_reached"
        can_dispatch = False
        skip_reason = "stagnation_threshold_reached"
    elif open_prs >= max_open_prs:
        can_dispatch = False
        skip_reason = "max_open_prs_reached"
    elif daily_prs >= max_daily_prs:
        can_dispatch = False
        skip_reason = "max_daily_prs_reached"

    outputs = {
        "halt_now": str(halt_now).lower(),
        "halt_reason": halt_reason,
        "goal_achieved": str(goal_achieved).lower(),
        "can_dispatch": str(can_dispatch).lower(),
        "skip_reason": skip_reason,
    }
    write_github_output(outputs)
    print(json.dumps(outputs, ensure_ascii=False))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Deterministic autonomous research operations for ruca-maths/rubidium."
    )
    parser.add_argument(
        "--repo-root",
        default=".",
        help="Repository root directory (default: current working directory)",
    )
    parser.add_argument(
        "--config",
        default=DEFAULT_CONFIG_PATH,
        help=f"Path to autonomous config JSON (default: {DEFAULT_CONFIG_PATH})",
    )

    sub = parser.add_subparsers(dest="command", required=True)

    p_imm = sub.add_parser("check-immutable", help="Check PR files against immutable core")
    p_imm.add_argument("--files-json", required=True, help="JSON file or JSON array of changed paths")
    p_imm.set_defaults(func=cmd_check_immutable)

    p_lean = sub.add_parser("verify-lean-static", help="Static check on changed Lean files")
    p_lean.add_argument("--files-json", required=True, help="JSON file or JSON array of changed paths")
    p_lean.set_defaults(func=cmd_verify_lean_static)

    p_rt = sub.add_parser("redteam-check", help="Validate conjecture JSON and run redteam tests")
    p_rt.add_argument("--files-json", required=True, help="JSON file or JSON array of changed paths")
    p_rt.set_defaults(func=cmd_redteam_check)

    p_de = sub.add_parser("record-dead-end", help="Record an unmerged closed PR to dead_ends.jsonl")
    p_de.add_argument("--pr-number", required=True, type=int)
    p_de.add_argument("--title", default="")
    p_de.add_argument("--body", default="")
    p_de.add_argument("--labels", default="")
    p_de.add_argument("--url", default="")
    p_de.add_argument("--head-ref", default="")
    p_de.add_argument("--closed-at", default="")
    p_de.set_defaults(func=cmd_record_dead_end)

    p_sync = sub.add_parser("sync-status", help="Deterministically regenerate proved index and STATUS.md")
    p_sync.set_defaults(func=cmd_sync_status)

    p_cb = sub.add_parser("check-circuit-breaker", help="Evaluate halt and dispatch conditions")
    p_cb.add_argument("--open-prs", required=True, type=int)
    p_cb.add_argument("--daily-prs", required=True, type=int)
    p_cb.set_defaults(func=cmd_check_circuit_breaker)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    sys.exit(main())
