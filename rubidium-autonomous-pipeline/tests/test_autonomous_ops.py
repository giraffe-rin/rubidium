#!/usr/bin/env python3
"""Unit tests for scripts/autonomous_ops.py."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT_PATH = REPO_ROOT / "scripts" / "autonomous_ops.py"
CONFIG_PATH = REPO_ROOT / "config" / "autonomous.json"


def run_ops(
    repo_root: Path,
    args: list[str],
    github_output: Path | None = None,
) -> tuple[subprocess.CompletedProcess[str], dict[str, str]]:
    env = os.environ.copy()
    if github_output is not None:
        env["GITHUB_OUTPUT"] = str(github_output)
    else:
        env.pop("GITHUB_OUTPUT", None)

    proc = subprocess.run(
        [sys.executable, str(SCRIPT_PATH), "--repo-root", str(repo_root), *args],
        capture_output=True,
        text=True,
        env=env,
    )

    outputs: dict[str, str] = {}
    if github_output is not None and github_output.is_file():
        for line in github_output.read_text(encoding="utf-8").splitlines():
            if "=" in line:
                k, v = line.split("=", 1)
                outputs[k] = v
    return proc, outputs


class TestAutonomousOps(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        (self.root / "config").mkdir(parents=True)
        (self.root / "config" / "autonomous.json").write_text(
            CONFIG_PATH.read_text(encoding="utf-8"),
            encoding="utf-8",
        )
        (self.root / "data").mkdir(parents=True)
        (self.root / "lean" / "Rubidium").mkdir(parents=True)
        (self.root / "problems" / "restricted-stone-game").mkdir(parents=True)
        (self.root / "claims" / "conjectures").mkdir(parents=True)
        (self.root / "claims" / "proved").mkdir(parents=True)
        (self.root / "code" / "redteam").mkdir(parents=True)

        self.gh_out = self.root / "github_output.txt"

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def test_check_immutable_violation_and_allowed(self) -> None:
        # 1. Immutable core violation
        files_json = json.dumps(["lean/Rubidium/Game.lean", "notes/log.md"])
        proc, outputs = run_ops(
            self.root, ["check-immutable", "--files-json", files_json], self.gh_out
        )
        self.assertEqual(proc.returncode, 2)
        self.assertEqual(outputs.get("violation"), "true")
        self.assertIn("lean/Rubidium/Game.lean", outputs.get("violation_files", ""))

        # 2. Out-of-scope file violation
        self.gh_out.unlink(missing_ok=True)
        out_of_scope = json.dumps(["random_root_file.txt"])
        proc, outputs = run_ops(
            self.root, ["check-immutable", "--files-json", out_of_scope], self.gh_out
        )
        self.assertEqual(proc.returncode, 2)
        self.assertEqual(outputs.get("violation"), "true")
        self.assertIn("random_root_file.txt", outputs.get("violation_files", ""))

        # 3. Allowed paths pass with accurate flags
        self.gh_out.unlink(missing_ok=True)
        allowed = json.dumps(
            [
                "lean/Rubidium/K14.lean",
                "code/exp_k14.py",
                "claims/conjectures/c14.json",
                "notes/k14.md",
            ]
        )
        proc, outputs = run_ops(
            self.root, ["check-immutable", "--files-json", allowed], self.gh_out
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(outputs.get("violation"), "false")
        self.assertEqual(outputs.get("has_lean"), "true")
        self.assertEqual(outputs.get("has_code"), "true")
        self.assertEqual(outputs.get("has_conjecture"), "true")
        self.assertEqual(outputs.get("has_notes"), "true")

    def test_verify_lean_static_sorry_axiom_and_comments(self) -> None:
        # Clean file with sorry/axiom only inside comments and strings -> PASS
        clean_file = self.root / "lean" / "Rubidium" / "Clean.lean"
        clean_file.write_text(
            "\n".join(
                [
                    "-- This comment mentions sorry and axiom and unsafe",
                    "/- Block comment with /- nested sorry admit native_decide -/ extern -/",
                    'def docStr : String := "sorry axiom implemented_by"',
                    "theorem clean_thm : 1 + 1 = 2 := rfl",
                ]
            ),
            encoding="utf-8",
        )
        proc, _ = run_ops(
            self.root,
            ["verify-lean-static", "--files-json", json.dumps(["lean/Rubidium/Clean.lean"])],
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)

        # File containing real sorry -> FAIL
        sorry_file = self.root / "lean" / "Rubidium" / "HasSorry.lean"
        sorry_file.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
        proc, _ = run_ops(
            self.root,
            ["verify-lean-static", "--files-json", json.dumps(["lean/Rubidium/HasSorry.lean"])],
        )
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("sorry", proc.stderr)

        # File containing custom axiom -> FAIL
        axiom_file = self.root / "lean" / "Rubidium" / "HasAxiom.lean"
        axiom_file.write_text("axiom cheat : False\n", encoding="utf-8")
        proc, _ = run_ops(
            self.root,
            ["verify-lean-static", "--files-json", json.dumps(["lean/Rubidium/HasAxiom.lean"])],
        )
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("axiom", proc.stderr)

    def test_redteam_check_schema_and_counterexample(self) -> None:
        conj = self.root / "claims" / "conjectures" / "c01.json"
        conj.write_text(
            json.dumps(
                {
                    "id": "C-001",
                    "subgoal_id": "SG-004",
                    "statement": "All even m satisfy P(n, 0) iff ...",
                }
            ),
            encoding="utf-8",
        )
        rt_pass = self.root / "code" / "redteam" / "test_pass.py"
        rt_pass.write_text("import sys\nsys.exit(0)\n", encoding="utf-8")

        proc, outputs = run_ops(
            self.root,
            ["redteam-check", "--files-json", json.dumps(["claims/conjectures/c01.json"])],
            self.gh_out,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(outputs.get("counterexample_found"), "false")

        # Add failing redteam test -> exit code 3 + counterexample_found=true
        self.gh_out.unlink(missing_ok=True)
        rt_fail = self.root / "code" / "redteam" / "test_z_counterexample.py"
        rt_fail.write_text("import sys\nprint('counterexample n=14')\nsys.exit(1)\n", encoding="utf-8")
        proc, outputs = run_ops(
            self.root,
            ["redteam-check", "--files-json", json.dumps(["claims/conjectures/c01.json"])],
            self.gh_out,
        )
        self.assertEqual(proc.returncode, 3)
        self.assertEqual(outputs.get("counterexample_found"), "true")

    def test_record_dead_end_dedup_and_decomposition(self) -> None:
        dag_path = self.root / "data" / "dag.json"
        dag_path.write_text(
            json.dumps(
                {
                    "problem": "restricted-stone-game",
                    "subgoals": [
                        {
                            "id": "SG-004",
                            "title": "Even m",
                            "status": "open",
                            "dependencies": [],
                            "failures": 0,
                            "needs_decomposition": False,
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )

        # Record PR #101 twice -> deduplicated
        for _ in range(2):
            proc, _ = run_ops(
                self.root,
                [
                    "record-dead-end",
                    "--pr-number",
                    "101",
                    "--title",
                    "Attempt SG-004 proof v1",
                    "--labels",
                    "ci-failed",
                ],
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)

        lines = (self.root / "data" / "dead_ends.jsonl").read_text(encoding="utf-8").splitlines()
        self.assertEqual(len(lines), 1)

        # Record PR #102 (falsified-by-redteam -> stagnation should NOT increment)
        proc, _ = run_ops(
            self.root,
            [
                "record-dead-end",
                "--pr-number",
                "102",
                "--title",
                "Conjecture for SG-004",
                "--labels",
                "falsified-by-redteam",
            ],
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        state = json.loads((self.root / "data" / "state.json").read_text(encoding="utf-8"))
        self.assertEqual(state["stagnation_cycles"], 1)

        # Record PR #103 -> 3rd failure on SG-004 -> needs_decomposition=True
        proc, _ = run_ops(
            self.root,
            [
                "record-dead-end",
                "--pr-number",
                "103",
                "--title",
                "Attempt SG-004 proof v3",
                "--labels",
                "ci-failed",
            ],
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)

        dag = json.loads(dag_path.read_text(encoding="utf-8"))
        sg4 = dag["subgoals"][0]
        self.assertEqual(sg4["failures"], 3)
        self.assertTrue(sg4["needs_decomposition"])

        state = json.loads((self.root / "data" / "state.json").read_text(encoding="utf-8"))
        self.assertEqual(state["stagnation_cycles"], 2)

    def test_sync_status_regenerates_index_and_status_and_resets_stagnation(self) -> None:
        (self.root / "data" / "state.json").write_text(
            json.dumps({"stagnation_cycles": 7, "proved_theorem_count": 0, "status": "active"}),
            encoding="utf-8",
        )
        (self.root / "data" / "dag.json").write_text(
            json.dumps(
                {
                    "problem": "restricted-stone-game",
                    "subgoals": [
                        {
                            "id": "SG-002",
                            "title": "Small m",
                            "status": "proved",
                            "failures": 0,
                            "needs_decomposition": False,
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        (self.root / "lean" / "Rubidium" / "Sample.lean").write_text(
            "\n".join(
                [
                    "lemma helper_ok : 2 = 2 := rfl",
                    "theorem K3 : 3 = 3 := rfl",
                    "theorem unfinished : False := by sorry",
                ]
            ),
            encoding="utf-8",
        )

        proc, _ = run_ops(self.root, ["sync-status"])
        self.assertEqual(proc.returncode, 0, proc.stderr)

        idx = json.loads((self.root / "claims" / "proved" / "index.json").read_text(encoding="utf-8"))
        names = [t["name"] for t in idx["theorems"]]
        self.assertEqual(idx["count"], 2)
        self.assertEqual(names, ["helper_ok", "K3"])
        self.assertNotIn("unfinished", names)

        state = json.loads((self.root / "data" / "state.json").read_text(encoding="utf-8"))
        self.assertEqual(state["stagnation_cycles"], 0)
        self.assertEqual(state["proved_theorem_count"], 2)

        status_md = (
            self.root / "problems" / "restricted-stone-game" / "STATUS.md"
        ).read_text(encoding="utf-8")
        self.assertIn("`K3`", status_md)
        self.assertIn("`helper_ok`", status_md)
        self.assertIn("SG-002", status_md)

    def test_check_circuit_breaker_all_branches(self) -> None:
        # 1. Normal dispatch allowed
        (self.root / "data" / "state.json").write_text(
            json.dumps({"stagnation_cycles": 0, "proved_theorem_count": 0}),
            encoding="utf-8",
        )
        self.gh_out.unlink(missing_ok=True)
        proc, out = run_ops(
            self.root,
            ["check-circuit-breaker", "--open-prs", "1", "--daily-prs", "5"],
            self.gh_out,
        )
        self.assertEqual(proc.returncode, 0)
        self.assertEqual(out["halt_now"], "false")
        self.assertEqual(out["can_dispatch"], "true")

        # 2. WIP limit reached (max_open_prs=3)
        self.gh_out.unlink(missing_ok=True)
        proc, out = run_ops(
            self.root,
            ["check-circuit-breaker", "--open-prs", "3", "--daily-prs", "5"],
            self.gh_out,
        )
        self.assertEqual(proc.returncode, 0)
        self.assertEqual(out["halt_now"], "false")
        self.assertEqual(out["can_dispatch"], "false")
        self.assertEqual(out["skip_reason"], "max_open_prs_reached")

        # 3. Daily PR limit reached (max_daily_prs=24)
        self.gh_out.unlink(missing_ok=True)
        proc, out = run_ops(
            self.root,
            ["check-circuit-breaker", "--open-prs", "0", "--daily-prs", "24"],
            self.gh_out,
        )
        self.assertEqual(proc.returncode, 0)
        self.assertEqual(out["halt_now"], "false")
        self.assertEqual(out["can_dispatch"], "false")
        self.assertEqual(out["skip_reason"], "max_daily_prs_reached")

        # 4. Stagnation threshold reached (stagnation_threshold=20)
        (self.root / "data" / "state.json").write_text(
            json.dumps({"stagnation_cycles": 20, "proved_theorem_count": 0}),
            encoding="utf-8",
        )
        self.gh_out.unlink(missing_ok=True)
        proc, out = run_ops(
            self.root,
            ["check-circuit-breaker", "--open-prs", "0", "--daily-prs", "0"],
            self.gh_out,
        )
        self.assertEqual(proc.returncode, 0)
        self.assertEqual(out["halt_now"], "true")
        self.assertEqual(out["halt_reason"], "stagnation_threshold_reached")
        self.assertEqual(out["goal_achieved"], "false")
        self.assertEqual(out["can_dispatch"], "false")

        # 5. Goal achieved (MainTheorem proved without sorry)
        (self.root / "lean" / "Rubidium" / "Main.lean").write_text(
            "theorem MainTheorem : True := trivial\n", encoding="utf-8"
        )
        (self.root / "data" / "state.json").write_text(
            json.dumps({"stagnation_cycles": 0, "proved_theorem_count": 1}),
            encoding="utf-8",
        )
        self.gh_out.unlink(missing_ok=True)
        proc, out = run_ops(
            self.root,
            ["check-circuit-breaker", "--open-prs", "0", "--daily-prs", "0"],
            self.gh_out,
        )
        self.assertEqual(proc.returncode, 0)
        self.assertEqual(out["halt_now"], "true")
        self.assertEqual(out["halt_reason"], "goal_achieved")
        self.assertEqual(out["goal_achieved"], "true")
        self.assertEqual(out["can_dispatch"], "false")


if __name__ == "__main__":
    unittest.main()
