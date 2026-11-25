---
name: research-cycle
description: Execute one safe, auditable mathematical research cycle for the ruca-maths/rubidium repository.
---

# Rubidium Autonomous Research Cycle

1. Read `AGENTS.md`, `problems/restricted-stone-game/PROBLEM.md`, `problems/restricted-stone-game/STATUS.md`, and `data/dead_ends.jsonl`.
2. Decide the task with `next-task` (never pick a task by hand, never use Issues/labels for picking):
   `gh pr list --repo ruca-maths/rubidium --state open --base ruca-logic --json number,title,isDraft,headRefName,headRepositoryOwner,author > /tmp/open_prs.json`
   then `python3 scripts/autonomous_ops.py next-task --prs-json /tmp/open_prs.json --me agent/<your-agent-name>/`.
   Close every PR in `release_prs` first. If `action` is `stop`, stop here.
3. For `work` / `decompose`: claim the subgoal with an empty-commit draft PR titled `SG-xxx: ...` (AGENTS.md §3), re-run `next-task`, and continue only if your claim is `valid`.
4. Do the work in allowed paths only (Lean proofs in `lean/Rubidium/`, conjectures in `claims/conjectures/*.json`, red-team tests in `code/redteam/test_*.py`, notes in `notes/`). Never edit `STATUS.md` or other immutable-core files.
5. Mark the PR ready for review when `wip.can_mark_ready` is `true`. Never push directly to `ruca-logic`, never force-push, and write `needs-human` and stop on any contradiction.
