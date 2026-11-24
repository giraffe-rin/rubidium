---
name: research-cycle
description: Execute one safe, auditable mathematical research cycle for the ruca-maths/rubidium repository.
---

# Rubidium Autonomous Research Cycle

1. Read `AGENTS.md`, `problems/restricted-stone-game/PROBLEM.md`, `problems/restricted-stone-game/STATUS.md`, and the 5 newest files in `notes/`.
2. Respect WIP & human gates: never push directly to `ruca-logic`, never use `git push --force`, stop creating new proofs if 5+ unreviewed proof PRs exist, and label `needs-human` on any contradiction in a `[査読済み]` claim or complete main proof.
3. Add an append-only log in `notes/` and claim metadata in `claims/<ID>.yaml`, then run `python3 code/generate_status.py --check`.
4. Open a PR targeting `ruca-logic` with `Closes #<issue>`.
