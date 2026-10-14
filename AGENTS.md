# AGENTS.md — roles for non-Claude agents (e.g. Codex) and reviewers

Same invariants as `CLAUDE.md`. Two roles are used in this repository's workflow:

- **Worker**: implements one request in a git worktree, compiles with `lake env lean`, runs `tools/check_all.sh`, writes a report. Never commits.
- **Reader (read-only review)**: reads only the request text and the diff. Checks (a) each theorem statement against the printed formula (indices, bars, strict vs non-strict inequalities, added or missing hypotheses are deviations), (b) carrier discipline, (c) that each acceptance condition is actually established by a theorem (no vacuous statements, no hard-coded values), (d) that necessity countermodels accompany every "axiom not used" claim, (e) hygiene (no local paths). Verdict: *accept* or *revise*, with line references.

Read-only reviewers must not edit files or run `git`.
