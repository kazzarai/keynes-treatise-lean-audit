# CLAUDE.md — working rules for AI agents in this repository

This repository is a kernel-checked audit of J. M. Keynes, *A Treatise on Probability* (1921), in Lean 4 with a pinned Mathlib. Read this file first, then the phase file you are asked to touch.

## Invariants (never break)
1. **The 1921 Macmillan first-edition page is the sole standard.** Every theorem named `th_<ch>_<n>[_src]` states the formula *as printed*; deviations are recorded in `docs/COLLATION_INDEX_1921.md` (E/C/T/S/F) and printed errors get a machine-checked countermodel plus the corrected form. Transcriptions (Gutenberg text), translations and earlier Lean files are aids, not standards.
2. **Each phase file is self-contained**: `import Mathlib`, its own axioms/definitions, `#print axioms` for every verdict at the end. No phase imports another phase.
3. **Carrier discipline.** Part I (weight of argument) and Part III (induction) are encoded on the intensional carrier (`IProp`, `PrI`, see `phase6c`), never as `Prop → Prop → ℝ`: under `propext` + classical logic such a relation degenerates (`th_15_degeneracy`, `V_collapse`).
4. **Numbers are generated, not typed.** Verdict counts, file counts and run dates come from `logs/progress.json` written by `tools/check_all.sh`. Do not hand-edit them in `README.md`.
5. **No `sorry`.** `sorryAx` must not appear in any `#print axioms` output.
6. **No local paths, no personal data.** No absolute paths into a user's home directory (macOS, Linux or Windows); no names other than authors cited bibliographically.
7. **Agents do not run `git commit`/`push`.** The maintainer merges and tags.

## How to add or change a phase
1. Write the acceptance conditions first, as theorem statements (one per ledger row).
2. Prove them. Then deliberately drop one axiom from the dependency list and confirm the proof breaks (necessity), before restoring it.
3. Run `bash tools/check_all.sh phases/<file>.lean` and fix anything red.
4. Report: theorems proved, `#print axioms` lines, conditions not met, suspected printed errors with folio numbers.

## Vocabulary
Use Keynes's own terms (probability-relation, weight of argument, premiss/conclusion, favourable/unfavourable evidence, law of error, most probable value) and the terms of the maintainer's published work cited in `README.md`. Do not coin new metaphors in code comments or docs.
