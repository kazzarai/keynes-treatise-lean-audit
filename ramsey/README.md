# ramsey/ — Keynes–Ramsey, 1926 → 2026: a flag, not a result

**Status (2026-09-24): scope declaration only.** Nothing in this directory is part of
the canonical audit run, and no theorem about Ramsey is claimed here yet. This file
exists to date-stamp the intent and the design, in the centenary year of Ramsey's
*Truth and Probability* (1926).

## What this track will do

The Keynes–Ramsey dispute over the interpretation of probability (Ramsey's 1922
review of the *Treatise*; *Truth and Probability*, 1926; Keynes's 1931 concession)
has been argued for a century in prose. The Part II audit in this repository fixes,
theorem by theorem, what Keynes's own calculus proves and on which axioms it rests
(228 kernel verdicts, canonical run v7). That gives the dispute a formal floor it has
never had: both sides can now be reconstructed **on the same kernel, over the same
axiomatic floor**, and compared rather than paraphrased.

Planned items, in order:

1. **Map Ramsey's objections onto the ledger.** For each objection in the 1922
   review and in §§ 1–3 of *Truth and Probability*, identify which Part II
   definitions/theorems (by ledger number) it actually touches, and whether the
   audit's load-bearing map confirms, weakens, or is silent on it.
2. **Formalise the 1926 representation side by side.** Ramsey's coherence
   (Dutch-book) route to numerical degrees of belief, stated in Lean alongside
   Keynes's numerical-existence axiom (vii) and the Ch. XV measurement theorems, so
   that the two routes to "a number" are compared under `#print axioms` rather than
   by rhetoric.
3. **Locate the disagreement formally.** The audit already shows Keynes's system
   collapses to {0,1} under an extensional reading and is consistent only under an
   intensional one. The working hypothesis of this track is that the Keynes–Ramsey
   disagreement sits exactly at that seam: Ramsey's betting quotients are
   extensional by construction. This is a hypothesis to be tested, not a finding.

## What this track will not do

It will not adjudicate who "won". It will produce a certified map of where the two
systems agree, where they diverge, and which assumptions each divergence costs.

## Provenance

- Author: Kazunari Arai (Science Frontier Lab., Alai AI, Tokyo).
- Flag committed 2026-09-24; tag `ramsey-flag-20260924`.
- Related: `phases/` (Part II audit, 100/100 ledger), `docs/` (collation), the
  weight trilogy (phase 8), and the author's 2015 Keynes Society Japan paper on the
  "partial-continuity" reading of the *Treatise* and the *General Theory*.
