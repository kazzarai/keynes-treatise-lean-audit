# Keynes's *Treatise on Probability* (1921), Part II — A Lean 4 Kernel Audit

**Machine-checked formalisation of the axiom system of J. M. Keynes's
*A Treatise on Probability*, Part II (Chapters 12–17), with exact kernel
dependency measurements for every verified theorem.**

- **100 / 100** numbered theorems of the reconstruction ledger
  kernel-checked — **every chapter complete** (13: 30/30, 14: 47/47,
  15: 6/6, 17: 17/17), with one annotation: (14.34) is verified in
  corrected form, its printed form being machine-refuted (see **Errata**)
- **169 kernel-checked items** in the extensional development, plus the
  intensional (`KeynesI`) development and the erratum countermodel, across
  17 files — zero `sorry`
- Every verified theorem reports its **exact axiom cut-set** via
  `#print axioms` — the audit measures the gap between what Keynes *cites*
  and what his theorems *need*
- Includes two structural certificates: an **extensional-collapse theorem**
  and a **joint-inconsistency certificate** for the naive reading of
  Keynes's numerical existence axiom (quarantined; see below), plus a
  **pedantic re-encoding** on an intensional carrier in which Keynes's
  Theorem (12) is *proved* rather than assumed
- The relevance-transmission theorems (33)/(33.1)/(35), often summarised as
  "transitivity of relevance", are verified in their original *conditioned*
  form — collated against the source text — and their kernel cut-set is
  **empty of Keynes axioms**: comparative relevance transmission is pure
  ordered-field algebra
- Canonical, reproducible evidence: [`logs/keynes_audit_canonical_run_20260709_v5.log`](logs/keynes_audit_canonical_run_20260709_v5.log)
  records toolchain, dependency pins, **SHA-256 of every source file**, and
  the complete output of a single verified run (17/17 files, exit 0)

by **Kazunari Arai** (新井一成), with Claude (Anthropic).
Companion paper (working draft): *Formal Verification, Philosophical
Significance, and the Connection to the General Theory* — in preparation;
this repository is self-contained and is the primary artifact.

---

## Quick start

Requirements: [elan](https://github.com/leanprover/elan) (Lean toolchain
manager). The toolchain (`leanprover/lean4:v4.29.1`) and the Mathlib pin are
in `lean-toolchain` / `lake-manifest.json`.

```bash
# inside a lake project using the pinned toolchain + manifest
lake exe cache get                     # fetch prebuilt Mathlib oleans
lake env lean phases/keynes_part_ii_pilot.lean     # or any other phase file
```

Expected: exit code 0; warnings such as `unused variable` are benign. The
`#print axioms` blocks in the output are the audit data. Verify file
integrity against the SHA-256 list in the canonical log header. A theorem
whose axiom list contains `sorryAx` is unverified — **there are none in the
canonical run**.

## What is in each file

| File | Content | Adds |
|---|---|---|
| `phases/keynes_part_ii_pilot.lean` | Ch.12 core (Def. IX–XIII, Ax. iii) + Theorem (24) | 7 nodes |
| `phases/…phase2.lean` | Ch.12 completion + Ch.13 basics ((13.1)–(13.3), (13.19), (13.20)) | +18 |
| `phases/…phase3a.lean` | Multiplication (14.36), Bayes basic (14.38) | +3 |
| `phases/…phase3b.lean` | W. E. Johnson influence coefficient, binary | +5 |
| `phases/…phase3c.lean` | n-ary coefficient, repetition, full Bayes ratio form | +6 |
| `phases/…phase3d.lean` | Cumulative Bayes (14.46)–(14.48) | +3 |
| `phases/…phase4.lean` | **Ch.15 numerical measurement**; range principle promoted to axiom; degeneracy theorem; inconsistency certificate for naive Ax.(pre); intensional repair | +20 items |
| `phases/…phase5.lean` | **Ch.17**: Boole's challenge problem (56)-series, n-cause generalisation (57), Laplacean succession (58)-series; evidence accumulation (14.49) | +25 items |
| `phases/…phase6a.lean` | Total probability (14.25), n-hypothesis Bayes normalisation (14.46.2), independence-product theorems (17.57.1–.5); evidence-slot axiom `ax_iii_ev` | +24 items |
| `phases/…phase6b.lean` | Corollary sweep: 18 Ch.13 + 16 Ch.14 theorems | +39 items |
| `phases/…phase6c_skeleton.lean` | Intensional axiom layer, schema-certified tautologies (superseded by 6c) | KeynesI |
| `phases/…phase6c.lean` | **Pedantic encoding**: deep-embedded propositional syntax, truth-table tautology semantics, and **Theorem (12) demoted from axiom to theorem** along Keynes's own route (Def. VIII + both directional forms of Def. X) | KeynesI |
| `phases/…phase7a.lean` | Conditional-certainty bridge (13.16.1)/(13.16.3) (a reclassification correction — see collation status) | +2 |
| `phases/…phase7b.lean` | **First source-collated batch** (Sato tr., pp. 168–172): complement-irrelevance (14.30), conditioned relevance transmission (14.33)/(14.33.1)/(14.35), premise combination (14.39)/(14.40) | +6 |
| `phases/…phase7c.lean` | **Second source-collated batch** (Sato tr., pp. 160–162), completing Chapter 13: strengthened equivalence principle (13.12.1), (13.15.1), the disjunctive/conditional certainty family (13.16)/(13.16.2), conditional equivalence (13.17) | +5 |
| `phases/…phase7d.lean` | **The (14.34) erratum, resolved both ways**: machine proof that the printed bridge's RHS is trivialised by Keynes's own Def. X; an axiom-free rational countermodel (weights 2,1,1,2) falsifying the printed equation while satisfying all hypotheses; and the **corrected (34)** — a rearrangement of the inverse principle (38) — verified | +1 |
| `phases/…phase7e.lean` | General permutation rule (14.42.2) via `List.Perm` induction — the ledger's final item | +1 |
| `prolog/keynes_axioms_v2.pl` | Citation database of Part II: 25 definitions/axioms, 100 theorems, 177 citation relations (SWI-Prolog) | — |
| `logs/…canonical_run_20260709_v5.log` | **The citable evidence artifact** (17 files) | — |
| `logs/…canonical_run_20260708_v4.log`, `…_v3.log`, `…20260708.log` | Superseded runs over earlier corpora (retained as development history) | — |
| `docs/PHASE6C_DESIGN.md` | Design notes for the intensional migration, incl. planned Popper-function countermodel | — |

## Reading a dependency list

```
'Keynes.th_13_12' depends on axioms: [propext, Classical.choice, Quot.sound,
 Keynes.Pr, Keynes.ax_iii_op, Keynes.ax_iii_true, Keynes.ax_range_lo, Keynes.def_IX]
```

- `propext, Classical.choice, Quot.sound` — the **floor**: Lean's own axioms
  (the classical-extensional substrate). Across all 12 files it never grows:
  no theorem needs a fourth kernel axiom. Recursors (`List.rec` etc.) never
  appear — induction and convergence are consumed by the kernel without
  leaving an axiom trace.
- `Keynes.Pr` — the primitive probability relation (`Prop → Prop → ℝ`;
  no measure theory is imported anywhere).
- The rest — the Keynes axioms actually load-bearing. Compare with the
  citation trail in `prolog/keynes_axioms_v2.pl`: for (13.12) Keynes cites
  Def. X, Def. VIII and Ax. (ivb), and the kernel uses none of them. Nine such
  divergences ("Mode S") are catalogued across the corpus.
- In the `KeynesI` (intensional) files, the carrier and its connectives
  (`IProp`, `iand`, …) are themselves axiomatised, so they appear in the
  lists; the deep-embedding machinery (`Form`, `evalB`, `Taut`) does not.

### Intentional artifacts (do not be alarmed)

- `Keynes.Naive.collapse : False` (phase 4) is **deliberate**: a
  machine-checked certificate that the *naive extensional* reading of
  Keynes's Chapter-15 existence axiom is inconsistent with the fused
  tautology axiom over `Prop`. It is quarantined in its own namespace and
  imported by nothing. The repair (intensional carrier) is in the same file,
  and the pedantic encoding of `phase6c.lean` closes the loop.
- `th_15_degeneracy` (phase 4) proves that the fused extensional encoding
  collapses all probabilities to {0, 1}. It does not invalidate the
  conditional theorems (they hold in every model); it measures the price of
  extensionality — which is the philosophical point.

## Encoding conventions

1. Probability is a primitive relation between propositions, after Keynes —
   not a measure. Nothing is imported from measure theory.
2. Keynes's Ax. (iii) appears in operational forms: proposition-slot
   (`ax_iii_op`), evidence-slot (`ax_iii_ev`), True-certainty
   (`ax_iii_true`); the pedantic alternative (`phase6c.lean`) replaces all
   three by a single axiom over syntactically certified tautologies.
3. The range principle 0 ≤ α/h ≤ 1 (stated by Keynes in prose, never
   numbered) is an explicit axiom from phase 4 onward.
4. "Consistent" (整合) is read as non-impossibility (`Pr ≠ 0`); bare-evidence
   forms `α/b` are read with ambient evidence as `α/(b∧h)`.
5. DB nodes (38.1) and (48) state the same two-hypothesis Bayes formula; one
   Lean theorem is credited to both.
6. Every ledger item is verified; one carries an annotation. (14.34) is
   verified in its **corrected** form — the printed form is machine-refuted
   (see Errata below).

## Errata in the source, machine-certified

Collation against the English original (Project Gutenberg #32625, a
faithful transcription of the 1921 Macmillan edition) and the Japanese
Collected-Writings translation shows both editions agree — so the following
are defects of the source itself, not of any edition:

- **(14.33), prose vs. proof**: the statement reads "h₁ is not **more**
  favourable to a/hx than x is to a/hh₁", while Keynes's own printed proof
  requires (and we verify) "not **less**". The inequality direction in the
  prose is a slip; `phase7b` formalises the proof-side (true) form.
- **(14.34), the bridge display**: the printed equation's RHS is
  trivialised to 1 by Keynes's own Def. X applied on evidence *ha*
  (machine proof: `th_34_printed_rhs_trivial`), while its LHS telescopes to
  (a/hh₁)/(a/hx) ≠ 1 in general — an axiom-free rational countermodel
  (weights 2,1,1,2) satisfies every hypothesis of (34) as printed and
  falsifies both the display and the theorem
  (`Erratum34Countermodel`, all checks by `norm_num`). The correct bridge,

  > (a/hh₁)/(a/hx) = (h₁/ah)/(h₁/h) · (x/h)/(x/ah),

  is a rearrangement of the inverse principle (38) — the diagnosis is that
  two evidence subscripts were interchanged (h ↔ ha). The corrected
  theorem is verified as `th_14_34`.

## Fidelity and collation status (read before quoting "faithful to Keynes")

The Lean statements were originally encoded from the reconstruction ledger
(`prolog/keynes_axioms_v2.pl`), which was itself rebuilt from thesis
materials after the loss of the original research environment. Counts
written `n/100` are **ledger-relative**. Collation against the source text
(Sato's Japanese translation of the *Treatise*, Keynes Collected Writings
vol. 8) is in progress and has already produced corrections in both
directions:

- The ledger's headline for (33)–(35) ("transitivity of relevance") was a
  misleading summary; the source text states *conditioned comparative*
  transmission theorems, now verified as `phase7b` with page references.
- Most damaged ledger glosses turned out to be **lost negation overbars**:
  e.g. the ledger's (13.16) read `(h₁+h₂)/h = 1` (false as stated), while
  the source reads `(h₁+h̄₂)/h = 1`. Collation recovered and `phase7c`
  verified the entire damaged Chapter-13 group.
- The ledger **undercounts** the original's sub-numbered items:
  (29.1)–(29.3), (33.1), (38.2), (40.1) exist in the source but not in the
  ledger. One of these, (33.1), is verified here as an extra-ledger item.
- A notable corpus-level result: Keynes's Ax. (ii) (the equality axiom) is
  **never load-bearing** in any of the 98 verified dependency sets — even
  for (13.12.1), whose printed proof invokes it explicitly, the kernel
  route closes through certainty propagation (13.9) plus the equivalence
  theorem (13.12).
- A systematic collation pass over all verified statements (page reference
  per theorem) is the gate we have set ourselves for submitting the
  companion paper.

## Roadmap (v1.1)

1. **Full source-collation pass** over all verified statements (7f) — a
   page reference for every theorem, plus a systematic related-work survey;
   completion of this item is the submission gate for the companion paper.
   (Chapter 16, the observations chapter, joins the collation scope: it
   contains Keynes's named prose restatements of the key theorems.)
2. Popper-function countermodel certifying that the degeneracy theorem is
   unprovable in the pedantic encoding (6c-model).
3. External kernel re-check of the corpus via an independent verifier, to
   extend the trust chain beyond the shipping kernel.
4. **Phase 8 (research direction): the weight of argument.** Axiomatise
   Keynes's *weight* (Treatise, Ch. VI) alongside the audited probability
   calculus and formalise its role as the bridge to the *General Theory*'s
   treatment of confidence (GT Ch. 12) — the point where the boundary view
   meets macroeconomics.

## Citation

```
Arai, K. (2026). Keynes's Treatise on Probability, Part II: a Lean 4 kernel
audit. https://github.com/kazzarai/keynes-treatise-lean-audit
(canonical run v5, 2026-07-09, Lean 4 v4.29.1)
```

## License

MIT (see `LICENSE`). The Prolog database and documentation are included
under the same terms.
