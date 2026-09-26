# Keynes's *Treatise on Probability* (1921), Part II — A Lean 4 Kernel Audit

**Machine-checked formalisation of the axiom system of J. M. Keynes's
*A Treatise on Probability*, Part II (Chapters 12–17), with exact kernel
dependency measurements for every verified theorem.**

- **100 / 100** numbered theorems of the reconstruction ledger
  kernel-checked — **every chapter complete** (13: 30/30, 14: 47/47,
  15: 6/6, 17: 17/17), with one annotation: (14.34) is verified in
  corrected form, its printed form being machine-refuted (see **Errata**)
- **261 kernel-checked `#print axioms` verdicts** across **24 files**
  (v8 = 236; phase 7i adds 25)
  (extensional development, intensional/`KeynesI` development, erratum
  countermodel, the source-form batch `7g`/`7h`, the weight trilogy
  `8a`–`8c`, the Ch. VI axiom-anchor file `8d`, and the 1921-image
  re-collation file `7i`) — zero `sorry`
- **Collation against the 1921 Macmillan page images (September 2026)**:
  every ledger row re-read on the scanned first edition (Cornell copy,
  archive.org `cu31924014110435`), which supersedes the July collation
  (Gutenberg transcription + Collected Writings translation). The image pass
  found 13 Lean statements that deviated from the printed propositions and
  five printed propositions that are false; both are resolved in `phase7i`.
  Fidelity tally (100 ledger rows): **86 verified as printed / 4 core
  verified (general form not assembled) / 1 index inconsistency (consistent
  form verified) / 4 strict inequalities (inclusive form verified, strictness
  refuted) / 5 printed propositions machine-refuted and verified in corrected
  form**. No theorem withdrawn. Row-by-row index:
  [`docs/COLLATION_INDEX_1921.md`](docs/COLLATION_INDEX_1921.md)
  (the July index `docs/COLLATION_INDEX_7F.md` is retained as history)
- **The weight trilogy (August 2026, `phase8a`–`8c`)**: Chapter 26's
  conventional coefficient *c* (footnote comparative statics F1–F3 verified,
  the F4 non-comparability adjudicated, superadditivity), the short-term
  probability weighting function W = p/(p+H) of Murata (2010) and
  Takayabu–Arai (2012) — **the 2012 subadditivity conjecture resolved**:
  refuted in its unrestricted reading (core fact: ln 2 > 1/2), a theorem for
  p₁+p₂ ≤ e/(1+e); subcertainty holds centrally and reverses at the edges —
  and Brady's weight V = K/(K+I) (monotonicity, limit, intersubjective-time
  counterexample). 39 theorems, floor-only: **no probability axioms used**
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
- Canonical, reproducible evidence: [`logs/keynes_audit_canonical_run_20260926_v9.log`](logs/keynes_audit_canonical_run_20260926_v9.log)
  records toolchain, dependency pins, **SHA-256 of every source file**, and
  the complete output of a single verified run (**24/24 files, exit 0**);
  regenerate with `bash run_v9.sh`. The v8 log (23 files), v7 log (22 files) and v6 log
  (19 files) are retained as development history

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
bash run_v9.sh                         # full canonical run (SHA-256-bound log)
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
| `phases/…phase7g.lean` | **Source-exact forms I** (from the 7f collation queue): full inclusion–exclusion (24.4)/(24.5), chained-exclusive additivity (24.6)/(24.7), total probability (25), posterior normalisation (25.1), overbar forms (26)/(26.1)/(28)/(28.1), the p=1/2 special case (40.1), the general m,n form of (50) on the intensional carrier (with `ax_mae` renamed **`ax_vii`** per the collation), and Keynes's six-equation elimination example (55) — verified at the substrate floor | +13 |
| `phases/…phase7h.lean` | **Source-exact forms II**: Johnson's multi-evidence formulae as **division-free product identities** — (46.1) at `{Pr, Def. X (both forms)}` + floor, no non-vanishing guards — (47.1), (48), (48.1), the (49) exchange step and (49.1) mixture core; the chain-complement recursion of (57)(i); and Boole's Problem X in full: closed form, the *true* (58.2) (log-convexity of the predictive sequence), and the posterior (58.3), with Boole's tacit assumption as the named hypothesis `NegChainIndep` | +14 |
| `phases/…phase8a.lean` | **Ch. 26 coefficient c** = 2pw/((1+q)(1+w)): risk identities R = pqA = qE, Czuber's reinsurance series, boundary values, footnote comparative statics F1–F3, the F4 adjudication (printed-direction theorem + amended-direction witnesses), superadditivity | +13 |
| `phases/…phase8b.lean` | **Short-term probability weighting** W = p/(p+H) (Murata 2010; Takayabu–Arai 2012): the 2012 subadditivity conjecture resolved — refutation at the center pair (ln 2 > 1/2; interior witness; base-2 twin) and the regional theorem p₁+p₂ ≤ e/(1+e) (derivative-free); subcertainty central/edge split; inverse-S certified | +16 |
| `phases/…phase8c.lean` | **Brady weight** V = K/(K+I): range, K-monotonicity (subjective time), the Brady limit I→∞, the intersubjective-time counterexample and its general form | +9 |
| `phases/…phase8d.lean` | **Ch. VI anchors** (first Part-I file): Keynes's own weight principles as axioms over a primitive `V` — monotonicity (§1), complement symmetry (§3), mutual-inference equivalence (§4) — with relevance defined as strict weight-increase (§2); the §3 dichotomy `th_vi_2` and Keynes's own three-alternative chain `th_vi_4`. **Load datum: the chain's kernel cut-set is `{Pr, V, ax_vi_compl, ax_vi_equiv}` — the monotonicity axiom is idle in Keynes's own Ch. VI derivation.** ℚ certificates for the §6 numerical example and urn pair; bridge to phase 8c (the §1 thesis holds when new evidence raises K alone, and has an intersubjective counterexample) | +9 |
| `prolog/keynes_axioms_v2.pl` | Citation database of Part II: 25 definitions/axioms, 100 theorems, 177 citation relations (SWI-Prolog) | — |
| `docs/COLLATION_INDEX_7F.md` | **Row-by-row collation index**: page/line anchor and fidelity status for every ledger row; errata catalogue; Boole (1854) attribution map | — |
| `phases/…phase7i.lean` | **1921-image re-collation**: the 13 statements the image pass found deviating from print, re-stated and verified in their printed form — (2)(3) disjunctive range forms, (10) three-term equality, (11) conclusion a/h=1, (37) chain-conditional hypothesis, (38.1) general two-alternative form, (43) separative-factor identities, (46.2) consistent two-letter form, (49.1) coefficient decomposition + monotonicity corollary, (56.4) bound triple, (57.1) the Π-coefficient equality itself, (57.2) bounds without independence, (57.3) Π-coefficient lower bound; plus machine refutations of five printed propositions — (35) non-strict hypothesis (8-region countermodel), (46.1) missing (x/h)ⁿ factor (8-region countermodel), (58.2) missing (1−q) factor and (58.3) exponent off by one (rational instances), (52)/(53) strictness — with the corrected forms verified | +25 |
| `logs/…canonical_run_20260926_v9.log` | **The citable evidence artifact** (24 files) | — |
| `run_v9.sh` | Regenerates the canonical log over `phases/*.lean` (SHA-256-bound) | — |
| `logs/…canonical_run_20260925_v8.log`, `…20260801_v7.log`, `…20260714_v6.log`, `…_v5.log`, `…_v4.log`, `…_v3.log`, `…20260708.log` | Superseded runs over earlier corpora (retained as development history) | — |
| `docs/PHASE6C_DESIGN.md` | Design notes for the intensional migration, incl. planned Popper-function countermodel | — |

## Reading a dependency list

```
'Keynes.th_13_12' depends on axioms: [propext, Classical.choice, Quot.sound,
 Keynes.Pr, Keynes.ax_iii_op, Keynes.ax_iii_true, Keynes.ax_range_lo, Keynes.def_IX]
```

- `propext, Classical.choice, Quot.sound` — the **floor**: Lean's own axioms
  (the classical-extensional substrate). Across all 24 files it never grows:
  no theorem needs a fourth kernel axiom. Recursors (`List.rec` etc.) never
  appear — induction and convergence are consumed by the kernel without
  leaving an axiom trace. The phase-8a–8c files declare no `Keynes.*` axioms at
  all — the weight layer is pure real analysis over the floor. Phase 8d is the
  exception by design: it declares Keynes's Ch. VI weight principles as named
  axioms (`KeynesWeightVI.ax_vi_*`) precisely so that `#print axioms` can
  report which of them his own derivation consumes.
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

Every item below was read on the page images of the 1921 Macmillan first
edition (September 2026); the Gutenberg transcription and the Japanese
Collected-Writings translation were used only as aids. (A July note claiming
a prose/proof reversal in (14.33) is **withdrawn**: the 1921 page reads "not
less favourable", consistent with the proof; the reversal was a Gutenberg
transcription error.)

Substantive — the printed proposition is false, machine-refuted, and
verified in corrected form:

- **(14.35)**, `phase7i`: the hypothesis "x is not **more** favourable to
  a/h than h₁x is" is printed non-strict; an 8-region rational countermodel
  satisfies all printed hypotheses (with equality in that one) while h₁ is
  irrelevant to a, so the conclusion fails. The strict form is verified
  (`th_14_35`, `phase7b`).
- **(14.46.1)**, `phase7i`: the display omits the factor (x/h)ⁿ that the
  cumulative formula (46) requires — the very omission Keynes calls "the
  second incorrect statement" on the same page. An 8-region countermodel
  with unequal priors breaks the printed proportionality; the form with the
  factor holds.
- **(17.58.2)**, `phase7i`: the numerator of the printed difference formula
  carries one factor (1 − q); the correct numerator is a(p−a)q^{n−2}(1−q)²
  (`th_17_58_2_numerator`, an identity). At a=½, p=¾, n=2 the true
  difference is 1/15, the printed expression 2/15.
- **(17.58.3)**, `phase7i`: the printed closed form a/[a+(p−a)qⁿ] has the
  exponent one too high; with y₁ = p the correct form is a/[a+(p−a)q^{n−1}]
  (n=1: 2/3 vs printed 4/5). The division-free form t_n·f(n) = a is
  verified (`phase7h`).
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

Minor — strict inequalities that are not derivable (equality is attainable;
the inclusive forms are what the corpus verifies): **(15.52)**, **(15.53)**,
**(17.56.2)**, **(17.56.5)** (`phase7i` exhibits the equality cases for
(52) and (53)). Typographical: **(14.46.2)** prints Π^{n−1} against
(x/h)^{−n}, an index mismatch; the consistent two-letter form is verified
(`th_14_46_2_src2`).

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
  **never load-bearing** in any verified dependency set in the corpus — even
  for (13.12.1), whose printed proof invokes it explicitly, the kernel
  route closes through certainty propagation (13.9) plus the equivalence
  theorem (13.12).
- **The July collation pass (7f)** anchored every ledger row to the Gutenberg
  transcription and the translation's page images and reported
  93 exact / 6 faithful-core / 1 erratum. **The September pass against the
  1921 first-edition page images supersedes it**: it found that 13 Lean
  statements had drifted from the printed propositions (weakened, partial,
  or differently stated) and that five printed propositions are false.
  Both are resolved in `phase7i`; the honest tally is now
  **86 / 4 / 1 / 4 / 5** as defined above. Lesson recorded for the method:
  a transcription and a translation are not independent enough to stand in
  for the printed page. See `docs/COLLATION_INDEX_1921.md`.
- The weight trilogy (`phase8a`–`8c`) lies **outside** the 100-item Part-II
  ledger; its source anchors are Ch. VI / Ch. XXVI and Takayabu–Arai (2012)
  (see the file headers for verbatim attribution, including the first
  formulation of W in Murata 2010).

## Roadmap (v1.5)

1. ~~**Full source-collation pass** (7f, July 2026)~~ superseded by the
   ~~**1921 first-edition image pass** (7i, September 2026)~~ — **done**.
   Remaining: Chapter 16 (prose restatements, no numbered theorems); the four
   core items ((44), (46), (49), (49.1) in general n-letter form); and
   **Chapter 17 §§3–12** (the 1911 JRSS "principal averages" material, 41
   un-numbered formulae, ledgered under Keynes's 1911 numbering — not yet
   formalised).
2. Popper-function countermodel certifying that the degeneracy theorem is
   unprovable in the pedantic encoding (6c-model).
3. External kernel re-check of the corpus via an independent verifier, to
   extend the trust chain beyond the shipping kernel.
4. ~~Phase 8: the weight of argument~~ — **done (August–September 2026)**:
   the Ch. 26 coefficient, the 2012 weighting function (conjecture
   resolved), Brady's V, and the Ch. VI axiom anchors (8d, first Part-I
   file: the monotonicity principle is idle in Keynes's own derivation) are
   verified (canonical run v8). Remaining: the GT Ch. 12 bridge.
   A Keynes–Ramsey track is flagged in `ramsey/` (scope only, no results).
5. Phase 9: replicate and adjudicate the 2012 Prolog structural analysis
   (the derivation-order lattice question, the INRC-group embedding, and
   ledger provenance from the thesis appendices).

## Citation

```
Arai, K. (2026). Keynes's Treatise on Probability, Part II: a Lean 4 kernel
audit. https://github.com/kazzarai/keynes-treatise-lean-audit
(release v1.3; canonical run v9, 2026-09-26, Lean 4 v4.29.1)
```

## License

MIT (see `LICENSE`). The Prolog database and documentation are included
under the same terms.
