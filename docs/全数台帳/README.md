# Formula census of the 1921 first edition (docs/全数台帳)

**Every printed formula of *A Treatise on Probability* (Macmillan, 1921; Cornell copy), all 33 chapters plus the Notes on Part III, counted one by one from the page images.** No transcription, OCR layer or translation was used as evidence; where a glyph could not be read it is marked `[?]`.

- `chNN.md` — one table per chapter, one row per printed formula or notation. `notes_III.md` — the Notes on Part III. `summary.csv` — one row per chapter (machine-readable).
- Counting rule (`materials/原典照合1921/全数台帳/数え方の規則.md`, summarised here): a **formula line** is any printed expression containing a relation symbol (=, ≠, <, ≤, ≡, ⊃, …); one printed line = one row (a five-line proof is five rows, each tied to its item). A **notation** is a compound expression without a relation symbol (`a/h`, `g(φ, f)`, `A_{a₁…aₙ}(φ)`); bare single symbols, even with subscripts or bars, are not counted. Footnotes, figures, tables and quoted formulae of other authors (Boole, Laplace, Czuber, …) are counted; re-statements are counted again and linked to the first occurrence. An **item** is a numbered theorem/definition/axiom, or a single un-numbered row.
- Columns: row id (`chNN-NNN`), folio, §, position (text / footnote n / figure / table), kind (display / inline), number, item id, transcription as printed (subscripts, bars, dashes, the inequality glyphs of the period), formula/notation, source author if quoted, re-statement link, **Lean status**, anchor words (3–6 printed words next to the formula, for locating it on the page image), remarks.
- Lean status, decided mechanically by one rule: **✓** the printed relation appears in a theorem statement (only bound-variable names, Lean notation and subscript layout may differ); **≈** the theorem states an algebraically equivalent form (denominators cleared, a definition substituted, hypotheses re-parametrised); **✎** the printed form is refuted and a corrected form is the theorem; **not yet** — nothing in the statement of any theorem (lines inside a proof, values absorbed by substitution, sums only). At item level, an item counts as covered if any of its lines is ✓/≈/✎.
- The names in the Lean column (`file/theorem`) are checked mechanically: stage [4] of `tools/check_all.sh` (`tools/check_ledger_refs.py`) fails if a name cited for a ✓/≈/✎ formula row or a notation row is not declared anywhere in `phases/`.

## Totals (v1.9)
Formula lines **1,175**; notations 731; items 698 (numbered 202). Lines whose relation appears in a theorem statement: ✓ 542 / ≈ 293 / ✎ 33; not yet 307 (Part V 141, Part I 81, Part II 50, Part III 18, Part IV 17 = 307; the 50 of Part II include Chapter 11 1 and Chapter 12 6, of which 2 are records of the boundary of the formalisation, besides the definition-only, restatement and quoted-author lines of Chapters 14, 16 and 17). Of the 307, 38 are definition-only (naming) lines, all in Part II. Items covered by at least one theorem: 416 / 698; numbered items 185 / 202. By part: I 21/102 items, II 333/358, III 44/62, IV 18/35, V 0/141. Part II (Chapters X–XVII) has 825 formula lines: ✓ 477 / ≈ 270 / ✎ 28 / not yet 50, of which 38 are definition-only.

The per-chapter figures below are the counts of the ledger rows (`chNN.md`, formula rows by Lean status) and agree with each chapter's own 集計 table; `summary.csv` is regenerated from the same rows for Part II, and its 'numbered' column is not uniform across parts (some chapters count numbered lines, some numbered items) — the table below is the one to cite.

## Per chapter
| Part | Ch. | Title | Formula lines | Items | Items covered | Numbered (covered/total) | ✓ / ≈ / ✎ / not yet (lines) | Notations |
|---|---|---|---|---|---|---|---|---|
| I | 1 | The Meaning of Probability | 1 | 1 | 0 | 0/0 | 0 / 0 / 0 / 1 | 0 |
| I | 2 | Probability in Relation to the Theory of Knowledge | 0 | 0 | 0 | 0/0 | 0 / 0 / 0 / 0 | 0 |
| I | 3 | The Measurement of Probabilities | 8 | 8 | 4 | 1/2 | 0 / 3 / 1 / 4 | 19 |
| I | 4 | The Principle of Indifference | 31 | 31 | 5 | 0/3 | 5 / 0 / 0 / 26 | 95 |
| I | 5 | Other Methods of Determining Probabilities | 16 | 16 | 0 | 0/3 | 0 / 0 / 0 / 16 | 22 |
| I | 6 | The Weight of Arguments | 32 | 32 | 13 | 2/5 | 11 / 2 / 0 / 19 | 26 |
| I | 7 | Historical Retrospect | 0 | 0 | 0 | 0/0 | 0 / 0 / 0 / 0 | 5 |
| I | 8 | The Frequency Theory of Probability | 14 | 14 | 3 | 0/0 | 2 / 1 / 0 / 11 | 14 |
| I | 9 | The Constructive Theory of Part I Summarised | 0 | 0 | 0 | 0/0 | 0 / 0 / 0 / 0 | 1 |
| II | 10 | Introductory | 29 | 26 | 26 | 9/9 | 23 / 6 / 0 / 0 | 13 |
| II | 11 | The Theory of Groups | 30 | 30 | 29 | 0/0 | 25 / 4 / 0 / 1 | 2 |
| II | 12 | The Definitions and Axioms of Inference and Probability | 56 | 30 | 24 | 17/21 | 40 / 10 / 0 / 6 | 16 |
| II | 13 | The Fundamental Theorems of Necessary Inference | 169 | 36 | 36 | 34/34 | 90 / 79 / 0 / 0 | 0 |
| II | 14 | The Fundamental Theorems of Probable Inference | 188 | 70 | 66 | 55/55 | 111 / 60 / 6 / 11 | 37 |
| II | 15 | Numerical Measurement and Approximation of Probabilities | 62 | 23 | 23 | 10/10 | 49 / 8 / 5 / 0 | 6 |
| II | 16 | Observations on the Theorems of Chapter XIV | 89 | 89 | 76 | 0/0 | 59 / 16 / 1 / 13 | 41 |
| II | 17 | Some Problems in Inverse Probability, including Averages | 202 | 54 | 53 | 49/49 | 80 / 87 / 16 / 19 | 20 |
| III | 18 | Introduction | 0 | 0 | 0 | 0/0 | 0 / 0 / 0 / 0 | 1 |
| III | 19 | The Nature of Argument by Analogy | 16 | 16 | 7 | 0/0 | 3 / 2 / 2 / 9 | 49 |
| III | 20 | The Value of Multiplication of Instances, or Pure Induction | 30 | 30 | 24 | 0/0 | 15 / 7 / 2 / 6 | 10 |
| III | 21 | The Nature of Inductive Argument Continued | 3 | 3 | 0 | 0/0 | 0 / 0 / 0 / 3 | 4 |
| III | 22 | The Justification of These Methods | 3 | 3 | 3 | 0/0 | 3 / 0 / 0 / 0 | 25 |
| III | 23 | Some Historical Notes on Induction | 0 | 0 | 0 | 0/0 | 0 / 0 / 0 / 0 | 0 |
| IV | 24 | The Meanings of Objective Chance, and of Randomness | 0 | 0 | 0 | 0/0 | 0 / 0 / 0 / 0 | 18 |
| IV | 25 | Some Problems arising out of the Discussion of Chance | 4 | 4 | 1 | 0/0 | 0 / 1 / 0 / 3 | 6 |
| IV | 26 | The Application of Probability to Conduct | 31 | 31 | 17 | 0/0 | 6 / 10 / 1 / 14 | 11 |
| V | 27 | The Nature of Statistical Inference | 0 | 0 | 0 | 0/0 | 0 / 0 / 0 / 0 | 0 |
| V | 28 | The Law of Great Numbers | 0 | 0 | 0 | 0/0 | 0 / 0 / 0 / 0 | 0 |
| V | 29 | The Use of A Priori Probabilities for the Prediction of Statistical Frequency | 83 | 83 | 0 | 0/2 | 0 / 0 / 0 / 83 | 106 |
| V | 30 | The Mathematical Use of Statistical Frequencies | 12 | 12 | 0 | 0/0 | 0 / 0 / 0 / 12 | 52 |
| V | 31 | The Inversion of Bernoulli's Theorem | 2 | 2 | 0 | 0/0 | 0 / 0 / 0 / 2 | 44 |
| V | 32 | The Inductive Use of Statistical Frequencies | 26 | 26 | 0 | 0/0 | 0 / 0 / 0 / 26 | 7 |
| V | 33 | Outline of a Constructive Theory | 18 | 18 | 0 | 0/0 | 0 / 0 / 0 / 18 | 79 |
| III | N3 | Notes on Part III | 20 | 10 | 10 | 9/9 | 20 / 0 / 0 / 0 | 2 |
| **all** | | | **1,175** | **698** | **416** | **185/202** | **542 / 293 / 33 / 307** | **731** |

## ℝ 依存 A〜E の本数 (第II部)

`tools/real_dependence.py` が `phases/keynes_part_ii_*.lean` の theorem・lemma・example 1,258 本を分類した値 (洗い出しのみ、判定ではない)。複数に当たるときは C > D > E > A′ > B > A (A′ = 順序付き環、比較可能性は不要)。台帳 ch12–ch17 の各行の「ℝ 依存」列は、その行の Lean 欄が指す定理・公理の class_trans (呼び先と公理の使用まで辿った最強値) で、定義のみ・境界の記録・数えない行・未対応は「—」。定義と内訳は `real_dependence.md`・`real_dependence.csv`。

表の数字は `python3 -I tools/real_dependence.py --write-ledger --write-readme` の出力を写したもの (手で直さない)。

| 単位 | A 順序のみ | A′ 順序付き環 | B 加法・乗法 | C 線形順序 | D 体の構造 | E 数値 | — | 計 |
|---|---|---|---|---|---|---|---|---|
| 定理・例 (第II部 38 ファイル、class: 字面のみ) | 419 | 12 | 142 | 490 | 84 | 111 | — | 1,258 |
| 定理・例 (同、class_trans: 呼び先・公理まで) | 176 | 14 | 163 | 700 | 105 | 100 | — | 1,258 |
| 台帳の行 (ch12–ch17、class_trans) | 50 | 8 | 129 | 456 | 65 | 37 | 162 | 907 |
