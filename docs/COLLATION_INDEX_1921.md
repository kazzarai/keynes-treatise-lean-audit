# 1921年初版画像照合索引 (v1.3) — 台帳100定理 × Macmillan 1921 folio × Lean

**基準**: 1921年 Macmillan 初版の頁画像 (Cornell 蔵書、archive.org cu31924014110435; PDF頁 = folio + 20)。tex・佐藤訳・既存Leanは補助。
**照合**: 2026-09-26、5班並列 + 新井/Claude による L/K 全件の再判定。詳細は `原典照合1921/照合_A〜E.md`。
**処置**: Phase 7i (`phases/keynes_part_ii_phase7i.lean`, 25判定) — 逸脱13本を印刷形で再定理化、原著側の誤りを機械反駁。

## 最終分類 (100項目)

| 分類 | 本数 | 意味 |
|---|---|---|
| E 印刷どおり検証 | 86 | 印刷命題と同一の主張がカーネル通過 (7i で修復した13本を含む) |
| C 中核一致 | 4 | 数学的中核は検証済、印刷の一般形は未組み上げ |
| T 添字不整合 | 1 | 印刷の添字が整合せず、整合形を検証 |
| S 狭義不等号 | 4 | 印刷の狭義不等号は導出不能 (等号事例)、包含形を検証 |
| F 印刷形は偽 | 5 | 印刷命題が反例つきで機械反駁され、修正形を検証 |

## 行別

| 章 | 定理 | folio | Phase (Lean) | 分類 | 注記 |
|---|---|---|---|---|---|
| 13 | (1) | 139 | P2 | E |  |
| 13 | (2) | 139 | P2 → 7i th_13_2_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 13 | (3) | 139 | P2 → 7i th_13_3_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 13 | (4) | 140 | 6b | E |  |
| 13 | (5) | 140 | 6b | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 13 | (6) | 140 | 6b | E |  |
| 13 | (7) | 140 | 6b | E |  |
| 13 | (8) | 140 | 6b | E |  |
| 13 | (9) | 140 | 6b | E |  |
| 13 | (10) | 140 | 6b → 7i th_13_10_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 13 | (11) | 141 | 6b → 7i th_13_11_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 13 | (12) | 141 | 6b | E |  |
| 13 | (12.1) | 141 | 7c | E |  |
| 13 | (13) | 141 | 6b | E |  |
| 13 | (13.1) | 141 | 6b | E |  |
| 13 | (13.2) | 141 | 6b | E |  |
| 13 | (14) | 141 | 6b | E |  |
| 13 | (15) | 141 | 6b | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 13 | (15.1) | 142 | 7c | E |  |
| 13 | (16) | 142 | 7c | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 13 | (16.1) | 142 | 7a | E |  |
| 13 | (16.2) | 142 | 7c | E |  |
| 13 | (16.3) | 142 | 7a | E |  |
| 13 | (17) | 142 | 7c | E |  |
| 13 | (18) | 142 | 6b | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 13 | (19) | 142 | P2 | E |  |
| 13 | (20) | 143 | P2 | E |  |
| 13 | (21) | 143 | 6b | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 13 | (22) | 143 | 6b | E |  |
| 13 | (23) | 143 | 6b | E |  |
| 14 | (24) | 144 | pilot | E |  |
| 14 | (24.1) | 144 | pilot | E |  |
| 14 | (24.2) | 144 | 3a | E |  |
| 14 | (24.3) | 144 | 6b | E |  |
| 14 | (24.4) | 145 | 6b→7g | E |  |
| 14 | (24.5) | 145 | 6b→7g | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 14 | (24.6) | 145 | 6b | E |  |
| 14 | (24.7) | 145 | 6b | E |  |
| 14 | (25) | 145 | 6a | E |  |
| 14 | (25.1) | 145 | 6a→7g | E |  |
| 14 | (26) | 146 | 6b→7g | E |  |
| 14 | (26.1) | 146 | 6b | E |  |
| 14 | (27) | 146 | 6b | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 14 | (27.1) | 146 | 6b | E |  |
| 14 | (28) | 146 | 6b→7g | E |  |
| 14 | (28.1) | 146 | 6b | E |  |
| 14 | (29) | 146 | 6b | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 14 | (30) | 146 | 7b | E |  |
| 14 | (31) | 147 | 6b | E |  |
| 14 | (32) | 147 | 6b | E |  |
| 14 | (33) | 147 | 7b | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 14 | (34) | 147 | 7d★ | F | printed bridge refuted (7d countermodel); repaired form verified |
| 14 | (35) | 148 | 7b | F | non-strict "not more favourable" refuted (7i Erratum35); strict repair verified (7b th_14_35) |
| 14 | (36) | 148 | 3a | E |  |
| 14 | (37) | 148 | 6b → 7i th_14_37_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 14 | (38) | 148 | 3a | E |  |
| 14 | (38.1) | 148 | 3d → 7i th_14_38_1_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 14 | (39) | 150 | 7b | E |  |
| 14 | (40) | 150 | 7b | E |  |
| 14 | (41) | 150 | 3b | E |  |
| 14 | (41.1) | 151 | 3c | E |  |
| 14 | (41.2) | 151 | 6b | E |  |
| 14 | (42) | 151 | 3b | E |  |
| 14 | (42.1) | 151 | 3c | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 14 | (42.2) | 151 | 7e | E |  |
| 14 | (43) | 151 | 3c → 7i th_14_43_src(+_2) | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 14 | (44) | 151 | 3b | C | notational convention; 7f terminal state |
| 14 | (44.1) | 151 | 3b | E |  |
| 14 | (45) | 151 | 3c | E |  |
| 14 | (46) | 151 | 3d | C | core verified (7h); full cumulative chain not assembled |
| 14 | (46.1) | 152 | 6a→7h | F | factor (x/h)^n omitted; proportionality refuted (7i Erratum46_1); (46) with factor verified |
| 14 | (46.2) | 153 | 6a→7h | T | index inconsistency Π^{n−1} vs (x/h)^{−n}; consistent 2-letter form verified (7i th_14_46_2_src2) |
| 14 | (47) | 153 | 3d→7h | E |  |
| 14 | (47.1) | 153 | 6a→7h | E |  |
| 14 | (48) | 153 | 3d→7h | E |  |
| 14 | (49) | 154 | P5→7h | C | core verified (7h); full monotone sequence not assembled |
| 14 | (49.1) | 155 | 6a→7h → 7i | C | 2-letter identity + monotonicity corollary verified (7i); general n-letter form not assembled |
| 15 | (50) | 159 | P4→7g | E |  |
| 15 | (51) | 162 | P4 | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 15 | (52) | 162 | P4 | S | printed strict >; inclusive ≥ verified (P4); strictness fails when both propositions certain (7i) |
| 15 | (53) | 162 | P4 | S | printed strict <; inclusive ≤ verified (P4); strictness fails at y=x (7i) |
| 15 | (54) | 162 | P4 | E |  |
| 15 | (55) | 163 | P4→7g | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 17 | (56) | 186 | P5 | E |  |
| 17 | (56.1) | 188 | P5 | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 17 | (56.2) | 189 | P5 | S | printed strict <; inclusive verified (P5); equality attainable |
| 17 | (56.3) | 189 | P5 | E |  |
| 17 | (56.4) | 189 | P5 → 7i th_17_56_4_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 17 | (56.5) | 189 | P5 | S | printed strict >; inclusive verified (P5); equality attainable |
| 17 | (57) | 189 | P5→7h | E | Gutenberg tex garbled here; Lean follows the 1921 image |
| 17 | (57.1) | 190 | 6a → 7i th_17_57_1_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 17 | (57.2) | 191 | P5 → 7i th_17_57_2_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 17 | (57.3) | 191 | 6a → 7i th_17_57_3_src | E | 7f Lean deviated from print; re-stated in printed form (7i) |
| 17 | (57.4) | 191 | 6a | E |  |
| 17 | (57.5) | 191 | 6a | E |  |
| 17 | (57.6) | 191 | P5 | E |  |
| 17 | (58) | 192 | P5→7h | E |  |
| 17 | (58.1) | 193 | P5→7h | E |  |
| 17 | (58.2) | 193 | P5→7h | F | numerator lacks a factor (1−q); refuted at a=1/2,p=3/4,n=2 (7i Erratum58); corrected (1−q)^2 verified (7h core, 7i) |
| 17 | (58.3) | 193 | P5→7h | F | closed form exponent n should be n−1; refuted at n=1 (7i Erratum58); t_n·f(n)=a verified (7h) |

## 6c (内包版、B09 修復 2026-10-20) — T: 前提の補充 (台帳100項目の外)

Phase 6c (`phases/keynes_part_ii_phase6c.lean`) states the following on the intensional carrier (`IProp`, `PrI`) with a premiss `Cons h` ("h is not an inconsistent conjunction", Axiom (i) proviso, folio 135) that the printed formula does not carry. "T" here means *premiss supplied*, not the index-inconsistency sense used in the 100-row ledger above; these rows are outside that ledger and do not change its totals.

| 章 | 定理 | folio | Phase (Lean) | 分類 | 注記 |
|---|---|---|---|---|---|
| 13 | (1) | 139 | 6c th_13_1_i | T | Printed a/h + ā/h = 1 has no proviso; Lean adds Cons h, since the step b/h = 1 in Keynes's proof exists only for a consistent premiss (Axiom (i)). |
| 13 | (12) | 141 | 6c th_12_i, th_12_i_short | T | Printed "If (a≡b)/h = 1, a/h = b/h" has no proviso; Lean adds Cons h, the range in which (a≡b)/h exists (Axiom (i)). |
| 13 | (13) | 141 | 6c th_13_13_conj_i | T | Printed "a/a = 1, unless a is inconsistent"; Lean states the premiss-(a∧h) form a/(a∧h) = 1 with Cons h and Cons (a∧h), because the 6c axiom set has no premiss substitution (Axiom (ii)). |
| 14 | (24) | 144 | 6c th_24_i | T | Printed (a+b)/h = a/h + b/h − ab/h has no proviso; Lean adds Cons h, inherited from the substitution principle (12) used in the proof. |

## 撤回

- (33): Phase 7d ヘッダの「原典散文が証明と逆向き」は Gutenberg 転記誤り ("not more")。1921年版は "not less favourable" で命題文と証明が整合。正誤表から外す。

## Gutenberg tex の転記崩れ (台帳範囲、Lean は画像準拠)

(5) 番号欠落 / (15) h₁h₂/h・by II. / (16) 内側バー / (18) a/a=1 / (21) a/h₂ / (24.5) 指数 (−1)^{n−1} / (27) by (v.) / (29) h₂側の追加 / (33) not more→not less / (42.1) 波括弧 / (49) x̄/h / (49.1) −1 の位置 / (51) x/ȳh / (55) μ⩽ / (56.1) 4箇所 / (57) 二重バー・余分な /

## 第 III 部 第 XX・XXII 章 (phase9a、台帳外、分類は裁定待ち)

照合: `原典照合1921/img_partIII/folio_235–238.png`, `folio_254.png`、台帳 `第III部帰納/台帳_ch20_純粋帰納.md`。Lean: `phases/keynes_part_iii_phase9a.lean`。分類欄は作業役の候補で、裁定は司令塔。

| 章 | 式 | folio | Phase (Lean) | 分類 (候補) | 注記 |
|---|---|---|---|---|---|
| 20 | F20.6 第 2 段 (E-III-1) | 235 | 9a th_20_6_src / ErratumE_III_1 / th_20_6_cor | F | 第 2 段の分子は印刷では `x_n/hx_1…x_{n−1}` で g が脱落 (結合確率 `g x_n/hx_1…x_{n−1}` であるべき)。印刷のままでは第 2 段は p_n = 1 のときに限り成り立つ (th_20_6_src)。数値反駁 p_0=1/8, p_1=1/4, p_2=1/2 (ErratumE_III_1)。g を復した 4 段を検証 (th_20_6_cor; 条件 p_0 ≠ 0, x_1…x_n/h ≠ 0)。第 1・3・4 段のみの連鎖は th_20_6_lines134 |
| 22 | folio 254 の条件 `x_r/x_1…x_{r−1}ḡh = 1 − ε` (E-III-2) | 254 (対 237) | 9a th_22_254_eq_src / th_E_III_2_not_lt / th_E_III_2_refutes_F20_16 / th_22_254_eq_exact | E または T | 第 XX 章 folio 237 は `< 1 − ε`、folio 254 は `= 1 − ε`。等号版は同じ ε で第 XX 章の印刷前提を満たさず (a)、脚注 F20.16 の `< (1 − ε)^n` を反証する (b) が、ε/2 を取れば印刷形 th_20_15_src から極限が出る (c)。結論は壊れない (E 寄り)。章間の不整合として T も候補 |
| 20 | F20.9 `p_n > p_{n−1} so long as y_n ≠ 1` (F20.9-a) | 236 | 9a th_20_9_src / th_20_9_iff / th_20_9_needs_p_pos / th_20_9_J_zero / Witness_F20_9_J | S または C | Keynes が明示しない前提 p_{n−1} > 0 と x_1…x_{n−1}/h ≠ 0 (前提が不可能でない) を付して検証。p_{n−1} = 0 なら (y_n ≠ 0 のもとで) p_n = 0 で狭義不等号は破れる (th_20_9_needs_p_pos、公理群の中)。x_1…x_{n−1}/h = 0 なら p_0 = 0 で p_n は定まらない (th_20_9_J_zero、数値例 Witness_F20_9_J)。脚注 F20.13 (folio 236) は同文の再掲 |

phase9a の末尾は、phase6c 由来の公理群 (`def_VIII_i` と `ax_iii_taut` を不整合な証拠に適用) が矛盾を導くこと (`th_6c_axioms_inconsistent`) を記録する。修復は phase6c の管轄で裁定待ち。

## 8a/8d のアンカー (台帳外)

phase8a: 第26章§7 の係数・恒等式・脚注 F1〜F4 は folio **315** の印刷と一致 (Lean コメントの folio 314 は誤記)。F4 の印刷仮定 w=w′, q>q′ を画像で確定、印刷の「比較不能」は脚注内で自己矛盾 (keynes_F4_printed_determinate)。
phase8d: 第6章の文言・数値アンカー (§1 核文、§3 補元対称、§4 三択連鎖、§6 分数、§8 和/差) は folio 71–79 の印刷と一致。

## 第26章 (台帳外: `原典照合1921/台帳_ch26.md`、phase8a / phase8a2、2026-10-20 更新)

folio 307–323 の全葉を画像で通読し、記号式 27 件 (F26.1–F26.27) を台帳化。8a 未検証分を `phases/keynes_part_iv_phase8a2.lean` で定理化 (36 判定)。分類は上の E/C/T/S/F に倣う。「候補」は所見候補 (正誤表への採否は裁定待ち)。F26.23 の S は「疑義 (印刷にない設定を置いた上での不一致)」の意味で用いる (狭義不等号ではない; 第26章限りの用法、裁定待ち)。

| 章 | 台帳 | folio | Phase (Lean) | 分類 | 注記 |
|---|---|---|---|---|---|
| 26 | F26.1–7 | 315 | 8a `c`, `risk_identities`, `c_one_one`, `c_zero_*` | E | 係数 c = 2pw/((1+q)(1+w))、R = p(A−E) = pqA = qE、境界値 |
| 26 | F26.8 | 315 fn1 | 8a2 `th_26_fn1_second_order_risk`, `czuberRisk` | E | R₁ = qR = q²E (印刷どおり) |
| 26 | F26.9 | 315 fn1 | 8a2 `th_26_fn1_printed_iff`, `th_26_fn1_printed_refuted`, `th_26_fn1_consistent_R`, `th_26_fn1_consistent_reindexed`, `th_26_fn1_czuber_tsum` | T 候補 | 印刷は R₁ = qR = q²E と定義した上で E+R₁+R₂+… = E(1+q+q²+…) = E/(1−q) = E/p = A と書く。この定義では左辺は E(1+q²+q³+…) で、第 1 の等号は qE = 0 のときのみ (q = 1/2, E = 1 で 3/2 ≠ 2)。整合形 (一次のリスク R を級数に含める / 添字を R₁ = qE と読み替える) と係数級数 E/(1−q) = E/p = A を検証 |
| 26 | F26.10–12 | 315 fn2 | 8a `keynes_F1`–`keynes_F3` (8a2 `th_26_fn2_F2`) | E | 脚注 2 の F1–F3 |
| 26 | F26.13 (F4) | 315 fn2 | 8a `keynes_F4_*` → 8a2 `th_26_fn2_F4_printed_determinate`, `_amended_witness_lt/gt` | F | 印刷「w=w′, q>q′ では一般に比較できない」は F2 の記号交換で cA < c′A′ が確定 (8a 既出、正誤候補 #3); 修正案 w>w′, q>q′ は両向きの証人で真に非比較 |
| 26 | F26.14 | 316 | 8a2 `th_26_first_head` (補助) | E | 利得規則 2^{r−1} の確率模型 (1/2)^r |
| 26 | F26.15 / F26.17 | 317 | 8a2 `th_26_petersburg_term`, `th_26_petersburg_finite`; 必要性 `th_26_petersburg_term_r0` | E | Σ_1^n (½)^r 2^{r−1} = n/2 |
| 26 | F26.16 / F26.17 | 317 | 8a2 `th_26_petersburg_unbounded`, `_tendsto`, `_not_summable` | E | 「無限の和」の三形 |
| 26 | F26.18 / F26.19 | 317 | 8a2 `th_26_bernoulli_deriv`, `th_26_bernoulli_initial` (補助) | E | dy = k dx/x ⇒ y = k log(x/a) |
| 26 | F26.20 | 318 | 8a2 `th_26_moral_expectation`; 反例 `th_26_laplace_printed_refuted` | F 候補 | 印刷 x = (a+x₁)p₁(a+x₂)p₂… は指数 p₁, p₂ がベースラインに落ちている; 文字どおりの積は a = 1, x_i = 1, p_i = ½ で偽; 指数形 Π(a+x_i)^{p_i} を検証 |
| 26 | F26.21 | 318 | 8a2 `th_26_bernoulli_summable`, `th_26_bernoulli_stake_strict`, `th_26_bernoulli_stake_bounds` | E | 印刷「£1000 の財産で £6 の掛金」: 対数効用の公平掛金 s* は存在して 5.9 < s* < 6 (log の Taylor 評価、s* ≈ 5.97); £6 ちょうどは払い過ぎ。「£6」は丸めの読み |
| 26 | F26.22 | 318 | 8a2 `th_26_cramer_cap`; `th_26_two_pow_24`, `th_26_printed_16777116_refuted` | F 候補 | 「2²⁴ (16,777,116)」は 16,777,216 の誤り (百の位); 結論 £13 は検証 |
| 26 | F26.23 | 318 | 8a2 `th_26_cramer_sqrt_expectation`, `th_26_cramer_sqrt_stake`, `th_26_cramer_sqrt_dubious` | S | 印刷「£2 : 9s.」; Paul の初期財産 0 という印刷にない設定の下では 3/2 + √2 ≈ £2 18s 3d (Cramer 原文「約 2.9」の読み替えか)。設定を置いた判定なので疑義に留める |
| 26 | F26.24 | 319 | 8a2 `th_26_relative_risk`, `th_26_relative_risk_tendsto`, `th_26_petersburg_risk_unbounded` | E | 解釈つき (R の多結果への拡張は印刷にない); 1 − 1/n ≤ R/E < 1、R/E → 1、R は非有界 |
| 26 | F26.25 | 319 | 8a2 `th_26_laurent_poorer` | C | f(a) = b/(a+b) 自体は Laurent の引用 (Keynes も導出せず)、単調性のみ検証 |
| 26 | F26.26 | 319 | 8a2 `th_26_laurent_limit` | E | 「b = ∞ なら f(a) = 1」を b → ∞ の極限で |
| 26 | F26.27 | 322 | — | — | Buffon の 1/10,000 (経験的定数、対象外) |
| 26 | F 補 1 | 311 fn1 | 8a2 `th_26_fn_leibniz_division` (補助) | E | Leibniz の比例分割 (言語的記述) |