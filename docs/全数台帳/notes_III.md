# 全数台帳 notes_III — "Notes on Part III" (i.) On the Use of the Term *Induction* / (ii.) On the Use of the Term *Cause*

- folio 274–280 (PDF 頁 294–300)。Notes の本文は 274–277、278 は白紙、279 は第IV部の中扉 ("PART IV / SOME PHILOSOPHICAL APPLICATIONS OF PROBABILITY")、280 は白紙 (裏)。
- 読了頁 (順に閲覧): 274, 275, 276, 277, 278, 279, 280 (全 7 頁)。274–278 は `原典照合1921/img_partIII/folio_NNN.png` (130 dpi 相当)。279, 280 は img_partIII に無かったので、Cornell PDF (頁 299, 300) から `原典照合1921/render_tool` (pdf_pages.py → batch_render.py、純 Python JBIG2 復号) で描画し、第 2 回で `原典照合1921/img_all/folio_279.png`, `folio_280.png` (縮小版 722×1204) と `img_all/hires/folio_279.png`, `folio_280.png` (原寸 1445×2408) に置いた (OCR 層 p299.txt の先頭行「PART IV … 279」で頁番号を照合; p300.txt は空)。描画は他の img_all と同じ白黒反転 (地が黒) の様式。
- 276 (定義 (i.)–(ix.))、277 (§4) は原寸 (1445×2408) を 2–3 倍に切り出して再確認。
- 数え方: `materials/原典照合1921/全数台帳/数え方の規則.md` の本則と補則 1〜8 (司令塔裁定 2026-10-24、補則 8 は 2026-10-25) に従う。第III部での運用細則 (裸記号の範囲、省略点列、数列、参考行、項目 ID、Lean 対応の 4 値) は ch18.md ヘッダに一括して書き、各章はそれを参照する。 **番号欄**: 印刷の項目番号 (i.)–(ix.) を番号欄と項目 ID に書き、「番号付き」に数える (裁定事項: 式番号ではなく定義の項目番号)。1 項目に複数の条件式があれば式ごとに 1 行。
- 活字の注記: `≠` は `=` に縦棒を重ねた活字 (原寸で確認)。`ā` は a の上バー。
- ヘッダ注記 (裸記号・語): 274 `ἐπαγωγή` (ギリシャ語の語、式ではない); 276 `k`, `l`, `a`, `b`, `A`, `B`, `h` (「k and l」「a and b」「A and B」は裸記号の対); 277 `a`, `b`。277 の並置 `kl` (2 回) は ch18-001 `AB` と同じ基準で記法 (notes-021, 022; 第 1 回はここに入れていたのを読み手役の指摘で修正)。
- 既存台帳との突き合わせ: `第III部帰納/台帳_ch21_22_正当化.md` 付録 B は 276 を「確率式あり (9 定義)」、277 を「確率式あり (1)」と記録 (項目単位)。本台帳は条件式単位で 276 に 19 本、277 に 1 本。(viii.) の第 2 条件が `b/hk ≠ 1` (l なし) で (ix.) の `b/hkl ≠ 0` と非対称である点は既存台帳・索引 (E-III-4) と一致。
- Lean: `phases/keynes_part_iii_phase9c.lean` §5 (`Notes_ii.SuffCause`, `NecCause`, `Def_iii`, `LawOfCausation`, `SuffCauseUnder`, `NecCauseUnder`, `PossSuffCause`, `PossNecCause`, `PossSuffCauseUnder_src`, `PossSuffCauseUnder_l`, `PossNecCauseUnder`, `CausallyIndependent`, `DepForProb`; Keynes 体系への特殊化 `def_viii_src`, `def_viii_l`, `def_ix`, `def_x_src`, `dep_for_prob`; 定理 `notes_viii_certain_add_l`, `def_viii_l_imp_src`, `def_viii_l_dep`, `def_ix_dep`, `def_x_src_symm`, 反例 `E_III_4_countermodel`, `E_III_4_corrected_imp_printed`)。索引: E-III-4 (notes-014)、(viii.)(ix.) の h の量化の補充 (注記)。
- Lean 対応の判定 (補則 8 の ✓; ch18.md 細則 6): (i.)–(ix.) と §4 の式は「If 条件式, A is …」の定義で、Lean の `def` (Notes_ii.*) の本体にその条件式がそのまま現れる (前提の連言 akl は `R.conj a (R.conj k l)` の結合順で書かれる) ので ✓ とする。notes-014 は印刷形 (l なし) が `PossSuffCauseUnder_src` の本体にそのまま現れるので ✓ (l を補った形は別の def)。
- 第 1 回からの変更 (第 2 回): 277 の `kl` を記法 2 行 (notes-021, 022) に立てた (記法 0 → 2)。式 20 行の Lean 対応は補則 5 でも維持。
- 第 2 回からの変更 (第 3 回): (1) 補則 8 により式 20 行の Lean 欄を ✓ にした (Lean 欄は def 名、帰結の定理は備考)。(2) 読み手役 第 2 回 F候補7: 「うち番号付き」を式行の単位 19 (notes-001–019) と項目の単位 9 ((i.)–(ix.)) に分けて集計行に併記し、summary.csv の `うち番号付き` 列は式行の単位 (19) と定めた (ch18.md 細則 5)。項目数 10 は (i.)–(ix.) の 9 と notes-020 の 1。

| 行ID | folio | § | 位置 | 種別 | 番号 | 項目ID | 転記 (印刷どおり) | 式/記法 | 引用元 | 再掲 | 既存の Lean (phase/名前) | 照合語 | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| notes-001 | 276 | (ii.) 3 | 本文 | 行内 | (i.) | (i.) | `b/ak = 1,` | 式 | — | — | ✓ phase9c/Notes_ii.SuffCause (def 本体) | `(i.) If` / `, A is a sufficient cause of B.` | 十分原因 |
| notes-002 | 276 | (ii.) 3 | 本文 | 行内 | (ii.) | (ii.) | `b/āk = 0,` | 式 | — | — | ✓ phase9c/Notes_ii.NecCause (def 本体) | `(ii.) If` / `, A is a necessary cause of B.` | 必要原因 |
| notes-003 | 276 | (ii.) 3 | 本文 | 行内 | (iii.) | (iii.) | `b/ak = 1.` | 式 | — | notes-001 | ✓ phase9c/Notes_ii.Def_iii (def 本体) | `a sufficient cause of B unless` | k が全法則を含む場合 |
| notes-004 | 276 | (ii.) 3 | 本文 | 行内 | (iii.) | (iii.) | `b/ak = 1.` | 式 | — | notes-001 | ✓ phase9c/Notes_ii.LawOfCausation (def 本体) | `prior to B, such that` / `No use has been made` | 因果律の言い換え |
| notes-005 | 276 | (ii.) 3 | 本文 | 行内 | (iv.) | (iv.) | `b/akl = 1` | 式 | — | — | ✓ phase9c/Notes_ii.SuffCauseUnder (def 本体) | `(iv.) If` / `and` | 条件 l 下の十分原因、第 1 条件 |
| notes-006 | 276 | (ii.) 3 | 本文 | 行内 | (iv.) | (iv.) | `b/kl ≠ 1,` | 式 | — | — | ✓ phase9c/Notes_ii.SuffCauseUnder (def 本体) | `and` / `, A is a sufficient cause of B under conditions l.` | 第 2 条件 |
| notes-007 | 276 | (ii.) 3 | 本文 | 行内 | (v.) | (v.) | `b/ākl = 0` | 式 | — | — | ✓ phase9c/Notes_ii.NecCauseUnder (def 本体) | `(v.) If` / `and` | 条件 l 下の必要原因、第 1 条件 |
| notes-008 | 276 | (ii.) 3 | 本文 | 行内 | (v.) | (v.) | `b/kl ≠ 0,` | 式 | — | — | ✓ phase9c/Notes_ii.NecCauseUnder (def 本体) | `and` / `, A is a necessary cause of B under` | 第 2 条件 |
| notes-009 | 276 | (ii.) 3 | 本文 | 行内 | (vi.) | (vi.) | `b/ahk = 1` | 式 | — | — | ✓ phase9c/Notes_ii.PossSuffCause (def 本体) | `existential proposition h such that` | 可能的十分原因、第 1 条件 |
| notes-010 | 276 | (ii.) 3 | 本文 | 行内 | (vi.) | (vi.) | `b/hk ≠ 1,` | 式 | — | — | ✓ phase9c/Notes_ii.PossSuffCause (def 本体) | `and` / `, A is, relative to k, a possible sufficient cause` | 第 2 条件 |
| notes-011 | 276 | (ii.) 3 | 本文 | 行内 | (vii.) | (vii.) | `b/āhk = 0` | 式 | — | — | ✓ phase9c/Notes_ii.PossNecCause (def 本体) | `existential proposition h such that` | 可能的必要原因、第 1 条件 |
| notes-012 | 276 | (ii.) 3 | 本文 | 行内 | (vii.) | (vii.) | `b/hk ≠ 0,` | 式 | — | — | ✓ phase9c/Notes_ii.PossNecCause (def 本体) | `and` / `, A is, relative to k, a possible necessary cause` | 第 2 条件 |
| notes-013 | 276 | (ii.) 3 | 本文 | 行内 | (viii.) | (viii.) | `b/ahkl = 1,` | 式 | — | — | ✓ phase9c/Notes_ii.PossSuffCauseUnder_src (def 本体), phase9c/def_viii_src | `(viii.) If` | 条件 l 下の可能的十分原因、第 1 条件。(viii.)(ix.) は (vi.)(vii.) と異なり「there is an existential proposition h」を書かない (索引注記) |
| notes-014 | 276 | (ii.) 3 | 本文 | 行内 | (viii.) | (viii.) | `b/hk ≠ 1,` | 式 | — | — | ✓ phase9c/Notes_ii.PossSuffCauseUnder_src (def 本体、印刷形), phase9c/def_viii_src | `b/ahkl = 1,` (直前) / `and h/akl ≠ 0` | 第 2 条件に `l` が無い ((iv.) は `b/kl`、(ix.) は `b/hkl`; 索引 E-III-4、S 疑義)。印刷形がそのまま def 本体にあるので ✓。l を補った形は phase9c/Notes_ii.PossSuffCauseUnder_l, phase9c/def_viii_l、関係は phase9c/def_viii_l_imp_src, phase9c/E_III_4_countermodel, phase9c/E_III_4_corrected_imp_printed |
| notes-015 | 276 | (ii.) 3 | 本文 | 行内 | (viii.) | (viii.) | `h/akl ≠ 0,` | 式 | — | — | ✓ phase9c/Notes_ii.PossSuffCauseUnder_src (def 本体), phase9c/def_viii_src | `and` / `, A is, relative to k,` | 第 3 条件 |
| notes-016 | 276 | (ii.) 3 | 本文 | 行内 | (ix.) | (ix.) | `b/āhkl = 0,` | 式 | — | — | ✓ phase9c/Notes_ii.PossNecCauseUnder (def 本体), phase9c/def_ix | `(ix.) If` | 条件 l 下の可能的必要原因、第 1 条件 |
| notes-017 | 276 | (ii.) 3 | 本文 | 行内 | (ix.) | (ix.) | `b/hkl ≠ 0,` | 式 | — | — | ✓ phase9c/Notes_ii.PossNecCauseUnder (def 本体), phase9c/def_ix | `b/āhkl = 0,` (直前) | 第 2 条件 (l あり) |
| notes-018 | 276 | (ii.) 3 | 本文 | 行内 | (ix.) | (ix.) | `h/ākl ≠ 0,` | 式 | — | — | ✓ phase9c/Notes_ii.PossNecCauseUnder (def 本体), phase9c/def_ix | `b/hkl ≠ 0,` (直前) / `and` | 第 3 条件 |
| notes-019 | 276 | (ii.) 3 | 本文 | 行内 | (ix.) | (ix.) | `h/akl ≠ 0,` | 式 | — | notes-015 | ✓ phase9c/Notes_ii.PossNecCauseUnder (def 本体), phase9c/def_ix | `and` / `, A is, relative to k, a possible necessary cause` | 第 4 条件。頁末「relative to k, a possible necessary cause of B under conditions l.」 |
| notes-020 | 277 | (ii.) 4 | 本文 | 行内 | — | notes-020 | `b/ahkl ≠ b/āhkl,` | 式 | — | — | ✓ phase9c/Notes_ii.DepForProb (def 本体), phase9c/dep_for_prob | `causa essendi and causa cognoscendi. If` / `where a and b may be any propositions` | 「確率上の依存」(causa cognoscendi) の定義。帰結は phase9c/def_viii_l_dep, phase9c/def_ix_dep。(x.) 因果的独立の定義 (277) は語のみ (phase9c/Notes_ii.CausallyIndependent, phase9c/def_x_src) |
| notes-021 | 277 | (ii.) 4 | 本文 | 行内 | — | — | `kl.` | 記法 | — | — | phase9c/Notes_ii.DepForProb (前提 R.conj k l), phase9c/dep_for_prob | `causa cognoscendi for b, relative to data` / `If a and b are causally dependent` | 「確率上の依存」の文末。名詞的資料 k と存在的資料 l の連言 (並置; ch18-001 `AB` と同じ基準で記法)。ピリオドは文末の句点 |
| notes-022 | 277 | (ii.) 4 | 本文 | 行内 | — | — | `kl.` | 記法 | — | notes-021 | phase9c/def_x_src (引数 k l) | `possible causa essendi, relative to data` / `But, after all, the essential` | 定義 (x.) を適用した文の文末。ピリオドは文末の句点 |

## 集計 (補則 1〜8 適用、第 3 回)
- 行数 22 (式 20、記法 2、参考 0)。
- 式行 20 (表示 0: なし; 行内 20: notes-001–020)。項目数 10 (項目 ID の異なり数: (i.)–(ix.) の 9 と notes-020)、うち番号付き (式行) 19: notes-001–019 / (項目) 9: (i.)–(ix.)。summary.csv の `うち番号付き` は式行の単位で 19。
- 記法 2 (表示 0: なし; 行内 2: notes-021–022)。
- ✓ 20: notes-001–020。≈ 0: なし。✎ 0: なし (Lean 対応 (式) 20)。未 (式) 0: なし。
- 記法の Lean 対応 2: notes-021–022。記法で未 0: なし。
- 参考行 0: なし (式にも記法にも Lean 対応にも数えない)。
- 判読不能 [?]: 0。
- 式・記法のない頁: 274, 275, 278 (白紙), 279 (中扉), 280 (白紙)。
- 所見候補: notes-014 (E-III-4、索引済み)、notes-013/016 の h の量化 (索引済み注記)。
