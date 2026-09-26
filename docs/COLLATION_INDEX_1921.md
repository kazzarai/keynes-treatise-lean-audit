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

## 撤回

- (33): Phase 7d ヘッダの「原典散文が証明と逆向き」は Gutenberg 転記誤り ("not more")。1921年版は "not less favourable" で命題文と証明が整合。正誤表から外す。

## Gutenberg tex の転記崩れ (台帳範囲、Lean は画像準拠)

(5) 番号欠落 / (15) h₁h₂/h・by II. / (16) 内側バー / (18) a/a=1 / (21) a/h₂ / (24.5) 指数 (−1)^{n−1} / (27) by (v.) / (29) h₂側の追加 / (33) not more→not less / (42.1) 波括弧 / (49) x̄/h / (49.1) −1 の位置 / (51) x/ȳh / (55) μ⩽ / (56.1) 4箇所 / (57) 二重バー・余分な /

## 8a/8d のアンカー (台帳外)

phase8a: 第26章§7 の係数・恒等式・脚注 F1〜F4 は folio **315** の印刷と一致 (Lean コメントの folio 314 は誤記)。F4 の印刷仮定 w=w′, q>q′ を画像で確定、印刷の「比較不能」は脚注内で自己矛盾 (keynes_F4_printed_determinate)。
phase8d: 第6章の文言・数値アンカー (§1 核文、§3 補元対称、§4 三択連鎖、§6 分数、§8 和/差) は folio 71–79 の印刷と一致。