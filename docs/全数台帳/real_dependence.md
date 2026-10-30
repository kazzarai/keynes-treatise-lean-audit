# ℝ 依存の洗い出し (第II部、B32)

`tools/real_dependence.py` が `phases/keynes_part_ii_*.lean` の theorem・lemma・example を 1 本ずつ字面で分類し、公理の使用と同じファイル内の呼び出しを辿った値を別に出した結果。洗い出しのみで、証明の良し悪しは判定しない。分類は排他で、複数に当たるときは C > D > E > A′ > B > A。

- **A 順序のみ**: ≤ の推移・反対称・反射など、下のどの語にも当たらない
- **A′ 順序付き環 (比較可能性は不要)**: `mul_pos`・`mul_nonneg`・`sub_nonneg`・`sub_pos`・`add_pos`・`add_nonneg`・`sq_nonneg`・`pow_pos`・`abs_nonneg`・`mul_le_mul*`・`add_le_add*`・`div_pos`・`div_nonneg`・`div_le_*` など、名前全体で判定する「順序と環の演算」の補題 (`div_*` と `inv_pos` 系は D にも当たるので D になる)
- **B 加法・乗法**: `ring`・`mul_*`・`add_*`・`sub_*`・`sq_*`・`Finset.sum_*` (A′ の補題名に当たらないもの。線形順序は使わない)
- **C 線形順序**: `linarith`・`nlinarith`・`positivity`・`le_total`・`lt_or_le`・`le_or_lt`・`abs_*` (`abs_nonneg` を除く)・`max`/`min` など
- **D 体の構造**: `field_simp`・`div_*`・`inv_*`・`one_div`
- **E 数値**: `norm_num`・`Real.*`

class は宣言の字面に現れる語だけで決める。`class_trans` は、本文で使う同じファイルの別定理と公理まで辿った最強の分類 (公理は下の表で分類し、`def_IX*`・`def_X_*`・`def_XII`・`ax_iva_*`・`ax_ivc`・`ax_v`・`ax_vi` を B、`ax_ivb` を A′、`def_XI*`・`ax_mae*`・`ax_vii*` を D とする)。台帳の列は `class_trans` で付ける。

## ファイル別 (class)

| ファイル | 宣言数 | grep 本数 | 一致 | A | A′ | B | C | D | E |
|---|---|---|---|---|---|---|---|---|---|
| keynes_part_ii_phase10a | 36 | 36 | ○ | 8 | 3 | 9 | 11 | 2 | 3 |
| keynes_part_ii_phase10b | 122 | 122 | ○ | 57 | 1 | 16 | 36 | 10 | 2 |
| keynes_part_ii_phase10c | 182 | 182 | ○ | 55 | 5 | 20 | 68 | 24 | 10 |
| keynes_part_ii_phase10d | 119 | 119 | ○ | 16 | 1 | 14 | 62 | 13 | 13 |
| keynes_part_ii_phase10e | 59 | 59 | ○ | 10 | 0 | 5 | 29 | 7 | 8 |
| keynes_part_ii_phase10f | 44 | 44 | ○ | 20 | 0 | 7 | 13 | 3 | 1 |
| keynes_part_ii_phase10g | 19 | 19 | ○ | 11 | 0 | 1 | 6 | 1 | 0 |
| keynes_part_ii_phase10h | 77 | 77 | ○ | 24 | 0 | 5 | 34 | 9 | 5 |
| keynes_part_ii_phase12b_underdetermination | 38 | 38 | ○ | 23 | 2 | 1 | 3 | 5 | 4 |
| keynes_part_ii_phase2 | 7 | 7 | ○ | 2 | 0 | 0 | 5 | 0 | 0 |
| keynes_part_ii_phase3a | 8 | 8 | ○ | 2 | 0 | 0 | 6 | 0 | 0 |
| keynes_part_ii_phase3b | 7 | 7 | ○ | 1 | 0 | 1 | 2 | 3 | 0 |
| keynes_part_ii_phase3c | 7 | 7 | ○ | 4 | 0 | 2 | 0 | 1 | 0 |
| keynes_part_ii_phase3d | 4 | 4 | ○ | 2 | 0 | 1 | 0 | 1 | 0 |
| keynes_part_ii_phase4 | 13 | 13 | ○ | 1 | 0 | 0 | 8 | 1 | 3 |
| keynes_part_ii_phase5 | 25 | 25 | ○ | 5 | 1 | 2 | 15 | 0 | 2 |
| keynes_part_ii_phase6a | 28 | 28 | ○ | 7 | 0 | 2 | 17 | 1 | 1 |
| keynes_part_ii_phase6b | 46 | 46 | ○ | 6 | 0 | 3 | 31 | 4 | 2 |
| keynes_part_ii_phase6c | 12 | 12 | ○ | 5 | 0 | 1 | 6 | 0 | 0 |
| keynes_part_ii_phase6c_inconsistency | 6 | 6 | ○ | 3 | 0 | 0 | 3 | 0 | 0 |
| keynes_part_ii_phase6c_model | 28 | 28 | ○ | 20 | 0 | 0 | 1 | 5 | 2 |
| keynes_part_ii_phase6c_necessity | 48 | 48 | ○ | 34 | 0 | 1 | 6 | 4 | 3 |
| keynes_part_ii_phase6c_skeleton | 3 | 3 | ○ | 3 | 0 | 0 | 0 | 0 | 0 |
| keynes_part_ii_phase7a | 3 | 3 | ○ | 0 | 0 | 0 | 3 | 0 | 0 |
| keynes_part_ii_phase7b | 8 | 8 | ○ | 1 | 0 | 1 | 6 | 0 | 0 |
| keynes_part_ii_phase7c | 12 | 12 | ○ | 2 | 0 | 0 | 8 | 2 | 0 |
| keynes_part_ii_phase7d | 7 | 7 | ○ | 0 | 0 | 0 | 1 | 1 | 5 |
| keynes_part_ii_phase7e | 4 | 4 | ○ | 3 | 0 | 1 | 0 | 0 | 0 |
| keynes_part_ii_phase7g | 23 | 23 | ○ | 6 | 0 | 2 | 12 | 2 | 1 |
| keynes_part_ii_phase7h | 24 | 24 | ○ | 4 | 0 | 8 | 11 | 0 | 1 |
| keynes_part_ii_phase7i | 48 | 48 | ○ | 6 | 0 | 5 | 19 | 5 | 13 |
| keynes_part_ii_phase7i_model | 37 | 37 | ○ | 25 | 1 | 6 | 1 | 1 | 3 |
| keynes_part_ii_phase8a | 20 | 20 | ○ | 3 | 0 | 4 | 9 | 1 | 3 |
| keynes_part_ii_phase8b | 33 | 33 | ○ | 6 | 0 | 1 | 20 | 3 | 3 |
| keynes_part_ii_phase8c | 9 | 9 | ○ | 1 | 0 | 0 | 5 | 2 | 1 |
| keynes_part_ii_phase8d | 10 | 10 | ○ | 3 | 0 | 0 | 1 | 0 | 6 |
| keynes_part_ii_phase9x | 80 | 80 | ○ | 6 | 0 | 6 | 35 | 17 | 16 |
| keynes_part_ii_pilot | 2 | 2 | ○ | 0 | 0 | 0 | 2 | 0 | 0 |
| **第II部合計** | **1258** | **1258** | ○ | **385** | **14** | **125** | **495** | **128** | **111** |

(grep 本数 = 各ファイルの `grep -c '^theorem\|^lemma\|^example'`)

## 直接 (class) と辿った値 (class_trans) の本数

| | A | A′ | B | C | D | E | 計 |
|---|---|---|---|---|---|---|---|
| 直接 (class) | 385 | 14 | 125 | 495 | 128 | 111 | 1258 |
| 呼び先と公理の使用まで (class_trans) | 170 | 15 | 130 | 705 | 146 | 92 | 1258 |

✎ 行は反例 (数値模型) の E を含むため強めに出る。

原則: 迷ったら強い側 (上位のクラス) に置く。少なめに分類して見落とす方が危険だから (人の裁定、2026-10-30)。迷った語は下の「振り分け表」に挙げる。

## 公理の分類 (使うと呼び側の class_trans が上がる)

| 公理名 (規則) | クラス | 根拠の演算 |
|---|---|---|
| `def_IX(_i)?` | B | 和 (ab/h + ab̄/h = a/h) |
| `def_X_(left / right)(_i)?` | B | 積 (ab/h = a/bh · b/h) |
| `def_XII` | B | 和と差 (P + Q = R ならば P = R − Q) |
| `ax_iva_(mul / add)` | B | 和・積の交換律 |
| `ax_ivb` | A′ | 順序付き環 (0 < Q ならば P < P + Q。裁定 F32.7: B ではなく A′) |
| `ax_ivc` | B | 和の簡約 |
| `ax_v` | B | 和の結合・交換 |
| `ax_vi` | B | 積の分配律 |
| `def_XI(_i)?` | D | 除算 (PQ = R ならば P = R/Q、Q ≠ 0) |
| `ax_mae(_prop)? / ax_vii(_i)?` | D | p/n の値 (自然数の除算を含む存在。裁定 F32.8: D のまま) |
| `ax_ii / ax_iii_\w+ / def_VIII_i(_src)?` | A | 値の等式 (= 1 の前件・後件の移し替え) |
| `cons_of_pos(_src)? / cons_iff_taut / cons_true` | A | 値 ≠ 0 と Cons の関係 |
| `ax_range_(lo / hi)(_i)?` | A | 値域 0 ≤ P ≤ 1 (順序のみ) |
| `ax_vi_(mono / compl / equiv) / th_12_i` | A | 等式・単調性 (加法・乗法は使わない) |

`ax_mae`・`ax_mae_prop`・`ax_vii`・`ax_vii_i` は D のまま (自然数 n での除算 p/n を含む存在の主張なので、B にはしない。裁定 F32.8)。`ax_ivb` は 0 < Q ならば P < P + Q で、加法と順序の両方を使うので B ではなく A′ (裁定 F32.7)。

原始概念 (`Pr`・`PrI`・`Cons`・`IProp`・`iand` など) と命題論理の `ktaut_*` は ℝ の演算を使わないので分類しない。

## 台帳 ch12 の公理の行

Lean 欄が公理を指す行 (定理も併記する行は、定理を含めた最強値が行のクラス)。

| 行ID | 項目ID | 公理名 | 公理のクラス | 行のクラス | 根拠の演算 |
|---|---|---|---|---|---|
| ch12-010 | Def. VI | `cons_of_pos_src` | A | A | 値 ≠ 0 と Cons の関係 |
| ch12-012 | Def. VIII | `def_VIII_i_src` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-013 | Def. VIII | `def_VIII_i_src` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-014 | Def. VIII | `def_VIII_i_src` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-016 | Ax. (ii.) | `ax_ii` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-017 | Ax. (ii.) | `ax_ii` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-018 | Ax. (iii.) | `ax_iii_taut` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-019 | Ax. (iii.) | `ax_iii_taut` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-020 | Ax. (iii.) | `ax_iii_taut` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-021 | Ax. (iii.) | `ax_iii_taut` | A | A | 値の等式 (= 1 の前件・後件の移し替え) |
| ch12-026 | Def. IX | `def_IX`・`def_IX_i` | B・B | B | 和 (ab/h + ab̄/h = a/h) |
| ch12-027 | Def. X | `def_X_left`・`def_X_left_i`・`def_X_right`・`def_X_right_i` | B・B・B・B | B | 積 (ab/h = a/bh · b/h) |
| ch12-028 | Def. XI | `def_XI`・`def_XI_i` | D・D | D | 除算 (PQ = R ならば P = R/Q、Q ≠ 0) |
| ch12-029 | Def. XI | `def_XI`・`def_XI_i` | D・D | D | 除算 (PQ = R ならば P = R/Q、Q ≠ 0) |
| ch12-030 | Def. XII | `def_XII` | B | B | 和と差 (P + Q = R ならば P = R − Q) |
| ch12-031 | Def. XII | `def_XII` | B | B | 和と差 (P + Q = R ならば P = R − Q) |
| ch12-034 | Ax. (iv. a) | `ax_iva_mul` | B | B | 和・積の交換律 |
| ch12-036 | Ax. (iv. a) | `ax_iva_add` | B | B | 和・積の交換律 |
| ch12-040 | Ax. (iv. b) | `ax_ivb` | A′ | C | 順序付き環 (0 < Q ならば P < P + Q。裁定 F32.7: B ではなく A′) |
| ch12-064 | Ax. (vi.) | `ax_vi` | B | B | 積の分配律 |

## 章別 (台帳 ch12–ch17 の行ごとの「ℝ 依存」)

行の値は、Lean 欄が指す定理・公理の class_trans のうち最強の分類。「—」は定義のみ・境界の記録・数えない行 (参考・裸記号)・記法のみ。

| 章 | 行数 | A | A′ | B | C | D | E | — |
|---|---|---|---|---|---|---|---|---|
| ch12 | 74 | 15 | 2 | 17 | 10 | 6 | 0 | 24 |
| ch13 | 170 | 10 | 2 | 21 | 121 | 15 | 0 | 1 |
| ch14 | 231 | 6 | 1 | 23 | 124 | 28 | 2 | 47 |
| ch15 | 68 | 2 | 0 | 2 | 45 | 17 | 2 | 0 |
| ch16 | 134 | 10 | 0 | 16 | 43 | 10 | 0 | 55 |
| ch17 | 230 | 6 | 0 | 11 | 119 | 42 | 19 | 33 |
| **合計** | **907** | **49** | **5** | **90** | **462** | **118** | **23** | **160** |

✎ 行は反例 (数値模型) の E を含むため強めに出る。

## 「—」の行

- **定義のみ・記法のみ (Lean 欄が def・原始概念・記号を指し、定理・公理を指さない)** (15): ch12-001, 002, 003, 024, 025, 072, 074, ch14-079, 094, 130, 136, ch16-001, ch17-110, 167, 221
- **数えない行 (裸記号)** (15): ch12-004, 015, ch13-121, ch16-017, 068, 069, 134, ch17-001, 038, 075, 099, 101, 211, 219, 225
- **未対応 (定義のみ・境界の記録・Lean に無い)** (124): ch12-005, 006, 007, 011, 032, 033, 035, 052, 055, 056, 058, 059, 063, 065, 068, ch14-007, 008, 024, 026, 034, 097, 117, 118, 119, 124, 125, 128, 159, 161, 163, 164, 166, 169, 172, 175, 185, 189, 192, 194, 200, 201, 202, 204, 206, 216, 217, 218, 219, 220, 221, 226, 229, ch16-003, 004, 005, 006, 007, 008, 009, 010, 015, 016, 019, 038, 039, 040, 041, 042, 043, 044, 046, 047, 048, 049, 056, 058, 061, 062, 076, 077, 078, 079, 080, 081, 082, 083, 084, 085, 086, 087, 088, 089, 090, 095, 102, 103, 118, 123, 130, 131, 132, 133, ch17-003, 006, 007, 008, 009, 011, 012, 020, 054, 060, 077, 091, 094, 114, 135, 152, 154, 155, 170, 171, 178, 201
- **数えない行 (参考)** (6): ch14-087, 089, 090, 092, 135, 191

## Π への移植の見積り

Π への移植で比較可能性を作り直す要作業は、C 705 本 (class_trans、呼び先と公理まで辿った値) を上限とする。下の「比較可能性を直接使う定理」は、`le_total`・`lt_trichotomy`・`le_or_lt`・`le_or_gt` と、同じ働きの `lt_or_le`・`lt_or_ge`・`lt_or_gt_of_ne` を本文で直接使う定理で、比較可能性が本質的に要る箇所の下限の参考値である (`linarith` 等は比較可能性を暗に使うだけで数えない。`lt_or_eq_of_le`・`eq_or_lt_of_le` は半順序でも成り立つので数えない)。

### 比較可能性を直接使う定理 (6 本)

| ファイル | 定理 | 行 (最初の使用) | 使う語 |
|---|---|---|---|
| keynes_part_ii_phase10d | `hasDerivAt_abs_sub` | 1260 | `lt_or_gt_of_ne` |
| keynes_part_ii_phase10d | `i6_sign` | 1337 | `le_or_gt` |
| keynes_part_ii_phase9x | `th_17_1911_i_6_sign` | 555 | `le_or_gt` |
| keynes_part_ii_phase9x | `th_17_1911_iv_2_src` | 1074 | `le_total` |
| keynes_part_ii_phase9x | `th_17_1911_iv_3_src` | 1091 | `lt_or_gt_of_ne` |
| keynes_part_ii_phase9x | `th_17_1911_12_src` | 1122 | `lt_or_gt_of_ne` |

## 振り分け表 (迷った語は上位に置く)

語の振り分けで A か A′ か、B か D か迷うときは上位のクラスに置いた (裁定 2026-10-30)。旧版で語に当たらず A になっていたものは、迷う語として挙げて上げた。整域の性質 (`mul_eq_zero`・`mul_ne_zero`・`eq_zero_or_eq_zero_of_mul_eq_zero` など零因子が無いこと) は D 扱い (強い側、裁定 F32.14)。

| 語 (正規表現) | 迷った候補 | 置いたクラス | 理由 | 使う定理の本数 (class の字面) |
|---|---|---|---|---|
| `Finset\.sum_le_sum\w*` | B/A′ | A′ | 和と順序の両方 (単調性) | 2 |
| `Finset\.sum_nonneg / Finset\.sum_pos / Finset\.sum_eq_zero_iff_of_nonneg` | B/A′ | A′ | 和と順序の両方 (非負・正) | 4 |
| `mul_eq_zero / mul_ne_zero / pow_ne_zero / pow_eq_zero_iff / eq_zero_or_eq_zero_of_mul_eq_zero` | B/D | D | 零因子が無いこと (整域の性質)。環では成り立たない | 71 |
| `mul_left_cancel₀ / mul_right_cancel₀` | B/D | D | 0 でない元での簡約 (逆元か整域が要る) | 18 |
| `eq_div_iff / eq_div_of_mul_eq / div_eq_iff` | A/D | D | 除算を含む (旧版は語に当たらず A になっていた) | 27 |
| `sq_abs` | B/C | C | 絶対値を含む | 11 |
| `exact_mod_cast / norm_cast / push_cast` | A/E | E | ℕ → ℝ の型変換 (旧版は語に当たらず A になっていた) | 39 |
| `one_mul / zero_add / zero_mul / eq_sub_of_add_eq / linear_combination` | A/B | B | 加法・乗法 (旧版は語に当たらず A になっていた) | 105 |

## 括弧の中の定理名から拾った台帳の行

台帳の Lean 欄は括弧の中の定理名も拾う (括弧を消さない、裁定 F32.11)。括弧の外だけで拾った旧版と比べて、拾う参照が増えた行を挙げる (値が変わった行は → で示す)。Lean 欄が「未」でも括弧内に定理名があれば拾って値を付ける (強い側に倒す裁定、2026-10-30。例: ch14-156・ch17-134)。

12 行。

| 行ID | 項目ID | 括弧の中から拾った定理・公理 | 旧版の値 → 新しい値 |
|---|---|---|---|
| ch14-018 | (24.6) | `Keynes.th_14_24_6_src` (phase7g, C) | C → C |
| ch14-048 | (28) | `Keynes.th_14_28` (phase6b, C) | C → C |
| ch14-091 | (34) | `KeynesI.th_14_r091_rhs_one` (phase10c, D)・`KeynesI.th_14_r091_printed_iff` (phase10c, D) | C → C |
| ch14-129 | Def. XV | `Keynes.th_14_41_b` (phase3b, D) | — → D |
| ch14-147 | (43) | `Keynes.th_14_43` (phase3c, B) | D → D |
| ch14-156 | (44.1) | `Keynes.th_14_44_1` (phase3b, C) | — → C |
| ch14-162 | (46) | `KeynesI.th_14_r162_printed_iff` (phase10c, C) | C → C |
| ch15-012 | Ax. (vii.) | `ax_mae` (phase4, D)・`ax_vii` (phase7g, D) | D → D |
| ch15-016 | (50) | `KeynesI.th_15_50_exists` (phase10e, D) | D → D |
| ch15-020 | (50) | `KeynesI.th_15_50_exists` (phase10e, D) | D → D |
| ch15-057 | (55) | `Keynes.th_15_55_worked` (phase7g, C) | C → C |
| ch17-134 | (i.) | `KeynesLawOfError.th_17_1911_i_6_integrate` (phase9x, C) | B → C |

## クラス C の定理 (Π への移植で比較可能性が要る箇所)

495 本 (class が C のもの)。ファイル別に定理名を並べる。

- **keynes_part_ii_phase10a** (11): `th_13_1_i`・`taut_neg_zero`・`conj_neg_cert_zero`・`th_12_i_short`・`th_12_iii_last`・`th_12_ivb_mul_lt`・`th_12_ivb_add_gt`・`nec_12_6_unbracketed`・`nec_12_6_rebracketed`・`th_12_6_sum_exists`・`th_12_7_sub`
- **keynes_part_ii_phase10b** (36): `th_13_1_i`・`taut_neg_zero`・`conj_neg_cert_zero`・`eq_of_cert_iff`・`conj_le_left_i`・`le_of_taut`・`prem_drop_cert`・`self_cert`・`conj_cert`・`th_13_1_r002`・`th_13_1_r005`・`th_13_1_1`・`th_13_1_1_r010`・`th_13_1_1_r011`・`th_13_1_2`・`th_13_1_3`・`th_13_1_3_r017`・`th_13_1_3_r018`・`th_13_1_4`・`th_13_5_r027`・`th_13_5_r029`・`th_13_5_r031`・`th_13_5_r032`・`th_13_6_r039`・`th_13_7_r043`・`th_13_7_r046`・`th_13_7_r047`・`th_13_9_r059`・`th_13_12_r078`・`th_13_13_r089`・`th_13_15_r106`・`th_13_16_2_r124`・`th_13_r129`・`th_13_20_r145`・`th_13_21_r157`・`th_13_23_r170`
- **keynes_part_ii_phase10c** (68): `th_13_1_i`・`taut_neg_zero`・`conj_neg_cert_zero`・`th_12_i_short`・`th_24_i`・`pr_not`・`conj_le_left`・`th_8_i`・`th_9_i`・`zero_of_disj_zero`・`disj_zero`・`th_14_r002`・`th_14_r003`・`th_14_r004`・`th_14_r005`・`falsum_zero`・`conj_disjL_zero`・`th_25_i`・`th_14_r038`・`th_14_r042`・`th_14_r043`・`th_14_r049`・`th_14_r050`・`th_14_r055`・`th_29_i`・`not_conj_zero_of_cert`・`th_14_r060`・`th_14_r064`・`th_14_r067`・`th_14_r070`・`th_14_r073`・`th_14_r085`・`th_14_r091_cor`・`th_14_r114`・`pr_split`・`th_14_r131`・`coef2_joint`・`coef3_joint`・`coef4_joint`・`prodL_le_one`・`prodL_gt_one`・`prodL_lt_one`・`coefL_joint`・`cum_point`・`th_14_r160`・`th_14_r162_cor`・`th_14_r175`・`th_14_r178_cor`・`th_14_r186`・`th_14_r190`・`joint_ge_prod`・`th_14_r197`・`prod_d_xh`・`th_14_r199_cor`・`th_14_r203`・`th_14_r205`・`th_14_r207`・`th_14_r208`・`cheb_ge_one`・`th_14_r213`・`th_14_r222`・`th_14_r225`・`th_14_r228`・`th_14_r230`・`th_14_r231`・`simplified_46_fails`・`printed_46_2_prop_false`・`printed_46_line2_false`
- **keynes_part_ii_phase10d** (62): `th_13_1_i`・`taut_neg_zero`・`conj_neg_cert_zero`・`th_12_i_short`・`th_24_i`・`th_17_56_raw_i`・`th_17_56_l004`・`th_17_56_l005`・`th_17_56_l017`・`th_17_56_l018`・`th_17_56_l025`・`th_17_56_l036`・`th_17_57_l039`・`th_17_57_l040`・`th_17_57_l041`・`th_17_57_l042`・`th_17_57_l043`・`th_17_57_l046`・`th_17_57_l047`・`th_17_57_l051`・`term57_i`・`one_sub_prod_le_sum`・`nterm_bounds`・`th_17_57_l067`・`term57_4_i`・`th_17_57_l069`・`th_17_57_l072`・`th_17_58_l079`・`closed58`・`th_17_58_l080`・`th_17_58_l083`・`th_17_58_l084`・`th_17_58_l093`・`th_17_58_l095`・`th_17_58_l098`・`hasDerivAt_abs_sub`・`i6_deriv`・`i6_integrate`・`i6_sign`・`th_17_N1_l114`・`th_17_i_l122`・`th_17_i_l132`・`th_17_ii_l141`・`th_17_ii_l147`・`ii9_identify`・`th_17_ii_l161_printed_fails`・`th_17_iii_l164`・`th_17_iv_l170`・`th_17_iv_l173`・`th_17_iv_l174`・`th_17_iv_l178`・`th_17_vi_l187`・`th_17_vi_l188`・`th_17_vi_l192`・`th_17_3_l201`・`th_17_N3_l215`・`th_17_N4_l216_printed_fails`・`th_17_N4_l216`・`th_17_N4_l217_printed_fails`・`th_17_N4_l217`・`th_17_N5_l222`・`th_17_N5_l223`
- **keynes_part_ii_phase10e** (29): `th_13_1_i`・`taut_neg_zero`・`conj_neg_cert_zero`・`eq_of_cert_iff`・`conj_le_left_i`・`th_24_i`・`conj_lower_i`・`th_15_r011`・`th_15_r027`・`th_15_51_r033`・`th_15_51_r036`・`th_15_51_r037`・`th_15_r038`・`th_15_r039`・`th_15_r040`・`th_15_52_r043`・`th_15_53_r046`・`th_15_53_r047`・`th_15_53_r048`・`th_15_55_r057`・`th_15_55_r058`・`th_15_55_r059`・`th_15_55_r060`・`th_15_55_r061`・`th_15_55_r062`・`th_15_55_r063`・`th_15_55_r064`・`th_15_55_r065`・`th_15_55_r066`
- **keynes_part_ii_phase10f** (13): `th_13_1_i`・`taut_neg_zero`・`conj_neg_cert_zero`・`conj_certain`・`th_11_001`・`th_11_004`・`th_11_008`・`th_11_010`・`th_11_019`・`group_cond_ii_form`・`th_11_027`・`th_11_030`・`th_11_031`
- **keynes_part_ii_phase10g** (6): `th_13_1_i`・`conj_neg_cert_zero`・`th_10_II_conj`・`th_10_III_compl`・`th_10_VII_not`・`th_10_48_equal`
- **keynes_part_ii_phase10h** (34): `th_13_1_i`・`taut_neg_zero`・`conj_neg_cert_zero`・`eq_of_cert_iff`・`conj_le_left_i`・`th_24_i`・`follows_both`・`zero_transfer`・`conj_subst_mutual`・`half_of_indiff`・`th_16_r003_premissless_fails`・`th_16_r013`・`th_16_r021`・`th_16_r022`・`th_16_r023`・`th_16_r031`・`th_16_r032_nearer`・`th_16_r046`・`th_16_r056_iff`・`th_16_r056_le`・`th_16_r056_fails`・`th_16_r059`・`th_16_r075`・`th_16_r084`・`th_16_r111`・`testimony_den`・`th_16_r111_printed_iff`・`th_16_r113`・`th_16_r116`・`th_16_r117`・`th_16_r121`・`th_16_r125`・`th_16_r126`・`th_16_r129`
- **keynes_part_ii_phase12b_underdetermination** (3): `prw_eq_one_iff`・`not_determined`・`every_interior_value`
- **keynes_part_ii_phase2** (5): `th_24`・`th_24_1`・`th_13_1`・`th_13_19`・`th_13_20`
- **keynes_part_ii_phase3a** (6): `th_24`・`th_24_1`・`th_13_1`・`th_13_19`・`th_13_20`・`th_14_24_2`
- **keynes_part_ii_phase3b** (2): `th_24`・`th_14_44_1`
- **keynes_part_ii_phase4** (8): `th_13_1`・`th_24`・`pr_false`・`th_15_51`・`th_15_52`・`th_15_53`・`th_15_54`・`th_15_55`
- **keynes_part_ii_phase5** (15): `th_24`・`pr_false`・`pr_conj_le_left`・`pr_conj_le_right`・`th_14_49`・`th_17_56_raw`・`th_17_56`・`th_17_56_1`・`th_17_56_2`・`th_17_56_4`・`th_17_56_5`・`incl_excl`・`pr_le_bigOr`・`th_17_58_2`・`th_17_58_3`
- **keynes_part_ii_phase6a** (17): `th_13_1`・`th_24`・`pr_false`・`pr_conj_le_left`・`pr_conj_le_right`・`incl_excl`・`pr_conj_bigOr_le`・`overlapSum_nonneg`・`overlapSum_map_and_zero_of_excl`・`overlapSum_map_le_pairProdSum`・`prodComplement_eq`・`th_14_25`・`th_14_49_1`・`th_17_57_1`・`th_17_57_3`・`th_17_57_4`・`th_17_57_5`
- **keynes_part_ii_phase6b** (31): `th_13_1`・`th_24`・`pr_false`・`pr_conj_le_left`・`pr_conj_le_right`・`th_13_5`・`th_13_7`・`th_13_8_conj`・`th_13_9`・`th_13_10`・`th_13_12`・`th_13_13`・`th_13_13_1`・`th_13_13_2`・`th_13_18`・`th_13_22`・`th_13_23`・`incl_excl`・`pr_conj_bigOr_le`・`overlapSum_zero_of_excl`・`th_14_24_3`・`th_14_24_4`・`th_14_24_6`・`th_14_24_7`・`th_14_26_1`・`th_14_27`・`th_14_27_1`・`th_14_28`・`th_14_28_1`・`th_14_31`・`th_14_32`
- **keynes_part_ii_phase6c** (6): `th_13_1_i`・`taut_neg_zero`・`conj_neg_cert_zero`・`th_12_i`・`th_12_i_short`・`th_24_i`
- **keynes_part_ii_phase6c_inconsistency** (3): `th_12_i`・`th_13_1_i`・`th_6c_old_inconsistent`
- **keynes_part_ii_phase6c_model** (1): `model_ax_range_lo_i`
- **keynes_part_ii_phase6c_necessity** (6): `compl₀`・`taut_neg_zero₀`・`conj_neg_cert_zero₀`・`th_12₀`・`two_valued_of_absorbing`・`model_ax_range_lo_i`
- **keynes_part_ii_phase7a** (3): `th_13_1`・`th_13_16_1`・`th_13_16_3`
- **keynes_part_ii_phase7b** (6): `th_13_1`・`th_14_30`・`th_14_33`・`th_14_33_1`・`th_14_35`・`th_14_40`
- **keynes_part_ii_phase7c** (8): `th_13_1`・`pr_conj_le_right`・`th_13_8_conj`・`th_13_9`・`th_13_12`・`th_13_16_3`・`th_13_16`・`th_13_16_2`
- **keynes_part_ii_phase7d** (1): `th_14_34`
- **keynes_part_ii_phase7g** (12): `th_13_1`・`pr_false`・`th_24`・`pr_conj_le_right`・`pr_or_ge`・`th_14_24_4_src`・`th_14_25_1_src`・`th_14_26_src`・`th_14_28_src`・`th_14_28_1_src`・`th_14_40_1_src`・`th_15_55_worked`
- **keynes_part_ii_phase7h** (11): `th_13_1`・`pr_false`・`th_14_49_step_src`・`th_14_49_1_src`・`th_17_57_step`・`th_17_57_ii_n2`・`q_value`・`th_17_58_closed`・`th_17_58_2_core`・`th_17_58_2_src`・`th_17_58_3_src`
- **keynes_part_ii_phase7i** (19): `list_sum_le`・`list_sum_nonneg'`・`list_sum_expand`・`th_13_1`・`pr_false`・`th_24`・`pr_conj_le_left`・`pr_conj_le_right`・`th_13_7`・`th_13_10_src`・`th_14_49_1_cor2`・`th_17_56_raw`・`th_17_56_4_src`・`th_17_57_step`・`th_17_57_1_term`・`booleDecomp_le`・`th_17_57_2_src`・`keynes57_1_ge`・`th_15_53_strict_fails`
- **keynes_part_ii_phase7i_model** (1): `ext_forced`
- **keynes_part_ii_phase8a** (9): `den_pos`・`div_lt_div_of_cross`・`c_nonneg`・`c_le_one`・`keynes_F1`・`c_pos`・`keynes_F2`・`keynes_F3`・`c_superadd`
- **keynes_part_ii_phase8b** (20): `H_pos`・`D_pos`・`W_lt_one`・`log_two_gt_half`・`underweight_at_half`・`subadd_fails_at_half`・`mul_log_lower`・`mul_log_upper`・`D_mono`・`subadd_small_prob`・`subadd_up_to_073`・`subcert_at_half`・`log_hundred_lt`・`H_hundredth_lt`・`supercert_at_edge`・`overweight_at_edge`・`log_500_le`・`H_0998_ub`・`H_0499_lb`・`subadd_fails_interior`
- **keynes_part_ii_phase8c** (5): `V_nonneg`・`V_le_one`・`subjective_time_mono`・`ignorance_decreases_weight`・`intersubjective_general`
- **keynes_part_ii_phase8d** (1): `th_vi_1_brady_holds`
- **keynes_part_ii_phase9x** (35): `th_17_1911_i_1_src`・`th_17_1911_i_2_src`・`th_17_1911_i_5_law`・`th_17_1911_i_6_src`・`th_17_1911_i_6_integrate`・`th_17_1911_i_6_sign`・`th_17_1911_ii_1_src`・`th_17_1911_ii_3_impossible`・`th_17_1911_ii_9_src`・`th_17_1911_ii_9_printed_fails`・`th_17_1911_iii_1_src`・`th_17_1911_11_src`・`median_aux_right`・`th_17_1911_iv_2_src`・`th_17_1911_iv_3_src`・`th_17_1911_12_src`・`th_17_1911_iv_5_src`・`th_17_1911_iv_6_corrected`・`th_17_1911_v_2_src`・`th_17_1911_v_3_src`・`th_17_1911_vi_2_src`・`th_17_1911_vi_4_law`・`th_17_1911_vi_4_exceeds_one`・`th_17_1911_3_src`・`th_17_1911_3_abs`・`logLik_median_eq`・`th_17_1911_4_src`・`th_17_1911_9_leads_gmean`・`th_17_1911_6_src`・`th_17_1911_counterexample`・`deriv_even_is_odd`・`deriv_odd_is_even`・`th_17_1921_N3_src`・`th_17_1921_N4_order`・`th_17_1921_N7_src`
- **keynes_part_ii_pilot** (2): `th_24`・`th_24_1`

