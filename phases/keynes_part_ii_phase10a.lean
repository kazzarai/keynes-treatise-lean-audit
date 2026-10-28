/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 10a
#
# 第 XII 章「推論と確率の定義と公理」(1921 年 Macmillan 初版 folio 133–138)
# 全数台帳 docs/全数台帳/ch12.md の式行のうち Lean 欄が「未」だった行を、
# 行ごとに定理文として書く (B28a)。
#
# ## 基準
#   1921 年初版の頁画像のみ。定理名は th_12_<項目>_<枝>。台帳の行 ID (ch12-NNN)
#   は各定理の docstring に書く。
#
# ## キャリア
#   phase6c の内包キャリア (IProp, PrI, Cons; 公理 (i) の但し書き付き) をそのまま
#   写す。`Prop → Prop → ℝ` 型の確率関係は置かない (CLAUDE.md 不変条件 3)。
#   公理 (iv.)–(vi.) の P, Q, R, S, T は「確率関係」(folio 136: 「If P, Q, R are
#   relations of probability」) なので、PrI の値 PrI p h 等として書く。Def. I
#   (folio 134: 「a/h = P」) の名前付けがそのまま PrI p h = P にあたる。
#
# ## 収録 (台帳の行 ID)
#   A. 公理 (iii.) の末尾 (folio 135): 「If a/h = 1, ah≡h.」      ch12-022, 023
#   B. 公理 (iv. b) (folio 136): 「PQ<P unless Q=1 or P=0; P+Q>P unless Q=0.
#      PQ=P if Q=1 or P=0; P+Q=P if Q=0.」          ch12-037–039, 041–046
#      公理 (iv. c) (folio 136): 「If PQ⋛PR, then Q⋛R unless P=0. If P+Q⋛P+R,
#      then Q⋛R and conversely.」                     ch12-047–051
#      ⋛ は <, =, > の 3 通りを重ねた活字なので、3 本の定理に分ける。
#      「unless …」は場合分けの前提 (… でないならば) として書き、別に
#      「… または …」の選言形も置く。
#   C. 公理 (v.) (folio 137): 符号付きの和の組み替え            ch12-061, 062
#      公理 (vi.) (folio 137): P(R±S) = PR±PS                    ch12-064
#      ± は文字ごとに一つの符号 (同じ文字の ± はどの括弧でも同じ、∓ はその逆)
#      と読み、符号を Bool で受ける (sgn true = 1, sgn false = −1)。
#   D. §6 末尾 (folio 137) の結合の例                ch12-053, 054, 057, 060
#      §7 (folio 137) の派生命題の例                  ch12-066, 067, 069
#   E. Def. XIV (folio 138): 「If a₁/a₂h = a₁/h, a₂ is irrelevant … to a₁/h.」
#                                                     ch12-073
#   Def. I・II・III・VII (folio 134) は名付けだけの行 (定義のみ) なので定理を置かない
#   (台帳は式行のまま 未)。
#
# ## 公理の使い方 (必要性)
#   B の不等式の行は値域の公理 ax_range_lo_i / ax_range_hi_i を要する。値域の
#   公理を外した実数の上では印刷形が成り立たないことを、反例 nec_12_* として
#   置く (B の各定理の必要性)。A は ax_iii_taut・def_IX_i・def_X_left_i・
#   def_X_right_i・cons_of_pos を通る。C・D は実数の環の演算だけで閉じ、公理群を
#   使わない (#print axioms に KeynesXII の公理が現れない)。
#
# ## 形式化の境界 (散文の条件で、公理化しないもの)
#   - 公理 (iv.)–(vi.) と §6–§7 の「和・積が存在する場合に」(folio 136–137) は、
#     PrI の値が実数で和・積が常に定まるため前提にならない。
#   - folio 137 の「it does not follow that P + S + T = R」「we cannot infer from
#     the foregoing axioms that (P + S) + T = R」(ch12-055, 058): Keynes の代数は
#     和の結合律を仮定しないので従わない。ℝ 担体では従う —— 担体の強さの差
#     (所見候補 F12.1)。ℝ 担体での帰結を nec_12_6_unbracketed・
#     nec_12_6_rebracketed に記録し、台帳の行には対応づけない (Lean 欄は 未)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase10a.lean
-/

import Mathlib

namespace KeynesXII

/-! ## 内包的キャリアと結合子 (phase6c と同一) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 `Cons h`: 「h は矛盾する連言でない」(folio 135、公理 (i))。 -/
axiom Cons : IProp → Prop

/-! ## Keynes 操作公理群 (内包版、phase6c と同一) -/

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- Def. VIII 双条件読み、但し書き付き (phase6c と同一)。 -/
axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- Def. VIII 印刷どおり (→ のみ、phase6c と同一)。 -/
axiom def_VIII_i_src (a b h : IProp) :
    PrI b (iand a h) = 1 → PrI a (iand b h) = 1 → PrI (iiff a b) h = 1

/-! ## 深い埋め込み: 構文・評価・トートロジー (phase6c と同一) -/

inductive Form : Type where
  | var  : ℕ → Form
  | tru  : Form
  | fls  : Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | neg  : Form → Form
  | iffF : Form → Form → Form

def evalB (v : ℕ → Bool) : Form → Bool
  | .var n    => v n
  | .tru      => true
  | .fls      => false
  | .conj f g => evalB v f && evalB v g
  | .disj f g => evalB v f || evalB v g
  | .neg f    => !(evalB v f)
  | .iffF f g => evalB v f == evalB v g

/-- 論証的トートロジー: すべての真理値割当で真。 -/
def Taut (f : Form) : Prop := ∀ v : ℕ → Bool, evalB v f = true

noncomputable def interp (env : ℕ → IProp) : Form → IProp
  | .var n    => env n
  | .tru      => itrue
  | .fls      => inot itrue
  | .conj f g => iand (interp env f) (interp env g)
  | .disj f g => ior (interp env f) (interp env g)
  | .neg f    => inot (interp env f)
  | .iffF f g => iiff (interp env f) (interp env g)

/-- Ax.(iii) 本体、但し書き付き (phase6c と同一)。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

/-! ## 整合性の公理 (phase6c と同一; 本ファイルの定理が使うのは cons_of_pos のみ) -/

axiom cons_true : Cons itrue
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## 移植定理 (phase6c と同一の証明) -/

theorem itrue_certain (h : IProp) (hc : Cons h) : PrI itrue h = 1 :=
  ax_iii_taut Form.tru (fun _ => itrue) h hc (fun _ => rfl)

theorem true_conj (a h : IProp) (hc : Cons h) : PrI (iand itrue a) h = PrI a h := by
  have hr := def_X_left_i itrue a h
  by_cases ha : PrI a h = 0
  · rw [ha, mul_zero] at hr
    rw [hr, ha]
  · have hca : Cons (iand a h) := cons_of_pos a h ha hc
    rw [itrue_certain (iand a h) hca, one_mul] at hr
    exact hr

/-- 第13章の式 (1) (folio 139): a/h + ā/h = 1。 -/
theorem th_13_1_i (a h : IProp) (hc : Cons h) : PrI a h + PrI (inot a) h = 1 := by
  have step := def_IX_i itrue a h
  rw [true_conj (inot a) h hc, true_conj a h hc, itrue_certain h hc] at step
  linarith

theorem taut_neg_zero (f : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.neg f)) : PrI (interp env f) h = 0 := by
  have h1 : PrI (inot (interp env f)) h = 1 := ax_iii_taut (Form.neg f) env h hc ht
  have h2 := th_13_1_i (interp env f) h hc
  linarith

theorem conj_neg_cert_zero (x E h : IProp) (hc : Cons h) (hE : PrI E h = 1) :
    PrI (iand x (inot E)) h = 0 := by
  have h1 := th_13_1_i E h hc
  have hnE : PrI (inot E) h = 0 := by linarith
  rw [def_X_left_i x (inot E) h, hnE, mul_zero]

/-- 第13章の (12) (folio 141) の短い証明 (phase6c の th_12_i_short と同一)。 -/
theorem th_12_i_short (a b h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h := by
  have hba : PrI (iand b (inot a)) h = 0 := by
    have s := def_IX_i (iand b (inot a)) (iiff a b) h
    have z1 := conj_neg_cert_zero (iand b (inot a)) (iiff a b) h hc hcert
    have z2 : PrI (iand (iand b (inot a)) (iiff a b)) h = 0 :=
      taut_neg_zero
        (Form.conj (Form.conj (Form.var 1) (Form.neg (Form.var 0)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h hc
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  have hab : PrI (iand a (inot b)) h = 0 := by
    have s := def_IX_i (iand a (inot b)) (iiff a b) h
    have z1 := conj_neg_cert_zero (iand a (inot b)) (iiff a b) h hc hcert
    have z2 : PrI (iand (iand a (inot b)) (iiff a b)) h = 0 :=
      taut_neg_zero
        (Form.conj (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h hc
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  have e1 := def_IX_i a b h
  have e2 := def_IX_i b a h
  have e3 := def_X_left_i a b h
  have e4 := def_X_right_i b a h
  linarith

/-- 認証代入: 構文的トートロジー ↔ の解釈同士は (整合な証拠の下で) 確率が等しい
(phase6c の subst_taut を th_12_i_short で閉じたもの)。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i_short _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-! ## A. 公理 (iii.) の末尾 (folio 135) -/

/-- **Ax. (iii.) 末尾** (folio 135): 「If a/h = 1, ah≡h. That is to say, if a is
included in the group specified by h, h and ah are equivalent.」
台帳 ch12-022 (前件 a/h = 1)、ch12-023 (後件 ah≡h)。
等値は前提に相対的 (folio 134、Def. VIII の後: 「equivalence is relative to a
premiss h」) なので、後件 ah≡h を前提 h の下の等値 (ah≡h)/h = 1 として書く。
但し書き `Cons h` は公理 (i) (folio 135) の姿。
証明: \overline{(ah≡h)} は h ā とトートロジー的に同値なので (認証代入)、
(h ā)/h = h/(āh) · ā/h = 0 (ā/h = 0 は第13章の (1) と a/h = 1 から)。
よって第13章の (1) で (ah≡h)/h = 1。 -/
theorem th_12_iii_last (a h : IProp) (hc : Cons h) (ha : PrI a h = 1) :
    PrI (iiff (iand a h) h) h = 1 := by
  have hna : PrI (inot a) h = 0 := by
    have := th_13_1_i a h hc
    linarith
  have hsub : PrI (inot (iiff (iand a h) h)) h = PrI (iand h (inot a)) h :=
    subst_taut
      (Form.neg (Form.iffF (Form.conj (Form.var 0) (Form.var 1)) (Form.var 1)))
      (Form.conj (Form.var 1) (Form.neg (Form.var 0)))
      (fun n => match n with | 0 => a | _ => h) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have hx := def_X_left_i h (inot a) h
  rw [hna, mul_zero] at hx
  have hc1 := th_13_1_i (iiff (iand a h) h) h hc
  linarith

/-! ## B. 公理 (iv. b)・(iv. c) (folio 136)

P = p/h, Q = q/k, R = r/l は確率関係 (前提はそれぞれ別でよい)。 -/

/-- **Ax. (iv. b) 第 1 行前半** (folio 136): 「PQ<P unless Q=1 or P=0」。
台帳 ch12-037 (PQ < P)、038 (Q = 1)、039 (P = 0)。但し書きを前提 Q ≠ 1, P ≠ 0
として書く。値域の公理 (0 ≤ P, Q ≤ 1) を要する (nec_12_ivb_mul_lt)。 -/
theorem th_12_ivb_mul_lt (p h q k : IProp)
    (hQ : PrI q k ≠ 1) (hP : PrI p h ≠ 0) :
    PrI p h * PrI q k < PrI p h := by
  have hP0 : 0 < PrI p h := lt_of_le_of_ne (ax_range_lo_i p h) (Ne.symm hP)
  have hQ1 : PrI q k < 1 := lt_of_le_of_ne (ax_range_hi_i q k) hQ
  nlinarith

/-- **Ax. (iv. b) 第 1 行前半、選言形**: PQ < P、さもなくば Q = 1 または P = 0。
台帳 ch12-037、038、039。 -/
theorem th_12_ivb_mul_lt_unless (p h q k : IProp) :
    PrI p h * PrI q k < PrI p h ∨ PrI q k = 1 ∨ PrI p h = 0 := by
  by_cases hQ : PrI q k = 1
  · exact Or.inr (Or.inl hQ)
  by_cases hP : PrI p h = 0
  · exact Or.inr (Or.inr hP)
  exact Or.inl (th_12_ivb_mul_lt p h q k hQ hP)

/-- **Ax. (iv. b) 第 1 行後半** (folio 136): 「P+Q>P unless Q=0」。
台帳 ch12-040 (P + Q > P)、041 (Q = 0)。但し書きを前提 Q ≠ 0 として書く
(値域の公理 0 ≤ Q で 0 < Q になる。nec_12_ivb_add_gt)。 -/
theorem th_12_ivb_add_gt (p h q k : IProp) (hQ : PrI q k ≠ 0) :
    PrI p h + PrI q k > PrI p h := by
  have hQ0 : 0 < PrI q k := lt_of_le_of_ne (ax_range_lo_i q k) (Ne.symm hQ)
  linarith

/-- **Ax. (iv. b) 第 1 行後半、選言形**: P + Q > P、さもなくば Q = 0。
台帳 ch12-040、041。 -/
theorem th_12_ivb_add_gt_unless (p h q k : IProp) :
    PrI p h + PrI q k > PrI p h ∨ PrI q k = 0 := by
  by_cases hQ : PrI q k = 0
  · exact Or.inr hQ
  · exact Or.inl (th_12_ivb_add_gt p h q k hQ)

/-- **Ax. (iv. b) 第 2 行前半** (folio 136): 「PQ=P if Q=1 or P=0」。
台帳 ch12-042 (PQ = P)、043 (Q = 1)、044 (P = 0)。 -/
theorem th_12_ivb_mul_eq (p h q k : IProp) (hc : PrI q k = 1 ∨ PrI p h = 0) :
    PrI p h * PrI q k = PrI p h := by
  rcases hc with hQ | hP
  · rw [hQ, mul_one]
  · rw [hP, zero_mul]

/-- **Ax. (iv. b) 第 2 行後半** (folio 136): 「P+Q=P if Q=0」。
台帳 ch12-045 (P + Q = P)、046 (Q = 0)。 -/
theorem th_12_ivb_add_eq (p h q k : IProp) (hQ : PrI q k = 0) :
    PrI p h + PrI q k = PrI p h := by
  rw [hQ, add_zero]

/-- **Ax. (iv. c) 前半、⋛ の < の場合** (folio 136): 「If PQ⋛PR, then Q⋛R unless
P=0」。台帳 ch12-047 (PQ ⋛ PR)、048 (Q ⋛ R)、049 (P = 0)。
値域の公理 0 ≤ P を要する (nec_12_ivc_mul_lt)。 -/
theorem th_12_ivc_mul_lt (p h q k r l : IProp) (hP : PrI p h ≠ 0)
    (hlt : PrI p h * PrI q k < PrI p h * PrI r l) :
    PrI q k < PrI r l := by
  have hP0 : 0 < PrI p h := lt_of_le_of_ne (ax_range_lo_i p h) (Ne.symm hP)
  exact lt_of_mul_lt_mul_left hlt hP0.le

/-- **Ax. (iv. c) 前半、⋛ の = の場合**。台帳 ch12-047、048、049。 -/
theorem th_12_ivc_mul_eq (p h q k r l : IProp) (hP : PrI p h ≠ 0)
    (heq : PrI p h * PrI q k = PrI p h * PrI r l) :
    PrI q k = PrI r l :=
  mul_left_cancel₀ hP heq

/-- **Ax. (iv. c) 前半、⋛ の > の場合**。台帳 ch12-047、048、049。 -/
theorem th_12_ivc_mul_gt (p h q k r l : IProp) (hP : PrI p h ≠ 0)
    (hgt : PrI p h * PrI q k > PrI p h * PrI r l) :
    PrI q k > PrI r l :=
  th_12_ivc_mul_lt p h r l q k hP hgt

/-- **Ax. (iv. c) 後半、⋛ の < の場合** (folio 136): 「If P+Q⋛P+R, then Q⋛R and
conversely」。「conversely」を ↔ で書く。台帳 ch12-050 (P + Q ⋛ P + R)、
051 (Q ⋛ R)。 -/
theorem th_12_ivc_add_lt (p h q k r l : IProp) :
    PrI p h + PrI q k < PrI p h + PrI r l ↔ PrI q k < PrI r l :=
  add_lt_add_iff_left _

/-- **Ax. (iv. c) 後半、⋛ の = の場合**。台帳 ch12-050、051。 -/
theorem th_12_ivc_add_eq (p h q k r l : IProp) :
    PrI p h + PrI q k = PrI p h + PrI r l ↔ PrI q k = PrI r l :=
  add_right_inj _

/-- **Ax. (iv. c) 後半、⋛ の > の場合**。台帳 ch12-050、051。 -/
theorem th_12_ivc_add_gt (p h q k r l : IProp) :
    PrI p h + PrI q k > PrI p h + PrI r l ↔ PrI q k > PrI r l :=
  add_lt_add_iff_left _

/-! ### 値域の公理の必要性 (B)

値域の公理を外した実数の上では、(iv. b)(iv. c) の不等式の行は成り立たない。 -/

/-- PQ < P (Q ≠ 1, P ≠ 0) は実数一般では偽: P = 1, Q = 2。 -/
theorem nec_12_ivb_mul_lt :
    ¬ ∀ P Q : ℝ, Q ≠ 1 → P ≠ 0 → P * Q < P := by
  intro H
  have := H 1 2 (by norm_num) (by norm_num)
  norm_num at this

/-- P + Q > P (Q ≠ 0) は実数一般では偽: Q = −1。 -/
theorem nec_12_ivb_add_gt :
    ¬ ∀ P Q : ℝ, Q ≠ 0 → P + Q > P := by
  intro H
  have := H 0 (-1) (by norm_num)
  norm_num at this

/-- PQ < PR ⇒ Q < R (P ≠ 0) は実数一般では偽: P = −1, Q = 1, R = 0。 -/
theorem nec_12_ivc_mul_lt :
    ¬ ∀ P Q R : ℝ, P ≠ 0 → P * Q < P * R → Q < R := by
  intro H
  have := H (-1) 1 0 (by norm_num) (by norm_num)
  norm_num at this

/-! ## C. 公理 (v.)・(vi.) (folio 137) -/

/-- 符号 ±: true は +、false は −。 -/
def sgn : Bool → ℝ
  | true  => 1
  | false => -1

/-- **Ax. (v.) 第 1 の等号** (folio 137): [±P±Q] + [±R±S] = [±P±R] − [∓Q∓S]。
台帳 ch12-061。sP … sS は文字ごとの符号、∓ はその逆符号 −sgn。 -/
theorem th_12_v_1 (p h q k r l s m : IProp) (sP sQ sR sS : Bool) :
    (sgn sP * PrI p h + sgn sQ * PrI q k) + (sgn sR * PrI r l + sgn sS * PrI s m)
      = (sgn sP * PrI p h + sgn sR * PrI r l)
        - (-sgn sQ * PrI q k + -sgn sS * PrI s m) := by
  ring

/-- **Ax. (v.) 第 2 の等号** (folio 137、行をまたぐ):
[±P±R] − [∓Q∓S] = [±P±R] + [±Q±S]。台帳 ch12-061、062。 -/
theorem th_12_v_2 (p h q k r l s m : IProp) (sP sQ sR sS : Bool) :
    (sgn sP * PrI p h + sgn sR * PrI r l) - (-sgn sQ * PrI q k + -sgn sS * PrI s m)
      = (sgn sP * PrI p h + sgn sR * PrI r l) + (sgn sQ * PrI q k + sgn sS * PrI s m) := by
  ring

/-- **Ax. (v.) 第 3 の等号** (folio 137): [±P±R] + [±Q±S] = [±P±Q] − [∓R∓S]。
台帳 ch12-062。 -/
theorem th_12_v_3 (p h q k r l s m : IProp) (sP sQ sR sS : Bool) :
    (sgn sP * PrI p h + sgn sR * PrI r l) + (sgn sQ * PrI q k + sgn sS * PrI s m)
      = (sgn sP * PrI p h + sgn sQ * PrI q k)
        - (-sgn sR * PrI r l + -sgn sS * PrI s m) := by
  ring

/-- **Ax. (v.) 全体** (folio 137、2 行の連鎖等式)。台帳 ch12-061、062。 -/
theorem th_12_v (p h q k r l s m : IProp) (sP sQ sR sS : Bool) :
    (sgn sP * PrI p h + sgn sQ * PrI q k) + (sgn sR * PrI r l + sgn sS * PrI s m)
      = (sgn sP * PrI p h + sgn sR * PrI r l)
        - (-sgn sQ * PrI q k + -sgn sS * PrI s m) ∧
    (sgn sP * PrI p h + sgn sR * PrI r l) - (-sgn sQ * PrI q k + -sgn sS * PrI s m)
      = (sgn sP * PrI p h + sgn sR * PrI r l) + (sgn sQ * PrI q k + sgn sS * PrI s m) ∧
    (sgn sP * PrI p h + sgn sR * PrI r l) + (sgn sQ * PrI q k + sgn sS * PrI s m)
      = (sgn sP * PrI p h + sgn sQ * PrI q k)
        - (-sgn sR * PrI r l + -sgn sS * PrI s m) :=
  ⟨th_12_v_1 p h q k r l s m sP sQ sR sS, th_12_v_2 p h q k r l s m sP sQ sR sS,
    th_12_v_3 p h q k r l s m sP sQ sR sS⟩

/-- **Ax. (vi.)** (folio 137): 「P(R±S) = PR±PS」。台帳 ch12-064。 -/
theorem th_12_vi (p h r l s m : IProp) (sS : Bool) :
    PrI p h * (PrI r l + sgn sS * PrI s m)
      = PrI p h * PrI r l + sgn sS * (PrI p h * PrI s m) := by
  ring

/-! ## D. §6 末尾と §7 の例 (folio 137) -/

/-- **§6 末尾** (folio 137): 「if P+Q=R and Q=S+T, … The equation must be written
P+(S+T)=R」。台帳 ch12-053 (P + Q = R)、054 (Q = S + T)、057 (P + (S + T) = R)。 -/
theorem th_12_6_bracketed (p h q k r l s m t n : IProp)
    (h1 : PrI p h + PrI q k = PrI r l) (h2 : PrI q k = PrI s m + PrI t n) :
    PrI p h + (PrI s m + PrI t n) = PrI r l := by
  rw [← h2]; exact h1

/-- ℝ 担体での帰結 (形式化の境界の記録、台帳の行には対応づけない)。
§6 末尾 (folio 137): 「it does not follow that P+S+T=R, since no meaning has
been assigned to such an expression as P+S+T」(ch12-055)。Keynes の代数では
従わない (結合律を仮定しない)。PrI の値は実数で和が全域・結合的なので、Lean が
括弧なしの和を左結合 (P + S) + T と読むと ℝ 担体では従う —— 担体の強さの差
(所見候補 F12.1)。 -/
theorem nec_12_6_unbracketed (p h q k r l s m t n : IProp)
    (h1 : PrI p h + PrI q k = PrI r l) (h2 : PrI q k = PrI s m + PrI t n) :
    PrI p h + PrI s m + PrI t n = PrI r l := by
  linarith

/-- ℝ 担体での帰結 (形式化の境界の記録、台帳の行には対応づけない)。
§6 末尾 (folio 137): 「we cannot infer from the foregoing axioms that
(P+S)+T=R. The following axioms allow us to make this … inferences」(ch12-058)。
Keynes の代数では公理 (v.) と和の存在 (P+S=A) なしには従わない。ℝ 担体では
環の演算だけで従う (所見候補 F12.1)。 -/
theorem nec_12_6_rebracketed (p h q k r l s m t n : IProp)
    (h1 : PrI p h + PrI q k = PrI r l) (h2 : PrI q k = PrI s m + PrI t n) :
    (PrI p h + PrI s m) + PrI t n = PrI r l := by
  linarith

/-- **§6 末尾** (folio 137): 「in cases in which the sum P+S exists, i.e. when
P+S=A and A is a relation of probability」。A = a/g (確率関係)。
台帳 ch12-060 (P + S = A)。結論は (P+S)+T = R を A で書いた形。 -/
theorem th_12_6_sum_exists (p h q k r l s m t n a g : IProp)
    (h1 : PrI p h + PrI q k = PrI r l) (h2 : PrI q k = PrI s m + PrI t n)
    (hA : PrI p h + PrI s m = PrI a g) :
    PrI a g + PrI t n = PrI r l := by
  linarith

/-- **§7** (folio 137): 「if P+Q = R+S then P−R = S−Q, provided that the differences
P−R and S−Q exist」。台帳 ch12-066 (P + Q = R + S)、067 (P − R = S − Q)。
差の存在条件は実数の上では前提にならない (形式化の境界)。 -/
theorem th_12_7_sub (p h q k r l s m : IProp)
    (h1 : PrI p h + PrI q k = PrI r l + PrI s m) :
    PrI p h - PrI r l = PrI s m - PrI q k := by
  linarith

/-- **§7** (folio 137): 「(P+Q)(R+S) = (P+Q)R + (P+Q)S = [PR+QR] + [PS+QS] =
[PR+QS] + [QR+PS]」。台帳 ch12-069 (行内の連鎖等式 1 本; 等号ごとに連言の成分)。 -/
theorem th_12_7_distrib (p h q k r l s m : IProp) :
    (PrI p h + PrI q k) * (PrI r l + PrI s m)
      = (PrI p h + PrI q k) * PrI r l + (PrI p h + PrI q k) * PrI s m ∧
    (PrI p h + PrI q k) * PrI r l + (PrI p h + PrI q k) * PrI s m
      = (PrI p h * PrI r l + PrI q k * PrI r l)
        + (PrI p h * PrI s m + PrI q k * PrI s m) ∧
    (PrI p h * PrI r l + PrI q k * PrI r l) + (PrI p h * PrI s m + PrI q k * PrI s m)
      = (PrI p h * PrI r l + PrI q k * PrI s m)
        + (PrI q k * PrI r l + PrI p h * PrI s m) := by
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ## E. Def. XIII・XIV (folio 138) -/

/-- **Def. XIII** (folio 138): 「If a₁/a₂h = a₁/h and a₂/a₁h = a₂/h, the
probabilities a₁/h and a₂/h are independent.」 -/
def Independent (a₁ a₂ h : IProp) : Prop :=
  PrI a₁ (iand a₂ h) = PrI a₁ h ∧ PrI a₂ (iand a₁ h) = PrI a₂ h

/-- **Def. XIV** (folio 138): 「If a₁/a₂h = a₁/h, a₂ is irrelevant on the whole, or,
for short, irrelevant to a₁/h.」 -/
def Irrelevant (a₂ a₁ h : IProp) : Prop := PrI a₁ (iand a₂ h) = PrI a₁ h

/-- **Def. XIV の対称形**: a₁/a₂h = a₁/h ならば a₂/a₁h = a₂/h (a₁/h ≠ 0 のとき)。
Def. X の左右両形 a₁a₂/h = a₁/a₂h · a₂/h = a₂/a₁h · a₁/h で a₁/h を約す。
台帳 ch12-073。 -/
theorem th_12_XIV_symm (a₁ a₂ h : IProp) (hirr : PrI a₁ (iand a₂ h) = PrI a₁ h)
    (h1 : PrI a₁ h ≠ 0) :
    PrI a₂ (iand a₁ h) = PrI a₂ h := by
  have hl := def_X_left_i a₁ a₂ h
  have hr := def_X_right_i a₁ a₂ h
  rw [hirr] at hl
  have heq : PrI a₁ h * PrI a₂ (iand a₁ h) = PrI a₁ h * PrI a₂ h := by
    rw [mul_comm (PrI a₁ h) (PrI a₂ (iand a₁ h)), ← hr, hl, mul_comm]
  exact mul_left_cancel₀ h1 heq

/-- **Def. XIV から Def. XIII へ**: a₁/a₂h = a₁/h かつ a₁/h ≠ 0 ならば、a₁/h と
a₂/h は独立 (Def. XIII の 2 条件)。台帳 ch12-073。 -/
theorem th_12_XIV_indep (a₁ a₂ h : IProp) (hirr : PrI a₁ (iand a₂ h) = PrI a₁ h)
    (h1 : PrI a₁ h ≠ 0) :
    Independent a₁ a₂ h :=
  ⟨hirr, th_12_XIV_symm a₁ a₂ h hirr h1⟩

end KeynesXII

/-! ## 監査クエリ (Phase 10a) -/

-- 移植定理 (phase6c)
#print axioms KeynesXII.itrue_certain
#print axioms KeynesXII.true_conj
#print axioms KeynesXII.th_13_1_i
#print axioms KeynesXII.taut_neg_zero
#print axioms KeynesXII.conj_neg_cert_zero
#print axioms KeynesXII.th_12_i_short
#print axioms KeynesXII.subst_taut
-- A. 公理 (iii.) 末尾
#print axioms KeynesXII.th_12_iii_last
-- B. 公理 (iv. b)・(iv. c)
#print axioms KeynesXII.th_12_ivb_mul_lt
#print axioms KeynesXII.th_12_ivb_mul_lt_unless
#print axioms KeynesXII.th_12_ivb_add_gt
#print axioms KeynesXII.th_12_ivb_add_gt_unless
#print axioms KeynesXII.th_12_ivb_mul_eq
#print axioms KeynesXII.th_12_ivb_add_eq
#print axioms KeynesXII.th_12_ivc_mul_lt
#print axioms KeynesXII.th_12_ivc_mul_eq
#print axioms KeynesXII.th_12_ivc_mul_gt
#print axioms KeynesXII.th_12_ivc_add_lt
#print axioms KeynesXII.th_12_ivc_add_eq
#print axioms KeynesXII.th_12_ivc_add_gt
#print axioms KeynesXII.nec_12_ivb_mul_lt
#print axioms KeynesXII.nec_12_ivb_add_gt
#print axioms KeynesXII.nec_12_ivc_mul_lt
-- C. 公理 (v.)・(vi.)
#print axioms KeynesXII.th_12_v_1
#print axioms KeynesXII.th_12_v_2
#print axioms KeynesXII.th_12_v_3
#print axioms KeynesXII.th_12_v
#print axioms KeynesXII.th_12_vi
-- D. §6 末尾・§7
#print axioms KeynesXII.th_12_6_bracketed
#print axioms KeynesXII.nec_12_6_unbracketed
#print axioms KeynesXII.nec_12_6_rebracketed
#print axioms KeynesXII.th_12_6_sum_exists
#print axioms KeynesXII.th_12_7_sub
#print axioms KeynesXII.th_12_7_distrib
-- E. Def. XIV
#print axioms KeynesXII.th_12_XIV_symm
#print axioms KeynesXII.th_12_XIV_indep
