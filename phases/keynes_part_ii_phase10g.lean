/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 10g
#
# 第 X 章「Introductory」(1921 年 Macmillan 初版 folio 115–122)
# 全数台帳 docs/全数台帳/ch10.md の式行のうち Lean 欄が「未」だった 6 行を、
# 行ごとに定理文として書く (B28g)。
#
# ## 基準
#   1921 年初版の頁画像のみ (folio 120 §4、folio 121 §6)。定理名は
#   th_10_<項目>_<枝>。台帳の行 ID (ch10-NNN) は各定理の docstring に書く。
#
# ## キャリア
#   phase6c の内包キャリア (IProp, PrI, Cons; 公理 (i) の但し書き付き) をそのまま
#   写す。`Prop → Prop → ℝ` 型の確率関係は置かない (CLAUDE.md 不変条件 3)。
#
# ## 収録 (台帳の行 ID)
#   A. Def. II  (folio 120): 「The Definition of Certainty : a/h = 1.」   ch10-008
#   B. Def. III (folio 120): 「The Definition of Impossibility : a/h = 0.」 ch10-009
#   C. Def. VII (folio 120): 「The Definition of a Group : the class of
#      propositions a such that a/h = 1 is the group h.」              ch10-011
#   D. Def. XII (folio 120): 「The Definition of Irrelevance : if a₁/a₂h = a₁/h,
#      a₂ is irrelevant to a₁/h.」                                     ch10-021
#   E. (48) の等事前の場合 (folio 121): 「and if a₁/h = a₂/h,
#      a₁/bh = q₁/(q₁ + q₂)」                                        ch10-042, 043
#
#   定義の行 (A–D) は、台帳の細則 6 (ch10.md ヘッダ第 3 回) に従い、印刷の関係式を
#   本体とする def を置き、その def を使う定理を併せて置く。
#
# ## 定義番号の食い違い (備考に残すもの)
#   folio 120 §4 は「the numbers referring to the numbers of Chapter XII.」と
#   言いながら独立を XI.、無関連を XII. と印刷する。第 XII 章 (folio 138) では
#   独立・無関連は XIII.・XIV.。本ファイルの定理名は第 X 章の印刷の番号 (XII) を使い、
#   内容は第 XII 章の Def. XIV と同じ。
#
# ## 前提の補充 (T)
#   E の印刷 (folio 121) に但し書きは無い。除法のため b/h ≠ 0 が要り、これを第 XIV 章
#   (38) の但し書き「provided bh is consistent」の形 `Cons (iand b h)` で置き、
#   cons_of_pos_src (Def. VI の印刷の向きの対偶) で b/h ≠ 0 に落とす。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase10g.lean
-/

import Mathlib

namespace KeynesX

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

/-! ## 整合性の公理 (phase6c と同一; 本ファイルの定理が使うのは cons_of_pos と cons_of_pos_src) -/

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

theorem conj_neg_cert_zero (x E h : IProp) (hc : Cons h) (hE : PrI E h = 1) :
    PrI (iand x (inot E)) h = 0 := by
  have h1 := th_13_1_i E h hc
  have hnE : PrI (inot E) h = 0 := by linarith
  rw [def_X_left_i x (inot E) h, hnE, mul_zero]

/-! ## A. Def. II (folio 120) -/

/-- **Def. II** (folio 120 §4): 「II. The Definition of Certainty : a/h = 1.」
台帳 ch10-008。def の本体が印刷の関係式 a/h = 1。 -/
def Certain (a h : IProp) : Prop := PrI a h = 1

/-- **Def. II の名前と関係式**: a/h が確実であることと a/h = 1 とは同じ。台帳 ch10-008。 -/
theorem th_10_II (a h : IProp) : Certain a h ↔ PrI a h = 1 :=
  Iff.rfl

/-- **Def. II の用例 1**: 整合な h のもとで、形式的真理 ⊤ の確率は確実 (公理 (iii.)、
folio 135)。台帳 ch10-008。 -/
theorem th_10_II_true (h : IProp) (hc : Cons h) : Certain itrue h :=
  itrue_certain h hc

/-- **Def. II の用例 2**: a/h と b/h が確実ならば ab/h も確実 (h 整合)。
Def. IX で ab/h = a/h − ab̄/h、ab̄/h = a/b̄h · b̄/h、b̄/h = 0 は第13章の (1)。
台帳 ch10-008。 -/
theorem th_10_II_conj (a b h : IProp) (hc : Cons h)
    (ha : Certain a h) (hb : Certain b h) : Certain (iand a b) h := by
  have s := def_IX_i a b h
  have z := conj_neg_cert_zero a b h hc hb
  unfold Certain at ha ⊢
  linarith

/-! ## B. Def. III (folio 120) -/

/-- **Def. III** (folio 120 §4): 「III. The Definition of Impossibility : a/h = 0.」
台帳 ch10-009。def の本体が印刷の関係式 a/h = 0。 -/
def Impossible (a h : IProp) : Prop := PrI a h = 0

/-- **Def. III の名前と関係式**: a/h が不可能であることと a/h = 0 とは同じ。台帳 ch10-009。 -/
theorem th_10_III (a h : IProp) : Impossible a h ↔ PrI a h = 0 :=
  Iff.rfl

/-- **Def. III と Def. II**: h 整合のとき、a/h が確実であることと ā/h が不可能で
あることとは同値 (第13章の (1)、folio 139)。台帳 ch10-009。 -/
theorem th_10_III_compl (a h : IProp) (hc : Cons h) :
    Certain a h ↔ Impossible (inot a) h := by
  have s := th_13_1_i a h hc
  unfold Certain Impossible
  constructor
  · intro ha; linarith
  · intro hn; linarith

/-- **Def. III の用例**: 整合な h のもとで、⊤ の否定の確率は不可能。台帳 ch10-009。 -/
theorem th_10_III_false (h : IProp) (hc : Cons h) : Impossible (inot itrue) h :=
  (th_10_III_compl itrue h hc).mp (th_10_II_true h hc)

/-- **Def. III と Def. VI**: a/h が不可能ならば ah は整合でない (Def. VI、folio 120
「ah is inconsistent if a/h = 0」の向き; cons_of_pos_src の対偶)。台帳 ch10-009。 -/
theorem th_10_III_inconsistent (a h : IProp) (hi : Impossible a h) :
    ¬ Cons (iand a h) :=
  fun hca => cons_of_pos_src a h hca hi

/-! ## C. Def. VII (folio 120) -/

/-- **Def. VII** (folio 120 §4): 「VII. The Definition of a Group : the class of
propositions a such that a/h = 1 is the group h.」台帳 ch10-011。
集合の内包の条件が印刷の関係式 a/h = 1。 -/
def groupOf (h : IProp) : Set IProp := {a | PrI a h = 1}

/-- **Def. VII の所属と関係式**: a が群 h に属することと a/h = 1 とは同じ。台帳 ch10-011。 -/
theorem th_10_VII (a h : IProp) : a ∈ groupOf h ↔ PrI a h = 1 :=
  Iff.rfl

/-- **Def. VII の用例 1**: ⊤ は整合な h の群に属する。台帳 ch10-011。 -/
theorem th_10_VII_true (h : IProp) (hc : Cons h) : itrue ∈ groupOf h :=
  itrue_certain h hc

/-- **Def. VII の用例 2**: 群 h は連言で閉じる (h 整合)。台帳 ch10-011。 -/
theorem th_10_VII_conj (a b h : IProp) (hc : Cons h)
    (ha : a ∈ groupOf h) (hb : b ∈ groupOf h) : iand a b ∈ groupOf h :=
  th_10_II_conj a b h hc ha hb

/-- **Def. VII の用例 3**: a が群 h に属すれば ā は属さない (h 整合)。台帳 ch10-011。 -/
theorem th_10_VII_not (a h : IProp) (hc : Cons h) (ha : a ∈ groupOf h) :
    inot a ∉ groupOf h := by
  intro hn
  have s := th_13_1_i a h hc
  rw [th_10_VII] at ha hn
  linarith

/-! ## D. Def. XII (folio 120) -/

/-- **Def. XI** (folio 120 §4; 第 XII 章 folio 138 では XIII.): 「if a₁/a₂h = a₁/h
and a₂/a₁h = a₂/h, a₁/h and a₂/h are independent.」D の用例のために置く
(台帳 ch10-018・019 は既に 3a/Independent で対応)。 -/
def Independent (a₁ a₂ h : IProp) : Prop :=
  PrI a₁ (iand a₂ h) = PrI a₁ h ∧ PrI a₂ (iand a₁ h) = PrI a₂ h

/-- **Def. XII** (folio 120 §4; 第 XII 章 folio 138 では XIV.): 「XII. The Definition
of Irrelevance : if a₁/a₂h = a₁/h, a₂ is irrelevant to a₁/h.」台帳 ch10-021。
def の本体が印刷の関係式 a₁/a₂h = a₁/h。 -/
def Irrelevant (a₂ a₁ h : IProp) : Prop := PrI a₁ (iand a₂ h) = PrI a₁ h

/-- **Def. XII の前件から名前へ**: a₁/a₂h = a₁/h ならば a₂ は a₁/h に無関連。
台帳 ch10-021。 -/
theorem th_10_XII (a₁ a₂ h : IProp) (hirr : PrI a₁ (iand a₂ h) = PrI a₁ h) :
    Irrelevant a₂ a₁ h :=
  hirr

/-- **Def. XII の対称形** (folio 121 の Theorem of Independence の予告と同じ内容):
a₂ が a₁/h に無関連ならば a₁ は a₂/h に無関連 (a₁/h ≠ 0 のとき)。
Def. X の左右両形 a₁a₂/h = a₁/a₂h · a₂/h = a₂/a₁h · a₁/h で a₁/h を約す。
台帳 ch10-021。 -/
theorem th_10_XII_symm (a₁ a₂ h : IProp) (hirr : Irrelevant a₂ a₁ h)
    (h1 : PrI a₁ h ≠ 0) : Irrelevant a₁ a₂ h := by
  unfold Irrelevant at hirr ⊢
  have hl := def_X_left_i a₁ a₂ h
  have hr := def_X_right_i a₁ a₂ h
  rw [hirr] at hl
  have heq : PrI a₁ h * PrI a₂ (iand a₁ h) = PrI a₁ h * PrI a₂ h := by
    rw [mul_comm (PrI a₁ h) (PrI a₂ (iand a₁ h)), ← hr, hl, mul_comm]
  exact mul_left_cancel₀ h1 heq

/-- **Def. XII から Def. XI へ**: a₂ が a₁/h に無関連で a₁/h ≠ 0 ならば、a₁/h と
a₂/h は独立。台帳 ch10-021。 -/
theorem th_10_XII_indep (a₁ a₂ h : IProp) (hirr : Irrelevant a₂ a₁ h)
    (h1 : PrI a₁ h ≠ 0) : Independent a₁ a₂ h :=
  ⟨hirr, th_10_XII_symm a₁ a₂ h hirr h1⟩

/-! ## E. (48) の等事前の場合 (folio 121) -/

/-- **(48) の等事前の場合** (folio 121 §6): 「Further, if a₁/h = p₁, a₂/h = p₂,
b/a₁h = q₁, b/a₂h = q₂, and a₁/bh + a₂/bh = 1, then a₁/bh = p₁q₁/(p₁q₁ + p₂q₂) ;
and if a₁/h = a₂/h, a₁/bh = q₁/(q₁ + q₂)」。
台帳 ch10-042 (前提 heq: a₁/h = a₂/h)、ch10-043 (結論 a₁/bh = q₁/(q₁ + q₂))。
前提 hp₁–hsum は台帳 ch10-036–040 の行。印刷に但し書きは無いが、除法のため
`Cons (iand b h)` (第 XIV 章 (38) の「provided bh is consistent」) を補う (T)。
証明: Def. X の左右両形で a_i/bh · b/h = p_i q_i、和をとって b/h = p₁(q₁ + q₂)
(p₂ = p₁)。b/h ≠ 0 (cons_of_pos_src) から p₁ ≠ 0、q₁ + q₂ ≠ 0 で p₁ を約す。 -/
theorem th_10_48_equal (a₁ a₂ b h : IProp) (p₁ p₂ q₁ q₂ : ℝ)
    (hp₁ : PrI a₁ h = p₁) (hp₂ : PrI a₂ h = p₂)
    (hq₁ : PrI b (iand a₁ h) = q₁) (hq₂ : PrI b (iand a₂ h) = q₂)
    (hsum : PrI a₁ (iand b h) + PrI a₂ (iand b h) = 1)
    (heq : PrI a₁ h = PrI a₂ h)
    (hcb : Cons (iand b h)) :
    PrI a₁ (iand b h) = q₁ / (q₁ + q₂) := by
  have hb : PrI b h ≠ 0 := cons_of_pos_src b h hcb
  have hp : p₂ = p₁ := by
    rw [← hp₁, ← hp₂]
    exact heq.symm
  have e₁l := def_X_left_i a₁ b h
  have e₁r := def_X_right_i a₁ b h
  have e₂l := def_X_left_i a₂ b h
  have e₂r := def_X_right_i a₂ b h
  rw [hq₁, hp₁] at e₁r
  rw [hq₂, hp₂] at e₂r
  have k₁ : PrI a₁ (iand b h) * PrI b h = p₁ * q₁ := by rw [← e₁l, e₁r]; ring
  have k₂ : PrI a₂ (iand b h) * PrI b h = p₂ * q₂ := by rw [← e₂l, e₂r]; ring
  have hS : PrI b h = p₁ * (q₁ + q₂) := by
    have : (PrI a₁ (iand b h) + PrI a₂ (iand b h)) * PrI b h = p₁ * q₁ + p₂ * q₂ := by
      rw [add_mul, k₁, k₂]
    rw [hsum, one_mul, hp] at this
    linarith
  have hp0 : p₁ ≠ 0 := by
    intro h0
    apply hb
    rw [hS, h0, zero_mul]
  have hq0 : q₁ + q₂ ≠ 0 := by
    intro h0
    apply hb
    rw [hS, h0, mul_zero]
  rw [eq_div_iff hq0]
  apply mul_left_cancel₀ hp0
  rw [hS] at k₁
  rw [← k₁]
  ring

end KeynesX

/-! ## 監査クエリ (Phase 10g) -/

-- 移植定理 (phase6c)
#print axioms KeynesX.itrue_certain
#print axioms KeynesX.true_conj
#print axioms KeynesX.th_13_1_i
#print axioms KeynesX.conj_neg_cert_zero
-- A. Def. II
#print axioms KeynesX.th_10_II
#print axioms KeynesX.th_10_II_true
#print axioms KeynesX.th_10_II_conj
-- B. Def. III
#print axioms KeynesX.th_10_III
#print axioms KeynesX.th_10_III_compl
#print axioms KeynesX.th_10_III_false
#print axioms KeynesX.th_10_III_inconsistent
-- C. Def. VII
#print axioms KeynesX.th_10_VII
#print axioms KeynesX.th_10_VII_true
#print axioms KeynesX.th_10_VII_conj
#print axioms KeynesX.th_10_VII_not
-- D. Def. XII
#print axioms KeynesX.th_10_XII
#print axioms KeynesX.th_10_XII_symm
#print axioms KeynesX.th_10_XII_indep
-- E. (48) の等事前の場合
#print axioms KeynesX.th_10_48_equal
