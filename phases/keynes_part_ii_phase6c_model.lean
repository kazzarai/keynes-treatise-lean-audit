/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 6c 有限モデル
#
# 新井一成・Claude共著、2026年10月20日 (B09)
# **修復後の phase6c 公理群 (KeynesI、Cons 付き) の無矛盾性: 有限モデル**
#
# ## 目的
#   phase6c.lean の公理群 (2026-10-20 修復版) を満たす具体的な構造を一つ作り、
#   各公理の文をそのまま命題として書いて証明する (axiom 宣言そのものはモデル化
#   できないので、公理の文を写す)。これにより
#   (a) 修復後の公理群は無矛盾 (モデルが存在する)、
#   (b) 修復前の経路 pr_self_evidence (任意の a, h で a/(a ∧ h) = 1) は
#       修復後の公理群から導けない (モデルで偽)、
#   が示される。(b) は健全性による通常の論法: 公理群から導ける命題はすべての
#   モデルで真なので、あるモデルで偽な命題は導けない。
#   さらに公理群を一つの構造 `Sys` にまとめ、「Sys を満たす任意の構造で
#   a/(a ∧ h) = 1」が偽であることを Lean 内部の定理 not_self_evidence として示す。
#
# ## モデル
#   世界集合 W := Fin 2、命題 M := Finset W (世界の集合)。
#   連言 := ∩、選言 := ∪、否定 := 補集合、同値 := (p ∩ q) ∪ (pᶜ ∩ qᶜ)、⊤ := univ。
#   pr p h := if h.card = 0 then 0 else (p ∩ h).card / h.card (条件付き相対頻度;
#   h.card = 0 のときは 0 と約定)。
#   Cons h := h.Nonempty (h が充足可能 = 矛盾する連言でない)。
#
# ## 原典 (唯一の基準) との対応
#   Cons h が偽 (h = ∅) のときの pr の値は約定であり、原典の公理 (i) (folio 135)
#   が「存在しない」とする確率関係の代わりに置いた値である。公理群は Cons h の
#   範囲でしか pr の値を拘束しないので、約定の取り方は公理の成立に影響しない
#   ことを各定理が確かめる (def_IX_i, def_X_*_i, ax_range_* は約定 0 の下で
#   無条件に成立する)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase6c_model.lean
-/

import Mathlib

namespace KeynesI_model

/-! ## 構文 (phase6c.lean と同一の複製) -/

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

def Taut (f : Form) : Prop := ∀ v : ℕ → Bool, evalB v f = true

/-! ## 公理群の構造化 (phase6c.lean の axiom 宣言の写し) -/

/-- 結合子・確率関係・整合性述語の組。 -/
structure Ops where
  IProp : Type
  iand : IProp → IProp → IProp
  ior  : IProp → IProp → IProp
  inot : IProp → IProp
  iiff : IProp → IProp → IProp
  itrue : IProp
  PrI : IProp → IProp → ℝ
  Cons : IProp → Prop

/-- 構文の解釈 (phase6c.lean の interp と同じ形)。 -/
def Ops.interp (S : Ops) (env : ℕ → S.IProp) : Form → S.IProp
  | .var n    => env n
  | .tru      => S.itrue
  | .fls      => S.inot S.itrue
  | .conj f g => S.iand (S.interp env f) (S.interp env g)
  | .disj f g => S.ior (S.interp env f) (S.interp env g)
  | .neg f    => S.inot (S.interp env f)
  | .iffF f g => S.iiff (S.interp env f) (S.interp env g)

/-- **修復後の公理群** (phase6c.lean の axiom の文をそのまま場に写したもの)。 -/
structure Sys (S : Ops) : Prop where
  def_IX_i : ∀ p q h, S.PrI (S.iand p (S.inot q)) h + S.PrI (S.iand p q) h = S.PrI p h
  def_X_left_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI p (S.iand q h) * S.PrI q h
  def_X_right_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI q (S.iand p h) * S.PrI p h
  def_XI_i : ∀ (P Q R : ℝ), Q ≠ 0 → P * Q = R → P = R / Q
  ax_range_lo_i : ∀ p h, 0 ≤ S.PrI p h
  ax_range_hi_i : ∀ p h, S.PrI p h ≤ 1
  def_VIII_i : ∀ a b h, S.Cons (S.iand a h) → S.Cons (S.iand b h) →
    (S.PrI (S.iiff a b) h = 1 ↔ (S.PrI b (S.iand a h) = 1 ∧ S.PrI a (S.iand b h) = 1))
  def_VIII_i_src : ∀ a b h,
    S.PrI b (S.iand a h) = 1 → S.PrI a (S.iand b h) = 1 → S.PrI (S.iiff a b) h = 1
  ax_iii_taut : ∀ (f : Form) (env : ℕ → S.IProp) (h : S.IProp),
    S.Cons h → Taut f → S.PrI (S.interp env f) h = 1
  cons_true : S.Cons S.itrue
  cons_of_pos_src : ∀ a h, S.Cons (S.iand a h) → S.PrI a h ≠ 0
  cons_of_pos : ∀ a h, S.PrI a h ≠ 0 → S.Cons h → S.Cons (S.iand a h)
  cons_iff_taut : ∀ (f g : Form) (env : ℕ → S.IProp),
    Taut (Form.iffF f g) → (S.Cons (S.interp env f) ↔ S.Cons (S.interp env g))

/-! ## 有限モデル -/

/-- 世界集合。 -/
abbrev W := Fin 2
/-- 命題 = 世界の集合。 -/
abbrev M := Finset W

def mand (p q : M) : M := p ∩ q
def mor  (p q : M) : M := p ∪ q
def mnot (p : M) : M := pᶜ
def miff (p q : M) : M := (p ∩ q) ∪ (pᶜ ∩ qᶜ)
def mtrue : M := Finset.univ

/-- 条件付き相対頻度。h.card = 0 のときは 0 と約定。 -/
noncomputable def pr (p h : M) : ℝ :=
  if h.card = 0 then 0 else ((p ∩ h).card : ℝ) / h.card

/-- 整合性 = 充足可能性。 -/
def Cons (h : M) : Prop := h.Nonempty

/-! ### 基本補題 -/

theorem pr_of_card_zero {p h : M} (hh : h.card = 0) : pr p h = 0 := by
  simp [pr, hh]

theorem pr_of_card_ne_zero {p h : M} (hh : h.card ≠ 0) :
    pr p h = ((p ∩ h).card : ℝ) / h.card := by
  simp [pr, hh]

theorem cons_iff_card {h : M} : Cons h ↔ h.card ≠ 0 :=
  Finset.card_ne_zero.symm

/-- 前提が整合なとき、確実 ⟺ 前提が結論を含む。 -/
theorem pr_eq_one_iff {p h : M} (hh : h.card ≠ 0) : pr p h = 1 ↔ h ⊆ p := by
  have hpos : (0 : ℝ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
  rw [pr_of_card_ne_zero hh, div_eq_one_iff_eq hpos.ne']
  constructor
  · intro H
    have hc : (p ∩ h).card = h.card := by exact_mod_cast H
    have e : p ∩ h = h := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hc.ge
    exact Finset.inter_eq_right.mp e
  · intro H
    rw [Finset.inter_eq_right.mpr H]

/-- 確実ならば h.card ≠ 0 (約定 0 ≠ 1)。 -/
theorem card_ne_zero_of_pr_eq_one {p h : M} (H : pr p h = 1) : h.card ≠ 0 := by
  intro hh
  rw [pr_of_card_zero hh] at H
  exact zero_ne_one H

theorem card_ne_zero_of_inter {a h : M} (hc : (a ∩ h).card ≠ 0) : h.card ≠ 0 := by
  intro hh
  apply hc
  exact Nat.eq_zero_of_le_zero (hh ▸ Finset.card_le_card Finset.inter_subset_right)

/-- Def. VIII の集合論的中身: h ⊆ (a ≡ b) ⟺ (a ∩ h ⊆ b ∧ b ∩ h ⊆ a)。 -/
theorem subset_miff_iff (a b h : M) :
    h ⊆ miff a b ↔ (a ∩ h ⊆ b ∧ b ∩ h ⊆ a) := by
  simp only [miff, Finset.subset_iff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  constructor
  · intro H
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rcases H hw.2 with ⟨_, hb⟩ | ⟨hna, _⟩
      · exact hb
      · exact absurd hw.1 hna
    · rcases H hw.2 with ⟨ha, _⟩ | ⟨_, hnb⟩
      · exact ha
      · exact absurd hw.1 hnb
  · rintro ⟨H1, H2⟩ w hw
    by_cases ha : w ∈ a
    · exact Or.inl ⟨ha, H1 ⟨ha, hw⟩⟩
    · exact Or.inr ⟨ha, fun hb => ha (H2 ⟨hb, hw⟩)⟩

/-! ### 各公理の成立 (公理の文をそのまま命題として証明) -/

/-- **Def. IX** (folio 135): ab/h + a\bar{b}/h = a/h。 -/
theorem model_def_IX_i (p q h : M) :
    pr (mand p (mnot q)) h + pr (mand p q) h = pr p h := by
  by_cases hh : h.card = 0
  · simp [pr, hh]
  · have key : (mand (mand p (mnot q)) h).card + (mand (mand p q) h).card
        = (mand p h).card := by
      have e1 : mand (mand p q) h = (mand p h).filter (fun w => w ∈ q) := by
        ext w; simp [mand, Finset.mem_filter]; tauto
      have e2 : mand (mand p (mnot q)) h = (mand p h).filter (fun w => ¬ w ∈ q) := by
        ext w; simp [mand, mnot, Finset.mem_filter]; tauto
      rw [e1, e2, add_comm]
      exact Finset.card_filter_add_card_filter_not _
    simp only [pr, if_neg hh]
    rw [← add_div]
    congr 1
    exact_mod_cast key

/-- **Def. X 左形** (folio 135): ab/h = a/bh · b/h。 -/
theorem model_def_X_left_i (p q h : M) :
    pr (mand p q) h = pr p (mand q h) * pr q h := by
  by_cases hh : h.card = 0
  · simp [pr, hh]
  by_cases hqh : (mand q h).card = 0
  · have hz : (mand (mand p q) h).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← hqh]
      apply Finset.card_le_card
      intro w hw
      simp only [mand, Finset.mem_inter] at hw ⊢
      exact ⟨hw.1.2, hw.2⟩
    simp only [pr, if_neg hh, if_pos hqh]
    simp [mand] at hz
    simp [mand, hz]
  · simp only [mand] at hqh
    have hpos : (0 : ℝ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
    have hqpos : (0 : ℝ) < (q ∩ h).card := by exact_mod_cast Nat.pos_of_ne_zero hqh
    simp only [pr, mand, if_neg hh, if_neg hqh, Finset.inter_assoc]
    field_simp

/-- **Def. X 右形** (folio 135): ab/h = b/ah · a/h。 -/
theorem model_def_X_right_i (p q h : M) :
    pr (mand p q) h = pr q (mand p h) * pr p h := by
  have e : mand p q = mand q p := by simp [mand, Finset.inter_comm]
  rw [e]
  exact model_def_X_left_i q p h

/-- **Def. XI** (folio 136): PQ = R ならば P = R/Q (実数の算術)。 -/
theorem model_def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q :=
  fun H => (eq_div_iff hQ).mpr H

/-- **値域 (下)**: 0 ≤ a/h。 -/
theorem model_ax_range_lo_i (p h : M) : 0 ≤ pr p h := by
  unfold pr
  split_ifs
  · exact le_refl 0
  · positivity

/-- **値域 (上)**: a/h ≤ 1。 -/
theorem model_ax_range_hi_i (p h : M) : pr p h ≤ 1 := by
  by_cases hh : h.card = 0
  · simp [pr, hh]
  · have hpos : (0 : ℝ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
    rw [pr_of_card_ne_zero hh, div_le_one hpos]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right

/-- **Def. VIII 双条件読み、但し書き付き** (folio 134、案 A)。 -/
theorem model_def_VIII_i (a b h : M) (hca : Cons (mand a h)) (hcb : Cons (mand b h)) :
    pr (miff a b) h = 1 ↔ (pr b (mand a h) = 1 ∧ pr a (mand b h) = 1) := by
  have hca' : (mand a h).card ≠ 0 := cons_iff_card.mp hca
  have hcb' : (mand b h).card ≠ 0 := cons_iff_card.mp hcb
  have hh : h.card ≠ 0 := card_ne_zero_of_inter hca'
  rw [pr_eq_one_iff hh, pr_eq_one_iff hca', pr_eq_one_iff hcb']
  exact subset_miff_iff a b h

/-- **Def. VIII 印刷どおり** (folio 134、→ のみ、但し書きなし、案 B)。 -/
theorem model_def_VIII_i_src (a b h : M) :
    pr b (mand a h) = 1 → pr a (mand b h) = 1 → pr (miff a b) h = 1 := by
  intro H1 H2
  have hca' := card_ne_zero_of_pr_eq_one H1
  have hcb' := card_ne_zero_of_pr_eq_one H2
  have hh : h.card ≠ 0 := card_ne_zero_of_inter hca'
  rw [pr_eq_one_iff hca'] at H1
  rw [pr_eq_one_iff hcb'] at H2
  rw [pr_eq_one_iff hh]
  exact (subset_miff_iff a b h).mpr ⟨H1, H2⟩

/-- 有限モデルの結合子の組。 -/
noncomputable def finOps : Ops where
  IProp := M
  iand := mand
  ior := mor
  inot := mnot
  iiff := miff
  itrue := mtrue
  PrI := pr
  Cons := Cons

/-- 構文の有限モデル解釈。 -/
def finInterp (env : ℕ → M) : Form → M
  | .var n    => env n
  | .tru      => mtrue
  | .fls      => mnot mtrue
  | .conj f g => mand (finInterp env f) (finInterp env g)
  | .disj f g => mor (finInterp env f) (finInterp env g)
  | .neg f    => mnot (finInterp env f)
  | .iffF f g => miff (finInterp env f) (finInterp env g)

theorem finOps_interp (env : ℕ → M) (f : Form) : finOps.interp env f = finInterp env f := by
  induction f with
  | var n => rfl
  | tru => rfl
  | fls => rfl
  | conj f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl
  | disj f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl
  | neg f ihf => simp only [Ops.interp]; rw [ihf]; rfl
  | iffF f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl

/-- 解釈の帰属 ⟺ 世界での真理値評価。 -/
theorem mem_finInterp (env : ℕ → M) (f : Form) (w : W) :
    w ∈ finInterp env f ↔ evalB (fun n => decide (w ∈ env n)) f = true := by
  induction f with
  | var n => simp [finInterp, evalB]
  | tru => simp [finInterp, evalB, mtrue]
  | fls => simp [finInterp, evalB, mtrue, mnot]
  | conj f g ihf ihg => simp [finInterp, evalB, mand, ihf, ihg]
  | disj f g ihf ihg => simp [finInterp, evalB, mor, ihf, ihg]
  | neg f ihf => simp [finInterp, evalB, mnot, ihf]
  | iffF f g ihf ihg =>
    simp only [finInterp, evalB, miff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
      ihf, ihg]
    cases evalB (fun n => decide (w ∈ env n)) f <;> cases evalB (fun n => decide (w ∈ env n)) g <;>
      simp

/-- **Ax.(iii) 但し書き付き** (folio 135): 整合な h の下で恒真式は確実。 -/
theorem model_ax_iii_taut (f : Form) (env : ℕ → M) (h : M) (hc : Cons h) (ht : Taut f) :
    pr (finInterp env f) h = 1 := by
  rw [pr_eq_one_iff (cons_iff_card.mp hc)]
  intro w _
  rw [mem_finInterp]
  exact ht _

/-- **cons_true**: ⊤ は整合。 -/
theorem model_cons_true : Cons mtrue := Finset.univ_nonempty

/-- **cons_of_pos_src** (Def. VI 印刷の向きの対偶、folio 134): ah 整合ならば a/h ≠ 0。 -/
theorem model_cons_of_pos_src (a h : M) : Cons (mand a h) → pr a h ≠ 0 := by
  intro hca
  have hca' : (mand a h).card ≠ 0 := cons_iff_card.mp hca
  have hh : h.card ≠ 0 := card_ne_zero_of_inter hca'
  rw [pr_of_card_ne_zero hh]
  have hpos : (0 : ℝ) < (a ∩ h).card := by
    exact_mod_cast Nat.pos_of_ne_zero hca'
  have hhpos : (0 : ℝ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
  exact (div_pos hpos hhpos).ne'

/-- **cons_of_pos** (Def. VI の逆向き、(10) folio 140): a/h ≠ 0 かつ h 整合ならば ah 整合。 -/
theorem model_cons_of_pos (a h : M) : pr a h ≠ 0 → Cons h → Cons (mand a h) := by
  intro hne _
  rw [cons_iff_card]
  intro hz
  apply hne
  by_cases hh : h.card = 0
  · exact pr_of_card_zero hh
  · rw [pr_of_card_ne_zero hh]
    simp only [mand] at hz
    simp [hz]

/-- **cons_iff_taut**: 論証的同値な命題は整合性を共有。 -/
theorem model_cons_iff_taut (f g : Form) (env : ℕ → M) (ht : Taut (Form.iffF f g)) :
    Cons (finInterp env f) ↔ Cons (finInterp env g) := by
  have e : finInterp env f = finInterp env g := by
    ext w
    rw [mem_finInterp, mem_finInterp]
    have H := ht (fun n => decide (w ∈ env n))
    simp only [evalB, beq_iff_eq] at H
    rw [H]
  rw [e]

/-- **有限モデルは修復後の公理群をすべて満たす**。 -/
theorem finSys : Sys finOps where
  def_IX_i := model_def_IX_i
  def_X_left_i := model_def_X_left_i
  def_X_right_i := model_def_X_right_i
  def_XI_i := model_def_XI_i
  ax_range_lo_i := model_ax_range_lo_i
  ax_range_hi_i := model_ax_range_hi_i
  def_VIII_i := model_def_VIII_i
  def_VIII_i_src := model_def_VIII_i_src
  ax_iii_taut := fun f env h hc ht => by
    show pr (finOps.interp env f) h = 1
    rw [finOps_interp]
    exact model_ax_iii_taut f env h hc ht
  cons_true := model_cons_true
  cons_of_pos_src := model_cons_of_pos_src
  cons_of_pos := model_cons_of_pos
  cons_iff_taut := fun f g env ht => by
    show Cons (finOps.interp env f) ↔ Cons (finOps.interp env g)
    rw [finOps_interp, finOps_interp]
    exact model_cons_iff_taut f g env ht

/-! ### 旧経路の遮断 -/

/-- **旧経路の結論 pr_self_evidence はモデルで偽**: a := ∅ (矛盾)、h := ⊤ で
a/(a ∧ h) = 0 ≠ 1。修復後の公理群はすべてこのモデルで真なので、任意の a, h で
a/(a ∧ h) = 1 を主張する定理は修復後の公理群から導けない。 -/
theorem model_not_self_evidence : ∃ a h : M, pr a (mand a h) ≠ 1 :=
  ⟨∅, Finset.univ, by simp [pr, mand]⟩

/-- **修復前の Def. VIII (但し書きなし双条件) はモデルで偽**: a = b = ∅、h = ⊤ で
(a≡b)/h = 1 だが b/(ah) = 0。 -/
theorem model_old_def_VIII_fails :
    ∃ a b h : M, ¬ (pr (miff a b) h = 1 ↔ (pr b (mand a h) = 1 ∧ pr a (mand b h) = 1)) := by
  refine ⟨∅, ∅, Finset.univ, ?_⟩
  have h1 : pr (miff ∅ ∅) Finset.univ = 1 := by
    rw [pr_eq_one_iff (by simp)]
    exact (subset_miff_iff ∅ ∅ Finset.univ).mpr ⟨by simp, by simp⟩
  have h2 : pr (∅ : M) (mand ∅ Finset.univ) = 0 := by simp [pr, mand]
  rw [h1, h2]
  norm_num

/-- **修復前の Ax.(iii) (但し書きなし) はモデルで偽**: 矛盾する前提 ∅ の下で
恒真式 ⊤ の値は約定 0。 -/
theorem model_old_ax_iii_taut_fails :
    ∃ (f : Form) (env : ℕ → M) (h : M), Taut f ∧ pr (finInterp env f) h ≠ 1 :=
  ⟨Form.tru, fun _ => ∅, ∅, fun _ => rfl, by simp [pr]⟩

/-- **Lean 内部の非導出性**: 修復後の公理群 (構造 Sys) を満たす任意の構造で
a/(a ∧ h) = 1 が成り立つ、という主張は偽。 -/
theorem not_self_evidence :
    ¬ ∀ (S : Ops), Sys S → ∀ a h : S.IProp, S.PrI a (S.iand a h) = 1 := by
  intro H
  obtain ⟨a, h, hne⟩ := model_not_self_evidence
  exact hne (H finOps finSys a h)

/-- **中間値の実現** (H15): このモデルでは a/h = 1/2 が実現される (a := {0}、h := ⊤)。
確率関係が {0, 1} に退化しない。 -/
theorem model_intermediate_value : pr ({0} : M) Finset.univ = 1 / 2 := by
  rw [pr_of_card_ne_zero (by simp)]
  simp

end KeynesI_model

/-! ## 監査クエリ -/

#check @KeynesI_model.finSys
#check @KeynesI_model.not_self_evidence
#check @KeynesI_model.model_not_self_evidence
#check @KeynesI_model.model_intermediate_value

-- 各公理の成立 (axiom 宣言を含まないこと = propext, Classical.choice, Quot.sound のみ)
#print axioms KeynesI_model.model_def_IX_i
#print axioms KeynesI_model.model_def_X_left_i
#print axioms KeynesI_model.model_def_X_right_i
#print axioms KeynesI_model.model_def_XI_i
#print axioms KeynesI_model.model_ax_range_lo_i
#print axioms KeynesI_model.model_ax_range_hi_i
#print axioms KeynesI_model.model_def_VIII_i
#print axioms KeynesI_model.model_def_VIII_i_src
#print axioms KeynesI_model.model_ax_iii_taut
#print axioms KeynesI_model.model_cons_true
#print axioms KeynesI_model.model_cons_of_pos_src
#print axioms KeynesI_model.model_cons_of_pos
#print axioms KeynesI_model.model_cons_iff_taut
#print axioms KeynesI_model.finSys
-- 旧経路の遮断
#print axioms KeynesI_model.model_not_self_evidence
#print axioms KeynesI_model.model_old_def_VIII_fails
#print axioms KeynesI_model.model_old_ax_iii_taut_fails
#print axioms KeynesI_model.not_self_evidence
#print axioms KeynesI_model.model_intermediate_value
