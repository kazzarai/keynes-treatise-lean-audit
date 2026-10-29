/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 12b
#
# 新井一成・Claude共著、2026年10月29日 (B31)
# **不定性の定理: 同じ証拠 h の下で a/h の値が異なる二つの模型**
#
# ## 目的
#   phase6c の公理群 (KeynesI、Cons 付き、2026-10-20 修復版) は、整合な前提 h と
#   原子命題 a に対して確率関係 a/h の値を一つに定めない。これを、全公理を満たす
#   有限模型を二つ作り、同じ a・同じ h で値が異なることを示して定理にする
#   (`underdetermined`)。方法は phase6c_model と同じ: axiom 宣言そのものは模型に
#   できないので、公理の文を構造 `Sys` に写し、模型がそれを満たすことを証明する。
#
# ## 模型
#   世界集合 W := Fin 3、命題 M := Finset W。結合子は phase6c_model と同じ
#   (∩, ∪, 補集合, (p ∩ q) ∪ (pᶜ ∩ qᶜ), univ)、Cons h := h.Nonempty。
#   確率関係は正の重み wt : W → ℝ (各世界で 0 < wt w) による条件付きの重みの比
#     prw wt p h := if h = ∅ then 0 else μ(p ∩ h) / μ(h)、μ(p) := Σ_{w ∈ p} wt w。
#   h = ∅ のときの 0 は phase6c_model と同じ約定 (公理 (i) の但し書きの外側の値)。
#   §2 で任意の正の重みについて 13 本の公理文を証明し (`wSys`)、§3 で
#     M₁: 重み (1, 1, 1)、M₂: 重み (4, 1, 1)
#   に当てはめる。a := {0} (= 原子命題 var 0 の解釈)、h := ⊤ (= univ) で
#     M₁ では a/h = 1/3、M₂ では a/h = 4/6 = 2/3。
#   二つの模型は担体・結合子・Cons・構文の解釈まで同一で (`same_frame`)、違うのは
#   確率関係 PrI だけである。
#
# ## 原典 (唯一の基準) との対応
#   公理 (i) (第12章 §5, folio 135):「h が矛盾する連言でないとき、a と h の間に
#   確率関係がただ一つ存在する」。この「ただ一つ」は一つの模型の中での一意性
#   (PrI が関数であること) であり、どの値かは公理 (ii)(iii) と定義 VI–X が定めない。
#   第4章 §2 (folio 42) の無差別原理は「選択肢の一つを他より述べる既知の理由が
#   なければ、その知識に相対的に各選択肢の主張は等しい確率をもつ」とする。M₁ の
#   等しい重みは三つの世界にこの原理を当てた場合にあたり、M₂ は当てない場合で、
#   どちらも公理群を満たす。h (ここでは ⊤) が無差別原理の分割を与えないとき、
#   a/h の値は公理から定まらない。
#   第3章 §20 (folio 39) の図との関係: 本ファイルの値はすべて数値の道筋 OAI の上に
#   あり、値を数に限っても公理群は OAI 上の位置を選ばない (B30 の道筋の図とは
#   別の論点)。
#   対照: 命題を真偽で同一視した外延担体 (Prop → Prop → ℝ) では、ax_iii_true と
#   Def. IX だけで Pr p h が p の真理値 (0 か 1) に固定され、同じ a, h での値は
#   すべての模型で一致する (phase7i_model `ext_forced`; 証明は再掲しない)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase12b_underdetermination.lean
-/

import Mathlib

namespace KeynesI_underdet

/-! ## §1 構文と公理群 (phase6c_model.lean と同一の複製) -/

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

/-- **修復後の公理群** (phase6c.lean の axiom の文をそのまま場に写したもの、13 本)。 -/
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

/-! ## §2 重み付き有限模型 (任意の正の重み) -/

/-- 世界集合。 -/
abbrev W := Fin 3
/-- 命題 = 世界の集合。 -/
abbrev M := Finset W

def mand (p q : M) : M := p ∩ q
def mor  (p q : M) : M := p ∪ q
def mnot (p : M) : M := pᶜ
def miff (p q : M) : M := (p ∩ q) ∪ (pᶜ ∩ qᶜ)
def mtrue : M := Finset.univ

/-- 命題 p に含まれる世界の重みの和。 -/
def mu (wt : W → ℝ) (p : M) : ℝ := ∑ w ∈ p, wt w

/-- 条件付きの重みの比。h = ∅ のときは 0 と約定 (phase6c_model と同じ)。 -/
noncomputable def prw (wt : W → ℝ) (p h : M) : ℝ :=
  if h = ∅ then 0 else mu wt (p ∩ h) / mu wt h

/-- 整合性 = 充足可能性。 -/
def Cons (h : M) : Prop := h.Nonempty

section Weighted

variable {wt : W → ℝ} (hw : ∀ w, 0 < wt w)

/-! ### 基本補題 -/

include hw in
theorem mu_nonneg (p : M) : 0 ≤ mu wt p :=
  Finset.sum_nonneg (fun w _ => (hw w).le)

include hw in
theorem mu_pos {p : M} (hp : p.Nonempty) : 0 < mu wt p :=
  Finset.sum_pos (fun w _ => hw w) hp

theorem prw_of_empty (p : M) : prw wt p ∅ = 0 := by
  simp [prw]

theorem prw_of_ne {p h : M} (hh : h ≠ ∅) : prw wt p h = mu wt (p ∩ h) / mu wt h := by
  rw [prw, if_neg hh]

theorem ne_empty_of_cons {h : M} (hc : Cons h) : h ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp hc

theorem ne_empty_of_inter {a h : M} (hc : a ∩ h ≠ ∅) : h ≠ ∅ := by
  rintro rfl
  exact hc (Finset.inter_empty a)

include hw in
/-- 前提が整合なとき、確実 ⟺ 前提が結論を含む。 -/
theorem prw_eq_one_iff {p h : M} (hh : h ≠ ∅) : prw wt p h = 1 ↔ h ⊆ p := by
  have hpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [prw_of_ne hh, div_eq_one_iff_eq hpos.ne']
  constructor
  · intro H
    by_contra hns
    obtain ⟨w, hwh, hwp⟩ := Finset.not_subset.mp hns
    have e1 : p ∩ h = h.filter (· ∈ p) := by
      ext x; simp [and_comm]
    have hs := Finset.sum_filter_add_sum_filter_not h (· ∈ p) wt
    have hpos2 : 0 < mu wt (h.filter (· ∉ p)) :=
      mu_pos hw ⟨w, by simp [hwh, hwp]⟩
    rw [e1] at H
    unfold mu at H hpos2
    linarith
  · intro H
    rw [Finset.inter_eq_right.mpr H]

/-- 確実ならば h ≠ ∅ (約定 0 ≠ 1)。 -/
theorem ne_empty_of_prw_eq_one {p h : M} (H : prw wt p h = 1) : h ≠ ∅ := by
  rintro rfl
  rw [prw_of_empty] at H
  exact zero_ne_one H

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
    prw wt (mand p (mnot q)) h + prw wt (mand p q) h = prw wt p h := by
  by_cases hh : h = ∅
  · simp [prw, hh]
  · rw [prw_of_ne hh, prw_of_ne hh, prw_of_ne hh, ← add_div]
    congr 1
    have e1 : mand p q ∩ h = (p ∩ h).filter (· ∈ q) := by
      ext w; simp [mand]; tauto
    have e2 : mand p (mnot q) ∩ h = (p ∩ h).filter (· ∉ q) := by
      ext w; simp [mand, mnot]; tauto
    rw [e1, e2, add_comm]
    exact Finset.sum_filter_add_sum_filter_not _ _ _

include hw in
/-- **Def. X 左形** (folio 135): ab/h = a/bh · b/h。 -/
theorem model_def_X_left_i (p q h : M) :
    prw wt (mand p q) h = prw wt p (mand q h) * prw wt q h := by
  by_cases hh : h = ∅
  · subst hh; simp [prw, mand]
  by_cases hqh : mand q h = ∅
  · have hz : mand p q ∩ h = ∅ := by
      have hsub : p ∩ (q ∩ h) ⊆ q ∩ h := Finset.inter_subset_right
      simp only [mand] at hqh ⊢
      rw [Finset.inter_assoc]
      exact Finset.subset_empty.mp (hsub.trans hqh.subset)
    rw [hqh, prw_of_empty, zero_mul, prw_of_ne hh, hz]
    simp [mu]
  · have hqpos : 0 < mu wt (q ∩ h) :=
      mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hqh)
    have hpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
    rw [prw_of_ne hh, prw_of_ne hqh, prw_of_ne hh]
    simp only [mand, Finset.inter_assoc]
    field_simp

include hw in
/-- **Def. X 右形** (folio 135): ab/h = b/ah · a/h。 -/
theorem model_def_X_right_i (p q h : M) :
    prw wt (mand p q) h = prw wt q (mand p h) * prw wt p h := by
  have e : mand p q = mand q p := by simp [mand, Finset.inter_comm]
  rw [e]
  exact model_def_X_left_i hw q p h

/-- **Def. XI** (folio 136): PQ = R ならば P = R/Q (実数の算術)。 -/
theorem model_def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q :=
  fun H => (eq_div_iff hQ).mpr H

include hw in
/-- **値域 (下)**: 0 ≤ a/h。 -/
theorem model_ax_range_lo_i (p h : M) : 0 ≤ prw wt p h := by
  unfold prw
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (mu_nonneg hw _) (mu_nonneg hw _)

include hw in
/-- **値域 (上)**: a/h ≤ 1。 -/
theorem model_ax_range_hi_i (p h : M) : prw wt p h ≤ 1 := by
  by_cases hh : h = ∅
  · simp [prw, hh]
  · have hpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
    rw [prw_of_ne hh, div_le_one hpos]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun w _ _ => (hw w).le)

include hw in
/-- **Def. VIII 双条件読み、但し書き付き** (folio 134、案 A)。 -/
theorem model_def_VIII_i (a b h : M) (hca : Cons (mand a h)) (hcb : Cons (mand b h)) :
    prw wt (miff a b) h = 1 ↔ (prw wt b (mand a h) = 1 ∧ prw wt a (mand b h) = 1) := by
  have hca' : mand a h ≠ ∅ := ne_empty_of_cons hca
  have hcb' : mand b h ≠ ∅ := ne_empty_of_cons hcb
  have hh : h ≠ ∅ := ne_empty_of_inter hca'
  rw [prw_eq_one_iff hw hh, prw_eq_one_iff hw hca', prw_eq_one_iff hw hcb']
  exact subset_miff_iff a b h

include hw in
/-- **Def. VIII 印刷どおり** (folio 134、→ のみ、但し書きなし、案 B)。 -/
theorem model_def_VIII_i_src (a b h : M) :
    prw wt b (mand a h) = 1 → prw wt a (mand b h) = 1 → prw wt (miff a b) h = 1 := by
  intro H1 H2
  have hca' := ne_empty_of_prw_eq_one H1
  have hcb' := ne_empty_of_prw_eq_one H2
  have hh : h ≠ ∅ := ne_empty_of_inter hca'
  rw [prw_eq_one_iff hw hca'] at H1
  rw [prw_eq_one_iff hw hcb'] at H2
  rw [prw_eq_one_iff hw hh]
  exact (subset_miff_iff a b h).mpr ⟨H1, H2⟩

end Weighted

/-- 重み wt の模型の結合子の組。担体・結合子・Cons は wt によらない。 -/
noncomputable def wOps (wt : W → ℝ) : Ops where
  IProp := M
  iand := mand
  ior := mor
  inot := mnot
  iiff := miff
  itrue := mtrue
  PrI := prw wt
  Cons := Cons

/-- 構文の有限模型解釈 (wt によらない)。 -/
def finInterp (env : ℕ → M) : Form → M
  | .var n    => env n
  | .tru      => mtrue
  | .fls      => mnot mtrue
  | .conj f g => mand (finInterp env f) (finInterp env g)
  | .disj f g => mor (finInterp env f) (finInterp env g)
  | .neg f    => mnot (finInterp env f)
  | .iffF f g => miff (finInterp env f) (finInterp env g)

theorem wOps_interp (wt : W → ℝ) (env : ℕ → M) (f : Form) :
    (wOps wt).interp env f = finInterp env f := by
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

section Weighted2

variable {wt : W → ℝ} (hw : ∀ w, 0 < wt w)

include hw in
/-- **Ax.(iii) 但し書き付き** (folio 135): 整合な h の下で恒真式は確実。 -/
theorem model_ax_iii_taut (f : Form) (env : ℕ → M) (h : M) (hc : Cons h) (ht : Taut f) :
    prw wt (finInterp env f) h = 1 := by
  rw [prw_eq_one_iff hw (ne_empty_of_cons hc)]
  intro w _
  rw [mem_finInterp]
  exact ht _

/-- **cons_true**: ⊤ は整合。 -/
theorem model_cons_true : Cons mtrue := Finset.univ_nonempty

include hw in
/-- **cons_of_pos_src** (Def. VI 印刷の向きの対偶、folio 134): ah 整合ならば a/h ≠ 0。 -/
theorem model_cons_of_pos_src (a h : M) : Cons (mand a h) → prw wt a h ≠ 0 := by
  intro hca
  have hh : h ≠ ∅ := ne_empty_of_inter (ne_empty_of_cons hca)
  have hhpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [prw_of_ne hh]
  exact (div_pos (mu_pos hw hca) hhpos).ne'

/-- **cons_of_pos** (Def. VI の逆向き、(10) folio 140): a/h ≠ 0 かつ h 整合ならば ah 整合。 -/
theorem model_cons_of_pos (a h : M) : prw wt a h ≠ 0 → Cons h → Cons (mand a h) := by
  intro hne hc
  by_contra hz
  apply hne
  rw [Cons, Finset.not_nonempty_iff_eq_empty] at hz
  rw [prw_of_ne (ne_empty_of_cons hc)]
  simp only [mand] at hz
  simp [hz, mu]

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

include hw in
/-- **正の重みの模型は修復後の公理群 13 本をすべて満たす**。 -/
theorem wSys : Sys (wOps wt) where
  def_IX_i := model_def_IX_i
  def_X_left_i := model_def_X_left_i hw
  def_X_right_i := model_def_X_right_i hw
  def_XI_i := model_def_XI_i
  ax_range_lo_i := model_ax_range_lo_i hw
  ax_range_hi_i := model_ax_range_hi_i hw
  def_VIII_i := model_def_VIII_i hw
  def_VIII_i_src := model_def_VIII_i_src hw
  ax_iii_taut := fun f env h hc ht => by
    show prw wt ((wOps wt).interp env f) h = 1
    rw [wOps_interp]
    exact model_ax_iii_taut hw f env h hc ht
  cons_true := model_cons_true
  cons_of_pos_src := model_cons_of_pos_src hw
  cons_of_pos := model_cons_of_pos
  cons_iff_taut := fun f g env ht => by
    show Cons ((wOps wt).interp env f) ↔ Cons ((wOps wt).interp env g)
    rw [wOps_interp, wOps_interp]
    exact model_cons_iff_taut f g env ht

include hw in
/-- **Ax.(ii) 同値の公理** (folio 135、phase6c の 13 本には含まれない; 参考):
(a≡b)/h = 1 ならば x/ah = x/bh。 -/
theorem model_ax_ii (a b x h : M) :
    prw wt (miff a b) h = 1 → prw wt x (mand a h) = prw wt x (mand b h) := by
  intro H
  have hh := ne_empty_of_prw_eq_one H
  rw [prw_eq_one_iff hw hh, subset_miff_iff] at H
  have e : mand a h = mand b h := by
    simp only [mand]
    exact Finset.Subset.antisymm
      (Finset.subset_inter H.1 Finset.inter_subset_right)
      (Finset.subset_inter H.2 Finset.inter_subset_right)
  rw [e]

end Weighted2

/-! ## §3 二つの模型 M₁・M₂ と不定性の定理 -/

/-- M₁ の重み (1, 1, 1): 三つの世界に等しい重み。 -/
def wt₁ : W → ℝ := fun _ => 1
/-- M₂ の重み (4, 1, 1)。 -/
def wt₂ : W → ℝ := fun w => if w = 0 then 4 else 1

theorem wt₁_pos : ∀ w, 0 < wt₁ w := fun _ => by norm_num [wt₁]
theorem wt₂_pos : ∀ w, 0 < wt₂ w := fun w => by unfold wt₂; split_ifs <;> norm_num

/-- 原子命題の割り当て: var n はすべて世界 0 だけで真。 -/
def env₀ : ℕ → M := fun _ => {0}
/-- 結論 a := var 0 の解釈 = {0}。 -/
def a₀ : M := {0}
/-- 前提 h := ⊤ の解釈 = univ。 -/
def h₀ : M := Finset.univ

theorem a₀_interp (wt : W → ℝ) : (wOps wt).interp env₀ (Form.var 0) = a₀ := rfl
theorem h₀_interp (wt : W → ℝ) : (wOps wt).interp env₀ Form.tru = h₀ := rfl

/-- h₀ = ⊤ は整合 (公理 (i) の但し書きを満たす)。 -/
theorem cons_h₀ : Cons h₀ := Finset.univ_nonempty

/-- **M₁ と M₂ は担体・結合子・Cons・構文の解釈が同一** (違いは PrI だけ)。 -/
theorem same_frame (v₁ v₂ : W → ℝ) :
    (wOps v₁).IProp = (wOps v₂).IProp ∧
    (wOps v₁).iand = (wOps v₂).iand ∧ (wOps v₁).ior = (wOps v₂).ior ∧
    (wOps v₁).inot = (wOps v₂).inot ∧ (wOps v₁).iiff = (wOps v₂).iiff ∧
    (wOps v₁).itrue = (wOps v₂).itrue ∧ (wOps v₁).Cons = (wOps v₂).Cons ∧
    (∀ (env : ℕ → M) (f : Form), (wOps v₁).interp env f = (wOps v₂).interp env f) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun env f => by rw [wOps_interp, wOps_interp]⟩

/-- **M₁ では a/h = 1/3**。 -/
theorem M₁_value : (wOps wt₁).PrI a₀ h₀ = 1 / 3 := by
  show prw wt₁ a₀ h₀ = 1 / 3
  rw [prw_of_ne (ne_empty_of_cons cons_h₀)]
  simp [mu, wt₁, a₀, h₀]

/-- **M₂ では a/h = 2/3**。 -/
theorem M₂_value : (wOps wt₂).PrI a₀ h₀ = 2 / 3 := by
  show prw wt₂ a₀ h₀ = 2 / 3
  rw [prw_of_ne (ne_empty_of_cons cons_h₀)]
  simp [mu, wt₂, a₀, h₀, Fin.sum_univ_three]
  norm_num

/-- **不定性の定理**: phase6c の公理群 13 本を満たす模型 M₁・M₂ があり、同じ原子
命題 a (= var 0) と同じ整合な前提 h (= ⊤) について PrI₁ a h ≠ PrI₂ a h。
二つの模型は PrI 以外すべて同一 (`same_frame`)。無差別原理 (第4章 §2, folio 42)
の分割を h が与えないとき、a/h の値は公理から定まらない。 -/
theorem underdetermined :
    ∃ v₁ v₂ : W → ℝ, Sys (wOps v₁) ∧ Sys (wOps v₂) ∧
      (wOps v₁).Cons ((wOps v₁).interp env₀ Form.tru) ∧
      (wOps v₁).PrI ((wOps v₁).interp env₀ (Form.var 0)) ((wOps v₁).interp env₀ Form.tru) ≠
      (wOps v₂).PrI ((wOps v₂).interp env₀ (Form.var 0)) ((wOps v₂).interp env₀ Form.tru) := by
  refine ⟨wt₁, wt₂, wSys wt₁_pos, wSys wt₂_pos, cons_h₀, ?_⟩
  rw [a₀_interp, h₀_interp, a₀_interp, h₀_interp, M₁_value, M₂_value]
  norm_num

/-- 系 (Lean 内部の言明): 公理群を満たす全ての正の重みの模型で a/h が同じ値 c を
とる、という c は存在しない。 -/
theorem not_determined :
    ¬ ∃ c : ℝ, ∀ v : W → ℝ, (∀ w, 0 < v w) → (wOps v).PrI a₀ h₀ = c := by
  rintro ⟨c, H⟩
  have h1 := H wt₁ wt₁_pos
  have h2 := H wt₂ wt₂_pos
  rw [M₁_value] at h1
  rw [M₂_value] at h2
  linarith

/-- 補足: 開区間 (0, 1) のどの値 c も、ある正の重み (c, (1-c)/2, (1-c)/2) の模型で
a/h の値として実現される (各模型は `wSys` により公理群を満たす)。 -/
theorem every_interior_value (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ v : W → ℝ, (∀ w, 0 < v w) ∧ (wOps v).PrI a₀ h₀ = c := by
  refine ⟨fun w => if w = 0 then c else (1 - c) / 2, ?_, ?_⟩
  · intro w
    dsimp only
    split_ifs
    · exact hc0
    · linarith
  · show prw _ a₀ h₀ = c
    rw [prw_of_ne (ne_empty_of_cons cons_h₀)]
    simp [mu, a₀, h₀, Fin.sum_univ_three]
    have e : c + (1 - c) / 2 + (1 - c) / 2 = 1 := by ring
    rw [e, div_one]

/-- 重みの正値性は落とせない: 重み (1, 0, 0) では cons_of_pos_src が偽
(a := {1}, h := ⊤ は ah 整合だが a/h = 0)。 -/
theorem zero_weight_breaks :
    ¬ ∀ a h : M, Cons (mand a h) → prw (fun w : W => if w = 0 then 1 else 0) a h ≠ 0 := by
  intro H
  apply H {1} Finset.univ ⟨1, by simp [mand]⟩
  rw [prw_of_ne Finset.univ_nonempty.ne_empty]
  simp [mu]

end KeynesI_underdet

/-! ## 監査クエリ -/

#check @KeynesI_underdet.underdetermined
#check @KeynesI_underdet.wSys

-- 各公理の成立 (任意の正の重み)
#print axioms KeynesI_underdet.model_def_IX_i
#print axioms KeynesI_underdet.model_def_X_left_i
#print axioms KeynesI_underdet.model_def_X_right_i
#print axioms KeynesI_underdet.model_def_XI_i
#print axioms KeynesI_underdet.model_ax_range_lo_i
#print axioms KeynesI_underdet.model_ax_range_hi_i
#print axioms KeynesI_underdet.model_def_VIII_i
#print axioms KeynesI_underdet.model_def_VIII_i_src
#print axioms KeynesI_underdet.model_ax_iii_taut
#print axioms KeynesI_underdet.model_cons_true
#print axioms KeynesI_underdet.model_cons_of_pos_src
#print axioms KeynesI_underdet.model_cons_of_pos
#print axioms KeynesI_underdet.model_cons_iff_taut
#print axioms KeynesI_underdet.wSys
#print axioms KeynesI_underdet.model_ax_ii
-- 二つの模型と不定性
#print axioms KeynesI_underdet.same_frame
#print axioms KeynesI_underdet.M₁_value
#print axioms KeynesI_underdet.M₂_value
#print axioms KeynesI_underdet.underdetermined
#print axioms KeynesI_underdet.not_determined
#print axioms KeynesI_underdet.every_interior_value
#print axioms KeynesI_underdet.zero_weight_breaks
