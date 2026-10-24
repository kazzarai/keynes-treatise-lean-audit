/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 6c 但し書きの必要性
#
# 新井一成・Claude共著、2026年10月23日 (B11)
# **公理 (i) の但し書き (Cons) を一切置かず、定義 VIII を印刷どおり → のみで読んだ
#   公理群 S₀ の無矛盾性 (有限モデル) と、但し書きが要る正確な場所**
#
# ## 結論 (一段落)
#   (a) 但し書きなし・印刷方向 VIII の公理群 S₀ = {def_IX_i, def_X_left_i,
#       def_X_right_i, ax_range_lo_i, ax_range_hi_i, def_VIII_i_src (→ のみ),
#       ax_iii_taut (Cons なし)} は**無矛盾**である。世界集合 W = Fin 2 上の有限
#       モデルで、整合な前提 (h ≠ ∅) には条件付き相対頻度、矛盾する前提 (h = ∅)
#       には固定した一世界 w₀ での真理値 (p ↦ [w₀ ∈ p]) を割り当てると、S₀ の
#       全公理の文が定理として成り立つ (finSys₀、th_S0_consistent)。公理 (i)
#       (folio 135) は整合な前提について確率関係の存在と一意性を主張し、矛盾する
#       前提については沈黙する。空前提の値はその沈黙の部分を埋めるモデル側の約定である。
#   (b) 中間値は**あり**: 同じモデルで a/h = 1/2 が実現される
#       (model_intermediate_value、th_S0_not_two_valued)。S₀ は二値に退化しない。
#       S₀ が p/h ∈ {0, 1} を強制するのは p ∧ h = h を満たす前提に限る
#       (two_valued_of_absorbing: (pp ≡ p)/h = 1 と Def. X 左形から p/h = p/h · p/h)。
#       このモデルでは ∅ がそれにあたる (任意の p で p ∧ ∅ = ∅)。S₀ には整合性の
#       述語がないので、矛盾する前提一般について S₀ が値を強制するとは言わない。
#   (c) 四つの読み方の決着 (定理名付き): 真偽同一視 (Pr : Prop → Prop → ℝ) は二値に
#       強制される (phase7i_model の ext_forced)／内包・定義 VIII 双条件・但し書きなし
#       は矛盾 (phase6c_inconsistency の th_6c_old_inconsistent)／内包・定義 VIII
#       印刷方向・但し書きなしは無矛盾で中間値あり (本ファイルの th_S0_consistent、
#       model_intermediate_value)／内包・双条件・但し書き付き (修復版) は無矛盾で
#       中間値あり (phase6c_model の finSys、model_intermediate_value)。残る一組、
#       内包・双条件・但し書きを公理 (iii) 側にだけ置いた公理群 S_B は矛盾する
#       (th_VIII_bicond_iii_cons_inconsistent: Def. IX・双条件 VIII・Cons 付き (iii)・
#       cons_true の 4 本から False、VIII_bicond_iii_cons_core)。したがって但し書きは
#       定義 VIII 側に置く必要がある。但し書きが要るのは定義 VIII の逆向き
#       (← : (a≡b)/h = 1 ⟹ b/ah = 1) であり、逆向きは S₀ から導けない
#       (not_def_VIII_back)。公理 (iii) 側の但し書きは無矛盾性に不要である (本モデルは
#       Cons 付き修復版 (phase6c) の全公理と Cons なしの ax_iii_taut とを同時に満たす:
#       th_union_consistent)。旧経路の結論 (任意の a, h で a/(a∧h) = 1) も S₀ から
#       導けない (not_self_evidence₀)。
#
# ## 原典 (唯一の基準、1921 Macmillan 初版)
#   folio 134 (第12章 §4 Def. VI, VIII):
#   「VI. If a/h = 0, the conjunction ah is inconsistent. Def.」
#   「VIII. If b/ah = 1 and a/bh = 1, (a≡b)/h = 1. Def.
#    This may be regarded as the definition of Equivalence. Thus we see that
#    equivalence is relative to a premiss h. a is equivalent to b, given h,
#    if b follows from ah, and a from bh.」
#   folio 135 (第12章 §5 公理 (i), (iii)):
#   「We shall assume that there is included in every premiss with which we are
#    concerned the formal implications which allow us to assert the following
#    axioms:
#    (i.) Provided that a and h are propositions or conjunctions of propositions
#    or disjunctions of propositions, and that h is not an inconsistent
#    conjunction, there exists one and only one relation of probability P between
#    a as conclusion and h as premiss. Thus any conclusion a bears to any
#    consistent premiss h one and only one relation of probability.」
#   「(iii.) (\overline{a+b} ≡ \bar{a}\bar{b})/h = 1, (aa ≡ a)/h = 1,
#    (\bar{\bar{a}} ≡ a)/h = 1, (ab + \bar{a}b ≡ b)/h = 1.
#    If a/h = 1, ah ≡ h.」
#   folio 135 (第12章 §6 Def. IX, X):
#   「IX. ab/h + a\bar{b}/h = a/h. Def.
#    X. ab/h = a/bh . b/h = b/ah . a/h. Def.」
#
# ## 本ファイルの構成
#   1. 構文 Form / evalB / Taut (phase6c と同一の複製)。
#   2. 結合子の組 Ops₀ (Cons なし) と、S₀ の公理の文を場にした構造 Sys₀。
#      axiom 宣言はしない (モデル化のため命題として扱う)。
#   3. S₀ の内部定理: 但し書きなしで補完律 (1)、Th.(12)、代入原理が任意の前提で
#      成り立つこと、p ∧ h = h を満たす前提の下での二値性 (two_valued_of_absorbing)。
#   4. 有限モデル (W = Fin 2、空前提は w₀ = 0 での真理値) と各公理の成立、finSys₀。
#   5. 非導出性 (健全性による): 旧経路の結論、定義 VIII の逆向き、二値退化。
#   6. Cons 付き修復版 (phase6c) の公理の文 SysC を同じモデルが満たすこと
#      (S₀ ∪ 修復版の無矛盾性)。
#   7. 残る一組 S_B (定義 VIII 双条件・但し書きなし ＋ Cons 付き (iii)) から False
#      (th_VIII_bicond_iii_cons_inconsistent)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase6c_necessity.lean
-/

import Mathlib

namespace KeynesI_necessity

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

/-! ## S₀: 但し書きなし・印刷方向 VIII の公理群 (公理の文を場にした構造) -/

/-- 結合子・確率関係の組 (Cons なし)。 -/
structure Ops₀ where
  IProp : Type
  iand : IProp → IProp → IProp
  ior  : IProp → IProp → IProp
  inot : IProp → IProp
  iiff : IProp → IProp → IProp
  itrue : IProp
  PrI : IProp → IProp → ℝ

/-- 構文の解釈 (phase6c.lean の interp と同じ形)。 -/
def Ops₀.interp (S : Ops₀) (env : ℕ → S.IProp) : Form → S.IProp
  | .var n    => env n
  | .tru      => S.itrue
  | .fls      => S.inot S.itrue
  | .conj f g => S.iand (S.interp env f) (S.interp env g)
  | .disj f g => S.ior (S.interp env f) (S.interp env g)
  | .neg f    => S.inot (S.interp env f)
  | .iffF f g => S.iiff (S.interp env f) (S.interp env g)

/-- **S₀** (依頼 B11 の公理群)。def_VIII_i_src は印刷どおり → のみ (folio 134)、
ax_iii_taut は公理 (i) の但し書きなし (任意の前提 h、矛盾する連言を含む)。
def_XI_i (PQ = R ⟹ P = R/Q) は実数の算術で、Ops₀ に依らないので省く。 -/
structure Sys₀ (S : Ops₀) : Prop where
  def_IX_i : ∀ p q h, S.PrI (S.iand p (S.inot q)) h + S.PrI (S.iand p q) h = S.PrI p h
  def_X_left_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI p (S.iand q h) * S.PrI q h
  def_X_right_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI q (S.iand p h) * S.PrI p h
  ax_range_lo_i : ∀ p h, 0 ≤ S.PrI p h
  ax_range_hi_i : ∀ p h, S.PrI p h ≤ 1
  def_VIII_i_src : ∀ a b h,
    S.PrI b (S.iand a h) = 1 → S.PrI a (S.iand b h) = 1 → S.PrI (S.iiff a b) h = 1
  ax_iii_taut : ∀ (f : Form) (env : ℕ → S.IProp) (h : S.IProp),
    Taut f → S.PrI (S.interp env f) h = 1

/-! ## S₀ の内部定理 (但し書きなしで任意の前提に成り立つもの) -/

section Internal
variable {S : Ops₀} (hS : Sys₀ S)
include hS

/-- ⊤ は任意の前提 (矛盾する連言を含む) の下で確実。 -/
theorem itrue_certain₀ (h : S.IProp) : S.PrI S.itrue h = 1 :=
  hS.ax_iii_taut Form.tru (fun _ => S.itrue) h (fun _ => rfl)

/-- (⊤ ∧ a)/h = a/h、任意の前提。Def. X 左形と ⊤/(ah) = 1 (但し書きなし) から。 -/
theorem true_conj₀ (a h : S.IProp) : S.PrI (S.iand S.itrue a) h = S.PrI a h := by
  have hr := hS.def_X_left_i S.itrue a h
  rw [itrue_certain₀ hS (S.iand a h), one_mul] at hr
  exact hr

/-- **補完律 (1) の但し書きなし版**: a/h + \bar{a}/h = 1、任意の前提。
S₀ は矛盾する前提の下でも加法的な値を要求する。 -/
theorem compl₀ (a h : S.IProp) : S.PrI a h + S.PrI (S.inot a) h = 1 := by
  have step := hS.def_IX_i S.itrue a h
  rw [true_conj₀ hS (S.inot a) h, true_conj₀ hS a h, itrue_certain₀ hS h] at step
  linarith

/-- 矛盾の確率は 0、任意の前提。 -/
theorem taut_neg_zero₀ (f : Form) (env : ℕ → S.IProp) (h : S.IProp)
    (ht : Taut (Form.neg f)) : S.PrI (S.interp env f) h = 0 := by
  have h1 : S.PrI (S.inot (S.interp env f)) h = 1 := hS.ax_iii_taut (Form.neg f) env h ht
  have h2 := compl₀ hS (S.interp env f) h
  linarith

/-- E/h = 1 ならば (x ∧ \bar{E})/h = 0、任意の前提。 -/
theorem conj_neg_cert_zero₀ (x E h : S.IProp) (hE : S.PrI E h = 1) :
    S.PrI (S.iand x (S.inot E)) h = 0 := by
  have h1 := compl₀ hS E h
  have hnE : S.PrI (S.inot E) h = 0 := by linarith
  rw [hS.def_X_left_i x (S.inot E) h, hnE, mul_zero]

/-- **Th.(12) の但し書きなし版** (folio 141: If (a≡b)/h = 1, a/h = b/h)。
phase6c の th_12_i_short と同じ経路 (Def. IX・Def. X の 4 式)。定義 VIII は
どちらの向きも使わない。 -/
theorem th_12₀ (a b h : S.IProp) (hcert : S.PrI (S.iiff a b) h = 1) :
    S.PrI a h = S.PrI b h := by
  have hba : S.PrI (S.iand b (S.inot a)) h = 0 := by
    have s := hS.def_IX_i (S.iand b (S.inot a)) (S.iiff a b) h
    have z1 := conj_neg_cert_zero₀ hS (S.iand b (S.inot a)) (S.iiff a b) h hcert
    have z2 : S.PrI (S.iand (S.iand b (S.inot a)) (S.iiff a b)) h = 0 :=
      taut_neg_zero₀ hS
        (Form.conj (Form.conj (Form.var 1) (Form.neg (Form.var 0)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  have hab : S.PrI (S.iand a (S.inot b)) h = 0 := by
    have s := hS.def_IX_i (S.iand a (S.inot b)) (S.iiff a b) h
    have z1 := conj_neg_cert_zero₀ hS (S.iand a (S.inot b)) (S.iiff a b) h hcert
    have z2 : S.PrI (S.iand (S.iand a (S.inot b)) (S.iiff a b)) h = 0 :=
      taut_neg_zero₀ hS
        (Form.conj (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  have e1 := hS.def_IX_i a b h
  have e2 := hS.def_IX_i b a h
  have e3 := hS.def_X_left_i a b h
  have e4 := hS.def_X_right_i b a h
  linarith

/-- 代入原理の但し書きなし版。 -/
theorem subst_taut₀ (f g : Form) (env : ℕ → S.IProp) (h : S.IProp)
    (ht : Taut (Form.iffF f g)) :
    S.PrI (S.interp env f) h = S.PrI (S.interp env g) h :=
  th_12₀ hS _ _ h (hS.ax_iii_taut (Form.iffF f g) env h ht)

/-- **p ∧ h = h を満たす前提の下では二値**: p ∧ h = h ならば p/h ∈ {0, 1}。
(pp ≡ p)/h = 1 (公理 (iii) の第 2 式) と Th.(12) で pp/h = p/h、Def. X 左形で
pp/h = p/(ph) · p/h = p/h · p/h。主張はこの形の前提に限る。有限モデルでは ∅ が
それにあたる (任意の p で p ∧ ∅ = ∅)。S₀ には整合性の述語がないので、矛盾する前提
一般について S₀ が値を強制するとは言わない。 -/
theorem two_valued_of_absorbing (p h : S.IProp) (habs : S.iand p h = h) :
    S.PrI p h = 0 ∨ S.PrI p h = 1 := by
  have e : S.PrI (S.iand p p) h = S.PrI p h :=
    subst_taut₀ hS (Form.conj (Form.var 0) (Form.var 0)) (Form.var 0) (fun _ => p) h
      (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have x := hS.def_X_left_i p p h
  rw [habs, e] at x
  have hz : S.PrI p h * (S.PrI p h - 1) = 0 := by
    rw [mul_sub, mul_one]
    linarith
  rcases mul_eq_zero.mp hz with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

end Internal

/-! ## 有限モデル: 空前提に固定世界 w₀ の真理値を割り当てる -/

/-- 世界集合。 -/
abbrev W := Fin 2
/-- 命題 = 世界の集合。 -/
abbrev M := Finset W

/-- 矛盾する前提の下で真理値を評価する固定の一世界。 -/
def w₀ : W := 0

def mand (p q : M) : M := p ∩ q
def mor  (p q : M) : M := p ∪ q
def mnot (p : M) : M := pᶜ
def miff (p q : M) : M := (p ∩ q) ∪ (pᶜ ∩ qᶜ)
def mtrue : M := Finset.univ

/-- 確率関係: 前提が充足可能なら条件付き相対頻度、空前提 (矛盾する連言) なら
固定世界 w₀ での真理値 [w₀ ∈ p]。公理 (i) (folio 135) は整合な前提について確率関係の
存在と一意性を主張し、矛盾する前提については沈黙する。空前提の値はその沈黙の部分を
埋めるモデル側の約定であり、S₀ の全公理を満たす形の一つである (他の形が無いことは
示していない)。 -/
noncomputable def pr₀ (p h : M) : ℝ :=
  if h.card = 0 then (if w₀ ∈ p then 1 else 0) else ((p ∩ h).card : ℝ) / h.card

/-! ### 基本補題 -/

theorem pr₀_of_card_zero {p h : M} (hh : h.card = 0) :
    pr₀ p h = if w₀ ∈ p then 1 else 0 := by
  simp [pr₀, hh]

theorem pr₀_of_card_ne_zero {p h : M} (hh : h.card ≠ 0) :
    pr₀ p h = ((p ∩ h).card : ℝ) / h.card := by
  simp [pr₀, hh]

/-- 空前提の下で確実 ⟺ w₀ で真。 -/
theorem pr₀_empty_eq_one_iff {p h : M} (hh : h.card = 0) : pr₀ p h = 1 ↔ w₀ ∈ p := by
  rw [pr₀_of_card_zero hh]
  split_ifs with hw
  · exact ⟨fun _ => hw, fun _ => rfl⟩
  · exact ⟨fun H => absurd H zero_ne_one, fun H => absurd H hw⟩

/-- 空前提の下の値は二値。 -/
theorem pr₀_empty_two_valued {p h : M} (hh : h.card = 0) : pr₀ p h = 0 ∨ pr₀ p h = 1 := by
  rw [pr₀_of_card_zero hh]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- 充足可能な前提の下で確実 ⟺ 前提が結論を含む (phase6c_model と同じ)。 -/
theorem pr₀_eq_one_iff {p h : M} (hh : h.card ≠ 0) : pr₀ p h = 1 ↔ h ⊆ p := by
  have hpos : (0 : ℝ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
  rw [pr₀_of_card_ne_zero hh, div_eq_one_iff_eq hpos.ne']
  constructor
  · intro H
    have hc : (p ∩ h).card = h.card := by exact_mod_cast H
    have e : p ∩ h = h := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hc.ge
    exact Finset.inter_eq_right.mp e
  · intro H
    rw [Finset.inter_eq_right.mpr H]

theorem card_le_of_inter_left {a h : M} : (a ∩ h).card ≤ h.card :=
  Finset.card_le_card Finset.inter_subset_right

/-- Def. VIII の集合論的中身 (phase6c_model と同じ)。 -/
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

/-- w₀ ∈ (a≡b) ⟺ (w₀ ∈ a ⟺ w₀ ∈ b)。 -/
theorem mem_miff_iff (a b : M) (w : W) : w ∈ miff a b ↔ (w ∈ a ↔ w ∈ b) := by
  simp only [miff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  tauto

/-! ### 各公理の成立 (S₀ の公理の文をそのまま命題として証明) -/

/-- **Def. IX** (folio 135): ab/h + a\bar{b}/h = a/h、空前提は真理値の加法。 -/
theorem model_def_IX_i (p q h : M) :
    pr₀ (mand p (mnot q)) h + pr₀ (mand p q) h = pr₀ p h := by
  by_cases hh : h.card = 0
  · simp only [pr₀_of_card_zero hh, mand, mnot, Finset.mem_inter, Finset.mem_compl]
    by_cases hp : w₀ ∈ p <;> by_cases hq : w₀ ∈ q <;> simp [hp, hq]
  · have key : (mand (mand p (mnot q)) h).card + (mand (mand p q) h).card
        = (mand p h).card := by
      have e1 : mand (mand p q) h = (mand p h).filter (fun w => w ∈ q) := by
        ext w; simp [mand, Finset.mem_filter]; tauto
      have e2 : mand (mand p (mnot q)) h = (mand p h).filter (fun w => ¬ w ∈ q) := by
        ext w; simp [mand, mnot, Finset.mem_filter]; tauto
      rw [e1, e2, add_comm]
      exact Finset.card_filter_add_card_filter_not _
    simp only [pr₀, if_neg hh]
    rw [← add_div]
    congr 1
    exact_mod_cast key

/-- **Def. X 左形** (folio 135): ab/h = a/bh · b/h。 -/
theorem model_def_X_left_i (p q h : M) :
    pr₀ (mand p q) h = pr₀ p (mand q h) * pr₀ q h := by
  by_cases hh : h.card = 0
  · -- 空前提: 真理値の積
    obtain rfl := Finset.card_eq_zero.mp hh
    simp only [mand, Finset.inter_empty, pr₀_of_card_zero Finset.card_empty, Finset.mem_inter]
    by_cases hp : w₀ ∈ p <;> by_cases hq : w₀ ∈ q <;> simp [hp, hq]
  by_cases hqh : (mand q h).card = 0
  · -- q ∧ h = ∅: 両辺 0
    have hz : (mand (mand p q) h).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← hqh]
      apply Finset.card_le_card
      intro w hw
      simp only [mand, Finset.mem_inter] at hw ⊢
      exact ⟨hw.1.2, hw.2⟩
    have hq0 : pr₀ q h = 0 := by
      rw [pr₀_of_card_ne_zero hh]
      simp only [mand] at hqh
      simp [hqh]
    have hl : pr₀ (mand p q) h = 0 := by
      rw [pr₀_of_card_ne_zero hh, show (mand p q ∩ h).card = 0 from hz]
      simp
    rw [hl, hq0, mul_zero]
  · simp only [mand] at hqh
    have hpos : (0 : ℝ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
    have hqpos : (0 : ℝ) < (q ∩ h).card := by exact_mod_cast Nat.pos_of_ne_zero hqh
    simp only [pr₀, mand, if_neg hh, if_neg hqh, Finset.inter_assoc]
    field_simp

/-- **Def. X 右形** (folio 135): ab/h = b/ah · a/h。 -/
theorem model_def_X_right_i (p q h : M) :
    pr₀ (mand p q) h = pr₀ q (mand p h) * pr₀ p h := by
  have e : mand p q = mand q p := by simp [mand, Finset.inter_comm]
  rw [e]
  exact model_def_X_left_i q p h

/-- **値域 (下)**: 0 ≤ a/h。 -/
theorem model_ax_range_lo_i (p h : M) : 0 ≤ pr₀ p h := by
  unfold pr₀
  split_ifs
  · exact zero_le_one
  · exact le_refl 0
  · positivity

/-- **値域 (上)**: a/h ≤ 1。 -/
theorem model_ax_range_hi_i (p h : M) : pr₀ p h ≤ 1 := by
  by_cases hh : h.card = 0
  · rw [pr₀_of_card_zero hh]
    split_ifs
    · exact le_refl 1
    · exact zero_le_one
  · have hpos : (0 : ℝ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
    rw [pr₀_of_card_ne_zero hh, div_le_one hpos]
    exact_mod_cast card_le_of_inter_left

/-- **Def. VIII 印刷どおり、但し書きなし** (folio 134、→ のみ):
If b/ah = 1 and a/bh = 1, (a≡b)/h = 1。空前提では真理値の推論、
a ∧ h = ∅ ≠ b ∧ h の混合形は前提 a/bh = 1 が b ∧ h ⊆ a ∧ h = ∅ を強いて矛盾する。 -/
theorem model_def_VIII_i_src (a b h : M) :
    pr₀ b (mand a h) = 1 → pr₀ a (mand b h) = 1 → pr₀ (miff a b) h = 1 := by
  intro H1 H2
  by_cases hh : h.card = 0
  · -- h = ∅: a ∧ h = b ∧ h = ∅、H1: w₀ ∈ b、H2: w₀ ∈ a
    obtain rfl := Finset.card_eq_zero.mp hh
    simp only [mand, Finset.inter_empty] at H1 H2
    rw [pr₀_empty_eq_one_iff Finset.card_empty] at H1 H2 ⊢
    rw [mem_miff_iff]
    exact ⟨fun _ => H1, fun _ => H2⟩
  · rw [pr₀_eq_one_iff hh, subset_miff_iff]
    by_cases hah : (mand a h).card = 0
    · have hae : a ∩ h = ∅ := Finset.card_eq_zero.mp hah
      by_cases hbh : (mand b h).card = 0
      · have hbe : b ∩ h = ∅ := Finset.card_eq_zero.mp hbh
        exact ⟨by rw [hae]; exact Finset.empty_subset _,
               by rw [hbe]; exact Finset.empty_subset _⟩
      · -- b ∧ h ≠ ∅ かつ b ∧ h ⊆ a ⟹ b ∧ h ⊆ a ∧ h = ∅: 矛盾
        rw [pr₀_eq_one_iff hbh] at H2
        exfalso
        apply hbh
        rw [Finset.card_eq_zero, ← Finset.subset_empty, ← hae]
        intro w hw
        exact Finset.mem_inter.mpr ⟨H2 hw, (Finset.mem_inter.mp hw).2⟩
    · by_cases hbh : (mand b h).card = 0
      · have hbe : b ∩ h = ∅ := Finset.card_eq_zero.mp hbh
        rw [pr₀_eq_one_iff hah] at H1
        exfalso
        apply hah
        rw [Finset.card_eq_zero, ← Finset.subset_empty, ← hbe]
        intro w hw
        exact Finset.mem_inter.mpr ⟨H1 hw, (Finset.mem_inter.mp hw).2⟩
      · rw [pr₀_eq_one_iff hah] at H1
        rw [pr₀_eq_one_iff hbh] at H2
        exact ⟨H1, H2⟩

/-- 有限モデルの結合子の組 (Cons なし)。 -/
noncomputable def finOps₀ : Ops₀ where
  IProp := M
  iand := mand
  ior := mor
  inot := mnot
  iiff := miff
  itrue := mtrue
  PrI := pr₀

/-- 構文の有限モデル解釈。 -/
def finInterp (env : ℕ → M) : Form → M
  | .var n    => env n
  | .tru      => mtrue
  | .fls      => mnot mtrue
  | .conj f g => mand (finInterp env f) (finInterp env g)
  | .disj f g => mor (finInterp env f) (finInterp env g)
  | .neg f    => mnot (finInterp env f)
  | .iffF f g => miff (finInterp env f) (finInterp env g)

theorem finOps₀_interp (env : ℕ → M) (f : Form) : finOps₀.interp env f = finInterp env f := by
  induction f with
  | var n => rfl
  | tru => rfl
  | fls => rfl
  | conj f g ihf ihg => simp only [Ops₀.interp]; rw [ihf, ihg]; rfl
  | disj f g ihf ihg => simp only [Ops₀.interp]; rw [ihf, ihg]; rfl
  | neg f ihf => simp only [Ops₀.interp]; rw [ihf]; rfl
  | iffF f g ihf ihg => simp only [Ops₀.interp]; rw [ihf, ihg]; rfl

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

/-- **Ax.(iii) 但し書きなし** (folio 135): 任意の前提 (矛盾する連言 ∅ を含む) の下で
恒真式は確実。空前提では恒真式が w₀ で真であることによる。 -/
theorem model_ax_iii_taut (f : Form) (env : ℕ → M) (h : M) (ht : Taut f) :
    pr₀ (finInterp env f) h = 1 := by
  by_cases hh : h.card = 0
  · rw [pr₀_empty_eq_one_iff hh, mem_finInterp]
    exact ht _
  · rw [pr₀_eq_one_iff hh]
    intro w _
    rw [mem_finInterp]
    exact ht _

/-- **有限モデルは S₀ をすべて満たす** (受け入れ条件 2)。 -/
theorem finSys₀ : Sys₀ finOps₀ where
  def_IX_i := model_def_IX_i
  def_X_left_i := model_def_X_left_i
  def_X_right_i := model_def_X_right_i
  ax_range_lo_i := model_ax_range_lo_i
  ax_range_hi_i := model_ax_range_hi_i
  def_VIII_i_src := model_def_VIII_i_src
  ax_iii_taut := fun f env h ht => by
    show pr₀ (finOps₀.interp env f) h = 1
    rw [finOps₀_interp]
    exact model_ax_iii_taut f env h ht

/-! ### 無矛盾性と非導出性 -/

/-- **S₀ は無矛盾** (受け入れ条件 2): モデルが存在する。 -/
theorem th_S0_consistent : ∃ S : Ops₀, Sys₀ S := ⟨finOps₀, finSys₀⟩

/-- **S₀ から False は導けない** (受け入れ条件 3 の否定形): 「Sys₀ を満たす任意の構造で
False」は偽。 -/
theorem th_S0_not_inconsistent : ¬ ∀ S : Ops₀, Sys₀ S → False :=
  fun H => H finOps₀ finSys₀

/-- 旧経路の結論 (任意の a, h で a/(a ∧ h) = 1) はモデルで偽: a := ∅、h := ⊤ で
∅/(∅ ∧ ⊤) = ∅/∅ = [w₀ ∈ ∅] = 0。 -/
theorem model_not_self_evidence : ∃ a h : M, pr₀ a (mand a h) ≠ 1 :=
  ⟨∅, Finset.univ, by simp [pr₀, mand, w₀]⟩

/-- **旧経路の遮断 (Lean 内部)**: S₀ から a/(a ∧ h) = 1 は導けない。 -/
theorem not_self_evidence₀ :
    ¬ ∀ (S : Ops₀), Sys₀ S → ∀ a h : S.IProp, S.PrI a (S.iand a h) = 1 := by
  intro H
  obtain ⟨a, h, hne⟩ := model_not_self_evidence
  exact hne (H finOps₀ finSys₀ a h)

/-- **定義 VIII の逆向き (但し書きなし) はモデルで偽**: a = b = ∅、h = ⊤ で
(∅≡∅)/⊤ = 1 だが ∅/(∅ ∧ ⊤) = 0。 -/
theorem model_def_VIII_back_fails :
    ∃ a b h : M, pr₀ (miff a b) h = 1 ∧ pr₀ b (mand a h) ≠ 1 := by
  refine ⟨∅, ∅, Finset.univ, ?_, ?_⟩
  · rw [pr₀_eq_one_iff (by simp)]
    exact (subset_miff_iff ∅ ∅ Finset.univ).mpr ⟨by simp, by simp⟩
  · simp [pr₀, mand, w₀]

/-- **定義 VIII の逆向きは S₀ から導けない** (Lean 内部)。但し書きが要るのはこの向き
だけである (旧 6c はこの向きを但し書きなしで公理に置いて矛盾した)。 -/
theorem not_def_VIII_back :
    ¬ ∀ (S : Ops₀), Sys₀ S → ∀ a b h : S.IProp,
      S.PrI (S.iiff a b) h = 1 → S.PrI b (S.iand a h) = 1 := by
  intro H
  obtain ⟨a, b, h, hcert, hne⟩ := model_def_VIII_back_fails
  exact hne (H finOps₀ finSys₀ a b h hcert)

/-! ### 中間値 (受け入れ条件 4) -/

/-- **中間値の実現**: a := {0}、h := ⊤ で a/h = 1/2。 -/
theorem model_intermediate_value : pr₀ ({0} : M) Finset.univ = 1 / 2 := by
  rw [pr₀_of_card_ne_zero (by simp)]
  simp

/-- **S₀ は二値に退化しない** (縮退定理 ext_forced の内包版「任意の a, h で
a/h ∈ {0, 1}」は S₀ から導けない)。 -/
theorem th_S0_not_two_valued :
    ¬ ∀ (S : Ops₀), Sys₀ S → ∀ a h : S.IProp, S.PrI a h = 0 ∨ S.PrI a h = 1 := by
  intro H
  have := H finOps₀ finSys₀ ({0} : M) Finset.univ
  rw [show finOps₀.PrI ({0} : M) Finset.univ = pr₀ ({0} : M) Finset.univ from rfl,
    model_intermediate_value] at this
  rcases this with h0 | h1
  · norm_num at h0
  · norm_num at h1

/-- 空前提は任意の p で p ∧ ∅ = ∅ を満たす。 -/
theorem model_empty_absorbing (p : M) : mand p ∅ = ∅ := by
  simp [mand]

/-- **two_valued_of_absorbing のモデルでの実例**: p ∧ h = h を満たす前提の下の二値性を、
このモデルでそれにあたる ∅ に適用した形。モデルの約定 (真理値) が直接満たす形
(pr₀_empty_two_valued) と一致する。 -/
theorem model_empty_two_valued_from_S0 (p : M) : pr₀ p ∅ = 0 ∨ pr₀ p ∅ = 1 :=
  two_valued_of_absorbing finSys₀ p (∅ : M) (model_empty_absorbing p)

/-! ## 修復版 (phase6c、Cons 付き) との和集合の無矛盾性 (受け入れ条件 5 (c) の根拠) -/

/-- 結合子の組 + 整合性述語。 -/
structure OpsC extends Ops₀ where
  Cons : IProp → Prop

/-- **修復版の公理の文** (phase6c.lean の axiom のうち Cons を含むもの + Cons の公理 4 本)。
Cons を含まない公理 (Def. IX, X, 値域, def_VIII_i_src) は Sys₀ に既にある。 -/
structure SysC (S : OpsC) : Prop where
  def_VIII_i : ∀ a b h, S.Cons (S.iand a h) → S.Cons (S.iand b h) →
    (S.PrI (S.iiff a b) h = 1 ↔ (S.PrI b (S.iand a h) = 1 ∧ S.PrI a (S.iand b h) = 1))
  ax_iii_taut_cons : ∀ (f : Form) (env : ℕ → S.IProp) (h : S.IProp),
    S.Cons h → Taut f → S.PrI (S.toOps₀.interp env f) h = 1
  cons_true : S.Cons S.itrue
  cons_of_pos_src : ∀ a h, S.Cons (S.iand a h) → S.PrI a h ≠ 0
  cons_of_pos : ∀ a h, S.PrI a h ≠ 0 → S.Cons h → S.Cons (S.iand a h)
  cons_iff_taut : ∀ (f g : Form) (env : ℕ → S.IProp),
    Taut (Form.iffF f g) → (S.Cons (S.toOps₀.interp env f) ↔ S.Cons (S.toOps₀.interp env g))

/-- 整合性 = 充足可能性 (phase6c_model と同じ)。 -/
def Cons (h : M) : Prop := h.Nonempty

theorem cons_iff_card {h : M} : Cons h ↔ h.card ≠ 0 :=
  Finset.card_ne_zero.symm

theorem card_ne_zero_of_inter {a h : M} (hc : (a ∩ h).card ≠ 0) : h.card ≠ 0 := by
  intro hh
  apply hc
  exact Nat.eq_zero_of_le_zero (hh ▸ card_le_of_inter_left)

/-- **Def. VIII 双条件、但し書き付き** (folio 134、修復版): 本モデルでも成り立つ。 -/
theorem model_def_VIII_i (a b h : M) (hca : Cons (mand a h)) (hcb : Cons (mand b h)) :
    pr₀ (miff a b) h = 1 ↔ (pr₀ b (mand a h) = 1 ∧ pr₀ a (mand b h) = 1) := by
  have hca' : (mand a h).card ≠ 0 := cons_iff_card.mp hca
  have hcb' : (mand b h).card ≠ 0 := cons_iff_card.mp hcb
  have hh : h.card ≠ 0 := card_ne_zero_of_inter hca'
  rw [pr₀_eq_one_iff hh, pr₀_eq_one_iff hca', pr₀_eq_one_iff hcb']
  exact subset_miff_iff a b h

theorem model_cons_true : Cons mtrue := Finset.univ_nonempty

theorem model_cons_of_pos_src (a h : M) : Cons (mand a h) → pr₀ a h ≠ 0 := by
  intro hca
  have hca' : (mand a h).card ≠ 0 := cons_iff_card.mp hca
  have hh : h.card ≠ 0 := card_ne_zero_of_inter hca'
  rw [pr₀_of_card_ne_zero hh]
  have hpos : (0 : ℝ) < (a ∩ h).card := by
    exact_mod_cast Nat.pos_of_ne_zero hca'
  have hhpos : (0 : ℝ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
  exact (div_pos hpos hhpos).ne'

theorem model_cons_of_pos (a h : M) : pr₀ a h ≠ 0 → Cons h → Cons (mand a h) := by
  intro hne hc
  rw [cons_iff_card]
  intro hz
  apply hne
  rw [pr₀_of_card_ne_zero (cons_iff_card.mp hc)]
  simp only [mand] at hz
  simp [hz]

theorem model_cons_iff_taut (f g : Form) (env : ℕ → M) (ht : Taut (Form.iffF f g)) :
    Cons (finInterp env f) ↔ Cons (finInterp env g) := by
  have e : finInterp env f = finInterp env g := by
    ext w
    rw [mem_finInterp, mem_finInterp]
    have H := ht (fun n => decide (w ∈ env n))
    simp only [evalB, beq_iff_eq] at H
    rw [H]
  rw [e]

/-- 有限モデルの結合子の組 + 整合性述語。 -/
noncomputable def finOpsC : OpsC where
  toOps₀ := finOps₀
  Cons := Cons

/-- **同じモデルが修復版の公理の文をすべて満たす**。 -/
theorem finSysC : SysC finOpsC where
  def_VIII_i := model_def_VIII_i
  ax_iii_taut_cons := fun f env h _ ht => by
    show pr₀ (finOps₀.interp env f) h = 1
    rw [finOps₀_interp]
    exact model_ax_iii_taut f env h ht
  cons_true := model_cons_true
  cons_of_pos_src := model_cons_of_pos_src
  cons_of_pos := model_cons_of_pos
  cons_iff_taut := fun f g env ht => by
    show Cons (finOps₀.interp env f) ↔ Cons (finOps₀.interp env g)
    rw [finOps₀_interp, finOps₀_interp]
    exact model_cons_iff_taut f g env ht

/-- **S₀ ∪ 修復版は無矛盾**: 但し書きなしの ax_iii_taut と印刷方向 VIII を、Cons 付き
修復版の全公理に加えても矛盾しない。したがって公理 (iii) の但し書きは無矛盾性に
不要であり、但し書きが必要なのは定義 VIII の逆向きだけである (not_def_VIII_back と
phase6c_inconsistency の th_6c_old_inconsistent、および下の
th_VIII_bicond_iii_cons_inconsistent を合わせて)。 -/
theorem th_union_consistent : ∃ S : OpsC, Sys₀ S.toOps₀ ∧ SysC S :=
  ⟨finOpsC, finSys₀, finSysC⟩

/-! ## 残る一組: 定義 VIII 双条件 (但し書きなし) ＋ 公理 (iii) 但し書き付き (第2回 F2)

但し書きを公理 (iii) 側にだけ置き、定義 VIII は双条件のまま但し書きなしで読む公理群。
Def. IX, X, 値域は Sys₀ と同文 (Cons なし)、Cons の公理 4 本は修復版 (SysC) と同文。
結果は**矛盾**: 公理 (iii) (Cons ⊤ の下で (⊥ ≡ ⊥ ∧ q)/⊤ = 1、⊥ := ¬⊤) と双条件 VIII の
逆向きから、矛盾する前提 k := ⊥ ∧ ⊤ の下で ⊥/k = (⊥ ∧ q)/k = (⊥ ∧ ¬q)/k = 1 が出て、
Def. IX (p := ⊥、前提 k) が 1 + 1 = 1 になる。使う公理は Def. IX・双条件 VIII・
Cons 付き (iii)・cons_true の 4 本だけである (VIII_bicond_iii_cons_core)。 -/

/-- **公理群 S_B**: 定義 VIII 双条件 (但し書きなし) ＋ 公理 (iii) 但し書き付き。 -/
structure SysB (S : OpsC) : Prop where
  def_IX_i : ∀ p q h, S.PrI (S.iand p (S.inot q)) h + S.PrI (S.iand p q) h = S.PrI p h
  def_X_left_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI p (S.iand q h) * S.PrI q h
  def_X_right_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI q (S.iand p h) * S.PrI p h
  ax_range_lo_i : ∀ p h, 0 ≤ S.PrI p h
  ax_range_hi_i : ∀ p h, S.PrI p h ≤ 1
  def_VIII_i_bicond : ∀ a b h,
    S.PrI (S.iiff a b) h = 1 ↔ (S.PrI b (S.iand a h) = 1 ∧ S.PrI a (S.iand b h) = 1)
  ax_iii_taut_cons : ∀ (f : Form) (env : ℕ → S.IProp) (h : S.IProp),
    S.Cons h → Taut f → S.PrI (S.toOps₀.interp env f) h = 1
  cons_true : S.Cons S.itrue
  cons_of_pos_src : ∀ a h, S.Cons (S.iand a h) → S.PrI a h ≠ 0
  cons_of_pos : ∀ a h, S.PrI a h ≠ 0 → S.Cons h → S.Cons (S.iand a h)
  cons_iff_taut : ∀ (f g : Form) (env : ℕ → S.IProp),
    Taut (Form.iffF f g) → (S.Cons (S.toOps₀.interp env f) ↔ S.Cons (S.toOps₀.interp env g))

/-- **核**: Def. IX・双条件 VIII (但し書きなし)・Cons 付き (iii)・cons_true の 4 本から False。
Def. X、値域、残りの Cons 公理は使わない。 -/
theorem VIII_bicond_iii_cons_core {S : OpsC}
    (hIX : ∀ p q h, S.PrI (S.iand p (S.inot q)) h + S.PrI (S.iand p q) h = S.PrI p h)
    (hVIII : ∀ a b h,
      S.PrI (S.iiff a b) h = 1 ↔ (S.PrI b (S.iand a h) = 1 ∧ S.PrI a (S.iand b h) = 1))
    (hiii : ∀ (f : Form) (env : ℕ → S.IProp) (h : S.IProp),
      S.Cons h → Taut f → S.PrI (S.toOps₀.interp env f) h = 1)
    (hct : S.Cons S.itrue) : False := by
  -- (⊥ ≡ ⊥ ∧ q)/⊤ = 1 (公理 (iii)、Cons ⊤) → 双条件 VIII の逆向きで (⊥ ∧ q)/(⊥ ∧ ⊤) = 1
  have key : ∀ q : S.IProp,
      S.PrI (S.iand (S.inot S.itrue) q) (S.iand (S.inot S.itrue) S.itrue) = 1 := by
    intro q
    have hc : S.PrI (S.iiff (S.inot S.itrue) (S.iand (S.inot S.itrue) q)) S.itrue = 1 :=
      hiii (Form.iffF Form.fls (Form.conj Form.fls (Form.var 0))) (fun _ => q) S.itrue hct
        (by intro v; simp [evalB])
    exact ((hVIII _ _ _).mp hc).1
  -- (⊥ ≡ ⊥)/⊤ = 1 → ⊥/(⊥ ∧ ⊤) = 1
  have self : S.PrI (S.inot S.itrue) (S.iand (S.inot S.itrue) S.itrue) = 1 := by
    have hc : S.PrI (S.iiff (S.inot S.itrue) (S.inot S.itrue)) S.itrue = 1 :=
      hiii (Form.iffF Form.fls Form.fls) (fun _ => S.inot S.itrue) S.itrue hct
        (by intro v; simp [evalB])
    exact ((hVIII _ _ _).mp hc).1
  -- Def. IX (p := ⊥、q := ⊥、前提 k := ⊥ ∧ ⊤): 1 + 1 = 1
  have step := hIX (S.inot S.itrue) (S.inot S.itrue) (S.iand (S.inot S.itrue) S.itrue)
  rw [key (S.inot (S.inot S.itrue)), key (S.inot S.itrue), self] at step
  norm_num at step

/-- **S_B は矛盾する** (第2回 F2 の決着、(ii)): 但し書きを公理 (iii) 側にだけ置いても
双条件 VIII は救えない。但し書きは定義 VIII 側 (逆向きの前提 b/ah, a/bh の存在) に
置く必要がある。 -/
theorem th_VIII_bicond_iii_cons_inconsistent : ∀ S : OpsC, SysB S → False :=
  fun _ hS => VIII_bicond_iii_cons_core hS.def_IX_i hS.def_VIII_i_bicond
    hS.ax_iii_taut_cons hS.cons_true

/-- 同じことのモデル側の言い方: S_B を満たす構造は無い (finSys 系の流用は不可能)。 -/
theorem th_no_model_VIII_bicond_iii_cons : ¬ ∃ S : OpsC, SysB S :=
  fun ⟨S, hS⟩ => th_VIII_bicond_iii_cons_inconsistent S hS

end KeynesI_necessity

/-! ## 監査クエリ -/

#check @KeynesI_necessity.finSys₀
#check @KeynesI_necessity.th_S0_consistent
#check @KeynesI_necessity.th_S0_not_two_valued
#check @KeynesI_necessity.not_def_VIII_back
#check @KeynesI_necessity.two_valued_of_absorbing
#check @KeynesI_necessity.th_union_consistent
#check @KeynesI_necessity.th_VIII_bicond_iii_cons_inconsistent

-- S₀ の内部定理 (axiom 宣言を含まないこと = propext, Classical.choice, Quot.sound のみ)
#print axioms KeynesI_necessity.itrue_certain₀
#print axioms KeynesI_necessity.true_conj₀
#print axioms KeynesI_necessity.compl₀
#print axioms KeynesI_necessity.th_12₀
#print axioms KeynesI_necessity.subst_taut₀
#print axioms KeynesI_necessity.two_valued_of_absorbing
-- 各公理の成立 (受け入れ条件 2)
#print axioms KeynesI_necessity.model_def_IX_i
#print axioms KeynesI_necessity.model_def_X_left_i
#print axioms KeynesI_necessity.model_def_X_right_i
#print axioms KeynesI_necessity.model_ax_range_lo_i
#print axioms KeynesI_necessity.model_ax_range_hi_i
#print axioms KeynesI_necessity.model_def_VIII_i_src
#print axioms KeynesI_necessity.model_ax_iii_taut
#print axioms KeynesI_necessity.finSys₀
#print axioms KeynesI_necessity.th_S0_consistent
#print axioms KeynesI_necessity.th_S0_not_inconsistent
-- 非導出性
#print axioms KeynesI_necessity.model_not_self_evidence
#print axioms KeynesI_necessity.not_self_evidence₀
#print axioms KeynesI_necessity.model_def_VIII_back_fails
#print axioms KeynesI_necessity.not_def_VIII_back
-- 中間値 (受け入れ条件 4)
#print axioms KeynesI_necessity.model_intermediate_value
#print axioms KeynesI_necessity.th_S0_not_two_valued
#print axioms KeynesI_necessity.model_empty_two_valued_from_S0
-- 修復版との和集合
#print axioms KeynesI_necessity.model_def_VIII_i
#print axioms KeynesI_necessity.finSysC
#print axioms KeynesI_necessity.th_union_consistent
-- 残る一組 (第2回 F2): 定義 VIII 双条件 (但し書きなし) ＋ Cons 付き (iii) は矛盾
#print axioms KeynesI_necessity.VIII_bicond_iii_cons_core
#print axioms KeynesI_necessity.th_VIII_bicond_iii_cons_inconsistent
#print axioms KeynesI_necessity.th_no_model_VIII_bicond_iii_cons
