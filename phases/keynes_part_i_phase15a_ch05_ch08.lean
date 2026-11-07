/-
# Keynes (1921) *A Treatise on Probability* Part I — Lean 4 Phase 15a
#
# B43 (2026-11-07)
# **第5章 §§2–3 (folio 66–67) の比較の型 (ii.)(iii.) と図式化、第8章 §13 (folio 105–106) の
#   頻度理論の記法、第17章 §2 (folio 189) の (56.2)(56.5) の狭義不等式の反例**
#
# ## 原典 (唯一の基準、1921 Macmillan 初版) の該当箇所
#   folio 66 (第5章 §2 (ii.)): 「If h₁ is favourable, a/hh₁ > a/h. Similarly, if h₂ is favourable
#     to a/hh₁, a/hh₁h₂ > a/hh₁. The reverse holds if h₁ and h₂ are unfavourable.」
#     「We may find, for instance, that a/hh₁ > a/h, that a/h = b/h, that b/h > b/hh₂, and that,
#     therefore, a/hh₁ > b/hh₂.」(folio 67 冒頭: 「comparisons of this type by (iii.)」)
#   folio 67 (第5章 §3): 「if our relevant evidence h were of the form ψ₁(a)ψ₂(b)ψ₃(b), it is
#     easily seen that the comparison a/h < b/h could be justified on the lines laid down above.」
#     脚注 2: 「For a/ψ₂(a) = b/ψ₂(b) ; a/ψ₁(a) < a/ψ₂(a) ; b/ψ₂(b) < b/ψ₂(b)ψ₃(b) ;
#     a/ψ₁(a) = a/h ; and b/ψ₂(b)ψ₃(b) = b/h.」
#   folio 105 (第8章 §13): 「Let α_f represent the truth-frequency of any class α, and let a_α/h
#     stand for 'the probability of a on hypothesis h, α being the class of reference determined
#     by this hypothesis.' We then have a_α/h = α_f, and we require to prove a proposition, for
#     values of γ and δ not yet determined, which will be of the form :
#     (a + b)_δ/h = a_α/h + b_β/h − ab_γ/h.
#     Now if δ′ is the class of propositions (a + b) such that a is an α and b a β, it is easily
#     shown by the ordinary arithmetic of classes that δ′_f = α_f + β_f − αβ_f where αβ is the
#     class of propositions which are members of both α and β. In the case, therefore, where
#     δ = δ′ and γ = αβ, an addition theorem of the required kind has been established.」
#     「On the frequency theory, therefore, we cannot maintain that the addition theorem is true
#     in general, but only in those special cases where it happens that δ = δ′ and γ = αβ.」
#   folio 106: 「colour-blindness and black hair being independent for knowledge relative to the
#     given data, ab/h = p₁p₂/q², and that, therefore, by the addition theorem,
#     (a + b)/h = p₁/q + p₂/q − p₁p₂/q². But, on the frequency theory, this result might be
#     invalid; for αβ_f = p₁p₂/q², only if this is the actual proportion in fact」
#     「In the frequency notation ... the corresponding theorem will be of the form
#     ab_δ/h = a_γ/bh . b_β/h. For this equation to be satisfied it is easily seen that δ must be
#     the class of propositions xy such that x is a member of α and y of β, and γ the class of
#     propositions xb such that x is a member of α」
#   folio 189 (第17章 §2): 「(56.2) ... The only limit we then have is u < p₁ + p₂.」
#     「(56.5) If a₁/a₂h = a₁/h ... ∴ u > c₁p₁ + c₂p₂ − c₁c₂.」
#
# ## 担体 (四つ、互いに接続しない)
#   §1 第5章: phase12a_order の確率集合 Π (半順序の型 Deg、PrO : IProp → IProp → Deg) を
#     同文で宣言し直す。第5章 §2–§3 は数値によらない比較の章なので、ℝ 値の PrI でなく
#     半順序の上で書く (推移律だけを使う; ℝ も半順序なので同じ証明がそのまま通る)。
#     前提の並置は Def. X の形 (iand q h = 「qh」) で、印刷の hh₁ は iand h h₁、hh₁h₂ は
#     iand (iand h h₁) h₂、ψ₂(b)ψ₃(b) は iand (ψ₂ b) (ψ₃ b)。いずれも印刷の順のまま。
#     推移律の必要性は、推移律の無い 3 点の関係 ntR の模型 (th_5_r017_needs_trans) で示す。
#   §2 第8章: 頻度理論の担体 (第II部の公理と接続しない)。参照類は「系列 (成員の有限集合) と、
#     そのうち命題が真である成員の集合」の対 RefCls、真理頻度 α_f はその比 (ℚ)。
#     「a is an α and b a β」は同じ成員についての対と読む (αβ・δ′ は成員ごとの連言・選言;
#     folio 106 の「the actual proportion in fact of persons who are both colour-blind and
#     black-haired」の読み)。この読みと「α と β が同じ系列」(前提 hS) は印刷に無いので、
#     010・011・026 は ≈。頻度と確率の一致は外部公理 ax_freq_eq_prob に置く。
#   §2b 第8章 ch08-023: 添字の無い Keynes 自身の記法の行なので、第II部の担体 (IProp・PrI・Cons、
#     phase10c の KeynesI の写しの一部) の上で、022 を加法定理 (24) th_24_i に代入する。
#     頻度の担体の上の 023 (024 を前提に置く形) は th_8_r023_freq。
#   §3 第17章: phase5 の公理 (ax_range, ax_iii_true, def_IX, def_X_left/right) を有限集合の
#     上の法則の構造体 PrLaws に写し、4 世界の数え上げ模型 finPr がそれを満たすことを示した
#     うえで、(56.2)(56.5) の前提を満たし等号が成り立つ例を置く。
#     **PrLaws は phase5 の公理系と同じではない**: (1) iii_true は前提が空でない場合だけ
#     (phase6c の Cons h に当たる; phase5 の ax_iii_true は無条件) に弱めている、(2) ax_iii_op と
#     def_XI を含まない (命題は集合なので ax_iii_op は等号で自明、def_XI は実数の割り算の規則)、
#     (3) 担体は有限集合 (Fin 4 の部分集合) の上の数え上げ確率模型で、値は ℚ。
#     したがって反例が示すのは「PrLaws から狭義形は出ない」ことで、phase5 の公理系そのものの
#     模型ではない。
#
# ## 実行方法
#   lake env lean phases/keynes_part_i_phase15a_ch05_ch08.lean
-/

import Mathlib

namespace KeynesP15a

/-! ## §1 第5章: 確率集合 Π の半順序 (phase12a_order と同文の一部、import しない) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp

/-- 確率集合 Π (phase12a_order と同文)。 -/
axiom Deg : Type
/-- Π の半順序 (phase12a_order と同文)。 -/
axiom instPartialOrderDeg : PartialOrder Deg
attribute [instance] instPartialOrderDeg
/-- 確率関係 a/h の値 (phase12a_order と同文): 値域は Π。 -/
axiom PrO : IProp → IProp → Deg

/-- **好意的な証拠** (folio 66 §2 (ii.)「If h₁ is favourable, a/hh₁ > a/h」)。
前提の並置 hh₁ は Def. X の形 iand h h₁ で、印刷の順のまま。 -/
def Favourable (h₁ a h : IProp) : Prop := PrO a (iand h h₁) > PrO a h

/-- **好意的でない証拠** (folio 66「The reverse holds if h₁ and h₂ are unfavourable」):
a/hh₂ < a/h。 -/
def Unfavourable (h₂ a h : IProp) : Prop := PrO a (iand h h₂) < PrO a h

/-- **ch05-009** (folio 66): 「If h₁ is favourable, a/hh₁ > a/h」は定義 Favourable の本体。 -/
theorem th_5_r009 (h₁ a h : IProp) : Favourable h₁ a h ↔ PrO a (iand h h₁) > PrO a h :=
  Iff.rfl

/-- **ch05-011** (folio 66): 「if h₂ is favourable to a/hh₁, a/hh₁h₂ > a/hh₁」は、定義 Favourable を
前提 hh₁ (iand h h₁) に当てた本体 (定義の展開; 009 と同じ扱い)。 -/
theorem th_5_r011 (a h h₁ h₂ : IProp) :
    Favourable h₂ a (iand h h₁) ↔ PrO a (iand (iand h h₁) h₂) > PrO a (iand h h₁) :=
  Iff.rfl

/-- **ch05-017** (folio 66): 型 (iii.) の比較。「that a/hh₁ > a/h [014], that a/h = b/h [015],
that b/h > b/hh₂ [016], and that, therefore, a/hh₁ > b/hh₂ [017]」。
b/hh₂ < b/h = a/h < a/hh₁ と Π の推移律。 -/
theorem th_5_r017 (a b h h₁ h₂ : IProp) (h014 : Favourable h₁ a h)
    (h015 : PrO a h = PrO b h) (h016 : PrO b h > PrO b (iand h h₂)) :
    PrO a (iand h h₁) > PrO b (iand h h₂) := by
  unfold Favourable at h014
  rw [h015] at h014
  exact lt_trans h016 h014

/-- ch05-016 の別形: 016 は「h₂ は b/h に好意的でない」(Unfavourable) の本体。 -/
theorem th_5_r016 (h₂ b h : IProp) : Unfavourable h₂ b h ↔ PrO b h > PrO b (iand h h₂) :=
  Iff.rfl

/-- **ch05-022** (folio 67 §3 と脚注 2): Romulus の伝承 a と Caesar の伝承 b。ψ₁・ψ₂・ψ₃ は
命題関数 (ψ₁(x)「伝承 x は Caesar の時代よりずっと前から伝わる」、ψ₂(x)「伝承 x は Caesar の
時代から伝わる」、ψ₃(x)「伝承 x には伝承の外の支えがある」)。脚注 2 の 5 本 (023–027) を前提に
置くと、a/h = a/ψ₁(a) < a/ψ₂(a) = b/ψ₂(b) < b/ψ₂(b)ψ₃(b) = b/h で a/h < b/h。
5 本はどれも使う。 -/
theorem th_5_r022 (ψ₁ ψ₂ ψ₃ : IProp → IProp) (a b h : IProp)
    (h023 : PrO a (ψ₂ a) = PrO b (ψ₂ b))
    (h024 : PrO a (ψ₁ a) < PrO a (ψ₂ a))
    (h025 : PrO b (ψ₂ b) < PrO b (iand (ψ₂ b) (ψ₃ b)))
    (h026 : PrO a (ψ₁ a) = PrO a h)
    (h027 : PrO b (iand (ψ₂ b) (ψ₃ b)) = PrO b h) :
    PrO a h < PrO b h := by
  rw [← h026, ← h027]
  rw [h023] at h024
  exact lt_trans h024 h025

/-- 推移律の無い 3 点の関係 (th_5_r017_needs_trans の模型): 0 R 1 と 1 R 2 だけで、0 R 2 は無い。 -/
def ntR : Fin 3 → Fin 3 → Prop := fun x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2)

/-- **ch05-017 の推移律の必要性** (th_5_r017): 推移律の無い 3 点の関係 ntR を「<」の代わりに
置くと、017 の形の推論は通らない。値を b/hh₂ = 0、a/h = b/h = 1、a/hh₁ = 2 と置くと、前提 014
(a/h R a/hh₁)・015 (a/h = b/h)・016 (b/hh₂ R b/h) は成り立つが、結論 017 (b/hh₂ R a/hh₁) は
成り立たない。第 1 成分は ntR が推移的でないこと。この模型は 017 の形 (前提 3 本) だけを扱い、
022 (前提 5 本) の形の模型ではない。 -/
theorem th_5_r017_needs_trans :
    ¬ (∀ x y z : Fin 3, ntR x y → ntR y z → ntR x z) ∧
      ∃ A A₁ B B₂ : Fin 3, ntR A A₁ ∧ A = B ∧ ntR B₂ B ∧ ¬ ntR B₂ A₁ := by
  refine ⟨fun H => ?_, ⟨1, 2, 1, 0, ?_⟩⟩
  · have := H 0 1 2 (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
    revert this; unfold ntR; decide
  · unfold ntR; decide

/-! ## §2 第8章: 頻度理論の担体 (第II部の公理と接続しない) -/

/-- 参照類: 系列 (成員の有限集合) と、その成員のうち命題が真であるものの集合。 -/
structure RefCls (ι : Type) where
  series : Finset ι
  trueSet : Finset ι

section Freq

variable {ι : Type} [DecidableEq ι]

/-- **真理頻度 α_f** (folio 105「Let α_f represent the truth-frequency of any class α」):
系列のうち真である成員の割合。系列が空なら 0 (ℚ の x/0 = 0)。 -/
def RefCls.tf (α : RefCls ι) : ℚ := ((α.series ∩ α.trueSet).card : ℚ) / α.series.card

set_option linter.unusedVariables false in
/-- **頻度記法 a_α/h** (folio 105、ch08-009「We then have a_α/h = α_f」): 前提 h が定める
参照類 α による a の確率を、α の真理頻度と定める。a と h は値に現れない (頻度理論の定義)。 -/
def FreqProb {Γ : Type} (a : Γ) (α : RefCls ι) (h : Γ) : ℚ := α.tf

/-- **δ′** (folio 105「the class of propositions (a + b) such that a is an α and b a β」):
同じ成員について α と β の選言。系列は α の系列。 -/
def disjCls (α β : RefCls ι) : RefCls ι := ⟨α.series, α.trueSet ∪ β.trueSet⟩

/-- **αβ** (folio 105「the class of propositions which are members of both α and β」):
同じ成員について α と β の連言。 -/
def conjCls (α β : RefCls ι) : RefCls ι := ⟨α.series, α.trueSet ∩ β.trueSet⟩

/-- **γ** (folio 106「the class of propositions xb such that x is a member of α」): 前提 bh の
下の参照類。系列を β の真の成員に狭めた α。 -/
def condCls (α β : RefCls ι) : RefCls ι := ⟨α.series ∩ β.trueSet, α.trueSet⟩

/-- **ch08-009** (folio 105): a_α/h = α_f (定義 FreqProb の本体)。 -/
theorem th_8_r009 {Γ : Type} (a : Γ) (α : RefCls ι) (h : Γ) : FreqProb a α h = α.tf :=
  rfl

/-- **ch08-011** (folio 105): 「by the ordinary arithmetic of classes that
δ′_f = α_f + β_f − αβ_f」。α と β が同じ系列の上の類であるとき (「a is an α and b a β」を
同じ成員の対と読む)、有限集合の |A ∪ B| + |A ∩ B| = |A| + |B| (Finset.card_union_add_card_inter)
を系列の大きさで割る。 -/
theorem th_8_r011 (α β : RefCls ι) (hS : α.series = β.series) :
    (disjCls α β).tf = α.tf + β.tf - (conjCls α β).tf := by
  simp only [RefCls.tf, disjCls, conjCls]
  rw [← hS, Finset.inter_union_distrib_left]
  have e : α.series ∩ (α.trueSet ∩ β.trueSet) =
      (α.series ∩ α.trueSet) ∩ (α.series ∩ β.trueSet) := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [e]
  have hc := Finset.card_union_add_card_inter (α.series ∩ α.trueSet) (α.series ∩ β.trueSet)
  have hq : (((α.series ∩ α.trueSet) ∪ (α.series ∩ β.trueSet)).card : ℚ) =
      ((α.series ∩ α.trueSet).card : ℚ) + ((α.series ∩ β.trueSet).card : ℚ) -
        (((α.series ∩ α.trueSet) ∩ (α.series ∩ β.trueSet)).card : ℚ) := by
    have : (((α.series ∩ α.trueSet) ∪ (α.series ∩ β.trueSet)).card : ℚ) +
        (((α.series ∩ α.trueSet) ∩ (α.series ∩ β.trueSet)).card : ℚ) =
        ((α.series ∩ α.trueSet).card : ℚ) + ((α.series ∩ β.trueSet).card : ℚ) := by
      exact_mod_cast hc
    linarith
  rw [hq]
  ring

/-- **ch08-010** (folio 105): 頻度記法の加法定理 (a + b)_δ/h = a_α/h + b_β/h − ab_γ/h。
「In the case, therefore, where δ = δ′ [013] and γ = αβ [014], an addition theorem of the
required kind has been established」。前提 h013・h014 が印刷の二つの条件。+ と並置は
頻度の側の命題の選言 fdisj・連言 fconj (値には現れない)。 -/
theorem th_8_r010 {Γ : Type} (fdisj fconj : Γ → Γ → Γ) (a b h : Γ)
    (α β γ δ : RefCls ι) (hS : α.series = β.series)
    (h013 : δ = disjCls α β) (h014 : γ = conjCls α β) :
    FreqProb (fdisj a b) δ h = FreqProb a α h + FreqProb b β h - FreqProb (fconj a b) γ h := by
  subst h013 h014
  exact th_8_r011 α β hS

/-- **ch08-022** (folio 106): 「independent for knowledge relative to the given data」。
a と b が知識について独立とは ab/h = a/h . b/h (第16章 §2 の語)。 -/
def IndepForKnowledge (pab pa pb : ℚ) : Prop := pab = pa * pb

/-- ch08-022 の値: a/h = p₁/q、b/h = p₂/q のとき、知識についての独立は ab/h = p₁p₂/q²。 -/
theorem th_8_r022 (p₁ p₂ q pab : ℚ) :
    IndepForKnowledge pab (p₁ / q) (p₂ / q) ↔ pab = p₁ * p₂ / q ^ 2 := by
  unfold IndepForKnowledge
  constructor <;> intro H <;> rw [H] <;> ring

/-- **頻度理論では 024 を前提に 023 が出る** (folio 106「on the frequency theory, this result might
be invalid; for αβ_f = p₁p₂/q², only if this is the actual proportion in fact」)。頻度記法の加法定理
(010、δ = δ′ (h013) の下、γ は αβ そのもの) に、与えられた割合 p₁/q・p₂/q (ch08-020・021) と
事実の割合 αβ_f = p₁p₂/q² (024、前提 h024) を代入すると、頻度の (a + b)_δ/h が 023 の右辺になる。
Keynes 自身の記法での 023 (第II部の担体、022 を加法定理に代入) は th_8_r023。 -/
theorem th_8_r023_freq {Γ : Type} (fdisj fconj : Γ → Γ → Γ) (a b h : Γ)
    (α β δ : RefCls ι) (p₁ p₂ q : ℚ) (hS : α.series = β.series)
    (h013 : δ = disjCls α β)
    (h020 : FreqProb a α h = p₁ / q) (h021 : FreqProb b β h = p₂ / q)
    (h024 : (conjCls α β).tf = p₁ * p₂ / q ^ 2) :
    FreqProb (fdisj a b) δ h = p₁ / q + p₂ / q - p₁ * p₂ / q ^ 2 := by
  rw [th_8_r010 fdisj fconj a b h α β (conjCls α β) δ hS h013 rfl, h020, h021, th_8_r009, h024]

/-- **ch08-026** (folio 106): 頻度記法の乗法定理 ab_δ/h = a_γ/bh . b_β/h。「δ must be the class
of propositions xy such that x is a member of α and y of β, and γ the class of propositions xb
such that x is a member of α」を δ = αβ (同じ成員の連言)、γ = β の真の成員に狭めた α と読む。
前提 bh は頻度の側の連言 fconj b h (印刷の並置 bh の順のまま)。
β の真の成員が無い場合も両辺 0 で成り立つ。 -/
theorem th_8_r026 {Γ : Type} (fconj : Γ → Γ → Γ) (a b h : Γ)
    (α β γ δ : RefCls ι) (hS : α.series = β.series)
    (hδ : δ = conjCls α β) (hγ : γ = condCls α β) :
    FreqProb (fconj a b) δ h = FreqProb a γ (fconj b h) * FreqProb b β h := by
  subst hδ hγ
  simp only [FreqProb, RefCls.tf, conjCls, condCls]
  rw [← hS]
  have e1 : α.series ∩ (α.trueSet ∩ β.trueSet) = (α.series ∩ β.trueSet) ∩ α.trueSet := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [e1]
  by_cases hB : (α.series ∩ β.trueSet).card = 0
  · have h0 : ((α.series ∩ β.trueSet) ∩ α.trueSet).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc ((α.series ∩ β.trueSet) ∩ α.trueSet).card
          ≤ (α.series ∩ β.trueSet).card := Finset.card_le_card Finset.inter_subset_left
        _ = 0 := hB
    rw [h0, hB]
    simp
  · have hB' : ((α.series ∩ β.trueSet).card : ℚ) ≠ 0 := by exact_mod_cast hB
    rw [div_mul_div_comm, mul_comm ((α.series ∩ β.trueSet).card : ℚ) (α.series.card : ℚ),
      mul_div_mul_right _ _ hB']

/-- 加法定理は一般には成り立たない (folio 105「we cannot maintain that the addition theorem is
true in general」): γ = αβ でも δ が δ′ でなければ 010 は偽 (013 の必要性)。 -/
theorem th_8_r010_needs_013 :
    ¬ ∀ (α β γ δ : RefCls (Fin 2)), α.series = β.series → γ = conjCls α β →
      δ.tf = α.tf + β.tf - γ.tf := by
  intro H
  have := H ⟨{0}, {0}⟩ ⟨{0}, {0}⟩ (conjCls ⟨{0}, {0}⟩ ⟨{0}, {0}⟩) ⟨{0}, ∅⟩ rfl rfl
  simp [RefCls.tf, conjCls] at this

/-- 同じく、δ = δ′ でも γ が αβ でなく別の類 μ (folio 105「points to some quite different
class μ as the suitable class of reference for ab」) なら 010 は偽 (014 の必要性)。 -/
theorem th_8_r010_needs_014 :
    ¬ ∀ (α β γ δ : RefCls (Fin 2)), α.series = β.series → δ = disjCls α β →
      δ.tf = α.tf + β.tf - γ.tf := by
  intro H
  have := H ⟨{0}, {0}⟩ ⟨{0}, {0}⟩ ⟨{0}, ∅⟩ (disjCls ⟨{0}, {0}⟩ ⟨{0}, {0}⟩) rfl rfl
  simp [RefCls.tf, disjCls] at this

/-- **補助 (決まらないことだけを示す)**: 頻度の担体の上で、α_f = p₁/q・β_f = p₂/q (020・021) と
同じ系列 (hS) だけでは、頻度の (a + b)_δ′/h は 023 の右辺に決まらない (th_8_r023_freq の前提 h024
を落とすと通らない)。系列 2 人 (成員 0 は黒髪かつ色覚異常、成員 1 はどちらでもない)、
p₁ = p₂ = 1、q = 2 で、αβ_f = 1/2、(a + b)_δ′/h = 1/2 は 3/4 と違う。知識の側の確率 (KPr) も
知識についての独立 (022) もこの定理文には現れない; 022 が成り立つ模型での 024 の反例は
th_8_r024_needs_ax。 -/
theorem th_8_r023_freq_needs_024 :
    ¬ ∀ (α β : RefCls (Fin 2)) (p₁ p₂ q : ℚ), α.series = β.series →
      α.tf = p₁ / q → β.tf = p₂ / q →
      (disjCls α β).tf = p₁ / q + p₂ / q - p₁ * p₂ / q ^ 2 := by
  intro H
  have hα : (⟨Finset.univ, {0}⟩ : RefCls (Fin 2)).tf = 1 / 2 := by
    simp [RefCls.tf]
  have := H ⟨Finset.univ, {0}⟩ ⟨Finset.univ, {0}⟩ 1 1 2 rfl hα hα
  simp [RefCls.tf, disjCls] at this
  norm_num at this

end Freq

/-! ### 頻度と確率の一致 (外部公理) -/

/-- 頻度理論の側の命題。 -/
axiom FProp : Type
/-- 頻度理論の側の命題の連言 (ab)。 -/
axiom fand : FProp → FProp → FProp
/-- 「α being the class of reference determined by this hypothesis」: 前提 h が a に定める参照類。 -/
axiom refCls : FProp → FProp → RefCls ℕ
/-- 確率 a/h の値 (知識の側; 第II部の公理とは接続しない)。 -/
axiom KPr : FProp → FProp → ℚ

/-- **外部公理: 頻度と確率の一致** (頻度理論の主張): 確率 a/h は、h が a に定める参照類の真理頻度
a_α/h = α_f に等しい。KPr := (a h ↦ FreqProb a (refCls a h) h) で満たされるので無矛盾
(ax_freq_eq_prob_sat)。 -/
axiom ax_freq_eq_prob (a h : FProp) : KPr a h = FreqProb a (refCls a h) h

/-- ax_freq_eq_prob の形の等式は、参照類の割り当てが何であっても満たせる。 -/
theorem ax_freq_eq_prob_sat {Γ : Type} (cls : Γ → Γ → RefCls ℕ) :
    ∃ K : Γ → Γ → ℚ, ∀ a h, K a h = FreqProb a (cls a h) h :=
  ⟨fun a h => FreqProb a (cls a h) h, fun _ _ => rfl⟩

/-- **ch08-024** (folio 106): 「for αβ_f = p₁p₂/q², only if this is the actual proportion in
fact」。頻度と確率の一致 (外部公理) の下では、知識についての独立 (022) と与えられた割合
(020・021) と γ = αβ (014) から、事実の割合 αβ_f = p₁p₂/q² が出てしまう。この外部公理を
落とすと 024 は出ない (KPr と参照類を自由な関数に替えた模型 th_8_r024_needs_ax)。
024 が出れば、頻度の 023 は th_8_r023_freq で出る。 -/
theorem th_8_r024 (a b h : FProp) (p₁ p₂ q : ℚ)
    (h020 : KPr a h = p₁ / q) (h021 : KPr b h = p₂ / q)
    (h014 : refCls (fand a b) h = conjCls (refCls a h) (refCls b h))
    (h022 : IndepForKnowledge (KPr (fand a b) h) (KPr a h) (KPr b h)) :
    (conjCls (refCls a h) (refCls b h)).tf = p₁ * p₂ / q ^ 2 := by
  unfold IndepForKnowledge at h022
  rw [ax_freq_eq_prob, h014, h020, h021] at h022
  rw [th_8_r009] at h022
  rw [h022]
  ring

/-- **ch08-024 の外部公理の必要性** (th_8_r024 から ax_freq_eq_prob を落とした形): 命題の型 Γ、
連言 fand'、参照類の割り当て cls、確率 K を自由に取れるとすると、th_8_r024 の前提 h020・h021・
h014・h022 がすべて成り立つのに結論 αβ_f = p₁p₂/q² が成り立たない模型がある。
模型: Γ = Fin 3 (a = 0、b = 1、ab = fand' a b = 2、h = 0)、参照類はどれも 2 人の系列
{0, 1} のうち成員 0 だけが真の類 (黒髪かつ色覚異常の 1 人と、どちらでもない 1 人)、
確率は K a h = K b h = 1/2、K (ab) h = 1/4。p₁ = p₂ = 1、q = 2。
h020・h021: a/h = b/h = 1/2 = p₁/q = p₂/q。h014: 参照類はどれも同じなので γ = αβ。
h022: 模型の中で IndepForKnowledge (K ab h) (K a h) (K b h) が成り立つ (1/4 = 1/2 · 1/2)。
結論: αβ_f = 1/2 ≠ p₁p₂/q² = 1/4。模型の K は (ab, h) で ax_freq_eq_prob を満たさない
(K ab h = 1/4、頻度 αβ_f = 1/2)。定理文に FProp・fand・refCls・KPr・ax_freq_eq_prob は現れない。 -/
theorem th_8_r024_needs_ax :
    ¬ ∀ (Γ : Type) (fand' : Γ → Γ → Γ) (cls : Γ → Γ → RefCls ℕ) (K : Γ → Γ → ℚ)
      (a b h : Γ) (p₁ p₂ q : ℚ),
      K a h = p₁ / q → K b h = p₂ / q →
      cls (fand' a b) h = conjCls (cls a h) (cls b h) →
      IndepForKnowledge (K (fand' a b) h) (K a h) (K b h) →
      (conjCls (cls a h) (cls b h)).tf = p₁ * p₂ / q ^ 2 := by
  intro H
  have := H (Fin 3) (fun _ _ => 2) (fun _ _ => ⟨{0, 1}, {0}⟩)
    (fun x _ => ![1 / 2, 1 / 2, 1 / 4] x) 0 1 0 1 1 2
    (by norm_num) (by norm_num) (by simp [conjCls])
    (by unfold IndepForKnowledge; norm_num [Matrix.cons_val_two])
  simp [RefCls.tf, conjCls] at this
  norm_num at this

/-! ## §2b 第8章 ch08-023: 第II部の担体 (phase10c の KeynesI の写しの一部、import しない)

folio 106 の 022・023 は添字の無い Keynes 自身の記法なので、頻度の担体ではなく第II部の担体
(IProp・PrI・Cons、B09 修復後の phase6c の公理群) の上で述べる。IProp・iand は §1 と共有する
(§1 の PrO とは接続しない)。写すのは加法定理 (24) (th_24_i) の証明に要る公理だけ:
def_IX_i・def_X_left_i・def_X_right_i・ax_iii_taut・cons_of_pos (phase10c と同文)。 -/

axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

/-- 確率関係 a/h の値 (第II部の担体、phase6c と同文)。 -/
axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 (公理 (i) の但し書き、folio 135)。 -/
axiom Cons : IProp → Prop

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h

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

noncomputable def interp (env : ℕ → IProp) : Form → IProp
  | .var n    => env n
  | .tru      => itrue
  | .fls      => inot itrue
  | .conj f g => iand (interp env f) (interp env g)
  | .disj f g => ior (interp env f) (interp env g)
  | .neg f    => inot (interp env f)
  | .iffF f g => iiff (interp env f) (interp env g)

axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)

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

/-- 補完律 (第13章の式 (1)、folio 139)。 -/
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

/-- Th.(12) (folio 141)、def_VIII_i を用いない短い証明 (phase6c の th_12_i_short)。 -/
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

/-- 代入原理 (論証的同値な結論は同じ確率)。th_12_i_short 経由。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i_short _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-- 加法定理 (24) (folio 144; 第8章 folio 105 の ch08-006)、phase6c の th_24_i。 -/
theorem th_24_i (a b h : IProp) (hc : Cons h) :
    PrI (ior a b) h = PrI a h + PrI b h - PrI (iand a b) h := by
  have step1 := def_IX_i (ior a b) b h
  have e1 : PrI (iand (ior a b) (inot b)) h = PrI (iand a (inot b)) h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.neg (Form.var 1)))
      (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
      (fun n => match n with | 0 => a | _ => b) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have e2 : PrI (iand (ior a b) b) h = PrI b h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.var 1))
      (Form.var 1)
      (fun n => match n with | 0 => a | _ => b) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have step3 := def_IX_i a b h
  linarith [step1, e1, e2, step3]

/-- **ch08-023** (folio 106): 「and that, therefore, by the addition theorem,
(a + b)/h = p₁/q + p₂/q − p₁p₂/q²」。022 ab/h = p₁p₂/q² (前提 h022、印刷の式のまま) を
加法定理 (24) (th_24_i) に代入する。a/h = p₁/q・b/h = p₂/q (前提 h020・h021) は folio 105 の
「the proportion of black-haired men in the population is p₁/q and the proportion of colour-blind
men p₂/q」を確率に取る読みで、印刷に式としては無い (代入の形)。+ は ior (脚注 1「a + b is never
interpreted so as to exclude the conjunctive ab」)。Cons h は担体の但し書き。 -/
theorem th_8_r023 (a b h : IProp) (hc : Cons h) (p₁ p₂ q : ℝ)
    (h020 : PrI a h = p₁ / q) (h021 : PrI b h = p₂ / q)
    (h022 : PrI (iand a b) h = p₁ * p₂ / q ^ 2) :
    PrI (ior a b) h = p₁ / q + p₂ / q - p₁ * p₂ / q ^ 2 := by
  rw [th_24_i a b h hc, h020, h021, h022]

/-! ## §3 第17章 (56.2)(56.5): 有限模型で等号が成り立つ例 -/

section Ch17

variable {W : Type} [Fintype W] [DecidableEq W]

/-- 数え上げの条件つき確率: a/h = |a ∩ h| / |h| (h が空なら 0)。 -/
def finPr (a h : Finset W) : ℚ :=
  if h.card = 0 then 0 else ((a ∩ h).card : ℚ) / h.card

/-- phase5 の公理 (ax_range_lo/hi, ax_iii_true, def_IX, def_X_left, def_X_right) を有限集合の
上に写したもの。命題は集合、連言は ∩、否定つき連言 p ∧ ¬q は p \ q、選言は ∪ (ax_iii_op は
集合の等号で自明)。ax_iii_true だけは前提が空でないこと (phase6c の Cons h) を要する。
phase5 の公理系と同じではない: iii_true を弱め、ax_iii_op・def_XI を含まず、担体は有限集合の
上の数え上げ確率模型 (ファイル冒頭の §3 の注)。 -/
structure PrLaws (P : Finset W → Finset W → ℚ) : Prop where
  range_lo : ∀ a h, 0 ≤ P a h
  range_hi : ∀ a h, P a h ≤ 1
  iii_true : ∀ h : Finset W, h.Nonempty → P Finset.univ h = 1
  IX : ∀ p q h, P (p \ q) h + P (p ∩ q) h = P p h
  X_left : ∀ p q h, P (p ∩ q) h = P p (q ∩ h) * P q h
  X_right : ∀ p q h, P (p ∩ q) h = P q (p ∩ h) * P p h

omit [Fintype W] in
theorem finPr_X_left (p q h : Finset W) : finPr (p ∩ q) h = finPr p (q ∩ h) * finPr q h := by
  unfold finPr
  by_cases hh : h.card = 0
  · simp [hh]
  by_cases hqh : (q ∩ h).card = 0
  · have h0 : (p ∩ q ∩ h).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc (p ∩ q ∩ h).card ≤ (q ∩ h).card := by
            apply Finset.card_le_card
            intro x; simp only [Finset.mem_inter]; tauto
        _ = 0 := hqh
    rw [if_neg hh, if_pos hqh, zero_mul, h0]
    simp
  · rw [if_neg hh, if_neg hqh, if_neg hh, Finset.inter_assoc]
    have hq' : ((q ∩ h).card : ℚ) ≠ 0 := by exact_mod_cast hqh
    rw [div_mul_div_comm, mul_comm ((q ∩ h).card : ℚ) (h.card : ℚ),
      mul_div_mul_right _ _ hq']

/-- 数え上げ模型は PrLaws を満たす。 -/
theorem finLaws : PrLaws (finPr (W := W)) where
  range_lo a h := by
    unfold finPr; split_ifs <;> positivity
  range_hi a h := by
    unfold finPr
    split_ifs with hh
    · norm_num
    · have hpos : (0 : ℚ) < h.card := by exact_mod_cast Nat.pos_of_ne_zero hh
      rw [div_le_one hpos]
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  iii_true h hne := by
    unfold finPr
    have hh : h.card ≠ 0 := Finset.card_ne_zero.mpr hne
    rw [if_neg hh, Finset.univ_inter]
    exact div_self (by exact_mod_cast hh)
  IX p q h := by
    unfold finPr
    split_ifs with hh
    · norm_num
    · have hc := Finset.card_sdiff_add_card_inter (p ∩ h) q
      have e1 : (p ∩ h) \ q = p \ q ∩ h := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
      have e2 : (p ∩ h) ∩ q = p ∩ q ∩ h := by
        ext x; simp only [Finset.mem_inter]; tauto
      rw [e1, e2] at hc
      rw [← add_div]
      congr 1
      exact_mod_cast hc
  X_left p q h := finPr_X_left p q h
  X_right p q h := by
    rw [Finset.inter_comm p q]
    exact finPr_X_left q p h

/-- (56.2) の等号の例 (4 世界、h = 全体): e = {0, 1}、a₁ = 全体、a₂ = {2}。(a₁ + a₂)/eh = 1、
u = e/h = 1/2、p₁ = e/a₁h = 1/2、p₂ = e/a₂h = 0 (a₂ は空でないが e と両立しない) で
u = p₁ + p₂。c₁ = 1、c₂ = 1/4、0 < u < 1。 -/
theorem th_17_56_2_eq_model :
    finPr (Finset.univ ∪ {2}) ({0, 1} ∩ Finset.univ : Finset (Fin 4)) = 1 ∧
    finPr ({0, 1} : Finset (Fin 4)) Finset.univ = 1 / 2 ∧
    finPr ({0, 1} : Finset (Fin 4)) (Finset.univ ∩ Finset.univ) = 1 / 2 ∧
    finPr ({0, 1} : Finset (Fin 4)) ({2} ∩ Finset.univ) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [finPr] <;> norm_num

/-- **ch17-030 の反例** (folio 189 (56.2)「u < p₁ + p₂」): 印刷の狭義形は phase5 の公理を写した
法則 PrLaws から出ない。PrLaws を満たす数え上げ模型で (56.2) の前提 (a₁ + a₂)/eh = 1 が成り立ち、
u = p₁ + p₂ となる例がある (th_17_56_2_eq_model)。修正形 u ≤ p₁ + p₂ は phase5/th_17_56_2。 -/
theorem th_17_56_2_strict_cm :
    ¬ ∀ P : Finset (Fin 4) → Finset (Fin 4) → ℚ, PrLaws P →
      ∀ a₁ a₂ e h : Finset (Fin 4), h.Nonempty → P (a₁ ∪ a₂) (e ∩ h) = 1 →
        P e h < P e (a₁ ∩ h) + P e (a₂ ∩ h) := by
  intro H
  obtain ⟨hx, hu, hp₁, hp₂⟩ := th_17_56_2_eq_model
  have := H finPr finLaws Finset.univ {2} {0, 1} Finset.univ Finset.univ_nonempty hx
  rw [hu, hp₁, hp₂] at this
  norm_num at this

/-- (56.5) の等号の例 (4 世界 0 = ā₁ā₂, 1 = a₁ā₂, 2 = ā₁a₂, 3 = a₁a₂、h = 全体):
a₁ = {1, 3}、a₂ = {2, 3}、e = {1, 2, 3} (= a₁ + a₂)。a₁/a₂h = 1/2 = a₁/h (独立)、
c₁ = c₂ = 1/2、p₁ = p₂ = 1、u = 3/4 = c₁p₁ + c₂p₂ − c₁c₂ (e/a₁a₂h = 1 なので ch17-036 の
u = c₁p₁ + c₂p₂ − c₁c₂ . e/a₁a₂h が下限に一致する)。 -/
theorem th_17_56_5_eq_model :
    finPr ({1, 3} ∪ {2, 3}) ({1, 2, 3} ∩ Finset.univ : Finset (Fin 4)) = 1 ∧
    finPr ({1, 3} : Finset (Fin 4)) ({2, 3} ∩ Finset.univ) = 1 / 2 ∧
    finPr ({1, 3} : Finset (Fin 4)) Finset.univ = 1 / 2 ∧
    finPr ({2, 3} : Finset (Fin 4)) Finset.univ = 1 / 2 ∧
    finPr ({1, 2, 3} : Finset (Fin 4)) ({1, 3} ∩ Finset.univ) = 1 ∧
    finPr ({1, 2, 3} : Finset (Fin 4)) ({2, 3} ∩ Finset.univ) = 1 ∧
    finPr ({1, 2, 3} : Finset (Fin 4)) Finset.univ = 3 / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [finPr] <;> norm_num

/-- **ch17-037 の反例** (folio 189 (56.5)「∴ u > c₁p₁ + c₂p₂ − c₁c₂」): 印刷の狭義形は PrLaws
から出ない。前提 (a₁ + a₂)/eh = 1 と独立 a₁/a₂h = a₁/h を満たし、u = c₁p₁ + c₂p₂ − c₁c₂ となる
例がある (th_17_56_5_eq_model)。修正形 ≥ は phase5/th_17_56_5。 -/
theorem th_17_56_5_strict_cm :
    ¬ ∀ P : Finset (Fin 4) → Finset (Fin 4) → ℚ, PrLaws P →
      ∀ a₁ a₂ e h : Finset (Fin 4), h.Nonempty → P (a₁ ∪ a₂) (e ∩ h) = 1 →
        P a₁ (a₂ ∩ h) = P a₁ h →
        P e (a₁ ∩ h) * P a₁ h + P e (a₂ ∩ h) * P a₂ h - P a₁ h * P a₂ h < P e h := by
  intro H
  obtain ⟨hx, hi, hc₁, hc₂, hp₁, hp₂, hu⟩ := th_17_56_5_eq_model
  have := H finPr finLaws {1, 3} {2, 3} {1, 2, 3} Finset.univ Finset.univ_nonempty hx
    (by rw [hi, hc₁])
  rw [hu, hp₁, hp₂, hc₁, hc₂] at this
  norm_num at this

end Ch17

end KeynesP15a

/-! ## 判定 (#print axioms) -/

-- 第5章
#print axioms KeynesP15a.th_5_r009
#print axioms KeynesP15a.th_5_r011
#print axioms KeynesP15a.th_5_r016
#print axioms KeynesP15a.th_5_r017
#print axioms KeynesP15a.th_5_r022
#print axioms KeynesP15a.th_5_r017_needs_trans
-- 第8章
#print axioms KeynesP15a.th_8_r009
#print axioms KeynesP15a.th_8_r010
#print axioms KeynesP15a.th_8_r011
#print axioms KeynesP15a.th_8_r022
#print axioms KeynesP15a.th_8_r023_freq
#print axioms KeynesP15a.th_8_r026
#print axioms KeynesP15a.th_8_r010_needs_013
#print axioms KeynesP15a.th_8_r010_needs_014
#print axioms KeynesP15a.th_8_r023_freq_needs_024
#print axioms KeynesP15a.ax_freq_eq_prob_sat
#print axioms KeynesP15a.th_8_r024
#print axioms KeynesP15a.th_8_r024_needs_ax
#print axioms KeynesP15a.th_24_i
#print axioms KeynesP15a.th_8_r023
-- 第17章
#print axioms KeynesP15a.finLaws
#print axioms KeynesP15a.th_17_56_2_eq_model
#print axioms KeynesP15a.th_17_56_2_strict_cm
#print axioms KeynesP15a.th_17_56_5_eq_model
#print axioms KeynesP15a.th_17_56_5_strict_cm
