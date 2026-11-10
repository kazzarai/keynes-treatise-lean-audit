/-
# Keynes (1921) *A Treatise on Probability* Part I — Lean 4 Phase 17 (closing)
#
# **全数判定の締め (B51): 台帳の Lean 欄が裸の「未」だった式行のうち、判定を付けた行の定義と定理**
#
# ## 目的
#   台帳 (docs/全数台帳) の式行で Lean 欄が理由のない「未」だった 35 行を、判定を付けるか
#   「未 (分類: 理由)」に書き換えて締める。本ファイルはそのうち判定を付けた第4章・第6章の行の
#   定義 (名付け) と、例の仮定を前提として運ぶ定理、および 未 (境界) とした ch06-014 の
#   独立性 (重みの公理から出ず、反証もされない) を述べる。
#   担体は phase6c・phase13a と同じ内包的担体 (IProp・PrI) で、必要な宣言だけを再掲する。
#   重みの構造 WeightStructure と KeynesPr・Mono・Compl・Equiv は phase8dp と同文の再掲。
#   比較不能 Incomp は phase12a と同文の再掲。
#
# ## 原典 (唯一の基準、1921 Macmillan 初版) の該当箇所
#   folio 48 (第4章 §7): 「if x and f(x) are both continuous variables, ... and x must lie
#     between a and b, then the probability that x lies between c and d, where a < c < d < b,
#     seems to be (d − c)/(b − a)」
#   folio 57 (第4章 §17): 「Let us write the alternative ‘The proportion of black balls is x’
#     ≡ φ(x), and the datum ‘There are n balls in the bag, with regard to none of which it is
#     known whether they are black or white’ ≡ h.」
#   folio 60 (第4章 §21): 「i.e. φ(x) ≡ x is the only propositional function common to all
#     of them」; folio 61–62 (§§23–25): 「φ(x) ≡ ‘the individual is an inhabitant of country
#     x’」「for instance, where φ(x) ≡ x」「‘the interval of length l on which the point lies
#     is the xth interval of that length as we move along the line from left to right’ ≡ φ(x)」
#   folio 72 (第6章 §3): 「(ii.) a/hh₁ ⋛ a/h, where h₁ is a single unit of information」
#   folio 73 (第6章 §3): 「It might be thought that V(ab/h) < V(a/h), ... But this is invalid.
#     The argument ab/h is further off proof than was the argument a/h; but it is nearer
#     disproof. For example, if ab/h = 0 and a/h > 0, then V(ab/h) > V(a/h).」
#
# ## 本ファイルの判定対象 (台帳の行 → Lean)
#   ch04-085  定  phi_4_17      ch04-086  定  datum_4_17
#   ch04-113  定  phi_4_21      ch04-124  定  phi_4_21 (ch04-113 の再掲)
#   ch04-123  定  phi_4_23      ch04-126  定  phi_4_25
#   ch04-032  定  th_4_7_r032 (前提 h032)
#   ch06-002  ≈  th_6_r002 (ℝ 値の PrI で三分律); Π では th_6_r002_pi_incomp (比較不能がありうる)
#   ch06-012  定  th_6_r012_r013 (前提 h012)     ch06-013  定  th_6_r012_r013 (前提 h013)
#   ch06-014  未 (境界) — th_6_r014_not_derivable と th_6_r014_consistent (公理から独立)
#   ch06-009  未 (Keynes が却下) — 参考 th_6_r009_rule_fails (その規則は公理の模型で破れる)
#
# ## 予測: 全定理は Lean の標準の三公理 (propext, Classical.choice, Quot.sound) と、本ファイルの
#   担体の宣言 (IProp・iand・PrI) のうち文に現れるものだけに依存する。Keynes の確率の公理
#   (def_IX_i 等) は使わない。
-/

import Mathlib

noncomputable section
namespace KeynesClosing

/-! ## 内包的担体 (phase6c・phase13a と同文の宣言のうち、本ファイルで使うもの) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom PrI : IProp → IProp → ℝ

/-! ## 第4章 §§17, 21, 23, 25 — ≡ による命題関数の名付け (定) -/

/-- **ch04-085 (定)**: ‘The proportion of black balls is x’ ≡ φ(x)。
命題「黒球の割合は x」の族 black を受け取り、φ をその名付けとする (定義のみ)。 -/
def phi_4_17 (black : ℝ → IProp) : ℝ → IProp := black

/-- **ch04-086 (定)**: ‘There are n balls in the bag, with regard to none of which it is known
whether they are black or white’ ≡ h。球の数 n ごとの資料の命題 bag n の名付け (定義のみ)。 -/
def datum_4_17 (bag : ℕ → IProp) (n : ℕ) : IProp := bag n

/-- **ch04-113・ch04-124 (定)**: φ(x) ≡ x。選択肢の命題そのものを返す命題関数
(「the only propositional function common to all of them」; 124 は 113 の再掲)。 -/
def phi_4_21 : IProp → IProp := fun x => x

/-- **ch04-123 (定)**: φ(x) ≡ ‘the individual is an inhabitant of country x’。
国の型 C と命題の族 inhabitant を受け取り、φ をその名付けとする (定義のみ)。 -/
def phi_4_23 {C : Type} (inhabitant : C → IProp) : C → IProp := inhabitant

/-- **ch04-126 (定)**: ‘the interval of length l on which the point lies is the xth interval
of that length as we move along the line from left to right’ ≡ φ(x)。
長さ l と番号 x の命題の族 onInterval を受け取り、l を固めた族を φ と名付ける (定義のみ)。 -/
def phi_4_25 (onInterval : ℝ → ℕ → IProp) (l : ℝ) : ℕ → IProp := onInterval l

/-! ## 第4章 §7 — 連続変数の例の仮定 a < c < d < b (定) -/

/-- **ch04-032 (定: 例の仮定)**: a < c < d < b を前提 h032 として運ぶ。その下で
(d − c)/(b − a) (ch04-033、記法) は 0 と 1 の間にある (確率の値の範囲に入る)。 -/
theorem th_4_7_r032 (a b c d : ℝ) (h032 : a < c ∧ c < d ∧ d < b) :
    0 < (d - c) / (b - a) ∧ (d - c) / (b - a) < 1 := by
  obtain ⟨h1, h2, h3⟩ := h032
  have hba : 0 < b - a := by linarith
  refine ⟨div_pos (by linarith) hba, ?_⟩
  rw [div_lt_one hba]
  linarith

/-! ## 第6章 §3 (ii.) — a/hh₁ ⋛ a/h (≈; Π では比較不能がありうる) -/

/-- **ch06-002 (≈)**: a/hh₁ ⋛ a/h (「greater than, equal to, or less than」)。
ℝ 値の PrI では三分律 (lt_trichotomy) でそのまま成り立つ。前提の並置 hh₁ は iand h h₁。 -/
theorem th_6_r002 (a h h₁ : IProp) :
    PrI a (iand h h₁) > PrI a h ∨ PrI a (iand h h₁) = PrI a h ∨ PrI a (iand h h₁) < PrI a h := by
  rcases lt_trichotomy (PrI a (iand h h₁)) (PrI a h) with hl | he | hg
  · exact Or.inr (Or.inr hl)
  · exact Or.inr (Or.inl he)
  · exact Or.inl hg

/-- 比較不能 (phase12a と同文): x ≤ y でも y ≤ x でもない。 -/
def Incomp {D : Type} [LE D] (x y : D) : Prop := ¬ x ≤ y ∧ ¬ y ≤ x

/-- **ch06-002 の Π 側**: 確率集合 Π を半順序の型にすると、a/hh₁ と a/h は比較不能になりうる
(第3章 §20 folio 39 の「not comparable」)。値の型は Bool × Bool (成分ごとの順序、
O = (false, false)、I = (true, true))、命題の型は Bool、前提の並置は (&&)。a = h = true、
h₁ = false で a/hh₁ = (false, true)、a/h = (true, false)。このとき ⋛ の三つのどれも成り立たない。 -/
theorem th_6_r002_pi_incomp :
    ∃ (Γ : Type) (and_ : Γ → Γ → Γ) (Pr : Γ → Γ → Bool × Bool) (a h h₁ : Γ),
      (∀ p k, ((false, false) : Bool × Bool) ≤ Pr p k ∧ Pr p k ≤ (true, true)) ∧
      Incomp (Pr a (and_ h h₁)) (Pr a h) ∧
      ¬ (Pr a (and_ h h₁) > Pr a h ∨ Pr a (and_ h h₁) = Pr a h ∨ Pr a (and_ h h₁) < Pr a h) := by
  refine ⟨Bool, (· && ·), fun _ k => if k then (true, false) else (false, true),
    true, true, false, ?_, ?_, ?_⟩
  · intro p k
    cases k <;> simp [Prod.le_def]
  · simp [Incomp, Prod.le_def]
  · simp [Prod.lt_iff]

/-! ## 第6章 §3 — 反例の前提 ab/h = 0, a/h > 0 (定) -/

/-- **ch06-012・ch06-013 (定: 例の仮定)**: ab/h = 0 (前提 h012) と a/h > 0 (前提 h013) を運ぶ。
その下で ab/h < a/h (「The argument ab/h is further off proof than was the argument a/h」)。 -/
theorem th_6_r012_r013 (a b h : IProp) (h012 : PrI (iand a b) h = 0) (h013 : 0 < PrI a h) :
    PrI (iand a b) h < PrI a h := by
  rw [h012]
  exact h013

/-! ## 第6章 §3 — V(ab/h) > V(a/h) (ch06-014) は重みの公理から独立

phase8dp と同文の重みの構造。命題の型 Γ 上の結合子、第二段の値 Pr、第三段の値 V。 -/

/-- 第6章の三段の写像をまとめた構造 (phase8dp と同文)。 -/
structure WeightStructure (Γ : Type) where
  and_ : Γ → Γ → Γ
  or_  : Γ → Γ → Γ
  not_ : Γ → Γ
  Pr : Γ → Γ → ℝ
  V  : Γ → Γ → ℝ

namespace WeightStructure

variable {Γ : Type} (S : WeightStructure Γ)

/-- 第二段の公理 (def_IX_i, def_X_left_i, def_X_right_i, ax_range) の構造版 (phase8dp と同文)。 -/
def KeynesPr : Prop :=
  (∀ p q h, S.Pr (S.and_ p (S.not_ q)) h + S.Pr (S.and_ p q) h = S.Pr p h) ∧
  (∀ p q h, S.Pr (S.and_ p q) h = S.Pr p (S.and_ q h) * S.Pr q h) ∧
  (∀ p q h, S.Pr (S.and_ p q) h = S.Pr q (S.and_ p h) * S.Pr p h) ∧
  (∀ p h, 0 ≤ S.Pr p h) ∧ (∀ p h, S.Pr p h ≤ 1)

/-- ax_vi_mono_i の構造版 (phase8dp と同文)。 -/
def Mono : Prop := ∀ a h h₁, S.V a h ≤ S.V a (S.and_ h h₁)
/-- ax_vi_compl_i の構造版 (phase8dp と同文)。 -/
def Compl : Prop := ∀ a h, S.V a h = S.V (S.not_ a) h
/-- ax_vi_equiv_i の構造版 (phase8dp と同文)。 -/
def Equiv : Prop := ∀ a b h,
  S.Pr a (S.and_ b h) = 1 → S.Pr b (S.and_ a h) = 1 → S.V a h = S.V b h

end WeightStructure

/-! ### 2 世界の有限模型: 命題は Bool × Bool (世界 0・世界 1 で真か)、
Pr(a/h) = |a ∩ h| / |h| (h が空なら 0)、V は二通り。 -/

/-- 命題の連言・選言・否定 (世界ごと)。 -/
def and2 (p q : Bool × Bool) : Bool × Bool := (p.1 && q.1, p.2 && q.2)
def or2 (p q : Bool × Bool) : Bool × Bool := (p.1 || q.1, p.2 || q.2)
def not2 (p : Bool × Bool) : Bool × Bool := (!p.1, !p.2)

/-- 命題が真である世界の数。 -/
def cnt (p : Bool × Bool) : ℝ := (if p.1 then 1 else 0) + (if p.2 then 1 else 0)

/-- 数え上げの確率 a/h (h が空なら 0)。 -/
def pr2 (p h : Bool × Bool) : ℝ := if cnt h = 0 then 0 else cnt (and2 p h) / cnt h

/-- h が a を証明または反証する (h ⊆ a または a ∩ h = ∅)。 -/
def decides2 (a h : Bool × Bool) : Bool :=
  ((!h.1 || a.1) && (!h.2 || a.2)) || (and2 a h == (false, false))

/-- 重み V₁(a/h) = (h と両立しない世界の数) + [h が a を証明または反証する] (phase8dp の V₁ と同じ形)。 -/
def V12 (a h : Bool × Bool) : ℝ := (2 - cnt h) + (if decides2 a h then 1 else 0)

/-- 模型: 重みが V₁ のもの。 -/
def model1 : WeightStructure (Bool × Bool) where
  and_ := and2
  or_ := or2
  not_ := not2
  Pr := pr2
  V := V12

/-- 模型: 重みが恒等的に 0 のもの。 -/
def model0 : WeightStructure (Bool × Bool) where
  and_ := and2
  or_ := or2
  not_ := not2
  Pr := pr2
  V := fun _ _ => 0

/-- 2 世界の数え上げの確率は第二段の公理 (KeynesPr) を満たす (重みによらない)。 -/
theorem pr2_KeynesPr (Vf : Bool × Bool → Bool × Bool → ℝ) :
    (WeightStructure.mk and2 or2 not2 pr2 Vf).KeynesPr := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ <;> norm_num [pr2, cnt, and2, not2]
  · rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ <;> norm_num [pr2, cnt, and2]
  · rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ <;> norm_num [pr2, cnt, and2]
  · rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ <;> norm_num [pr2, cnt, and2]
  · rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ <;> norm_num [pr2, cnt, and2]

theorem model1_KeynesPr : model1.KeynesPr := pr2_KeynesPr V12
theorem model0_KeynesPr : model0.KeynesPr := pr2_KeynesPr _

theorem model1_Mono : model1.Mono := by
  rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ <;>
    norm_num [model1, V12, cnt, decides2, and2]

theorem model1_Compl : model1.Compl := by
  rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ <;> norm_num [model1, V12, cnt, decides2, and2, not2]

theorem model1_Equiv : model1.Equiv := by
  rintro ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ ⟨_ | _, _ | _⟩ <;>
    norm_num [model1, V12, pr2, cnt, decides2, and2]

theorem model0_Mono : model0.Mono := fun _ _ _ => le_refl _
theorem model0_Compl : model0.Compl := fun _ _ => rfl
theorem model0_Equiv : model0.Equiv := fun _ _ _ _ _ => rfl

/-- **ch06-014 は重みの公理から出ない**: 第二段の公理 (KeynesPr) と重みの公理 (Mono・Compl・
Equiv) を満たす模型 (V ≡ 0) で、ab/h = 0 (ch06-012) と a/h > 0 (ch06-013) が成り立つのに
V(ab/h) > V(a/h) は成り立たない。a = 世界 0 だけで真、b = 世界 1 だけで真、h = 両方で真。 -/
theorem th_6_r014_not_derivable :
    ∃ S : WeightStructure (Bool × Bool), S.KeynesPr ∧ S.Mono ∧ S.Compl ∧ S.Equiv ∧
      ∃ a b h, S.Pr (S.and_ a b) h = 0 ∧ 0 < S.Pr a h ∧ ¬ S.V (S.and_ a b) h > S.V a h := by
  refine ⟨model0, model0_KeynesPr, model0_Mono, model0_Compl, model0_Equiv,
    (true, false), (false, true), (true, true), ?_, ?_, ?_⟩
  · norm_num [model0, pr2, cnt, and2]
  · norm_num [model0, pr2, cnt, and2]
  · simp [model0]

/-- **ch06-014 は重みの公理で反証されない**: 同じ公理を満たす別の模型 (V = V₁: h と両立しない
世界の数 + h が結論を証明または反証すれば 1) では、同じ a, b, h で V(ab/h) = 1 > 0 = V(a/h)。
th_6_r014_not_derivable と合わせ、ch06-014 は重みの公理から独立 (V と「反証に近い」を結ぶ
公理を外から足さなければ定理にならない)。 -/
theorem th_6_r014_consistent :
    ∃ S : WeightStructure (Bool × Bool), S.KeynesPr ∧ S.Mono ∧ S.Compl ∧ S.Equiv ∧
      ∃ a b h, S.Pr (S.and_ a b) h = 0 ∧ 0 < S.Pr a h ∧ S.V (S.and_ a b) h > S.V a h := by
  refine ⟨model1, model1_KeynesPr, model1_Mono, model1_Compl, model1_Equiv,
    (true, false), (false, true), (true, true), ?_, ?_, ?_⟩
  · norm_num [model1, pr2, cnt, and2]
  · norm_num [model1, pr2, cnt, and2]
  · norm_num [model1, V12, cnt, decides2, and2]

/-- **ch06-009 (Keynes が却下) の参考**: 「V(ab/h) < V(a/h)」を規則 (すべての a, b, h で) と
すると、重みの公理の模型 model1 で破れる (a = 世界 0 だけ、b = 世界 1 だけ、h = 両方)。
Keynes の「But this is invalid」に当たる。 -/
theorem th_6_r009_rule_fails :
    ∃ S : WeightStructure (Bool × Bool), S.KeynesPr ∧ S.Mono ∧ S.Compl ∧ S.Equiv ∧
      ¬ ∀ a b h, S.V (S.and_ a b) h < S.V a h := by
  refine ⟨model1, model1_KeynesPr, model1_Mono, model1_Compl, model1_Equiv, ?_⟩
  intro H
  have := H (true, false) (false, true) (true, true)
  norm_num [model1, V12, cnt, decides2, and2] at this

end KeynesClosing

/-! ## 監査クエリ -/
#print axioms KeynesClosing.phi_4_17
#print axioms KeynesClosing.datum_4_17
#print axioms KeynesClosing.phi_4_21
#print axioms KeynesClosing.phi_4_23
#print axioms KeynesClosing.phi_4_25
#print axioms KeynesClosing.th_4_7_r032
#print axioms KeynesClosing.th_6_r002
#print axioms KeynesClosing.th_6_r002_pi_incomp
#print axioms KeynesClosing.th_6_r012_r013
#print axioms KeynesClosing.pr2_KeynesPr
#print axioms KeynesClosing.model1_Mono
#print axioms KeynesClosing.model1_Compl
#print axioms KeynesClosing.model1_Equiv
#print axioms KeynesClosing.th_6_r014_not_derivable
#print axioms KeynesClosing.th_6_r014_consistent
#print axioms KeynesClosing.th_6_r009_rule_fails
