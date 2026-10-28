/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 10f
# 第 XI 章 "The Theory of Groups, with special reference to Logical Consistence,
# Inference, and Logical Priority" (folio 123–132)
#
# 基準: 1921 年 Macmillan 初版の頁画像 (folio 125, 128, 129, 130, 131 を直接照合)。
# 台帳: docs/全数台帳/ch11.md の式行 30 本 (ch11-001 … ch11-035)。
#
# ## 構成
#   §0  内包的な命題集合 IProp と確率関係 PrI — phase6c の公理群の部分集合
#       (def_VIII_i・def_VIII_i_src・def_XI_i・cons_true・cons_iff_taut を置かない;
#       各 phase は自己完結)。担体は IProp、`Prop → Prop → ℝ` 型の確率関係は置かない。
#   §1  phase6c の補題の写し (itrue_certain, true_conj, th_13_1_i, taut_neg_zero,
#       conj_neg_cert_zero) と、群の閉包の補題 (conj_certain, cons_iff_pos)
#   §2  §9 (folio 128): 確実性 a/h = 1、不可能性 a/h = 0、γ・ω の積と和、≠ と < >
#   §3  §11 (folio 129): 要求 (requirement)、群 h の中での要求
#   §4  §12 (folio 130): 仮言的推論 'If p, q'、断定的推論 'p ∴ q'
#   §5  §13 (folio 130–131): p/h = a の読み、絶対的に確実・不可能、一般化された要求
#
# ## 群の読み (folio 125 §6)
# 「群 (group)」は (i.)(ii.)(iii.) の三条件で語で定義される (式ではないので台帳に数えない)。
# 本ファイルは「h が指定する群」を {a | a/h = 1} (h は整合、Cons h) と読み、
# th_11_027 でこの集合が条件 (ii.)「p と 'p implies q' が属すれば q も属す」と
# (iii.)「p が属すれば p の否定は排除される」を満たすことを示す。(i.) (形式的真理の
# 代入例) は Ax.(iii) (ax_iii_taut) の形で入っている。
#
# ## 実在群 (real group) の読み (folio 129 §11)
# 実在群 = 基礎的集合が真と知られている群。Keynes は「what follows will be equally valid
# whatever criterion is taken, so long as the fundamental set is in some manner or other
# determined uniquely」と書くので、基準を公理化せず、述語 R : IProp → Prop を定義の
# パラメータとして置く (RealGroup R h := R h ∧ Cons h)。新しい公理は置かない。
#
# ## 形式化の境界 (台帳の備考に転記)
#   * 前提側の置換 (h′/h = 1 のとき h ≡ hh′) は KeynesI に無いので、部分群の推移性
#     (h′/h = 1, p/h′ = 1 ⊢ p/h = 1) は導けない。一般化された要求 (folio 131) が §11 の
#     要求に「帰着する」主張は、一般化 ⇒ §11 の向きを p/h = 1 (印刷の条件) と h/h = 1
#     (追加の前提) のもとで示し (th_11_035)、逆向きは示さない。
#   * a/a = 1 (前提 a) は KeynesI で未導出なので、h/h = 1 は定理の前提として置く。
#     th_11_035 から h/h = 1 を外すと偽になる反例モデル (§0 の公理をすべて満たす) を
#     nec_11_035_hh に置く。
#   * ch11-026 (p/h = a) は名付けの行 (定義のみ) なので定理を置かない。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase10f.lean
-/

import Mathlib

namespace KeynesXI

/-! ## §0 内包的キャリアと結合子 (phase6c の写し) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- **整合性述語** `Cons h`: 「h は矛盾する連言でない」(folio 135、公理 (i))。
第 XI 章の語では「h は自己整合で、したがって群を指定する」(folio 130 §13:
「it is postulated that h is self-consistent and therefore specifies a group」)。 -/
axiom Cons : IProp → Prop

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- 命題論理の構文 (phase6c と同一)。 -/
inductive Form : Type where
  | var  : ℕ → Form
  | tru  : Form
  | fls  : Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | neg  : Form → Form
  | iffF : Form → Form → Form

/-- Boolean 評価 (phase6c と同一)。 -/
def evalB (v : ℕ → Bool) : Form → Bool
  | .var n    => v n
  | .tru      => true
  | .fls      => false
  | .conj f g => evalB v f && evalB v g
  | .disj f g => evalB v f || evalB v g
  | .neg f    => !(evalB v f)
  | .iffF f g => evalB v f == evalB v g

/-- 形式的に真 (phase6c と同一)。 -/
def Taut (f : Form) : Prop := ∀ v : ℕ → Bool, evalB v f = true

/-- 構文の内包的解釈 (phase6c と同一)。 -/
noncomputable def interp (env : ℕ → IProp) : Form → IProp
  | .var n    => env n
  | .tru      => itrue
  | .fls      => inot itrue
  | .conj f g => iand (interp env f) (interp env g)
  | .disj f g => ior (interp env f) (interp env g)
  | .neg f    => inot (interp env f)
  | .iffF f g => iiff (interp env f) (interp env g)

/-- **Ax.(iii)、但し書き付き** (phase6c と同一)。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

/-- **ah 整合ならば a/h ≠ 0** (phase6c と同一、Def. VI 印刷の向き、folio 134)。 -/
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0

/-- **a/h ≠ 0 かつ h 整合ならば ah 整合** (phase6c と同一、Def. VI の逆向き)。 -/
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)

/-! ## §1 補題 (phase6c の写し) と群の閉包 -/

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

/-- 補完律 a/h + \bar{a}/h = 1 (第13章の (1)、folio 139; phase6c の写し)。 -/
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

/-- **群は連言で閉じる**: p/h = 1, q/h = 1 ならば pq/h = 1 (h 整合)。
Def. IX で p/h = p\bar{q}/h + pq/h、p\bar{q}/h = 0 (q は確実)。 -/
theorem conj_certain (p q h : IProp) (hc : Cons h) (hp : PrI p h = 1) (hq : PrI q h = 1) :
    PrI (iand p q) h = 1 := by
  have s := def_IX_i p q h
  rw [conj_neg_cert_zero p q h hc hq] at s
  linarith

/-- **ph が群を指定すること ⇔ p/h ≠ 0** (h 整合)。cons_of_pos_src と cons_of_pos の対。 -/
theorem cons_iff_pos (p h : IProp) (hc : Cons h) : Cons (iand p h) ↔ PrI p h ≠ 0 :=
  ⟨cons_of_pos_src p h, fun hp => cons_of_pos p h hp hc⟩

/-! ## §2 第 XI 章 §9 (folio 128): 確実性・不可能性の記号 -/

/-- h が指定する群: {a | a/h = 1} (folio 128: 「included in the group specified by h,
this is denoted by a/h = 1」)。h が整合 (Cons h) のときに群の条件を満たす (th_11_027)。 -/
def groupOf (h : IProp) : Set IProp := {a | PrI a h = 1}

/-- **ch11-001** a/h = 1 (folio 128 §9): 「If a follows from h and is, therefore, included
in the group specified by h, this is denoted by a/h = 1.」
「a が h から帰結する」を、前提 h が g h₀ の形で g が a を形式的に含意する
(¬(\bar{a} g) が形式的に真) ことと読む。前提 g h₀ は整合 (群を指定する) とする。 -/
theorem th_11_001 (f g : Form) (env : ℕ → IProp) (h₀ : IProp) (hc₀ : Cons h₀)
    (hcg : Cons (iand (interp env g) h₀))
    (hfol : Taut (Form.neg (Form.conj (Form.neg f) g))) :
    PrI (interp env f) (iand (interp env g) h₀) = 1 ∧
      interp env f ∈ groupOf (iand (interp env g) h₀) := by
  have z : PrI (iand (inot (interp env f)) (interp env g)) h₀ = 0 :=
    taut_neg_zero (Form.conj (Form.neg f) g) env h₀ hc₀ hfol
  rw [def_X_left_i] at z
  have hg : PrI (interp env g) h₀ ≠ 0 := cons_of_pos_src _ _ hcg
  have hn : PrI (inot (interp env f)) (iand (interp env g) h₀) = 0 := by
    rcases mul_eq_zero.mp z with h1 | h1
    · exact h1
    · exact absurd h1 hg
  have hs := th_13_1_i (interp env f) (iand (interp env g) h₀) hcg
  have h1 : PrI (interp env f) (iand (interp env g) h₀) = 1 := by linarith
  exact ⟨h1, h1⟩

/-- **ch11-003** a . γ = a (folio 128 §9): γ は確実性の関係。積は Def. X (第 XII 章で定義)
の意味: a := a/h、γ := c/ah とおくと、a . γ = (ac)/h であり、γ = 1 のとき a . γ = a。 -/
theorem th_11_003 (a c h : IProp) (hγ : PrI c (iand a h) = 1) :
    PrI a h * PrI c (iand a h) = PrI a h ∧ PrI (iand a c) h = PrI a h := by
  refine ⟨by rw [hγ, mul_one], ?_⟩
  rw [def_X_right_i a c h, hγ, one_mul]

/-- **ch11-004** a/h = 0 (folio 128 §9): 「if a is excluded from the group specified by h
… this is denoted by a/h = 0」; 排除 = 「its contradictory follows from the premiss」。
h 整合のもとで a/h = 0 ⇔ \bar{a}/h = 1。 -/
theorem th_11_004 (a h : IProp) (hc : Cons h) : PrI a h = 0 ↔ PrI (inot a) h = 1 := by
  have := th_13_1_i a h hc
  constructor <;> intro h1 <;> linarith

/-- **ch11-006** a . ω = ω (folio 128 §9): ω は不可能性の関係。a := a/h、ω := c/ah とおくと
ω = 0 のとき a . ω = ω、かつ積 (ac)/h は 0。 -/
theorem th_11_006 (a c h : IProp) (hω : PrI c (iand a h) = 0) :
    PrI a h * PrI c (iand a h) = PrI c (iand a h) ∧ PrI (iand a c) h = 0 := by
  refine ⟨by rw [hω, mul_zero], ?_⟩
  rw [def_X_right_i a c h, hω, zero_mul]

/-- **ch11-007** a + ω = a (folio 128 §9): 和は Def. IX (第 XII 章で定義) の意味。
a := p\bar{q}/h、ω := pq/h とおくと、ω = 0 のとき a + ω = a であり、a は p/h に等しい。 -/
theorem th_11_007 (p q h : IProp) (hω : PrI (iand p q) h = 0) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI (iand p (inot q)) h ∧
      PrI (iand p (inot q)) h = PrI p h := by
  have s := def_IX_i p q h
  refine ⟨by rw [hω, add_zero], ?_⟩
  rw [hω, add_zero] at s
  exact s

/-- **ch11-008** a/h ≠ 1 (folio 128 §9): 「if a is not included in the group specified by h,
this is written a/h ≠ 1」。h 整合のもとで、a が群に含まれないこと ⇔ \bar{a} が排除されないこと。 -/
theorem th_11_008 (a h : IProp) (hc : Cons h) : PrI a h ≠ 1 ↔ PrI (inot a) h ≠ 0 := by
  have := th_13_1_i a h hc
  constructor
  · intro h1 h2; exact h1 (by linarith)
  · intro h1 h2; exact h1 (by linarith)

/-- **ch11-009** a/h < 1 (folio 128 §9): 「a/h ≠ 1 or a/h < 1」— 二つの書き方は同値。 -/
theorem th_11_009 (a h : IProp) : PrI a h ≠ 1 ↔ PrI a h < 1 :=
  ⟨fun h1 => lt_of_le_of_ne (ax_range_hi_i a h) h1, fun h1 => ne_of_lt h1⟩

/-- **ch11-010** a/h ≠ 0 (folio 128 §9): 「if it is not excluded, this is written a/h ≠ 0」。
h 整合のもとで、a が排除されないこと ⇔ \bar{a} が群に含まれないこと。 -/
theorem th_11_010 (a h : IProp) (hc : Cons h) : PrI a h ≠ 0 ↔ PrI (inot a) h ≠ 1 := by
  have := th_13_1_i a h hc
  constructor
  · intro h1 h2; exact h1 (by linarith)
  · intro h1 h2; exact h1 (by linarith)

/-- **ch11-011** a/h > 0 (folio 128 §9): 「a/h ≠ 0 or a/h > 0」— 二つの書き方は同値。 -/
theorem th_11_011 (a h : IProp) : PrI a h ≠ 0 ↔ PrI a h > 0 :=
  ⟨fun h1 => lt_of_le_of_ne (ax_range_lo_i a h) (Ne.symm h1), fun h1 => ne_of_gt h1⟩

/-! ## §3 第 XI 章 §11 (folio 129): 要求 (requirement) -/

/-- 実在群 (real group): 基礎的集合が実在の基準 R を満たし、整合な群。 -/
def RealGroup (R : IProp → Prop) (h : IProp) : Prop := R h ∧ Cons h

/-- 「p does not require q」(folio 129): 「if there is a real group h such that
p/h = 1, q/h ≠ 1」。 -/
def NotRequires (R : IProp → Prop) (p q : IProp) : Prop :=
  ∃ h, RealGroup R h ∧ PrI p h = 1 ∧ PrI q h ≠ 1

/-- 「p requires q」(folio 129): 「if there is no real group to which p belongs and q does
not belong」。 -/
def Requires (R : IProp → Prop) (p q : IProp) : Prop := ¬ NotRequires R p q

/-- 「p does not require q within the group h」(folio 129): 「if there is a group h′ such
that h′/h = 1, p/h′ = 1, q/h′ ≠ 1」。h′ は群 (整合) とする。
印刷は p/h = 1 (p belongs to h) を前提に置く。定理 th_11_035 では仮定している
(定義の本体には入れない)。 -/
def NotRequiresWithin (h p q : IProp) : Prop :=
  ∃ h', Cons h' ∧ PrI h' h = 1 ∧ PrI p h' = 1 ∧ PrI q h' ≠ 1

/-- **ch11-012** p/h = 1 (folio 129 §11): p が q を要求するなら、p が属する実在群 h には
q も属する (定義の対偶)。 -/
theorem th_11_012 (R : IProp → Prop) (p q h : IProp) (hreq : Requires R p q)
    (hh : RealGroup R h) (hp : PrI p h = 1) : PrI q h = 1 := by
  by_contra hq
  exact hreq ⟨h, hh, hp, hq⟩

/-- **ch11-013** q/h ≠ 1 (folio 129 §11): 実在群 h で p/h = 1, q/h ≠ 1 ならば p は q を
要求せず、q/h < 1。 -/
theorem th_11_013 (R : IProp → Prop) (p q h : IProp) (hh : RealGroup R h)
    (hp : PrI p h = 1) (hq : PrI q h ≠ 1) : NotRequires R p q ∧ PrI q h < 1 :=
  ⟨⟨h, hh, hp, hq⟩, (th_11_009 q h).mp hq⟩

/-- 要求は反射的。 -/
theorem requires_refl (R : IProp → Prop) (p : IProp) : Requires R p p := by
  rintro ⟨h, _, hp, hq⟩
  exact hq hp

/-- 要求は推移的。 -/
theorem requires_trans (R : IProp → Prop) (p q r : IProp)
    (hpq : Requires R p q) (hqr : Requires R q r) : Requires R p r := by
  rintro ⟨h, hh, hp, hr⟩
  exact hr (th_11_012 R q r h hqr hh (th_11_012 R p q h hpq hh hp))

/-- **ch11-014** h′/h = 1 (folio 129 §11): 「This reduces to the proposition next but one
above if h is the Universe of Reference.」U を参照の宇宙 (実在群 = U に含まれる整合な群)
とすると、群 U の中での非要求は §11 の非要求と同値。 -/
theorem th_11_014 (R : IProp → Prop) (U p q : IProp)
    (hU : ∀ k, Cons k → (R k ↔ PrI k U = 1)) :
    (∃ h', Cons h' ∧ PrI h' U = 1 ∧ PrI p h' = 1 ∧ PrI q h' ≠ 1) ↔ NotRequires R p q := by
  constructor
  · rintro ⟨h', hc', h1, hp, hq⟩
    exact ⟨h', ⟨(hU h' hc').mpr h1, hc'⟩, hp, hq⟩
  · rintro ⟨h, ⟨hR, hc⟩, hp, hq⟩
    exact ⟨h, hc, (hU h hc).mp hR, hp, hq⟩

/-- **ch11-015** p/h′ = 1 (folio 129 §11): 部分群 h′ (h′/h = 1) で p/h′ = 1, q/h′ ≠ 1
ならば、群 h の中で p は q を要求しない。 -/
theorem th_11_015 (h h' p q : IProp) (hc' : Cons h') (h1 : PrI h' h = 1)
    (hp : PrI p h' = 1) (hq : PrI q h' ≠ 1) : NotRequiresWithin h p q :=
  ⟨h', hc', h1, hp, hq⟩

/-- **ch11-016** q/h′ ≠ 1 (folio 129 §11): 部分群 h′ で p/h′ = 1, q/h′ ≠ 1 のとき、
p と \bar{q} の連言は h′ から排除されず、\bar{q}ph′ は整合 (p を知って q を知らないことが
できる)。 -/
theorem th_11_016 (h' p q : IProp) (hc' : Cons h') (hp : PrI p h' = 1) (hq : PrI q h' ≠ 1) :
    PrI (iand (inot q) p) h' ≠ 0 ∧ Cons (iand (iand (inot q) p) h') := by
  have s := def_IX_i (inot q) p h'
  rw [conj_neg_cert_zero (inot q) p h' hc' hp, zero_add] at s
  have hnq : PrI (inot q) h' ≠ 0 := (th_11_008 q h' hc').mp hq
  have hne : PrI (iand (inot q) p) h' ≠ 0 := by rw [s]; exact hnq
  exact ⟨hne, cons_of_pos _ _ hne hc'⟩

/-! ## §4 第 XI 章 §12 (folio 130): 推論 -/

/-- 仮言的推論 'If p, q' (folio 130): 「there is a real group h such that q/ph = 1, and
q/h ≠ 1. In order that this may be the case, ph must specify a group」。
ph が群を指定すること (Cons (ph)) を定義に含める。 -/
def HypInf (R : IProp → Prop) (p q : IProp) : Prop :=
  ∃ h, RealGroup R h ∧ Cons (iand p h) ∧ PrI q (iand p h) = 1 ∧ PrI q h ≠ 1

/-- 断定的推論 'p ∴ q' (folio 130): 「'if p, q' is true, and in addition 'p' belongs to a
real group」。 -/
def AssInf (R : IProp → Prop) (p q : IProp) : Prop :=
  (∃ h, RealGroup R h ∧ PrI p h = 1) ∧ HypInf R p q

/-- **ch11-018** q/ph = 1 (folio 130 §12): q/ph = 1 ならば qp/h = p/h (Def. X 左形)。 -/
theorem th_11_018 (p q h : IProp) (hq : PrI q (iand p h) = 1) :
    PrI (iand q p) h = PrI p h := by
  rw [def_X_left_i q p h, hq, one_mul]

/-- **ch11-019** q/h ≠ 1 (folio 130 §12): q/ph = 1 かつ q/h ≠ 1 ならば p/h ≠ 1 —
仮言的推論の p は群 h に属さない (仮言的である)。 -/
theorem th_11_019 (p q h : IProp) (hq1 : PrI q (iand p h) = 1) (hq2 : PrI q h ≠ 1) :
    PrI p h ≠ 1 := by
  intro hp
  have e := th_11_018 p q h hq1
  have s := def_IX_i q p h
  have lo := ax_range_lo_i (iand q (inot p)) h
  have hi := ax_range_hi_i q h
  exact hq2 (by linarith)

/-- **ch11-020** p/h ≠ 0 (folio 130 §12): 「ph must specify a group; i.e. p/h ≠ 0」。
仮言的推論の定義は、Cons (ph) を p/h ≠ 0 に置き換えた形と同値。 -/
theorem th_11_020 (R : IProp → Prop) (p q : IProp) :
    HypInf R p q ↔
      ∃ h, RealGroup R h ∧ PrI q (iand p h) = 1 ∧ PrI q h ≠ 1 ∧ PrI p h ≠ 0 := by
  constructor
  · rintro ⟨h, hh, hcp, hq1, hq2⟩
    exact ⟨h, hh, hq1, hq2, (cons_iff_pos p h hh.2).mp hcp⟩
  · rintro ⟨h, hh, hq1, hq2, hp⟩
    exact ⟨h, hh, (cons_iff_pos p h hh.2).mpr hp, hq1, hq2⟩

/-- **ch11-022** p/h = 1 (folio 130 §12): p が群 h に属するとき、qp/h = q/ph。 -/
theorem th_11_022 (p q h : IProp) (hp : PrI p h = 1) :
    PrI (iand q p) h = PrI q (iand p h) := by
  rw [def_X_left_i q p h, hp, mul_one]

/-- **ch11-023** q/ph′ = 1 (folio 130 §12): 'p ∴ q' の二つの群 h, h′ は異なる
(p/h = 1 だが p/h′ ≠ 1)。 -/
theorem th_11_023 (R : IProp → Prop) (p q : IProp) (hpq : AssInf R p q) :
    ∃ h h', RealGroup R h ∧ RealGroup R h' ∧ PrI p h = 1 ∧ PrI q (iand p h') = 1 ∧
      PrI p h' ≠ 1 ∧ h ≠ h' := by
  obtain ⟨⟨h, hh, hp⟩, ⟨h', hh', _, hq1, hq2⟩⟩ := hpq
  have hp' := th_11_019 p q h' hq1 hq2
  refine ⟨h, h', hh, hh', hp, hq1, hp', ?_⟩
  rintro rfl
  exact hp' hp

/-- **ch11-024** q/h′ ≠ 1 (folio 130 §12): q/ph′ = 1, q/h′ ≠ 1, p/h′ ≠ 0 ならば
p/h′ は中間の値 0 < p/h′ < 1。 -/
theorem th_11_024 (p q h' : IProp) (hq1 : PrI q (iand p h') = 1) (hq2 : PrI q h' ≠ 1)
    (hp0 : PrI p h' ≠ 0) : 0 < PrI p h' ∧ PrI p h' < 1 :=
  ⟨(th_11_011 p h').mp hp0, (th_11_009 p h').mp (th_11_019 p q h' hq1 hq2)⟩

/-- **ch11-025** p/h′ ≠ 0 (folio 130 §12): 「i.e. there are proper groups h and h′ such
that p/h = 1, q/ph′ = 1, q/h′ ≠ 1, and p/h′ ≠ 0」— 断定的推論の定義はこの形と同値。 -/
theorem th_11_025 (R : IProp → Prop) (p q : IProp) :
    AssInf R p q ↔
      ∃ h h', RealGroup R h ∧ RealGroup R h' ∧ PrI p h = 1 ∧ PrI q (iand p h') = 1 ∧
        PrI q h' ≠ 1 ∧ PrI p h' ≠ 0 := by
  unfold AssInf
  rw [th_11_020]
  constructor
  · rintro ⟨⟨h, hh, hp⟩, ⟨h', hh', hq1, hq2, hp0⟩⟩
    exact ⟨h, h', hh, hh', hp, hq1, hq2, hp0⟩
  · rintro ⟨h, h', hh, hh', hp, hq1, hq2, hp0⟩
    exact ⟨⟨h, hh, hp⟩, ⟨h', hh', hq1, hq2, hp0⟩⟩

/-! ## §5 第 XI 章 §13 (folio 130–131): 中間の確率度への適用 -/

/-! ch11-026 p/h = a (folio 130 §13) は記号の意味を述べる名付けの行 (定義のみ) なので、
定理を置かない (台帳の Lean 欄は 未)。 -/

/-- 群の条件 (ii.) (folio 125 §6) の構文版: f と 'f implies g' (\bar{f} + g) が群 h に
属すれば g も属す (h 整合)。f \bar{g} (\bar{f} + g) の否定が形式的に真であることを使う。 -/
theorem group_cond_ii_form (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (hp : PrI (interp env f) h = 1)
    (hi : PrI (interp env (Form.disj (Form.neg f) g)) h = 1) :
    PrI (interp env g) h = 1 := by
  have hX := conj_certain _ _ h hc hp hi
  have s := def_IX_i (inot (interp env g))
    (iand (interp env f) (interp env (Form.disj (Form.neg f) g))) h
  rw [conj_neg_cert_zero _ _ h hc hX, zero_add] at s
  have ht : Taut (Form.neg (Form.conj (Form.neg g)
      (Form.conj f (Form.disj (Form.neg f) g)))) := by
    intro v
    simp only [evalB]
    cases evalB v f <;> cases evalB v g <;> rfl
  have z := taut_neg_zero _ env h hc ht
  simp only [interp] at z s
  rw [z] at s
  have := th_13_1_i (interp env g) h hc
  linarith

/-- **ch11-027** p/h = 1 (folio 130 §13): 「p follows from h and is, therefore, included in
the group specified by h」。{p | p/h = 1} は群の条件 (folio 125 §6) を満たす:
(ii.) p と 'p implies q' (\bar{p} + q) が属すれば q が属す、(iii.) p が属すれば \bar{p} は
排除される; あわせて連言で閉じる。 -/
theorem th_11_027 (p q h : IProp) (hc : Cons h) (hp : PrI p h = 1) :
    (PrI (ior (inot p) q) h = 1 → PrI q h = 1) ∧
      PrI (inot p) h = 0 ∧
      (∀ x, PrI x h = 1 → PrI (iand p x) h = 1) := by
  refine ⟨?_, ?_, fun x hx => conj_certain p x h hc hp hx⟩
  · intro hi
    exact group_cond_ii_form (Form.var 0) (Form.var 1)
      (fun n => if n = 0 then p else q) h hc hp hi
  · have := th_13_1_i p h hc
    linarith

/-- **ch11-028** p/h = 0 (folio 130 §13): 「p/h = 0 means that p is excluded from the group
specified by h」。h 整合のもとで p/h = 0 ⇔ ph は群を指定しない (矛盾する連言)。 -/
theorem th_11_028 (p h : IProp) (hc : Cons h) : PrI p h = 0 ↔ ¬ Cons (iand p h) := by
  rw [cons_iff_pos p h hc, not_not]

/-- 絶対的に確実 (folio 130–131): ある実在群 h で p/h = 1。 -/
def AbsCertain (R : IProp → Prop) (p : IProp) : Prop := ∃ h, RealGroup R h ∧ PrI p h = 1

/-- 絶対的に不可能 (folio 131): ある実在群 h で p/h = 0。 -/
def AbsImpossible (R : IProp → Prop) (p : IProp) : Prop := ∃ h, RealGroup R h ∧ PrI p h = 0

/-- **ch11-030** p/h = 1 (folio 130 §13): 「if p/h = 1 and h specifies any real group, p is
said to be absolutely certain」。そのとき \bar{p} は (同じ群で) 絶対的に不可能。 -/
theorem th_11_030 (R : IProp → Prop) (p h : IProp) (hh : RealGroup R h) (hp : PrI p h = 1) :
    AbsCertain R p ∧ AbsImpossible R (inot p) := by
  have := th_13_1_i p h hh.2
  exact ⟨⟨h, hh, hp⟩, ⟨h, hh, by linarith⟩⟩

/-- **ch11-031** p/h = 0 (folio 131 §13): 「Similarly if p/h = 0 under the same conditions,
p is absolutely impossible」。そのとき \bar{p} は絶対的に確実 (「we know to be false」)。 -/
theorem th_11_031 (R : IProp → Prop) (p h : IProp) (hh : RealGroup R h) (hp : PrI p h = 0) :
    AbsImpossible R p ∧ AbsCertain R (inot p) := by
  have := th_13_1_i p h hh.2
  exact ⟨⟨h, hh, hp⟩, ⟨h, hh, by linarith⟩⟩

/-- 一般化された非要求 (folio 131 §13): 「The probability of p does not require q within the
group h, if there is a subgroup h′ such that, for every subgroup h″ which includes h′ and is
included in h (i.e. h′/h″ = 1, h″/h = 1), p/h″ = p/h′, and q/h′ ≠ q/h.」
h′ は h の部分群 (h′/h = 1)、h″ は群 (整合) とする。 -/
def GenNotRequiresWithin (h p q : IProp) : Prop :=
  ∃ h', Cons h' ∧ PrI h' h = 1 ∧
    (∀ h'', Cons h'' → PrI h' h'' = 1 → PrI h'' h = 1 → PrI p h'' = PrI p h') ∧
    PrI q h' ≠ PrI q h

/-- **ch11-033** h″/h = 1 (folio 131 §13): h″ の範囲は h 自身を含む (h/h = 1 のとき) ので、
条件から p/h = p/h′。前提 h/h = 1 は印刷に無く、外せない (nec_11_033_hh)。 -/
theorem th_11_033 (h h' p : IProp) (hc : Cons h) (h1 : PrI h' h = 1) (hhh : PrI h h = 1)
    (hall : ∀ h'', Cons h'' → PrI h' h'' = 1 → PrI h'' h = 1 → PrI p h'' = PrI p h') :
    PrI p h = PrI p h' :=
  hall h hc h1 hhh

/-- **ch11-034** p/h″ = p/h′ (folio 131 §13): 一般化された非要求が成り立てば、
p/h = p/h′ かつ q/h′ ≠ q/h となる部分群 h′ があり、h′ は h と異なる (h/h = 1 のとき)。 -/
theorem th_11_034 (h p q : IProp) (hc : Cons h) (hhh : PrI h h = 1)
    (hg : GenNotRequiresWithin h p q) :
    ∃ h', Cons h' ∧ PrI h' h = 1 ∧ PrI p h = PrI p h' ∧ PrI q h' ≠ PrI q h ∧ h' ≠ h := by
  obtain ⟨h', hc', h1, hall, hq⟩ := hg
  refine ⟨h', hc', h1, th_11_033 h h' p hc h1 hhh hall, hq, ?_⟩
  rintro rfl
  exact hq rfl

/-- **ch11-035** q/h′ ≠ q/h (folio 131 §13): 「When p is included in the group h, this
definition reduces to the definition of requirement given in § 11.」
p/h = 1 (印刷の条件) のもとで、一般化された非要求 ⇒ §11 の群 h の中での非要求。
前提 h/h = 1 を追加する (a/a = 1 は KeynesI で未導出)。q/h で場合分けする:
q/h = 1 なら h′ が §11 の証人 (q/h′ ≠ q/h = 1)、q/h ≠ 1 なら h 自身が証人。
(逆向きは前提側の置換を要し、KeynesI では示さない。) -/
theorem th_11_035 (h p q : IProp) (hc : Cons h) (hhh : PrI h h = 1)
    (hp : PrI p h = 1) (hg : GenNotRequiresWithin h p q) :
    NotRequiresWithin h p q := by
  by_cases hq : PrI q h = 1
  · obtain ⟨h', hc', h1, hall, hne⟩ := hg
    have e := th_11_033 h h' p hc h1 hhh hall
    refine ⟨h', hc', h1, by rw [← e, hp], ?_⟩
    rw [hq] at hne
    exact hne
  · exact ⟨h, hc, hhh, hp, hq⟩

/-! ## 必要性: th_11_035 の前提 h/h = 1 は落とせない (反例モデル)

モデル: 世界 Fin 2、命題は対 (C, P) — C は結論として読むときの集合、P は前提として読むときの
集合。連言 ab = (C_a ∩ C_b, C_a ∩ P_b)、否定・選言・同値・itrue は P = C、
a/h = |C_a ∩ P_h| / |P_h|。整合 Cons h は「P_h が空でなく、P_h ⊆ {1} または C_h = ∅」。
このモデルは §0 の公理 (def_IX_i, def_X_left_i, def_X_right_i, 値域, ax_iii_taut,
cons_of_pos_src, cons_of_pos) をすべて満たす。h = (∅, 全体)、p = itrue、q = ({1}, {1})
とおくと、th_11_035 の前提のうち h/h = 1 以外 (h 整合、p/h = 1、一般化された非要求;
証人 h′ = (全体, {1})) は成り立ち、h/h = 0 で、結論 (群 h の中での非要求) は偽。
したがって h/h = 1 は §0 の公理群からは出ず、th_11_035 の証明から外せない。 -/

namespace NecModel

/-- 反例モデルの命題: (結論側の集合 C, 前提側の集合 P)。 -/
abbrev MI := Finset (Fin 2) × Finset (Fin 2)

/-- 反例モデルの連言。 -/
def mand (a b : MI) : MI := (a.1 ∩ b.1, a.1 ∩ b.2)
/-- 反例モデルの選言。 -/
def mor (a b : MI) : MI := (a.1 ∪ b.1, a.1 ∪ b.1)
/-- 反例モデルの否定。 -/
def mnot (a : MI) : MI := (a.1ᶜ, a.1ᶜ)
/-- 反例モデルの同値。 -/
def miff (a b : MI) : MI :=
  (Finset.univ.filter (fun ω => (ω ∈ a.1 ↔ ω ∈ b.1)),
   Finset.univ.filter (fun ω => (ω ∈ a.1 ↔ ω ∈ b.1)))
/-- 反例モデルの itrue。 -/
def mtrue : MI := (Finset.univ, Finset.univ)

/-- 反例モデルの確率関係 a/h = |C_a ∩ P_h| / |P_h|。 -/
noncomputable def mPr (a h : MI) : ℝ := ((a.1 ∩ h.2).card : ℝ) / (h.2.card : ℝ)

/-- 反例モデルの整合性述語。 -/
def mCons (h : MI) : Prop := h.2.Nonempty ∧ (h.2 ⊆ {1} ∨ h.1 = ∅)

/-- 反例モデルでの構文の解釈 (interp と同じ形)。 -/
def mInterp (env : ℕ → MI) : Form → MI
  | .var n    => env n
  | .tru      => mtrue
  | .fls      => mnot mtrue
  | .conj f g => mand (mInterp env f) (mInterp env g)
  | .disj f g => mor (mInterp env f) (mInterp env g)
  | .neg f    => mnot (mInterp env f)
  | .iffF f g => miff (mInterp env f) (mInterp env g)

theorem mem_mInterp (env : ℕ → MI) (ω : Fin 2) (f : Form) :
    ω ∈ (mInterp env f).1 ↔ evalB (fun n => decide (ω ∈ (env n).1)) f = true := by
  induction f with
  | var n => simp [mInterp, evalB]
  | tru => simp [mInterp, mtrue, evalB]
  | fls => simp [mInterp, mnot, mtrue, evalB]
  | conj f g ihf ihg => simp [mInterp, mand, evalB, ihf, ihg]
  | disj f g ihf ihg => simp [mInterp, mor, evalB, ihf, ihg]
  | neg f ih => simp [mInterp, mnot, evalB, ih]
  | iffF f g ihf ihg =>
      simp only [mInterp, miff, evalB, Finset.mem_filter, Finset.mem_univ, true_and, ihf, ihg]
      cases evalB (fun n => decide (ω ∈ (env n).1)) f <;>
        cases evalB (fun n => decide (ω ∈ (env n).1)) g <;> simp

theorem mdiv (x y z : ℝ) (h : y = 0 → x = 0) : x / y * (y / z) = x / z := by
  by_cases hy : y = 0
  · simp [hy, h hy]
  · rw [div_mul_div_comm, mul_comm x y, mul_div_mul_left x z hy]

theorem mPr_one (a h : MI) (hne : h.2.Nonempty) (hs : h.2 ⊆ a.1) : mPr a h = 1 := by
  unfold mPr
  rw [Finset.inter_eq_right.mpr hs]
  exact div_self (by exact_mod_cast (Finset.card_pos.mpr hne).ne')

theorem m_def_X (p q h : MI) (hcq : (q.1 ∩ h.2).card = 0 → (p.1 ∩ (q.1 ∩ h.2)).card = 0)
    (e : (p.1 ∩ q.1) ∩ h.2 = p.1 ∩ (q.1 ∩ h.2)) :
    mPr (mand p q) h = mPr p (mand q h) * mPr q h := by
  unfold mPr mand
  simp only
  rw [e, mdiv]
  intro h0
  exact_mod_cast hcq (by exact_mod_cast h0)

/-- 反例の前提 h = (∅, 全体): h/h = 0。 -/
def hS : MI := (∅, Finset.univ)
/-- 反例の q = ({1}, {1})。 -/
def qS : MI := ({1}, {1})

/-- **nec_11_035_hh** (必要性): §0 の公理をすべて満たすモデルで、th_11_035 の前提のうち
h/h = 1 だけが破れ、結論が偽になる。 -/
theorem nec_11_035_hh :
    -- §0 の公理がモデルで成り立つ
    (∀ p q h, mPr (mand p (mnot q)) h + mPr (mand p q) h = mPr p h) ∧
    (∀ p q h, mPr (mand p q) h = mPr p (mand q h) * mPr q h) ∧
    (∀ p q h, mPr (mand p q) h = mPr q (mand p h) * mPr p h) ∧
    (∀ p h, 0 ≤ mPr p h) ∧ (∀ p h, mPr p h ≤ 1) ∧
    (∀ (f : Form) env h, mCons h → Taut f → mPr (mInterp env f) h = 1) ∧
    (∀ a h, mCons (mand a h) → mPr a h ≠ 0) ∧
    (∀ a h, mPr a h ≠ 0 → mCons h → mCons (mand a h)) ∧
    -- h = (∅, 全体)、p = itrue、q = ({1}, {1}) で th_11_035 の h/h = 1 以外の前提が成り立ち、
    -- h/h ≠ 1、結論は偽
    (mCons hS ∧ mPr hS hS ≠ 1 ∧ mPr mtrue hS = 1 ∧
     (∃ h', mCons h' ∧ mPr h' hS = 1 ∧
        (∀ h'', mCons h'' → mPr h' h'' = 1 → mPr h'' hS = 1 → mPr mtrue h'' = mPr mtrue h') ∧
        mPr qS h' ≠ mPr qS hS) ∧
     ¬ ∃ h', mCons h' ∧ mPr h' hS = 1 ∧ mPr mtrue h' = 1 ∧ mPr qS h' ≠ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q h
    unfold mPr mand mnot
    simp only
    rw [← add_div]
    congr 1
    have e1 : p.1 ∩ q.1ᶜ ∩ h.2 = (p.1 ∩ h.2) \ q.1 := by
      ext ω; simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]; tauto
    have e2 : p.1 ∩ q.1 ∩ h.2 = (p.1 ∩ h.2) ∩ q.1 := by
      ext ω; simp only [Finset.mem_inter]; tauto
    rw [e1, e2]
    exact_mod_cast Finset.card_sdiff_add_card_inter (p.1 ∩ h.2) q.1
  · intro p q h
    refine m_def_X p q h (fun h0 => ?_) (Finset.inter_assoc _ _ _)
    exact Nat.eq_zero_of_le_zero (h0 ▸ Finset.card_le_card Finset.inter_subset_right)
  · intro p q h
    have e : (p.1 ∩ q.1) ∩ h.2 = (q.1 ∩ p.1) ∩ h.2 := by rw [Finset.inter_comm p.1]
    have := m_def_X q p h
      (fun h0 => Nat.eq_zero_of_le_zero (h0 ▸ Finset.card_le_card Finset.inter_subset_right))
      (Finset.inter_assoc _ _ _)
    unfold mPr mand at this ⊢
    simp only at this ⊢
    rw [e, this]
  · intro p h
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro p h
    exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
      (Nat.cast_nonneg _)
  · intro f env h hc hf
    apply mPr_one _ _ hc.1
    intro ω _
    exact (mem_mInterp env ω f).mpr (hf _)
  · rintro a h ⟨hne, _⟩
    unfold mPr
    have hn : (a.1 ∩ h.2).Nonempty := hne
    apply div_ne_zero
    · exact_mod_cast (Finset.card_pos.mpr hn).ne'
    · exact_mod_cast (Finset.card_pos.mpr (hn.mono Finset.inter_subset_right)).ne'
  · rintro a h hp ⟨_, hs | hC⟩
    · have hn : (a.1 ∩ h.2).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty] at hn
        exact hp (by simp [mPr, hn])
      exact ⟨hn, Or.inl (Finset.inter_subset_right.trans hs)⟩
    · have hn : (a.1 ∩ h.2).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty] at hn
        exact hp (by simp [mPr, hn])
      exact ⟨hn, Or.inr (by simp [mand, hC])⟩
  · refine ⟨⟨Finset.univ_nonempty, Or.inr rfl⟩, by simp [mPr, hS], ?_, ?_, ?_⟩
    · exact mPr_one _ _ Finset.univ_nonempty (Finset.subset_univ _)
    · refine ⟨(Finset.univ, {1}), ⟨⟨1, by simp⟩, Or.inl subset_rfl⟩,
        mPr_one _ _ Finset.univ_nonempty subset_rfl, ?_, ?_⟩
      · intro h'' hc'' _ _
        rw [mPr_one _ _ hc''.1 (Finset.subset_univ _),
          mPr_one _ _ ⟨1, by simp⟩ (Finset.subset_univ _)]
      · rw [mPr_one _ _ ⟨1, by simp⟩ subset_rfl]
        simp [mPr, hS, qS]
    · rintro ⟨h', ⟨hne, hs | hC⟩, h1, _, hq⟩
      · exact hq (mPr_one _ _ hne hs)
      · simp [mPr, hS, hC] at h1

/-- **nec_11_033_hh** (必要性): 同じモデルで、th_11_033 の前提のうち h/h = 1 だけが破れ、
結論 p/h = p/h′ が偽になる。h = (∅, 全体)、h′ = (全体, {1})、p = ({1}, {1}):
h 整合、h′/h = 1、(h′/h″ = 1, h″/h = 1 を満たす整合な h″ はすべて P″ = {1} で p/h″ = 1 = p/h′)
だが、p/h = 1/2 ≠ 1 = p/h′。 -/
theorem nec_11_033_hh :
    mCons hS ∧ mPr hS hS ≠ 1 ∧ mPr (Finset.univ, {1}) hS = 1 ∧
    (∀ h'', mCons h'' → mPr (Finset.univ, {1}) h'' = 1 → mPr h'' hS = 1 →
      mPr qS h'' = mPr qS (Finset.univ, {1})) ∧
    mPr qS hS ≠ mPr qS (Finset.univ, {1}) := by
  have hq' : mPr qS (Finset.univ, {1}) = 1 := mPr_one _ _ ⟨1, by simp⟩ subset_rfl
  refine ⟨⟨Finset.univ_nonempty, Or.inr rfl⟩, by simp [mPr, hS],
    mPr_one _ _ Finset.univ_nonempty (Finset.subset_univ _), ?_, ?_⟩
  · rintro h'' ⟨hne, hs | hC⟩ _ h2
    · rw [hq']
      exact mPr_one _ _ hne hs
    · simp [mPr, hS, hC] at h2
  · rw [hq']
    simp [mPr, hS, qS]

end NecModel

end KeynesXI

/-! ## 公理の出力 -/

#print axioms KeynesXI.conj_certain
#print axioms KeynesXI.cons_iff_pos
#print axioms KeynesXI.th_11_001
#print axioms KeynesXI.th_11_003
#print axioms KeynesXI.th_11_004
#print axioms KeynesXI.th_11_006
#print axioms KeynesXI.th_11_007
#print axioms KeynesXI.th_11_008
#print axioms KeynesXI.th_11_009
#print axioms KeynesXI.th_11_010
#print axioms KeynesXI.th_11_011
#print axioms KeynesXI.th_11_012
#print axioms KeynesXI.th_11_013
#print axioms KeynesXI.requires_refl
#print axioms KeynesXI.requires_trans
#print axioms KeynesXI.th_11_014
#print axioms KeynesXI.th_11_015
#print axioms KeynesXI.th_11_016
#print axioms KeynesXI.th_11_018
#print axioms KeynesXI.th_11_019
#print axioms KeynesXI.th_11_020
#print axioms KeynesXI.th_11_022
#print axioms KeynesXI.th_11_023
#print axioms KeynesXI.th_11_024
#print axioms KeynesXI.th_11_025
#print axioms KeynesXI.group_cond_ii_form
#print axioms KeynesXI.th_11_027
#print axioms KeynesXI.th_11_028
#print axioms KeynesXI.th_11_030
#print axioms KeynesXI.th_11_031
#print axioms KeynesXI.th_11_033
#print axioms KeynesXI.th_11_034
#print axioms KeynesXI.th_11_035
#print axioms KeynesXI.NecModel.nec_11_035_hh
#print axioms KeynesXI.NecModel.nec_11_033_hh
