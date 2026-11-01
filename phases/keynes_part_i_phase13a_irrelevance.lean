/-
# Keynes (1921) *A Treatise on Probability* Part I — Lean 4 Phase 13a
#
# 新井一成・Claude共著、2026年10月31日 (B34)
# **第4章 §14 の無関連・独立の定義、§21 の可分な選択肢の条件、第5章 §§2, 4 の
#   狭義不等式と好意的関連の十分条件**
#
# ## 第I部の式を第II部の型の上で扱う理由 (3 行)
#   第4章 folio 55 は無関連の定義を述べたうえで「Some propositions regarding irrelevance
#   will be proved in Part II」と証明を第II部に先送りし、第5章 folio 66・68 も「pending the
#   symbolic developments of Part II」とするので、phase6c の内包的担体 (IProp・PrI・Cons) で書く。
#   B30 (phase12a_order) は確率集合 Π を半順序の型にしたが、本ファイルの関係式 (=, ≠, <, 積) は
#   数値の道筋 OAI の上の比較であり、ℝ 値の PrI で書く; ch05-005 の狭義形は Π 上の Ax. (iv. b)
#   「PQ < P unless Q = 1 or P = 0」(folio 136、phase12a の ax_ivb_*) を Def. X と値域から導く形にあたる。
#
# ## 原典 (唯一の基準、1921 Macmillan 初版) の該当箇所
#   folio 55 (第4章 §14) 本文: 「If h̄₁ is the contradictory of h₁ and x/h₁h = x/h, then
#     x/h̄₁h = x/h. Thus the contradictory of irrelevant evidence is also irrelevant.」
#     本文: 「Any proposition which is irrelevant in the strict sense is, of course, also
#     irrelevant in the simpler sense」
#   folio 55 脚注 2: 「That is to say, h₁ is irrelevant to x/h, if there is no proposition h′₁
#     such that h′₁/h₁h = 1, h′₁/h ≠ 1, and x/h′₁h ≠ x/h.」
#   folio 55 脚注 4: 「I.e. (in symbolism) h₁ and h₂ are independent and complementary parts of
#     h if h₁h₂ = h, h₁/h₂ ≠ 1, and h₂/h₁ ≠ 1. Also h₁ is relevant if x/h ≠ x/h₂.」
#   folio 60 (第4章 §21): 「An alternative φ(a_r) is divisible if
#     (i.) [φ(a_r) ≡ φ(a_r′) + φ(a_r″)]/h = 1, (ii.) φ(a_r′) . φ(a_r″)/h = 0,
#     (iii.) φ(a_r′)/h ≠ 0 and φ(a_r″)/h ≠ 0」
#   folio 66 (第5章 §2): 「(i.) The propositions of Part II. will enable us to prove that
#     ab/h < a/h unless b/ah = 1 ;」
#   folio 68 (第5章 §4): 「(1) The addition of new evidence h₁ to a doubtful argument a/h is
#     favourably relevant, if either of the following conditions is fulfilled :—(a) if
#     a/hh̄₁ = 0 ; (b) if a/hh₁ = 1.」脚注 1: 「h₁ is new evidence so long as h₁/h ≠ 1.」
#     脚注 2: 「The argument is doubtful so long as a/h is neither certain nor impossible.」
#
# ## 読み (弱い読みを定理にし、強い読みは境界に記録する)
#   - 命題の等号 h₁h₂ = h (ch04-063) は IProp の等号 (Lean の =) と読む。同値 (≡)/h = 1 と
#     読む強い読みは置かない。
#   - 前提の連言は Def. X の形 (iand q h = 「qh」) で書く。本公理系には前提の連言の可換も
#     前提側の置換 (公理 (ii)) も無いので、印刷が「hh₁」「hh̄₁」の順 (ch05-029, 030) のものは
#     h₁h・h̄₁h の順に書いた (順序違い → ≈)。
#   - ch04-054 は x/h̄₁h が存在する範囲 (公理 (i) の但し書き: h̄₁h が整合) と Cons h の下で
#     示す (th_4_r054)。但し書きを落とした形は全公理を満たす模型で偽 (model_r054_needs_cons)。
#   - ch05-005 は b/ah が存在する範囲 (Cons (a ∧ h)) で示す (th_5_r005)。但し書きの代わりに
#     a/h ≠ 0 を置いた形 (th_5_r005_pos) と、a/h ≠ 0 の下の双条件 (th_5_r005_iff) も置く。
#     但し書きも a/h ≠ 0 も無い形は全公理を満たす模型で偽 (model_r005_needs_cons)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_i_phase13a_irrelevance.lean
-/

import Mathlib

namespace KeynesIrr

/-! ## §1 phase6c の公理群の再掲 (同名・同形、import しない) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 `Cons h`: 「h は矛盾する連言でない」(folio 135、公理 (i))。 -/
axiom Cons : IProp → Prop

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- Def. VIII 双条件読み、但し書き付き (phase6c と同文)。 -/
axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- Def. VIII 印刷どおり (phase6c と同文)。本ファイルの定理はこれを用いない。 -/
axiom def_VIII_i_src (a b h : IProp) :
    PrI b (iand a h) = 1 → PrI a (iand b h) = 1 → PrI (iiff a b) h = 1

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

axiom cons_true : Cons itrue
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## §2 phase6c の定理の再証明 (本ファイルで使うものだけ、証明も phase6c と同じ) -/

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

/-- 第13章の (1) (folio 139): a/h + \bar{a}/h = 1 (Cons h 付き)。 -/
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

/-- 第13章の (12) (folio 141): (a≡b)/h = 1 ならば a/h = b/h。phase6c の th_12_i_short と
同じ証明 (def_VIII_i を用いない)。 -/
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

/-- 認証代入 (phase6c の subst_taut を th_12_i_short で閉じたもの)。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i_short _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-- 第14章の (24) 加法定理 (folio 144、phase6c と同じ証明)。 -/
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

/-- 第13章の (13) の前提 a ∧ h 版 (phase6c と同じ証明)。 -/
theorem th_13_13_conj_i (a h : IProp) (hc : Cons h) (hca : Cons (iand a h)) :
    PrI a (iand a h) = 1 := by
  have hcert : PrI (iiff a a) h = 1 :=
    ax_iii_taut (Form.iffF (Form.var 0) (Form.var 0)) (fun _ => a) h hc
      (by intro v; simp [evalB])
  exact ((def_VIII_i a a h hca hca).mp hcert).1

/-! ## §3 定義 (folio 55・60・68 の印刷形をそのまま写す) -/

/-- **単純な無関連** (folio 55 本文・脚注 1): 「h₁ is irrelevant to x/h if x/h₁h = x/h」。
第II部の Def. XIV (folio 138) と同じ形。 -/
def Irrelevant (x h₁ h : IProp) : Prop := PrI x (iand h₁ h) = PrI x h

/-- **厳密な無関連** (folio 55 脚注 2): 「h₁ is irrelevant to x/h, if there is no proposition
h′₁ such that h′₁/h₁h = 1, h′₁/h ≠ 1, and x/h′₁h ≠ x/h」。 -/
def StrictlyIrrelevant (x h₁ h : IProp) : Prop :=
  ¬ ∃ h₁' : IProp, PrI h₁' (iand h₁ h) = 1 ∧ PrI h₁' h ≠ 1 ∧ PrI x (iand h₁' h) ≠ PrI x h

/-- **独立・相補な部分** (folio 55 脚注 4): 「h₁ and h₂ are independent and complementary
parts of h if h₁h₂ = h, h₁/h₂ ≠ 1, and h₂/h₁ ≠ 1」。h₁h₂ = h は IProp の等号。 -/
def IndependentComplementary (h₁ h₂ h : IProp) : Prop :=
  iand h₁ h₂ = h ∧ PrI h₁ h₂ ≠ 1 ∧ PrI h₂ h₁ ≠ 1

/-- **関連する部分** (folio 55 脚注 4): 「Also h₁ is relevant if x/h ≠ x/h₂」。 -/
def RelevantPart (x h₁ h₂ h : IProp) : Prop :=
  IndependentComplementary h₁ h₂ h ∧ PrI x h ≠ PrI x h₂

/-- **可分の 3 条件** (folio 60 (i.)–(iii.))、部分選択肢 a_r′, a_r″ を名指した形。
φ は命題関数 φ(x)、+ は選言 ior、ピリオドは連言 iand。 -/
def DivisibleBy {α : Type} (φ : α → IProp) (ar ar' ar'' : α) (h : IProp) : Prop :=
  PrI (iiff (φ ar) (ior (φ ar') (φ ar''))) h = 1 ∧
  PrI (iand (φ ar') (φ ar'')) h = 0 ∧
  (PrI (φ ar') h ≠ 0 ∧ PrI (φ ar'') h ≠ 0)

/-- **可分な選択肢** (folio 60): 「An alternative φ(a_r) is divisible if」(i.)–(iii.) を満たす
同じ形の部分選択肢 φ(a_r′), φ(a_r″) がある。 -/
def Divisible {α : Type} (φ : α → IProp) (ar : α) (h : IProp) : Prop :=
  ∃ ar' ar'' : α, DivisibleBy φ ar ar' ar'' h

/-- **新しい証拠** (folio 68 脚注 1): 「h₁ is new evidence so long as h₁/h ≠ 1」。 -/
def NewEvidence (h₁ h : IProp) : Prop := PrI h₁ h ≠ 1

/-- **疑わしい論証** (folio 68 脚注 2): 「a/h is neither certain nor impossible」。 -/
def Doubtful (a h : IProp) : Prop := PrI a h ≠ 1 ∧ PrI a h ≠ 0

/-- **好意的に関連する** (folio 66 §2 (ii.): 「If h₁ is favourable, a/hh₁ > a/h」)。
前提の連言は Def. X の形 h₁h で書く (印刷は hh₁)。 -/
def FavourablyRelevant (a h₁ h : IProp) : Prop := PrI a (iand h₁ h) > PrI a h

/-- **好意的関連の十分条件** (folio 68 (1)): 「(a) if a/hh̄₁ = 0 ; (b) if a/hh₁ = 1」の選言。
前提の連言は h̄₁h・h₁h の順で書く。 -/
def FavourableCondition (a h₁ h : IProp) : Prop :=
  PrI a (iand (inot h₁) h) = 0 ∨ PrI a (iand h₁ h) = 1

/-! ## §4 補題: h の下で確実な証拠は無関連 -/

/-- h₁/h = 1 ならば x/h₁h = x/h (Cons h)。(1) で \bar{h}₁/h = 0、Def. IX と Def. X 左形。 -/
theorem irrelevant_of_certain (x h₁ h : IProp) (hc : Cons h) (h1 : PrI h₁ h = 1) :
    Irrelevant x h₁ h := by
  unfold Irrelevant
  have hn : PrI (inot h₁) h = 0 := by have := th_13_1_i h₁ h hc; linarith
  have s := def_IX_i x h₁ h
  have e1 := def_X_left_i x (inot h₁) h
  have e2 := def_X_left_i x h₁ h
  rw [hn, mul_zero] at e1
  rw [h1, mul_one] at e2
  linarith

/-! ## §5 第4章 folio 55: 無関連・独立 (ch04-054, 060–066) -/

/-- **ch04-054** (folio 55): 「If h̄₁ is the contradictory of h₁ and x/h₁h = x/h, then
x/h̄₁h = x/h」。前提 Cons h と、x/h̄₁h が存在する範囲 Cons (h̄₁ ∧ h) (公理 (i) の但し書き)
の下で示す。経路: Def. IX で x/h = x h̄₁/h + x h₁/h、Def. X 左形で各項を
x/h̄₁h · h̄₁/h と x/h₁h · h₁/h に開き、(1) h₁/h + h̄₁/h = 1 から
(x/h̄₁h − x/h) · h̄₁/h = 0。h̄₁/h ≠ 0 は Def. VI の印刷の向き (cons_of_pos_src)。 -/
theorem th_4_r054 (x h₁ h : IProp) (hc : Cons h) (hcn : Cons (iand (inot h₁) h))
    (hirr : Irrelevant x h₁ h) : Irrelevant x (inot h₁) h := by
  unfold Irrelevant at *
  have hq : PrI (inot h₁) h ≠ 0 := cons_of_pos_src (inot h₁) h hcn
  have hsum := th_13_1_i h₁ h hc
  have s := def_IX_i x h₁ h
  have e1 := def_X_left_i x (inot h₁) h
  have e2 := def_X_left_i x h₁ h
  rw [hirr] at e2
  have key : (PrI x (iand (inot h₁) h) - PrI x h) * PrI (inot h₁) h = 0 := by
    linear_combination -e1 + s - e2 - (PrI x h) * hsum
  rcases mul_eq_zero.mp key with h0 | h0
  · linarith
  · exact absurd h0 hq

/-- ch04-054 の別形: 但し書き Cons (h̄₁ ∧ h) の代わりに「h₁ が新しい証拠」h₁/h ≠ 1
(folio 68 脚注 1) を置く。 -/
theorem th_4_r054_of_new (x h₁ h : IProp) (hc : Cons h) (hnew : NewEvidence h₁ h)
    (hirr : Irrelevant x h₁ h) : Irrelevant x (inot h₁) h := by
  unfold Irrelevant NewEvidence at *
  have hsum := th_13_1_i h₁ h hc
  have hq : PrI (inot h₁) h ≠ 0 := by
    intro h0; apply hnew; linarith
  have s := def_IX_i x h₁ h
  have e1 := def_X_left_i x (inot h₁) h
  have e2 := def_X_left_i x h₁ h
  rw [hirr] at e2
  have key : (PrI x (iand (inot h₁) h) - PrI x h) * PrI (inot h₁) h = 0 := by
    linear_combination -e1 + s - e2 - (PrI x h) * hsum
  rcases mul_eq_zero.mp key with h0 | h0
  · linarith
  · exact absurd h0 hq

/-- **ch04-060** (folio 55 脚注 2、h′₁/h₁h = 1): 厳密な無関連の定義の言い換え。
h₁h から推論でき (h′₁/h₁h = 1)、h からは推論できない (h′₁/h ≠ 1) どの h′₁ についても
x/h′₁h = x/h。 -/
theorem th_4_r060 (x h₁ h : IProp) :
    StrictlyIrrelevant x h₁ h ↔
      ∀ h₁' : IProp, PrI h₁' (iand h₁ h) = 1 → PrI h₁' h ≠ 1 →
        PrI x (iand h₁' h) = PrI x h := by
  constructor
  · intro H h' h1 h2
    by_contra h3
    exact H ⟨h', h1, h2, h3⟩
  · rintro H ⟨h', h1, h2, h3⟩
    exact h3 (H h' h1 h2)

/-- **ch04-061** (folio 55 脚注 2、h′₁/h ≠ 1): Cons h の下では条件 h′₁/h ≠ 1 を外しても
定義は変わらない (h から推論できる h′₁ は §4 により無関連)。 -/
theorem th_4_r061 (x h₁ h : IProp) (hc : Cons h) :
    StrictlyIrrelevant x h₁ h ↔
      ∀ h₁' : IProp, PrI h₁' (iand h₁ h) = 1 → PrI x (iand h₁' h) = PrI x h := by
  constructor
  · intro H h' h1
    by_cases h2 : PrI h' h = 1
    · exact irrelevant_of_certain x h' h hc h2
    · exact (th_4_r060 x h₁ h).mp H h' h1 h2
  · rintro H ⟨h', h1, _, h3⟩
    exact h3 (H h' h1)

/-- **ch04-062** (folio 55 脚注 2、x/h′₁h ≠ x/h): 「Any proposition which is irrelevant in the
strict sense is, of course, also irrelevant in the simpler sense」。h′₁ := h₁ と置き、
h₁/h₁h = 1 は (13) の前提 h₁ ∧ h 版 (Cons (h₁ ∧ h) 付き)。 -/
theorem th_4_r062 (x h₁ h : IProp) (hc : Cons h) (hc1 : Cons (iand h₁ h))
    (H : StrictlyIrrelevant x h₁ h) : Irrelevant x h₁ h :=
  (th_4_r061 x h₁ h hc).mp H h₁ (th_13_13_conj_i h₁ h hc hc1)

/-- **ch04-063** (folio 55 脚注 4、h₁h₂ = h): 定義 ↔ 印刷の 3 条件。 -/
theorem th_4_r063 (h₁ h₂ h : IProp) :
    IndependentComplementary h₁ h₂ h ↔
      (iand h₁ h₂ = h ∧ PrI h₁ h₂ ≠ 1 ∧ PrI h₂ h₁ ≠ 1) :=
  Iff.rfl

/-- **ch04-064** (folio 55 脚注 4、h₁/h₂ ≠ 1): 「neither can be inferred from the other」の
片側。h₁/h₂ ≠ 1 と Cons h₂ から、h₂ に h₁ の否定を加えた h̄₁h₂ は整合 ((1) と cons_of_pos)。 -/
theorem th_4_r064 (h₁ h₂ h : IProp) (hc2 : Cons h₂)
    (H : IndependentComplementary h₁ h₂ h) : Cons (iand (inot h₁) h₂) := by
  have hsum := th_13_1_i h₁ h₂ hc2
  have hne : PrI (inot h₁) h₂ ≠ 0 := by
    intro h0; apply H.2.1; linarith
  exact cons_of_pos (inot h₁) h₂ hne hc2

/-- **ch04-065** (folio 55 脚注 4、h₂/h₁ ≠ 1): 同じくもう片側。 -/
theorem th_4_r065 (h₁ h₂ h : IProp) (hc1 : Cons h₁)
    (H : IndependentComplementary h₁ h₂ h) : Cons (iand (inot h₂) h₁) := by
  have hsum := th_13_1_i h₂ h₁ hc1
  have hne : PrI (inot h₂) h₁ ≠ 0 := by
    intro h0; apply H.2.2; linarith
  exact cons_of_pos (inot h₂) h₁ hne hc1

/-- **ch04-066** (folio 55 脚注 4、x/h ≠ x/h₂): 本文の「the addition of it to h₂ affects
the probability of x」(x/h₁h₂ ≠ x/h₂) と脚注の記号形 x/h ≠ x/h₂ は h₁h₂ = h の下で同じ。 -/
theorem th_4_r066 (x h₁ h₂ h : IProp) (H : IndependentComplementary h₁ h₂ h) :
    PrI x (iand h₁ h₂) ≠ PrI x h₂ ↔ PrI x h ≠ PrI x h₂ := by
  rw [H.1]

/-- ch04-066 の系: 関連する部分は h₂ に対して新しい証拠 (h₁/h₂ ≠ 1 は関連から出る)。 -/
theorem th_4_r066_new (x h₁ h₂ h : IProp) (hc2 : Cons h₂) (heq : iand h₁ h₂ = h)
    (hrel : PrI x h ≠ PrI x h₂) : NewEvidence h₁ h₂ := by
  intro h1
  apply hrel
  have := irrelevant_of_certain x h₁ h₂ hc2 h1
  unfold Irrelevant at this
  rw [heq] at this
  exact this

/-! ## §6 第4章 folio 60: 可分な選択肢の 3 条件 (ch04-109–111) -/

/-- **ch04-109** (folio 60 (i.)): [φ(a_r) ≡ φ(a_r′) + φ(a_r″)]/h = 1 ならば
φ(a_r)/h = (φ(a_r′) + φ(a_r″))/h ((12)、Cons h 付き)。 -/
theorem th_4_r109 {α : Type} (φ : α → IProp) (ar ar' ar'' : α) (h : IProp) (hc : Cons h)
    (hi : PrI (iiff (φ ar) (ior (φ ar') (φ ar''))) h = 1) :
    PrI (φ ar) h = PrI (ior (φ ar') (φ ar'')) h :=
  th_12_i_short _ _ h hc hi

/-- **ch04-110** (folio 60 (ii.)): (i.) と (ii.) φ(a_r′) . φ(a_r″)/h = 0 から
φ(a_r)/h = φ(a_r′)/h + φ(a_r″)/h ((24) 加法定理、Cons h 付き)。 -/
theorem th_4_r110 {α : Type} (φ : α → IProp) (ar ar' ar'' : α) (h : IProp) (hc : Cons h)
    (hi : PrI (iiff (φ ar) (ior (φ ar') (φ ar''))) h = 1)
    (hii : PrI (iand (φ ar') (φ ar'')) h = 0) :
    PrI (φ ar) h = PrI (φ ar') h + PrI (φ ar'') h := by
  rw [th_4_r109 φ ar ar' ar'' h hc hi, th_24_i _ _ h hc, hii, sub_zero]

/-- **ch04-111** (folio 60 (iii.)): 3 条件の下で、部分選択肢はどちらも元の選択肢より
確率が小さい (φ(a_r′)/h < φ(a_r)/h かつ φ(a_r″)/h < φ(a_r)/h)。 -/
theorem th_4_r111 {α : Type} (φ : α → IProp) (ar ar' ar'' : α) (h : IProp) (hc : Cons h)
    (H : DivisibleBy φ ar ar' ar'' h) :
    PrI (φ ar') h < PrI (φ ar) h ∧ PrI (φ ar'') h < PrI (φ ar) h := by
  obtain ⟨hi, hii, h1, h2⟩ := H
  have e := th_4_r110 φ ar ar' ar'' h hc hi hii
  have l1 := ax_range_lo_i (φ ar') h
  have l2 := ax_range_lo_i (φ ar'') h
  have p1 : 0 < PrI (φ ar') h := lt_of_le_of_ne l1 (Ne.symm h1)
  have p2 : 0 < PrI (φ ar'') h := lt_of_le_of_ne l2 (Ne.symm h2)
  constructor <;> linarith

/-- 可分の定義 ↔ 印刷の 3 条件 (部分選択肢を存在量化した形)。 -/
theorem divisible_iff {α : Type} (φ : α → IProp) (ar : α) (h : IProp) :
    Divisible φ ar h ↔ ∃ ar' ar'' : α,
      PrI (iiff (φ ar) (ior (φ ar') (φ ar''))) h = 1 ∧
      PrI (iand (φ ar') (φ ar'')) h = 0 ∧
      (PrI (φ ar') h ≠ 0 ∧ PrI (φ ar'') h ≠ 0) :=
  Iff.rfl

/-! ## §7 第5章 folio 66: ab/h < a/h unless b/ah = 1 (ch05-005) -/

/-- **ch05-005** (folio 66): ab/h < a/h unless b/ah = 1。b/ah が存在する範囲
(公理 (i) の但し書き Cons (a ∧ h)) で、b/ah ≠ 1 ならば ab/h < a/h。
Def. X 右形 ab/h = b/ah · a/h、a/h ≠ 0 は Def. VI の印刷の向き (cons_of_pos_src)。 -/
theorem th_5_r005 (a b h : IProp) (hca : Cons (iand a h)) (hb : PrI b (iand a h) ≠ 1) :
    PrI (iand a b) h < PrI a h := by
  have ha : PrI a h ≠ 0 := cons_of_pos_src a h hca
  have hx := def_X_right_i a b h
  have hpos : 0 < PrI a h := lt_of_le_of_ne (ax_range_lo_i a h) (Ne.symm ha)
  have hlt : PrI b (iand a h) < 1 := lt_of_le_of_ne (ax_range_hi_i b (iand a h)) hb
  rw [hx]
  nlinarith

/-- ch05-005 の別形: 但し書きの代わりに a/h ≠ 0 を置く (Ax. (iv. b)「PQ < P unless Q = 1
or P = 0」(folio 136) の第 2 の例外)。Cons を用いない。 -/
theorem th_5_r005_pos (a b h : IProp) (ha : PrI a h ≠ 0) (hb : PrI b (iand a h) ≠ 1) :
    PrI (iand a b) h < PrI a h := by
  have hx := def_X_right_i a b h
  have hpos : 0 < PrI a h := lt_of_le_of_ne (ax_range_lo_i a h) (Ne.symm ha)
  have hlt : PrI b (iand a h) < 1 := lt_of_le_of_ne (ax_range_hi_i b (iand a h)) hb
  rw [hx]
  nlinarith

/-- ch05-005 の「unless」: b/ah = 1 ならば ab/h = a/h。 -/
theorem th_5_r005_unless (a b h : IProp) (hb : PrI b (iand a h) = 1) :
    PrI (iand a b) h = PrI a h := by
  rw [def_X_right_i a b h, hb, one_mul]

/-- ch05-005 を「unless」の双条件として読んだ形: a/h ≠ 0 の下で
ab/h < a/h ↔ b/ah ≠ 1。 -/
theorem th_5_r005_iff (a b h : IProp) (ha : PrI a h ≠ 0) :
    PrI (iand a b) h < PrI a h ↔ PrI b (iand a h) ≠ 1 := by
  constructor
  · intro hlt hb
    rw [th_5_r005_unless a b h hb] at hlt
    exact lt_irrefl _ hlt
  · exact th_5_r005_pos a b h ha

/-! ## §8 第5章 folio 68: 好意的関連の十分条件と新しい証拠 (ch05-029, 030, 037) -/

/-- **ch05-029** (folio 68 (a)): 新しい証拠 h₁ と疑わしい論証 a/h について、
a/h̄₁h = 0 ならば h₁ は好意的に関連する (a/h₁h > a/h)。Def. IX と Def. X 左形で
a/h = a/h₁h · h₁/h、h₁/h < 1 と a/h > 0 から。Cons を用いない。 -/
theorem th_5_r029 (a h₁ h : IProp) (hnew : NewEvidence h₁ h) (hd : Doubtful a h)
    (h0 : PrI a (iand (inot h₁) h) = 0) : FavourablyRelevant a h₁ h := by
  unfold FavourablyRelevant
  have s := def_IX_i a h₁ h
  have e1 := def_X_left_i a (inot h₁) h
  have e2 := def_X_left_i a h₁ h
  rw [h0, zero_mul] at e1
  have hq0 := ax_range_lo_i h₁ h
  have hq1 : PrI h₁ h < 1 := lt_of_le_of_ne (ax_range_hi_i h₁ h) hnew
  have hapos : 0 < PrI a h := lt_of_le_of_ne (ax_range_lo_i a h) (Ne.symm hd.2)
  have hP0 := ax_range_lo_i a (iand h₁ h)
  have hprod : PrI a h = PrI a (iand h₁ h) * PrI h₁ h := by linarith
  have hP : 0 < PrI a (iand h₁ h) := by
    rcases lt_or_eq_of_le hP0 with hp | hp
    · exact hp
    · rw [← hp, zero_mul] at hprod; linarith
  rw [hprod]
  nlinarith [mul_lt_mul_of_pos_left hq1 hP]

/-- **ch05-030** (folio 68 (b)): 疑わしい論証 a/h について、a/h₁h = 1 ならば
h₁ は好意的に関連する。a/h ≠ 1 と値域だけで出る。 -/
theorem th_5_r030 (a h₁ h : IProp) (hd : Doubtful a h) (h1 : PrI a (iand h₁ h) = 1) :
    FavourablyRelevant a h₁ h := by
  unfold FavourablyRelevant
  rw [h1]
  exact lt_of_le_of_ne (ax_range_hi_i a h) hd.1

/-- ch05-029/030 をまとめた形 (folio 68 (1)「if either of the following conditions is
fulfilled」)。 -/
theorem th_5_favourable (a h₁ h : IProp) (hnew : NewEvidence h₁ h) (hd : Doubtful a h)
    (hcond : FavourableCondition a h₁ h) : FavourablyRelevant a h₁ h := by
  rcases hcond with h0 | h1
  · exact th_5_r029 a h₁ h hnew hd h0
  · exact th_5_r030 a h₁ h hd h1

/-- **ch05-037** (folio 68 脚注 1、h₁/h ≠ 1): 関連する証拠は新しい証拠である
(x/h₁h ≠ x/h ならば h₁/h ≠ 1、Cons h)。対偶は §4 irrelevant_of_certain。 -/
theorem th_5_r037 (x h₁ h : IProp) (hc : Cons h) (hrel : ¬ Irrelevant x h₁ h) :
    NewEvidence h₁ h := fun h1 => hrel (irrelevant_of_certain x h₁ h hc h1)

/-- ch05-037 の系: (b) a/h₁h = 1 と疑わしい a/h からは h₁ が新しいことが出る (Cons h)。 -/
theorem th_5_r030_new (a h₁ h : IProp) (hc : Cons h) (hd : Doubtful a h)
    (h1 : PrI a (iand h₁ h) = 1) : NewEvidence h₁ h := by
  apply th_5_r037 a h₁ h hc
  unfold Irrelevant
  rw [h1]
  exact fun e => hd.1 e.symm

end KeynesIrr

/-! ## §9 有限模型 (phase12b の世界模型の複製): 可分の 3 条件の証人と、但し書きの境界 -/

namespace KeynesIrr_model

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

def Ops.interp (S : Ops) (env : ℕ → S.IProp) : Form → S.IProp
  | .var n    => env n
  | .tru      => S.itrue
  | .fls      => S.inot S.itrue
  | .conj f g => S.iand (S.interp env f) (S.interp env g)
  | .disj f g => S.ior (S.interp env f) (S.interp env g)
  | .neg f    => S.inot (S.interp env f)
  | .iffF f g => S.iiff (S.interp env f) (S.interp env g)

/-- phase6c の公理群 13 本を場に写したもの (phase12b の Sys と同文)。 -/
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

abbrev W := Fin 3
abbrev M := Finset W

def mand (p q : M) : M := p ∩ q
def mor  (p q : M) : M := p ∪ q
def mnot (p : M) : M := pᶜ
def miff (p q : M) : M := (p ∩ q) ∪ (pᶜ ∩ qᶜ)
def mtrue : M := Finset.univ

def mu (wt : W → ℝ) (p : M) : ℝ := ∑ w ∈ p, wt w

/-- 条件付きの重みの比。h = ∅ のときは 0 と約定 (phase6c_model・phase12b と同じ)。 -/
noncomputable def prw (wt : W → ℝ) (p h : M) : ℝ :=
  if h = ∅ then 0 else mu wt (p ∩ h) / mu wt h

def Cons (h : M) : Prop := h.Nonempty

section Weighted

variable {wt : W → ℝ} (hw : ∀ w, 0 < wt w)

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

theorem ne_empty_of_prw_eq_one {p h : M} (H : prw wt p h = 1) : h ≠ ∅ := by
  rintro rfl
  rw [prw_of_empty] at H
  exact zero_ne_one H

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
theorem model_def_X_right_i (p q h : M) :
    prw wt (mand p q) h = prw wt q (mand p h) * prw wt p h := by
  have e : mand p q = mand q p := by simp [mand, Finset.inter_comm]
  rw [e]
  exact model_def_X_left_i hw q p h

theorem model_def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q :=
  fun H => (eq_div_iff hQ).mpr H

include hw in
theorem model_ax_range_lo_i (p h : M) : 0 ≤ prw wt p h := by
  unfold prw
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (mu_nonneg hw _) (mu_nonneg hw _)

include hw in
theorem model_ax_range_hi_i (p h : M) : prw wt p h ≤ 1 := by
  by_cases hh : h = ∅
  · simp [prw, hh]
  · have hpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
    rw [prw_of_ne hh, div_le_one hpos]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun w _ _ => (hw w).le)

include hw in
theorem model_def_VIII_i (a b h : M) (hca : Cons (mand a h)) (hcb : Cons (mand b h)) :
    prw wt (miff a b) h = 1 ↔ (prw wt b (mand a h) = 1 ∧ prw wt a (mand b h) = 1) := by
  have hca' : mand a h ≠ ∅ := ne_empty_of_cons hca
  have hcb' : mand b h ≠ ∅ := ne_empty_of_cons hcb
  have hh : h ≠ ∅ := ne_empty_of_inter hca'
  rw [prw_eq_one_iff hw hh, prw_eq_one_iff hw hca', prw_eq_one_iff hw hcb']
  exact subset_miff_iff a b h

include hw in
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

noncomputable def wOps (wt : W → ℝ) : Ops where
  IProp := M
  iand := mand
  ior := mor
  inot := mnot
  iiff := miff
  itrue := mtrue
  PrI := prw wt
  Cons := Cons

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
theorem model_ax_iii_taut (f : Form) (env : ℕ → M) (h : M) (hc : Cons h) (ht : Taut f) :
    prw wt (finInterp env f) h = 1 := by
  rw [prw_eq_one_iff hw (ne_empty_of_cons hc)]
  intro w _
  rw [mem_finInterp]
  exact ht _

theorem model_cons_true : Cons mtrue := Finset.univ_nonempty

include hw in
theorem model_cons_of_pos_src (a h : M) : Cons (mand a h) → prw wt a h ≠ 0 := by
  intro hca
  have hh : h ≠ ∅ := ne_empty_of_inter (ne_empty_of_cons hca)
  have hhpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [prw_of_ne hh]
  exact (div_pos (mu_pos hw hca) hhpos).ne'

theorem model_cons_of_pos (a h : M) : prw wt a h ≠ 0 → Cons h → Cons (mand a h) := by
  intro hne hc
  by_contra hz
  apply hne
  rw [Cons, Finset.not_nonempty_iff_eq_empty] at hz
  rw [prw_of_ne (ne_empty_of_cons hc)]
  simp only [mand] at hz
  simp [hz, mu]

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
/-- 正の重みの模型は phase6c の公理群 13 本をすべて満たす (phase12b の wSys と同じ)。 -/
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

end Weighted2

/-! ### 等しい重み (1, 1, 1) の模型 -/

def wt₁ : W → ℝ := fun _ => 1

theorem wt₁_pos : ∀ w, 0 < wt₁ w := fun _ => by norm_num [wt₁]

/-- 可分の 3 条件 (folio 60) を場 S の上で書いたもの (§3 の DivisibleBy と同文)。 -/
def DivisibleByS (S : Ops) {α : Type} (φ : α → S.IProp) (ar ar' ar'' : α) (h : S.IProp) :
    Prop :=
  S.PrI (S.iiff (φ ar) (S.ior (φ ar') (φ ar''))) h = 1 ∧
  S.PrI (S.iand (φ ar') (φ ar'')) h = 0 ∧
  (S.PrI (φ ar') h ≠ 0 ∧ S.PrI (φ ar'') h ≠ 0)

/-- 選択肢 a_r := {0, 1}、部分選択肢 a_r′ := {0}、a_r″ := {1}、φ := 恒等、h := ⊤。 -/
def ar₀ : M := {0, 1}
def ar₀' : M := {0}
def ar₀'' : M := {1}

theorem prw₁_univ_singleton (i : W) : prw wt₁ {i} mtrue = 1 / 3 := by
  rw [prw_of_ne (ne_empty_of_cons model_cons_true)]
  simp [mu, wt₁, mtrue]

/-- **可分の 3 条件の証人** (ch04-109–111): 全公理を満たす模型 (重み (1,1,1)) で、整合な
h = ⊤ の下、{0, 1} は {0} と {1} に分けられ (i.)(ii.)(iii.) が同時に成り立つ。 -/
theorem model_divisible_witness :
    Sys (wOps wt₁) ∧ (wOps wt₁).Cons mtrue ∧
      DivisibleByS (wOps wt₁) (fun x : M => x) ar₀ ar₀' ar₀'' mtrue := by
  refine ⟨wSys wt₁_pos, model_cons_true, ?_, ?_, ?_, ?_⟩
  · show prw wt₁ (miff ar₀ (mor ar₀' ar₀'')) mtrue = 1
    have e : miff ar₀ (mor ar₀' ar₀'') = mtrue := by decide
    rw [e, prw_eq_one_iff wt₁_pos (ne_empty_of_cons model_cons_true)]
  · show prw wt₁ (mand ar₀' ar₀'') mtrue = 0
    have e : mand ar₀' ar₀'' = ∅ := by decide
    rw [e, prw_of_ne (ne_empty_of_cons model_cons_true)]
    simp [mu]
  · show prw wt₁ ar₀' mtrue ≠ 0
    rw [ar₀', prw₁_univ_singleton]; norm_num
  · show prw wt₁ ar₀'' mtrue ≠ 0
    rw [ar₀'', prw₁_univ_singleton]; norm_num

/-- **ch04-054 の但し書きの境界**: 全公理を満たす模型で、Cons h かつ x/h₁h = x/h だが
x/h̄₁h ≠ x/h (x := {0}、h₁ := h := ⊤; h̄₁h = ∅ は整合でなく、約定により x/∅ = 0)。
但し書き Cons (h̄₁ ∧ h) を落とした印刷形は公理群から導けない。 -/
theorem model_r054_needs_cons :
    ∃ S : Ops, Sys S ∧ ∃ x h₁ h : S.IProp, S.Cons h ∧ ¬ S.Cons (S.iand (S.inot h₁) h) ∧
      S.PrI x (S.iand h₁ h) = S.PrI x h ∧ S.PrI x (S.iand (S.inot h₁) h) ≠ S.PrI x h := by
  refine ⟨wOps wt₁, wSys wt₁_pos, ({0} : M), mtrue, mtrue, model_cons_true, ?_, ?_, ?_⟩
  · show ¬ Cons (mand (mnot mtrue) mtrue)
    have e : mand (mnot mtrue) mtrue = ∅ := by decide
    rw [e, Cons]; simp
  · show prw wt₁ {0} (mand mtrue mtrue) = prw wt₁ {0} mtrue
    have e : mand mtrue mtrue = mtrue := by decide
    rw [e]
  · show prw wt₁ {0} (mand (mnot mtrue) mtrue) ≠ prw wt₁ {0} mtrue
    have e : mand (mnot mtrue) mtrue = ∅ := by decide
    rw [e, prw_of_empty, prw₁_univ_singleton]; norm_num

/-- **ch05-005 の但し書きの境界**: 全公理を満たす模型で、b/ah ≠ 1 だが ab/h < a/h は偽
(a := ∅、b := h := ⊤: ah = ∅ は整合でなく a/h = 0)。但し書き Cons (a ∧ h) も a/h ≠ 0 も
無い印刷形は公理群から導けない (Ax. (iv. b) の第 2 の例外 P = 0 にあたる)。 -/
theorem model_r005_needs_cons :
    ∃ S : Ops, Sys S ∧ ∃ a b h : S.IProp, S.Cons h ∧ S.PrI b (S.iand a h) ≠ 1 ∧
      ¬ (S.PrI (S.iand a b) h < S.PrI a h) := by
  refine ⟨wOps wt₁, wSys wt₁_pos, (∅ : M), mtrue, mtrue, model_cons_true, ?_, ?_⟩
  · show prw wt₁ mtrue (mand ∅ mtrue) ≠ 1
    have e : mand ∅ mtrue = ∅ := by decide
    rw [e, prw_of_empty]; norm_num
  · show ¬ (prw wt₁ (mand ∅ mtrue) mtrue < prw wt₁ ∅ mtrue)
    have e : mand ∅ mtrue = ∅ := by decide
    rw [e]
    exact lt_irrefl _

end KeynesIrr_model

/-! ## 監査クエリ -/

#check @KeynesIrr.th_4_r054
#check @KeynesIrr.th_5_r005
#check @KeynesIrr_model.model_divisible_witness

-- 定義 (行の印刷形をそのまま写したもの)
#print axioms KeynesIrr.Irrelevant
#print axioms KeynesIrr.StrictlyIrrelevant
#print axioms KeynesIrr.IndependentComplementary
#print axioms KeynesIrr.RelevantPart
#print axioms KeynesIrr.DivisibleBy
#print axioms KeynesIrr.Divisible
#print axioms KeynesIrr.NewEvidence
#print axioms KeynesIrr.Doubtful
#print axioms KeynesIrr.FavourablyRelevant
#print axioms KeynesIrr.FavourableCondition
-- 再証明した phase6c の定理
#print axioms KeynesIrr.th_13_1_i
#print axioms KeynesIrr.th_12_i_short
#print axioms KeynesIrr.th_24_i
#print axioms KeynesIrr.th_13_13_conj_i
#print axioms KeynesIrr.irrelevant_of_certain
-- 第4章 folio 55 (ch04-054, 060–066)
#print axioms KeynesIrr.th_4_r054
#print axioms KeynesIrr.th_4_r054_of_new
#print axioms KeynesIrr.th_4_r060
#print axioms KeynesIrr.th_4_r061
#print axioms KeynesIrr.th_4_r062
#print axioms KeynesIrr.th_4_r063
#print axioms KeynesIrr.th_4_r064
#print axioms KeynesIrr.th_4_r065
#print axioms KeynesIrr.th_4_r066
#print axioms KeynesIrr.th_4_r066_new
-- 第4章 folio 60 (ch04-109–111)
#print axioms KeynesIrr.th_4_r109
#print axioms KeynesIrr.th_4_r110
#print axioms KeynesIrr.th_4_r111
#print axioms KeynesIrr.divisible_iff
-- 第5章 folio 66・68 (ch05-005, 029, 030, 037)
#print axioms KeynesIrr.th_5_r005
#print axioms KeynesIrr.th_5_r005_pos
#print axioms KeynesIrr.th_5_r005_unless
#print axioms KeynesIrr.th_5_r005_iff
#print axioms KeynesIrr.th_5_r029
#print axioms KeynesIrr.th_5_r030
#print axioms KeynesIrr.th_5_favourable
#print axioms KeynesIrr.th_5_r037
#print axioms KeynesIrr.th_5_r030_new
-- 有限模型
#print axioms KeynesIrr_model.wSys
#print axioms KeynesIrr_model.model_divisible_witness
#print axioms KeynesIrr_model.model_r054_needs_cons
#print axioms KeynesIrr_model.model_r005_needs_cons
