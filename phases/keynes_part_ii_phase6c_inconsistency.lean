/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 6c 不整合の記録
#
# 新井一成・Claude共著、2026年10月20日 (B09)
# **修復前の phase6c 公理群 (KeynesI) から False が導けることの記録**
#
# ## 経緯
#   phases/keynes_part_ii_phase6c.lean の 2026-07-08 版は、Keynes 第12章 §5 の
#   公理 (i) にある但し書き「h が矛盾する連言でない (h is not an inconsistent
#   conjunction)」(folio 135) を公理群に写し取っていなかった。その結果、
#   ax_iii_taut (任意の証拠 h の下で恒真式は確実) と def_VIII_i (Def. VIII の
#   双条件読み) から次の経路で False が導ける (発見: B06、2026-10-19)。
#
#   経路:
#     1. ax_iii_taut: (a ≡ a)/h = 1 が任意の h で成立。
#     2. def_VIII_i の逆向き (→): a/(a ∧ h) = 1。
#     3. a := ¬⊤, h := ⊤ とおくと (¬⊤)/((¬⊤) ∧ ⊤) = 1。
#     4. 補完律 th_13_1_i (k := (¬⊤) ∧ ⊤): ⊤/k + (¬⊤)/k = 1、⊤/k = 1 より (¬⊤)/k = 0。
#     5. 1 = 0。
#
#   原典 (唯一の基準、folio 135、第12章 §5 公理 (i)):
#   「(i.) Provided that a and h are propositions or conjunctions of propositions
#    or disjunctions of propositions, and that h is not an inconsistent
#    conjunction, there exists one and only one relation of probability P between
#    a as conclusion and h as premiss. Thus any conclusion a bears to any
#    consistent premiss h one and only one relation of probability.」
#   手順 2 の前提 (¬⊤) ∧ ⊤ は矛盾する連言なので、原典では a/((¬⊤) ∧ ⊤) は存在しない。
#   形式化がこの但し書きを落としたことが原因である。
#
# ## 本ファイルの役割
#   修復前の公理群のうち本経路に要る公理だけを namespace KeynesI_old に複製し
#   (def_XI_i と値域公理 ax_range_lo_i/hi_i は不要なので省略)、False を導く定理
#   th_6c_old_inconsistent を残す。修復版は phase6c.lean (Cons 述語付き)、
#   修復版の無矛盾性は phase6c_model.lean (有限モデル) に示す。本ファイルは
#   修復後も記録として残す。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase6c_inconsistency.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KeynesI_old

/-! ## 修復前の公理群 (phase6c 2026-07-08 版から本経路に要るものだけを複製、
def_XI_i と値域公理 ax_range_lo_i/hi_i は省略) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h

/-- 修復前の Def. VIII 双条件読み (但し書きなし)。 -/
axiom def_VIII_i (a b h : IProp) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

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

/-- 修復前の Ax.(iii): 任意の証拠 h (矛盾する連言を含む) の下で恒真式は確実。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Taut f → PrI (interp env f) h = 1

/-! ## 修復前の定理 (同版を基に simp 引数から Taut を外した写し) -/

theorem th_12_i (a b h : IProp) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h := by
  obtain ⟨hba, hab⟩ := (def_VIII_i a b h).mp hcert
  have hl := def_X_left_i a b h
  have hr := def_X_right_i a b h
  rw [hab, one_mul] at hl
  rw [hba, one_mul] at hr
  linarith

theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i _ _ h (ax_iii_taut (Form.iffF f g) env h ht)

theorem itrue_certain (h : IProp) : PrI itrue h = 1 :=
  ax_iii_taut Form.tru (fun _ => itrue) h (fun _ => rfl)

theorem th_13_1_i (a h : IProp) : PrI a h + PrI (inot a) h = 1 := by
  have step := def_IX_i itrue a h
  have e1 : PrI (iand itrue (inot a)) h = PrI (inot a) h :=
    subst_taut (Form.conj Form.tru (Form.neg (Form.var 0))) (Form.neg (Form.var 0))
      (fun _ => a) h (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have e2 : PrI (iand itrue a) h = PrI a h :=
    subst_taut (Form.conj Form.tru (Form.var 0)) (Form.var 0)
      (fun _ => a) h (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have e3 := itrue_certain h
  linarith [step, e1, e2, e3]

/-! ## 不整合 -/

/-- **手順 1–2**: 但し書きなしの ax_iii_taut と def_VIII_i から、任意の a, h について
a/(a ∧ h) = 1 (矛盾する前提 a ∧ h の場合を含む)。原典ではこの前提の下の確率関係は
存在しない (folio 135、公理 (i))。 -/
theorem pr_self_evidence_old (a h : IProp) : PrI a (iand a h) = 1 := by
  have hcert : PrI (iiff a a) h = 1 :=
    ax_iii_taut (Form.iffF (Form.var 0) (Form.var 0)) (fun _ => a) h
      (by intro v; simp [evalB])
  exact ((def_VIII_i a a h).mp hcert).1

/-- **手順 3–5**: 修復前の公理群は False を導く。 -/
theorem th_6c_old_inconsistent : False := by
  -- k := (¬⊤) ∧ ⊤ は矛盾する連言
  have h1 : PrI (inot itrue) (iand (inot itrue) itrue) = 1 :=
    pr_self_evidence_old (inot itrue) itrue
  have h2 := th_13_1_i itrue (iand (inot itrue) itrue)
  have h3 := itrue_certain (iand (inot itrue) itrue)
  linarith

end KeynesI_old

/-! ## 監査クエリ -/

#check @KeynesI_old.pr_self_evidence_old
#check @KeynesI_old.th_6c_old_inconsistent

-- 矛盾の被導出関係: def_VIII_i (逆向き) と ax_iii_taut (但し書きなし) の両方が現れる
#print axioms KeynesI_old.pr_self_evidence_old
#print axioms KeynesI_old.th_6c_old_inconsistent
