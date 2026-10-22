/-
# Keynes (1921) *A Treatise on Probability* Part III — Lean 4 Phase 9c
# 第 XXII 章 "The Justification of these Methods" (folio 251–264) と
# Notes on Part III (ii.) "On the Use of the Term *Cause*" (folio 276–277)
#
# 基準: 1921 年 Macmillan 初版の頁画像 (folio 252, 253, 254, 255, 259, 260, 276, 277 を直接照合)。
# 台帳: 第III部帰納/台帳_ch21_22_正当化.md (F22.1–F22.21、表記不統一フラグ T1–T4、組版注記 N1–N3)。
#
# ## 構成
#   §0  内包的な命題集合 IProp と確率関係 PrI — phase6c の公理群の部分集合 (def_XI_i を置かない;
#       各 phase は自己完結)
#   §1  第 II 部の公理から導く補題 (連言の単調性、確実な命題の付加、連言成分の確実性)
#   §2  F22.1, F22.2, F22.4 — §2, §4 の設定 (肯定的類推、一般化の問い、性質の集合の包括性)。
#       F22.13 (folio 255 §4、二集合 a_r, a_s の定義) は定義のみで定理化対象外
#   §3  F22.9, F22.10, F22.11, F22.12 — §3 純粋帰納の予備条件と第 XX 章の極限 (folio 254–255)。
#       g := g(φf) とおき、F22.9 "g/h = p_0, p_0 は有限" は限定独立多様性から導く
#   §4  F22.17, F22.18, F22.19 — §11 帰納仮説 H, H′ と帰納法 (folio 259–260)
#   §5  Notes (ii.) 因果定義 (i.)–(x.) と §4 の「確率上の依存」(folio 276–277)、
#       E-III-4 ((viii.) の b/hk に l が無い) の印刷形と l を補った形、両者が異なる有限モデル
#   §6  有限モデル FinSys が第 II 部の公理の形 (値域、Def. VIII、Def. IX、Def. X、Ax.(iii)) を
#       満たすことの確認 (FinSys_PartII)、F22.18 の補充前提の必要性 (FinSys での反例)、
#       追加公理それぞれについて「FinSys_PartII ∧ ¬(追加公理の FinSys での写し)」(indep_ax_22_*)
#
# ## §0 の公理群について (2026-10-20 注記)
# §0 は phase6c の初版公理群の写しである。この公理群 (def_VIII_i と ax_iii_taut を任意の前提 h
# について置く形) は修復前は矛盾する (phase6c_inconsistency: 第 XII 章 公理 (i) の但し書き
# "h is not an inconsistent conjunction" (folio 135) が落ちていた)。修復は別依頼 B09 で進行中
# (Cons 述語を置き、ax_iii_taut と def_VIII_i に Cons の前提を付ける)。本ファイルは修復後に
# §0 を修復版に合わせて再コンパイルする。それまで、§1–§5 の KeynesI 上の定理は「印刷の式が
# 第 II 部の公理の形から導けること」の記録として読み、矛盾する公理群の上では「導けない」という
# 主張は成り立たない (何でも導ける) ので、本ファイルはそのような主張を置かない。
#
# ## 追加公理 (印刷が前提として挙げる条件。名前付きで宣言し、末尾の #print axioms の
# 出力で、どの定理の導出に用いられるかを示す)
#   ax_22_limited_independent_variety  … 限定独立多様性 (folio 253–254 §3; 260 §11 の帰納仮説):
#                                        どの φ, f についても g(φf)/h は有限
#   ax_22_10_instances_certain         … x_r/gh = 1 (folio 254; 前提)
#   ax_22_11_eps_finite                … x_r/x_1x_2…x_{r−1}ḡh = 1 − ε, ε は有限 (folio 254; 印刷は等号)
#   ax_22_17_CH_finite                 … C/H は有限値をもつ (folio 259–260)
#   ax_22_19_HH'_finite                … H/H′ は有限値をもつ (folio 260)
#   (第 1 回で公理としていた ax_22_9_p0_finite "g/h = p_0, p_0 は有限" は、g := g(φf) とおくことで
#    ax_22_limited_independent_variety から導かれる定理 th_22_9_src になった。)
#   §6 に、空でない前提について第 II 部の公理の形を満たす有限モデル FinSys が、記号を具体的に
#   とると上の各条件 (と旧 ax_22_9_p0_finite の内容) を満たさないことを定理として置く
#   (indep_ax_22_*: 各定理は FinSys_PartII ∧ ¬X の形)。主張の範囲はこの有限モデルに限る。
#   「追加公理は第 II 部の公理から導けない」とは主張しない (上の注記)。
#
# ## Notes (ii.) の定義のうち、本ファイルの定理が用いるもの
#   def_viii_src … def_viii_l_imp_src (前提の並べ替えを仮定した下での l 補正形 ⇒ 印刷形)
#   def_viii_l   … def_viii_l_imp_src, def_viii_l_dep ((viii.) l 補正形 ⇒ §4 の確率上の依存)
#   def_ix       … def_ix_dep ((ix.) ⇒ §4 の確率上の依存)
#   def_x_src    … def_x_src_symm (因果的独立の対称性)
#   dep_for_prob … def_viii_l_dep, def_ix_dep
#   (vi.)–(ix.) の "there is an existential proposition h" を ∃ h として量化するが、
#   (viii.)(ix.) の印刷は h を量化せずに書く (索引に記録)。
#
# ## 前提の連言の順序について (転記上の約束)
# Keynes は前提 hx_1x_2…x_n, HE, akl などを連言として書き、その順序を区別しない。
# 内包的な命題集合では Def. X の両形が「新たに付す命題を先頭」に置く形
# (PrI p (iand q h)) を与えるため、本ファイルでは Lean 上の前提を
# `iand (x_1…x_n) h`, `iand E H` の順で書く。命題の内容の逸脱ではない。
# 第 II 部の公理群には前提側の連言を並べ替える原理が無い (所見候補として報告)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_iii_phase9c.lean
-/

import Mathlib

namespace KeynesI

/-! ## §0 内包的な命題集合と確率関係 (phase6c の公理群の部分集合: def_XI_i は置かない) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

/-- 確率関係 a/h (結論 a、前提 h)。 -/
axiom PrI : IProp → IProp → ℝ

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- Def. VIII (等値の定義) の双条件読み (phase6c と同一)。 -/
axiom def_VIII_i (a b h : IProp) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- 命題論理の構文 (論証的同値の対象言語; phase6c と同一)。 -/
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

/-- Ax.(iii): 論証的トートロジーの任意の解釈は、任意の前提の下で確実。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Taut f → PrI (interp env f) h = 1

/-- Th.(12) 内包版 (phase6c の証明を再掲)。 -/
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

/-- Th.(13.1) 補完律 (phase6c の証明を再掲)。 -/
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

/-! ## §1 第 II 部の公理から導く補題 -/

/-- 連言の確率は左成分の確率を超えない (Def. X 右形と値域)。 -/
theorem pr_iand_le_left (p q h : IProp) : PrI (iand p q) h ≤ PrI p h := by
  rw [def_X_right_i]
  have h0 := ax_range_lo_i p h
  have h1 := ax_range_hi_i q (iand p h)
  have h2 := ax_range_lo_i q (iand p h)
  nlinarith

/-- 連言の確率は右成分の確率を超えない (Def. X 左形と値域)。 -/
theorem pr_iand_le_right (p q h : IProp) : PrI (iand p q) h ≤ PrI q h := by
  rw [def_X_left_i]
  have h0 := ax_range_lo_i q h
  have h1 := ax_range_hi_i p (iand q h)
  have h2 := ax_range_lo_i p (iand q h)
  nlinarith

/-- 結論側の連言の交換 (Ax.(iii) による代入)。 -/
theorem pr_iand_comm (p q h : IProp) : PrI (iand p q) h = PrI (iand q p) h :=
  subst_taut (Form.conj (Form.var 0) (Form.var 1)) (Form.conj (Form.var 1) (Form.var 0))
    (fun n => match n with | 0 => p | _ => q) h
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])

/-- 結論側の確実な命題 itrue は落とせる。 -/
theorem pr_iand_itrue (a h : IProp) : PrI (iand a itrue) h = PrI a h :=
  subst_taut (Form.conj (Form.var 0) Form.tru) (Form.var 0)
    (fun _ => a) h (by intro v; cases h0 : v 0 <;> simp [evalB, h0])

/-- 前提側の確実な命題 itrue も落とせる: a/(itrue h) = a/h (Def. X 左形経由)。 -/
theorem pr_premiss_itrue (a h : IProp) : PrI a (iand itrue h) = PrI a h := by
  have hX := def_X_left_i a itrue h
  rw [itrue_certain, mul_one, pr_iand_itrue] at hX
  exact hX.symm

/-- 確実な命題を結論の連言に加えても確率は変わらない: b/h = 1 ならば ab/h = a/h。 -/
theorem pr_iand_certain (a b h : IProp) (hb : PrI b h = 1) :
    PrI (iand a b) h = PrI a h := by
  have hIX := def_IX_i a b h
  have hc := th_13_1_i b h
  have hle := pr_iand_le_right a (inot b) h
  have hlo := ax_range_lo_i (iand a (inot b)) h
  linarith

/-- 確実な命題は、不可能でない前提を付け加えても確実: b/h = 1, a/h ≠ 0 ならば b/ah = 1。 -/
theorem certain_add_premiss (a b h : IProp) (hb : PrI b h = 1) (ha : PrI a h ≠ 0) :
    PrI b (iand a h) = 1 := by
  have hX := def_X_right_i a b h
  rw [pr_iand_certain a b h hb] at hX
  have hprod : (PrI b (iand a h) - 1) * PrI a h = 0 := by linarith
  rcases mul_eq_zero.mp hprod with h1 | h1
  · linarith
  · exact absurd h1 ha

/-- 確実な二命題の連言は確実。 -/
theorem certain_iand (a b h : IProp) (ha : PrI a h = 1) (hb : PrI b h = 1) :
    PrI (iand a b) h = 1 := by
  rw [pr_iand_certain a b h hb]; exact ha

/-- 有限個の命題の連言 a_1 a_2 … a_k (k = 0 では確実な命題 itrue)。 -/
noncomputable def conjFin : (k : ℕ) → (Fin k → IProp) → IProp
  | 0, _ => itrue
  | k + 1, f => iand (conjFin k (fun i => f i.castSucc)) (f (Fin.last k))

/-- 変数 var 0 … var (k−1) の連言 (構文側)。 -/
def conjVars : ℕ → Form
  | 0 => Form.tru
  | k + 1 => Form.conj (conjVars k) (Form.var k)

theorem interp_conjVars (env : ℕ → IProp) :
    ∀ k, interp env (conjVars k) = conjFin k (fun i => env i.val)
  | 0 => rfl
  | k + 1 => by
      simp [conjVars, interp, conjFin, interp_conjVars env k]

theorem evalB_conjVars (v : ℕ → Bool) :
    ∀ k, (evalB v (conjVars k) = true ↔ ∀ i, i < k → v i = true)
  | 0 => by simp [conjVars, evalB]
  | k + 1 => by
      simp only [conjVars, evalB, Bool.and_eq_true, evalB_conjVars v k]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h1 i hi
        · exact h2
      · intro h
        exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h k (Nat.lt_succ_self k)⟩

/-- 連言にその成分を付け加えても同値 (トートロジー)。 -/
theorem taut_conj_component (k m : ℕ) (hm : m < k) :
    Taut (Form.iffF (Form.conj (conjVars k) (Form.var m)) (conjVars k)) := by
  intro v
  simp only [evalB]
  cases hc : evalB v (conjVars k)
  · simp
  · have := (evalB_conjVars v k).mp hc m hm
    simp [this]

/-- 添字 i < k では f i、それ以外では itrue を返す環境。 -/
noncomputable def envOf (k : ℕ) (f : Fin k → IProp) : ℕ → IProp :=
  fun i => if hi : i < k then f ⟨i, hi⟩ else itrue

theorem envOf_val (k : ℕ) (f : Fin k → IProp) (i : Fin k) : envOf k f i.val = f i := by
  simp [envOf, i.isLt]

/-- 連言の各成分は、その連言 (不可能でない) を前提に加えると確実。 -/
theorem conjFin_component_certain (k : ℕ) (f : Fin k → IProp) (m : Fin k) (h : IProp)
    (hne : PrI (conjFin k f) h ≠ 0) : PrI (f m) (iand (conjFin k f) h) = 1 := by
  have hsub := subst_taut (Form.conj (conjVars k) (Form.var m.val)) (conjVars k) (envOf k f) h
    (taut_conj_component k m.val m.isLt)
  simp only [interp, interp_conjVars, envOf_val] at hsub
  have hX := def_X_right_i (conjFin k f) (f m) h
  rw [hsub] at hX
  have hprod : (PrI (f m) (iand (conjFin k f) h) - 1) * PrI (conjFin k f) h = 0 := by linarith
  rcases mul_eq_zero.mp hprod with h1 | h1
  · linarith
  · exact absurd h1 hne

/-! ## §2 第 XXII 章 §2, §4 の設定 — F22.1, F22.2, F22.13 (folio 252, 255) -/

/-- **F22.1** (folio 252 §2): "a set of n instances which have r known qualities,
a_1a_2 . . . a_r in common, these r qualities constituting the known positive analogy."
対象の型 Obj 上の性質 a_i : Obj → IProp と事例 x_j : Obj について、
既知の肯定的類推は連言 ⋀_{j, i} a_i(x_j)。 -/
noncomputable def posAnalogy {Obj : Type} {n r : ℕ} (a : Fin r → Obj → IProp) (x : Fin n → Obj) :
    IProp :=
  conjFin (n * r) (fun m => a (finProdFinEquiv.symm m).2 (x (finProdFinEquiv.symm m).1))

/-- **th_22_1** (F22.1): 既知の肯定的類推 (不可能でない) を前提に加えると、
各事例 x_j の各性質 a_i は確実。 -/
theorem th_22_1 {Obj : Type} {n r : ℕ} (a : Fin r → Obj → IProp) (x : Fin n → Obj)
    (h : IProp) (hne : PrI (posAnalogy a x) h ≠ 0) (i : Fin r) (j : Fin n) :
    PrI (a i (x j)) (iand (posAnalogy a x) h) = 1 := by
  have := conjFin_component_certain (n * r)
    (fun m => a (finProdFinEquiv.symm m).2 (x (finProdFinEquiv.symm m).1))
    (finProdFinEquiv (j, i)) h hne
  simpa [posAnalogy] using this

/-- **F22.2** (folio 252 §2): "three (say) are picked out, namely, a_1, a_2, a_3" —
前提側の性質の連言 a_1 a_2 a_3 (対象 o について)。 -/
noncomputable def prem_22_2 {Obj : Type} (a : ℕ → Obj → IProp) (o : Obj) : IProp :=
  iand (a 1 o) (iand (a 2 o) (a 3 o))

/-- **F22.2** (folio 252 §2): "certain other qualities which we have picked out, namely,
a_{r−1}, a_r" — 結論側の性質の連言 a_{r−1} a_r。 -/
noncomputable def concl_22_2 {Obj : Type} (a : ℕ → Obj → IProp) (r : ℕ) (o : Obj) : IProp :=
  iand (a (r - 1) o) (a r o)

/-- "whether the qualities a_{r−1}, a_r are *bound up* with the qualities a_1, a_2, a_3":
一般化 g がこれを述べるとは、どの対象 o についても、g と前提側の性質の下で
結論側の性質が確実であること。 -/
def BoundUp {Obj : Type} (g h : IProp) (prem concl : Obj → IProp) : Prop :=
  ∀ o, PrI (concl o) (iand g (iand (prem o) h)) = 1

/-- 一般化の確率は、任意の対象についての結論側の性質の確率を下から抑える。 -/
theorem gen_le_instance {Obj : Type} (g h : IProp) (prem concl : Obj → IProp)
    (hg : BoundUp g h prem concl) (o : Obj) :
    PrI g (iand (prem o) h) ≤ PrI (concl o) (iand (prem o) h) := by
  have hX := def_X_right_i g (concl o) (iand (prem o) h)
  rw [hg o, one_mul] at hX
  rw [← hX]
  exact pr_iand_le_right _ _ _

/-- **th_22_2** (F22.2): "with what probability all objects having these three qualities
have also certain other qualities" — その確率 g/(a_1a_2a_3(o) h) は、どの対象 o についても
a_{r−1}a_r(o)/(a_1a_2a_3(o) h) を超えない。印刷は問いの設定であって定理文ではない。
この定理文は、問いの設定 (一般化 g が「bound up」を述べること = BoundUp) から読み込んだ
解釈であり、印刷の命題そのものではない。 -/
theorem th_22_2 {Obj : Type} (a : ℕ → Obj → IProp) (r : ℕ) (g h : IProp)
    (hg : BoundUp g h (prem_22_2 a) (concl_22_2 a r)) (o : Obj) :
    PrI g (iand (prem_22_2 a o) h) ≤ PrI (concl_22_2 a r o) (iand (prem_22_2 a o) h) :=
  gen_le_instance g h (prem_22_2 a) (concl_22_2 a r) hg o

/-- **F22.13** (folio 255 §4、定義のみ・定理化対象外): "The numerous characters of an object
which are known to us may be represented by a_1a_2 . . . a_n. We select two sets of these,
a_r and a_s" — 添字の有限列 S で与えた性質の集合の連言。印刷には不等式が無いので
F22.13 自体は定理にしない (台帳: 定義)。th_22_4 がこの定義を用いる。 -/
noncomputable def qualSet {Obj : Type} (a : ℕ → Obj → IProp) (o : Obj) {m : ℕ}
    (S : Fin m → ℕ) : IProp :=
  conjFin m (fun i => a (S i) o)

/-- **th_22_4** (F22.4, folio 252 §2): "We distrust the generalisation if the terms typified by
a_{r−1}a_r are numerous and comprehensive" の第 II 部で言える部分 — 前提側の性質の集合 S と
結論側の集合 T について、結論側の集合をさらに U だけ包括的にすると、S を前提とする確率は
上がらない。(F22.4 の後半 "We trust it if the terms typified by a_1a_2a_3 are numerous and
comprehensive" は群構造の仮定を要するので、本ファイルでは定理にしない。) -/
theorem th_22_4 {Obj : Type} (a : ℕ → Obj → IProp) (o : Obj) {ms mt mu : ℕ}
    (S : Fin ms → ℕ) (T : Fin mt → ℕ) (U : Fin mu → ℕ) (h : IProp) :
    PrI (iand (qualSet a o T) (qualSet a o U)) (iand (qualSet a o S) h)
      ≤ PrI (qualSet a o T) (iand (qualSet a o S) h) :=
  pr_iand_le_left _ _ _

/-! ## §3 第 XXII 章 §3 — 純粋帰納の予備条件 F22.9, F22.10, F22.11, F22.12 (folio 254–255)

folio 254: "If x_r, etc., are the instances,
    g/h = p_0, where p_0 is finite,
    x_r/gh = 1, etc.,
and x_r/x_1x_2 . . . x_{r-1}ḡh = 1 − ε, where ε is finite.
And hence, by the argument of Chapter XX., the probability of a generalisation, based on such
evidence as this, is capable, under suitable conditions, of tending towards certainty as a
limit, when the number of instances is increased." -/

/-- 事例の連言 x_1 x_2 … x_n (n = 0 では itrue)。 -/
noncomputable def conjInst (x : ℕ → IProp) : ℕ → IProp
  | 0 => itrue
  | n + 1 => iand (conjInst x n) (x (n + 1))

/-- p_n = g/hx_1x_2…x_n (第 XX 章の記法; 前提は `iand (x_1…x_n) h` の順で書く)。 -/
noncomputable def p_ (g h : IProp) (x : ℕ → IProp) (n : ℕ) : ℝ :=
  PrI g (iand (conjInst x n) h)

/-- x_1x_2…x_n/ḡh。 -/
noncomputable def Y_ (g h : IProp) (x : ℕ → IProp) (n : ℕ) : ℝ :=
  PrI (conjInst x n) (iand (inot g) h)

/-- x_r/x_1x_2…x_{r−1}ḡh (r = n + 1 と書く; r = 1 では前提は itrue ḡh)。 -/
noncomputable def y_ (g h : IProp) (x : ℕ → IProp) (n : ℕ) : ℝ :=
  PrI (x (n + 1)) (iand (conjInst x n) (iand (inot g) h))

/-- 補助: p_0 = g/h — 添字 0 の p_ は à priori 確率 g/h に一致する (前提側の itrue を落とす)。 -/
theorem p_zero (g h : IProp) (x : ℕ → IProp) : p_ g h x 0 = PrI g h :=
  pr_premiss_itrue g h

/-- 補助: r = 1 の条件 x_1/x_0…ḡh は印刷の x_1/ḡh に一致する。 -/
theorem y_zero (g h : IProp) (x : ℕ → IProp) : y_ g h x 0 = PrI (x 1) (iand (inot g) h) :=
  pr_premiss_itrue _ _

/-- 補助: 空の連言 (itrue) は確実。 -/
theorem Y_zero (g h : IProp) (x : ℕ → IProp) : Y_ g h x 0 = 1 :=
  itrue_certain _

/-- 補助 (Def. X 右形の書き換え): x_1…x_{n+1}/ḡh = x_{n+1}/x_1…x_n ḡh · x_1…x_n/ḡh
(第 XX 章 F20.16 の形)。 -/
theorem Y_succ (g h : IProp) (x : ℕ → IProp) (n : ℕ) :
    Y_ g h x (n + 1) = y_ g h x n * Y_ g h x n :=
  def_X_right_i _ _ _

/-- **F22.10 の帰結**: ∀ r, x_r/gh = 1 ならば ∀ n, x_1x_2…x_n/gh = 1。 -/
theorem conjInst_certain (g h : IProp) (x : ℕ → IProp)
    (hx : ∀ r, PrI (x r) (iand g h) = 1) : ∀ n, PrI (conjInst x n) (iand g h) = 1
  | 0 => itrue_certain _
  | n + 1 => certain_iand _ _ _ (conjInst_certain g h x hx n) (hx (n + 1))

/-- 第 XX 章 F20.11 の形 (積の形): p_n (p_0 + x_1…x_n/ḡh (1 − p_0)) = p_0。 -/
theorem pn_formula (g h : IProp) (x : ℕ → IProp) (hx : ∀ r, PrI (x r) (iand g h) = 1)
    (n : ℕ) :
    p_ g h x n * (PrI g h + Y_ g h x n * (1 - PrI g h)) = PrI g h := by
  have h1 := def_X_right_i g (conjInst x n) h
  rw [conjInst_certain g h x hx n, one_mul] at h1
  have h2 := def_X_left_i g (conjInst x n) h
  have h3 := def_IX_i (conjInst x n) g h
  have h4 := pr_iand_comm (conjInst x n) g h
  have h5 := def_X_left_i (conjInst x n) (inot g) h
  have h6 := th_13_1_i g h
  have hng : PrI (inot g) h = 1 - PrI g h := by linarith
  rw [hng] at h5
  have hXh : PrI (conjInst x n) h
      = PrI g h + PrI (conjInst x n) (iand (inot g) h) * (1 - PrI g h) := by linarith
  unfold p_ Y_
  rw [← hXh, ← h2, h1]

/-- 分母 p_0 + Y_n (1 − p_0) は p_0 > 0 なら正。 -/
theorem pn_den_pos (g h : IProp) (x : ℕ → IProp) (hp0 : 0 < PrI g h) (n : ℕ) :
    0 < PrI g h + Y_ g h x n * (1 - PrI g h) := by
  have hY := ax_range_lo_i (conjInst x n) (iand (inot g) h)
  have hp1 := ax_range_hi_i g h
  have : 0 ≤ Y_ g h x n * (1 - PrI g h) := mul_nonneg hY (by linarith)
  linarith

/-- 第 XX 章 F20.11: p_n = p_0 / (p_0 + x_1…x_n/ḡh (1 − p_0)) (p_0 は有限)。 -/
theorem pn_eq (g h : IProp) (x : ℕ → IProp) (hx : ∀ r, PrI (x r) (iand g h) = 1)
    (hp0 : 0 < PrI g h) (n : ℕ) :
    p_ g h x n = PrI g h / (PrI g h + Y_ g h x n * (1 - PrI g h)) := by
  rw [eq_div_iff (pn_den_pos g h x hp0 n).ne']
  exact pn_formula g h x hx n

/-- 印刷の等号条件 (F22.11 "= 1 − ε") の下で x_1…x_n/ḡh = (1 − ε)^n。 -/
theorem Y_pow (g h : IProp) (x : ℕ → IProp) (ε : ℝ) (hy : ∀ n, y_ g h x n = 1 - ε) :
    ∀ n, Y_ g h x n = (1 - ε) ^ n
  | 0 => by rw [Y_zero]; simp
  | n + 1 => by rw [Y_succ, hy, Y_pow g h x ε hy n, pow_succ]; ring

/-- 第 XX 章の不等号条件 ("< 1 − ε") の下で x_1…x_n/ḡh ≤ (1 − ε)^n。 -/
theorem Y_le_pow (g h : IProp) (x : ℕ → IProp) (ε : ℝ) (hy : ∀ n, y_ g h x n ≤ 1 - ε)
    (hε : 0 ≤ 1 - ε) : ∀ n, Y_ g h x n ≤ (1 - ε) ^ n
  | 0 => by rw [Y_zero]; simp
  | n + 1 => by
      rw [Y_succ, pow_succ]
      have hY0 : 0 ≤ Y_ g h x n := ax_range_lo_i _ _
      have ih := Y_le_pow g h x ε hy hε n
      calc y_ g h x n * Y_ g h x n ≤ (1 - ε) * (1 - ε) ^ n := mul_le_mul (hy n) ih hY0 hε
        _ = (1 - ε) ^ n * (1 - ε) := by ring

/-- 実数の補題: p_0 / (p_0 + (1 − ε)^n (1 − p_0)) → 1 (n → ∞)、0 ≤ 1 − ε < 1、p_0 > 0。 -/
theorem lower_bound_tendsto (p0 ε : ℝ) (hp0 : 0 < p0) (hε0 : 0 ≤ 1 - ε) (hε1 : 1 - ε < 1) :
    Filter.Tendsto (fun n : ℕ => p0 / (p0 + (1 - ε) ^ n * (1 - p0))) Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun n : ℕ => (1 - ε) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hε0 hε1
  have h2 : Filter.Tendsto (fun n : ℕ => p0 + (1 - ε) ^ n * (1 - p0)) Filter.atTop
      (nhds (p0 + 0 * (1 - p0))) :=
    tendsto_const_nhds.add (h1.mul_const _)
  have h3 : Filter.Tendsto (fun n : ℕ => p0 / (p0 + (1 - ε) ^ n * (1 - p0))) Filter.atTop
      (nhds (p0 / (p0 + 0 * (1 - p0)))) :=
    tendsto_const_nhds.div h2 (by simp [hp0.ne'])
  simpa [hp0.ne'] using h3

/-- **F22.11 (印刷の等号形) の帰結**: g/h = p_0 有限、x_r/gh = 1、
x_r/x_1…x_{r−1}ḡh = 1 − ε (ε 有限) ならば p_n → 1 (n → ∞)。
"the probability of a generalisation … is capable … of tending towards certainty as a limit". -/
theorem th_22_11_limit (g h : IProp) (x : ℕ → IProp) (hx : ∀ r, PrI (x r) (iand g h) = 1)
    (hp0 : 0 < PrI g h) (ε : ℝ) (hε : 0 < ε) (hy : ∀ n, y_ g h x n = 1 - ε) :
    Filter.Tendsto (p_ g h x) Filter.atTop (nhds 1) := by
  have hε0 : 0 ≤ 1 - ε := by rw [← hy 0]; exact ax_range_lo_i _ _
  have hε1 : 1 - ε < 1 := by linarith
  refine (lower_bound_tendsto (PrI g h) ε hp0 hε0 hε1).congr ?_
  intro n
  rw [pn_eq g h x hx hp0 n, Y_pow g h x ε hy n]

/-- **cor_22_11_chXX** (台帳 T1: 第 XX 章では不等号 "< 1 − ε"): 不等号条件でも p_n → 1。
第 XX 章の印刷は狭義の < であり、ここで仮定する ≤ はそれより弱い仮定、したがって定理としては
強い形。印刷の等号形 (folio 254) はこの不等号形の特別の場合 (ε を共通にとった形)。 -/
theorem cor_22_11_chXX (g h : IProp) (x : ℕ → IProp) (hx : ∀ r, PrI (x r) (iand g h) = 1)
    (hp0 : 0 < PrI g h) (ε : ℝ) (hε : 0 < ε) (hy : ∀ n, y_ g h x n ≤ 1 - ε) :
    Filter.Tendsto (p_ g h x) Filter.atTop (nhds 1) := by
  have hε0 : 0 ≤ 1 - ε := le_trans (ax_range_lo_i _ _) (hy 0)
  have hε1 : 1 - ε < 1 := by linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (lower_bound_tendsto (PrI g h) ε hp0 hε0 hε1) tendsto_const_nhds ?_ ?_
  · intro n
    rw [pn_eq g h x hx hp0 n]
    have hY := Y_le_pow g h x ε hy hε0 n
    have hp1 := ax_range_hi_i g h
    have hd1 := pn_den_pos g h x hp0 n
    have hd2 : 0 < PrI g h + (1 - ε) ^ n * (1 - PrI g h) := by
      have : 0 ≤ (1 - ε) ^ n * (1 - PrI g h) := mul_nonneg (pow_nonneg hε0 n) (by linarith)
      linarith
    rw [div_le_div_iff₀ hd2 hd1]
    have : Y_ g h x n * (1 - PrI g h) ≤ (1 - ε) ^ n * (1 - PrI g h) :=
      mul_le_mul_of_nonneg_right hY (by linarith)
    nlinarith
  · intro n
    exact ax_range_hi_i _ _

/-- **F22.12 の第 II 部で言える部分 (事例数)**: "p_m, which is based upon numerous instances,
depends for its magnitude upon their number" — p_n は n について単調非減少
(第 XX 章 F20.9 "p_n > p_{n−1} so long as y_n ≠ 1" の非狭義形)。 -/
theorem th_22_12_instances (g h : IProp) (x : ℕ → IProp)
    (hx : ∀ r, PrI (x r) (iand g h) = 1) (hp0 : 0 < PrI g h) (n : ℕ) :
    p_ g h x n ≤ p_ g h x (n + 1) := by
  rw [pn_eq g h x hx hp0 n, pn_eq g h x hx hp0 (n + 1)]
  have hY0 : 0 ≤ Y_ g h x n := ax_range_lo_i _ _
  have hy1 : y_ g h x n ≤ 1 := ax_range_hi_i _ _
  have hYle : Y_ g h x (n + 1) ≤ Y_ g h x n := by
    rw [Y_succ]
    calc y_ g h x n * Y_ g h x n ≤ 1 * Y_ g h x n := mul_le_mul_of_nonneg_right hy1 hY0
      _ = Y_ g h x n := one_mul _
  have hp1 := ax_range_hi_i g h
  have hd1 := pn_den_pos g h x hp0 n
  have hd2 := pn_den_pos g h x hp0 (n + 1)
  rw [div_le_div_iff₀ hd1 hd2]
  have : Y_ g h x (n + 1) * (1 - PrI g h) ≤ Y_ g h x n * (1 - PrI g h) :=
    mul_le_mul_of_nonneg_right hYle (by linarith)
  nlinarith

/-- 補助 (実数の不等式; 確率関係の公理を用いない)。**F22.12 の第 II 部で言える部分 (類推)**:
"we endeavour to obtain evidence which makes the initial probability p_0 relatively high" —
第 XX 章の式 p_0/(p_0 + Y(1 − p_0)) は p_0 について単調非減少
(Y = x_1…x_n/ḡh ∈ [0, 1] を固定)。 -/
theorem th_22_12_analogy (p p' Y : ℝ) (hp : 0 < p) (hpp : p ≤ p') (hp1 : p' ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) :
    p / (p + Y * (1 - p)) ≤ p' / (p' + Y * (1 - p')) := by
  have hd1 : 0 < p + Y * (1 - p) := by nlinarith
  have hd2 : 0 < p' + Y * (1 - p') := by nlinarith
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith

/-! ### §3 の追加公理と判定 (folio 254 の三行を名前付きの公理として宣言) -/

/-- 一般化 g(φ f) (folio 254 の印刷表記は `g(φf)`、第 XIX 章では `g(φ, f)`; 台帳 T2)。
対象の型 Obj 上の二つの性質 φ, f から一般化の命題を作る。 -/
axiom gen {Obj : Type} : (Obj → IProp) → (Obj → IProp) → IProp

/-- §3 の à priori の前提 h ("in the absence of evidence to the contrary")。 -/
axiom h_ : IProp

/-- **追加公理: 限定独立多様性** (folio 253–254 §3, F22.6–F22.8; folio 260 §11 の帰納仮説
"some limitation of independent variety"): 生成子性質が有限個なので群も有限個であり、
"there is, in the absence of evidence to the contrary, a finite probability that the second
set will belong to the group specified by the first set" — すなわち、どの二つの性質
φ, f についても一般化 g(φf) は h の下で有限 (不可能から有限量だけ離れた) 確率をもつ。 -/
axiom ax_22_limited_independent_variety {Obj : Type} (φ f : Obj → IProp) :
    0 < PrI (gen φ f) h_

/-- folio 254 の設定: 対象の型と、事例が共有する二つの性質 φ, f
("the instances have two groups of characters in common, namely φ and f")。 -/
axiom Obj_ : Type
axiom φ_ : Obj_ → IProp
axiom f_ : Obj_ → IProp

/-- 一般化 g := g(φf) (folio 254 "if the generalisation g(φf) is valid")。
第 1 回では g を独立の公理としていたが、限定独立多様性と結ぶため gen φ_ f_ とおく。 -/
noncomputable def g_ : IProp := gen φ_ f_

/-- 事例 x_r (folio 254 "If x_r, etc., are the instances")。 -/
axiom x_ : ℕ → IProp

/-- p_0 = g/h (folio 254 第 1 行)。 -/
noncomputable def p_0 : ℝ := PrI g_ h_

/-- **th_22_9_src** (F22.9, folio 254): "For the reason already explained there is a finite
probability that f and φ belong to the same group. If this is the case, i.e. if the
generalisation g(φf) is valid … g/h = p_0, where p_0 is finite" — g := g(φf) とおくと、
p_0 = g/h が有限 (0 < p_0) であることは限定独立多様性 (ax_22_limited_independent_variety) から
導かれる。第 1 回の追加公理 ax_22_9_p0_finite はこの定理に置き換えた。以下の th_22_9,
th_22_11_src, th_22_12 はこの定理を通じて限定独立多様性を用いる。 -/
theorem th_22_9_src : 0 < p_0 :=
  ax_22_limited_independent_variety φ_ f_

/-- **追加公理 (F22.10, 前提)**: x_r/gh = 1, etc.。 -/
axiom ax_22_10_instances_certain : ∀ r, PrI (x_ r) (iand g_ h_) = 1

/-- **追加公理 (F22.11, 印刷どおりの等号)**: x_r/x_1x_2 . . . x_{r−1}ḡh = 1 − ε, where ε is finite。
(第 XX 章では不等号 "< 1 − ε"; 台帳 T1。等号形は不等号形を含意する。) -/
axiom ax_22_11_eps_finite : ∃ ε : ℝ, 0 < ε ∧ ∀ n, y_ g_ h_ x_ n = 1 - ε

/-- **th_22_9** (F22.9, folio 254): g/h = p_0 で p_0 は有限。p_0 が有限であることの帰結として、
第 XX 章の式 p_n = p_0/(p_0 + x_1…x_n/ḡh (1 − p_0)) が成り立つ
(p_0 = g/h は定義 p_0 による)。 -/
theorem th_22_9 (n : ℕ) :
    0 < p_0 ∧ p_ g_ h_ x_ n = p_0 / (p_0 + Y_ g_ h_ x_ n * (1 - p_0)) :=
  ⟨th_22_9_src, pn_eq g_ h_ x_ ax_22_10_instances_certain th_22_9_src n⟩

/-- **th_22_10** (F22.10, folio 254): x_r/gh = 1, etc. — したがって x_1x_2…x_n/gh = 1。 -/
theorem th_22_10 (n : ℕ) : PrI (conjInst x_ n) (iand g_ h_) = 1 :=
  conjInst_certain g_ h_ x_ ax_22_10_instances_certain n

/-- **th_22_11_src** (F22.11, folio 254, 印刷の等号形): 三条件の下で
"the probability of a generalisation … tending towards certainty as a limit" — p_n → 1。
p_0 の有限性は th_22_9_src (限定独立多様性) から取る。 -/
theorem th_22_11_src : Filter.Tendsto (p_ g_ h_ x_) Filter.atTop (nhds 1) := by
  obtain ⟨ε, hε, hy⟩ := ax_22_11_eps_finite
  exact th_22_11_limit g_ h_ x_ ax_22_10_instances_certain th_22_9_src ε hε hy

/-- **th_22_12** (F22.12, folio 255): p_m は事例数とともに単調非減少 (p_n ≤ p_{n+1})。 -/
theorem th_22_12 (n : ℕ) : p_ g_ h_ x_ n ≤ p_ g_ h_ x_ (n + 1) :=
  th_22_12_instances g_ h_ x_ ax_22_10_instances_certain th_22_9_src n

/-! ## §4 第 XXII 章 §11 — F22.17, F22.18, F22.19 (folio 259–260)

folio 259–260: "If our conclusion is C and our empirical evidence is E, then, in order to justify
inductive methods, our premisses must include, in addition to E, a general hypothesis H such that
C/H, the à priori probability of our conclusion, has a finite value. The effect of E is to
increase the probability of C above its initial à priori value, C/HE being greater than C/H.
… If, therefore, we have another general hypothesis H′ and other evidence E′, such that H/H′
has a finite value, we can, without being guilty of a circular argument, use evidence E′ by
the same method as before to strengthen the probability H/H′." -/

/-- **th_22_17** (F22.17 の必要性): C/H = 0 ならば、H の下で不可能でないどんな証拠 E を
加えても C/HE = 0 — C/H が有限でなければ帰納法は結論の確率を上げられない。
(前提 HE は `iand E H` の順で書く。) -/
theorem th_22_17 (C E H : IProp) (h0 : PrI C H = 0) (hE : PrI E H ≠ 0) :
    PrI C (iand E H) = 0 := by
  have h1 := def_X_left_i C E H
  have h2 := def_X_right_i C E H
  rw [h0, mul_zero] at h2
  rw [h2] at h1
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h hE

/-- **帰納法 (inductive method, folio 260)**: C/H が有限、E が CH の下で確実
(経験が H のもとでの期待に一致)、E が H の下では確実でないならば、C/HE > C/H。 -/
theorem inductive_method (C E H : IProp) (hCH : 0 < PrI C H)
    (hE : PrI E (iand C H) = 1) (hEH : PrI E H < 1) :
    PrI C H < PrI C (iand E H) := by
  have h1 := def_X_left_i C E H
  have h2 := def_X_right_i C E H
  rw [hE, one_mul] at h2
  rw [h2] at h1
  have hEH0 := ax_range_lo_i E H
  have hC0 := ax_range_lo_i C (iand E H)
  have hc : 0 < PrI C (iand E H) :=
    lt_of_le_of_ne hC0 (fun h0 => by rw [← h0, zero_mul] at h1; linarith)
  nlinarith [mul_lt_mul_of_pos_left hEH hc]

/-- 結論 C、経験的証拠 E、一般仮説 H、より原始的な仮説 H′、その証拠 E′
(folio 259–260 ではローマン体大文字; 台帳 N3)。 -/
axiom C_ : IProp
axiom E_ : IProp
axiom H_ : IProp
axiom H'_ : IProp
axiom E'_ : IProp

/-- **追加公理 (F22.17)**: C/H, the à priori probability of our conclusion, has a finite value。 -/
axiom ax_22_17_CH_finite : 0 < PrI C_ H_

/-- **追加公理 (F22.19)**: H/H′ has a finite value。 -/
axiom ax_22_19_HH'_finite : 0 < PrI H_ H'_

/-- **th_22_18** (F22.18, folio 260): "The effect of E is to increase the probability of C above
its initial à priori value, C/HE being greater than C/H"。C/H の有限性 (F22.17) を用いる。
**印刷に無い前提の補充 (索引 T 候補)**: 印刷は C/H が有限であることだけを挙げて
"C/HE being greater than C/H" と書くが、空でない前提をもつ有限モデル FinSys (第 II 部の公理の
形を満たす; finSys_partII) では C/H > 0 だけから C/HE > C/H は出ない
(反例 F22_18_needs_premisses: C = {0}, H = 全体, E = {1} で C/H = 1/2, C/HE = 0)。
ここでは第 XX 章の帰納法の設定どおり、E が CH の下で確実 (E/CH = 1: 経験が H のもとでの
期待に一致) かつ E が H の下では確実でない (E/H < 1) という二つの前提を足している。 -/
theorem th_22_18 (hE : PrI E_ (iand C_ H_) = 1) (hEH : PrI E_ H_ < 1) :
    PrI C_ H_ < PrI C_ (iand E_ H_) :=
  inductive_method C_ E_ H_ ax_22_17_CH_finite hE hEH

/-- **th_22_19** (F22.19, folio 260): H/H′ が有限なら "we can, without being guilty of a
circular argument, use evidence E′ by the same method as before to strengthen the probability
H/H′" — 同じ帰納法を (C, E, H) := (H, E′, H′) に適用する。
th_22_18 と同じく、印刷に無い前提 E′/HH′ = 1 と E′/H′ < 1 を足している (索引 T 候補)。 -/
theorem th_22_19 (hE' : PrI E'_ (iand H_ H'_) = 1) (hE'H' : PrI E'_ H'_ < 1) :
    PrI H_ H'_ < PrI H_ (iand E'_ H'_) :=
  inductive_method H_ E'_ H'_ ax_22_19_HH'_finite hE' hE'H'

/-! ## §5 Notes on Part III (ii.) "On the Use of the Term *Cause*" (folio 276–277)

folio 276 §2–3: データを k (nomologic, 法則的) と l (ontologic, 存在的) に分け、
存在命題 a, b が事象 A, B を特定の時点に関係づける (A は B に先行)。
定義 (i.)–(ix.) は folio 276、(x.) と §4 は folio 277。
以下の定義は、命題集合と連言・否定・確率関係をもつ任意の体系 R について述べ、
Keynes の体系 (IProp, iand, inot, PrI) と有限モデルの両方に適用する。
前提の連言は印刷の文字順に右結合で書く: akl = conj a (conj k l), ahkl = conj a (conj h (conj k l))。 -/

/-- 命題集合 Γ (P) とその上の連言・否定、および確率関係 pr (結論, 前提)。 -/
structure ProbRelSystem where
  P : Type
  conj : P → P → P
  neg : P → P
  pr : P → P → ℝ

namespace Notes_ii

variable (R : ProbRelSystem)

/-- **(i.)** "If b/ak = 1, A is a sufficient cause of B." -/
def SuffCause (a b k : R.P) : Prop := R.pr b (R.conj a k) = 1

/-- **(ii.)** "If b/āk = 0, A is a necessary cause of B." -/
def NecCause (a b k : R.P) : Prop := R.pr b (R.conj (R.neg a) k) = 0

/-- **(iii.)** "If k includes all the laws of the existent universe, then A is *not* a sufficient
cause of B unless b/ak = 1." — 存在論的な十分原因の述語 IsCause と、k の完全性 Complete を
与えたとき、Complete k の下では IsCause a b → b/ak = 1。 -/
def Def_iii (Complete : R.P → Prop) (IsCause : R.P → R.P → Prop) (k : R.P) : Prop :=
  Complete k → ∀ a b, IsCause a b → R.pr b (R.conj a k) = 1

/-- **(iii.) 因果律** "if k is the body of natural law, then, if b is true, there is always
another true proposition a, which asserts existences prior to B, such that b/ak = 1." -/
def LawOfCausation (Tr : R.P → Prop) (Prior : R.P → R.P → Prop) (k : R.P) : Prop :=
  ∀ b, Tr b → ∃ a, Tr a ∧ Prior a b ∧ R.pr b (R.conj a k) = 1

/-- **(iv.)** "If b/akl = 1 and b/kl ≠ 1, A is a sufficient cause of B under conditions l." -/
def SuffCauseUnder (a b k l : R.P) : Prop :=
  R.pr b (R.conj a (R.conj k l)) = 1 ∧ R.pr b (R.conj k l) ≠ 1

/-- **(v.)** "If b/ākl = 0 and b/kl ≠ 0, A is a necessary cause of B under conditions l." -/
def NecCauseUnder (a b k l : R.P) : Prop :=
  R.pr b (R.conj (R.neg a) (R.conj k l)) = 0 ∧ R.pr b (R.conj k l) ≠ 0

/-- **(vi.)** "If there is any existential proposition h such that b/ahk = 1 and b/hk ≠ 1,
A is, relative to k, a possible sufficient cause of B." (Ex: 存在命題であること) -/
def PossSuffCause (Ex : R.P → Prop) (a b k : R.P) : Prop :=
  ∃ h, Ex h ∧ R.pr b (R.conj a (R.conj h k)) = 1 ∧ R.pr b (R.conj h k) ≠ 1

/-- **(vii.)** "If there is an existential proposition h such that b/āhk = 0 and b/hk ≠ 0,
A is, relative to k, a possible necessary cause of B." -/
def PossNecCause (Ex : R.P → Prop) (a b k : R.P) : Prop :=
  ∃ h, Ex h ∧ R.pr b (R.conj (R.neg a) (R.conj h k)) = 0 ∧ R.pr b (R.conj h k) ≠ 0

/-- **(viii.) 印刷どおり** "If b/ahkl = 1, b/hk ≠ 1, and h/akl ≠ 0, A is, relative to k,
a possible sufficient cause of B under conditions l." — 第 2 条件 b/hk に l が無い
(E-III-4)。h は (vi.), (vii.) と同様に存在命題として存在量化する
(印刷の (viii.)(ix.) は "there is an existential proposition h" を書かない; 索引に記録)。 -/
def PossSuffCauseUnder_src (Ex : R.P → Prop) (a b k l : R.P) : Prop :=
  ∃ h, Ex h ∧ R.pr b (R.conj a (R.conj h (R.conj k l))) = 1 ∧
    R.pr b (R.conj h k) ≠ 1 ∧ R.pr h (R.conj a (R.conj k l)) ≠ 0

/-- **(viii.) l を補った形** b/ahkl = 1, b/hkl ≠ 1, h/akl ≠ 0 — (ix.) の第 2 条件 b/hkl ≠ 0
と対称になる形。 -/
def PossSuffCauseUnder_l (Ex : R.P → Prop) (a b k l : R.P) : Prop :=
  ∃ h, Ex h ∧ R.pr b (R.conj a (R.conj h (R.conj k l))) = 1 ∧
    R.pr b (R.conj h (R.conj k l)) ≠ 1 ∧ R.pr h (R.conj a (R.conj k l)) ≠ 0

/-- **(ix.)** "If b/āhkl = 0, b/hkl ≠ 0, h/ākl ≠ 0, and h/akl ≠ 0, A is, relative to k,
a possible necessary cause of B under conditions l." -/
def PossNecCauseUnder (Ex : R.P → Prop) (a b k l : R.P) : Prop :=
  ∃ h, Ex h ∧ R.pr b (R.conj (R.neg a) (R.conj h (R.conj k l))) = 0 ∧
    R.pr b (R.conj h (R.conj k l)) ≠ 0 ∧
    R.pr h (R.conj (R.neg a) (R.conj k l)) ≠ 0 ∧ R.pr h (R.conj a (R.conj k l)) ≠ 0

/-- **(x.)** (folio 277) "Two events are *causally independent* if no part of either is, relative
to our nomologic data, a possible cause of any part of the other under the conditions of our
existential knowledge." — 「部分」の述語 Part と、条件 l 下の可能的十分原因 PSC
((viii.) の印刷形または l を補った形) と可能的必要原因 PNC ((ix.)) を与えて定義する。
印刷は「可能的原因」が十分・必要のどちらかを指定しないので、両者の選言にとる。 -/
def CausallyIndependent (Part : R.P → R.P → Prop)
    (PSC PNC : R.P → R.P → R.P → R.P → Prop) (a b k l : R.P) : Prop :=
  ∀ a' b', Part a' a → Part b' b →
    ¬ (PSC a' b' k l ∨ PNC a' b' k l) ∧ ¬ (PSC b' a' k l ∨ PNC b' a' k l)

/-- **§4** (folio 277) "If b/ahkl ≠ b/āhkl, … we have 'dependence for probability,' and a is a
*causa cognoscendi* for b, relative to data kl." -/
def DepForProb (a b h k l : R.P) : Prop :=
  R.pr b (R.conj a (R.conj h (R.conj k l))) ≠ R.pr b (R.conj (R.neg a) (R.conj h (R.conj k l)))

end Notes_ii

/-- Keynes の体系: 命題集合 IProp、連言 iand、否定 inot、確率関係 PrI。 -/
noncomputable def KeynesSys : ProbRelSystem := ⟨IProp, iand, inot, PrI⟩

/-- Keynes の体系における (viii.) 印刷形。 -/
def def_viii_src (Ex : IProp → Prop) (a b k l : IProp) : Prop :=
  Notes_ii.PossSuffCauseUnder_src KeynesSys Ex a b k l

/-- Keynes の体系における (viii.) l を補った形。 -/
def def_viii_l (Ex : IProp → Prop) (a b k l : IProp) : Prop :=
  Notes_ii.PossSuffCauseUnder_l KeynesSys Ex a b k l

/-- Keynes の体系における (ix.)。 -/
def def_ix (Ex : IProp → Prop) (a b k l : IProp) : Prop :=
  Notes_ii.PossNecCauseUnder KeynesSys Ex a b k l

/-- Keynes の体系における (x.) (PSC に印刷形 (viii.) をとる)。 -/
def def_x_src (Ex : IProp → Prop) (Part : IProp → IProp → Prop) (a b k l : IProp) : Prop :=
  Notes_ii.CausallyIndependent KeynesSys Part (def_viii_src Ex) (def_ix Ex) a b k l

/-- Keynes の体系における §4 の「確率上の依存」。 -/
def dep_for_prob (a b h k l : IProp) : Prop := Notes_ii.DepForProb KeynesSys a b h k l

/-- (viii.) の第 2 条件を l を補った形から印刷形へ移す第 II 部の内容:
b/hk = 1 かつ l/hk ≠ 0 ならば b/(l hk) = 1。前提の連言の順序を並べ替える原理が
第 II 部の公理群に無いため、前提は `iand l (iand h k)` の形 (l を先頭に付す) で述べる。 -/
theorem notes_viii_certain_add_l (b h k l : IProp) (hb : PrI b (iand h k) = 1)
    (hl : PrI l (iand h k) ≠ 0) : PrI b (iand l (iand h k)) = 1 :=
  certain_add_premiss l b (iand h k) hb hl

/-- 前提 m の下での b の確率の分解 (Def. IX と Def. X 左形):
b/m = b/(a m) · a/m + b/(ā m) · ā/m。 -/
theorem pr_decompose (a b m : IProp) :
    PrI b m = PrI b (iand a m) * PrI a m + PrI b (iand (inot a) m) * PrI (inot a) m := by
  have hIX := def_IX_i b a m
  have hX1 := def_X_left_i b a m
  have hX2 := def_X_left_i b (inot a) m
  linarith

/-- **def_viii_l_imp_src** (Keynes の体系): l を補った形 (viii.) は、(α) 前提 hkl の連言を
l(hk) に並べ替えてよいこと、(β) l が hk の下で不可能でないことを仮定すれば、印刷形 (viii.) を
含意する。(α) は第 II 部の公理群に無い原理 (所見候補)、(β) は Keynes の Ax.(i) の約定。
有限モデルでの対応物は E_III_4_corrected_imp_printed (無条件)。 -/
theorem def_viii_l_imp_src (Ex : IProp → Prop) (a b k l : IProp)
    (hperm : ∀ h, Ex h → PrI b (iand h (iand k l)) = PrI b (iand l (iand h k)))
    (hl : ∀ h, Ex h → PrI l (iand h k) ≠ 0) :
    def_viii_l Ex a b k l → def_viii_src Ex a b k l := by
  rintro ⟨h, hEx, hcert, hne, hne0⟩
  refine ⟨h, hEx, hcert, ?_, hne0⟩
  intro hhk
  apply hne
  change PrI b (iand h k) = 1 at hhk
  change PrI b (iand h (iand k l)) = 1
  rw [hperm h hEx]
  exact notes_viii_certain_add_l b h k l hhk (hl h hEx)

/-- **def_viii_l_dep** (Keynes の体系): l を補った形 (viii.) の証人 h について、
A は B の causa cognoscendi (§4 の確率上の依存 b/ahkl ≠ b/āhkl) である。
b/ahkl = 1 かつ b/āhkl = 1 なら分解により b/hkl = 1 となり、第 2 条件に反する。 -/
theorem def_viii_l_dep (Ex : IProp → Prop) (a b k l : IProp) :
    def_viii_l Ex a b k l → ∃ h, Ex h ∧ dep_for_prob a b h k l := by
  rintro ⟨h, hEx, hcert, hne, -⟩
  refine ⟨h, hEx, ?_⟩
  change PrI b (iand a (iand h (iand k l))) = 1 at hcert
  change PrI b (iand h (iand k l)) ≠ 1 at hne
  change PrI b (iand a (iand h (iand k l))) ≠ PrI b (iand (inot a) (iand h (iand k l)))
  intro heq
  apply hne
  have hd := pr_decompose a b (iand h (iand k l))
  have hc := th_13_1_i a (iand h (iand k l))
  rw [← heq, hcert, one_mul, one_mul] at hd
  linarith

/-- **def_ix_dep** (Keynes の体系): (ix.) の証人 h について、A は B の causa cognoscendi
(b/ahkl ≠ b/āhkl) である。b/āhkl = 0 かつ b/ahkl = 0 なら分解により b/hkl = 0 となり、
第 2 条件に反する。 -/
theorem def_ix_dep (Ex : IProp → Prop) (a b k l : IProp) :
    def_ix Ex a b k l → ∃ h, Ex h ∧ dep_for_prob a b h k l := by
  rintro ⟨h, hEx, hzero, hne, -, -⟩
  refine ⟨h, hEx, ?_⟩
  change PrI b (iand (inot a) (iand h (iand k l))) = 0 at hzero
  change PrI b (iand h (iand k l)) ≠ 0 at hne
  change PrI b (iand a (iand h (iand k l))) ≠ PrI b (iand (inot a) (iand h (iand k l)))
  intro heq
  apply hne
  have hd := pr_decompose a b (iand h (iand k l))
  rw [heq, hzero, zero_mul, zero_mul] at hd
  linarith

/-- **def_x_src_symm** (Keynes の体系): (x.) の因果的独立は二事象について対称。 -/
theorem def_x_src_symm (Ex : IProp → Prop) (Part : IProp → IProp → Prop) (a b k l : IProp) :
    def_x_src Ex Part a b k l ↔ def_x_src Ex Part b a k l := by
  unfold def_x_src Notes_ii.CausallyIndependent
  exact ⟨fun H a' b' ha hb => (H b' a' hb ha).symm,
    fun H a' b' ha hb => (H b' a' hb ha).symm⟩

/-! ### E-III-4 の有限モデル: 印刷形 (viii.) と l を補った形が異なる例

2 点集合 {0, 1} 上の命題 = 部分集合、連言 = 共通部分、否定 = 補集合、
確率関係 = 一様分布の条件付き確率 (前提が空集合のときは 1 とおく;
Keynes は矛盾する前提を除外するので、この値は以下の反例の導出に用いられない)。 -/

/-- 一様分布の条件付き確率 (結論 b, 前提 a)。 -/
noncomputable def finPr (b a : Finset (Fin 2)) : ℝ :=
  if a = ∅ then 1 else ((a ∩ b).card : ℝ) / (a.card : ℝ)

/-- 有限モデル。 -/
noncomputable abbrev FinSys : ProbRelSystem := ⟨Finset (Fin 2), (· ∩ ·), (·ᶜ), finPr⟩

theorem finPr_singleton_self : finPr {0} {0} = 1 := by
  simp [finPr]

theorem finPr_empty (b : Finset (Fin 2)) : finPr b ∅ = 1 := by
  simp [finPr]

/-- 印刷形 (viii.) は a = k = h = 全体、b = l = {0} で成り立つ。 -/
theorem E_III_4_printed_holds :
    Notes_ii.PossSuffCauseUnder_src FinSys (fun _ => True) (Finset.univ : Finset (Fin 2)) ({0} : Finset (Fin 2)) Finset.univ {0} := by
  refine ⟨Finset.univ, trivial, ?_, ?_, ?_⟩
  · show finPr {0} (Finset.univ ∩ (Finset.univ ∩ (Finset.univ ∩ {0}))) = 1
    have e : (Finset.univ ∩ (Finset.univ ∩ (Finset.univ ∩ {0})) : Finset (Fin 2)) = {0} := by
      decide
    rw [e]; exact finPr_singleton_self
  · show finPr {0} (Finset.univ ∩ Finset.univ) ≠ 1
    have e : (Finset.univ ∩ Finset.univ : Finset (Fin 2)) = Finset.univ := by decide
    have hne : (Finset.univ : Finset (Fin 2)) ≠ ∅ := by decide
    rw [e]
    simp [finPr, hne]
  · show finPr Finset.univ (Finset.univ ∩ (Finset.univ ∩ {0})) ≠ 0
    have e : (Finset.univ ∩ (Finset.univ ∩ {0}) : Finset (Fin 2)) = {0} := by decide
    rw [e]
    simp [finPr]

/-- l を補った形 (viii.) は同じ入力で成り立たない: どの h についても前提 ahkl と hkl は
同じ集合 h ∩ {0} になるので、b/ahkl = 1 と b/hkl ≠ 1 は両立しない。
(空集合の前提に対する値のとり方に依らない。) -/
theorem E_III_4_corrected_fails :
    ¬ Notes_ii.PossSuffCauseUnder_l FinSys (fun _ => True) (Finset.univ : Finset (Fin 2)) ({0} : Finset (Fin 2)) Finset.univ {0} := by
  rintro ⟨(h : Finset (Fin 2)), -, hcert, hne, -⟩
  apply hne
  have e1 : (Finset.univ ∩ (h ∩ (Finset.univ ∩ {0})) : Finset (Fin 2)) = h ∩ {0} := by
    ext i; simp
  have e2 : (h ∩ (Finset.univ ∩ {0}) : Finset (Fin 2)) = h ∩ {0} := by
    ext i; simp
  change finPr {0} (Finset.univ ∩ (h ∩ (Finset.univ ∩ {0}))) = 1 at hcert
  change finPr {0} (h ∩ (Finset.univ ∩ {0})) = 1
  rw [e1] at hcert
  rw [e2]
  exact hcert

/-- **E-III-4 の反例**: 印刷形 (viii.) と l を補った形 (viii.) は有限モデルで異なる。 -/
theorem E_III_4_countermodel :
    Notes_ii.PossSuffCauseUnder_src FinSys (fun _ => True) (Finset.univ : Finset (Fin 2)) ({0} : Finset (Fin 2)) Finset.univ {0} ∧
    ¬ Notes_ii.PossSuffCauseUnder_l FinSys (fun _ => True) (Finset.univ : Finset (Fin 2)) ({0} : Finset (Fin 2)) Finset.univ {0} :=
  ⟨E_III_4_printed_holds, E_III_4_corrected_fails⟩

/-- 有限モデルで pr b a = 1 であることと a ⊆ b は同値 (a が空でないとき)。 -/
theorem finPr_eq_one_iff (b a : Finset (Fin 2)) (ha : a ≠ ∅) : finPr b a = 1 ↔ a ⊆ b := by
  unfold finPr
  rw [if_neg ha]
  have hpos : (0 : ℝ) < a.card := by
    have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ha)
    exact_mod_cast this
  rw [div_eq_one_iff_eq hpos.ne']
  constructor
  · intro hc
    have hc' : (a ∩ b).card = a.card := by exact_mod_cast hc
    have heq : a ∩ b = a :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq hc'.symm)
    intro i hi
    have hi' : i ∈ a ∩ b := by rw [heq]; exact hi
    exact (Finset.mem_inter.mp hi').2
  · intro hsub
    rw [Finset.inter_eq_left.mpr hsub]

/-- 有限モデルで pr b a = 1 であることと a ⊆ b は同値 (a が空のときは空前提の約定 1 と ∅ ⊆ b)。 -/
theorem finPr_eq_one_iff' (b a : Finset (Fin 2)) : finPr b a = 1 ↔ a ⊆ b := by
  by_cases ha : a = ∅
  · subst ha
    simp [finPr]
  · exact finPr_eq_one_iff b a ha

/-- 有限モデルでは確実性は前提を狭めても保たれる: pr b a = 1 かつ a' ⊆ a ならば pr b a' = 1。 -/
theorem finPr_eq_one_mono (b a a' : Finset (Fin 2)) (h1 : finPr b a = 1) (hsub : a' ⊆ a) :
    finPr b a' = 1 := by
  rw [finPr_eq_one_iff'] at h1 ⊢
  exact hsub.trans h1

/-- 有限モデルでは l を補った形 (viii.) は印刷形 (viii.) を無条件に含意する
(前提 hkl ⊆ hk なので、b/hk = 1 ならば b/hkl = 1; 空前提は約定 1 で同じ向きに働く)。
印刷形は l を補った形より弱い定義である。第 1 回の仮定 ∀ h, h ∩ (k ∩ l) ≠ ∅ は
h = ∅ で偽になり定理を空虚にしていたので外した。 -/
theorem E_III_4_corrected_imp_printed (Ex : Finset (Fin 2) → Prop) (a b k l : Finset (Fin 2)) :
    Notes_ii.PossSuffCauseUnder_l FinSys Ex a b k l →
    Notes_ii.PossSuffCauseUnder_src FinSys Ex a b k l := by
  rintro ⟨(h : Finset (Fin 2)), hEx, hcert, hne1, hne0⟩
  refine ⟨h, hEx, hcert, ?_, hne0⟩
  intro hhk
  apply hne1
  change finPr b (h ∩ k) = 1 at hhk
  change finPr b (h ∩ (k ∩ l)) = 1
  refine finPr_eq_one_mono b (h ∩ k) (h ∩ (k ∩ l)) hhk ?_
  intro i hi
  rw [← Finset.inter_assoc] at hi
  exact Finset.mem_of_mem_inter_left hi

/-- 第 1 回の仮定 ∀ h, h ∩ (k ∩ l) ≠ ∅ が偽であること (h = ∅)。
この仮定を置いた定理は前件が偽で空虚だった。 -/
theorem E_III_4_old_hyp_false (k l : Finset (Fin 2)) : ¬ ∀ h : Finset (Fin 2), h ∩ (k ∩ l) ≠ ∅ :=
  fun H => H ∅ (Finset.empty_inter _)

/-- l を補った形 (viii.) が成り立つ有限モデルの例 (無条件の含意が空虚でないことの確認):
a = {0}, b = {0}, k = l = 全体, h = 全体。b/ahkl = 1, b/hkl = 1/2 ≠ 1, h/akl = 1 ≠ 0。 -/
theorem E_III_4_corrected_holds_example :
    Notes_ii.PossSuffCauseUnder_l FinSys (fun _ => True) ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2)) Finset.univ Finset.univ := by
  refine ⟨Finset.univ, trivial, ?_, ?_, ?_⟩
  · show finPr {0} ({0} ∩ (Finset.univ ∩ (Finset.univ ∩ Finset.univ))) = 1
    rw [finPr_eq_one_iff']
    intro i hi
    exact Finset.mem_of_mem_inter_left hi
  · show finPr {0} (Finset.univ ∩ (Finset.univ ∩ Finset.univ)) ≠ 1
    intro H
    rw [finPr_eq_one_iff'] at H
    have := H (Finset.mem_inter.mpr ⟨Finset.mem_univ 1, Finset.mem_inter.mpr ⟨Finset.mem_univ 1, Finset.mem_univ 1⟩⟩)
    simp at this
  · show finPr Finset.univ ({0} ∩ (Finset.univ ∩ Finset.univ)) ≠ 0
    have e : ({0} ∩ (Finset.univ ∩ Finset.univ) : Finset (Fin 2)) = {0} := by decide
    rw [e]
    simp [finPr]

/-! ### 有限モデルが第 II 部の操作 (値域、Def. IX、Def. X) を満たすことの確認
(前提が空でない場合; Keynes の Ax.(i) は矛盾する前提を除外する)。 -/

theorem finPr_range (b a : Finset (Fin 2)) : 0 ≤ finPr b a ∧ finPr b a ≤ 1 := by
  unfold finPr
  split_ifs with ha
  · exact ⟨zero_le_one, le_rfl⟩
  · have hpos : (0 : ℝ) < a.card := by
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ha)
      exact_mod_cast this
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [div_le_one hpos]
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left

/-- Def. IX: (p q̄)/a + (p q)/a = p/a。 -/
theorem finPr_IX (p q a : Finset (Fin 2)) (ha : a ≠ ∅) :
    finPr (p ∩ qᶜ) a + finPr (p ∩ q) a = finPr p a := by
  simp only [finPr, if_neg ha]
  rw [← add_div]
  congr 1
  have hc := Finset.card_sdiff_add_card_inter (a ∩ p) q
  rw [Finset.sdiff_eq_inter_compl, Finset.inter_assoc, Finset.inter_assoc] at hc
  exact_mod_cast hc

/-- Def. X 左形: (p q)/a = p/(q a) · q/a。 -/
theorem finPr_X_left (p q a : Finset (Fin 2)) (ha : a ≠ ∅) :
    finPr (p ∩ q) a = finPr p (q ∩ a) * finPr q a := by
  by_cases hqa : q ∩ a = ∅
  · have h1 : a ∩ (p ∩ q) = ∅ := by
      ext i; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      rintro ⟨hia, -, hiq⟩
      have : i ∈ q ∩ a := Finset.mem_inter.mpr ⟨hiq, hia⟩
      rw [hqa] at this
      exact Finset.notMem_empty i this
    have h2 : a ∩ q = ∅ := by rw [Finset.inter_comm]; exact hqa
    simp only [finPr, if_neg ha, if_pos hqa, h1, h2, Finset.card_empty, Nat.cast_zero,
      zero_div, one_mul]
  · have e1 : q ∩ a ∩ p = a ∩ (p ∩ q) := by
      ext i; simp only [Finset.mem_inter]; tauto
    have e2 : a ∩ q = q ∩ a := Finset.inter_comm _ _
    have hpos : ((q ∩ a).card : ℝ) ≠ 0 := by
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hqa)
      exact_mod_cast this.ne'
    simp only [finPr, if_neg ha, if_neg hqa, e1, e2]
    field_simp

/-- Def. X 右形: (p q)/a = q/(p a) · p/a。 -/
theorem finPr_X_right (p q a : Finset (Fin 2)) (ha : a ≠ ∅) :
    finPr (p ∩ q) a = finPr q (p ∩ a) * finPr p a := by
  rw [Finset.inter_comm p q]
  exact finPr_X_left q p a ha

/-- 有限モデルにおける対象言語 Form の解釈 (var ↦ env、tru ↦ 全体、fls ↦ ∅、conj ↦ ∩、
disj ↦ ∪、neg ↦ 補集合、iffF ↦ (∩) ∪ (補 ∩ 補))。 -/
def finInterp (env : ℕ → Finset (Fin 2)) : Form → Finset (Fin 2)
  | .var n    => env n
  | .tru      => Finset.univ
  | .fls      => ∅
  | .conj f g => finInterp env f ∩ finInterp env g
  | .disj f g => finInterp env f ∪ finInterp env g
  | .neg f    => (finInterp env f)ᶜ
  | .iffF f g => (finInterp env f ∩ finInterp env g) ∪ ((finInterp env f)ᶜ ∩ (finInterp env g)ᶜ)

/-- 点 ω が解釈に属することと、ω の定める真理値割当で式が真であることは同値。 -/
theorem mem_finInterp (env : ℕ → Finset (Fin 2)) (ω : Fin 2) :
    ∀ f : Form, ω ∈ finInterp env f ↔ evalB (fun i => decide (ω ∈ env i)) f = true
  | .var n    => by simp [finInterp, evalB]
  | .tru      => by simp [finInterp, evalB]
  | .fls      => by simp [finInterp, evalB]
  | .conj f g => by simp [finInterp, evalB, mem_finInterp env ω f, mem_finInterp env ω g]
  | .disj f g => by simp [finInterp, evalB, mem_finInterp env ω f, mem_finInterp env ω g]
  | .neg f    => by simp [finInterp, evalB, mem_finInterp env ω f]
  | .iffF f g => by
      simp only [finInterp, evalB, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
        mem_finInterp env ω f, mem_finInterp env ω g]
      cases evalB (fun i => decide (ω ∈ env i)) f <;>
        cases evalB (fun i => decide (ω ∈ env i)) g <;> simp

/-- Ax.(iii) (有限モデル): 論証的トートロジーの解釈は、任意の前提の下で確実。 -/
theorem finPr_taut (f : Form) (env : ℕ → Finset (Fin 2)) (a : Finset (Fin 2)) (ht : Taut f) :
    finPr (finInterp env f) a = 1 := by
  rw [finPr_eq_one_iff']
  intro ω _
  rw [mem_finInterp]
  exact ht _

/-- Def. VIII (有限モデル): (a ≡ b)/h = 1 ↔ b/(a h) = 1 ∧ a/(b h) = 1。
前提が空の場合も約定 1 の下で成り立つ。 -/
theorem finPr_VIII (a b h : Finset (Fin 2)) :
    finPr ((a ∩ b) ∪ (aᶜ ∩ bᶜ)) h = 1 ↔ (finPr b (a ∩ h) = 1 ∧ finPr a (b ∩ h) = 1) := by
  rw [finPr_eq_one_iff', finPr_eq_one_iff', finPr_eq_one_iff']
  constructor
  · intro H
    constructor
    · intro ω hω
      have hωh := H (Finset.mem_of_mem_inter_right hω)
      have hωa := Finset.mem_of_mem_inter_left hω
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl] at hωh
      tauto
    · intro ω hω
      have hωh := H (Finset.mem_of_mem_inter_right hω)
      have hωb := Finset.mem_of_mem_inter_left hω
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl] at hωh
      tauto
  · rintro ⟨H1, H2⟩ ω hω
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    by_cases ha : ω ∈ a
    · exact Or.inl ⟨ha, H1 (Finset.mem_inter.mpr ⟨ha, hω⟩)⟩
    · refine Or.inr ⟨ha, fun hb => ha (H2 (Finset.mem_inter.mpr ⟨hb, hω⟩))⟩

/-! ### F22.18 の補充前提の必要性 (folio 260 "C/HE being greater than C/H")

印刷は C/H の有限性だけを挙げる。空でない前提をもつ有限モデル FinSys で
C = {0}, H = 全体, E = {1} ととると
C/H = 1/2 (有限)、E/H = 1/2 ≠ 0 (E は H の下で不可能でない) だが C/HE = 0 < C/H。
この例で欠けているのは th_22_18 が足した前提 E/CH = 1 (ここでは E/CH = 0)。 -/

theorem finPr_zero_univ_card : ((Finset.univ : Finset (Fin 2)).card : ℝ) = 2 := by
  simp

/-- **F22_18_needs_premisses**: 空でない前提をもつ FinSys では、C/H が有限なだけでは
C/HE > C/H は出ない。 -/
theorem F22_18_needs_premisses :
    0 < finPr ({0} : Finset (Fin 2)) Finset.univ ∧
    finPr ({1} : Finset (Fin 2)) Finset.univ ≠ 0 ∧
    ¬ (finPr ({0} : Finset (Fin 2)) Finset.univ < finPr {0} ({1} ∩ Finset.univ)) ∧
    finPr ({1} : Finset (Fin 2)) ({0} ∩ Finset.univ) ≠ 1 := by
  have e0 : (Finset.univ ∩ ({0} : Finset (Fin 2))).card = 1 := by decide
  have e1 : (Finset.univ ∩ ({1} : Finset (Fin 2))).card = 1 := by decide
  have e2 : (({1} : Finset (Fin 2)) ∩ Finset.univ) = {1} := by decide
  have e3 : (({1} : Finset (Fin 2)) ∩ {0}) = ∅ := by decide
  have e4 : (({0} : Finset (Fin 2)) ∩ Finset.univ) = {0} := by decide
  have e5 : (({0} : Finset (Fin 2)) ∩ {1}) = ∅ := by decide
  have hu : (Finset.univ : Finset (Fin 2)) ≠ ∅ := by decide
  have h1 : (({1} : Finset (Fin 2))) ≠ ∅ := by decide
  have h0 : (({0} : Finset (Fin 2))) ≠ ∅ := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [finPr, if_neg hu, e0, finPr_zero_univ_card]; norm_num
  · simp only [finPr, if_neg hu, e1, finPr_zero_univ_card]; norm_num
  · rw [e2]
    simp only [finPr, if_neg hu, if_neg h1, e0, e3, finPr_zero_univ_card]; norm_num
  · rw [e4]
    simp only [finPr, if_neg h0, e5]; norm_num

/-! ### 追加公理それぞれについて: FinSys_PartII ∧ ¬(追加公理の FinSys での写し)

主張の範囲 (2026-10-20 是正): 「追加公理は第 II 部の公理から導けない」とは言わない。
§0 の公理群は修復前の phase6c の写しで矛盾するので (ヘッダの注記)、その上では何でも導ける。
ここで示すのは、空でない前提について第 II 部の公理の形 (値域 finPr_range、Def. VIII finPr_VIII、
Def. IX finPr_IX、Def. X finPr_X_left/right、Ax.(iii) finPr_taut) を満たす有限モデル FinSys
(その連言が FinSys_PartII) が、記号 (g, h, x_r, gen, C, H, H′) を具体的にとると追加公理の条件
X を満たさないこと、すなわち各定理 indep_ax_22_* が「FinSys_PartII ∧ ¬X」の形をとることである。
事例の連言と y_ の FinSys での写しは finConjInst, fin_y (itrue ↦ 全体、iand ↦ ∩、
inot ↦ 補集合、PrI ↦ finPr)。 -/

/-- **FinSys_PartII**: FinSys が第 II 部の公理の形を満たすこと (Def. IX と Def. X は
空でない前提について; 値域、Def. VIII、Ax.(iii) は空前提の約定 1 の下でも成り立つ)。 -/
def FinSys_PartII : Prop :=
  (∀ b a : Finset (Fin 2), 0 ≤ finPr b a ∧ finPr b a ≤ 1) ∧
  (∀ a b h : Finset (Fin 2),
    finPr ((a ∩ b) ∪ (aᶜ ∩ bᶜ)) h = 1 ↔ (finPr b (a ∩ h) = 1 ∧ finPr a (b ∩ h) = 1)) ∧
  (∀ p q a : Finset (Fin 2), a ≠ ∅ → finPr (p ∩ qᶜ) a + finPr (p ∩ q) a = finPr p a) ∧
  (∀ p q a : Finset (Fin 2), a ≠ ∅ → finPr (p ∩ q) a = finPr p (q ∩ a) * finPr q a) ∧
  (∀ p q a : Finset (Fin 2), a ≠ ∅ → finPr (p ∩ q) a = finPr q (p ∩ a) * finPr p a) ∧
  (∀ (f : Form) (env : ℕ → Finset (Fin 2)) (a : Finset (Fin 2)),
    Taut f → finPr (finInterp env f) a = 1)

/-- **finSys_partII**: FinSys は第 II 部の公理の形を満たす (§6 前半の六定理の連言)。 -/
theorem finSys_partII : FinSys_PartII :=
  ⟨finPr_range, finPr_VIII, finPr_IX, finPr_X_left, finPr_X_right, finPr_taut⟩

/-- 補助: 空集合の確率は空でない前提の下で 0。 -/
theorem finPr_empty_concl (a : Finset (Fin 2)) (ha : a ≠ ∅) : finPr ∅ a = 0 := by
  simp [finPr, if_neg ha]

/-- 補助: 互いに素な単元集合の間の確率は 0 (C = {1}, H = {0})。 -/
theorem finPr_one_zero : finPr ({1} : Finset (Fin 2)) {0} = 0 := by
  have e : (({0} : Finset (Fin 2)) ∩ {1}) = ∅ := by decide
  have h0 : (({0} : Finset (Fin 2))) ≠ ∅ := by decide
  simp only [finPr, if_neg h0, e, Finset.card_empty, Nat.cast_zero, zero_div]

/-- 補助: 互いに素な単元集合の間の確率は 0 (H = {0}, H′ = {1})。 -/
theorem finPr_zero_one : finPr ({0} : Finset (Fin 2)) {1} = 0 := by
  have e : (({1} : Finset (Fin 2)) ∩ {0}) = ∅ := by decide
  have h1 : (({1} : Finset (Fin 2))) ≠ ∅ := by decide
  simp only [finPr, if_neg h1, e, Finset.card_empty, Nat.cast_zero, zero_div]

/-- **indep_ax_22_liv**: FinSys は第 II 部の公理の形を満たし、かつ限定独立多様性の写し
"∀ φ f, 0 < g(φf)/h" は、gen を常に ∅、h を全体とする解釈で破れる (g(φf)/h = 0)。 -/
theorem indep_ax_22_liv :
    FinSys_PartII ∧
    ¬ ∀ (φ f : Fin 2 → Finset (Fin 2)),
        0 < finPr ((fun _ _ => (∅ : Finset (Fin 2))) φ f) Finset.univ := by
  refine ⟨finSys_partII, fun H => ?_⟩
  have h : 0 < finPr (∅ : Finset (Fin 2)) Finset.univ := H (fun _ => ∅) (fun _ => ∅)
  rw [finPr_empty_concl _ (by decide)] at h
  exact lt_irrefl _ h

/-- **indep_ax_22_9**: FinSys は第 II 部の公理の形を満たし、かつ旧 ax_22_9_p0_finite の内容
"0 < g/h" は g = ∅, h = 全体で破れる。 -/
theorem indep_ax_22_9 :
    FinSys_PartII ∧ ¬ (0 < finPr (∅ : Finset (Fin 2)) Finset.univ) := by
  refine ⟨finSys_partII, ?_⟩
  rw [finPr_empty_concl _ (by decide)]
  exact lt_irrefl _

/-- **indep_ax_22_10**: FinSys は第 II 部の公理の形を満たし、かつ "∀ r, x_r/gh = 1" は
x_r = {1}, g = h = 全体で破れる (x_r/gh = 1/2)。 -/
theorem indep_ax_22_10 :
    FinSys_PartII ∧
    ¬ ∀ r : ℕ, finPr ((fun _ => ({1} : Finset (Fin 2))) r) (Finset.univ ∩ Finset.univ) = 1 := by
  refine ⟨finSys_partII, fun H => ?_⟩
  have := H 0
  rw [finPr_eq_one_iff'] at this
  have h0 := this (Finset.mem_inter.mpr ⟨Finset.mem_univ 0, Finset.mem_univ 0⟩)
  simp at h0

/-- conjInst の FinSys での写し: x_1 ∩ … ∩ x_n (n = 0 では全体)。 -/
def finConjInst (x : ℕ → Finset (Fin 2)) : ℕ → Finset (Fin 2)
  | 0 => Finset.univ
  | n + 1 => finConjInst x n ∩ x (n + 1)

/-- y_ の FinSys での写し: x_{n+1}/x_1…x_n ḡ h。 -/
noncomputable def fin_y (g h : Finset (Fin 2)) (x : ℕ → Finset (Fin 2)) (n : ℕ) : ℝ :=
  finPr (x (n + 1)) (finConjInst x n ∩ (gᶜ ∩ h))

/-- **indep_ax_22_11**: FinSys は第 II 部の公理の形を満たし、かつ
"∃ ε > 0, ∀ r, x_r/x_1…x_{r−1}ḡh = 1 − ε" は x_r = 全体, g = {0}, h = 全体で破れる
(r = 1 で x_1/ḡh = 1 なので ε = 0 になる)。 -/
theorem indep_ax_22_11 :
    FinSys_PartII ∧
    ¬ ∃ ε : ℝ, 0 < ε ∧
        ∀ n, fin_y ({0} : Finset (Fin 2)) Finset.univ (fun _ => Finset.univ) n = 1 - ε := by
  refine ⟨finSys_partII, ?_⟩
  rintro ⟨ε, hε, hy⟩
  have h0 := hy 0
  have h1 : fin_y ({0} : Finset (Fin 2)) Finset.univ (fun _ => Finset.univ) 0 = 1 := by
    unfold fin_y
    rw [finPr_eq_one_iff']
    intro ω _
    exact Finset.mem_univ ω
  rw [h1] at h0
  linarith

/-- **indep_ax_22_17**: FinSys は第 II 部の公理の形を満たし、かつ "0 < C/H" は
C = {1}, H = {0} (どちらも空でない) で破れる (C/H = 0)。
indep_ax_22_9 (g = ∅) とは別の事例をとる: 結論が空集合でなくても前提と素なら C/H = 0。 -/
theorem indep_ax_22_17 :
    FinSys_PartII ∧ ¬ (0 < finPr ({1} : Finset (Fin 2)) {0}) := by
  refine ⟨finSys_partII, ?_⟩
  rw [finPr_one_zero]
  exact lt_irrefl _

/-- **indep_ax_22_19**: FinSys は第 II 部の公理の形を満たし、かつ "0 < H/H′" は
H = {0}, H′ = {1} (どちらも空でない) で破れる (H/H′ = 0)。indep_ax_22_17 の C, H を
H, H′ に置き直した事例で、第 2 段の帰納仮説 H′ が第 1 段の H と素な場合にあたる。 -/
theorem indep_ax_22_19 :
    FinSys_PartII ∧ ¬ (0 < finPr ({0} : Finset (Fin 2)) {1}) := by
  refine ⟨finSys_partII, ?_⟩
  rw [finPr_zero_one]
  exact lt_irrefl _

end KeynesI

/-! ## 判定 (Phase 9c) -/

#check @KeynesI.th_22_1
#check @KeynesI.th_22_2
#check @KeynesI.th_22_4
#check @KeynesI.th_22_9_src
#check @KeynesI.th_22_9
#check @KeynesI.th_22_10
#check @KeynesI.th_22_11_src
#check @KeynesI.cor_22_11_chXX
#check @KeynesI.th_22_12
#check @KeynesI.th_22_12_analogy
#check @KeynesI.th_22_17
#check @KeynesI.th_22_18
#check @KeynesI.th_22_19
#check @KeynesI.E_III_4_countermodel
#check @KeynesI.E_III_4_corrected_imp_printed
#check @KeynesI.F22_18_needs_premisses

-- 第 XXII 章 (11 本 + 補助)
#print axioms KeynesI.th_22_1
#print axioms KeynesI.th_22_2
#print axioms KeynesI.th_22_4
#print axioms KeynesI.th_22_9_src
#print axioms KeynesI.th_22_9
#print axioms KeynesI.th_22_10
#print axioms KeynesI.th_22_11_src
#print axioms KeynesI.cor_22_11_chXX
#print axioms KeynesI.th_22_12
#print axioms KeynesI.th_22_12_analogy
#print axioms KeynesI.th_22_17
#print axioms KeynesI.th_22_18
#print axioms KeynesI.th_22_19
-- Notes (ii.) と E-III-4
#print axioms KeynesI.notes_viii_certain_add_l
#print axioms KeynesI.def_viii_l_imp_src
#print axioms KeynesI.def_viii_l_dep
#print axioms KeynesI.def_ix_dep
#print axioms KeynesI.def_x_src_symm
#print axioms KeynesI.E_III_4_countermodel
#print axioms KeynesI.E_III_4_corrected_imp_printed
#print axioms KeynesI.E_III_4_old_hyp_false
#print axioms KeynesI.E_III_4_corrected_holds_example
-- 有限モデルが第 II 部の公理の形を満たすこと
#print axioms KeynesI.finPr_range
#print axioms KeynesI.finPr_VIII
#print axioms KeynesI.finPr_IX
#print axioms KeynesI.finPr_X_left
#print axioms KeynesI.finPr_X_right
#print axioms KeynesI.finPr_taut
#print axioms KeynesI.finSys_partII
-- F22.18 の補充前提の必要性 (FinSys)、追加公理ごとの FinSys_PartII ∧ ¬X
#print axioms KeynesI.F22_18_needs_premisses
#print axioms KeynesI.indep_ax_22_liv
#print axioms KeynesI.indep_ax_22_9
#print axioms KeynesI.indep_ax_22_10
#print axioms KeynesI.indep_ax_22_11
#print axioms KeynesI.indep_ax_22_17
#print axioms KeynesI.indep_ax_22_19
