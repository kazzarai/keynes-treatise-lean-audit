/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 3b
#
# 新井一成・Claude共著、2026年4月
# Phase 3a (Ch.14 乗法・Bayes 基本形, 28 ノード) → Phase 3b (Johnson 影響係数, +5 定理)
#
# ## 本ファイルで追加したもの
#   Definitions (新):
#     Infl  : Johnson 影響係数 {αβ} := Pr(α∧β,h) / (Pr α h · Pr β h)
#   Theorems:
#     Th.(14.41)_b : αβ/h = {αβ} · α/h · β/h           ――― Def.XI 経由
#     Th.(14.42)   : {αβ} = {βα}                        ――― 交換律
#     Th.(14.44)   : 独立 → {αβ} = 1                    ――― Th.(14.36) 経由
#     Th.(14.44.1) : {αβ} = 1 → αβ/h = α/h · β/h        ――― 逆方向
#     (補助) infl_eq_one_iff : {αβ} = 1 ⇔ αβ/h = α/h·β/h
#
# 継承: Phase 3a の全 28 ノード (再掲)
#
# ## Phase 3b で意図的に省いた定理
#   (43) 分離因数規則  ――― n-ary 一般化が必要、Phase 3c へ
#   (45) 反復規則 {ααβ}={αβ} ――― 命題集合上の {} 表記が必要、Phase 3c へ
#
# ## 期待される新規 surface
#   th_14_41_b : def_X_left (Th.14.36 経由でなく直接), def_XI
#   th_14_42   : ax_iii_op (∧ 交換律), 算術
#   th_14_44   : th_14_36 経由で def_X_left のみ
#   th_14_44_1 : 算術 + th_14_36 逆方向
#
# ## 検証方法
#   1. https://live.lean-lang.org/ にアクセス
#   2. エディタ全消去 → このファイルを貼る
#   3. Mathlib ロード後、赤波線がないこと
#   4. ファイル末尾の `#print axioms` 出力を確認
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Keynes

/-! ## プリミティブ・公理・定義 (Phase 3a から継承) -/

axiom Pr : Prop → Prop → ℝ

def Certain       (α h : Prop) : Prop := Pr α h = 1
def Impossible    (α h : Prop) : Prop := Pr α h = 0
def NonCertain    (α h : Prop) : Prop := Pr α h < 1
def NonImpossible (α h : Prop) : Prop := 0 < Pr α h
def Inconsistent  (α h : Prop) : Prop := Pr α h = 0
def InGroup       (α h : Prop) : Prop := Pr α h = 1
def KEq (α β h : Prop) : Prop := Pr β (α ∧ h) = 1 ∧ Pr α (β ∧ h) = 1

axiom ax_ii (α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)
axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1
axiom ax_iva_mul (P Q : ℝ) : P * Q = Q * P
axiom ax_iva_add (P Q : ℝ) : P + Q = Q + P
axiom ax_ivb (P Q : ℝ) : 0 < Q → P < P + Q
axiom ax_ivc (P Q R : ℝ) : P + Q = P + R → Q = R
axiom ax_v (P Q R S : ℝ) : (P + Q) + (R + S) = (P + R) + (Q + S)
axiom ax_vi (P R S : ℝ) : P * (R + S) = P * R + P * S

axiom def_IX (p q h : Prop) :
    Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h
axiom def_X_left (p q h : Prop) :
    Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h
axiom def_X_right (p q h : Prop) :
    Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h
axiom def_XI (P Q R : ℝ) (hQ : Q ≠ 0) :
    P * Q = R → P = R / Q
axiom def_XII (P Q R : ℝ) :
    P + Q = R → P = R - Q

def Independent (p q h : Prop) : Prop :=
    Pr p (q ∧ h) = Pr p h ∧ Pr q (p ∧ h) = Pr q h
def Irrelevant (α₂ α₁ h : Prop) : Prop := Pr α₁ (α₂ ∧ h) = Pr α₁ h

/-! ## Phase 3a の既証定理 (回帰用) -/

theorem th_24 (α β h : Prop) :
    Pr (α ∨ β) h = Pr α h + Pr β h - Pr (α ∧ β) h := by
  have step1 : Pr ((α ∨ β) ∧ ¬β) h + Pr ((α ∨ β) ∧ β) h = Pr (α ∨ β) h :=
    def_IX (α ∨ β) β h
  have eq1 : ((α ∨ β) ∧ ¬β) ↔ (α ∧ ¬β) := by tauto
  have eq2 : ((α ∨ β) ∧ β) ↔ β := by tauto
  rw [ax_iii_op _ _ h eq1, ax_iii_op _ _ h eq2] at step1
  have step3 : Pr (α ∧ ¬β) h + Pr (α ∧ β) h = Pr α h :=
    def_IX α β h
  linarith

theorem th_14_36 (α β h : Prop) (hindep : Independent α β h) :
    Pr (α ∧ β) h = Pr α h * Pr β h := by
  have step1 : Pr (α ∧ β) h = Pr α (β ∧ h) * Pr β h :=
    def_X_left α β h
  rw [step1, hindep.1]

/-! ## Phase 3b: Johnson 影響係数 -/

/-- **Johnson 影響係数** {αβ}.
Keynes p.158: $\{\alpha\beta\} := \dfrac{\alpha\beta/h}{(\alpha/h)(\beta/h)}$.

α と β が独立 ⇔ {αβ}=1.
独立から離れる度合いを測る統計的依存性の係数(modern term: dependency ratio,
related to mutual information).

`noncomputable` 修飾は ℝ の除法が classical であるため必須(Mathlib では
`Real.instDivInvMonoid` が noncomputable)。 -/
noncomputable def Infl (α β h : Prop) : ℝ := Pr (α ∧ β) h / (Pr α h * Pr β h)

/-- **Th.(14.41)_b** 影響係数による αβ/h の累積展開.
$\alpha\beta/h = \{\alpha\beta\} \cdot \alpha/h \cdot \beta/h$ when
$\alpha/h \neq 0$ and $\beta/h \neq 0$.

Keynes Prolog DB: cites(th14_41, def_x), cites(th14_41, def_xiii).

## Proof architecture
| Step | Mechanism                | Cites             |
|------|--------------------------|-------------------|
|  1   | Infl の定義展開          | (Lean def)        |
|  2   | div_mul_cancel (field)   | (Mathlib)         |

`Infl` が `def` なので axiom として surface しない。実際に必要なのは
`Pr α h * Pr β h ≠ 0` という field operation 用の前提のみ。
Keynes が引用する `def_x`, `def_xiii` は Infl 定義の中に包摂される。 -/
theorem th_14_41_b (α β h : Prop) (hα : Pr α h ≠ 0) (hβ : Pr β h ≠ 0) :
    Pr (α ∧ β) h = Infl α β h * Pr α h * Pr β h := by
  unfold Infl
  have hprod : Pr α h * Pr β h ≠ 0 := mul_ne_zero hα hβ
  field_simp

/-- **Th.(14.42)** 影響係数の交換律. {αβ} = {βα}.

Keynes Prolog DB: cites(th14_42, def_x).

## Proof architecture
| Step | Mechanism                | Cites             |
|------|--------------------------|-------------------|
|  1   | Infl の定義展開          | (Lean def)        |
|  2   | (α∧β) ↔ (β∧α) by tauto   | explicit ax_iii_op|
|  3   | ℝ 乗法可換             | (built-in)        |

注意: Keynes は (42) を「Def.X による式変形」だけで導出しているが、
Lean では (α∧β) と (β∧α) の同値性も明示的に必要。
これは th_14_24_2 と同様の Mode A' finding (∧ 交換律が implicit Ax.(iii))。 -/
theorem th_14_42 (α β h : Prop) : Infl α β h = Infl β α h := by
  unfold Infl
  have eq : (α ∧ β) ↔ (β ∧ α) := by tauto
  rw [ax_iii_op _ _ h eq, mul_comm (Pr α h) (Pr β h)]

/-- **Th.(14.44)** 独立性 → 影響係数 = 1.

Keynes Prolog DB: cites(th14_44, def_x), cites(th14_44, th14_41_2).

## Proof architecture
| Step | Mechanism                | Cites             |
|------|--------------------------|-------------------|
|  1   | th_14_36 (乗法定理)      | explicit          |
|  2   | Infl の定義展開          | (Lean def)        |
|  3   | 自己除算                 | (Mathlib field)   |

検証対象: th_14_36 経由でのみ閉じるため、kernel リストに def_X_left のみ
出るはず(他の axiom は要らない)。 -/
theorem th_14_44 (α β h : Prop)
    (hindep : Independent α β h) (hα : Pr α h ≠ 0) (hβ : Pr β h ≠ 0) :
    Infl α β h = 1 := by
  unfold Infl
  rw [th_14_36 α β h hindep]
  exact div_self (mul_ne_zero hα hβ)

/-- **Th.(14.44.1)** 影響係数 = 1 → αβ/h = α/h · β/h (独立性は推論できないが
    積分解は成立する).
    Keynes 原文では (44.1) は「{αβ}=1 → α/h と β/h は独立な推論」だが、
    本 Lean 版は積分解だけを述べる weaker 形. 真の独立性 (条件付き確率の等式)
    の導出は Phase 3c へ. -/
theorem th_14_44_1 (α β h : Prop)
    (hα : Pr α h ≠ 0) (hβ : Pr β h ≠ 0) (hinfl : Infl α β h = 1) :
    Pr (α ∧ β) h = Pr α h * Pr β h := by
  have h41 : Pr (α ∧ β) h = Infl α β h * Pr α h * Pr β h :=
    th_14_41_b α β h hα hβ
  rw [hinfl] at h41
  linarith

/-- **補助** `infl_eq_one_iff_indep_product`. 上 2 定理の合成. -/
theorem infl_eq_one_iff_indep_product (α β h : Prop)
    (hα : Pr α h ≠ 0) (hβ : Pr β h ≠ 0) :
    Infl α β h = 1 ↔ Pr (α ∧ β) h = Pr α h * Pr β h := by
  constructor
  · intro hinfl
    exact th_14_44_1 α β h hα hβ hinfl
  · intro h_eq
    unfold Infl
    rw [h_eq]
    exact div_self (mul_ne_zero hα hβ)

end Keynes

/-! ## 監査クエリ (Phase 3b 新規) -/

#check @Keynes.Infl
#check @Keynes.th_14_41_b
#check @Keynes.th_14_42
#check @Keynes.th_14_44
#check @Keynes.th_14_44_1
#check @Keynes.infl_eq_one_iff_indep_product

-- Kernel 依存. 注目点:
--   - Infl は def なので axiom リストには出ない
--   - field_simp が tactic として使われた箇所では `Pr` のみ surface するはず
--     (def_XI は明示的に呼ばないと出ない、Phase 3a と同じ理由)
--   - th_14_44 は th_14_36 経由なので def_X_left が surface
--   - th_14_42 は ax_iii_op が surface (Mode A' on conjunction commutativity)
#print axioms Keynes.th_14_41_b
#print axioms Keynes.th_14_42
#print axioms Keynes.th_14_44
#print axioms Keynes.th_14_44_1
#print axioms Keynes.infl_eq_one_iff_indep_product

-- 回帰テスト
#print axioms Keynes.th_14_36
#print axioms Keynes.th_24
