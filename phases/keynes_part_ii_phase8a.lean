/-
# Keynes (1921) *A Treatise on Probability* — Lean 4 Phase 8a
#
# 新井一成・Claude共著、2026年7月31日
# **第26章: リスク・慣行的係数 c = 2pw/((1+q)(1+w)) の完全代数**
# ⚠ DRAFT v1 — サンドボックス未コンパイル。check_phase8.sh でローカル確認。
#
# ## 原典アンカー (英tex l.15734-15768, folio 314-316 — WEIGHT_DESIGN.md §1)
#   リスク: E = pA, R = p(A−E) = p(1−p)A = pqA = qE
#   Czuber 再保険級数 (脚注): E(1+q+q²+…) = E/p = A
#   慣行的係数: c = 2pw/((1+q)(1+w))、q = 1−p。境界: p=1∧w=1→1、p=0∨w=0→0
#   ケインズ脚注の比較静学 (pA = p′A′ の下):
#     F1: w>w′ ∧ q=q′ ⟹ cA > c′A′
#     F2: w=w′ ∧ q<q′ ⟹ cA > c′A′
#     F3: w>w′ ∧ q<q′ ⟹ cA > c′A′
#     F4: w=w′ ∧ q>q′ ⟹ 「一般には比較できない」(印刷本文)
#
# ## 本ファイルの判定対象
#   T1  risk_identities      : R の恒等式連鎖
#   T2  czuber_partial/rem   : 再保険級数の有限閉形式と残差
#   T3  c_one_one/c_zero_*/c_nonneg/c_le_one : 境界条件と値域
#   T4-T6 keynes_F1/F2/F3    : 脚注不等式3本
#   T7a keynes_F4_printed_determinate : ⚠印刷版F4のケース (w=w′∧q>q′) は
#       実は確定的に cA < c′A′ — F2 と記号交換で同一ケースのため。
#       「比較できない」という印刷本文への機械的反証 (正誤候補#3)
#   T7b keynes_F4_amended_incomparable : 修正案 {w>w′ ∧ q>q′} (重みと危険が
#       逆方向) は真に非比較 — 両向きの具体証人ペア
#   T8  c_superadd           : c は p について超加法的 (確実性愛好) —
#       2012年予想(C2)の W との対照項
#
# ## 予測 (H34): 本ファイル全定理は floor のみ (Keynes 公理ゼロ)。
#   第26章の係数計算は (55) と同じく基盤算術である。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KeynesWeight

/-! ## T1: リスクの恒等式 (folio 314) -/

/-- E = pA、q = 1−p のとき R = p(A−E) = pqA = qE。 -/
theorem risk_identities (p A : ℝ) :
    p * (A - p * A) = p * (1 - p) * A ∧
    p * (1 - p) * A = (1 - p) * (p * A) := by
  constructor <;> ring

/-! ## T2: Czuber 再保険級数 (folio 314 脚注) -/

/-- 幾何部分和 (自前再帰 — Finset API のドリフト回避)。 -/
noncomputable def geomSum (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => geomSum q n + q ^ (n + 1)

/-- **Czuber 級数の有限閉形式**: E·(1+q+…+qⁿ) = A·(1 − q^{n+1})、E = pA、q = 1−p。 -/
theorem czuber_partial (p A : ℝ) : ∀ n : ℕ,
    (p * A) * geomSum (1 - p) n = A * (1 - (1 - p) ^ (n + 1)) := by
  intro n
  induction n with
  | zero => simp [geomSum]; ring
  | succ k ih =>
      simp only [geomSum]
      have : p * A * (geomSum (1 - p) k + (1 - p) ^ (k + 1))
          = p * A * geomSum (1 - p) k + p * A * (1 - p) ^ (k + 1) := by ring
      rw [this, ih]
      ring

/-- 残差形: A − E·Σqᵏ = A·q^{n+1} — 「十分な回数の再保険でリスクは完全に移転できる」
の残差が幾何的に消えることの代数的核 (極限は位相を要するため残差表示で述べる)。 -/
theorem czuber_remainder (p A : ℝ) (n : ℕ) :
    A - (p * A) * geomSum (1 - p) n = A * (1 - p) ^ (n + 1) := by
  rw [czuber_partial]
  ring

/-! ## 慣行的係数 c -/

/-- **c = 2pw/((1+q)(1+w))**、q = 1−p により 1+q = 2−p。 -/
noncomputable def c (p w : ℝ) : ℝ := 2 * p * w / ((2 - p) * (1 + w))

theorem den_pos {p w : ℝ} (hp1 : p ≤ 1) (hw0 : 0 ≤ w) :
    0 < (2 - p) * (1 + w) := by nlinarith

theorem c_spec {p w : ℝ} (hp1 : p ≤ 1) (hw0 : 0 ≤ w) :
    c p w * ((2 - p) * (1 + w)) = 2 * p * w := by
  unfold c
  exact div_mul_cancel₀ _ (ne_of_gt (den_pos hp1 hw0))

/-- 除算比較の自前ヘルパ (div_lt_div_iff 系のドリフト回避)。 -/
theorem div_lt_div_of_cross {a1 a2 d1 d2 : ℝ} (h1 : 0 < d1) (h2 : 0 < d2)
    (hx : a1 * d2 < a2 * d1) : a1 / d1 < a2 / d2 := by
  have hd1 : d1 ≠ 0 := ne_of_gt h1
  have hd2 : d2 ≠ 0 := ne_of_gt h2
  have e1 : a1 / d1 * (d1 * d2) = a1 * d2 := by
    first | (field_simp; ring) | field_simp
  have e2 : a2 / d2 * (d1 * d2) = a2 * d1 := by
    first | (field_simp; ring) | field_simp
  have hp : 0 < d1 * d2 := mul_pos h1 h2
  nlinarith [e1, e2]

/-! ## T3: 境界条件と値域 (folio 315) -/

theorem c_one_one : c 1 1 = 1 := by unfold c; norm_num

theorem c_zero_p (w : ℝ) : c 0 w = 0 := by unfold c; simp

theorem c_zero_w (p : ℝ) : c p 0 = 0 := by unfold c; simp

theorem c_nonneg {p w : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hw0 : 0 ≤ w) :
    0 ≤ c p w := by
  unfold c
  apply div_nonneg
  · nlinarith
  · exact le_of_lt (den_pos hp1 hw0)

theorem c_le_one {p w : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : c p w ≤ 1 := by
  have hd := den_pos hp1 hw0
  have key : 2 * p * w ≤ (2 - p) * (1 + w) := by nlinarith
  unfold c
  first
    | exact (div_le_one hd).mpr key
    | { rw [div_le_one hd]; exact key }

/-! ## T4-T6: ケインズ脚注の比較静学 (folio 315 脚注) -/

/- 中核構図: pA = p′A′ =: E > 0 のとき cA = (2w/(1+w))·E/(2−p)。
比較は「重み因子 × 危険因子」に分解される。以下は直接比較で処理。 -/

/-- **F1** (w>w′、q=q′ すなわち p=p′): cA > c′A′。 -/
theorem keynes_F1 {p w w' A A' : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hA : 0 < A)
    (hE : p * A = p * A') (hw' : 0 ≤ w') (hww : w' < w) :
    c p w' * A' < c p w * A := by
  have hAA : A' = A := by
    have := mul_left_cancel₀ (ne_of_gt hp0) hE
    linarith [this]
  subst hAA
  have hcc : c p w' < c p w := by
    unfold c
    apply div_lt_div_of_cross (den_pos hp1 hw')
      (den_pos hp1 (le_of_lt (lt_of_le_of_lt hw' hww)))
    -- 交差: 2pw′·(2−p)(1+w) < 2pw·(2−p)(1+w′) ⟺ w′(1+w) < w(1+w′) ⟺ w′ < w
    have h2p : (0 : ℝ) < 2 - p := by linarith
    nlinarith [mul_pos (mul_pos hp0 h2p) (sub_pos.mpr hww)]
  exact mul_lt_mul_of_pos_right hcc hA

/-- c の正値性 (0<p≤1、0<w)。 -/
theorem c_pos {p w : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hw0 : 0 < w) :
    0 < c p w := by
  unfold c
  apply div_pos
  · nlinarith
  · exact den_pos hp1 (le_of_lt hw0)

/-- cA の払い出し: (cA)·(2−p)(1+w) = 2w·(pA)。比較静学の共通エンジン。 -/
theorem cA_spec {p w A : ℝ} (hp1 : p ≤ 1) (hw0 : 0 ≤ w) :
    (c p w * A) * ((2 - p) * (1 + w)) = 2 * w * (p * A) := by
  have h := c_spec hp1 hw0
  calc (c p w * A) * ((2 - p) * (1 + w))
      = (c p w * ((2 - p) * (1 + w))) * A := by ring
    _ = (2 * p * w) * A := by rw [h]
    _ = 2 * w * (p * A) := by ring

/-- **F2** (w=w′、q<q′ すなわち p>p′): cA > c′A′。 -/
theorem keynes_F2 {p p' w A A' : ℝ}
    (hp'0 : 0 < p') (hp1 : p ≤ 1) (hp'1 : p' ≤ 1) (hA : 0 < A)
    (hE : p * A = p' * A') (hw0 : 0 < w) (hpp : p' < p) :
    c p' w * A' < c p w * A := by
  have hp0 : 0 < p := lt_trans hp'0 hpp
  have hw0' : 0 ≤ w := le_of_lt hw0
  have h1w : (0 : ℝ) < 1 + w := by linarith
  have hX : 0 < c p w * A := mul_pos (c_pos hp0 hp1 hw0) hA
  have m1 := cA_spec (A := A) hp1 hw0'
  have m2 := cA_spec (A := A') hp'1 hw0'
  -- 共通値: 両者の払い出しは 2w·(pA) に一致
  have meq : (c p' w * A') * ((2 - p') * (1 + w))
      = (c p w * A) * ((2 - p) * (1 + w)) := by
    rw [m1, m2, ← hE]
  -- (2−p)(1+w) < (2−p′)(1+w) と X>0 から Y·D′ = X·D < X·D′ → Y < X
  have hDlt : (2 - p) * (1 + w) < (2 - p') * (1 + w) := by nlinarith
  have step : (c p' w * A') * ((2 - p') * (1 + w))
      < (c p w * A) * ((2 - p') * (1 + w)) := by
    rw [meq]
    exact mul_lt_mul_of_pos_left hDlt hX
  have hD' : 0 < (2 - p') * (1 + w) := den_pos hp'1 hw0'
  exact lt_of_mul_lt_mul_right step (le_of_lt hD')

/-- **F3** (w>w′、q<q′): cA > c′A′ — 重み単調 (F1) と危険単調 (F2) の連鎖。 -/
theorem keynes_F3 {p p' w w' A A' : ℝ}
    (hp'0 : 0 < p') (hp1 : p ≤ 1) (hp'1 : p' ≤ 1) (hA : 0 < A)
    (hE : p * A = p' * A') (hw'0 : 0 ≤ w') (hww : w' < w) (hpp : p' < p) :
    c p' w' * A' < c p w * A := by
  have hp0 : 0 < p := lt_trans hp'0 hpp
  have hA' : 0 < A' := by
    have hE0 : 0 < p' * A' := by rw [← hE]; exact mul_pos hp0 hA
    nlinarith
  -- 第1段: 同じ p′,A′ で重みを w′→w に上げる (F1 型)
  have step1 : c p' w' * A' < c p' w * A' :=
    keynes_F1 hp'0 hp'1 hA' rfl hw'0 hww
  -- 第2段: 危険側 (F2)
  have hw0 : 0 < w := lt_of_le_of_lt hw'0 hww
  have step2 : c p' w * A' < c p w * A :=
    keynes_F2 hp'0 hp1 hp'1 hA hE hw0 hpp
  exact lt_trans step1 step2

/-! ## T7: F4 の裁定 -/

/-- **T7a ⚠正誤候補#3**: 印刷版 F4 のケース (w=w′、q>q′ すなわち p<p′) は
「一般に比較できない」どころか**確定的**: cA < c′A′。
証明は F2 の記号交換そのもの — 印刷本文の F2 と F4 は同一ケースの
双対であり、F4 の「比較できない」は F2 と両立しない。 -/
theorem keynes_F4_printed_determinate {p p' w A A' : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hp'1 : p' ≤ 1) (hA' : 0 < A')
    (hE : p * A = p' * A') (hw0 : 0 < w) (hpp : p < p') :
    c p w * A < c p' w * A' :=
  keynes_F2 hp0 hp'1 hp1 hA' hE.symm hw0 hpp

/-- **T7b**: 修正案 F4′ = {w>w′ ∧ q>q′} (重みは第1項に有利、危険は不利) は
真に非比較 — 証人ペア。共通: E=1, p=1/2, A=2, p′=3/4, A′=4/3, w=1。
証人A (w′=9/10): cA < c′A′。 -/
theorem keynes_F4_amended_witness_lt :
    c (1/2) 1 * 2 < c (3/4) (9/10) * (4/3) := by
  unfold c
  norm_num

/-- **T7b続**: 証人B (w′=1/100): cA > c′A′。同一の符号条件 (w>w′, q>q′) で
逆順 — 併せて非比較性の機械的証明。 -/
theorem keynes_F4_amended_witness_gt :
    c (3/4) (1/100) * (4/3) < c (1/2) 1 * 2 := by
  unfold c
  norm_num

/-! ## T8: c の超加法性 (2012年予想 W との対照) -/

/-- **c は p について超加法的**: c(p₁,w) + c(p₂,w) ≤ c(p₁+p₂,w)。
差は 2w·p₁p₂(4−(p₁+p₂)) ≥ 0 に比例する。ケインズの慣行的係数は
「確実性愛好」— 短期確率加重関数 W (phase8b) の小確率過大視と正反対。 -/
theorem c_superadd {p₁ p₂ w : ℝ}
    (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (hs : p₁ + p₂ ≤ 1) (hw : 0 ≤ w) :
    c p₁ w + c p₂ w ≤ c (p₁ + p₂) w := by
  have h1' : p₁ ≤ 1 := by linarith
  have h2' : p₂ ≤ 1 := by linarith
  have hd1 := den_pos h1' hw
  have hd2 := den_pos h2' hw
  have hds := den_pos hs hw
  have e1 := c_spec h1' hw
  have e2 := c_spec h2' hw
  have es := c_spec hs hw
  -- 全分母の積 P で払う
  set D1 := (2 - p₁) * (1 + w) with hD1
  set D2 := (2 - p₂) * (1 + w) with hD2
  set Ds := (2 - (p₁ + p₂)) * (1 + w) with hDs
  have E1 : c p₁ w * (D1 * (D2 * Ds)) = 2 * p₁ * w * (D2 * Ds) := by
    calc c p₁ w * (D1 * (D2 * Ds)) = (c p₁ w * D1) * (D2 * Ds) := by ring
    _ = 2 * p₁ * w * (D2 * Ds) := by rw [e1]
  have E2 : c p₂ w * (D1 * (D2 * Ds)) = 2 * p₂ * w * (D1 * Ds) := by
    calc c p₂ w * (D1 * (D2 * Ds)) = (c p₂ w * D2) * (D1 * Ds) := by ring
    _ = 2 * p₂ * w * (D1 * Ds) := by rw [e2]
  have Es : c (p₁ + p₂) w * (D1 * (D2 * Ds)) = 2 * (p₁ + p₂) * w * (D1 * D2) := by
    calc c (p₁ + p₂) w * (D1 * (D2 * Ds))
        = (c (p₁ + p₂) w * Ds) * (D1 * D2) := by ring
    _ = 2 * (p₁ + p₂) * w * (D1 * D2) := by rw [es]
  -- 多項式核: 差 = 2w(1+w)²·p₁p₂·(4−s) ≥ 0
  have key : 2 * p₁ * w * (D2 * Ds) + 2 * p₂ * w * (D1 * Ds)
      ≤ 2 * (p₁ + p₂) * w * (D1 * D2) := by
    simp only [hD1, hD2, hDs]
    nlinarith [mul_nonneg (mul_nonneg h1 h2) hw, sq_nonneg (1 + w),
               mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hw) (sq_nonneg (1 + w))]
  have hP : 0 < D1 * (D2 * Ds) := mul_pos hd1 (mul_pos hd2 hds)
  have goal' : (c p₁ w + c p₂ w) * (D1 * (D2 * Ds))
      ≤ c (p₁ + p₂) w * (D1 * (D2 * Ds)) := by
    have expand : (c p₁ w + c p₂ w) * (D1 * (D2 * Ds))
        = c p₁ w * (D1 * (D2 * Ds)) + c p₂ w * (D1 * (D2 * Ds)) := by ring
    rw [expand, E1, E2, Es]
    exact key
  exact le_of_mul_le_mul_right goal' hP

end KeynesWeight

/-! ## 監査クエリ (Phase 8a) -/

#check @KeynesWeight.risk_identities
#check @KeynesWeight.czuber_partial
#check @KeynesWeight.czuber_remainder
#check @KeynesWeight.c_one_one
#check @KeynesWeight.c_le_one
#check @KeynesWeight.keynes_F1
#check @KeynesWeight.keynes_F4_amended_witness_lt
#check @KeynesWeight.keynes_F4_amended_witness_gt
#check @KeynesWeight.c_superadd

#print axioms KeynesWeight.risk_identities
#print axioms KeynesWeight.czuber_partial
#print axioms KeynesWeight.czuber_remainder
#print axioms KeynesWeight.c_one_one
#print axioms KeynesWeight.c_nonneg
#print axioms KeynesWeight.c_le_one
#print axioms KeynesWeight.keynes_F1
#print axioms KeynesWeight.keynes_F2
#print axioms KeynesWeight.keynes_F3
#print axioms KeynesWeight.keynes_F4_printed_determinate
#print axioms KeynesWeight.keynes_F4_amended_witness_lt
#print axioms KeynesWeight.keynes_F4_amended_witness_gt
#print axioms KeynesWeight.c_superadd
