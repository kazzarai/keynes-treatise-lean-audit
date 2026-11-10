/-
# Keynes (1921) *A Treatise on Probability* — Lean 4 Phase 8a-3

# **第26章 (The Application of Probability to Conduct) の端点・前提・積分の補い (B50)**

## 原典アンカー (1921 Macmillan 初版、PDF 頁 = folio + 20)
  folio 315 §8 (係数 c の端点、脚注 2 の F1–F4 の条件)、folio 317 §9 (Bernoulli の道徳的財産)、
  folio 318 (x = (a+x₁)^{p₁}(a+x₂)^{p₂}…)、folio 319 §10 (Laurent の f(a), b = ∞)。
  台帳: docs/全数台帳/ch26.md。phase8a / phase8a2 はこの前提を p′ → p, w′ → w の置換で吸収して
  いたので、台帳の行 `p = 1`, `w = 1`, `p = 0`, `w = 0`, `q = q′`, `w = w′`, `b = ∞` は定理文に
  現れなかった。本ファイルは同じ主張を**前提として明示した形**で述べ直す (定: 例の仮定・端点の約定)。
  phase ファイルは相互に import しないので、c は自前で定義する (phase8a と同一の式)。

## 本ファイルの判定対象 (台帳の行 → 定理)
  ch26-001  (p + q = 1)          前提 hpq, hpq′ (th_26_fn2_F1_explicit 等)
  ch26-002  E = pA               th_26_risk_identities_explicit (前提 hE; q は前提 hpq で p + q = 1)
  ch26-006  p = 1,  ch26-007  w = 1    th_26_c_endpoint_one       (c = 1)
  ch26-008  p = 0                     th_26_c_endpoint_zero_p    (c = 0)
  ch26-009  w = 0                     th_26_c_endpoint_zero_w    (c = 0)
  ch26-014  q = q′                    th_26_fn2_F1_explicit (前提 hqq)
  ch26-017  w = w′                    th_26_fn2_F2_explicit (前提 hww)
  ch26-025  w = w′                    th_26_fn2_F4_printed_explicit (前提 hww)
  ch26-034  y = k log x/a             th_26_bernoulli_integral (∫ₐˣ k dt/t)、th_26_bernoulli_ode_unique
                                      (dy = k dx/x かつ y(a) = 0 なら y = k log(x/a))
  ch26-035  x = Π(a + x_i)^{p_i}      th_26_moral_fortune_eq (x の「道徳的財産が期待のそれに等しい」という
                                      性質からの導出; 印刷は指数が組み落とされている → phase8a2/th_26_laplace_printed_refuted;
                                      判定は ✎ (印刷形の反駁と修正形の定理がある))
  ch26-040  b = ∞                     th_26_laurent_infinite_b (前提 b_n → ∞)

## 形式化の境界の記録 (定理にしていないもの)
  * ch26-039 f(a) = b/(a+b): Laurent の引用。賭けの模型 (公平な 1 単位の賭けか) が印刷になく、脚注 2 は
    導出に疑義を述べる。f の def も置かない (未)。
  * ch26-041 f(a) = 1: 結論側。b → ∞ の極限形 (phase8a2/th_26_laurent_limit) を ✎ に数えるかは裁定待ち (未)。

## 予測: 本ファイルの全定理は Lean の標準の三公理 (propext, Classical.choice, Quot.sound) のみに依存する。
-/

import Mathlib

namespace KeynesCh26b

open Filter Topology MeasureTheory intervalIntegral

/-- 慣行的係数 c = 2pw/((1+q)(1+w))、1+q = 2−p (phase8a `c` と同一)。 -/
noncomputable def c (p w : ℝ) : ℝ := 2 * p * w / ((2 - p) * (1 + w))

theorem den_pos {p w : ℝ} (hp1 : p ≤ 1) (hw0 : 0 ≤ w) : 0 < (2 - p) * (1 + w) := by nlinarith

theorem c_spec {p w : ℝ} (hp1 : p ≤ 1) (hw0 : 0 ≤ w) :
    c p w * ((2 - p) * (1 + w)) = 2 * p * w := by
  unfold c
  exact div_mul_cancel₀ _ (ne_of_gt (den_pos hp1 hw0))

theorem c_pos {p w : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hw0 : 0 < w) : 0 < c p w := by
  unfold c
  apply div_pos
  · nlinarith
  · exact den_pos hp1 (le_of_lt hw0)

theorem cA_spec {p w A : ℝ} (hp1 : p ≤ 1) (hw0 : 0 ≤ w) :
    (c p w * A) * ((2 - p) * (1 + w)) = 2 * w * (p * A) := by
  have h := c_spec hp1 hw0
  calc (c p w * A) * ((2 - p) * (1 + w)) = (c p w * ((2 - p) * (1 + w))) * A := by ring
    _ = (2 * p * w) * A := by rw [h]
    _ = 2 * w * (p * A) := by ring

/-! ## A. folio 315 §8 — 端点 (ch26-006〜009) -/

/-- 印刷: 「c は p = 1 かつ w = 1 のとき 1 に等しい」。条件 p = 1, w = 1 を前提 hp, hw として置く。 -/
theorem th_26_c_endpoint_one {p w : ℝ} (hp : p = 1) (hw : w = 1) : c p w = 1 := by
  subst hp; subst hw; unfold c; norm_num

/-- 印刷: 「p = 0 のとき c は 0」。条件 p = 0 を前提 hp として置く (w は任意)。 -/
theorem th_26_c_endpoint_zero_p {p w : ℝ} (hp : p = 0) : c p w = 0 := by
  subst hp; unfold c; simp

/-- 印刷: 「w = 0 のとき c は 0」。条件 w = 0 を前提 hw として置く (p は任意)。 -/
theorem th_26_c_endpoint_zero_w {p w : ℝ} (hw : w = 0) : c p w = 0 := by
  subst hw; unfold c; simp

/-! ## B. folio 315 脚注 2 — F1・F2・F4 の条件を前提として明示した形 (ch26-001, 014, 017, 025) -/

/-- **F1 (条件を明示)**: p + q = 1, p′ + q′ = 1, pA = p′A′, w > w′, q = q′ ⟹ cA > c′A′
(phase8a `keynes_F1` は q = q′ を p′ = p の置換で吸収していた)。 -/
theorem th_26_fn2_F1_explicit {p p' q q' w w' A A' : ℝ}
    (hpq : p + q = 1) (hpq' : p' + q' = 1) (hqq : q = q')
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hA : 0 < A)
    (hE : p * A = p' * A') (hw' : 0 ≤ w') (hww : w' < w) :
    c p' w' * A' < c p w * A := by
  have hpp : p' = p := by linarith
  subst hpp
  have hAA : A' = A := by
    have := mul_left_cancel₀ (ne_of_gt hp0) hE
    linarith [this]
  subst hAA
  have hw0 : 0 ≤ w := le_of_lt (lt_of_le_of_lt hw' hww)
  have hd1 := den_pos hp1 hw'
  have hd2 := den_pos hp1 hw0
  have hcc : c p' w' < c p' w := by
    unfold c
    rw [div_lt_div_iff₀ hd1 hd2]
    have h2p : (0 : ℝ) < 2 - p' := by linarith
    nlinarith [mul_pos (mul_pos hp0 h2p) (sub_pos.mpr hww)]
  exact mul_lt_mul_of_pos_right hcc hA

/-- **F2 (条件を明示)**: p + q = 1, p′ + q′ = 1, pA = p′A′, w = w′, q < q′ ⟹ cA > c′A′
(phase8a `keynes_F2` は w = w′ を置換で吸収していた)。 -/
theorem th_26_fn2_F2_explicit {p p' q q' w w' A A' : ℝ}
    (hpq : p + q = 1) (hpq' : p' + q' = 1) (hww : w = w')
    (hp'0 : 0 < p') (hp1 : p ≤ 1) (hp'1 : p' ≤ 1) (hA : 0 < A)
    (hE : p * A = p' * A') (hw0 : 0 < w) (hqq : q < q') :
    c p' w' * A' < c p w * A := by
  subst hww
  have hpp : p' < p := by linarith
  have hp0 : 0 < p := lt_trans hp'0 hpp
  have hw0' : 0 ≤ w := le_of_lt hw0
  have hX : 0 < c p w * A := mul_pos (c_pos hp0 hp1 hw0) hA
  have m1 := cA_spec (A := A) hp1 hw0'
  have m2 := cA_spec (A := A') hp'1 hw0'
  have meq : (c p' w * A') * ((2 - p') * (1 + w)) = (c p w * A) * ((2 - p) * (1 + w)) := by
    rw [m1, m2, ← hE]
  have hDlt : (2 - p) * (1 + w) < (2 - p') * (1 + w) := by nlinarith
  have step : (c p' w * A') * ((2 - p') * (1 + w)) < (c p w * A) * ((2 - p') * (1 + w)) := by
    rw [meq]
    exact mul_lt_mul_of_pos_left hDlt hX
  have hD' : 0 < (2 - p') * (1 + w) := den_pos hp'1 hw0'
  exact lt_of_mul_lt_mul_right step (le_of_lt hD')

/-- **F4 (印刷どおりの条件を明示)**: pA = p′A′, w = w′, q > q′ のとき「一般に比較できない」と印刷されているが、
F2 の記号交換で cA < c′A′ が確定する (phase8a `keynes_F4_printed_determinate` の条件明示版)。 -/
theorem th_26_fn2_F4_printed_explicit {p p' q q' w w' A A' : ℝ}
    (hpq : p + q = 1) (hpq' : p' + q' = 1) (hww : w = w')
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hp'1 : p' ≤ 1) (hA' : 0 < A')
    (hE : p * A = p' * A') (hw0 : 0 < w) (hqq : q' < q) :
    c p w * A < c p' w' * A' :=
  th_26_fn2_F2_explicit (p := p') (p' := p) (q := q') (q' := q) (w := w') (w' := w) (A := A') (A' := A)
    hpq' hpq hww.symm hp0 hp'1 hp1 hA' hE.symm (by rw [← hww]; exact hw0) hqq

/-- **ch26-002 (E = pA を前提として明示)**: E = pA, p + q = 1 のとき R = p(A − E) = p(1 − p)A = pqA = qE。
phase8a `risk_identities` は E を pA に、q を 1 − p に置換した形で述べていた。ここでは E, q を自由な量とし、
印刷の関係 E = pA (数学的期待) と p + q = 1 を前提 hE, hpq として置く。 -/
theorem th_26_risk_identities_explicit {p q A E : ℝ} (hE : E = p * A) (hpq : p + q = 1) :
    p * (A - E) = p * (1 - p) * A ∧ p * (1 - p) * A = p * q * A ∧ p * q * A = q * E := by
  have hq : q = 1 - p := by linarith
  subst hE; subst hq
  refine ⟨by ring, by ring, by ring⟩

/-! ## B′. 前提の必要性 (落とすと結論が崩れる) -/

/-- th_26_c_endpoint_zero_p から p = 0 を落とすと崩れる: p = 1, w = 1 で c = 1 ≠ 0。 -/
theorem th_26_c_endpoint_zero_p_needs_p : ∃ p w : ℝ, c p w ≠ 0 :=
  ⟨1, 1, by unfold c; norm_num⟩

/-- th_26_c_endpoint_zero_w から w = 0 を落とすと崩れる: p = 1, w = 1 で c = 1 ≠ 0。 -/
theorem th_26_c_endpoint_zero_w_needs_w : ∃ p w : ℝ, c p w ≠ 0 :=
  ⟨1, 1, by unfold c; norm_num⟩

/-- th_26_risk_identities_explicit から E = pA を落とすと崩れる: p = q = 1/2, A = 2, E = 0 で
p(A − E) = 1 ≠ 1/2 = p(1 − p)A。 -/
theorem th_26_risk_identities_needs_hE :
    ∃ p q A E : ℝ, p + q = 1 ∧ p * (A - E) ≠ p * (1 - p) * A :=
  ⟨1/2, 1/2, 2, 0, by norm_num, by norm_num⟩

/-- th_26_fn2_F2_explicit から w = w′ を落とすと崩れる: 他の前提 (p + q = 1, p′ + q′ = 1, pA = p′A′, q < q′,
0 < p′ ≤ 1, 0 < A, 0 < w) をすべて満たす p = 1, p′ = 1/2, A = 1, A′ = 2, w = 1/10, w′ = 1 (w ≠ w′) で
c′A′ = 2/3 ≥ cA = 2/11 となり、cA > c′A′ が成り立たない。 -/
theorem th_26_fn2_F2_needs_ww :
    ∃ p p' q q' w w' A A' : ℝ,
      p + q = 1 ∧ p' + q' = 1 ∧ 0 < p' ∧ p ≤ 1 ∧ p' ≤ 1 ∧ 0 < A ∧ p * A = p' * A' ∧ 0 < w ∧ q < q' ∧
      ¬ (c p' w' * A' < c p w * A) :=
  ⟨1, 1/2, 0, 1/2, 1/10, 1, 1, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by unfold c; norm_num⟩

/-- th_26_fn2_F4_printed_explicit から w = w′ を落とすと崩れる: 他の前提をすべて満たす
p = 1/2, p′ = 1, A = 2, A′ = 1, w = 1, w′ = 1/10 (w ≠ w′) で cA = 2/3 ≥ c′A′ = 2/11 となり、
cA < c′A′ が成り立たない。 -/
theorem th_26_fn2_F4_needs_ww :
    ∃ p p' q q' w w' A A' : ℝ,
      p + q = 1 ∧ p' + q' = 1 ∧ 0 < p ∧ p ≤ 1 ∧ p' ≤ 1 ∧ 0 < A' ∧ p * A = p' * A' ∧ 0 < w ∧ q' < q ∧
      ¬ (c p w * A < c p' w' * A') :=
  ⟨1/2, 1, 1/2, 0, 1, 1/10, 2, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by unfold c; norm_num⟩

/-- th_26_c_endpoint_one から w = 1 を落とすと崩れる: c 1 2 = 4/3 ≠ 1。 -/
theorem th_26_c_endpoint_one_needs_w : c 1 2 ≠ 1 := by unfold c; norm_num

/-- th_26_c_endpoint_one から p = 1 を落とすと崩れる: c (1/2) 1 = 1/3 ≠ 1。 -/
theorem th_26_c_endpoint_one_needs_p : c (1/2) 1 ≠ 1 := by unfold c; norm_num

/-- th_26_fn2_F1_explicit から q = q′ を落とすと崩れる: p = 1/2, p′ = 3/4 (q = 1/2 ≠ q′ = 1/4)、
A = 2, A′ = 4/3 (pA = p′A′ = 1)、w = 1 > w′ = 9/10 でも cA > c′A′ とは限らない。 -/
theorem th_26_fn2_F1_needs_qq : ¬ (c (3/4) (9/10) * (4/3) < c (1/2) 1 * 2) := by
  unfold c; norm_num

/-! ## C. folio 317 §9 — y = k log x/a は dy = k dx/x の積分 (ch26-034) -/

/-- **ch26-034 (積分形)**: y(x) = ∫ₐˣ k dt/t = k log(x/a) (y(a) = 0)。 -/
theorem th_26_bernoulli_integral (k a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    ∫ t in a..x, k / t = k * Real.log (x / a) := by
  have h : (fun t : ℝ => k / t) = fun t => k * t⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [h, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hx]

/-- **ch26-034 (微分方程式形)**: dy = k dx/x (x > 0) かつ y(a) = 0 なら y = k log(x/a)。
phase8a2 `th_26_bernoulli_deriv` の逆向き (y を一般の関数としてよい)。 -/
theorem th_26_bernoulli_ode_unique (k a : ℝ) (ha : 0 < a) (y : ℝ → ℝ)
    (hy : ∀ t, 0 < t → HasDerivAt y (k / t) t) (h0 : y a = 0) :
    ∀ x, 0 < x → y x = k * Real.log (x / a) := by
  have hg : ∀ t, 0 < t → HasDerivAt (fun x => k * Real.log (x / a)) (k / t) t := by
    intro t ht
    have h1 : HasDerivAt (fun x : ℝ => x / a) (1 / a) t := (hasDerivAt_id t).div_const a
    have h2 := (h1.log (by positivity)).const_mul k
    convert h2 using 1
    field_simp
  have hdy : DifferentiableOn ℝ y (Set.Ioi 0) := fun t ht => (hy t ht).differentiableAt.differentiableWithinAt
  have hdg : DifferentiableOn ℝ (fun x => k * Real.log (x / a)) (Set.Ioi 0) :=
    fun t ht => (hg t ht).differentiableAt.differentiableWithinAt
  have heq : (Set.Ioi (0:ℝ)).EqOn (deriv y) (deriv (fun x => k * Real.log (x / a))) := by
    intro t ht
    rw [(hy t ht).deriv, (hg t ht).deriv]
  have hon := isOpen_Ioi.eqOn_of_deriv_eq (isPreconnected_Ioi) hdy hdg heq (x := a) ha
    (by rw [h0, div_self ha.ne', Real.log_one, mul_zero])
  intro x hx
  exact hon hx

/-! ## D. folio 318 — x の道徳的財産が期待のそれに等しい ⟹ x = Π(a + x_i)^{p_i} (ch26-035) -/

/-- **ch26-035 (指数形)**: x を「現在の所有が増分 x_i の期待と同じ道徳的財産 k log(x/a) を与える物理的財産」
とすると、x = Π (a + x_i)^{p_i} (Σ p_i = 1, k ≠ 0)。印刷は指数 p_i がベースラインに組まれている
(phase8a2/th_26_laplace_printed_refuted)。 -/
theorem th_26_moral_fortune_eq {ι : Type*} (s : Finset ι) (p x_ : ι → ℝ) (a x k : ℝ) (ha : 0 < a)
    (hxpos : 0 < x) (hk : k ≠ 0)
    (hx : ∀ i ∈ s, 0 < a + x_ i) (hp : ∑ i ∈ s, p i = 1)
    (hmoral : k * Real.log (x / a) = ∑ i ∈ s, p i * (k * Real.log ((a + x_ i) / a))) :
    x = ∏ i ∈ s, (a + x_ i) ^ (p i) := by
  have hprod : ∀ i ∈ s, (a + x_ i) ^ (p i) ≠ 0 :=
    fun i hi => (Real.rpow_pos_of_pos (hx i hi) _).ne'
  have hP : (∏ i ∈ s, (a + x_ i) ^ (p i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hprod
  have hPpos : 0 < ∏ i ∈ s, (a + x_ i) ^ (p i) :=
    Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hx i hi) _
  have h1 : ∀ i ∈ s, Real.log ((a + x_ i) ^ (p i)) = p i * Real.log (a + x_ i) :=
    fun i hi => Real.log_rpow (hx i hi) _
  have h2 : ∀ i ∈ s, p i * (k * Real.log ((a + x_ i) / a))
      = k * (p i * Real.log (a + x_ i)) - (k * Real.log a) * p i := by
    intro i hi
    rw [Real.log_div (hx i hi).ne' ha.ne']
    ring
  have hrhs : ∑ i ∈ s, p i * (k * Real.log ((a + x_ i) / a))
      = k * Real.log ((∏ i ∈ s, (a + x_ i) ^ (p i)) / a) := by
    rw [Real.log_div hP ha.ne', Real.log_prod hprod, Finset.sum_congr rfl h1,
      Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp]
    ring
  rw [hrhs] at hmoral
  have hlog : Real.log (x / a) = Real.log ((∏ i ∈ s, (a + x_ i) ^ (p i)) / a) :=
    mul_left_cancel₀ hk hmoral
  have hinj := Real.log_injOn_pos (Set.mem_Ioi.mpr (div_pos hxpos ha))
    (Set.mem_Ioi.mpr (div_pos hPpos ha)) hlog
  exact (div_left_inj' ha.ne').mp hinj

/-! ## E. folio 319 §10 — b = ∞ (ch26-040) -/

/-- **ch26-040**: 「b = ∞」を前提 hb (b_n → ∞) として置くと、b_n/(a + b_n) → 1
(phase8a2 `th_26_laurent_limit` は b → ∞ を filter `atTop` として述べる)。 -/
theorem th_26_laurent_infinite_b (a : ℝ) (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) :
    Tendsto (fun n => b n / (a + b n)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => a / (a + b n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ a hb)
  have h2 : Tendsto (fun n => 1 - a / (a + b n)) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h1
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [hb.eventually_gt_atTop 0, hb.eventually_gt_atTop (-a)] with n hn hn'
  have : a + b n ≠ 0 := by linarith
  field_simp
  ring

end KeynesCh26b

/-! ## 監査クエリ (Phase 8a-3) -/

#print axioms KeynesCh26b.th_26_c_endpoint_one
#print axioms KeynesCh26b.th_26_c_endpoint_zero_p
#print axioms KeynesCh26b.th_26_c_endpoint_zero_w
#print axioms KeynesCh26b.th_26_fn2_F1_explicit
#print axioms KeynesCh26b.th_26_fn2_F2_explicit
#print axioms KeynesCh26b.th_26_fn2_F4_printed_explicit
#print axioms KeynesCh26b.th_26_risk_identities_explicit
#print axioms KeynesCh26b.th_26_c_endpoint_zero_p_needs_p
#print axioms KeynesCh26b.th_26_c_endpoint_zero_w_needs_w
#print axioms KeynesCh26b.th_26_risk_identities_needs_hE
#print axioms KeynesCh26b.th_26_fn2_F2_needs_ww
#print axioms KeynesCh26b.th_26_fn2_F4_needs_ww
#print axioms KeynesCh26b.th_26_c_endpoint_one_needs_w
#print axioms KeynesCh26b.th_26_c_endpoint_one_needs_p
#print axioms KeynesCh26b.th_26_fn2_F1_needs_qq
#print axioms KeynesCh26b.th_26_bernoulli_integral
#print axioms KeynesCh26b.th_26_bernoulli_ode_unique
#print axioms KeynesCh26b.th_26_moral_fortune_eq
#print axioms KeynesCh26b.th_26_laurent_infinite_b
