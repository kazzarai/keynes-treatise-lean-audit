/- ============================================================
   PHASE 8b — 短期確率加重関数 W(p) = p / (p + H(p)) の解析層
   (2012年劣加法性予想の決着本体)

   出典アンカー:
   - W の初出: 村田晴紀 (2010) 東京学芸大学2009年度修士論文
     (高籔・新井 2012 紀要63 脚注9 が初出と明記)
   - 式(3): 高籔・新井 (2012) 東京学芸大学紀要 人文社会科学系II 63集
     W(p) = p/(p+H), H = −(p log p + q log q), q = 1−p
   - 劣加法性予想 (C2): 同紀要 pp.264-265 (「Wは劣加法性を満たしそう」)
   - 逆S字・小確率過大視: 同紀要 図10 / 村田 (2012) ケインズ学会報告 図5

   本ファイルの決着 (WEIGHT_DESIGN §3 T9-T13):
   - T9  : W(0)=0, W(1)=1, 値域
   - T10 : ★大域劣加法性の反証★ — W(1) > W(½)+W(½)。核は ln 2 > 1/2
   - T11 : 【設計訂正 2026-08-01】 subcertainty W(p)+W(1−p)<1 は
           大域では成立しない。sum<1 ⟺ pq<H² であり、
           中央 (p=1/2) では成立、端 (p=1/100) では逆向き (sum>1)。
           → subcert_at_half + supercert_at_edge の対で機械決着
   - T12 : ★領域限定劣加法性★ — p₁+p₂ ≤ e/(1+e) ⟹ 劣加法。
           微分不使用: log x ≤ x−1 (Real.log_le_sub_one_of_pos) だけから
           接線不等式 → D(p)=p+H(p) の星形域単調性 → 劣加法
   - T13 : 小確率過大視 W(1/100) > 1/100 + 中央過小視 W(1/2) < 1/2
           (逆S字の両翼 = 村田図5・紀要図10の機械認定)

   方針: Mathlib解析は Real.log の初等補題のみ。導関数・積分は使わない。
   ============================================================ -/

import Mathlib

noncomputable section
namespace KeynesWeightW

open Real

/-- 二値エントロピー H(p) = −(p log p + (1−p) log (1−p))。
    log 0 = 0 の Mathlib 規約により H(0) = H(1) = 0 が定義から従う。 -/
def H (p : ℝ) : ℝ := -(p * Real.log p + (1 - p) * Real.log (1 - p))

/-- 分母 D(p) = p + H(p)。紀要の「確率とエントロピーの和」。 -/
def D (p : ℝ) : ℝ := p + H p

/-- 短期確率加重関数 W(p) = p / (p + H(p))。式(3)。 -/
def W (p : ℝ) : ℝ := p / D p

/- ---------- 基本補題 ---------- -/

lemma H_symm (p : ℝ) : H (1 - p) = H p := by
  unfold H
  rw [sub_sub_cancel]
  ring

lemma H_zero : H 0 = 0 := by simp [H]

lemma H_one : H 1 = 0 := by simp [H]

lemma H_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < H p := by
  have h1 : Real.log p < 0 := Real.log_neg hp hp1
  have h2 : Real.log (1 - p) < 0 := Real.log_neg (by linarith) (by linarith)
  have m1 : p * Real.log p < 0 := mul_neg_of_pos_of_neg hp h1
  have m2 : (1 - p) * Real.log (1 - p) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) h2
  unfold H
  nlinarith

lemma D_pos {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : 0 < D p := by
  rcases lt_or_eq_of_le hp1 with h | h
  · have := H_pos hp h
    unfold D
    linarith
  · subst h
    unfold D
    rw [H_one]
    norm_num

/- ---------- T9: 境界と値域 ---------- -/

theorem W_zero : W 0 = 0 := by simp [W, D, H_zero]

theorem W_one : W 1 = 1 := by simp [W, D, H_one]

theorem W_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ W p := by
  rcases eq_or_lt_of_le hp with h | h
  · simp [W, ← h]
  · exact div_nonneg hp (D_pos h hp1).le

theorem W_lt_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : W p < 1 := by
  have hH := H_pos hp hp1
  have hD := D_pos hp hp1.le
  rw [W, div_lt_one hD]
  unfold D
  linarith

/- ---------- 中央の値: H(1/2) = log 2 ---------- -/

lemma H_half : H (1 / 2) = Real.log 2 := by
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  unfold H
  rw [h12, hlog]
  ring

lemma log_two_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

/-- 逆S字の右翼: 中央での過小視 W(1/2) < 1/2 (紀要図10・村田図5の中央部)。 -/
theorem underweight_at_half : W (1 / 2) < 1 / 2 := by
  have hD1 : (1 : ℝ) < D (1 / 2) := by
    unfold D
    rw [H_half]
    linarith [log_two_gt_half]
  have hDpos : (0 : ℝ) < D (1 / 2) := by linarith
  rw [W, div_lt_iff₀ hDpos]
  nlinarith

/- ---------- T10: 2012年大域劣加法性予想の反証 ---------- -/

/-- ★ 反証の核: p₁ = p₂ = 1/2 で劣加法性が破れる。
    W(1) = 1 > W(1/2) + W(1/2)。核となる解析事実は ln 2 > 1/2 のみ。 -/
theorem subadd_fails_at_half : W (1 / 2) + W (1 / 2) < W (1 / 2 + 1 / 2) := by
  have h : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  rw [h, W_one]
  have := underweight_at_half
  linarith

/-- ★ 2012年予想 (C2) の大域形の機械反証 (存在文)。 -/
theorem conj2012_global_refuted :
    ∃ p₁ p₂ : ℝ, 0 < p₁ ∧ 0 < p₂ ∧ p₁ + p₂ ≤ 1 ∧
      W p₁ + W p₂ < W (p₁ + p₂) :=
  ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, subadd_fails_at_half⟩

/- ---------- 接線不等式 (微分不使用の核) ----------
   t ↦ t log t の接線評価を log x ≤ x − 1 だけから導く。 -/

/-- 下からの接線評価: 0 < u ≤ v ⟹ (v−u)(1 + log u) ≤ v log v − u log u。 -/
lemma mul_log_lower {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    (v - u) * (1 + Real.log u) ≤ v * Real.log v - u * Real.log u := by
  have h1 : Real.log (u / v) ≤ u / v - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hu hv)
  have h2 : Real.log (u / v) = Real.log u - Real.log v :=
    Real.log_div hu.ne' hv.ne'
  rw [h2] at h1
  -- v·(log v − log u) ≥ v − u
  have h4 : v * (Real.log u - Real.log v) ≤ v * (u / v - 1) :=
    mul_le_mul_of_nonneg_left h1 hv.le
  have h5 : v * (u / v - 1) = u - v := by field_simp
  nlinarith [h4]

/-- 上からの接線評価: 0 < u ≤ v ⟹ v log v − u log u ≤ (v−u)(1 + log v)。 -/
lemma mul_log_upper {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    v * Real.log v - u * Real.log u ≤ (v - u) * (1 + Real.log v) := by
  have h1 : Real.log (v / u) ≤ v / u - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hv hu)
  have h2 : Real.log (v / u) = Real.log v - Real.log u :=
    Real.log_div hv.ne' hu.ne'
  rw [h2] at h1
  -- u·(log v − log u) ≤ v − u
  have h4 : u * (Real.log v - Real.log u) ≤ u * (v / u - 1) :=
    mul_le_mul_of_nonneg_left h1 hu.le
  have h5 : u * (v / u - 1) = v - u := by field_simp
  nlinarith [h4]

/- ---------- T12: 星形域での D の単調性 → 領域限定劣加法性 ---------- -/

/-- D(p) = p + H(p) は 0 < x ≤ y、y(1+e) ≤ e (⟺ y ≤ e/(1+e)) の範囲で単調。
    接線評価2本と log((1−y)/y) ≥ −1 だけで閉じる (微分不使用)。 -/
lemma D_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy1 : y < 1)
    (hreg : y * (1 + Real.exp 1) ≤ Real.exp 1) : D x ≤ D y := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
  have hqx : 0 < 1 - x := by linarith
  have hqy : 0 < 1 - y := by linarith
  have hqq : 1 - y ≤ 1 - x := by linarith
  -- A: y log y − x log x ≤ (y−x)(1+log y)
  have hA := mul_log_upper hx hy0 hxy
  -- B: ((1−x)−(1−y))(1+log(1−y)) ≤ (1−x)log(1−x) − (1−y)log(1−y)
  have hB := mul_log_lower hqy hqx hqq
  -- 星形条件: 1 + log(1−y) − log y ≥ 0
  have hstar : (0 : ℝ) ≤ 1 + (Real.log (1 - y) - Real.log y) := by
    have hq : (0 : ℝ) < (1 - y) / y := div_pos hqy hy0
    have hexp : Real.exp (-1) ≤ (1 - y) / y := by
      rw [Real.exp_neg, le_div_iff₀ hy0]
      have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have hinv : Real.exp 1 * (Real.exp 1)⁻¹ = 1 :=
        mul_inv_cancel₀ he.ne'
      nlinarith [mul_le_mul_of_nonneg_left hreg (inv_nonneg.mpr he.le)]
    have hlog := (Real.le_log_iff_exp_le hq).mpr hexp
    have hsplit : Real.log ((1 - y) / y) = Real.log (1 - y) - Real.log y :=
      Real.log_div hqy.ne' hy0.ne'
    rw [hsplit] at hlog
    linarith
  have hprod : (0 : ℝ) ≤ (y - x) * (1 + (Real.log (1 - y) - Real.log y)) :=
    mul_nonneg (by linarith) hstar
  unfold D H
  nlinarith [hA, hB, hprod]

/-- ★ T12: 領域限定劣加法性 (2012年予想の生き残り部分)。
    仮定 (p₁+p₂)(1+e) ≤ e は p₁+p₂ ≤ e/(1+e) ≈ 0.731 の除算なし形。 -/
theorem subadd_small_prob {p₁ p₂ : ℝ} (h₁ : 0 < p₁) (h₂ : 0 < p₂)
    (hreg : (p₁ + p₂) * (1 + Real.exp 1) ≤ Real.exp 1) :
    W (p₁ + p₂) ≤ W p₁ + W p₂ := by
  have hs0 : 0 < p₁ + p₂ := by linarith
  have hs1 : p₁ + p₂ < 1 := by
    nlinarith [Real.exp_pos 1, hreg, hs0]
  have hD1 : D p₁ ≤ D (p₁ + p₂) := D_mono h₁ (by linarith) hs1 hreg
  have hD2 : D p₂ ≤ D (p₁ + p₂) := D_mono h₂ (by linarith) hs1 hreg
  have hDp1 : 0 < D p₁ := D_pos h₁ (by linarith)
  have hDp2 : 0 < D p₂ := D_pos h₂ (by linarith)
  have hDs : 0 < D (p₁ + p₂) := lt_of_lt_of_le hDp1 hD1
  have g1 : p₁ / D (p₁ + p₂) ≤ p₁ / D p₁ := by
    rw [div_le_div_iff₀ hDs hDp1]
    exact mul_le_mul_of_nonneg_left hD1 h₁.le
  have g2 : p₂ / D (p₁ + p₂) ≤ p₂ / D p₂ := by
    rw [div_le_div_iff₀ hDs hDp2]
    exact mul_le_mul_of_nonneg_left hD2 h₂.le
  have expand : W (p₁ + p₂) = p₁ / D (p₁ + p₂) + p₂ / D (p₁ + p₂) := by
    rw [W, add_div]
  rw [expand]
  have w1 : W p₁ = p₁ / D p₁ := rfl
  have w2 : W p₂ = p₂ / D p₂ := rfl
  rw [w1, w2]
  linarith [g1, g2]

/-- T12の数値系: p₁+p₂ ≤ 0.73 なら劣加法 (e > 2.7182818283 を使用)。 -/
theorem subadd_up_to_073 {p₁ p₂ : ℝ} (h₁ : 0 < p₁) (h₂ : 0 < p₂)
    (hs : p₁ + p₂ ≤ 73 / 100) : W (p₁ + p₂) ≤ W p₁ + W p₂ := by
  apply subadd_small_prob h₁ h₂
  have he := Real.exp_one_gt_d9
  nlinarith [he, hs, mul_le_mul_of_nonneg_right hs (Real.exp_pos 1).le]

/- ---------- T11: subcertainty の二面決着 ---------- -/

/-- 中央での subcertainty (K–T の subcertainty が成り立つ側)。 -/
theorem subcert_at_half : W (1 / 2) + W (1 / 2) < 1 := by
  have := underweight_at_half
  linarith

/- 端の数値評価に使う log の上界。log 100 = 6 log 2 + log(25/16)。 -/
lemma log_hundred_lt : Real.log 100 < 4.7214 := by
  have h64 : (100 : ℝ) = 2 ^ 6 * (25 / 16) := by norm_num
  rw [h64, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  have h2 := Real.log_two_lt_d9
  have h25 : Real.log ((25 : ℝ) / 16) ≤ 25 / 16 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  push_cast
  nlinarith

lemma H_hundredth_pos : 0 < H (1 / 100) :=
  H_pos (by norm_num) (by norm_num)

/-- H(1/100) < 3/50 = 0.06 (実値 ≈ 0.0560)。 -/
lemma H_hundredth_lt : H (1 / 100) < 3 / 50 := by
  have hq : (1 : ℝ) - 1 / 100 = 99 / 100 := by norm_num
  have hl1 : Real.log ((1 : ℝ) / 100) = -Real.log 100 := by
    rw [one_div, Real.log_inv]
  have hl2 : Real.log ((99 : ℝ) / 100) = -Real.log ((100 : ℝ) / 99) := by
    have h : ((99 : ℝ) / 100) = ((100 : ℝ) / 99)⁻¹ := by norm_num
    rw [h, Real.log_inv]
  have hb1 := log_hundred_lt
  have hb2 : Real.log ((100 : ℝ) / 99) ≤ 100 / 99 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have hb3 : (0 : ℝ) < Real.log ((100 : ℝ) / 99) :=
    Real.log_pos (by norm_num)
  unfold H
  rw [hq, hl1, hl2]
  nlinarith [hb1, hb2, hb3]

/-- ★ 端での supercertainty: W(1/100) + W(99/100) > 1。
    subcertainty は大域では成立しない (設計訂正の機械証明)。
    核: sum > 1 ⟺ pq > H²、ここで pq = 99/10000 > (3/50)² > H²。 -/
theorem supercert_at_edge : 1 < W (1 / 100) + W (99 / 100) := by
  have hsym : H (99 / 100) = H (1 / 100) := by
    have h := H_symm (1 / 100)
    rwa [show (1 : ℝ) - 1 / 100 = 99 / 100 by norm_num] at h
  have hH := H_hundredth_lt
  have hHp := H_hundredth_pos
  have hd1 : 0 < D (1 / 100) := by
    unfold D
    nlinarith
  have hd2 : 0 < D (99 / 100) := by
    unfold D
    rw [hsym]
    nlinarith
  have w1 : W (1 / 100) = (1 / 100) / D (1 / 100) := rfl
  have w2 : W (99 / 100) = (99 / 100) / D (99 / 100) := rfl
  rw [w1, w2, div_add_div _ _ hd1.ne' hd2.ne', lt_div_iff₀ (mul_pos hd1 hd2)]
  unfold D
  rw [hsym]
  nlinarith [hH, hHp, mul_lt_mul_of_pos_left hH hHp]

/- ---------- T13: 逆S字の左翼 — 小確率の過大視 ---------- -/

/-- W(1/100) > 1/100 (小確率過大視)。核: D(1/100) < 1。 -/
theorem overweight_at_edge : (1 : ℝ) / 100 < W (1 / 100) := by
  have hH := H_hundredth_lt
  have hHp := H_hundredth_pos
  have hd : 0 < D (1 / 100) := by
    unfold D
    nlinarith
  have hD1 : D (1 / 100) < 1 := by
    unfold D
    nlinarith
  rw [W, lt_div_iff₀ hd]
  nlinarith

/-- ★ 逆S字の機械認定 (両翼): 小確率で過大視・中央で過小視。
    紀要 (2012) 図10 と村田 (2012) 図5 の定性的主張の定理化。 -/
theorem inverse_S_certified :
    (1 : ℝ) / 100 < W (1 / 100) ∧ W (1 / 2) < 1 / 2 :=
  ⟨overweight_at_edge, underweight_at_half⟩

/- ---------- 補強1: 内点反例 (確実性到達を避けた破れ) ----------
   反例 p₁=p₂=1/2 は和がちょうど1。「内部に限る」読みへの応答として
   p₁=p₂=499/1000 (和 998/1000 < 1) でも破れることを機械化する。
   鍵: 2·(499/1000) = 499/500 なので、不等式は D(499/500) < D(499/1000)
   に帰着する。必要なのは H の2点評価だけ。 -/

/-- log 500 ≤ 9 log 2 (500 = 2⁹·(125/128)、第2因子は1以下)。 -/
lemma log_500_le : Real.log 500 ≤ 9 * Real.log 2 := by
  have h500 : (500 : ℝ) = 2 ^ 9 * (125 / 128) := by norm_num
  rw [h500, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  have hn : Real.log ((125 : ℝ) / 128) ≤ 0 :=
    Real.log_nonpos (by norm_num) (by norm_num)
  push_cast
  linarith

/-- H(499/500) < 3/200 (実値 ≈ 0.01448)。 -/
lemma H_0998_ub : H (499 / 500) < 3 / 200 := by
  have e1 : Real.log ((499 : ℝ) / 500) = -Real.log (500 / 499) := by
    rw [show ((499 : ℝ) / 500) = ((500 : ℝ) / 499)⁻¹ by norm_num, Real.log_inv]
  have e2 : Real.log ((1 : ℝ) / 500) = -Real.log 500 := by
    rw [one_div, Real.log_inv]
  have b1 : Real.log ((500 : ℝ) / 499) ≤ 1 / 499 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500 / 499 by norm_num)
    norm_num at h ⊢
    linarith
  have b2 := log_500_le
  have b3 : (0 : ℝ) ≤ Real.log (500 / 499) :=
    Real.log_nonneg (by norm_num)
  have b4 := Real.log_two_lt_d9
  unfold H
  rw [show (1 : ℝ) - 499 / 500 = 1 / 500 by norm_num, e1, e2]
  nlinarith [b1, b2, b3, b4]

/-- H(499/1000) > 173/250 = 0.692 (実値 ≈ 0.69315)。 -/
lemma H_0499_lb : (173 : ℝ) / 250 < H (499 / 1000) := by
  have e1 : Real.log ((499 : ℝ) / 1000) = -Real.log (1000 / 499) := by
    rw [show ((499 : ℝ) / 1000) = ((1000 : ℝ) / 499)⁻¹ by norm_num, Real.log_inv]
  have e2 : Real.log ((501 : ℝ) / 1000) = -Real.log (1000 / 501) := by
    rw [show ((501 : ℝ) / 1000) = ((1000 : ℝ) / 501)⁻¹ by norm_num, Real.log_inv]
  have d1 : Real.log ((1000 : ℝ) / 499) = Real.log 2 + Real.log (500 / 499) := by
    rw [show ((1000 : ℝ) / 499) = 2 * (500 / 499) by norm_num,
      Real.log_mul two_ne_zero (by norm_num)]
  have d2 : Real.log ((1000 : ℝ) / 501) = Real.log 2 + Real.log (500 / 501) := by
    rw [show ((1000 : ℝ) / 501) = 2 * (500 / 501) by norm_num,
      Real.log_mul two_ne_zero (by norm_num)]
  have g1 : (0 : ℝ) ≤ Real.log (500 / 499) := Real.log_nonneg (by norm_num)
  have g2 : Real.log ((501 : ℝ) / 500) ≤ 1 / 500 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 501 / 500 by norm_num)
    norm_num at h ⊢
    linarith
  have g2' : -(1 / 500 : ℝ) ≤ Real.log (500 / 501) := by
    rw [show ((500 : ℝ) / 501) = ((501 : ℝ) / 500)⁻¹ by norm_num, Real.log_inv]
    linarith
  have gt2 := Real.log_two_gt_d9
  unfold H
  rw [show (1 : ℝ) - 499 / 1000 = 501 / 1000 by norm_num, e1, e2, d1, d2]
  nlinarith [g1, g2', gt2]

/-- ★ 内点反例: p₁ = p₂ = 499/1000 (和 = 499/500 < 1) でも劣加法性は破れる。 -/
theorem subadd_fails_interior :
    W (499 / 1000) + W (499 / 1000) < W (499 / 1000 + 499 / 1000) := by
  have hub := H_0998_ub
  have hlb := H_0499_lb
  have hd1 : 0 < D (499 / 1000) := D_pos (by norm_num) (by norm_num)
  have hd2 : 0 < D (499 / 500) := D_pos (by norm_num) (by norm_num)
  have key : D (499 / 500) < D (499 / 1000) := by
    unfold D
    nlinarith [hub, hlb]
  have w1 : W (499 / 1000) = (499 / 1000) / D (499 / 1000) := rfl
  have lhs : W (499 / 1000) + W (499 / 1000) = (499 / 500) / D (499 / 1000) := by
    rw [w1, ← add_div]
    norm_num
  have rhs : W (499 / 1000 + 499 / 1000) = (499 / 500) / D (499 / 500) := by
    rw [show (499 : ℝ) / 1000 + 499 / 1000 = 499 / 500 by norm_num]
    rfl
  rw [lhs, rhs, div_lt_div_iff₀ hd1 hd2]
  exact mul_lt_mul_of_pos_left key (by norm_num)

/- ---------- 補強2: 底2版 (村田 2012 の図の底) ----------
   紀要は対数の底を明示していない。核不等式は底 b で log_b 2 > 1/2
   ⟺ b < 4。よって底 e (本編) と底 2 (村田の図) は両方カバーされる。
   底2では H₂(1/2) = 1 となり対数評価すら不要 (1/3 + 1/3 < 1)。
   底 b ≥ 4 では中心対は反例にならず、大域成否は底依存で未決着。 -/

def H2 (p : ℝ) : ℝ := H p / Real.log 2

def D2 (p : ℝ) : ℝ := p + H2 p

def W2 (p : ℝ) : ℝ := p / D2 p

lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem W2_one : W2 1 = 1 := by
  simp [W2, D2, H2, H_one]

/-- ★ 底2でも中心対で破れる: W₂(½)+W₂(½) = 2/3 < 1 = W₂(1)。 -/
theorem base2_subadd_fails_at_half :
    W2 (1 / 2) + W2 (1 / 2) < W2 (1 / 2 + 1 / 2) := by
  have h2 : H2 (1 / 2) = 1 := by
    unfold H2
    rw [H_half]
    exact div_self (ne_of_gt log_two_pos)
  have hw : W2 (1 / 2) = 1 / 3 := by
    unfold W2 D2
    rw [h2]
    norm_num
  rw [show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, W2_one, hw]
  norm_num

/- ---------- 監査 (Phase 8b) ---------- -/

#check @W_zero
#check @conj2012_global_refuted
#check @subadd_small_prob

#print axioms KeynesWeightW.W_zero
#print axioms KeynesWeightW.W_one
#print axioms KeynesWeightW.W_lt_one
#print axioms KeynesWeightW.underweight_at_half
#print axioms KeynesWeightW.subadd_fails_at_half
#print axioms KeynesWeightW.conj2012_global_refuted
#print axioms KeynesWeightW.D_mono
#print axioms KeynesWeightW.subadd_small_prob
#print axioms KeynesWeightW.subadd_up_to_073
#print axioms KeynesWeightW.subcert_at_half
#print axioms KeynesWeightW.supercert_at_edge
#print axioms KeynesWeightW.overweight_at_edge
#print axioms KeynesWeightW.inverse_S_certified
#print axioms KeynesWeightW.subadd_fails_interior
#print axioms KeynesWeightW.W2_one
#print axioms KeynesWeightW.base2_subadd_fails_at_half

end KeynesWeightW
