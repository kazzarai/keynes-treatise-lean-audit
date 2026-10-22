/-
# Keynes (1921) *A Treatise on Probability* — Lean 4 Phase 8a-2

# 新井一成・Claude 共著、2026年10月18日 (第 2 回是正 2026年10月20日)
# **第26章 (The Application of Probability to Conduct) の全数台帳 — 8a 未検証行の検証**

## 原典アンカー (1921 Macmillan 初版、PDF 頁 = folio + 20)
  第26章は folio 307–323。記号式は folio 315 (§8: E, R, c, 脚注 1–2)、316–317 (§9: Petersburg)、
  318 (Bernoulli–Laplace の式、Cramer の二解)、319 (相対リスク R/E、Laurent の f(a))、322 (Buffon の 1/10,000)
  に限られる。台帳: `原典照合1921/台帳_ch26.md` (F26.1–F26.27)。
  folio 315 の係数 c・リスク R・Czuber 級数 (有限形)・脚注 F1–F4 は phase8a で検証済 (本ファイルはその続き)。

## 本ファイルの判定対象 (台帳番号 → 定理)
  F26.8   R₁ = qR = q²E                              th_26_fn1_second_order_risk (列 `czuberRisk` の第 1 項)
  F26.9   E+R₁+R₂+… = E(1+q+q²+…) = E/(1−q) = E/p = A  印刷どおり R₁ = q²E, R₂ = q³E, … と定義すると第 1 の等号は
                                                       qE = 0 のときしか成り立たない: th_26_fn1_printed_iff,
                                                       ℚ の証人 q = 1/2, E = 1 で 3/2 ≠ 2: th_26_fn1_printed_refuted。
                                                       整合形: R を含める th_26_fn1_consistent_R、添字を R₁ = qE と
                                                       読み替える th_26_fn1_consistent_reindexed。係数級数
                                                       E(1+q+…) = E/(1−q) = E/p = A 自体は th_26_fn1_czuber_tsum。
  F26.13  脚注 F4 (印刷どおり w=w′, q>q′ と修正案 w>w′) th_26_fn2_F4_printed_determinate / _amended_witness_lt / _gt
          (phase8a の keynes_F4_* と同一主張の再掲 — phase ファイルは相互に import しないため自前で証明)
  F26.14  (1/2)^{r−1}·(1/2) = (1/2)^r (最初の表が第 r 回) th_26_first_head (補助)
  F26.15  Σ_1^n (1/2)^r 2^{r−1} = n/2                  th_26_petersburg_term, th_26_petersburg_finite;
                                                       必要性 (r = 0 で項は 1): th_26_petersburg_term_r0
  F26.16  Σ_1^∞ (1/2)^r 2^{r−1} は「無限大」            th_26_petersburg_unbounded, th_26_petersburg_tendsto,
                                                       th_26_petersburg_not_summable
  F26.18  dy = k dx/x                                  th_26_bernoulli_deriv
  F26.19  y = k log(x/a)                               th_26_bernoulli_deriv, th_26_bernoulli_initial (補助)
  F26.20  x = (a+x₁)^{p₁}(a+x₂)^{p₂}⋯                   th_26_moral_expectation (指数形);
          印刷は指数が落ちて (a+x₁)p₁(a+x₂)p₂ と組まれている: th_26_laplace_printed_refuted (反例)
  F26.21  Bernoulli: 財産 £1000 で £6 の掛金            th_26_bernoulli_summable (対数効用で期待が有限),
                                                       th_26_bernoulli_stake_strict (s = 6 は払い過ぎ、s = 5.9 は不足),
                                                       th_26_bernoulli_stake_bounds (公平掛金 s* が存在し 5.9 < s* < 6、
                                                       かつ一意) — 印刷「£6」は s* ≈ 5.97 の丸め
  F26.22  Cramer: 2²⁴ 超を同価 → £13                   th_26_cramer_cap;  印刷 "(16,777,116)" は 2²⁴ ≠ 16,777,116
                                                       (th_26_printed_16777116_refuted; 正しくは 16,777,216)
  F26.23  Cramer: 効用 ∝ √(金額) → 印刷 "£2 : 9s."      th_26_cramer_sqrt_expectation, th_26_cramer_sqrt_stake:
                                                       掛金 = 3/2 + √2 ≈ £2 18s 3d; 印刷値 £2 9s は疑義
                                                       (th_26_cramer_sqrt_dubious — Paul の初期財産 0 という
                                                       印刷にない設定の下での結論)
  F26.24  R/E は「ほとんど 1」、R は「無限大」           th_26_relative_risk, th_26_relative_risk_tendsto (R/E → 1),
                                                       th_26_petersburg_risk_unbounded (解釈つき)
  F26.25  f(a) = b/(a+b): 貧しいほど破産しやすい         th_26_laurent_poorer
  F26.26  b = ∞ なら f(a) = 1                           th_26_laurent_limit
  (補)    folio 311 脚注 Leibniz の比例分割             th_26_fn_leibniz_division (補助)

## 形式化の境界の記録 (本ファイルで定理にしていないもの)
  * F26.21 の数値 "£6": 対数効用の公平掛金 s* は Σ_{r≥0} 2^{−(r+1)} log(1000 − s* + 2^r) = log 1000 の解。
    本ファイルは log の Taylor 評価 (`Real.abs_log_sub_add_sum_range_le`) と log 2 の 10 桁評価で
    5.9 < s* < 6 を定理にした (`th_26_bernoulli_stake_bounds`)。s* の小数展開 (≈ 5.968) 自体は述べていない。
  * F26.23 の反証は「Paul の初期財産を 0 とし、公平掛金 s を √s = Σ 2^{-r} √(2^{r−1}) で定める」という
    Cramer 自身の設定 (Keynes の文は財産を指定しない) の下での結論。Cramer の原文は「約 2.9」で、
    印刷の "£2 : 9s." は小数 2.9 を £2 9s と読み替えた可能性が高い (所見候補)。印刷にない設定を置いた
    判定なので「疑義」(S) に留め、反駁 (F) とはしない。
  * F26.24 の R/E: Keynes は R を単一の利得 A (確率 p) についてのみ定義している (folio 315)。
    多結果の賭けへの拡張は印刷にないので、本ファイルは「各結果 r に p_r(A_r − p_r A_r) を適用して足す」
    という読みを明示して定理にした (Czuber の Risiko の加法性と同型)。別の読みなら結論は変わり得る。
  * F26.25 の f(a) = b/(a+b) 自体 (公平な賭けの破産確率) は Laurent の結果の引用で、Keynes は導出していない。
    本ファイルも導出せず、その式から従う単調性と極限のみを定理にした。脚注 2 の「Laurent の推論は誤り」は
    形式化の対象外。
  * F26.27 Buffon の 1/10,000 は経験的定数の引用で、導出される主張ではない (対象外)。
  * F26.9 の反例は証人 q = 1/2, E = 1 (ℚ の値) を取り、級数は ℝ の tsum で評価した (ℚ は完備でなく、
    幾何級数の総和を ℚ 上で述べる補題が Mathlib にない)。

## 予測: 本ファイルの全定理は Lean の基底公理 (propext, Classical.choice, Quot.sound) のみに依存する。
   第26章の式は (55) や 8a と同じく実数層の算術であり、Keynes 固有の公理は要らない。
-/

import Mathlib

namespace KeynesCh26

open Finset Filter Topology

/-! ## A. folio 315 §8 — 脚注 1 の補完 (F26.8, F26.9) -/

/-- **F26.8** 脚注 1: 二次のリスク R₁ = qR = q²E (R = qE)。 -/
theorem th_26_fn1_second_order_risk (q E : ℝ) : q * (q * E) = q ^ 2 * E := by ring

/-- 脚注 1 の印刷どおりの再保険リスクの列: 第 0 項が R = qE (first insurance)、
R₁ = qR = q²E (Risiko of the second order)、以下 R_{k+1} = q R_k。 -/
noncomputable def czuberRisk (q E : ℝ) : ℕ → ℝ
  | 0 => q * E
  | k + 1 => q * czuberRisk q E k

theorem czuberRisk_closed (q E : ℝ) (k : ℕ) : czuberRisk q E k = q ^ (k + 1) * E := by
  induction k with
  | zero => simp [czuberRisk]
  | succ k ih => rw [czuberRisk, ih]; ring

/-- 印刷の定義との一致: czuberRisk q E 1 = qR = q²E (F26.8)。 -/
theorem czuberRisk_one (q E : ℝ) : czuberRisk q E 1 = q * (q * E) ∧ czuberRisk q E 1 = q ^ 2 * E :=
  ⟨by simp [czuberRisk], by rw [czuberRisk_closed]⟩

theorem tsum_czuberRisk_succ (q E : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' k : ℕ, czuberRisk q E (k + 1) = q ^ 2 * E * (1 - q)⁻¹ := by
  have : (fun k : ℕ => czuberRisk q E (k + 1)) = fun k => (q ^ 2 * E) * q ^ k := by
    funext k; rw [czuberRisk_closed]; ring
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

theorem tsum_czuberRisk (q E : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' k : ℕ, czuberRisk q E k = q * E * (1 - q)⁻¹ := by
  have : (fun k : ℕ => czuberRisk q E k) = fun k => (q * E) * q ^ k := by
    funext k; rw [czuberRisk_closed]; ring
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

/-- **F26.9 印刷形の判定** (folio 315 脚注 1、T 候補: 添字不整合)。印刷は R₁ = qR = q²E と定義した上で
E + R₁ + R₂ + … = E(1 + q + q² + …) と書く。この定義では左辺は E(1 + q² + q³ + …) であり、
印刷の第 1 の等号は qE = 0 のときに限って成り立つ (左辺は右辺より R = qE だけ小さい)。 -/
theorem th_26_fn1_printed_iff (q E : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    E + ∑' k : ℕ, czuberRisk q E (k + 1) = E * ∑' k : ℕ, q ^ k ↔ q * E = 0 := by
  rw [tsum_czuberRisk_succ q E hq0 hq1, tsum_geometric_of_lt_one hq0 hq1]
  have h1 : (1:ℝ) - q ≠ 0 := by linarith
  have key : E + q ^ 2 * E * (1 - q)⁻¹ - E * (1 - q)⁻¹ = -(q * E) := by
    field_simp
    ring
  constructor <;> intro h <;> linarith

/-- **F26.9 印刷形の反例** (ℚ の証人 q = 1/2, E = 1): E + R₁ + R₂ + … = 1 + 1/4 + 1/8 + … = 3/2、
E(1 + q + q² + …) = 2、両者は等しくない。 -/
theorem th_26_fn1_printed_refuted :
    (1:ℝ) + ∑' k : ℕ, czuberRisk (1 / 2) 1 (k + 1) = 3 / 2 ∧
    (1:ℝ) * ∑' k : ℕ, ((1:ℝ) / 2) ^ k = 2 ∧
    (1:ℝ) + ∑' k : ℕ, czuberRisk (1 / 2) 1 (k + 1) ≠ (1:ℝ) * ∑' k : ℕ, ((1:ℝ) / 2) ^ k := by
  have h1 : (1:ℝ) + ∑' k : ℕ, czuberRisk (1 / 2) 1 (k + 1) = 3 / 2 := by
    rw [tsum_czuberRisk_succ _ _ (by norm_num) (by norm_num)]; norm_num
  have h2 : (1:ℝ) * ∑' k : ℕ, ((1:ℝ) / 2) ^ k = 2 := by rw [tsum_geometric_two]; ring
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

/-- **F26.9 整合形 (i)**: 一次のリスク R = qE を級数に含めれば E + R + R₁ + R₂ + … = E/(1 − q)。 -/
theorem th_26_fn1_consistent_R (q E : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    E + ∑' k : ℕ, czuberRisk q E k = E / (1 - q) := by
  rw [tsum_czuberRisk q E hq0 hq1]
  have h1 : (1:ℝ) - q ≠ 0 := by linarith
  field_simp
  ring

/-- **F26.9 整合形 (ii)**: 添字を R₁ = qE, R₂ = q²E, … と読み替えれば印刷の等式どおり
E + R₁ + R₂ + … = E(1 + q + q² + …) = E/(1 − q)。 -/
theorem th_26_fn1_consistent_reindexed (q E : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    E + ∑' k : ℕ, q ^ (k + 1) * E = E * ∑' k : ℕ, q ^ k ∧ E * ∑' k : ℕ, q ^ k = E / (1 - q) := by
  have : (fun k : ℕ => q ^ (k + 1) * E) = fun k => (q * E) * q ^ k := by funext k; ring
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have h1 : (1:ℝ) - q ≠ 0 := by linarith
  constructor
  · field_simp
    ring
  · rw [div_eq_mul_inv]

/-- **F26.9 係数級数**: E(1+q+q²+…) = E/(1−q) = E/p = A、E = pA、q = 1−p、0 < p ≤ 1。
phase8a は有限閉形式 `czuber_partial` と残差 `czuber_remainder` で述べた。ここでは無限和。
(印刷の左辺 E+R₁+R₂+… との不整合は `th_26_fn1_printed_iff` 参照。) -/
theorem th_26_fn1_czuber_tsum (p A : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (p * A) * ∑' k : ℕ, (1 - p) ^ k = (p * A) / (1 - (1 - p)) ∧
    (p * A) / (1 - (1 - p)) = (p * A) / p ∧ (p * A) / p = A := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tsum_geometric_of_lt_one (by linarith) (by linarith), div_eq_mul_inv]
  · rw [show (1:ℝ) - (1 - p) = p by ring]
  · field_simp

/-! ## B. folio 315 脚注 2 — F4 の両形 (F26.13; phase8a の再掲) -/

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

/-- 脚注 2 第 2 節 (F2): pA = p′A′、w = w′、q < q′ (p′ < p) ⟹ cA > c′A′ (phase8a `keynes_F2`)。 -/
theorem th_26_fn2_F2 {p p' w A A' : ℝ}
    (hp'0 : 0 < p') (hp1 : p ≤ 1) (hp'1 : p' ≤ 1) (hA : 0 < A)
    (hE : p * A = p' * A') (hw0 : 0 < w) (hpp : p' < p) :
    c p' w * A' < c p w * A := by
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

/-- **F26.13 印刷どおり** (w = w′、q > q′ すなわち p < p′): 「一般に比較できない」と印刷されているが、
F2 の記号交換そのもので cA < c′A′ が確定する (phase8a `keynes_F4_printed_determinate` の再掲)。 -/
theorem th_26_fn2_F4_printed_determinate {p p' w A A' : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hp'1 : p' ≤ 1) (hA' : 0 < A')
    (hE : p * A = p' * A') (hw0 : 0 < w) (hpp : p < p') :
    c p w * A < c p' w * A' :=
  th_26_fn2_F2 hp0 hp'1 hp1 hA' hE.symm hw0 hpp

/-- **F26.13 修正案** (w > w′、q > q′): 真に非比較 — 証人 A (w′ = 9/10) では cA < c′A′。 -/
theorem th_26_fn2_F4_amended_witness_lt : c (1/2) 1 * 2 < c (3/4) (9/10) * (4/3) := by
  unfold c; norm_num

/-- **F26.13 修正案** 証人 B (w′ = 1/100) では cA > c′A′。同じ符号条件で逆順 — 非比較性の機械的証明。 -/
theorem th_26_fn2_F4_amended_witness_gt : c (3/4) (1/100) * (4/3) < c (1/2) 1 * 2 := by
  unfold c; norm_num

/-! ## C. folio 316–317 §9 — Petersburg の賭け (F26.14–F26.17) -/

/-- **F26.14** の確率模型 (補助): 公平な硬貨の独立投げで、最初の表が第 r 回に出る確率は
(1/2)^{r−1}·(1/2) = (1/2)^r (Part II 乗法定理の数値形)。印刷の式ではなく、F26.15 の係数を支える補助定理。 -/
theorem th_26_first_head (r : ℕ) (hr : 1 ≤ r) : ((1:ℝ) / 2) ^ (r - 1) * (1 / 2) = (1 / 2) ^ r := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]

/-- **F26.15 の各項**: (1/2)^r·2^{r−1} = 1/2 (r ≥ 1)。 -/
theorem th_26_petersburg_term (r : ℕ) (hr : 1 ≤ r) : ((1:ℝ) / 2) ^ r * 2 ^ (r - 1) = 1 / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, mul_right_comm, ← mul_pow]
  norm_num

/-- **必要性 (F26.15)**: `th_26_petersburg_term` の仮定 1 ≤ r は落とせない。r = 0 では ℕ の減算で
0 − 1 = 0 となり、左辺は (1/2)^0·2^0 = 1 であって 1/2 ではない。 -/
theorem th_26_petersburg_term_r0 :
    ((1:ℝ) / 2) ^ 0 * 2 ^ (0 - 1) = 1 ∧ ((1:ℝ) / 2) ^ 0 * 2 ^ (0 - 1) ≠ 1 / 2 := by norm_num

/-- **F26.15 / F26.17**: Σ_{r=1}^{n} (1/2)^r 2^{r−1} = n/2 — 「Paul は n/2 シリングを払うべき」。 -/
theorem th_26_petersburg_finite (n : ℕ) :
    ∑ r ∈ Icc 1 n, ((1:ℝ) / 2) ^ r * 2 ^ (r - 1) = n / 2 := by
  rw [Finset.sum_congr rfl (fun r hr => th_26_petersburg_term r (Finset.mem_Icc.mp hr).1)]
  simp [Finset.sum_const, Nat.card_Icc]
  ring

/-- **F26.16 / F26.17**: 制限を外すと「無限の和」— 部分和はどの実数も超える。 -/
theorem th_26_petersburg_unbounded :
    ∀ M : ℝ, ∃ n : ℕ, M < ∑ r ∈ Icc 1 n, ((1:ℝ) / 2) ^ r * 2 ^ (r - 1) := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M)
  exact ⟨n, by rw [th_26_petersburg_finite]; linarith⟩

/-- **F26.16** 同、極限の形: 部分和 → +∞。 -/
theorem th_26_petersburg_tendsto :
    Tendsto (fun n : ℕ => ∑ r ∈ Icc 1 n, ((1:ℝ) / 2) ^ r * 2 ^ (r - 1)) atTop atTop := by
  simp_rw [th_26_petersburg_finite]
  exact tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)

/-- **F26.16** 同、総和不能の形: 項が 1/2 に留まり 0 に収束しない。 -/
theorem th_26_petersburg_not_summable :
    ¬ Summable (fun r : ℕ => ((1:ℝ) / 2) ^ (r + 1) * 2 ^ r) := by
  intro h
  have h0 := h.tendsto_atTop_zero
  have hfun : (fun r : ℕ => ((1:ℝ) / 2) ^ (r + 1) * 2 ^ r) = fun _ => (1:ℝ) / 2 := by
    funext r
    simpa using th_26_petersburg_term (r + 1) (by omega)
  rw [hfun] at h0
  have := tendsto_const_nhds_iff.mp h0
  norm_num at this

/-! ## D. folio 317 — Bernoulli の道徳的財産 (F26.18, F26.19) -/

/-- **F26.18 / F26.19**: y = k log(x/a) は dy = k dx/x を満たす (x > 0, a > 0)。 -/
theorem th_26_bernoulli_deriv (k a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (fun x => k * Real.log (x / a)) (k / x) x := by
  have h1 : HasDerivAt (fun x : ℝ => x / a) (1 / a) x := (hasDerivAt_id x).div_const a
  have h2 := (h1.log (by positivity)).const_mul k
  convert h2 using 1
  field_simp

/-- **F26.19** の積分定数 (補助): y = 0 となる x は a (「k, a は定数」の a の意味)。
印刷の式そのものではなく、F26.19 の定数 a の読みを支える補助定理。 -/
theorem th_26_bernoulli_initial (k a : ℝ) (ha : a ≠ 0) : k * Real.log (a / a) = 0 := by
  rw [div_self ha, Real.log_one, mul_zero]

/-! ## E. folio 318 — Bernoulli–Laplace の式 (F26.20) -/

/-- **F26.20 (指数形)**: 確率 p_i (Σp_i = 1) で増分 x_i を得る期待の道徳的価値は、
x = Π (a+x_i)^{p_i} を現に持つことの道徳的価値 k log(x/a) に等しい。 -/
theorem th_26_moral_expectation {ι : Type*} (s : Finset ι) (p x : ι → ℝ) (a k : ℝ) (ha : 0 < a)
    (hx : ∀ i ∈ s, 0 < a + x i) (hp : ∑ i ∈ s, p i = 1) :
    k * Real.log ((∏ i ∈ s, (a + x i) ^ (p i)) / a) =
      ∑ i ∈ s, p i * (k * Real.log ((a + x i) / a)) := by
  have hprod : ∀ i ∈ s, (a + x i) ^ (p i) ≠ 0 := fun i hi => (Real.rpow_pos_of_pos (hx i hi) _).ne'
  have hP : (∏ i ∈ s, (a + x i) ^ (p i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hprod
  rw [Real.log_div hP ha.ne', Real.log_prod hprod]
  have h1 : ∀ i ∈ s, Real.log ((a + x i) ^ (p i)) = p i * Real.log (a + x i) :=
    fun i hi => Real.log_rpow (hx i hi) _
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ i ∈ s, p i * (k * Real.log ((a + x i) / a))
      = k * (p i * Real.log (a + x i)) - (k * Real.log a) * p i := by
    intro i hi
    rw [Real.log_div (hx i hi).ne' ha.ne']
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp]
  ring

/-- **F26.20 (印刷形の反例)**: 印刷は指数が落ちて x = (a+x₁)p₁(a+x₂)p₂ と組まれている。
文字どおり積として読むと a = 1, x₁ = x₂ = 1, p₁ = p₂ = 1/2 で x = 1 となり、
道徳的価値 log(x/a) = 0 は期待の道徳的価値 (1/2)log 2 + (1/2)log 2 = log 2 > 0 に一致しない。 -/
theorem th_26_laplace_printed_refuted :
    Real.log (((1 + 1) * (1 / 2) * ((1 + 1) * (1 / 2))) / 1 : ℝ)
      ≠ (1 / 2) * Real.log ((1 + 1) / 1 : ℝ) + (1 / 2) * Real.log ((1 + 1) / 1 : ℝ) := by
  have h := Real.log_pos (by norm_num : (1:ℝ) < 2)
  norm_num
  linarith

/-! ## F. folio 318 — Cramer の二つの解 (F26.22, F26.23) -/

/-- **F26.22** 2²⁴ = 16,777,216。印刷の "(16,777,116)" とは一致しない (誤植、所見候補)。 -/
theorem th_26_two_pow_24 : (2:ℕ) ^ 24 = 16777216 := by norm_num

theorem th_26_printed_16777116_refuted : (2:ℕ) ^ 24 ≠ 16777116 := by norm_num

/-- 上限 2²⁴ で打ち切った利得の期待の項: (1/2)^{r+1}·min(2^r, 2²⁴) (第 r+1 回に最初の表)。 -/
noncomputable def cramerCapped (r : ℕ) : ℝ := ((1:ℝ) / 2) ^ (r + 1) * min ((2:ℝ) ^ r) (2 ^ 24)

theorem cramerCapped_small (r : ℕ) (hr : r < 25) : cramerCapped r = 1 / 2 := by
  unfold cramerCapped
  rw [min_eq_left (pow_le_pow_right₀ (by norm_num) (by omega))]
  simpa using th_26_petersburg_term (r + 1) (by omega)

theorem cramerCapped_large (r : ℕ) : cramerCapped (r + 25) = ((1:ℝ) / 2) ^ r * ((1 / 2) ^ 26 * 2 ^ 24) := by
  unfold cramerCapped
  rw [min_eq_right (pow_le_pow_right₀ (by norm_num) (by omega))]
  ring

theorem cramerCapped_summable : Summable cramerCapped := by
  refine Summable.of_nonneg_of_le (fun r => ?_) (fun r => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)).mul_left (2 ^ 23))
  · unfold cramerCapped
    exact mul_nonneg (by positivity) (le_min (by positivity) (by positivity))
  · unfold cramerCapped
    calc ((1:ℝ) / 2) ^ (r + 1) * min ((2:ℝ) ^ r) (2 ^ 24)
        ≤ (1 / 2) ^ (r + 1) * 2 ^ 24 := by gcongr; exact min_le_right _ _
      _ = 2 ^ 23 * (1 / 2) ^ r := by rw [pow_succ]; ring

/-- **F26.22**: Cramer の第 1 解 — 2²⁴ を超える金額を「道徳的に同価」とすると公平掛金は £13
(£1 単位): Σ_{r≥1} (1/2)^r min(2^{r−1}, 2²⁴) = 25/2 + 1/2 = 13。 -/
theorem th_26_cramer_cap : ∑' r : ℕ, cramerCapped r = 13 := by
  rw [← cramerCapped_summable.sum_add_tsum_nat_add 25]
  have hhead : ∑ i ∈ range 25, cramerCapped i = 25 / 2 := by
    rw [Finset.sum_congr rfl (fun i hi => cramerCapped_small i (Finset.mem_range.mp hi))]
    simp
    norm_num
  have htail : ∑' i : ℕ, cramerCapped (i + 25) = 1 / 2 := by
    simp_rw [cramerCapped_large]
    rw [tsum_mul_right, tsum_geometric_two]
    norm_num
  rw [hhead, htail]
  norm_num

/-- √(2^r) = (√2)^r。 -/
theorem th_26_sqrt_two_pow (r : ℕ) : Real.sqrt ((2:ℝ) ^ r) = (Real.sqrt 2) ^ r := by
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- **F26.23**: Cramer の第 2 解 — 快楽 ∝ √(金額) のとき、利得の√の期待は
Σ_{r≥1} (1/2)^r √(2^{r−1}) = 1 + √2/2。 -/
theorem th_26_cramer_sqrt_expectation :
    ∑' r : ℕ, ((1:ℝ) / 2) ^ (r + 1) * Real.sqrt (2 ^ r) = 1 + Real.sqrt 2 / 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlt : Real.sqrt 2 < 2 := by nlinarith
  have hterm : ∀ r : ℕ, ((1:ℝ) / 2) ^ (r + 1) * Real.sqrt (2 ^ r) = (Real.sqrt 2 / 2) ^ r * (1 / 2) := by
    intro r
    rw [th_26_sqrt_two_pow, pow_succ, div_pow, div_pow, one_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity) (by linarith)]
  -- (1 − √2/2)⁻¹ = 2 + √2、ゆえに (1 − √2/2)⁻¹·(1/2) = 1 + √2/2
  have key : (1 - Real.sqrt 2 / 2)⁻¹ = 2 + Real.sqrt 2 := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination (-1 / 2 : ℝ) * hs2
  rw [key]
  ring

/-- **F26.23** 公平掛金 s は √s = 1 + √2/2、すなわち s = (1 + √2/2)² = 3/2 + √2。 -/
theorem th_26_cramer_sqrt_stake : (1 + Real.sqrt 2 / 2) ^ 2 = 3 / 2 + Real.sqrt 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 4 : ℝ) * hs2

/-- **F26.23 印刷値の疑義** (S): 印刷 "£2 : 9s." = 2 + 9/20 = 2.45 は、Paul の初期財産を 0 とする
Cramer の設定 (印刷にはない) の下での公平掛金 3/2 + √2 (> 2.9) に一致しない。
その設定では £2 18s < 3/2 + √2 < £2 19s (≈ £2 18s 3d)。Cramer の原文「約 2.9」の小数を
£2 9s と読み替えた印刷と思われる (所見候補)。設定を置いた上での判定なので反駁 (F) ではなく疑義に留める。 -/
theorem th_26_cramer_sqrt_dubious :
    (2 + 9 / 20 : ℝ) < 3 / 2 + Real.sqrt 2 ∧
    (2 + 18 / 20 : ℝ) < 3 / 2 + Real.sqrt 2 ∧ (3 / 2 + Real.sqrt 2 : ℝ) < 2 + 19 / 20 := by
  have h1 : (7 / 5 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 2 < (29 / 20 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## G. folio 318 — Bernoulli の £6 (F26.21) -/

/-- **F26.21 の核**: 対数効用の下では Petersburg の期待 Σ (1/2)^{r+1} log(F + 2^r) は有限 (総和可能)。
F は初期財産 (Bernoulli の例では £1000)。 -/
theorem th_26_bernoulli_summable (F : ℝ) (hF : 0 ≤ F) :
    Summable (fun r : ℕ => ((1:ℝ) / 2) ^ (r + 1) * Real.log (F + 2 ^ r)) := by
  have hmaj : Summable (fun r : ℕ =>
      Real.log (F + 1) * (1 / 2 : ℝ) ^ r + Real.log 2 * ((r : ℝ) ^ 1 * (1 / 2 : ℝ) ^ r)) := by
    refine Summable.add ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _) ?_
    refine Summable.mul_left _ (summable_pow_mul_geometric_of_norm_lt_one 1 ?_)
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  refine Summable.of_nonneg_of_le (fun r => ?_) (fun r => ?_) hmaj
  · have : (1:ℝ) ≤ F + 2 ^ r := by
      have := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := r)
      linarith
    exact mul_nonneg (by positivity) (Real.log_nonneg this)
  · have hpow : (1:ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have h1 : (1:ℝ) ≤ F + 2 ^ r := by linarith
    have h2 : F + 2 ^ r ≤ (F + 1) * 2 ^ r := by nlinarith
    have h3 : Real.log (F + 2 ^ r) ≤ Real.log (F + 1) + Real.log 2 * r := by
      calc Real.log (F + 2 ^ r) ≤ Real.log ((F + 1) * 2 ^ r) := Real.log_le_log (by linarith) h2
        _ = Real.log (F + 1) + Real.log 2 * r := by
          rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; ring
    have hX : 0 ≤ Real.log (F + 1) + Real.log 2 * r := by
      have := Real.log_nonneg (by linarith : (1:ℝ) ≤ F + 1)
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
      positivity
    have hg : 0 ≤ ((1:ℝ) / 2) ^ r := by positivity
    calc ((1:ℝ) / 2) ^ (r + 1) * Real.log (F + 2 ^ r)
        ≤ (1 / 2) ^ (r + 1) * (Real.log (F + 1) + Real.log 2 * r) := by gcongr
      _ ≤ (Real.log (F + 1) + Real.log 2 * r) * (1 / 2) ^ r := by
          rw [pow_succ]; nlinarith [mul_nonneg hg hX]
      _ = Real.log (F + 1) * (1 / 2) ^ r + Real.log 2 * ((r : ℝ) ^ 1 * (1 / 2) ^ r) := by ring

/-! ### G-1. log の Taylor 評価 (有理数の上下界) -/

/-- 0 < x ≤ 1: −Σ_{i<n}(1−x)^{i+1}/(i+1) ∓ (1−x)^{n+1}/x で log x を挟む
(`Real.abs_log_sub_add_sum_range_le` の書き換え)。 -/
theorem log_taylor_le_one (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) (n : ℕ) :
    -(∑ i ∈ range n, (1 - x) ^ (i + 1) / (i + 1)) - (1 - x) ^ (n + 1) / x ≤ Real.log x ∧
    Real.log x ≤ -(∑ i ∈ range n, (1 - x) ^ (i + 1) / (i + 1)) + (1 - x) ^ (n + 1) / x := by
  have hx : |1 - x| < 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [sub_sub_cancel, abs_le, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - x), sub_sub_cancel] at h
  constructor <;> linarith [h.1, h.2]

/-- 1 ≤ x < 2: 同じ評価、剰余は (x−1)^{n+1}/(2−x)。 -/
theorem log_taylor_ge_one (x : ℝ) (h1 : 1 ≤ x) (h2 : x < 2) (n : ℕ) :
    -(∑ i ∈ range n, (1 - x) ^ (i + 1) / (i + 1)) - (x - 1) ^ (n + 1) / (2 - x) ≤ Real.log x ∧
    Real.log x ≤ -(∑ i ∈ range n, (1 - x) ^ (i + 1) / (i + 1)) + (x - 1) ^ (n + 1) / (2 - x) := by
  have hx : |1 - x| < 1 := by rw [abs_of_nonpos (by linarith)]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [sub_sub_cancel, abs_le, abs_of_nonpos (by linarith : 1 - x ≤ 0), neg_sub,
    show (1:ℝ) - (x - 1) = 2 - x by ring] at h
  constructor <;> linarith [h.1, h.2]

/-! ### G-2. Bernoulli の道徳的期待と公平掛金 -/

/-- 財産 F、掛金 s で £1 単位の Petersburg の賭けに参加したときの道徳的財産の期待 (k = 1):
Σ_{r≥0} (1/2)^{r+1} log(F − s + 2^r)。Bernoulli の公平掛金 s* はこれが log F (賭けない場合の
道徳的財産) に等しくなる s。 -/
noncomputable def bernoulliMoral (F s : ℝ) : ℝ :=
  ∑' r : ℕ, ((1:ℝ) / 2) ^ (r + 1) * Real.log (F - s + 2 ^ r)

theorem bernoulliMoral_summable (F s : ℝ) (hs : 0 ≤ F - s) :
    Summable (fun r : ℕ => ((1:ℝ) / 2) ^ (r + 1) * Real.log (F - s + 2 ^ r)) :=
  th_26_bernoulli_summable (F - s) hs

theorem geom_half_succ : ∑' r : ℕ, ((1:ℝ) / 2) ^ (r + 1) = 1 := by
  have : (fun r : ℕ => ((1:ℝ) / 2) ^ (r + 1)) = fun r => (1 / 2) * ((1:ℝ) / 2) ^ r := by
    funext r; ring
  rw [this, tsum_mul_left, tsum_geometric_two]; norm_num

theorem summable_half_succ_mul (a : ℝ) : Summable (fun r : ℕ => a * ((1:ℝ) / 2) ^ (r + 1)) :=
  ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))).mul_left a

/-- 正規化: 期待 − log F = Σ (1/2)^{r+1} log((F − s + 2^r)/F)。 -/
theorem bernoulliMoral_sub_log (F s : ℝ) (hF : 0 < F) (hs : 0 ≤ F - s) :
    bernoulliMoral F s - Real.log F
      = ∑' r : ℕ, ((1:ℝ) / 2) ^ (r + 1) * Real.log ((F - s + 2 ^ r) / F) := by
  have hpos : ∀ r : ℕ, 0 < F - s + 2 ^ r := fun r => by
    have := pow_pos (two_pos : (0:ℝ) < 2) r; linarith
  have hterm : ∀ r : ℕ, ((1:ℝ) / 2) ^ (r + 1) * Real.log ((F - s + 2 ^ r) / F)
      = ((1:ℝ) / 2) ^ (r + 1) * Real.log (F - s + 2 ^ r) - Real.log F * ((1:ℝ) / 2) ^ (r + 1) := by
    intro r; rw [Real.log_div (hpos r).ne' hF.ne']; ring
  simp_rw [hterm]
  rw [Summable.tsum_sub (bernoulliMoral_summable F s hs) (summable_half_succ_mul _), tsum_mul_left,
    geom_half_succ, mul_one]
  rfl

theorem summable_normalized (F s : ℝ) (hF : 0 < F) (hs : 0 ≤ F - s) :
    Summable (fun r : ℕ => ((1:ℝ) / 2) ^ (r + 1) * Real.log ((F - s + 2 ^ r) / F)) := by
  have hpos : ∀ r : ℕ, 0 < F - s + 2 ^ r := fun r => by
    have := pow_pos (two_pos : (0:ℝ) < 2) r; linarith
  have hterm : (fun r : ℕ => ((1:ℝ) / 2) ^ (r + 1) * Real.log ((F - s + 2 ^ r) / F))
      = fun r => ((1:ℝ) / 2) ^ (r + 1) * Real.log (F - s + 2 ^ r) - Real.log F * ((1:ℝ) / 2) ^ (r + 1) := by
    funext r; rw [Real.log_div (hpos r).ne' hF.ne']; ring
  rw [hterm]
  exact (bernoulliMoral_summable F s hs).sub (summable_half_succ_mul _)

/-- 掛金について単調 (非増加): 多く払うほど道徳的期待は下がる。 -/
theorem bernoulliMoral_anti (F : ℝ) {s s' : ℝ} (h : s ≤ s') (h' : s' ≤ F) :
    bernoulliMoral F s' ≤ bernoulliMoral F s := by
  unfold bernoulliMoral
  refine Summable.tsum_le_tsum (fun r => ?_) (bernoulliMoral_summable F s' (by linarith))
    (bernoulliMoral_summable F s (by linarith))
  have := pow_pos (two_pos : (0:ℝ) < 2) r
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (by positivity)

/-- 掛金について連続 (s ∈ [5.9, 6]; 一様優級数 (1/2)^{r+1} log(1000 + 2^r))。 -/
theorem bernoulliMoral_continuousOn :
    ContinuousOn (fun s : ℝ => bernoulliMoral 1000 s) (Set.Icc (59 / 10) 6) := by
  unfold bernoulliMoral
  refine continuousOn_tsum (u := fun r : ℕ => ((1:ℝ) / 2) ^ (r + 1) * Real.log (1000 + 2 ^ r))
    (fun r => ?_) (th_26_bernoulli_summable 1000 (by norm_num)) (fun r s hs => ?_)
  · refine ContinuousOn.mul continuousOn_const (ContinuousOn.log (by fun_prop) ?_)
    intro s hs
    have := pow_pos (two_pos : (0:ℝ) < 2) r
    have := hs.2
    linarith
  · obtain ⟨hs1, hs2⟩ := hs
    have h2r : (1:ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have hpos : 0 ≤ Real.log (1000 - s + 2 ^ r) := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hpos)]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (by positivity)

/-- 第 10 項以降: (1000 − s + 2^{k+10})/1000 = 2^k (1.024 + c/2^k)、c = (1000 − s)/1000。 -/
theorem bernoulli_term_shift (s : ℝ) (hs : 0 ≤ 1000 - s) (k : ℕ) :
    Real.log ((1000 - s + 2 ^ (k + 10)) / 1000)
      = k * Real.log 2 + Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ k) := by
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have hG : 0 < (1024 / 1000 : ℝ) + (1000 - s) / 1000 / 2 ^ k := by
    have := div_nonneg (div_nonneg hs (by norm_num : (0:ℝ) ≤ 1000)) h2k.le; linarith
  have heq : (1000 - s + 2 ^ (k + 10)) / 1000
      = 2 ^ k * (1024 / 1000 + (1000 - s) / 1000 / 2 ^ k) := by
    field_simp; ring
  rw [heq, Real.log_mul h2k.ne' hG.ne', Real.log_pow]

/-- 級数の分割: 先頭 10 項 + Σ k·2^{−(k+11)} log 2 (= log 2/1024) + 第 10–15 項の残差 + 裾。 -/
theorem bernoulli_split (s : ℝ) (hs : 0 ≤ 1000 - s) :
    ∑' r : ℕ, ((1:ℝ) / 2) ^ (r + 1) * Real.log ((1000 - s + 2 ^ r) / 1000)
      = ∑ r ∈ range 10, ((1:ℝ) / 2) ^ (r + 1) * Real.log ((1000 - s + 2 ^ r) / 1000)
        + Real.log 2 / 1024
        + ∑ k ∈ range 6, ((1:ℝ) / 2) ^ (k + 11) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ k)
        + ∑' j : ℕ, ((1:ℝ) / 2) ^ (j + 17) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6)) := by
  have hc0 : 0 ≤ (1000 - s) / 1000 := div_nonneg hs (by norm_num)
  have hGnn : ∀ k : ℕ, 0 ≤ Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ k) := fun k =>
    Real.log_nonneg (by have := div_nonneg hc0 (pow_pos (two_pos : (0:ℝ) < 2) k).le; linarith)
  have hGle : ∀ k : ℕ, Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ k) ≤ 24 / 1000 + (1000 - s) / 1000 := by
    intro k
    have h2k : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hle : (1000 - s) / 1000 / 2 ^ k ≤ (1000 - s) / 1000 := div_le_self hc0 h2k
    have hnn := div_nonneg hc0 (pow_pos (two_pos : (0:ℝ) < 2) k).le
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1024 / 1000 + (1000 - s) / 1000 / 2 ^ k)
    linarith
  have hB : Summable (fun k : ℕ => ((1:ℝ) / 2) ^ (k + 11) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ k)) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (hGnn k)) (fun k => ?_)
      (((summable_nat_add_iff 11).mpr
        (summable_geometric_of_lt_one (r := (1:ℝ) / 2) (by norm_num) (by norm_num))).mul_right
        (24 / 1000 + (1000 - s) / 1000))
    exact mul_le_mul_of_nonneg_left (hGle k) (by positivity)
  have hAfun : (fun k : ℕ => ((1:ℝ) / 2) ^ (k + 11) * (k * Real.log 2))
      = fun k : ℕ => (Real.log 2 / 2 ^ 11) * ((k : ℝ) * ((1:ℝ) / 2) ^ k) := by
    funext k; ring
  have hA : Summable (fun k : ℕ => ((1:ℝ) / 2) ^ (k + 11) * (k * Real.log 2)) := by
    rw [hAfun]
    refine Summable.mul_left _ (hasSum_coe_mul_geometric_of_norm_lt_one ?_).summable
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
  have hAsum : ∑' k : ℕ, ((1:ℝ) / 2) ^ (k + 11) * (k * Real.log 2) = Real.log 2 / 1024 := by
    rw [hAfun, tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one
      (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)]
    ring
  have hf := summable_normalized 1000 s (by norm_num) hs
  have hshift : (fun k : ℕ => ((1:ℝ) / 2) ^ (k + 10 + 1) * Real.log ((1000 - s + 2 ^ (k + 10)) / 1000))
      = fun k : ℕ => ((1:ℝ) / 2) ^ (k + 11) * ((k : ℝ) * Real.log 2)
        + ((1:ℝ) / 2) ^ (k + 11) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ k) := by
    funext k; rw [bernoulli_term_shift s hs k]; ring
  rw [← hf.sum_add_tsum_nat_add 10, hshift, hA.tsum_add hB, hAsum, ← hB.sum_add_tsum_nat_add 6]
  simp only [show ∀ j : ℕ, j + 6 + 11 = j + 17 from fun j => by omega]
  ring

/-- 裾 (第 16 項以降) の評価: 1 − x⁻¹ ≤ log x ≤ x − 1 を x ∈ [1.024, 1.024 + c/64] に適用。 -/
theorem bernoulli_tail_bounds (s : ℝ) (hs : 0 ≤ 1000 - s) :
    (1 - 1000 / 1024) / 2 ^ 16
      ≤ ∑' j : ℕ, ((1:ℝ) / 2) ^ (j + 17) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6)) ∧
    ∑' j : ℕ, ((1:ℝ) / 2) ^ (j + 17) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6))
      ≤ (24 / 1000 + (1000 - s) / 1000 / 64) / 2 ^ 16 := by
  have hc0 : 0 ≤ (1000 - s) / 1000 := div_nonneg hs (by norm_num)
  have hgeo : ∀ K : ℝ, ∑' j : ℕ, ((1:ℝ) / 2) ^ (j + 17) * K = K / 2 ^ 16 := by
    intro K
    have : (fun j : ℕ => ((1:ℝ) / 2) ^ (j + 17) * K) = fun j => (K / 2 ^ 17) * ((1:ℝ) / 2) ^ j := by
      funext j; ring
    rw [this, tsum_mul_left, tsum_geometric_two]; ring
  have hsumK : ∀ K : ℝ, Summable (fun j : ℕ => ((1:ℝ) / 2) ^ (j + 17) * K) := fun K =>
    ((summable_nat_add_iff 17).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))).mul_right K
  have hx : ∀ j : ℕ, (1024 / 1000 : ℝ) ≤ 1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6) := fun j => by
    have := div_nonneg hc0 (pow_pos (two_pos : (0:ℝ) < 2) (j + 6)).le; linarith
  have hlo : ∀ j : ℕ, ((1:ℝ) / 2) ^ (j + 17) * (1 - 1000 / 1024)
      ≤ ((1:ℝ) / 2) ^ (j + 17) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6)) := by
    intro j
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 := Real.one_sub_inv_le_log_of_pos (by linarith [hx j] : (0:ℝ) < 1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6))
    have h2 : (1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6))⁻¹ ≤ (1024 / 1000 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (hx j)
    norm_num at h2 ⊢
    linarith
  have hhi : ∀ j : ℕ, ((1:ℝ) / 2) ^ (j + 17) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6))
      ≤ ((1:ℝ) / 2) ^ (j + 17) * (24 / 1000 + (1000 - s) / 1000 / 64) := by
    intro j
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 := Real.log_le_sub_one_of_pos (by linarith [hx j] : (0:ℝ) < 1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6))
    have h64 : (64:ℝ) ≤ 2 ^ (j + 6) := by
      calc (64:ℝ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (j + 6) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (1000 - s) / 1000 / 2 ^ (j + 6) ≤ (1000 - s) / 1000 / 64 :=
      div_le_div_of_nonneg_left hc0 (by norm_num) h64
    linarith
  have hsum : Summable (fun j : ℕ => ((1:ℝ) / 2) ^ (j + 17) * Real.log (1024 / 1000 + (1000 - s) / 1000 / 2 ^ (j + 6))) :=
    Summable.of_nonneg_of_le (fun j => le_trans (by norm_num) (hlo j)) hhi (hsumK _)
  constructor
  · rw [← hgeo]; exact Summable.tsum_le_tsum hlo (hsumK _) hsum
  · rw [← hgeo]; exact Summable.tsum_le_tsum hhi hsum (hsumK _)

/-- s = 6: 正規化した期待は負 — £6 はわずかに払い過ぎ。各項は log の Taylor 評価 (有理数) で挟む。 -/
theorem bernoulli_six_neg :
    ∑' r : ℕ, ((1:ℝ) / 2) ^ (r + 1) * Real.log ((1000 - 6 + 2 ^ r) / 1000) < 0 := by
  rw [bernoulli_split 6 (by norm_num)]
  obtain ⟨tl, tu⟩ := bernoulli_tail_bounds 6 (by norm_num)
  generalize (∑' j : ℕ, ((1:ℝ) / 2) ^ (j + 17) * Real.log (1024 / 1000 + (1000 - 6) / 1000 / 2 ^ (j + 6))) = T at tl tu ⊢
  have l2 := Real.log_two_gt_d9
  have u2 := Real.log_two_lt_d9
  -- 先頭 10 項 (r = 9 は log 2 + log(0.753))
  obtain ⟨a0, b0⟩ := log_taylor_le_one ((1000 - 6 + 2 ^ 0) / 1000) (by norm_num) (by norm_num) 2
  obtain ⟨a1, b1⟩ := log_taylor_le_one ((1000 - 6 + 2 ^ 1) / 1000) (by norm_num) (by norm_num) 2
  obtain ⟨a2, b2⟩ := log_taylor_le_one ((1000 - 6 + 2 ^ 2) / 1000) (by norm_num) (by norm_num) 2
  obtain ⟨a3, b3⟩ := log_taylor_ge_one ((1000 - 6 + 2 ^ 3) / 1000) (by norm_num) (by norm_num) 2
  obtain ⟨a4, b4⟩ := log_taylor_ge_one ((1000 - 6 + 2 ^ 4) / 1000) (by norm_num) (by norm_num) 3
  obtain ⟨a5, b5⟩ := log_taylor_ge_one ((1000 - 6 + 2 ^ 5) / 1000) (by norm_num) (by norm_num) 3
  obtain ⟨a6, b6⟩ := log_taylor_ge_one ((1000 - 6 + 2 ^ 6) / 1000) (by norm_num) (by norm_num) 4
  obtain ⟨a7, b7⟩ := log_taylor_ge_one ((1000 - 6 + 2 ^ 7) / 1000) (by norm_num) (by norm_num) 5
  obtain ⟨a8, b8⟩ := log_taylor_ge_one ((1000 - 6 + 2 ^ 8) / 1000) (by norm_num) (by norm_num) 7
  have m9 : Real.log ((1000 - 6 + 2 ^ 9) / 1000 : ℝ) = Real.log 2 + Real.log ((1000 - 6 + 2 ^ 9) / 2000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨a9, b9⟩ := log_taylor_le_one ((1000 - 6 + 2 ^ 9) / 2000) (by norm_num) (by norm_num) 8
  -- 第 10–15 項 (k = 0 は log 2 + log(1.009))
  have m10 : Real.log (1024 / 1000 + (1000 - 6) / 1000 / 2 ^ 0 : ℝ)
      = Real.log 2 + Real.log ((1024 / 1000 + (1000 - 6) / 1000 / 2 ^ 0) / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨c0, d0⟩ := log_taylor_ge_one ((1024 / 1000 + (1000 - 6) / 1000 / 2 ^ 0) / 2) (by norm_num) (by norm_num) 2
  obtain ⟨c1, d1⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 6) / 1000 / 2 ^ 1) (by norm_num) (by norm_num) 7
  obtain ⟨c2, d2⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 6) / 1000 / 2 ^ 2) (by norm_num) (by norm_num) 5
  obtain ⟨c3, d3⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 6) / 1000 / 2 ^ 3) (by norm_num) (by norm_num) 4
  obtain ⟨c4, d4⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 6) / 1000 / 2 ^ 4) (by norm_num) (by norm_num) 3
  obtain ⟨c5, d5⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 6) / 1000 / 2 ^ 5) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at *
  linarith

/-- s = 5.9: 正規化した期待は正 — £5 18s では払い足りない。 -/
theorem bernoulli_five_nine_pos :
    0 < ∑' r : ℕ, ((1:ℝ) / 2) ^ (r + 1) * Real.log ((1000 - 59 / 10 + 2 ^ r) / 1000) := by
  rw [bernoulli_split (59 / 10) (by norm_num)]
  obtain ⟨tl, tu⟩ := bernoulli_tail_bounds (59 / 10) (by norm_num)
  generalize (∑' j : ℕ, ((1:ℝ) / 2) ^ (j + 17) * Real.log (1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ (j + 6))) = T at tl tu ⊢
  have l2 := Real.log_two_gt_d9
  have u2 := Real.log_two_lt_d9
  obtain ⟨a0, b0⟩ := log_taylor_le_one ((1000 - 59 / 10 + 2 ^ 0) / 1000) (by norm_num) (by norm_num) 2
  obtain ⟨a1, b1⟩ := log_taylor_le_one ((1000 - 59 / 10 + 2 ^ 1) / 1000) (by norm_num) (by norm_num) 2
  obtain ⟨a2, b2⟩ := log_taylor_le_one ((1000 - 59 / 10 + 2 ^ 2) / 1000) (by norm_num) (by norm_num) 2
  obtain ⟨a3, b3⟩ := log_taylor_ge_one ((1000 - 59 / 10 + 2 ^ 3) / 1000) (by norm_num) (by norm_num) 2
  obtain ⟨a4, b4⟩ := log_taylor_ge_one ((1000 - 59 / 10 + 2 ^ 4) / 1000) (by norm_num) (by norm_num) 3
  obtain ⟨a5, b5⟩ := log_taylor_ge_one ((1000 - 59 / 10 + 2 ^ 5) / 1000) (by norm_num) (by norm_num) 3
  obtain ⟨a6, b6⟩ := log_taylor_ge_one ((1000 - 59 / 10 + 2 ^ 6) / 1000) (by norm_num) (by norm_num) 4
  obtain ⟨a7, b7⟩ := log_taylor_ge_one ((1000 - 59 / 10 + 2 ^ 7) / 1000) (by norm_num) (by norm_num) 5
  obtain ⟨a8, b8⟩ := log_taylor_ge_one ((1000 - 59 / 10 + 2 ^ 8) / 1000) (by norm_num) (by norm_num) 7
  have m9 : Real.log ((1000 - 59 / 10 + 2 ^ 9) / 1000 : ℝ)
      = Real.log 2 + Real.log ((1000 - 59 / 10 + 2 ^ 9) / 2000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨a9, b9⟩ := log_taylor_le_one ((1000 - 59 / 10 + 2 ^ 9) / 2000) (by norm_num) (by norm_num) 8
  have m10 : Real.log (1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ 0 : ℝ)
      = Real.log 2 + Real.log ((1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ 0) / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨c0, d0⟩ := log_taylor_ge_one ((1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ 0) / 2) (by norm_num) (by norm_num) 2
  obtain ⟨c1, d1⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ 1) (by norm_num) (by norm_num) 7
  obtain ⟨c2, d2⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ 2) (by norm_num) (by norm_num) 5
  obtain ⟨c3, d3⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ 3) (by norm_num) (by norm_num) 4
  obtain ⟨c4, d4⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ 4) (by norm_num) (by norm_num) 3
  obtain ⟨c5, d5⟩ := log_taylor_ge_one (1024 / 1000 + (1000 - 59 / 10) / 1000 / 2 ^ 5) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at *
  linarith

/-- **F26.21 両端の判定**: 財産 £1000 で掛金 £6 は払い過ぎ (道徳的期待が log 1000 を下回る)、
£5 18s (= 5.9) では払い足りない。印刷の「£6 を払ってよい」は s* ≈ 5.97 の丸めの読みである。 -/
theorem th_26_bernoulli_stake_strict :
    bernoulliMoral 1000 6 < Real.log 1000 ∧ Real.log 1000 < bernoulliMoral 1000 (59 / 10) := by
  constructor
  · have := bernoulli_six_neg
    rw [← bernoulliMoral_sub_log 1000 6 (by norm_num) (by norm_num)] at this
    linarith
  · have := bernoulli_five_nine_pos
    rw [← bernoulliMoral_sub_log 1000 (59 / 10) (by norm_num) (by norm_num)] at this
    linarith

/-- **F26.21** Bernoulli の公平掛金 s* (bernoulliMoral 1000 s* = log 1000) は存在して 5.9 < s* < 6 を
満たし、掛金 ≤ 財産 の範囲で一意 (この区間の外に解はない)。印刷の「£6」は s* の丸め (s* ≈ 5.97) として
整合するが、£6 ちょうどは公平掛金ではない (`th_26_bernoulli_stake_strict`)。 -/
theorem th_26_bernoulli_stake_bounds :
    (∃ s : ℝ, 59 / 10 < s ∧ s < 6 ∧ bernoulliMoral 1000 s = Real.log 1000) ∧
    (∀ s : ℝ, s ≤ 1000 → bernoulliMoral 1000 s = Real.log 1000 → 59 / 10 < s ∧ s < 6) := by
  obtain ⟨h6, h59⟩ := th_26_bernoulli_stake_strict
  constructor
  · have hmem : Real.log 1000 ∈ Set.Icc (bernoulliMoral 1000 6) (bernoulliMoral 1000 (59 / 10)) :=
      ⟨h6.le, h59.le⟩
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ :=
      intermediate_value_Icc' (by norm_num : (59 / 10 : ℝ) ≤ 6) bernoulliMoral_continuousOn hmem
    refine ⟨s, lt_of_le_of_ne hs1 ?_, lt_of_le_of_ne hs2 ?_, hs⟩
    · rintro rfl
      exact absurd hs h59.ne'
    · rintro rfl
      exact absurd hs h6.ne
  · intro s hs hsol
    constructor
    · by_contra hle
      rw [not_lt] at hle
      have := bernoulliMoral_anti 1000 hle (by norm_num : (59 / 10 : ℝ) ≤ 1000)
      linarith
    · by_contra hle
      rw [not_lt] at hle
      have := bernoulliMoral_anti 1000 hle hs
      linarith

/-! ## H. folio 319 — 相対リスク R/E (F26.24、解釈つき) -/

/-- 各結果 r (利得 A_r = 2^{r−1}、確率 p_r = (1/2)^r) に folio 315 の定義 R = p(A − E) = p(A − pA) を
当てはめて n 回まで足したリスク。Keynes は多結果への拡張を印刷していない (ヘッダの境界記録参照)。 -/
noncomputable def petersburgRisk (n : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 n, ((1:ℝ) / 2) ^ r * (2 ^ (r - 1) - (1 / 2) ^ r * 2 ^ (r - 1))

theorem petersburgRisk_term (r : ℕ) (hr : 1 ≤ r) :
    ((1:ℝ) / 2) ^ r * (2 ^ (r - 1) - (1 / 2) ^ r * 2 ^ (r - 1)) = 1 / 2 - (1 / 2) ^ (r + 1) := by
  have h := th_26_petersburg_term r hr
  calc ((1:ℝ) / 2) ^ r * (2 ^ (r - 1) - (1 / 2) ^ r * 2 ^ (r - 1))
      = (1 / 2) ^ r * 2 ^ (r - 1) - (1 / 2) ^ r * ((1 / 2) ^ r * 2 ^ (r - 1)) := by ring
    _ = 1 / 2 - (1 / 2) ^ r * (1 / 2) := by rw [h]
    _ = 1 / 2 - (1 / 2) ^ (r + 1) := by rw [pow_succ]

theorem geom_half (n : ℕ) : ∑ r ∈ Icc 1 n, ((1:ℝ) / 2) ^ (r + 1) = 1 / 2 - (1 / 2) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring

/-- R_n = n/2 − 1/2 + (1/2)^{n+1} (閉形式)。 -/
theorem th_26_petersburg_risk_closed (n : ℕ) :
    petersburgRisk n = n / 2 - 1 / 2 + (1 / 2) ^ (n + 1) := by
  unfold petersburgRisk
  rw [Finset.sum_congr rfl (fun r hr => petersburgRisk_term r (Finset.mem_Icc.mp hr).1),
    Finset.sum_sub_distrib, geom_half]
  simp [Finset.sum_const, Nat.card_Icc]
  ring

/-- **F26.24**: 相対リスク R/E = 1 − (1 − (1/2)^n)/n、1 − 1/n ≤ R/E < 1 —「ほとんど 1」。 -/
theorem th_26_relative_risk (n : ℕ) (hn : 1 ≤ n) :
    petersburgRisk n / (n / 2) = 1 - (1 - (1 / 2) ^ n) / n ∧
    1 - 1 / (n : ℝ) ≤ petersburgRisk n / (n / 2) ∧ petersburgRisk n / (n / 2) < 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hpow0 : (0:ℝ) ≤ (1 / 2) ^ (n + 1) := by positivity
  have hpow1 : ((1:ℝ) / 2) ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  rw [th_26_petersburg_risk_closed]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · rw [le_div_iff₀ (by positivity)]
    have : (1 - 1 / (n:ℝ)) * (n / 2) = n / 2 - 1 / 2 := by
      field_simp
    rw [this]
    linarith
  · rw [div_lt_one (by positivity), pow_succ]
    nlinarith

/-- **F26.24 極限形**: R_n/E_n → 1 (n → ∞)。はさみうち 1 − 1/n ≤ R_n/E_n < 1 から。 -/
theorem th_26_relative_risk_tendsto :
    Tendsto (fun n : ℕ => petersburgRisk n / (n / 2)) atTop (𝓝 1) := by
  have hlo : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (th_26_relative_risk n hn).2.1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (th_26_relative_risk n hn).2.2.le

/-- **F26.24** 「回数に制限がなければリスクは無限大」: R_n はどの実数も超える。 -/
theorem th_26_petersburg_risk_unbounded : ∀ M : ℝ, ∃ n : ℕ, M < petersburgRisk n := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M + 1)
  refine ⟨n, ?_⟩
  rw [th_26_petersburg_risk_closed]
  have : (0:ℝ) ≤ (1 / 2) ^ (n + 1) := by positivity
  linarith

/-! ## I. folio 319 §10 — Laurent の f(a) = b/(a+b) (F26.25, F26.26) -/

/-- **F26.25**: f(a) = b/(a+b) は a について減少 —「相手より貧しいほど破産しやすい」。 -/
theorem th_26_laurent_poorer {a a' b : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (h : a < a') :
    b / (a' + b) < b / (a + b) :=
  div_lt_div_of_pos_left hb (by linarith) (by linarith)

/-- **F26.26**: 「b = ∞ なら f(a) = 1」— b → ∞ で b/(a+b) → 1。 -/
theorem th_26_laurent_limit (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun b : ℝ => b / (a + b)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun b : ℝ => a / (a + b)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ a tendsto_id)
  have h2 : Tendsto (fun b : ℝ => 1 - a / (a + b)) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h1
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have : a + b ≠ 0 := by linarith
  field_simp
  ring

/-! ## J. folio 311 脚注 — Leibniz の比例分割 (補) -/

/-- folio 311 脚注 1 (補助): 一方の請求が他方の 2 倍確からしいなら、金額 S をその比 (2 : 1) で分ける。
印刷は言語的な記述のみで記号式はない; 台帳の F 補 1 を支える補助定理。 -/
theorem th_26_fn_leibniz_division (S : ℝ) :
    (2 / 3) * S + (1 / 3) * S = S ∧ (2 / 3) * S = 2 * ((1 / 3) * S) := ⟨by ring, by ring⟩

end KeynesCh26

/-! ## 監査クエリ (Phase 8a-2) -/

#check @KeynesCh26.th_26_fn1_printed_iff
#check @KeynesCh26.th_26_fn1_czuber_tsum
#check @KeynesCh26.th_26_petersburg_finite
#check @KeynesCh26.th_26_moral_expectation
#check @KeynesCh26.th_26_cramer_cap
#check @KeynesCh26.th_26_cramer_sqrt_expectation
#check @KeynesCh26.th_26_bernoulli_stake_bounds
#check @KeynesCh26.th_26_relative_risk
#check @KeynesCh26.th_26_relative_risk_tendsto
#check @KeynesCh26.th_26_laurent_limit

#print axioms KeynesCh26.th_26_fn1_second_order_risk
#print axioms KeynesCh26.th_26_fn1_printed_iff
#print axioms KeynesCh26.th_26_fn1_printed_refuted
#print axioms KeynesCh26.th_26_fn1_consistent_R
#print axioms KeynesCh26.th_26_fn1_consistent_reindexed
#print axioms KeynesCh26.th_26_fn1_czuber_tsum
#print axioms KeynesCh26.th_26_fn2_F4_printed_determinate
#print axioms KeynesCh26.th_26_fn2_F4_amended_witness_lt
#print axioms KeynesCh26.th_26_fn2_F4_amended_witness_gt
#print axioms KeynesCh26.th_26_first_head
#print axioms KeynesCh26.th_26_petersburg_term
#print axioms KeynesCh26.th_26_petersburg_term_r0
#print axioms KeynesCh26.th_26_petersburg_finite
#print axioms KeynesCh26.th_26_petersburg_unbounded
#print axioms KeynesCh26.th_26_petersburg_tendsto
#print axioms KeynesCh26.th_26_petersburg_not_summable
#print axioms KeynesCh26.th_26_bernoulli_deriv
#print axioms KeynesCh26.th_26_bernoulli_initial
#print axioms KeynesCh26.th_26_moral_expectation
#print axioms KeynesCh26.th_26_laplace_printed_refuted
#print axioms KeynesCh26.th_26_two_pow_24
#print axioms KeynesCh26.th_26_printed_16777116_refuted
#print axioms KeynesCh26.th_26_cramer_cap
#print axioms KeynesCh26.th_26_cramer_sqrt_expectation
#print axioms KeynesCh26.th_26_cramer_sqrt_stake
#print axioms KeynesCh26.th_26_cramer_sqrt_dubious
#print axioms KeynesCh26.th_26_bernoulli_summable
#print axioms KeynesCh26.th_26_bernoulli_stake_strict
#print axioms KeynesCh26.th_26_bernoulli_stake_bounds
#print axioms KeynesCh26.th_26_petersburg_risk_closed
#print axioms KeynesCh26.th_26_relative_risk
#print axioms KeynesCh26.th_26_relative_risk_tendsto
#print axioms KeynesCh26.th_26_petersburg_risk_unbounded
#print axioms KeynesCh26.th_26_laurent_poorer
#print axioms KeynesCh26.th_26_laurent_limit
#print axioms KeynesCh26.th_26_fn_leibniz_division
