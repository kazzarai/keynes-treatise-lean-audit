/-
# Keynes (1921) *A Treatise on Probability* Part V — Lean 4 Phase 15c
# 第 XXXII 章 (folio 395–404): Bortkiewicz の一般確率と Lexis の分散比 Q
# 第 XXXIII 章 (folio 412–425): 建設的理論の概略 (統計的一般化、independent・uniform・stable、Bowley の r)
#
# 対象は台帳の式行 44 本 (ch32 の 26 本と ch33 の 18 本)。
# 第 32 章の式は Keynes の確率関係 (a/h) を含まない数値の式 (加重平均・確率誤差・分散比) なので、
# 第II部の担体には置かず実数の上で述べる。独立な成分 (020)・平均のまわりの偏差 (010)・Bowley の
# 相関係数 (第 33 章 097) は Mathlib の確率測度の上の分散・共分散 (Var・cov) で述べる。
# 第 33 章 §5–§8 の統計的一般化 φ(x)/R(x, S, φ, h) . h = p は Keynes の確率関係なので、第II部の担体
# (IProp・iand・inot・PrI、phase6c と同じ型) の上に、命題関数 φ・系列 S・事例 x を変数として置く。
#
# ## 基準
#   1921 年 Macmillan 初版の頁画像のみ (folio 395, 396, 398, 399, 400, 401, 404, 412, 413, 415, 420, 421, 424, 425)。
#   定理名は th_32_<行番号>・th_33_<行番号>。反例・必要性は nec_ で始める。
#
# ## 原典
#   (folio 395、§4、Bortkiewicz) 「a proportion z₁/z of the observations may belong to a group, for which,
#    given the frequency, the à priori probability of the character under observation in a particular instance
#    would be p₁, a proportion z₂/z may belong to a second group for which p₂ is the probability, and so on. …
#    the probability p for the group as a whole would be made up as follows : p = (z₁/z)p₁ + (z₂/z)p₂ + . . . .
#    We may call p a general probability, and p, etc., special probabilities. … If p₁ = p₂ = . . . . = p, then p,
#    for that particular way of resolving the total group into partial groups, is, in Bortkiewicz's
#    terminology, indifferent.」
#   (folio 396) 「If p′ is the empirical value of p (or, as I should prefer to call it, the frequency) given by a
#    series of n observations, we may have p′ = (n₁/n)p₁′ + (n₂/n)p₂′ + . . . .」
#   (folio 398–399、§6、Lexis) 「Where the underlying probability is constant, the probable error in a
#    particular frequency à priori is r = ρ√(2v(1 − v)/g), where ρ = ·4769, v is the underlying probability, and
#    g is the number of instances to which the frequency refers. … Now let R be the corresponding expression
#    derived à posteriori by reference to the actual deviations of a series of observed frequencies from their
#    mean, so that R = ρ√(2[δ²]/(n − 1)), where [δ²] is the sum of the squares of the deviations of the
#    individual frequencies from their mean and n is their number. Now, if the observed facts are due to merely
#    chance variations about a constant v, we must have approximately R = r … If p is the probable deviation of
#    the various values of v from their mean, then … R will tend to equal not r but √(r² + p²). In this event R
#    cannot be less than r. If, therefore, R < r, one must suppose that the individual instances of each
#    several series on which each frequency is based are not independent of one another. … three types of
#    series, differing fundamentally from one another according as R = r, > r, or < r, Lexis puts R/r = Q …
#    If Q = 1, we have normal dispersion; if Q > 1, we have supernormal dispersion; and if Q < 1, we have
#    subnormal dispersion … If the number of instances on which the frequencies are based is very great, r
#    becomes negligible in comparison with p (the physical component), and, therefore, R = √(r² + p²) becomes
#    approximately R = p.」
#    脚注 1 (Tschuprow): 「Q = P/C, where P (the Physical modulus) = √(2Σ_{k=1}^{k=n}(p_k − p)²/n) and C (the
#    Combinatorial modulus) = √(2p(1 − p)/M), M being the number of instances in each set, n the number of sets,
#    p_k the frequency for set k, and p the mean of the n frequencies.」
#   (folio 400) 「the forty-five registration districts of England … approximately satisfy the relation R = r.
#    But if we take the figures for all England … nevertheless R = 2·6 and r = 1·6, so that Q = 1·625」
#   (folio 401) 「He should, I think, have contemplated the result R > r as possibly indicating a non-typical,
#    organic series, and should not have assumed that, where R is greater than r, it is of the form √(r² + p²).」
#   (folio 404、§9) 「a general probability p and special probabilities p₁ etc., where p = (z₁/z)p₁ + (z₂/z)p₂ + . . .
#    … If the à priori calculations are based on the average over a field which is not homogeneous」
#   (folio 412、第 33 章 §5) 「Let us denote the proposition ' x is, on evidence h, a random member of S for
#    characteristic φ ' by R(x, S, φ, h) ; then our statistical generalisation is of the form
#    φ(x)/R(x, S, φ, h) . h = p.」 脚注 1: 「a is a random member of S for characteristic φ, if
#    φ(a)/S(a) . h = φ(b)/S(b) . h where S(b) . h contains no information about b, except that b is a member of S」
#   (folio 413、§6) 「In the simplest case, S is a finite series of which we know the truth frequency for the
#    characteristic φ, namely f. Then by a straightforward application of the Principle of Indifference we have
#    p = f, so that φ(x)/R(x, S, φ, h) . h = f. … If this determinate proportion is known to be f, we have, as
#    before, p = f.」 脚注 1: 「I.e. if f is the proportion of the members of the series for which φ(x) is true.」
#   (folio 415) 「i.e. φ(x)/R(x, S₁, φ, h) . h = p₁, etc. … either we must have p₁ = p₂ = etc., or at least p₁, p₂,
#    etc., must be stably grouped about their mean value. … where the instance under inquiry is a member of
#    identically the same series as that from which our samples were drawn, i.e. where S = S₁」
#   (folio 420 脚注 1 → 421) 「consider the terms a₁, a₂ . . . a_n of a series s(x) ; let ' a_r is g ' ≡ g_r and let
#    g_r/h = p_r, where h is our data. Then, if g_r/g_s . . . ḡ_t . . . h = p_r for all values of r, s, . . ., t . . .,
#    the terms of the series are independent relative to h. If p₁ = p₂ = . . . = p the terms are uniform. …
#    a compounded probability 1/nΣp_r. … Let the frequencies of the series for the characteristic under inquiry
#    be x₁, x₂, . . . x_n, and let x₁/h = θ₁(x₁), i.e. θ₁(x₁) is the probability of a frequency x₁ in the first
#    series. Then if x_r/x_s . . . h = θ_r(x_r) for all values of r, s, etc., the frequencies are independent ; and
#    if θ₁(x) = θ₂(x₂) = . . . θ(x), the frequencies are stable.」
#   (folio 424–425、§9、Bowley) 「X_t = ₁U_t + ₂U_t + . . . + _pU_t + ₁V_t + ₂V_t + . . . + _qV_t
#    Y_t = ₁U_t + ₂U_t + . . . + _pU_t + ₁W_t + ₂W_t + . . . _qW_t where ₁U_t, ₂U_t . . . ₁V_t, ₂V_t . . . ₁W_t,
#    ₂W_t . . . . are selected at random each from an independent group of quantities … If the constitutions
#    of the independent groups are similar in a certain statistical respect (i.e. if they have the same
#    standard deviations), then, Dr. Bowley concludes, r = p/(p + q)」
#
# ## 記法の読み (定義のみ)
#   genProb s z zt p : Σ_{i ∈ s} (z_i/zt) p_i (003・005・033)。Indifferent : 全ての p_i が一般確率に等しい (004)。
#   probErr ρ V    : ρ√(2V) (確率誤差; V は分散)。rBern ρ v g = probErr ρ (v(1 − v)/g) (006)。
#   ρL             : ·4769 (007)。Θ t = 2/√π ∫_0^t e^{−u²} du (phase14b・15b の Θ の写し)。
#   meanN・sqDevN  : n 個の数の平均と偏差平方和 [δ²] (008)。RLex ρ x = ρ√(2[δ²]/(n − 1)) (008)。
#   Qlex R r       : R/r (016)。PT・CT・QT : Tschuprow の P・C・Q (022–024)。
#   第 33 章: IProp・iand・inot・PrI (第II部の担体と同じ型)、Inst (事例 x, a, b の型)、系列 S と命題関数 φ は
#   Inst → IProp (S(x) は「x は類 S の成員」)、R x S φ h (「x は証拠 h のもとで特性 φ について S の random member」)、
#   StatGen φ S h p (016: すべての x で φ(x)/R(x, S, φ, h) . h = p)、tfreq S φ (S の φ の真理頻度 f)、
#   KnowsFreq h S φ (証拠 h は S の φ の真理頻度を知らせる)、gr・pr・prem (037–039)、fq r x (「第 r 系列の頻度は x」)、
#   θ h r x = fq r x / h (043)、Xt・Yt (095・096)、corr (相関係数 cov/√(Var·Var))。
#
# ## 外部公理 (Keynes の公理から出ないもの)
#   ax_freq_eq_prob : 証拠 h が S の φ の真理頻度を知らせるなら、random member x について
#     φ(x)/R(x, S, φ, h) . h = tfreq S φ。folio 413 の「by a straightforward application of the Principle of
#     Indifference we have p = f」の結論を公理に置く (B43 第 8 章の同名の公理と同じく「確率 = 頻度」の等置;
#     この phase は B43 の phase を import しない)。021・022・026 がこれに依る。外すと th_33_021・th_33_022・
#     th_33_026 が通らない (Unknown identifier) ことを確かめた。公理なしでは出ないことは th_33_022_needs_ax。
#   それ以外の定理は外部公理に依らない (Θ の数値評価・分散・共分散は Mathlib から証明した)。
#
# ## 所見候補
#   F33.1 (046): θ₁(x) = θ₂(x₂) = . . . θ(x) の引数が不揃い。全ての x について読むと θ が定数に限られる
#           (nec_33_046)。修正形は θ₁(x) = θ₂(x) = . . . = θ(x) (全ての系列で頻度の確率の関数が同じ、th_33_046_fix)。
#           依頼の修正案 θ₁(x₁) = θ₂(x₂) = … も x₁・x₂ を全てにわたらせると同じく定数に限られる (nec_33_046_x1x2)。
#   F32.1 案 (022–024): Tschuprow の P は n で割り、Lexis の R は n − 1 で割る。v = p、g = M なら
#           P/C = (R/r) √((n − 1)/n) で、「Q = P/C」は Lexis の Q と一致しない (th_32_022_lexis)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_v_phase15c_lexis_constructive.lean
-/
import Mathlib

namespace KeynesXXXc

open Real Finset Filter Topology MeasureTheory ProbabilityTheory

/-! ## 第 32 章 §4 (folio 395–396・404): 003・004・005・033 -/

/-- 一般確率 (003): Σ_{i ∈ s} (z_i/zt) p_i。zt は全体の数 z (「a proportion z₁/z」)。 -/
noncomputable def genProb {ι : Type*} (s : Finset ι) (z : ι → ℝ) (zt : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (z i / zt) * p i

/-- ch32-003 (定): p = (z₁/z)p₁ + (z₂/z)p₂ + . . . (一般確率の定義)。 -/
theorem th_32_003 {ι : Type*} (s : Finset ι) (z : ι → ℝ) (zt : ℝ) (p : ι → ℝ) :
    genProb s z zt p = ∑ i ∈ s, (z i / zt) * p i := rfl

/-- 003 の性質: z = Σ z_i (> 0) なら重み z_i/z の和は 1。 -/
theorem genProb_weights {ι : Type*} (s : Finset ι) (z : ι → ℝ) (zt : ℝ) (hz : zt = ∑ i ∈ s, z i)
    (hpos : 0 < zt) : ∑ i ∈ s, z i / zt = 1 := by
  rw [← Finset.sum_div, ← hz, div_self hpos.ne']

/-- 003 の性質: z = Σ z_i、z_i ≥ 0 なら、一般確率は特殊確率の下界と上界の間にある。 -/
theorem genProb_between {ι : Type*} (s : Finset ι) (z : ι → ℝ) (zt : ℝ) (hz : zt = ∑ i ∈ s, z i)
    (hpos : 0 < zt) (hz0 : ∀ i ∈ s, 0 ≤ z i) (p : ι → ℝ) (lo hi : ℝ)
    (hp : ∀ i ∈ s, lo ≤ p i ∧ p i ≤ hi) : lo ≤ genProb s z zt p ∧ genProb s z zt p ≤ hi := by
  have hw := genProb_weights s z zt hz hpos
  unfold genProb
  constructor
  · calc lo = ∑ i ∈ s, (z i / zt) * lo := by rw [← Finset.sum_mul, hw, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i hi' =>
          mul_le_mul_of_nonneg_left (hp i hi').1 (div_nonneg (hz0 i hi') hpos.le))
  · calc ∑ i ∈ s, (z i / zt) * p i ≤ ∑ i ∈ s, (z i / zt) * hi := Finset.sum_le_sum (fun i hi' =>
          mul_le_mul_of_nonneg_left (hp i hi').2 (div_nonneg (hz0 i hi') hpos.le))
      _ = hi := by rw [← Finset.sum_mul, hw, one_mul]

/-- 004 の「indifferent」: 全ての特殊確率が一般確率に等しい (p₁ = p₂ = . . . . = p)。 -/
def Indifferent {ι : Type*} (s : Finset ι) (z : ι → ℝ) (zt : ℝ) (p : ι → ℝ) : Prop :=
  ∀ i ∈ s, p i = genProb s z zt p

/-- ch32-004 (定): z = Σ z_i (> 0) のとき、indifferent であることは特殊確率が互いに等しいことと同値
(等号連鎖 p₁ = p₂ = . . . . の共通の値は一般確率 p に等しい)。 -/
theorem th_32_004 {ι : Type*} (s : Finset ι) (z : ι → ℝ) (zt : ℝ) (hz : zt = ∑ i ∈ s, z i)
    (hpos : 0 < zt) (p : ι → ℝ) :
    Indifferent s z zt p ↔ ∀ i ∈ s, ∀ j ∈ s, p i = p j := by
  constructor
  · intro h i hi j hj; rw [h i hi, h j hj]
  · intro h i hi
    have hw := genProb_weights s z zt hz hpos
    unfold genProb
    calc p i = ∑ k ∈ s, (z k / zt) * p i := by rw [← Finset.sum_mul, hw, one_mul]
      _ = ∑ k ∈ s, (z k / zt) * p k :=
          Finset.sum_congr rfl (fun k hk => by rw [h i hi k hk])

/-- ch32-005 (定): 経験値 (頻度) p′ = (n₁/n)p₁′ + (n₂/n)p₂′ + . . . . (003 と同じ形の定義)。 -/
theorem th_32_005 {ι : Type*} (s : Finset ι) (n : ι → ℝ) (nt : ℝ) (p' : ι → ℝ) :
    genProb s n nt p' = ∑ i ∈ s, (n i / nt) * p' i := rfl

/-- ch32-033 (定、003 の再掲) の補助: 「the average over a field」。群 i が z_i 個の成員を持ち、そのうち k_i 個が
特性を持つとき、特殊確率を群の割合 p_i = k_i/z_i と読むと、場全体の割合 (Σ k_i)/z は
p = (z₁/z)p₁ + (z₂/z)p₂ + . . . に等しい (z = Σ z_i)。p_i = k_i/z_i は印刷にない読み。 -/
theorem th_32_033 {ι : Type*} (s : Finset ι) (z k : ι → ℝ)
    (hz0 : ∀ i ∈ s, 0 < z i) (p : ι → ℝ) (hp : ∀ i ∈ s, p i = k i / z i) :
    (∑ i ∈ s, k i) / (∑ i ∈ s, z i) = genProb s z (∑ i ∈ s, z i) p := by
  unfold genProb
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [hp i hi]
  have := (hz0 i hi).ne'
  field_simp

/-! ## 第 32 章 §6 (folio 398–400): 確率誤差 r・R と分散比 Q -/

/-- 確率誤差 ρ√(2V) (V は分散)。 -/
noncomputable def probErr (ρ V : ℝ) : ℝ := ρ * √(2 * V)

/-- 006 の r: ρ√(2v(1 − v)/g) を probErr ρ (v(1 − v)/g) と書く。 -/
noncomputable def rBern (ρ v g : ℝ) : ℝ := probErr ρ (v * (1 - v) / g)

/-- ch32-006 (定): r = ρ√(2v(1 − v)/g)。 -/
theorem th_32_006 (ρ v g : ℝ) : rBern ρ v g = ρ * √(2 * v * (1 - v) / g) := by
  unfold rBern probErr; congr 2; ring

/-- 007 の ρ = ·4769。 -/
noncomputable def ρL : ℝ := 4769 / 10000

/-- Θ(t) = 2/√π ∫_0^t e^{−u²} du (phase14b・phase15b の Θ の写し)。 -/
noncomputable def Θ (t : ℝ) : ℝ := 2 / √π * ∫ u in (0 : ℝ)..t, exp (-(u ^ 2))

/-- e^{−u²} の Taylor 多項式 (5 項)。 -/
noncomputable def T5 (u : ℝ) : ℝ := 1 - u ^ 2 + u ^ 4 / 2 - u ^ 6 / 6 + u ^ 8 / 24

theorem exp_neg_sq_bound (u : ℝ) (hu : |u| ≤ 1) :
    |exp (-(u ^ 2)) - T5 u| ≤ u ^ 10 / 100 := by
  have hx : |(-(u ^ 2))| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg u)]
    have : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    rw [this]; exact pow_le_one₀ (abs_nonneg u) hu
  have h := Real.exp_bound hx (n := 5) (by norm_num)
  have e : ∑ i ∈ range 5, (-(u ^ 2)) ^ i / (i.factorial : ℝ) = T5 u := by
    simp [Finset.sum_range_succ, T5, Nat.factorial]; ring
  rw [e] at h
  have e2 : |(-(u ^ 2))| ^ 5 * ((Nat.succ 5 : ℕ) / ((Nat.factorial 5 : ℕ) * (5 : ℕ)) : ℝ)
      = u ^ 10 / 100 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg u)]; norm_num [Nat.factorial]; ring
  push_cast at h e2
  linarith

theorem int_T5_lo (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ u in (0 : ℝ)..t, (T5 u - u ^ 10 / 100) ≤ ∫ u in (0 : ℝ)..t, exp (-(u ^ 2)) := by
  apply intervalIntegral.integral_mono_on ht0
  · apply Continuous.intervalIntegrable; unfold T5; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  · intro u hu
    have hu' : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have := exp_neg_sq_bound u hu'
    rw [abs_le] at this; linarith [this.1]

theorem int_T5_hi (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ u in (0 : ℝ)..t, exp (-(u ^ 2)) ≤ ∫ u in (0 : ℝ)..t, (T5 u + u ^ 10 / 100) := by
  apply intervalIntegral.integral_mono_on ht0
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; unfold T5; fun_prop
  · intro u hu
    have hu' : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have := exp_neg_sq_bound u hu'
    rw [abs_le] at this; linarith [this.2]

theorem int_T5 (t c : ℝ) :
    ∫ u in (0 : ℝ)..t, (T5 u + c * u ^ 10) =
      t - t ^ 3 / 3 + t ^ 5 / 10 - t ^ 7 / 42 + t ^ 9 / 216 + c * t ^ 11 / 11 := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt
      (fun u : ℝ => u - u ^ 3 / 3 + u ^ 5 / 10 - u ^ 7 / 42 + u ^ 9 / 216 + c * u ^ 11 / 11)
      (T5 x + c * x ^ 10) x := by
    intro x _
    have := ((((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3)).add
      ((hasDerivAt_pow 5 x).div_const 10)).sub ((hasDerivAt_pow 7 x).div_const 42)).add
      ((hasDerivAt_pow 9 x).div_const 216)).add (((hasDerivAt_pow 11 x).const_mul c).div_const 11))
    convert this using 1
    unfold T5; norm_num; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; unfold T5; fun_prop)]
  ring

theorem sqrt_pi_lo : (177245 / 100000 : ℝ) < √π := by
  rw [Real.lt_sqrt (by norm_num)]; linarith [Real.pi_gt_d6]

theorem sqrt_pi_hi : √π < 177246 / 100000 := by
  rw [Real.sqrt_lt' (by norm_num)]; linarith [Real.pi_lt_d6]

/-- Θ(·4769) < 1/2。 -/
theorem Θ_lo : Θ (4769 / 10000) < 1 / 2 := by
  unfold Θ
  have h := int_T5_hi (4769 / 10000) (by norm_num) (by norm_num)
  have e := int_T5 (4769 / 10000) (1 / 100)
  have e' : ∫ u in (0 : ℝ)..(4769 / 10000), (T5 u + u ^ 10 / 100) =
      ∫ u in (0 : ℝ)..(4769 / 10000), (T5 u + 1 / 100 * u ^ 10) := by
    congr 1; funext u; ring
  rw [e', e] at h
  have hs := sqrt_pi_lo
  have hpos : 0 < √π := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
  nlinarith

/-- 1/2 < Θ(·47695)。 -/
theorem Θ_hi : 1 / 2 < Θ (47695 / 100000) := by
  unfold Θ
  have h := int_T5_lo (47695 / 100000) (by norm_num) (by norm_num)
  have e := int_T5 (47695 / 100000) (-(1 / 100))
  have e' : ∫ u in (0 : ℝ)..(47695 / 100000), (T5 u - u ^ 10 / 100) =
      ∫ u in (0 : ℝ)..(47695 / 100000), (T5 u + -(1 / 100) * u ^ 10) := by
    congr 1; funext u; ring
  rw [e', e] at h
  have hs := sqrt_pi_hi
  have hpos : 0 < √π := by positivity
  rw [div_mul_eq_mul_div, lt_div_iff₀ hpos]
  nlinarith

/-- Θ は狭義単調増加。 -/
theorem Θ_strictMono : StrictMono Θ := by
  intro a b hab
  unfold Θ
  apply mul_lt_mul_of_pos_left _ (by positivity)
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun u => exp (-(u ^ 2))) volume x y :=
    fun x y => (by fun_prop : Continuous fun u : ℝ => exp (-(u ^ 2))).intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)]
  have : 0 < ∫ u in a..b, exp (-(u ^ 2)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hi a b) (fun x _ => exp_pos _) hab
  linarith

theorem Θ_continuous : Continuous Θ := by
  unfold Θ
  apply Continuous.mul continuous_const
  exact intervalIntegral.continuous_primitive
    (fun x y => (by fun_prop : Continuous fun u : ℝ => exp (-(u ^ 2))).intervalIntegrable x y) 0

/-- ch32-007 (≈、数値評価): 確率誤差の定数 ρ は Θ(ρ) = 1/2 (= erf(ρ) = 1/2、「probable error」は半分の確率で
超えられる偏差) のただ 1 つの根で、その根は ·4769 と ·47695 の間にある (小数 4 位に丸めると ρ = ·4769)。 -/
theorem th_32_007 :
    ∃! t : ℝ, Θ t = 1 / 2 ∧ ρL < t ∧ t < 47695 / 100000 := by
  have hc : ContinuousOn Θ (Set.Icc ρL (47695 / 100000)) := Θ_continuous.continuousOn
  have hlo := Θ_lo
  have hhi := Θ_hi
  obtain ⟨t, ht, hΘ⟩ := intermediate_value_Icc (by unfold ρL; norm_num) hc
    ⟨(by unfold ρL; exact hlo.le), hhi.le⟩
  have h1 : ρL < t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h] at hΘ; unfold ρL at hΘ; linarith
    · exact h
  have h2 : t < 47695 / 100000 := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h] at hΘ; linarith
    · exact h
  refine ⟨t, ⟨hΘ, h1, h2⟩, fun s hs => Θ_strictMono.injective (hs.1.trans hΘ.symm)⟩

/-- n 個の数の平均。 -/
noncomputable def meanN {n : ℕ} (x : Fin n → ℝ) : ℝ := (1 / (n : ℝ)) * ∑ k, x k

/-- 偏差平方和 [δ²] = Σ (x_k − x̄)² (008)。 -/
noncomputable def sqDevN {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ k, (x k - meanN x) ^ 2

/-- 008 の R: ρ√(2[δ²]/(n − 1))。 -/
noncomputable def RLex (ρ : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ := probErr ρ (sqDevN x / ((n : ℝ) - 1))

/-- ch32-008 (定): R = ρ√(2[δ²]/(n − 1))。 -/
theorem th_32_008 (ρ : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    RLex ρ x = ρ * √(2 * sqDevN x / ((n : ℝ) - 1)) := by
  unfold RLex probErr; congr 2; ring

/-- 平均のまわりの偏差平方和の期待値 (偏りのない分散): 頻度 X_1, …, X_n が互いに無相関で、平均が同じ、
分散が同じ σ² なら E[[δ²]] = (n − 1)σ²。 -/
theorem sqDev_expect {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hX : ∀ k, MemLp (X k) 2 μ) (m σ2 : ℝ)
    (hm : ∀ k, μ[X k] = m) (hv : ∀ k, Var[X k; μ] = σ2)
    (hc : ∀ k l, k ≠ l → cov[X k, X l; μ] = 0) :
    ∫ ω, sqDevN (fun k => X k ω) ∂μ = ((n : ℝ) - 1) * σ2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set M : Ω → ℝ := fun ω => meanN (fun k => X k ω) with hMdef
  have mS : MemLp (∑ k, X k) 2 μ := memLp_finset_sum' _ (fun k _ => hX k)
  have eM : M = (1 / (n : ℝ)) • ∑ k, X k := by
    funext ω; simp [hMdef, meanN, Finset.sum_apply]
  have mM : MemLp M 2 μ := by rw [eM]; exact mS.const_smul _
  have mD : ∀ k, MemLp (X k - M) 2 μ := fun k => (hX k).sub mM
  have intM : μ[M] = m := by
    rw [eM]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [integral_const_mul, integral_finset_sum _ (fun k _ => (hX k).integrable one_le_two)]
    simp [hm]; field_simp
  have cXM : ∀ k, cov[X k, M; μ] = σ2 / n := by
    intro k
    rw [eM, covariance_smul_right, covariance_sum_right hX (hX k)]
    rw [Finset.sum_eq_single k (fun b _ hb => hc k b (Ne.symm hb)) (by simp),
      covariance_self (hX k).aemeasurable, hv k]
    ring
  have vM : Var[M; μ] = σ2 / n := by
    rw [eM, variance_smul, variance_sum hX]
    have : ∀ i, ∑ j, cov[X i, X j; μ] = σ2 := by
      intro i
      rw [Finset.sum_eq_single i (fun b _ hb => hc i b (Ne.symm hb)) (by simp),
        covariance_self (hX i).aemeasurable, hv i]
    simp [this]; field_simp
  have eD : ∀ k, μ[fun ω => (X k ω - M ω) ^ 2] = σ2 * ((n - 1) / n) := by
    intro k
    have h1 := variance_eq_sub (mD k)
    have h0 : μ[X k - M] = 0 := by
      simp only [Pi.sub_apply]
      rw [integral_sub ((hX k).integrable one_le_two) (mM.integrable one_le_two), hm k, intM]; ring
    rw [h0] at h1
    rw [variance_sub (hX k) mM, hv k, cXM k, vM] at h1
    have : (fun ω => (X k ω - M ω) ^ 2) = (X k - M) ^ 2 := by funext ω; simp
    rw [this]
    field_simp at h1 ⊢
    linarith
  have eS : (fun ω => sqDevN (fun k => X k ω)) = fun ω => ∑ k, (X k ω - M ω) ^ 2 := rfl
  rw [eS, integral_finset_sum _ (fun k _ => by
    have := (mD k).integrable_sq
    simpa using this)]
  simp only [eD]
  simp
  field_simp

/-- ch32-010 (≈): 「if the observed facts are due to merely chance variations about a constant v, we must have
approximately R = r」。n 個の頻度が互いに無相関で、平均が同じ、分散がどれも v(1 − v)/g (g 事例の頻度の分散)
なら、R² の期待値は r² に等しい (「approximately R = r」を E[R²] = r² と読む)。 -/
theorem th_32_010 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ρ v g : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hg : 0 < g)
    (n : ℕ) (hn : 2 ≤ n) (X : Fin n → Ω → ℝ) (hX : ∀ k, MemLp (X k) 2 μ) (m : ℝ)
    (hm : ∀ k, μ[X k] = m) (hvar : ∀ k, Var[X k; μ] = v * (1 - v) / g)
    (hc : ∀ k l, k ≠ l → cov[X k, X l; μ] = 0) :
    ∫ ω, (RLex ρ (fun k => X k ω)) ^ 2 ∂μ = (rBern ρ v g) ^ 2 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hS := sqDev_expect n (by omega) X hX m _ hm hvar hc
  have hnn : ∀ ω, 0 ≤ sqDevN (fun k => X k ω) := fun ω =>
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have e : ∀ ω, (RLex ρ (fun k => X k ω)) ^ 2
      = (2 * ρ ^ 2 / ((n : ℝ) - 1)) * sqDevN (fun k => X k ω) := by
    intro ω
    unfold RLex probErr
    have hn1' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    rw [mul_pow, Real.sq_sqrt (by have := hnn ω; positivity)]
    field_simp
  simp only [e]
  rw [integral_const_mul, hS]
  unfold rBern probErr
  have : 0 ≤ v * (1 - v) / g := div_nonneg (mul_nonneg hv0 (by linarith)) hg.le
  have hn1' : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- 016 の分散比 Q = R/r。 -/
noncomputable def Qlex (R r : ℝ) : ℝ := R / r

/-- ch32-016 (定): R/r = Q。 -/
theorem th_32_016 (R r : ℝ) : Qlex R r = R / r := rfl

/-- ch32-017 (✓): r > 0 のとき Q = 1 (normal dispersion) ⇔ R = r (013 の第 1 の型)。 -/
theorem th_32_017 (R r : ℝ) (hr : 0 < r) : Qlex R r = 1 ↔ R = r := by
  unfold Qlex; rw [div_eq_one_iff_eq hr.ne']

/-- ch32-018 (✓): r > 0 のとき Q > 1 (supernormal) ⇔ R > r (014)。 -/
theorem th_32_018 (R r : ℝ) (hr : 0 < r) : Qlex R r > 1 ↔ R > r := by
  unfold Qlex; rw [gt_iff_lt, one_lt_div hr]

/-- ch32-019 (✓): r > 0 のとき Q < 1 (subnormal) ⇔ R < r (015)。 -/
theorem th_32_019 (R r : ℝ) (hr : 0 < r) : Qlex R r < 1 ↔ R < r := by
  unfold Qlex; rw [div_lt_one hr]

/-- 017–019 の三分法: Q = 1・Q > 1・Q < 1 のどれか 1 つだけが成り立つ (網羅的かつ排他的)。 -/
theorem th_32_Q_trichotomy (R r : ℝ) :
    (Qlex R r = 1 ∨ Qlex R r > 1 ∨ Qlex R r < 1) ∧
    ¬ (Qlex R r = 1 ∧ Qlex R r > 1) ∧ ¬ (Qlex R r = 1 ∧ Qlex R r < 1) ∧
    ¬ (Qlex R r > 1 ∧ Qlex R r < 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases lt_trichotomy (Qlex R r) 1 with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro ⟨h1, h2⟩; rw [h1] at h2; exact lt_irrefl _ h2
  · rintro ⟨h1, h2⟩; rw [h1] at h2; exact lt_irrefl _ h2
  · rintro ⟨h1, h2⟩; exact lt_irrefl _ (h2.trans h1)

/-- 011 の補助: 「In this event R cannot be less than r」— r ≥ 0 なら √(r² + p²) ≥ r。 -/
theorem th_32_011 (r p : ℝ) (hr : 0 ≤ r) : r ≤ √(r ^ 2 + p ^ 2) := by
  rw [Real.le_sqrt hr (by positivity)]; nlinarith [sq_nonneg p]

/-- ch32-012 (≈): 「If, therefore, R < r」— R < r (r ≥ 0) なら R はどの p についても √(r² + p²) の形でない
(独立な 2 成分の形は成り立たない; 「one must suppose … not independent」の論理の部分)。 -/
theorem th_32_012 (R r : ℝ) (hr : 0 ≤ r) (hRr : R < r) : ∀ p : ℝ, R ≠ √(r ^ 2 + p ^ 2) := by
  intro p h
  have := th_32_011 r p hr
  rw [← h] at this
  linarith

/-- ch32-020 (≈): 頻度の偏差が独立な 2 成分 A (ordinary) と B (physical) の和なら、和の確率誤差は
各成分の確率誤差 r・p から R = √(r² + p²)。独立な確率変数の分散の加法性 (Mathlib の IndepFun.variance_add) による。
左辺の R を和の母分散の確率誤差 probErr ρ Var[A + B] に置き換えた定義の代入 (010 と同じ扱い); 印刷の R は
008 の偏差平方和による à posteriori の値で、「R will tend to equal」の近さは扱っていない。 -/
theorem th_32_020 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 ≤ ρ) (A B : Ω → ℝ) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hAB : A ⟂ᵢ[μ] B) :
    probErr ρ (Var[A + B; μ]) = √((probErr ρ (Var[A; μ])) ^ 2 + (probErr ρ (Var[B; μ])) ^ 2) := by
  rw [hAB.variance_add hA hB]
  unfold probErr
  have h1 := variance_nonneg A μ
  have h2 := variance_nonneg B μ
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  rw [show ρ ^ 2 * (2 * Var[A; μ]) + ρ ^ 2 * (2 * Var[B; μ])
      = ρ ^ 2 * (2 * (Var[A; μ] + Var[B; μ])) by ring]
  rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ]

/-- ch32-021 (≈): 「r becomes negligible in comparison with p … R = √(r² + p²) becomes approximately R = p」—
r → 0 で √(r² + p²) → p (p ≥ 0)。 -/
theorem th_32_021 (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun r : ℝ => √(r ^ 2 + p ^ 2)) (𝓝 0) (𝓝 p) := by
  have h : Tendsto (fun r : ℝ => √(r ^ 2 + p ^ 2)) (𝓝 0) (𝓝 (√((0 : ℝ) ^ 2 + p ^ 2))) :=
    ((continuous_pow 2).add continuous_const).sqrt.tendsto 0
  rwa [show (0 : ℝ) ^ 2 + p ^ 2 = p ^ 2 by ring, Real.sqrt_sq hp] at h

/-- 021 の後の文 (folio 399–400): 「p becomes negligible」のときは p → 0 で √(r² + p²) → r
(「a delusive appearance of normal dispersion」)。 -/
theorem th_32_021_r (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun p : ℝ => √(r ^ 2 + p ^ 2)) (𝓝 0) (𝓝 r) := by
  have h : Tendsto (fun p : ℝ => √(r ^ 2 + p ^ 2)) (𝓝 0) (𝓝 (√(r ^ 2 + (0 : ℝ) ^ 2))) :=
    (continuous_const.add (continuous_pow 2)).sqrt.tendsto 0
  rwa [show r ^ 2 + (0 : ℝ) ^ 2 = r ^ 2 by ring, Real.sqrt_sq hr] at h

/-- 024 の C (the Combinatorial modulus) = √(2p(1 − p)/M)。 -/
noncomputable def CT (p M : ℝ) : ℝ := √(2 * p * (1 - p) / M)

/-- 023 の P (the Physical modulus) = √(2Σ_{k=1}^{k=n}(p_k − p)²/n)、p は n 個の頻度の平均。 -/
noncomputable def PT {n : ℕ} (pk : Fin n → ℝ) : ℝ := √(2 * sqDevN pk / n)

/-- 022 の Q = P/C (Tschuprow の記法)。 -/
noncomputable def QT {n : ℕ} (pk : Fin n → ℝ) (M : ℝ) : ℝ := PT pk / CT (meanN pk) M

/-- ch32-022 (定): Q = P/C。 -/
theorem th_32_022 {n : ℕ} (pk : Fin n → ℝ) (M : ℝ) : QT pk M = PT pk / CT (meanN pk) M := rfl

/-- ch32-023 (定): P = √(2Σ(p_k − p)²/n)、p は平均。 -/
theorem th_32_023 {n : ℕ} (pk : Fin n → ℝ) :
    PT pk = √(2 * (∑ k, (pk k - meanN pk) ^ 2) / n) := rfl

/-- ch32-024 (定): C = √(2p(1 − p)/M)。 -/
theorem th_32_024 (p M : ℝ) : CT p M = √(2 * p * (1 - p) / M) := rfl

/-- 022 の補助 (F32.1 案): v = p (平均)、g = M、ρ > 0 なら Tschuprow の P/C は Lexis の R/r と
√((n − 1)/n) 倍だけ違う (P は n で、R は n − 1 で割る)。 -/
theorem th_32_022_lexis (ρ : ℝ) (hρ : 0 < ρ) {n : ℕ} (hn : 2 ≤ n) (pk : Fin n → ℝ) (M : ℝ) (hM : 0 < M)
    (hp0 : 0 < meanN pk) (hp1 : meanN pk < 1) :
    QT pk M = Qlex (RLex ρ pk) (rBern ρ (meanN pk) M) * √(((n : ℝ) - 1) / n) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1' : (n : ℝ) - 1 ≠ 0 := by linarith
  have hS : 0 ≤ sqDevN pk := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  unfold QT PT CT Qlex RLex rBern probErr
  generalize sqDevN pk = s at hS ⊢
  generalize meanN pk = v at hp0 hp1 ⊢
  have hC : 0 < 2 * v * (1 - v) / M := by
    have : 0 < 1 - v := by linarith
    positivity
  have e1 : 2 * (v * (1 - v) / M) = 2 * v * (1 - v) / M := by ring
  have e2 : 2 * s / (n : ℝ) = 2 * (s / ((n : ℝ) - 1)) * (((n : ℝ) - 1) / n) := by
    field_simp
  rw [e1, e2, Real.sqrt_mul (by have : 0 ≤ s / ((n : ℝ) - 1) := div_nonneg hS (by linarith); positivity)]
  have hsC : 0 < √(2 * v * (1 - v) / M) := Real.sqrt_pos.mpr hC
  field_simp

/-- ch32-028 (✓、数値評価): 026・027 の値 R = 2·6、r = 1·6 (前提 h026・h027) と 016 の Q = R/r から
Q = 1·625。 -/
theorem th_32_028 (R r Q : ℝ) (h026 : R = 2.6) (h027 : r = 1.6) (h016 : Q = Qlex R r) :
    Q = 1.625 := by
  rw [h016, h026, h027]; unfold Qlex; norm_num

/-- ch32-029 (✓): 「the result R > r」— Lexis の形 R = √(r² + p²) で physical component p ≠ 0、r ≥ 0 なら R > r。 -/
theorem th_32_029 (R r p : ℝ) (hr : 0 ≤ r) (hp : p ≠ 0) (hR : R = √(r ^ 2 + p ^ 2)) : R > r := by
  rw [hR, gt_iff_lt, Real.lt_sqrt hr]
  have := pow_pos (abs_pos.mpr hp) 2
  rw [sq_abs] at this
  linarith

/-- 029 の補助: R > r の結果は分散比では Q > 1 (supernormal、018) にあたる。逆に R > r の R はどれも
p = √(R² − r²) と置けば √(r² + p²) の形に書けるので、形だけからは organic な系列と区別できない
(folio 401「should not have assumed that, where R is greater than r, it is of the form √(r² + p²)」)。 -/
theorem th_32_029_form (R r : ℝ) (hr : 0 ≤ r) (hRr : R > r) :
    ∃ p : ℝ, p ≠ 0 ∧ R = √(r ^ 2 + p ^ 2) := by
  have hR0 : 0 < R := lt_of_le_of_lt hr hRr
  have hpos : 0 < R ^ 2 - r ^ 2 := by nlinarith
  refine ⟨√(R ^ 2 - r ^ 2), (Real.sqrt_pos.mpr hpos).ne', ?_⟩
  rw [Real.sq_sqrt hpos.le, show r ^ 2 + (R ^ 2 - r ^ 2) = R ^ 2 by ring, Real.sqrt_sq hR0.le]

/-! ## 第 33 章 §5–§8 (folio 412–421): 第II部の担体の上の統計的一般化 -/

/-- 命題 (第II部の担体と同じ型、phase6c と同文; import しない)。 -/
axiom IProp : Type
/-- 連言 (前提の並置 hh₁ は iand h h₁、印刷の順)。 -/
axiom iand : IProp → IProp → IProp
/-- 否定 (ḡ_t)。 -/
axiom inot : IProp → IProp
/-- 確率関係 a/h の値 (phase6c と同文)。 -/
axiom PrI : IProp → IProp → ℝ
/-- 事例 (x, a, b, a_r) の型。 -/
axiom Inst : Type
/-- R(x, S, φ, h): 「x is, on evidence h, a random member of S for characteristic φ」(folio 412)。
系列 S と特性 φ は命題関数 Inst → IProp (S(x) は「x is a member of the class S」)。 -/
axiom R : Inst → (Inst → IProp) → (Inst → IProp) → IProp → IProp

/-- 016 の統計的一般化: すべての x で φ(x)/R(x, S, φ, h) . h = p (前提は印刷の順に R(x, S, φ, h) . h)。
x は自由変数として印刷されている (脚注 1「The use of variables in probability … is very dangerous」) ので、
全ての事例にわたる形で読む。 -/
def StatGen (φ S : Inst → IProp) (h : IProp) (p : ℝ) : Prop :=
  ∀ x : Inst, PrI (φ x) (iand (R x S φ h) h) = p

/-- ch33-016 (定): φ(x)/R(x, S, φ, h) . h = p。 -/
theorem th_33_016 (φ S : Inst → IProp) (h : IProp) (p : ℝ) :
    StatGen φ S h p ↔ ∀ x : Inst, PrI (φ x) (iand (R x S φ h) h) = p := Iff.rfl

/-- 018 (脚注 1) の変数を使わない言い換え: φ(a)/S(a) . h = φ(b)/S(b) . h
(b は「S(b) . h contains no information about b, except that b is a member of S」となる事例)。 -/
def RandomMemberFn (S φ : Inst → IProp) (h : IProp) (a b : Inst) : Prop :=
  PrI (φ a) (iand (S a) h) = PrI (φ b) (iand (S b) h)

/-- ch33-018 (定): a is a random member of S for characteristic φ, if φ(a)/S(a) . h = φ(b)/S(b) . h。 -/
theorem th_33_018 (S φ : Inst → IProp) (h : IProp) (a b : Inst) :
    RandomMemberFn S φ h a b ↔ PrI (φ a) (iand (S a) h) = PrI (φ b) (iand (S b) h) := Iff.rfl

/-- S の特性 φ の真理頻度 f (folio 413 脚注 1「the proportion of the members of the series for which φ(x) is true」;
原子からなる無限の系列では「determinate proportion」)。 -/
axiom tfreq : (Inst → IProp) → (Inst → IProp) → ℝ
/-- 証拠 h は S の φ の真理頻度を知らせる (「of which we know the truth frequency」「is known to be f」)。 -/
axiom KnowsFreq : IProp → (Inst → IProp) → (Inst → IProp) → Prop

/-- **外部公理: 頻度と確率の一致** (folio 413「by a straightforward application of the Principle of
Indifference we have p = f」の結論; B43 第 8 章の同名の公理と同じく「確率 = 頻度」の等置で、Keynes の第II部の
公理からは出ない)。h が S の φ の真理頻度を知らせるなら、random member x について φ(x)/R(x, S, φ, h) . h = f。 -/
axiom ax_freq_eq_prob (h : IProp) (S φ : Inst → IProp) (hK : KnowsFreq h S φ) (x : Inst) :
    PrI (φ x) (iand (R x S φ h) h) = tfreq S φ

/-- ax_freq_eq_prob の形の等式は、真理頻度と「知らせる」の割り当てが何であっても満たせる
(確率を (x, S, φ, h) の関数として f を返すものにとればよい)。 -/
theorem ax_freq_eq_prob_sat {I Γ : Type} (tf : (I → Γ) → (I → Γ) → ℝ)
    (Kn : Γ → (I → Γ) → (I → Γ) → Prop) :
    ∃ K : I → (I → Γ) → (I → Γ) → Γ → ℝ, ∀ h S φ, Kn h S φ → ∀ x, K x S φ h = tf S φ :=
  ⟨fun _ S φ _ => tf S φ, fun _ _ _ _ _ => rfl⟩

/-- ch33-022 (外部公理依存): φ(x)/R(x, S, φ, h) . h = f (f は真理頻度)。 -/
theorem th_33_022 (h : IProp) (S φ : Inst → IProp) (hK : KnowsFreq h S φ) :
    StatGen φ S h (tfreq S φ) :=
  fun x => ax_freq_eq_prob h S φ hK x

/-- ch33-021 (外部公理依存): 有限の系列 S の真理頻度 f を知っているとき、統計的一般化の値 p は p = f
(事例が 1 つでもあれば; 前提 a)。 -/
theorem th_33_021 (h : IProp) (S φ : Inst → IProp) (hK : KnowsFreq h S φ) (p : ℝ)
    (hp : StatGen φ S h p) (a : Inst) : p = tfreq S φ := by
  rw [← hp a]; exact ax_freq_eq_prob h S φ hK a

/-- ch33-026 (外部公理依存): 原子からなる系列 S の φ の決まった割合 f が知られているとき、「as before」p = f
(021 と同じ公理に依る; 真理頻度 tfreq を決まった割合と読む)。 -/
theorem th_33_026 (h : IProp) (S φ : Inst → IProp) (hK : KnowsFreq h S φ) (p : ℝ)
    (hp : StatGen φ S h p) (a : Inst) : p = tfreq S φ :=
  th_33_021 h S φ hK p hp a

/-- 022 の外部公理の必要性 (th_33_022 から ax_freq_eq_prob を落とした形): 命題・事例・確率・R・真理頻度・
「知らせる」を自由にとれるとすると、h が真理頻度を知らせるのに φ(x)/R(x, S, φ, h) . h ≠ f の模型がある
(命題も事例も 1 つ、確率はいつも 0、真理頻度は 1)。定理文に IProp・PrI・R・tfreq・ax_freq_eq_prob は現れない。 -/
theorem th_33_022_needs_ax :
    ¬ ∀ (Γ I : Type) (and' : Γ → Γ → Γ) (Pr : Γ → Γ → ℝ) (R' : I → (I → Γ) → (I → Γ) → Γ → Γ)
      (tf : (I → Γ) → (I → Γ) → ℝ) (Kn : Γ → (I → Γ) → (I → Γ) → Prop)
      (h : Γ) (S φ : I → Γ) (x : I), Kn h S φ → Pr (φ x) (and' (R' x S φ h) h) = tf S φ := by
  intro H
  have := H Unit Unit (fun _ _ => ()) (fun _ _ => 0) (fun _ _ _ _ => ()) (fun _ _ => 1)
    (fun _ _ _ => True) () (fun _ => ()) (fun _ => ()) () trivial
  norm_num at this

/-- ch33-030 (定): 系列 S₁, S₂, … が probable-frequencies p₁, p₂, … に従う: φ(x)/R(x, S₁, φ, h) . h = p₁ (016 の
StatGen を S₁ に当てたもの)。 -/
theorem th_33_030 (φ : Inst → IProp) (S : ℕ → Inst → IProp) (h : IProp) (p : ℕ → ℝ) :
    StatGen φ (S 1) h (p 1) ↔ ∀ x : Inst, PrI (φ x) (iand (R x (S 1) φ h) h) = p 1 := Iff.rfl

/-- 031 の等号連鎖 p₁ = p₂ = etc. (添字 1 から; 隣どうしが等しい)。 -/
def EqChain (p : ℕ → ℝ) : Prop := ∀ i, 1 ≤ i → p i = p (i + 1)

/-- ch33-031 (定): p₁ = p₂ = etc. (stable value の第 1 の場合) は、添字 1 以上のどの 2 つも等しいことと同値。 -/
theorem th_33_031 (p : ℕ → ℝ) : EqChain p ↔ ∀ i j, 1 ≤ i → 1 ≤ j → p i = p j := by
  constructor
  · intro h
    have key : ∀ j, 1 ≤ j → p j = p 1 := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [← h k hk, ih]
    intro i j hi hj; rw [key i hi, key j hj]
  · intro h i hi; exact h i (i + 1) hi (by omega)

/-- ch33-032 (定): S = S₁ の場合 (調べる事例が標本を引いた系列と同一の系列の成員)、S₁ の統計的一般化はそのまま
S のものになる。 -/
theorem th_33_032 (φ S S₁ : Inst → IProp) (h : IProp) (p₁ : ℝ) (hS : S = S₁)
    (h030 : StatGen φ S₁ h p₁) : StatGen φ S h p₁ := by
  rw [hS]; exact h030

/-- 037 の g_r: 「' a_r is g ' ≡ g_r」(g は特性の命題関数、a は系列の項)。 -/
def gr (g : Inst → IProp) (a : ℕ → Inst) (r : ℕ) : IProp := g (a r)

/-- ch33-037 (定): 'a_r is g' ≡ g_r。 -/
theorem th_33_037 (g : Inst → IProp) (a : ℕ → Inst) (r : ℕ) : gr g a r = g (a r) := rfl

/-- 038 の p_r: g_r/h。 -/
noncomputable def pr (g : Inst → IProp) (a : ℕ → Inst) (h : IProp) (r : ℕ) : ℝ := PrI (gr g a r) h

/-- ch33-038 (定): g_r/h = p_r。 -/
theorem th_33_038 (g : Inst → IProp) (a : ℕ → Inst) (h : IProp) (r : ℕ) :
    pr g a h r = PrI (gr g a r) h := rfl

/-- 039 の前提 g_s . . . ḡ_t . . . h: 項の番号と真偽の並び l を印刷の順に前から並置し、最後に h を置く
(真なら g_s、偽なら ḡ_s)。 -/
noncomputable def prem (g : Inst → IProp) (a : ℕ → Inst) : List (ℕ × Bool) → IProp → IProp
  | [], h => h
  | (s, b) :: l, h => iand (if b then gr g a s else inot (gr g a s)) (prem g a l h)

/-- 039 の independent: 1 ≤ r ≤ n のどの r についても、r と違う番号の項の真偽をどう並置しても
g_r/g_s . . . ḡ_t . . . h = p_r。 -/
def IndepTerms (g : Inst → IProp) (a : ℕ → Inst) (h : IProp) (n : ℕ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ n → ∀ l : List (ℕ × Bool), (∀ e ∈ l, 1 ≤ e.1 ∧ e.1 ≤ n ∧ e.1 ≠ r) →
    PrI (gr g a r) (prem g a l h) = pr g a h r

/-- ch33-039 (定): g_r/g_s . . . ḡ_t . . . h = p_r (independent の定義)。 -/
theorem th_33_039 (g : Inst → IProp) (a : ℕ → Inst) (h : IProp) (n : ℕ) :
    IndepTerms g a h n ↔ ∀ r, 1 ≤ r → r ≤ n → ∀ l : List (ℕ × Bool),
      (∀ e ∈ l, 1 ≤ e.1 ∧ e.1 ≤ n ∧ e.1 ≠ r) → PrI (gr g a r) (prem g a l h) = pr g a h r := Iff.rfl

/-- 039 と第II部 Def. XIII (ch12-070 の a₁/a₂h = a₁/h) の対応: independent な項は、どの 2 つ r ≠ s についても
g_r/g_s h = g_r/h (Def. XIII の第 1 成分の形; 前提の並置の順も同じ)。 -/
theorem th_33_039_defXIII (g : Inst → IProp) (a : ℕ → Inst) (h : IProp) (n : ℕ)
    (hI : IndepTerms g a h n) (r s : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hrs : s ≠ r) : PrI (gr g a r) (iand (gr g a s) h) = PrI (gr g a r) h := by
  have := hI r hr hrn [(s, true)] (by simp; omega)
  simpa [prem, pr] using this

/-- 040 の uniform: p₁ = p₂ = . . . = p (1 ≤ r ≤ n の全ての p_r が p)。 -/
def Uniform (q : ℕ → ℝ) (n : ℕ) (p : ℝ) : Prop := ∀ r, 1 ≤ r → r ≤ n → q r = p

/-- ch33-040 (定): p₁ = p₂ = . . . = p。 -/
theorem th_33_040 (q : ℕ → ℝ) (n : ℕ) (p : ℝ) :
    Uniform q n p ↔ ∀ r, 1 ≤ r → r ≤ n → q r = p := Iff.rfl

/-- 040–041 の補助: uniform なら compounded probability 1/nΣp_r は Bernoullian probability p に等しい。 -/
theorem th_33_041_uniform (q : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (p : ℝ) (hU : Uniform q n p) :
    1 / (n : ℝ) * ∑ r ∈ Finset.Icc 1 n, q r = p := by
  rw [Finset.sum_congr rfl (fun r hr => hU r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)]
  simp
  have : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

/-- 「第 r 系列の頻度は x」の命題 (印刷は頻度 x_r とこの命題を同じ記号で書く)。 -/
axiom fq : ℕ → ℝ → IProp

/-- 043 の θ_r(x) = x/h (第 r 系列の頻度が x である確率)。 -/
noncomputable def θ (h : IProp) (r : ℕ) (x : ℝ) : ℝ := PrI (fq r x) h

/-- ch33-043 (定): x₁/h = θ₁(x₁)。 -/
theorem th_33_043 (h : IProp) (x₁ : ℝ) : θ h 1 x₁ = PrI (fq 1 x₁) h := rfl

/-- 045 の前提 x_s . . . h: (系列の番号, 頻度) の並びを印刷の順に前から並置し、最後に h を置く。 -/
noncomputable def fprem : List (ℕ × ℝ) → IProp → IProp
  | [], h => h
  | (s, y) :: l, h => iand (fq s y) (fprem l h)

/-- 045 の independent (頻度): r と違う系列の頻度をどう並置しても x_r/x_s . . . h = θ_r(x_r)。 -/
def IndepFreq (h : IProp) (n : ℕ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ n → ∀ l : List (ℕ × ℝ), (∀ e ∈ l, 1 ≤ e.1 ∧ e.1 ≤ n ∧ e.1 ≠ r) →
    ∀ x, PrI (fq r x) (fprem l h) = θ h r x

/-- ch33-045 (定): x_r/x_s . . . h = θ_r(x_r) (frequencies are independent)。 -/
theorem th_33_045 (h : IProp) (n : ℕ) :
    IndepFreq h n ↔ ∀ r, 1 ≤ r → r ≤ n → ∀ l : List (ℕ × ℝ), (∀ e ∈ l, 1 ≤ e.1 ∧ e.1 ≤ n ∧ e.1 ≠ r) →
      ∀ x, PrI (fq r x) (fprem l h) = θ h r x := Iff.rfl

/-- 046 の修正形 (stable): 1 ≤ r ≤ n の全ての系列で頻度の確率の関数が同じ θ: θ₁(x) = θ₂(x) = . . . = θ(x)。 -/
def StableFix (Θf : ℕ → ℝ → ℝ) (n : ℕ) (θ₀ : ℝ → ℝ) : Prop := ∀ r, 1 ≤ r → r ≤ n → ∀ x, Θf r x = θ₀ x

/-- 046 の印刷形: θ₁(x) = θ₂(x₂) = . . . θ(x) を自由変数 x・x₂ の全てにわたって読む。 -/
def StablePrinted (Θf : ℕ → ℝ → ℝ) (θ₀ : ℝ → ℝ) : Prop :=
  ∀ x x₂ : ℝ, Θf 1 x = Θf 2 x₂ ∧ Θf 2 x₂ = θ₀ x

/-- ch33-046 (✎、修正形): frequencies are stable ⇔ θ₁(x) = θ₂(x) = . . . = θ(x)。stable なら、どの 2 つの系列も
頻度の確率の関数が同じ。 -/
theorem th_33_046_fix (h : IProp) (n : ℕ) (θ₀ : ℝ → ℝ) (hS : StableFix (θ h) n θ₀)
    (r s : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) (hs : 1 ≤ s) (hsn : s ≤ n) : θ h r = θ h s := by
  funext x; rw [hS r hr hrn x, hS s hs hsn x]

/-- ch33-046 の反例 (F33.1): 印刷形 θ₁(x) = θ₂(x₂) = . . . θ(x) を全ての x・x₂ にわたって読むと、θ は定数に
限られる (頻度の確率が頻度によらず一定)。 -/
theorem nec_33_046 (Θf : ℕ → ℝ → ℝ) (θ₀ : ℝ → ℝ) (hP : StablePrinted Θf θ₀) :
    ∀ x y, θ₀ x = θ₀ y := by
  intro x y
  rw [← (hP x 0).2, ← (hP y 0).2]

/-- ch33-046 の反例 (依頼の修正案 θ₁(x₁) = θ₂(x₂) = …): x₁・x₂ を全てにわたらせると θ₁ は定数に限られる。 -/
theorem nec_33_046_x1x2 (Θf : ℕ → ℝ → ℝ) (hP : ∀ x₁ x₂ : ℝ, Θf 1 x₁ = Θf 2 x₂) :
    ∀ x y, Θf 1 x = Θf 1 y := by
  intro x y; rw [hP x 0, hP y 0]

/-- 頻度 0 と 1 が確率 1/2 ずつの分布 (どの系列も同じ)。 -/
noncomputable def θex (_r : ℕ) (x : ℝ) : ℝ := if x = 0 then 1 / 2 else if x = 1 then 1 / 2 else 0

/-- ch33-046 の反例の模型: θex は修正形の stable を満たすが、印刷形も依頼の修正案も満たさない。 -/
theorem nec_33_046_ex :
    StableFix θex 2 (θex 1) ∧ ¬ StablePrinted θex (θex 1) ∧
      ¬ (∀ x₁ x₂ : ℝ, θex 1 x₁ = θex 2 x₂) := by
  refine ⟨fun _ _ _ _ => rfl, fun hP => ?_, fun hP => ?_⟩
  · have := nec_33_046 θex (θex 1) hP 0 2
    norm_num [θex] at this
  · have := nec_33_046_x1x2 θex hP 0 2
    norm_num [θex] at this

/-! ## 第 33 章 §9 (folio 424–425、Bowley): 095・096・097 -/

/-- 095 の X_t = ₁U_t + . . . + _pU_t + ₁V_t + . . . + _qV_t (t は観測、確率空間の点)。 -/
def Xt {Ω : Type*} {p q : ℕ} (U : Fin p → Ω → ℝ) (V : Fin q → Ω → ℝ) (t : Ω) : ℝ :=
  ∑ i, U i t + ∑ j, V j t

/-- ch33-095 (定)。 -/
theorem th_33_095 {Ω : Type*} {p q : ℕ} (U : Fin p → Ω → ℝ) (V : Fin q → Ω → ℝ) (t : Ω) :
    Xt U V t = ∑ i, U i t + ∑ j, V j t := rfl

/-- 096 の Y_t = ₁U_t + . . . + _pU_t + ₁W_t + . . . _qW_t (印刷は末尾の + が無い; 和と読む)。 -/
def Yt {Ω : Type*} {p q : ℕ} (U : Fin p → Ω → ℝ) (W : Fin q → Ω → ℝ) (t : Ω) : ℝ :=
  ∑ i, U i t + ∑ j, W j t

/-- ch33-096 (定)。 -/
theorem th_33_096 {Ω : Type*} {p q : ℕ} (U : Fin p → Ω → ℝ) (W : Fin q → Ω → ℝ) (t : Ω) :
    Yt U W t = ∑ i, U i t + ∑ j, W j t := rfl

/-- 相関係数 r = cov[X, Y]/√(Var X · Var Y) (Bowley の「statistical description」)。 -/
noncomputable def corr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  cov[X, Y; μ] / √(Var[X; μ] * Var[Y; μ])

/-- 独立な量は無相関 (Mathlib の IndepFun.covariance_eq_zero; 097 の前提 hUU 等を独立性から与える)。 -/
theorem uncorr_of_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A B : Ω → ℝ) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (h : A ⟂ᵢ[μ] B) : cov[A, B; μ] = 0 :=
  h.covariance_eq_zero hA hB

/-- ch33-097 (✓): U・V・W が互いに無相関 (「independent groups」; 独立なら無相関、uncorrelated_of_indep) で、
標準偏差が全て同じ σ (「if they have the same standard deviations」) なら、X と Y の相関係数は r = p/(p + q)。 -/
theorem th_33_097 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (p q : ℕ) (hp : 0 < p) (U : Fin p → Ω → ℝ) (V W : Fin q → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hU : ∀ i, MemLp (U i) 2 μ) (hV : ∀ j, MemLp (V j) 2 μ) (hW : ∀ j, MemLp (W j) 2 μ)
    (hUU : ∀ i i', i ≠ i' → cov[U i, U i'; μ] = 0) (hVV : ∀ j j', j ≠ j' → cov[V j, V j'; μ] = 0)
    (hWW : ∀ j j', j ≠ j' → cov[W j, W j'; μ] = 0)
    (hUV : ∀ i j, cov[U i, V j; μ] = 0) (hUW : ∀ i j, cov[U i, W j; μ] = 0)
    (hVW : ∀ j j', cov[V j, W j'; μ] = 0)
    (hsU : ∀ i, Var[U i; μ] = σ ^ 2) (hsV : ∀ j, Var[V j; μ] = σ ^ 2) (hsW : ∀ j, Var[W j; μ] = σ ^ 2) :
    corr μ (Xt U V) (Yt U W) = (p : ℝ) / (p + q) := by
  have eX : Xt U V = ∑ i, U i + ∑ j, V j := by funext t; simp [Xt, Finset.sum_apply]
  have eY : Yt U W = ∑ i, U i + ∑ j, W j := by funext t; simp [Yt, Finset.sum_apply]
  rw [eX, eY]
  have mU : MemLp (∑ i, U i) 2 μ := memLp_finset_sum' _ (fun i _ => hU i)
  have mV : MemLp (∑ j, V j) 2 μ := memLp_finset_sum' _ (fun j _ => hV j)
  have mW : MemLp (∑ j, W j) 2 μ := memLp_finset_sum' _ (fun j _ => hW j)
  have diag : ∀ {n : ℕ} (Z : Fin n → Ω → ℝ), (∀ i, MemLp (Z i) 2 μ) →
      (∀ i i', i ≠ i' → cov[Z i, Z i'; μ] = 0) → (∀ i, Var[Z i; μ] = σ ^ 2) →
      cov[∑ i, Z i, ∑ i, Z i; μ] = n * σ ^ 2 := by
    intro n Z hZ hZZ hsZ
    rw [covariance_sum_sum hZ hZ]
    have : ∀ i, ∑ i', cov[Z i, Z i'; μ] = σ ^ 2 := by
      intro i
      rw [Finset.sum_eq_single i (fun b _ hb => hZZ i b (Ne.symm hb)) (by simp)]
      rw [covariance_self (hZ i).aemeasurable, hsZ i]
    simp [this]
  have cross : ∀ {n m : ℕ} (Z : Fin n → Ω → ℝ) (Z' : Fin m → Ω → ℝ), (∀ i, MemLp (Z i) 2 μ) →
      (∀ j, MemLp (Z' j) 2 μ) → (∀ i j, cov[Z i, Z' j; μ] = 0) → cov[∑ i, Z i, ∑ j, Z' j; μ] = 0 := by
    intro n m Z Z' hZ hZ' h0
    rw [covariance_sum_sum hZ hZ']; simp [h0]
  have cUV := cross U V hU hV hUV
  have cUW := cross U W hU hW hUW
  have cVW := cross V W hV hW hVW
  have cVU : cov[∑ j, V j, ∑ i, U i; μ] = 0 := by rw [covariance_comm]; exact cUV
  have cWU : cov[∑ j, W j, ∑ i, U i; μ] = 0 := by rw [covariance_comm]; exact cUW
  have dU := diag U hU hUU hsU
  have dV := diag V hV hVV hsV
  have dW := diag W hW hWW hsW
  have cXY : cov[∑ i, U i + ∑ j, V j, ∑ i, U i + ∑ j, W j; μ] = p * σ ^ 2 := by
    rw [covariance_add_left mU mV (mU.add mW), covariance_add_right mU mU mW,
      covariance_add_right mV mU mW, dU, cUW, cVU, cVW]; ring
  have vX : Var[∑ i, U i + ∑ j, V j; μ] = (p + q) * σ ^ 2 := by
    rw [← covariance_self (mU.add mV).aemeasurable, covariance_add_left mU mV (mU.add mV),
      covariance_add_right mU mU mV, covariance_add_right mV mU mV, dU, dV, cUV, cVU]; ring
  have vY : Var[∑ i, U i + ∑ j, W j; μ] = (p + q) * σ ^ 2 := by
    rw [← covariance_self (mU.add mW).aemeasurable, covariance_add_left mU mW (mU.add mW),
      covariance_add_right mU mU mW, covariance_add_right mW mU mW, dU, dW, cUW, cWU]; ring
  unfold corr
  rw [cXY, vX, vY]
  have hpq : (0 : ℝ) < p + q := by positivity
  rw [Real.sqrt_mul_self (by positivity)]
  field_simp

end KeynesXXXc

/-! ## #print axioms -/
-- 第 32 章 §4: 003・004・005・033
#print axioms KeynesXXXc.genProb
#print axioms KeynesXXXc.th_32_003
#print axioms KeynesXXXc.genProb_weights
#print axioms KeynesXXXc.genProb_between
#print axioms KeynesXXXc.Indifferent
#print axioms KeynesXXXc.th_32_004
#print axioms KeynesXXXc.th_32_005
#print axioms KeynesXXXc.th_32_033
-- 第 32 章 §6: 006–029
#print axioms KeynesXXXc.probErr
#print axioms KeynesXXXc.rBern
#print axioms KeynesXXXc.th_32_006
#print axioms KeynesXXXc.ρL
#print axioms KeynesXXXc.Θ
#print axioms KeynesXXXc.T5
#print axioms KeynesXXXc.exp_neg_sq_bound
#print axioms KeynesXXXc.int_T5_lo
#print axioms KeynesXXXc.int_T5_hi
#print axioms KeynesXXXc.int_T5
#print axioms KeynesXXXc.sqrt_pi_lo
#print axioms KeynesXXXc.sqrt_pi_hi
#print axioms KeynesXXXc.Θ_lo
#print axioms KeynesXXXc.Θ_hi
#print axioms KeynesXXXc.Θ_strictMono
#print axioms KeynesXXXc.Θ_continuous
#print axioms KeynesXXXc.th_32_007
#print axioms KeynesXXXc.meanN
#print axioms KeynesXXXc.sqDevN
#print axioms KeynesXXXc.RLex
#print axioms KeynesXXXc.th_32_008
#print axioms KeynesXXXc.sqDev_expect
#print axioms KeynesXXXc.th_32_010
#print axioms KeynesXXXc.Qlex
#print axioms KeynesXXXc.th_32_016
#print axioms KeynesXXXc.th_32_017
#print axioms KeynesXXXc.th_32_018
#print axioms KeynesXXXc.th_32_019
#print axioms KeynesXXXc.th_32_Q_trichotomy
#print axioms KeynesXXXc.th_32_011
#print axioms KeynesXXXc.th_32_012
#print axioms KeynesXXXc.th_32_020
#print axioms KeynesXXXc.th_32_021
#print axioms KeynesXXXc.th_32_021_r
#print axioms KeynesXXXc.CT
#print axioms KeynesXXXc.PT
#print axioms KeynesXXXc.QT
#print axioms KeynesXXXc.th_32_022
#print axioms KeynesXXXc.th_32_023
#print axioms KeynesXXXc.th_32_024
#print axioms KeynesXXXc.th_32_022_lexis
#print axioms KeynesXXXc.th_32_028
#print axioms KeynesXXXc.th_32_029
#print axioms KeynesXXXc.th_32_029_form
-- 第 33 章 §5–§8: 016–046
#print axioms KeynesXXXc.StatGen
#print axioms KeynesXXXc.th_33_016
#print axioms KeynesXXXc.RandomMemberFn
#print axioms KeynesXXXc.th_33_018
#print axioms KeynesXXXc.ax_freq_eq_prob_sat
#print axioms KeynesXXXc.th_33_022
#print axioms KeynesXXXc.th_33_021
#print axioms KeynesXXXc.th_33_026
#print axioms KeynesXXXc.th_33_022_needs_ax
#print axioms KeynesXXXc.th_33_030
#print axioms KeynesXXXc.EqChain
#print axioms KeynesXXXc.th_33_031
#print axioms KeynesXXXc.th_33_032
#print axioms KeynesXXXc.gr
#print axioms KeynesXXXc.th_33_037
#print axioms KeynesXXXc.pr
#print axioms KeynesXXXc.th_33_038
#print axioms KeynesXXXc.prem
#print axioms KeynesXXXc.IndepTerms
#print axioms KeynesXXXc.th_33_039
#print axioms KeynesXXXc.th_33_039_defXIII
#print axioms KeynesXXXc.Uniform
#print axioms KeynesXXXc.th_33_040
#print axioms KeynesXXXc.th_33_041_uniform
#print axioms KeynesXXXc.θ
#print axioms KeynesXXXc.th_33_043
#print axioms KeynesXXXc.fprem
#print axioms KeynesXXXc.IndepFreq
#print axioms KeynesXXXc.th_33_045
#print axioms KeynesXXXc.StableFix
#print axioms KeynesXXXc.StablePrinted
#print axioms KeynesXXXc.th_33_046_fix
#print axioms KeynesXXXc.nec_33_046
#print axioms KeynesXXXc.nec_33_046_x1x2
#print axioms KeynesXXXc.θex
#print axioms KeynesXXXc.nec_33_046_ex
-- 第 33 章 §9: 095・096・097
#print axioms KeynesXXXc.Xt
#print axioms KeynesXXXc.th_33_095
#print axioms KeynesXXXc.Yt
#print axioms KeynesXXXc.th_33_096
#print axioms KeynesXXXc.corr
#print axioms KeynesXXXc.uncorr_of_indep
#print axioms KeynesXXXc.th_33_097
