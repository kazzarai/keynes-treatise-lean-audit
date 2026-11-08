/-
# Keynes (1921) *A Treatise on Probability* Part V — Lean 4 Phase 15b
# 第 XXX 章 (folio 370–380): Laplace の方法と継起の規則、Pearson の「Bayes' Theorem」
# 第 XXXI 章 §3 (folio 386–387): Bernoulli の定理の逆
#
# 対象は台帳の式行 14 本 (ch30-005・007・009・021・029・034・035・054・056・057・059・060、ch31-023・031)。
# 第 30 章の式は Keynes の確率関係 (a/h) を含まない解析 (二項分布・Beta 積分・Γ 関数) で、第II部の担体には置かない。
# 第 31 章の 2 本も、Bernoulli の定理が f(q′)/h . f(q) に与える数値 (二項の項) の上の算術として扱う。
#
# ## 基準
#   1921 年 Macmillan 初版の頁画像のみ (folio 370, 376, 379, 380, 386, 387)。定理名は th_30_<行番号>・th_31_<行番号>。
#
# ## 原典
#   (folio 370、§4) 「if p is the probability à priori, there is a probability P that the proportion of times m/(m+n)
#    of the event's occurrence in μ (= m + n) trials will lie between p ± γ√(2pq/μ), where
#    P = 2/√π ∫_0^γ e^{−t²}dt + 1/√(2πμpq) e^{−γ²}. The inversion of the theorem, which he assumes without proof,
#    states that, if the event is observed to happen m times in μ trials, there is a probability P that the
#    probability of the event p will lie between m/μ ± γ√(2mn/μ³), where
#    P = 2/√π ∫_0^γ e^{−t²}dt + 1/√(2πμ (m/μ²)) e^{−γ²}.」
#   (folio 376、§9) 「the probability à posteriori that x lies between x and x + dx is proportional to x^m(1 − x)^n dx,
#    and is equal, therefore, to Ax^m(1 − x)^n dx where A is a constant. … A is determined by the equation
#    ∫_0 Ax^m(1 − x)^n dx = 1 ∴ A = Γ(m + n + 2)/(Γ(m + 1)Γ(n + 1)). Hence the probability that the event will occur
#    at the (m + n + 1)th trial … is A∫_0^1 x^{m+1}(1 − x)^n dx. If we substitute the value of A found above, this is
#    equal to (m + 1)/(m + n + 2). … In the cases where n = 0, … the formula yields the result (m + 1)/(m + 2)」
#    脚注 1 (Bachelier): 「writes ω̂(y)dy as the à priori probability that the probability is y, so that after m
#    occurrences is m+n trials the probability that the probability lies between y and y + dy is
#    y^m(1 − y)^n ω̂(y)dy / ∫y^m(1 − y)^n ω̂(y)dy. … the simplest hypothesis is to put ω̂ = 1, which leads, as above,
#    to Laplace's Law of Succession. He also proposes the hypothesis ω̂(y) = a + a₁y + a₂y² + . . ., in which case
#    the denominator is a series of Eulerian integrals.」
#   (folio 379、§12、Pearson) 「if on n = p + q trials an event has been observed to occur p times and fail q times,
#    the probability that the true chance lies between x and x + dx is, on the equal distribution of our ignorance,
#    P_x = x^p(1 − x)^q dx / ∫_0^1 x^p(1 − x)^q dx. This is Bayes' Theorem.」
#   (folio 380) 「Now suppose that a second trial of m = r + s instances be made, then the probability that the given
#    event will occur r times and fail s, is on the à priori chance being between x and x + dx
#    = P_x (Γm/(ΓrΓs)) n^r(1 − x)^s, and accordingly the total chance C_r, whatever x may be of the event occurring
#    r times in the second series, is C_r = (Γm/(ΓrΓs)) ∫_0^1 x^{p+r}(1 − x)^{q+s}dx / ∫_0^1 x^p(1 − x)^q dx.」
#   (folio 386、第 31 章 §3) 「Let l/m = q. … Let f(q) represent the proposition that q is the true value of l/m.
#    Let q′ represent the ratio of the number of instances actually before us in which A has been accompanied by B
#    to that of the instances in which A has not been accompanied by B; and let f′(q′) be the proposition which
#    asserts this.」 (folio 387) 「the formula could be reduced to the algebraical expression
#    f(q′)/h . f(q) / Σf(q′)/h . f(q), … It is easy to show that it is a maximum when q = q′, i.e. that q′ is the
#    most probable value of l/m」
#
# ## 記法の読み (定義のみ)
#   q p          : 1 − p (folio 370 の q; phase14b の写し)。
#   bterm m p n  : 二項の項 C(m, n) p^n q^{m−n} (phase14b の写し)。
#   mu m n       : μ := m + n (005)。
#   Θ・mpq・probWithin : phase14b の写し (Θ t = 2/√π ∫_0^t e^{−u²} du)。
#   propWithin μ p γ : 割合 n/μ が p ± γ√(2pq/μ) の間にある確率 (007 の「probability」)。
#   Pdir μ p γ   : 007 の P (印刷の式)。Pinv μ m γ は 009 の P (印刷の式)、Pinvfix μ m n γ は根号内を mn/μ² とした形。
#   Acoef m n    : Γ(m + n + 2)/(Γ(m + 1)Γ(n + 1)) (021 の A の値)。
#   bachNext ω m n : Bachelier の事後分布での次の生起の確率 ∫y^{m+1}(1 − y)^n ω / ∫y^m(1 − y)^n ω (034)。
#   ωpoly a K    : ω̂(y) = a + a₁y + a₂y² + … の初めの K 項 (035)。
#   pn p q       : n := p + q (054)。Px p q x : 056 の P_x (dx を除いた密度)。
#   fac059・fac059x・fac059fix : 059 で P_x に掛かる因子 (印刷 n^r / n^r を x^r に / 係数も Γ(m+1)/(Γ(r+1)Γ(s+1)) に)。
#   Cr p q r s m : 060 の右辺 (印刷の式)。
#   qratio l m   : q := l/m (第 31 章 023)。post S N k x : 一様な事前確率のもとでの q の事後確率
#                  bterm N x k / Σ_{s ∈ S} bterm N s k (387 の式; f(q′)/h . f(q) を Bernoulli の定理の値 bterm N q k と読む)。
#
# ## 外部公理 (Mathlib にないもの)
#   ax_normal_approx : 積分形の de Moivre–Laplace 定理 (phase14b の同名の公理の再掲、文も同じ)。
#     p ∈ (0, 1)、γ > 0 なら |n − mp| < √(2mpq) γ の確率は m → ∞ で Θ(γ) に近づく。
#     真な定理の言明なので反例の模型は作れない。必要性は、公理を外すと th_30_007 が通らない
#     (Unknown identifier `ax_normal_approx`) ことで確かめた (B44)。
#   Beta 積分 ∫_0^1 x^m (1 − x)^n dx = Γ(m + 1)Γ(n + 1)/Γ(m + n + 2) は Mathlib の
#   Complex.betaIntegral_eq_Gamma_mul_div から証明した (beta_nat、外部公理に依らない)。
#
# ## 所見候補
#   F30.1 (009): 根号内 2πμ (m/μ²) は、Laplace の逆の読み (007 の p・q に観測された m/μ・n/μ を入れる) では
#           2πμ (mn/μ²) で、n が欠けている。m = 1、n = 2 で両者は違う (nec_30_009)。m = 1 では μ を大きくすると
#           印刷の補正項が 1 を超え、P が確率にならない (nec_30_009_gt、外部公理に依らない)。印刷の形は μ → ∞ で
#           補正項が消えず、確率の極限 Θ(γ) に近づかない (nec_30_009_lim、外部公理に依る)。
#           司令塔裁定 (B44 r1): 009 は ✎ かつ 外 (修正形 th_30_009_fix が ax_normal_approx に依る)。
#   F30.4 (059): n^r は x^r の誤植。n^r のままでは因子が 1 を超え確率にならない (nec_30_059_n)。
#   F30.6 案 (059・060): 係数 Γm/(ΓrΓs) は、Γ を Γ 関数と読むと (同じ章の 021 は Γ(m + 1) の形で Γ 関数を使う)
#           二項係数 C(m, r) にならない (m = 2、r = s = 1、x = 1/2 で 1/4 ≠ 1/2、nec_30_059_gamma)。
#           Γk を k! と読めば二項係数になる (th_30_059_fact)。Γ 関数での正しい形は Γ(m + 1)/(Γ(r + 1)Γ(s + 1))
#           (th_30_059_fix)。060 は 059 の係数をそのまま受け継ぐ: p = q = 0、r = s = 1 (m = 2) で印刷の C_r は
#           1/6、係数を二項係数にした C_r は 1/3 (nec_30_060)。司令塔裁定 (B44 r1): 060 は ✎ (修正形は
#           th_30_060_fix・th_30_060_sum)。
#   F31.3 (第 31 章 031、司令塔裁定 B44 r1 で所見に昇格): q′ は印刷では「B を伴う事例の数と伴わない事例の数の比」
#           (k/(N − k)) で、この読みでは「maximum when q = q′」が成り立たない (N = 3、k = 1 で k/(N − k) = 1/2 の値
#           3/8 < 1/3 の値 4/9、nec_31_031_odds)。q′ を観測された割合 k/N に読み替えた th_31_031 が修正形。
#           最大が値として達成されるのは q の取りうる値の集合 S が k/N を含むとき (th_31_031_mem)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_v_phase15b_laplace.lean
-/
import Mathlib

namespace KeynesXXXb

open Real Finset Filter Topology

/-! ## 記法 (phase14b の写し) -/

/-- q := 1 − p (phase14b の q の写し)。 -/
noncomputable def q (p : ℝ) : ℝ := 1 - p

/-- 二項の項 C(m, n) p^n q^{m−n} (phase14b の bterm の写し)。 -/
noncomputable def bterm (m : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  (m.choose n : ℝ) * p ^ n * q p ^ (m - n)

/-- 二項の項の和は 1 (phase14b の th_29_005_one の写し)。 -/
theorem th_29_005_one (m : ℕ) (p : ℝ) : ∑ n ∈ range (m + 1), bterm m p n = 1 := by
  have h : (p + q p) ^ m = ∑ n ∈ range (m + 1), bterm m p n := by
    rw [add_pow]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    unfold bterm; ring
  rw [← h]; unfold q; simp

/-! ## §4 (folio 370): 005・007・009 -/

/-- ch30-005: μ (= m + n) の名付け。 -/
noncomputable def mu (m n : ℕ) : ℕ := m + n

/-- ch30-005 (定): μ = m + n。定理 th_30_008・th_30_009_subst では前提 hμ : μ = m + n に写す。 -/
theorem th_30_005 (m n : ℕ) : mu m n = m + n := rfl

/-- mpq (phase14b の写し)。 -/
noncomputable def mpq (m : ℕ) (p : ℝ) : ℝ := m * p * q p

/-- Θ(t) = 2/√π ∫_0^t e^{−u²} du (phase14b の写し)。 -/
noncomputable def Θ (t : ℝ) : ℝ := 2 / √π * ∫ u in (0 : ℝ)..t, exp (-(u ^ 2))

/-- 二項分布で |n − mp| < a となる確率 (phase14b の写し)。 -/
noncomputable def probWithin (m : ℕ) (p a : ℝ) : ℝ :=
  ∑ n ∈ (range (m + 1)).filter (fun n : ℕ => |(n : ℝ) - m * p| < a), bterm m p n

/-- 積分形の de Moivre–Laplace 定理 (外部公理、phase14b の ax_normal_approx の再掲): p ∈ (0, 1)、γ > 0 なら
|n − mp| < √(2mpq) γ の確率は m → ∞ で Θ(γ) に近づく。 -/
axiom ax_normal_approx (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) (hγ : 0 < γ) :
  Tendsto (fun m : ℕ => probWithin m p (√(2 * mpq m p) * γ)) atTop (𝓝 (Θ γ))

/-- 007 の「probability」: μ 回のうちの割合 n/μ が p ± γ√(2pq/μ) の間にある確率。 -/
noncomputable def propWithin (μ : ℕ) (p γ : ℝ) : ℝ :=
  ∑ n ∈ (range (μ + 1)).filter (fun n : ℕ => |(n : ℝ) / μ - p| < γ * √(2 * p * q p / μ)),
    bterm μ p n

/-- ch30-007 の P (印刷の式): 2/√π ∫_0^γ e^{−t²}dt + 1/√(2πμpq) e^{−γ²}。 -/
noncomputable def Pdir (μ : ℕ) (p γ : ℝ) : ℝ :=
  2 / √π * (∫ t in (0 : ℝ)..γ, exp (-(t ^ 2))) + 1 / √(2 * π * μ * p * q p) * exp (-(γ ^ 2))

/-- phase14b の sqrt_div_m の写し: √(2mpq)/m = √(2pq/m)。 -/
theorem sqrt_div_m (m : ℕ) (hm : 0 < m) (p : ℝ) :
    √(2 * mpq m p) / m = √(2 * p * q p / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : 2 * p * q p / m = 2 * mpq m p / (m : ℝ) ^ 2 := by unfold mpq; field_simp
  rw [this, sqrt_div' _ (by positivity), Real.sqrt_sq hm'.le]

/-- 割合の形 (p ± γ√(2pq/μ)) と回数の形 (μp ± √(2μpq) γ) は同じ事象。 -/
theorem propWithin_eq (μ : ℕ) (hμ : 0 < μ) (p γ : ℝ) :
    propWithin μ p γ = probWithin μ p (√(2 * mpq μ p) * γ) := by
  unfold propWithin probWithin
  congr 1
  apply Finset.filter_congr
  intro n _
  have hμ' : (0 : ℝ) < μ := by exact_mod_cast hμ
  rw [← sqrt_div_m μ hμ p]
  have e : (n : ℝ) / μ - p = ((n : ℝ) - μ * p) / μ := by field_simp
  rw [e, abs_div, abs_of_pos hμ', mul_div_assoc', mul_comm γ, div_lt_div_iff_of_pos_right hμ']

/-- P = Θ(γ) + e^{−γ²}/√(2πμpq)。 -/
theorem Pdir_eq (μ : ℕ) (p γ : ℝ) :
    Pdir μ p γ = Θ γ + exp (-(γ ^ 2)) / √(2 * π * mpq μ p) := by
  unfold Pdir Θ mpq
  rw [show 2 * π * μ * p * q p = 2 * π * (μ * p * q p) by ring]; ring

/-- 補正項 e^{−γ²}/√(2πμpq) は μ → ∞ で 0 (phase14b の th_29_029_vanish の写し)。 -/
theorem vanish (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) :
    Tendsto (fun m : ℕ => exp (-(γ ^ 2)) / √(2 * π * mpq m p)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  apply tendsto_sqrt_atTop.comp
  have hq0 : 0 < q p := by unfold q; linarith
  have hk : 0 < 2 * π * (p * q p) := by positivity
  have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hk
  refine this.congr (fun m => ?_)
  unfold mpq; ring

/-- ch30-007 (外部公理依存): 割合が p ± γ√(2pq/μ) の間にある確率と印刷の P の差は μ → ∞ で 0
(Bernoulli の定理の直接形; ax_normal_approx に依る)。 -/
theorem th_30_007 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun μ : ℕ => propWithin μ p γ - Pdir μ p γ) atTop (𝓝 0) := by
  have h := ((ax_normal_approx p hp0 hp1 γ hγ).sub_const (Θ γ)).sub (vanish p hp0 hp1 γ)
  rw [sub_self, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with μ hμ
  rw [propWithin_eq μ hμ, Pdir_eq]; ring

/-- μ = m + n なら q(m/μ) = n/μ。 -/
theorem q_ratio (m n μ : ℕ) (hμ : μ = m + n) (hpos : 0 < μ) :
    q ((m : ℝ) / μ) = (n : ℝ) / μ := by
  subst hμ
  have h : (0 : ℝ) < (m : ℝ) + n := by exact_mod_cast hpos
  unfold q; push_cast; field_simp; ring

/-- ch30-008 (記法の補助): 006 の幅 γ√(2pq/μ) に p := m/μ を入れると γ√(2mn/μ³)。 -/
theorem th_30_008 (m n μ : ℕ) (hμ : μ = m + n) (hpos : 0 < μ) (γ : ℝ) :
    γ * √(2 * ((m : ℝ) / μ) * q ((m : ℝ) / μ) / μ) = γ * √(2 * m * n / (μ : ℝ) ^ 3) := by
  have hμ' : (0 : ℝ) < μ := by exact_mod_cast hpos
  rw [q_ratio m n μ hμ hpos]; congr 2; field_simp

/-- ch30-009 の P (印刷の式): 2/√π ∫_0^γ e^{−t²}dt + 1/√(2πμ (m/μ²)) e^{−γ²}。 -/
noncomputable def Pinv (μ m : ℕ) (γ : ℝ) : ℝ :=
  2 / √π * (∫ t in (0 : ℝ)..γ, exp (-(t ^ 2))) +
    1 / √(2 * π * μ * ((m : ℝ) / (μ : ℝ) ^ 2)) * exp (-(γ ^ 2))

/-- ch30-009 の P の修正形: 根号内を 2πμ (mn/μ²) とする。 -/
noncomputable def Pinvfix (μ m n : ℕ) (γ : ℝ) : ℝ :=
  2 / √π * (∫ t in (0 : ℝ)..γ, exp (-(t ^ 2))) +
    1 / √(2 * π * μ * ((m : ℝ) * n / (μ : ℝ) ^ 2)) * exp (-(γ ^ 2))

/-- ch30-009 (修正形の等式): Laplace の逆の読み (007 の p・q に m/μ・n/μ を入れる) で 007 の P は
2/√π ∫_0^γ e^{−t²}dt + 1/√(2πμ (mn/μ²)) e^{−γ²} になる。 -/
theorem th_30_009_subst (m n μ : ℕ) (hμ : μ = m + n) (hpos : 0 < μ) (γ : ℝ) :
    Pdir μ ((m : ℝ) / μ) γ = Pinvfix μ m n γ := by
  have hμ' : (0 : ℝ) < μ := by exact_mod_cast hpos
  unfold Pdir Pinvfix
  rw [q_ratio m n μ hμ hpos]
  congr 4
  field_simp

/-- ch30-009 の反例 (F30.1): m = 1、n = 2 (μ = 3) で印刷の P と修正形の P は違う (どの γ でも)。 -/
theorem nec_30_009 (γ : ℝ) : Pinv 3 1 γ ≠ Pinvfix 3 1 2 γ := by
  unfold Pinv Pinvfix
  intro h
  have h' := add_left_cancel h
  have h'' := mul_right_cancel₀ (exp_pos _).ne' h'
  rw [one_div, one_div, inv_inj] at h''
  rw [Real.sqrt_inj (by positivity) (by positivity)] at h''
  norm_num at h''

/-- ch30-009 の反例 (F30.1、外部公理に依らない): m = 1 では印刷の補正項 1/√(2πμ (1/μ²)) e^{−γ²} は
√(μ/(2π)) e^{−γ²} で、μ を大きくすると 1 を超える。γ ≥ 0 なら積分の項は負でないので、印刷の P は 1 を超え
確率にならない (μ > 2π e^{2γ²} ととればよい)。 -/
theorem nec_30_009_gt (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ μ : ℕ, 1 < 1 / √(2 * π * μ * (((1 : ℕ) : ℝ) / (μ : ℝ) ^ 2)) * exp (-(γ ^ 2)) ∧
      1 < Pinv μ 1 γ := by
  obtain ⟨μ, hμ⟩ := exists_nat_gt (2 * π * exp (2 * γ ^ 2))
  refine ⟨μ, ?_⟩
  have hμ0 : (0 : ℝ) < μ := lt_trans (by positivity) hμ
  have e : 2 * π * (μ : ℝ) * (((1 : ℕ) : ℝ) / (μ : ℝ) ^ 2) = 2 * π / μ := by
    rw [Nat.cast_one]; field_simp
  have hs : 0 < √(2 * π / μ) := Real.sqrt_pos.mpr (by positivity)
  have hlt : √(2 * π / μ) < exp (-(γ ^ 2)) := by
    rw [Real.sqrt_lt' (exp_pos _), sq, ← Real.exp_add, div_lt_iff₀ hμ0]
    have h1 : exp (2 * γ ^ 2) * exp (-(γ ^ 2) + -(γ ^ 2)) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have h2 := mul_lt_mul_of_pos_right hμ (exp_pos (-(γ ^ 2) + -(γ ^ 2)))
    rw [mul_assoc, h1, mul_one] at h2
    linarith
  have hT : 1 < 1 / √(2 * π / μ) * exp (-(γ ^ 2)) := by
    rw [one_div_mul_eq_div, one_lt_div hs]; exact hlt
  have hI : 0 ≤ 2 / √π * ∫ t in (0 : ℝ)..γ, exp (-(t ^ 2)) :=
    mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hγ (fun t _ => (exp_pos _).le))
  rw [e]
  refine ⟨hT, ?_⟩
  unfold Pinv
  rw [e]
  linarith

theorem tendsto_mul_left_nat (k : ℕ) (hk : 0 < k) : Tendsto (fun N : ℕ => k * N) atTop atTop :=
  tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hk) tendsto_id

/-- ch30-009 (修正形、外部公理依存): m/μ = a/b を保って μ = bk → ∞ とすると、確率 (chance a/b での割合が
m/μ ± γ√(2mn/μ³) の間にある確率) と修正形の P の差は 0 に近づく。 -/
theorem th_30_009_fix (a b : ℕ) (ha : 0 < a) (hab : a < b) (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun k : ℕ => propWithin (b * k) ((a : ℝ) / b) γ -
      Pinvfix (b * k) (a * k) ((b - a) * k) γ) atTop (𝓝 0) := by
  have hb : 0 < b := by omega
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hp0 : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) hb'
  have hp1 : (a : ℝ) / b < 1 := (div_lt_one hb').mpr (by exact_mod_cast hab)
  have h := (th_30_007 _ hp0 hp1 γ hγ).comp (tendsto_mul_left_nat b hb)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < b * k := Nat.mul_pos hb hk
  have hsum : b * k = a * k + (b - a) * k := by rw [← Nat.add_mul]; congr 1; omega
  have hr : (((a * k : ℕ) : ℝ) / ((b * k : ℕ) : ℝ)) = (a : ℝ) / b := by
    push_cast; field_simp
  simp only [Function.comp]
  rw [← th_30_009_subst (a * k) ((b - a) * k) (b * k) hsum hpos γ, hr]

/-- ch30-009 の反例 (F30.1、外部公理依存): 印刷の P では 2πμ (m/μ²) = 2π a/b が一定で補正項が消えず、
確率と印刷の P の差は 0 でない値 −e^{−γ²}/√(2π a/b) に近づく。 -/
theorem nec_30_009_lim (a b : ℕ) (ha : 0 < a) (hab : a < b) (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun k : ℕ => propWithin (b * k) ((a : ℝ) / b) γ - Pinv (b * k) (a * k) γ) atTop
      (𝓝 (-(1 / √(2 * π * ((a : ℝ) / b)) * exp (-(γ ^ 2))))) ∧
    -(1 / √(2 * π * ((a : ℝ) / b)) * exp (-(γ ^ 2))) ≠ 0 := by
  have hb : 0 < b := by omega
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hp0 : (0 : ℝ) < (a : ℝ) / b := div_pos ha' hb'
  have hp1 : (a : ℝ) / b < 1 := (div_lt_one hb').mpr (by exact_mod_cast hab)
  refine ⟨?_, ?_⟩
  · have h1 := (th_30_007 _ hp0 hp1 γ hγ).comp (tendsto_mul_left_nat b hb)
    have h2 := (vanish _ hp0 hp1 γ).comp (tendsto_mul_left_nat b hb)
    have h := (h1.add h2).sub_const (1 / √(2 * π * ((a : ℝ) / b)) * exp (-(γ ^ 2)))
    rw [add_zero, zero_sub] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [Function.comp]
    rw [Pdir_eq]
    unfold Pinv Θ
    have e : (2 * π * ((b * k : ℕ) : ℝ) * (((a * k : ℕ) : ℝ) / ((b * k : ℕ) : ℝ) ^ 2))
        = 2 * π * ((a : ℝ) / b) := by push_cast; field_simp
    rw [e]; ring
  · have : 0 < 1 / √(2 * π * ((a : ℝ) / b)) * exp (-(γ ^ 2)) := by
      have : 0 < √(2 * π * ((a : ℝ) / b)) := Real.sqrt_pos.mpr (by positivity)
      positivity
    linarith

/-! ## §9 (folio 376): 021・029・034・035 -/

/-- Beta 積分 (Mathlib の Complex.betaIntegral_eq_Gamma_mul_div から):
∫_0^1 x^m (1 − x)^n dx = Γ(m + 1)Γ(n + 1)/Γ(m + n + 2)。 -/
theorem beta_nat (m n : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n
      = Real.Gamma (m + 1) * Real.Gamma (n + 1) / Real.Gamma (m + n + 2) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div ((m : ℂ) + 1) ((n : ℂ) + 1)
    (by simp; positivity) (by simp; positivity)
  unfold Complex.betaIntegral at h
  simp only [add_sub_cancel_right, Complex.cpow_natCast] at h
  have hL : (∫ x in (0 : ℝ)..1, (x : ℂ) ^ m * (1 - (x : ℂ)) ^ n)
      = ((∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  have h1 : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have h3 : ((m : ℂ) + 1 + ((n : ℂ) + 1)) = (((m : ℝ) + n + 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hL, h3, h1, h2, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  exact_mod_cast h

theorem beta_nat_pos (m n : ℕ) : 0 < ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n := by
  rw [beta_nat]
  have h1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < m + 1 by positivity)
  have h2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < n + 1 by positivity)
  have h3 := Real.Gamma_pos_of_pos (show (0 : ℝ) < m + n + 2 by positivity)
  positivity

/-- 021 の A の値 Γ(m + n + 2)/(Γ(m + 1)Γ(n + 1))。 -/
noncomputable def Acoef (m n : ℕ) : ℝ :=
  Real.Gamma (m + n + 2) / (Real.Gamma (m + 1) * Real.Gamma (n + 1))

/-- ch30-021: ∫_0^1 Ax^m(1 − x)^n dx = 1 ∴ A = Γ(m + n + 2)/(Γ(m + 1)Γ(n + 1))
(印刷の ∴ は → の向き; 逆向きも成り立つので ↔ で述べる。積分の上限 1 は印刷にない (F30.2))。 -/
theorem th_30_021 (m n : ℕ) (A : ℝ) :
    (∫ x in (0 : ℝ)..1, A * x ^ m * (1 - x) ^ n) = 1 ↔
      A = Real.Gamma (m + n + 2) / (Real.Gamma (m + 1) * Real.Gamma (n + 1)) := by
  show _ ↔ A = Acoef m n
  have hB := beta_nat_pos m n
  have e : (∫ x in (0 : ℝ)..1, A * x ^ m * (1 - x) ^ n)
      = A * ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n := by
    rw [← intervalIntegral.integral_const_mul]; simp only [mul_assoc]
  rw [e]
  have hA : Acoef m n = 1 / ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n := by
    rw [beta_nat]; unfold Acoef; rw [one_div_div]
  rw [hA]
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp

/-- ch30-025・026 (記法の補助、継起の規則): A∫_0^1 x^{m+1}(1 − x)^n dx = (m + 1)/(m + n + 2)。 -/
theorem th_30_026 (m n : ℕ) :
    Acoef m n * ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ n = (m + 1) / (m + n + 2) := by
  rw [beta_nat]; unfold Acoef
  push_cast
  have e2 : (m : ℝ) + 1 + n + 2 = (m + n + 2) + 1 := by ring
  rw [e2, Real.Gamma_add_one (by positivity : (m : ℝ) + 1 ≠ 0),
    Real.Gamma_add_one (by positivity : (m : ℝ) + n + 2 ≠ 0)]
  have h1 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < m + 1 by positivity)).ne'
  have h2 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < n + 1 by positivity)).ne'
  have h3 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < m + n + 2 by positivity)).ne'
  have h4 : (m : ℝ) + n + 2 ≠ 0 := by positivity
  field_simp

/-- ch30-029 (定、例の仮定 n = 0 を前提 hn に写す): このとき継起の規則は (m + 1)/(m + 2) (036)。 -/
theorem th_30_029 (m n : ℕ) (hn : n = 0) :
    Acoef m n * ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ n = (m + 1) / (m + 2) := by
  rw [th_30_026, hn]; push_cast; ring_nf

/-- ch30-029 の前提 n = 0 は外せない: m = 0、n = 1 で値は 1/3 で (m + 1)/(m + 2) = 1/2 ではない。 -/
theorem nec_30_029 :
    Acoef 0 1 * ∫ x in (0 : ℝ)..1, x ^ (0 + 1) * (1 - x) ^ 1 ≠ ((0 : ℕ) + 1 : ℝ) / ((0 : ℕ) + 2) := by
  rw [th_30_026]; norm_num

/-- 034 (脚注 1、Bachelier): 事後確率 y^m(1 − y)^n ω̂(y)dy / ∫y^m(1 − y)^n ω̂(y)dy のもとで次の生起の確率
∫y · (事後) = ∫y^{m+1}(1 − y)^n ω̂ / ∫y^m(1 − y)^n ω̂。 -/
noncomputable def bachNext (ω : ℝ → ℝ) (m n : ℕ) : ℝ :=
  (∫ y in (0 : ℝ)..1, y ^ (m + 1) * (1 - y) ^ n * ω y) /
    ∫ y in (0 : ℝ)..1, y ^ m * (1 - y) ^ n * ω y

/-- ch30-034 (定、仮定 ω̂ = 1 を前提 hω に写す): 「which leads, as above, to Laplace's Law of Succession」。 -/
theorem th_30_034 (ω : ℝ → ℝ) (hω : ∀ y, ω y = 1) (m n : ℕ) :
    bachNext ω m n = (m + 1) / (m + n + 2) := by
  unfold bachNext
  simp only [hω, mul_one]
  rw [← th_30_026, beta_nat, beta_nat]; unfold Acoef
  have h1 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < m + 1 by positivity)).ne'
  have h2 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < n + 1 by positivity)).ne'
  have h3 := (Real.Gamma_pos_of_pos (show (0 : ℝ) < m + n + 2 by positivity)).ne'
  push_cast
  field_simp

/-- ch30-034 の前提 ω̂ = 1 は外せない: ω̂(y) = y、m = n = 0 で値は 2/3 で 1/2 ではない。 -/
theorem nec_30_034 : bachNext (fun y => y) 0 0 ≠ ((0 : ℕ) + 1 : ℝ) / ((0 : ℕ) + 0 + 2) := by
  unfold bachNext
  simp only [pow_zero, mul_one, one_mul, zero_add, pow_one]
  have e : ∀ y : ℝ, y * y = y ^ 2 := fun y => by ring
  simp only [e, integral_pow, integral_id]
  norm_num

/-- ch30-035: ω̂(y) = a + a₁y + a₂y² + … の初めの K 項。 -/
noncomputable def ωpoly (a : ℕ → ℝ) (K : ℕ) (y : ℝ) : ℝ := ∑ k ∈ range K, a k * y ^ k

/-- ch30-035 (定、級数の記法): 「the denominator is a series of Eulerian integrals」の有限の部分和の形。
∫_0^1 y^m(1 − y)^n ω̂(y) dy = Σ_k a_k Γ(m + k + 1)Γ(n + 1)/Γ(m + k + n + 2)。無限級数の項別積分は扱わない。 -/
theorem th_30_035 (a : ℕ → ℝ) (K m n : ℕ) :
    ∫ y in (0 : ℝ)..1, y ^ m * (1 - y) ^ n * ωpoly a K y
      = ∑ k ∈ range K, a k *
          (Real.Gamma ((m + k : ℕ) + 1) * Real.Gamma (n + 1) / Real.Gamma ((m + k : ℕ) + n + 2)) := by
  unfold ωpoly
  have e : ∀ y : ℝ, y ^ m * (1 - y) ^ n * ∑ k ∈ range K, a k * y ^ k
      = ∑ k ∈ range K, a k * (y ^ (m + k) * (1 - y) ^ n) := by
    intro y; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
  simp only [e]
  rw [intervalIntegral.integral_finset_sum (fun k _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_const_mul, beta_nat]

/-! ## §12 (folio 379–380、Pearson): 054・056・057・059・060 -/

/-- ch30-054: n := p + q。 -/
noncomputable def pn (p q : ℕ) : ℕ := p + q

/-- ch30-054 (定): n = p + q (059 の印刷 n^r の n)。 -/
theorem th_30_054 (p q : ℕ) : pn p q = p + q := rfl

/-- ch30-056: P_x (dx を除いた密度) x^p(1 − x)^q / ∫_0^1 x^p(1 − x)^q dx。 -/
noncomputable def Px (p q : ℕ) (x : ℝ) : ℝ :=
  x ^ p * (1 - x) ^ q / ∫ y in (0 : ℝ)..1, y ^ p * (1 - y) ^ q

/-- ch30-056 (定): Pearson の「Bayes' Theorem」の式 (定義の展開)。 -/
theorem th_30_056 (p q : ℕ) (x : ℝ) :
    Px p q x = x ^ p * (1 - x) ^ q / ∫ y in (0 : ℝ)..1, y ^ p * (1 - y) ^ q := rfl

/-- ch30-056: P_x は [0, 1] 上で積分 1 (分母は Beta 積分で正)。 -/
theorem th_30_056_one (p q : ℕ) : ∫ x in (0 : ℝ)..1, Px p q x = 1 := by
  unfold Px
  rw [intervalIntegral.integral_div]
  exact div_self (beta_nat_pos p q).ne'

/-- ch30-059 の因子 (印刷の式): (Γm/(ΓrΓs)) n^r (1 − x)^s、n = p + q。 -/
noncomputable def fac059 (p q r s m : ℕ) (x : ℝ) : ℝ :=
  Real.Gamma m / (Real.Gamma r * Real.Gamma s) * (pn p q : ℝ) ^ r * (1 - x) ^ s

/-- ch30-059 の因子で n^r を x^r に替えたもの: (Γm/(ΓrΓs)) x^r (1 − x)^s。 -/
noncomputable def fac059x (r s m : ℕ) (x : ℝ) : ℝ :=
  Real.Gamma m / (Real.Gamma r * Real.Gamma s) * x ^ r * (1 - x) ^ s

/-- ch30-059 の因子の修正形: (Γ(m + 1)/(Γ(r + 1)Γ(s + 1))) x^r (1 − x)^s。 -/
noncomputable def fac059fix (r s m : ℕ) (x : ℝ) : ℝ :=
  Real.Gamma (m + 1) / (Real.Gamma (r + 1) * Real.Gamma (s + 1)) * x ^ r * (1 - x) ^ s

/-- ch30-059 (修正形、定理 th_30_059_fix の前提 hm に 057 m = r + s を写す): chance x のとき m 回のうち
r 回起こり s 回起こらない確率は二項の項 bterm m x r で、修正形の因子に等しい。 -/
theorem th_30_059_fix (r s m : ℕ) (hm : m = r + s) (x : ℝ) :
    fac059fix r s m x = bterm m x r := by
  unfold fac059fix bterm q
  rw [Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Nat.cast_choose ℝ (show r ≤ m by omega), show m - r = s by omega]

/-- bterm は Mathlib の二項分布 PMF.binomial の値 (phase14b の th_29_005_pmf の写し)。 -/
theorem th_30_059_pmf (x : NNReal) (hx : x ≤ 1) (m : ℕ) (i : Fin (m + 1)) :
    ((PMF.binomial x hx m i).toReal) = bterm m x i := by
  rw [PMF.binomial_apply]
  unfold bterm q
  simp only [Fin.val_last]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le (by exact_mod_cast hx) ENNReal.one_ne_top]
  simp
  ring

/-- ch30-059 (F30.6 案): Γk を k! と読めば Γm/(ΓrΓs) は二項係数 C(m, r)。 -/
theorem th_30_059_fact (r s m : ℕ) (hm : m = r + s) :
    (m.factorial : ℝ) / ((r.factorial : ℝ) * (s.factorial : ℝ)) = (m.choose r : ℝ) := by
  rw [Nat.cast_choose ℝ (show r ≤ m by omega), show m - r = s by omega]

/-- ch30-059 の反例 (F30.4): 印刷の n^r では、p = 2、q = 1 (n = 3)、r = 2、s = 1 (m = 3)、x = 1/2 で
因子は 9 となり 1 を超える (確率にならない)。二項の項 3/8 とも違う。 -/
theorem nec_30_059_n :
    1 < fac059 2 1 2 1 3 (1 / 2) ∧ fac059 2 1 2 1 3 (1 / 2) ≠ bterm 3 (1 / 2) 2 := by
  unfold fac059 bterm q pn
  have g3 : Real.Gamma ((3 : ℕ) : ℝ) = 2 := by
    rw [show ((3 : ℕ) : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  have g2 : Real.Gamma ((2 : ℕ) : ℝ) = 1 := by
    rw [show ((2 : ℕ) : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  rw [g3, g2]
  simp [Nat.choose]
  norm_num

/-- ch30-059 の反例 (F30.6 案): n^r を x^r に直しても、Γ を Γ 関数と読むと係数 Γm/(ΓrΓs) は二項係数でない。
m = 2、r = s = 1、x = 1/2 で (Γ2/(Γ1Γ1)) (1/2)(1/2) = 1/4、二項の項は 1/2。 -/
theorem nec_30_059_gamma :
    fac059x 1 1 2 (1 / 2) ≠ bterm 2 (1 / 2) 1 := by
  unfold fac059x bterm q
  have g2 : Real.Gamma ((2 : ℕ) : ℝ) = 1 := by
    rw [show ((2 : ℕ) : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  rw [g2]
  simp
  norm_num

/-- ch30-060 の右辺 (印刷の式): (Γm/(ΓrΓs)) ∫_0^1 x^{p+r}(1 − x)^{q+s}dx / ∫_0^1 x^p(1 − x)^q dx。 -/
noncomputable def Cr (p q r s m : ℕ) : ℝ :=
  Real.Gamma m / (Real.Gamma r * Real.Gamma s) *
    (∫ x in (0 : ℝ)..1, x ^ (p + r) * (1 - x) ^ (q + s)) /
      ∫ x in (0 : ℝ)..1, x ^ p * (1 - x) ^ q

/-- ch30-060: 「accordingly the total chance C_r, whatever x may be」= 056 の P_x と 059 の因子
(n^r を x^r に読んだもの、係数は印刷どおり Γm/(ΓrΓs)) の積を x について 0 から 1 まで積分したもの。 -/
theorem th_30_060 (p q r s m : ℕ) :
    ∫ x in (0 : ℝ)..1, Px p q x * fac059x r s m x = Cr p q r s m := by
  unfold Px fac059x Cr
  have e : ∀ x : ℝ, x ^ p * (1 - x) ^ q / (∫ y in (0 : ℝ)..1, y ^ p * (1 - y) ^ q) *
      (Real.Gamma m / (Real.Gamma r * Real.Gamma s) * x ^ r * (1 - x) ^ s)
      = (Real.Gamma m / (Real.Gamma r * Real.Gamma s) / ∫ y in (0 : ℝ)..1, y ^ p * (1 - y) ^ q) *
          (x ^ (p + r) * (1 - x) ^ (q + s)) := by
    intro x; rw [pow_add, pow_add]; ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul]; ring

/-- ch30-060 (係数を二項係数にした形、前提 hm に 057 を写す):
∫_0^1 P_x · C(m, r) x^r (1 − x)^s dx = C(m, r) ∫_0^1 x^{p+r}(1 − x)^{q+s}dx / ∫_0^1 x^p(1 − x)^q dx。 -/
theorem th_30_060_fix (p q r s m : ℕ) (hm : m = r + s) :
    ∫ x in (0 : ℝ)..1, Px p q x * bterm m x r
      = (m.choose r : ℝ) * (∫ x in (0 : ℝ)..1, x ^ (p + r) * (1 - x) ^ (q + s)) /
          ∫ x in (0 : ℝ)..1, x ^ p * (1 - x) ^ q := by
  unfold Px bterm
  have e : ∀ x : ℝ, x ^ p * (1 - x) ^ q / (∫ y in (0 : ℝ)..1, y ^ p * (1 - y) ^ q) *
      ((m.choose r : ℝ) * x ^ r * KeynesXXXb.q x ^ (m - r))
      = ((m.choose r : ℝ) / ∫ y in (0 : ℝ)..1, y ^ p * (1 - y) ^ q) *
          (x ^ (p + r) * (1 - x) ^ (q + s)) := by
    intro x; unfold KeynesXXXb.q; rw [show m - r = s by omega, pow_add, pow_add]; ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul]; ring

/-- ch30-060 (確かめ): 係数を二項係数にした C_r は r = 0, …, m で和 1。 -/
theorem th_30_060_sum (p q m : ℕ) :
    ∑ r ∈ range (m + 1), ∫ x in (0 : ℝ)..1, Px p q x * bterm m x r = 1 := by
  rw [← intervalIntegral.integral_finset_sum (fun r _ => by
    apply Continuous.intervalIntegrable; unfold Px bterm KeynesXXXb.q; fun_prop)]
  simp only [← Finset.mul_sum, th_29_005_one, mul_one]
  exact th_30_056_one p q

/-- ch30-060 の反例 (印刷の係数 Γm/(ΓrΓs)、F30.6 案): p = q = 0、r = s = 1 (m = 2) で印刷の C_r は 1/6、
係数を二項係数にした C_r (th_30_060_fix の左辺) は 1/3 で、両者は違う。 -/
theorem nec_30_060 :
    Cr 0 0 1 1 2 = 1 / 6 ∧ (∫ x in (0 : ℝ)..1, Px 0 0 x * bterm 2 x 1) = 1 / 3 ∧
      Cr 0 0 1 1 2 ≠ ∫ x in (0 : ℝ)..1, Px 0 0 x * bterm 2 x 1 := by
  have g4 : Real.Gamma 4 = 6 := by
    rw [show (4 : ℝ) = (3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num [Nat.factorial]
  have hC : Cr 0 0 1 1 2 = 1 / 6 := by
    unfold Cr; rw [beta_nat, beta_nat]; norm_num [g4]
  have hF : (∫ x in (0 : ℝ)..1, Px 0 0 x * bterm 2 x 1) = 1 / 3 := by
    rw [th_30_060_fix 0 0 1 1 2 rfl, beta_nat, beta_nat]; norm_num [g4, Nat.choose]
  refine ⟨hC, hF, ?_⟩
  rw [hC, hF]; norm_num

/-! ## 第 31 章 §3 (folio 386–387): 023・031 -/

/-- ch31-023: q := l/m。 -/
noncomputable def qratio (l m : ℕ) : ℝ := (l : ℝ) / m

/-- ch31-023 (定): l/m = q (名付け)。 -/
theorem th_31_023 (l m : ℕ) : qratio l m = (l : ℝ) / m := rfl

/-- x ∈ [0, 1] で x^k (1 − x)^{N−k} は x = k/N で最大 (重み付きの相加相乗平均)。 -/
theorem lik_max (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    x ^ k * (1 - x) ^ (N - k) ≤ ((k : ℝ) / N) ^ k * (1 - (k : ℝ) / N) ^ (N - k) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, sub_zero, one_pow, Nat.sub_zero]
    exact pow_le_one₀ (by linarith) (by linarith)
  rcases eq_or_lt_of_le hk with rfl | hkN
  · simp only [Nat.sub_self, pow_zero, mul_one, div_self hN'.ne', one_pow]
    exact pow_le_one₀ h0 h1
  set t : ℝ := (k : ℝ) / N with ht
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkN' : (k : ℝ) < N := by exact_mod_cast hkN
  have ht0 : 0 < t := div_pos hk' hN'
  have ht1 : t < 1 := (div_lt_one hN').mpr hkN'
  have h1t : 0 < 1 - t := by linarith
  have hp1 : 0 ≤ x / t := div_nonneg h0 ht0.le
  have hp2 : 0 ≤ (1 - x) / (1 - t) := div_nonneg (by linarith) h1t.le
  have hg := Real.geom_mean_le_arith_mean2_weighted ht0.le h1t.le hp1 hp2 (by ring)
  have hr : t * (x / t) + (1 - t) * ((1 - x) / (1 - t)) = 1 := by field_simp; ring
  rw [hr] at hg
  have hg' := Real.rpow_le_rpow (by positivity) hg (Nat.cast_nonneg N)
  rw [Real.one_rpow, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hp1, ← Real.rpow_mul hp2] at hg'
  have e1 : t * N = ((k : ℕ) : ℝ) := by rw [ht]; field_simp
  have e2 : (1 - t) * N = ((N - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk, ht]; field_simp
  rw [e1, e2, Real.rpow_natCast, Real.rpow_natCast] at hg'
  have htk : 0 < t ^ k * (1 - t) ^ (N - k) := mul_pos (pow_pos ht0 k) (pow_pos h1t _)
  have hsplit : x ^ k * (1 - x) ^ (N - k)
      = (x / t) ^ k * ((1 - x) / (1 - t)) ^ (N - k) * (t ^ k * (1 - t) ^ (N - k)) := by
    have ha : t ^ k ≠ 0 := (pow_pos ht0 k).ne'
    have hb : (1 - t) ^ (N - k) ≠ 0 := (pow_pos h1t _).ne'
    rw [div_pow x t k, div_pow (1 - x) (1 - t) (N - k)]; field_simp
  rw [hsplit]
  exact mul_le_of_le_one_left htk.le hg'

/-- 387 の式 f(q′)/h . f(q) / Σf(q′)/h . f(q): f(q′)/h . f(q) を Bernoulli の定理の値 bterm N q k
(N 事例のうち k 事例で A が B を伴う) と読み、和は q の取りうる値の有限集合 S にわたる。 -/
noncomputable def post (S : Finset ℝ) (N k : ℕ) (x : ℝ) : ℝ :=
  bterm N x k / ∑ s ∈ S, bterm N s k

/-- ch31-031 (分子): f(q′)/h . f(q) は q = k/N で最大。 -/
theorem th_31_031_lik (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    bterm N x k ≤ bterm N ((k : ℝ) / N) k := by
  unfold bterm q
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (lik_max N k hN hk x h0 h1) (Nat.cast_nonneg _)

/-- ch31-031 (修正形): 「it is a maximum when q = q′」。q′ を観測された割合 k/N に読み替える (印刷の語は B を
伴う数と伴わない数の比で、その読みでは成り立たない: nec_31_031_odds、F31.3)。 -/
theorem th_31_031 (S : Finset ℝ) (hS : ∀ s ∈ S, 0 ≤ s ∧ s ≤ 1) (N k : ℕ) (hN : 0 < N) (hk : k ≤ N)
    (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    post S N k x ≤ post S N k ((k : ℝ) / N) := by
  unfold post
  apply div_le_div_of_nonneg_right (th_31_031_lik N k hN hk x h0 h1)
  apply Finset.sum_nonneg
  intro s hs
  unfold bterm q
  have hs' := hS s hs
  have h1s : 0 ≤ 1 - s := by linarith
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs'.1 _)) (pow_nonneg h1s _)

/-- ch31-031 (最大の達成): q の取りうる値の集合 S が k/N を含めば、S 上の事後確率の最大値は q = k/N で達成される。
S に k/N が無ければ th_31_031 の上界は S 上の値としては達成されない。 -/
theorem th_31_031_mem (S : Finset ℝ) (hS : ∀ s ∈ S, 0 ≤ s ∧ s ≤ 1) (N k : ℕ) (hN : 0 < N) (hk : k ≤ N)
    (hkS : (k : ℝ) / N ∈ S) :
    IsGreatest ((fun x => post S N k x) '' (S : Set ℝ)) (post S N k ((k : ℝ) / N)) := by
  refine ⟨⟨_, Finset.mem_coe.mpr hkS, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h := hS x (Finset.mem_coe.mp hx)
  exact th_31_031 S hS N k hN hk x h.1 h.2

/-- ch31-031 の反例 (F31.3):q′ を印刷の語どおり比 k/(N − k) と読むと、N = 3、k = 1 で q′ = 1/2 の値 3/8 は
q = 1/3 の値 4/9 より小さく、最大ではない。 -/
theorem nec_31_031_odds :
    bterm 3 ((1 : ℝ) / (3 - 1)) 1 < bterm 3 ((1 : ℝ) / 3) 1 := by
  unfold bterm q; norm_num [Nat.choose]

end KeynesXXXb

/-! ## #print axioms -/
-- 写しと記法
#print axioms KeynesXXXb.q
#print axioms KeynesXXXb.bterm
#print axioms KeynesXXXb.th_29_005_one
-- §4: 005・007・008・009
#print axioms KeynesXXXb.mu
#print axioms KeynesXXXb.th_30_005
#print axioms KeynesXXXb.mpq
#print axioms KeynesXXXb.Θ
#print axioms KeynesXXXb.probWithin
#print axioms KeynesXXXb.propWithin
#print axioms KeynesXXXb.Pdir
#print axioms KeynesXXXb.sqrt_div_m
#print axioms KeynesXXXb.propWithin_eq
#print axioms KeynesXXXb.Pdir_eq
#print axioms KeynesXXXb.vanish
#print axioms KeynesXXXb.th_30_007
#print axioms KeynesXXXb.q_ratio
#print axioms KeynesXXXb.th_30_008
#print axioms KeynesXXXb.Pinv
#print axioms KeynesXXXb.Pinvfix
#print axioms KeynesXXXb.th_30_009_subst
#print axioms KeynesXXXb.nec_30_009
#print axioms KeynesXXXb.nec_30_009_gt
#print axioms KeynesXXXb.tendsto_mul_left_nat
#print axioms KeynesXXXb.th_30_009_fix
#print axioms KeynesXXXb.nec_30_009_lim
-- §9: 021・026・029・034・035
#print axioms KeynesXXXb.beta_nat
#print axioms KeynesXXXb.beta_nat_pos
#print axioms KeynesXXXb.Acoef
#print axioms KeynesXXXb.th_30_021
#print axioms KeynesXXXb.th_30_026
#print axioms KeynesXXXb.th_30_029
#print axioms KeynesXXXb.nec_30_029
#print axioms KeynesXXXb.bachNext
#print axioms KeynesXXXb.th_30_034
#print axioms KeynesXXXb.nec_30_034
#print axioms KeynesXXXb.ωpoly
#print axioms KeynesXXXb.th_30_035
-- §12: 054・056・057・059・060
#print axioms KeynesXXXb.pn
#print axioms KeynesXXXb.th_30_054
#print axioms KeynesXXXb.Px
#print axioms KeynesXXXb.th_30_056
#print axioms KeynesXXXb.th_30_056_one
#print axioms KeynesXXXb.fac059
#print axioms KeynesXXXb.fac059x
#print axioms KeynesXXXb.fac059fix
#print axioms KeynesXXXb.th_30_059_fix
#print axioms KeynesXXXb.th_30_059_pmf
#print axioms KeynesXXXb.th_30_059_fact
#print axioms KeynesXXXb.nec_30_059_n
#print axioms KeynesXXXb.nec_30_059_gamma
#print axioms KeynesXXXb.Cr
#print axioms KeynesXXXb.th_30_060
#print axioms KeynesXXXb.th_30_060_fix
#print axioms KeynesXXXb.th_30_060_sum
#print axioms KeynesXXXb.nec_30_060
-- 第 31 章: 023・031
#print axioms KeynesXXXb.qratio
#print axioms KeynesXXXb.th_31_023
#print axioms KeynesXXXb.lik_max
#print axioms KeynesXXXb.post
#print axioms KeynesXXXb.th_31_031_lik
#print axioms KeynesXXXb.th_31_031
#print axioms KeynesXXXb.th_31_031_mem
#print axioms KeynesXXXb.nec_31_031_odds
