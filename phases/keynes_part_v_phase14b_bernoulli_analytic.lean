/-
# Keynes (1921) *A Treatise on Probability* Part V — Lean 4 Phase 14b
# 第 XXIX 章 §2–§5 (folio 338–342): Bernoulli の定理の解析的導出
#
# この 40 行 (台帳 ch29-001〜040) は Keynes の確率論理 (a/h) を含まず、二項係数・Stirling・正規近似の解析である。
# Keynes が省いた導出は次の所で補った: 最大項 (008・009、「easily shown」→ 比の補題 bterm_ratio)、Stirling の h = 0 の場合 (012)、
#   非対称の消え方 (016・017、「easily seen」→ h = 1 の比)、変数変換 (023)、Bernoulli の言明 (034・035、分散と Chebyshev の評価)。
# 分担: B36 (phase14a) は §6–§7 の Keynes 記法の前提 (041〜054)、B39 は 055〜088 (§8 Poisson の定理 055〜063、§11 継起の規則 070〜088)、
#   本ファイルは 001〜040。
#
# ## 基準
#   1921 年 Macmillan 初版の頁画像のみ (folio 338–342)。定理名は th_29_<行番号>。台帳の行 ID は各定理の docstring に書く。
#
# ## 原典 (folio 338、§2)
#   「The probability of the event's occurring n times and failing m − n times out of the m occasions is
#    (subject to certain conditions to be elucidated later) p^n q^{m−n} multiplied by the coefficient of this
#    expression in the expansion of (p + q)^m, where p + q = 1. If we write n = mp − h, this term is
#    m!/((mp − h)! (mq + h)!) p^n q^{m−n}. It is easily shown that this is a maximum when h = 0, i.e. when n = mp
#    (or the nearest integer to this, where mp is not integral). … Provided that m is large, we can simplify the
#    expression … by means of Stirling's Theorem, and obtain as its approximate value 1/√(2πmpq) · e^{−h²/2mpq}.
#    As before, this is a maximum when h = 0, i.e. when n = mp.」
#   (folio 339) 「… the approximation implies a symmetrical distribution for different values of h about the value
#    for h = 0; while the expression under approximation is unsymmetrical. It is easily seen that this want of
#    symmetry is appreciable unless mpq is large. … the probability that the amount of the divergence from the
#    most probable value mp will lie between z and z + dz, is 1/√(2πmpq) e^{−z²/2mpq} dz. … The probability that
#    the divergence h … will be less than some given quantity a is, therefore, 1/√(2πmpq) ∫_{−a}^{+a} e^{−z²/2mpq} dz.
#    If we put z/√(2mpq) = t, this is equal to 2/√π ∫_0^{a/√(2mpq)} e^{−t²} dt. Thus, if we write a = √(2mpq) γ,
#    the probability that the number of occurrences will lie between mp + √(2mpq) γ and mp − √(2mpq) γ is measured
#    by 2/√π ∫_0^γ e^{−t²} dt.」 脚注 1: 「the error does not lie between h and h + 1.」
#    脚注 2: 「Some writers, using rather more precision, give the result as 2/√π ∫_0^γ e^{−t²}dt + e^{−γ²}/√(2πmpq)」
#   (folio 340) 「the proportion of occurrences will lie between p + √(2pq/m) γ and p − √(2pq/m) γ.
#    The different values of the integral 2/√π ∫_0^t e^{−t²}dt = Θ(t) are given in tables. … varies with the
#    magnitude of √(2pq/m) …」 §3: 「r/t is the probability … the proportionate number of the event's occurrences
#    will lie between (r + 1)/t and (r − 1)/t, is greater than c.」
#   (folio 341–342、§5) 二面とも表か二面とも裏かの硬貨: 「the probability of m heads and m tails in 2m tosses is
#    zero, and it is certain à priori that there will be either 2m heads or none.」「p^r is the probability of r
#    occurrences running」「the first r − 1 occasions」「If we wish to employ the expression 2/√π ∫_0^γ e^{−t²}dt
#    we are in a worse position. For this is an approximate formula which requires … that the series should be long」
#
# ## 記法の読み (定義のみ)
#   q p          : q := 1 − p (002 の「where p + q = 1」)。
#   bterm m p n  : 二項の一般項 C(m, n) p^n q^{m−n} (004・005・007)。
#   hdev m p n   : h := mp − n (006)。
#   nearest x    : 「the nearest integer」= round x (010、Keynes の文言どおり)。
#   mpq m p      : m p q (016)。
#   gauss m p h  : 1/√(2πmpq) · e^{−h²/2mpq} (012・020)。
#   Θ t          : 2/√π ∫_0^t e^{−u²} du (031; 印刷は積分変数も上限も t、F29.6)。
#   probWithin m p a : 二項分布で |n − mp| < a となる確率 (022・026・027 の「probability」)。
#
# ## 外部公理 (Mathlib にないもの)
#   ax_stirling_approx : 局所 de Moivre–Laplace 定理 (012 の一般の h)。p ∈ (0, 1) を固定し |h| ≤ C√m の範囲で
#                        bterm / gauss → 1 (一様)。標準的な定理 (Feller, vol. I, ch. VII §2) であり、ここでは公理として置く。
#   ax_normal_approx   : 積分形の de Moivre–Laplace 定理 (022・027・029)。|n − mp| < √(2mpq) γ の確率 → Θ(γ)。
#   どちらも実解析の真な定理の言明で、Lean の中では証明していない (無矛盾性はその真理性による; 模型は置いていない)。
#   ax_stirling_approx・ax_normal_approx は真な言明なので反例の模型は作れない。必要性は、公理を外すと参照が解決しない
#   こと (th_29_012・th_29_022・th_29_027・th_29_029_lim が通らなくなる) と、前提 p < 1 を外すと偽になる例
#   (p = 1 なら左辺 0、Θ(γ) > 0; nec_ax_normal_approx_p1) で示す。
#   Stirling の公式そのもの (011) は Mathlib の Stirling.factorial_isEquivalent_stirling の付け替え (借用) で、
#   印刷の式を Stirling で扱うのは h = 0 の場合 (012_h0) だけ。どちらも公理に依らない。
#
# ## 所見候補
#   F29.12: 338 の「(or the nearest integer to this, where mp is not integral)」は一般に偽 (nec_29_010・nec_29_010_small)。
#           最大項は mp − q ≤ N ≤ mp + p の整数 N = ⌊(m + 1)p⌋ (th_29_010_fix、0 ≤ p < 1)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_v_phase14b_bernoulli_analytic.lean
-/
import Mathlib

namespace KeynesXXIXb

open Real Finset Filter Topology Asymptotics

/-! ## 記法 (定義のみ) -/

/-- ch29-002: q := 1 − p (「where p + q = 1」の名付け)。 -/
noncomputable def q (p : ℝ) : ℝ := 1 - p

/-- ch29-004・005・007: 二項の一般項 C(m, n) p^n q^{m−n}。 -/
noncomputable def bterm (m : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  (m.choose n : ℝ) * p ^ n * q p ^ (m - n)

/-- ch29-006: h := mp − n (「If we write n = mp − h」の名付け)。 -/
noncomputable def hdev (m : ℕ) (p : ℝ) (n : ℕ) : ℝ := m * p - n

/-- ch29-010: 「the nearest integer」(Keynes の文言どおり、round)。 -/
noncomputable def nearest (x : ℝ) : ℤ := round x

/-- ch29-016: mpq。 -/
noncomputable def mpq (m : ℕ) (p : ℝ) : ℝ := m * p * q p

/-- ch29-012・020: 1/√(2πmpq) · e^{−h²/2mpq}。 -/
noncomputable def gauss (m : ℕ) (p h : ℝ) : ℝ :=
  1 / √(2 * π * mpq m p) * exp (-(h ^ 2) / (2 * mpq m p))

/-- ch29-031: Θ(t) = 2/√π ∫_0^t e^{−u²} du (印刷は積分変数も t)。 -/
noncomputable def Θ (t : ℝ) : ℝ := 2 / √π * ∫ u in (0 : ℝ)..t, exp (-(u ^ 2))

/-- 022・026・027: 二項分布で |n − mp| < a となる確率。 -/
noncomputable def probWithin (m : ℕ) (p a : ℝ) : ℝ :=
  ∑ n ∈ (range (m + 1)).filter (fun n : ℕ => |(n : ℝ) - m * p| < a), bterm m p n

/-! ## 002・005・007: 二項の一般項 -/

/-- ch29-002 (定義のみ: q の名付け)。 -/
theorem th_29_002 (p : ℝ) : p + q p = 1 := by unfold q; ring

theorem bterm_nonneg (m : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : ℕ) : 0 ≤ bterm m p n := by
  unfold bterm q
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- ch29-005: bterm は (p + q)^m の展開の項 (Mathlib add_pow)。 -/
theorem th_29_005 (m : ℕ) (p : ℝ) : (p + q p) ^ m = ∑ n ∈ range (m + 1), bterm m p n := by
  rw [add_pow]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold bterm; ring

theorem th_29_005_one (m : ℕ) (p : ℝ) : ∑ n ∈ range (m + 1), bterm m p n = 1 := by
  rw [← th_29_005, th_29_002, one_pow]

/-- ch29-005: Mathlib の二項分布 PMF.binomial の値は bterm。 -/
theorem th_29_005_pmf (p : NNReal) (hp : p ≤ 1) (m : ℕ) (i : Fin (m + 1)) :
    ((PMF.binomial p hp m i).toReal) = bterm m p i := by
  rw [PMF.binomial_apply]
  unfold bterm q
  have hp' : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  simp only [Fin.val_last]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le (by exact_mod_cast hp) ENNReal.one_ne_top]
  simp
  ring

/-- ch29-007: n = mp − h と書くと mp − h = n、mq + h = m − n で、
m!/((mp − h)!(mq + h)!) p^n q^{m−n} は bterm に等しい。 -/
theorem th_29_007 (m n : ℕ) (hn : n ≤ m) (p : ℝ) :
    (m : ℝ) * p - hdev m p n = n ∧ (m : ℝ) * q p + hdev m p n = ((m - n : ℕ) : ℝ) ∧
    (m.factorial : ℝ) / ((n.factorial : ℝ) * ((m - n).factorial : ℝ)) * p ^ n * q p ^ (m - n)
      = bterm m p n := by
  refine ⟨by unfold hdev; ring, ?_, ?_⟩
  · unfold hdev q; rw [Nat.cast_sub hn]; ring
  · unfold bterm; rw [Nat.cast_choose ℝ hn]

/-! ## 008・009・010: 最大項 (「It is easily shown」を補う) -/

/-- 隣り合う項の比: T(n+1)·(n+1)q = T(n)·(m − n)p。 -/
theorem bterm_ratio (m n : ℕ) (hn : n < m) (p : ℝ) :
    bterm m p (n + 1) * (((n : ℝ) + 1) * q p) = bterm m p n * (((m : ℝ) - n) * p) := by
  unfold bterm
  have h1 : m - n = (m - (n + 1)) + 1 := by omega
  have hc : ((m.choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) = (m.choose n : ℝ) * ((m : ℝ) - n) := by
    have h2 := congrArg (fun k : ℕ => (k : ℝ)) (Nat.choose_succ_right_eq m n)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hn.le] at h2
    exact h2
  rw [h1, pow_succ (q p) (m - (n + 1)), pow_succ p n]
  linear_combination (p ^ n * p * q p ^ (m - (n + 1)) * q p) * hc

theorem step_up (m n : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : n < m)
    (hle : (n : ℝ) + 1 ≤ m * p + p) : bterm m p n ≤ bterm m p (n + 1) := by
  rcases eq_or_lt_of_le h1 with hp | hp
  · have : bterm m p n = 0 := by
      unfold bterm q; rw [hp, sub_self, zero_pow (by omega)]; ring
    rw [this]; exact bterm_nonneg m h0 h1 _
  · have hq : 0 < q p := by unfold q; linarith
    have hr := bterm_ratio m n hn p
    have hb := bterm_nonneg m h0 h1 n
    have key : ((n : ℝ) + 1) * q p ≤ ((m : ℝ) - n) * p := by unfold q; nlinarith
    have hpos : 0 < ((n : ℝ) + 1) * q p := by positivity
    have : bterm m p n * (((n : ℝ) + 1) * q p) ≤ bterm m p (n + 1) * (((n : ℝ) + 1) * q p) := by
      rw [hr]; exact mul_le_mul_of_nonneg_left key hb
    exact le_of_mul_le_mul_right this hpos

theorem step_down (m n : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hge : (m : ℝ) * p - q p ≤ n) : bterm m p (n + 1) ≤ bterm m p n := by
  rcases lt_or_ge n m with hn | hn
  · have hq : 0 < q p := by
      by_contra hcon
      have hq0 : q p = 0 := le_antisymm (not_lt.mp hcon) (by unfold q; linarith)
      have hp1 : p = 1 := by unfold q at hq0; linarith
      rw [hq0, hp1] at hge
      have : (n : ℝ) < m := by exact_mod_cast hn
      linarith
    have hr := bterm_ratio m n hn p
    have hb := bterm_nonneg m h0 h1 n
    have key : ((m : ℝ) - n) * p ≤ ((n : ℝ) + 1) * q p := by unfold q at hge ⊢; nlinarith
    have hpos : 0 < ((n : ℝ) + 1) * q p := by positivity
    have : bterm m p (n + 1) * (((n : ℝ) + 1) * q p) ≤ bterm m p n * (((n : ℝ) + 1) * q p) := by
      rw [hr]; exact mul_le_mul_of_nonneg_left key hb
    exact le_of_mul_le_mul_right this hpos
  · have : bterm m p (n + 1) = 0 := by
      unfold bterm; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [this]; exact bterm_nonneg m h0 h1 n

/-- 最大項の一般形: mp − q ≤ N ≤ mp + p (N ≤ m) なら T(N) が最大。 -/
theorem th_29_mode (m N : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hNm : N ≤ m)
    (hlo : (m : ℝ) * p - q p ≤ N) (hhi : (N : ℝ) ≤ m * p + p) :
    ∀ k : ℕ, bterm m p k ≤ bterm m p N := by
  have up : ∀ d, d ≤ N → bterm m p (N - d) ≤ bterm m p N := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h' := ih (by omega)
      have hs : N - (d + 1) + 1 = N - d := by omega
      have hc : ((N - (d + 1) : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
        have : N - (d + 1) + 1 ≤ N := by omega
        exact_mod_cast this
      have := step_up m (N - (d + 1)) h0 h1 (by omega) (by linarith)
      rw [hs] at this; linarith
  have down : ∀ d, bterm m p (N + d) ≤ bterm m p N := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have := step_down m (N + d) h0 h1 (by push_cast; linarith)
      rw [← add_assoc]; linarith
  intro k
  rcases le_or_gt k N with hk | hk
  · have := up (N - k) (by omega); rwa [Nat.sub_sub_self hk] at this
  · have := down (k - N); rwa [Nat.add_sub_of_le hk.le] at this

/-- ch29-009: mp が整数 N なら、n = N で項は最大 (0 ≤ p ≤ 1)。 -/
theorem th_29_009 (m N : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hN : (N : ℝ) = m * p) :
    ∀ k : ℕ, bterm m p k ≤ bterm m p N := by
  have hNm : N ≤ m := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : (N : ℝ) ≤ m := by rw [hN]; nlinarith
    exact_mod_cast this
  exact th_29_mode m N h0 h1 hNm (by unfold q; linarith) (by linarith)

/-- ch29-008: h = 0 (h := mp − N) のとき項は最大。 -/
theorem th_29_008 (m N : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hN : hdev m p N = 0) :
    ∀ k : ℕ, bterm m p k ≤ bterm m p N :=
  th_29_009 m N h0 h1 (by unfold hdev at hN; linarith)

/-- ch29-010 (反例): 「or the nearest integer to this」は一般には偽。m = 6、p = 9/10 で mp = 5.4、
最も近い整数は 5 だが、T(6) > T(5)。 -/
theorem nec_29_010 :
    nearest ((6 : ℕ) * (9 / 10 : ℝ)) = 5 ∧ bterm 6 (9 / 10) 5 < bterm 6 (9 / 10) 6 := by
  constructor
  · unfold nearest; rw [round_eq, Int.floor_eq_iff]; norm_num
  · unfold bterm q; norm_num [Nat.choose]

/-- ch29-010 (反例、p が小さい側): m = 6、p = 1/10 で mp = 0.6、最も近い整数は 1 だが T(0) > T(1)。 -/
theorem nec_29_010_small :
    nearest ((6 : ℕ) * (1 / 10 : ℝ)) = 1 ∧ bterm 6 (1 / 10) 1 < bterm 6 (1 / 10) 0 := by
  constructor
  · unfold nearest; rw [round_eq, Int.floor_eq_iff]; norm_num
  · unfold bterm q; norm_num [Nat.choose]

/-- ch29-010 (修正形): 0 ≤ p < 1 なら N = ⌊(m + 1)p⌋ で項は最大。N は mp に隣り合う整数の一つ
(|N − mp| < 1) だが、最も近い整数とは限らない。 -/
theorem th_29_010_fix (m : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    (∀ k : ℕ, bterm m p k ≤ bterm m p ⌊((m : ℝ) + 1) * p⌋₊) ∧
      |(⌊((m : ℝ) + 1) * p⌋₊ : ℝ) - m * p| < 1 := by
  have hx : 0 ≤ ((m : ℝ) + 1) * p := by positivity
  have hlo := Nat.lt_floor_add_one (((m : ℝ) + 1) * p)
  have hhi := Nat.floor_le hx
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set N := ⌊((m : ℝ) + 1) * p⌋₊
  have hNm : N ≤ m := by
    have : (N : ℝ) < m + 1 := by nlinarith
    have : N < m + 1 := by exact_mod_cast this
    omega
  refine ⟨th_29_mode m N h0 h1.le hNm (by unfold q; linarith) (by linarith), ?_⟩
  rw [abs_lt]; constructor <;> linarith

/-! ## 011・012: Stirling -/

/-- ch29-011 (≈ 借用): Stirling の定理 n! ∼ √(2πn)(n/e)^n。Mathlib の
Stirling.factorial_isEquivalent_stirling の付け替えで、印刷の式は扱わない (印刷の式は th_29_012_h0)。 -/
theorem th_29_011 : IsEquivalent atTop (fun n : ℕ => (n.factorial : ℝ))
    (fun n => √(2 * n * π) * (n / exp 1) ^ n) := Stirling.factorial_isEquivalent_stirling

theorem tendsto_mul_left_nat (k : ℕ) (hk : 0 < k) : Tendsto (fun N : ℕ => k * N) atTop atTop :=
  tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hk) tendsto_id

/-- ch29-012 (h = 0 の場合、≈): p = a/b、m = bN、n = aN (mp が整数) のとき、
T(n) ∼ 1/√(2πmpq) (N → ∞)。Mathlib の Stirling だけから。 -/
theorem th_29_012_h0 (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    IsEquivalent atTop (fun N : ℕ => bterm (b * N) ((a : ℝ) / b) (a * N))
      (fun N : ℕ => gauss (b * N) ((a : ℝ) / b) 0) := by
  set c := b - a with hcdef
  have hc : 0 < c := by omega
  have hb : 0 < b := by omega
  have hF := th_29_011
  have hB := hF.comp_tendsto (tendsto_mul_left_nat b hb)
  have hA := hF.comp_tendsto (tendsto_mul_left_nat a ha)
  have hC := hF.comp_tendsto (tendsto_mul_left_nat c hc)
  have hall := (hB.div (hA.mul hC)).mul
    (IsEquivalent.refl (u := fun N : ℕ => ((a : ℝ) / b) ^ (a * N) * q ((a : ℝ) / b) ^ (c * N))
      (l := atTop))
  refine (hall.congr_left ?_).congr_right ?_
  · refine Eventually.of_forall (fun N => ?_)
    have hsub : b * N - a * N = c * N := by rw [hcdef, Nat.sub_mul]
    simp only [Function.comp, Pi.mul_apply, Pi.div_apply]
    unfold bterm
    rw [Nat.cast_choose ℝ (Nat.mul_le_mul_right N hab.le), hsub]
    ring
  · filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp, Pi.mul_apply, Pi.div_apply]
    have hx : (0 : ℝ) < N := by exact_mod_cast hN
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    have hcb : (c : ℝ) = b - a := by rw [hcdef, Nat.cast_sub hab.le]
    have hq : q ((a : ℝ) / b) = c / b := by unfold q; rw [hcb]; field_simp
    have hAC : b * N = a * N + c * N := by rw [hcdef, ← Nat.add_mul, Nat.add_sub_cancel' hab.le]
    have he : 0 < exp 1 := exp_pos 1
    -- 冪の部分
    have hpow : ((b * N : ℕ) / exp 1) ^ (b * N) /
        (((a * N : ℕ) / exp 1) ^ (a * N) * ((c * N : ℕ) / exp 1) ^ (c * N))
        * (((a : ℝ) / b) ^ (a * N) * ((c : ℝ) / b) ^ (c * N)) = 1 := by
      have e1 : (((a * N : ℕ) : ℝ) / exp 1) ^ (a * N)
          = ((a : ℝ) / b) ^ (a * N) * (((b * N : ℕ) : ℝ) / exp 1) ^ (a * N) := by
        rw [← mul_pow]; congr 1; push_cast; field_simp
      have e2 : (((c * N : ℕ) : ℝ) / exp 1) ^ (c * N)
          = ((c : ℝ) / b) ^ (c * N) * (((b * N : ℕ) : ℝ) / exp 1) ^ (c * N) := by
        rw [← mul_pow]; congr 1; push_cast; field_simp
      rw [e1, e2]
      conv_lhs => rw [show (b * N) = a * N + c * N from hAC]
      rw [pow_add]
      have : ((b * N : ℕ) : ℝ) / exp 1 ≠ 0 := by
        apply div_ne_zero _ he.ne'; positivity
      field_simp
    -- 平方根の部分
    have hsq : √(2 * ((b * N : ℕ) : ℝ) * π) /
        (√(2 * ((a * N : ℕ) : ℝ) * π) * √(2 * ((c * N : ℕ) : ℝ) * π))
        = 1 / √(2 * π * mpq (b * N) ((a : ℝ) / b)) := by
      unfold mpq
      rw [hq, div_eq_div_iff (by positivity) (by positivity), one_mul, ← sqrt_mul (by positivity),
        ← sqrt_mul (by positivity)]
      congr 1
      push_cast
      field_simp
    unfold gauss
    rw [hq]
    have he0 : exp (-(0 : ℝ) ^ 2 / (2 * mpq (b * N) ((a : ℝ) / b))) = 1 := by simp
    rw [he0, mul_one]
    linear_combination (√(2 * ((b * N : ℕ) : ℝ) * π) /
      (√(2 * ((a * N : ℕ) : ℝ) * π) * √(2 * ((c * N : ℕ) : ℝ) * π))) * hpow + hsq

/-- 局所 de Moivre–Laplace 定理 (外部公理): p ∈ (0, 1) を固定すると、|h| ≤ C√m の範囲で一様に
bterm m p n / gauss m p h → 1 (h = mp − n)。 -/
axiom ax_stirling_approx (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (C ε : ℝ) (hε : 0 < ε) :
  ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ n : ℕ, n ≤ m → |hdev m p n| ≤ C * √m →
    |bterm m p n / gauss m p (hdev m p n) - 1| ≤ ε

/-- ch29-012 (外部公理依存): 「obtain as its approximate value 1/√(2πmpq) · e^{−h²/2mpq}」。 -/
theorem th_29_012 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (C ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ n : ℕ, n ≤ m → |hdev m p n| ≤ C * √m →
      |bterm m p n / gauss m p (hdev m p n) - 1| ≤ ε :=
  ax_stirling_approx p hp0 hp1 C ε hε

/-! ## 013・014・015: 近似式の最大と対称 -/

/-- ch29-013: 近似式は h = 0 で最大。 -/
theorem th_29_013 (m : ℕ) (p h : ℝ) (hv : 0 ≤ mpq m p) : gauss m p h ≤ gauss m p 0 := by
  unfold gauss
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  have : 0 ≤ h ^ 2 / (2 * mpq m p) := by positivity
  rw [neg_div]; simp; exact this

/-- ch29-013 (強い形): mpq > 0、h ≠ 0 なら狭義。 -/
theorem th_29_013_strict (m : ℕ) (p h : ℝ) (hv : 0 < mpq m p) (hh : h ≠ 0) :
    gauss m p h < gauss m p 0 := by
  unfold gauss
  apply mul_lt_mul_of_pos_left _ (by positivity)
  apply exp_lt_exp.mpr
  have : 0 < h ^ 2 / (2 * mpq m p) := by positivity
  rw [neg_div]; simp; exact this

/-- ch29-014: n = mp で近似式は最大 (n を実数として)。 -/
theorem th_29_014 (m : ℕ) (p : ℝ) (hv : 0 ≤ mpq m p) (x : ℝ) :
    gauss m p (m * p - x) ≤ gauss m p (m * p - m * p) := by
  rw [sub_self]; exact th_29_013 m p _ hv

/-- ch29-015: 近似式は h の符号によらない (h = 0 について対称)。 -/
theorem th_29_015 (m : ℕ) (p h : ℝ) : gauss m p (-h) = gauss m p h := by
  unfold gauss; rw [neg_sq]

/-- ch29-015: 近似される式は対称でない。m = 3、p = 1/3 (mp = 1) で h = 1 と h = −1 の項が違う。 -/
theorem th_29_015_asym :
    hdev 3 (1 / 3) 0 = -(hdev 3 (1 / 3) 2) ∧ bterm 3 (1 / 3) 0 ≠ bterm 3 (1 / 3) 2 := by
  unfold hdev bterm q
  norm_num [Nat.choose]

/-! ## 016・017: 非対称は mpq が大きければ小さい (「It is easily seen」を h = 1 で補う) -/

/-- ch29-016 (h = 1): k = mp が整数のとき T(k+1)(mpq + q) = T(k−1)(mpq + p)。 -/
theorem th_29_016 (m k : ℕ) (p : ℝ) (hk1 : 1 ≤ k) (hkm : k < m) (hk : (k : ℝ) = m * p) :
    bterm m p (k + 1) * (mpq m p + q p) = bterm m p (k - 1) * (mpq m p + p) := by
  have hr1 := bterm_ratio m k hkm p
  have hr2 := bterm_ratio m (k - 1) (by omega) p
  rw [Nat.sub_add_cancel hk1] at hr2
  have hc : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk1]; simp
  rw [hc, hk] at hr2
  rw [hk] at hr1
  unfold mpq
  unfold q at *
  linear_combination hr1 + hr2

/-- ch29-016・017: 比 (mpq + p)/(mpq + q) は mpq → ∞ で 1 に近づく。 -/
theorem th_29_016_lim (p : ℝ) :
    Tendsto (fun v : ℝ => (v + p) / (v + q p)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun v : ℝ => (p - q p) / (v + q p)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h2 : Tendsto (fun v : ℝ => 1 + (p - q p) / (v + q p)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (-(q p))] with v hv
  have : v + q p ≠ 0 := by linarith
  field_simp
  ring

/-! ## 020: 正規密度 -/

/-- ch29-020: 1/√(2πmpq) e^{−z²/2mpq} は Mathlib の正規密度 N(0, mpq)。 -/
theorem th_29_020 (m : ℕ) (p : ℝ) (hv : 0 < mpq m p) (z : ℝ) :
    gauss m p z = ProbabilityTheory.gaussianPDFReal 0 ⟨mpq m p, hv.le⟩ z := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  unfold gauss
  simp [one_div]

theorem th_29_020_one (m : ℕ) (p : ℝ) (hv : 0 < mpq m p) : ∫ z, gauss m p z = 1 := by
  simp_rw [th_29_020 m p hv]
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  intro h
  have := congrArg (fun x : NNReal => (x : ℝ)) h
  simp at this
  linarith

/-! ## 022〜027: 変数変換と Θ -/

theorem cont_gaussexp (v : ℝ) : Continuous (fun z : ℝ => exp (-(z ^ 2) / (2 * v))) := by fun_prop

theorem cont_exp_neg_sq : Continuous (fun u : ℝ => exp (-(u ^ 2))) := by fun_prop

/-- ch29-023 の帰結: z/√(2v) = t の変数変換で ∫_0^{a/√(2v)} e^{−t²} dt = (√(2v))⁻¹ ∫_0^a e^{−z²/2v} dz。
印刷の z/√(2mpq) = t は置換の宣言 (定義のみ) で、台帳は 023 を未とし、この等式を 024 の ✓ に数える。 -/
theorem th_29_023 (v a : ℝ) (hv : 0 < v) :
    ∫ t in (0 : ℝ)..(a / √(2 * v)), exp (-(t ^ 2))
      = (√(2 * v))⁻¹ * ∫ z in (0 : ℝ)..a, exp (-(z ^ 2) / (2 * v)) := by
  have hs : 0 < √(2 * v) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : √(2 * v) ^ 2 = 2 * v := Real.sq_sqrt (by linarith)
  have := intervalIntegral.integral_comp_mul_left (fun z => exp (-(z ^ 2) / (2 * v)))
    (a := 0) (b := a / √(2 * v)) hs.ne'
  simp only [mul_zero, smul_eq_mul] at this
  rw [show √(2 * v) * (a / √(2 * v)) = a by field_simp] at this
  rw [← this]
  congr 1
  ext t
  congr 1
  rw [mul_pow, hs2]
  field_simp

/-- 偶関数の積分: ∫_{−a}^{a} = 2 ∫_0^a。 -/
theorem integral_even (v a : ℝ) :
    ∫ z in (-a)..a, exp (-(z ^ 2) / (2 * v)) = 2 * ∫ z in (0 : ℝ)..a, exp (-(z ^ 2) / (2 * v)) := by
  have hc := cont_gaussexp v
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := a)
    (fun z => exp (-(z ^ 2) / (2 * v)))
  simp only [neg_sq, neg_zero] at hneg
  rw [← hneg]
  ring

/-- ch29-022 = ch29-024: 1/√(2πv) ∫_{−a}^{a} e^{−z²/2v} dz = Θ(a/√(2v))。 -/
theorem th_29_024_v (v a : ℝ) (hv : 0 < v) :
    1 / √(2 * π * v) * ∫ z in (-a)..a, exp (-(z ^ 2) / (2 * v)) = Θ (a / √(2 * v)) := by
  unfold Θ
  rw [th_29_023 v a hv, integral_even]
  have hs : 0 < √(2 * v) := Real.sqrt_pos.mpr (by linarith)
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  have hsplit : √(2 * π * v) = √(2 * v) * √π := by
    rw [← sqrt_mul (by linarith)]; congr 1; ring
  rw [hsplit]
  field_simp

/-- ch29-024: mpq > 0 のとき 022 の積分は 2/√π ∫_0^{a/√(2mpq)} e^{−t²} dt。 -/
theorem th_29_024 (m : ℕ) (p a : ℝ) (hv : 0 < mpq m p) :
    1 / √(2 * π * mpq m p) * ∫ z in (-a)..a, exp (-(z ^ 2) / (2 * mpq m p))
      = Θ (a / √(2 * mpq m p)) :=
  th_29_024_v _ a hv

/-- ch29-025 (定義のみ): a = √(2mpq) γ と書くと a/√(2mpq) = γ。 -/
theorem th_29_025 (m : ℕ) (p a γ : ℝ) (hv : 0 < mpq m p) (ha : a = √(2 * mpq m p) * γ) :
    a / √(2 * mpq m p) = γ := by
  have hs : 0 < √(2 * mpq m p) := Real.sqrt_pos.mpr (by linarith)
  rw [ha]; field_simp

/-- ch29-026: |n − mp| < √(2mpq)γ ⇔ mp − √(2mpq)γ < n < mp + √(2mpq)γ。 -/
theorem th_29_026 (m : ℕ) (p γ x : ℝ) :
    |x - m * p| < √(2 * mpq m p) * γ ↔
      m * p - √(2 * mpq m p) * γ < x ∧ x < m * p + √(2 * mpq m p) * γ := by
  rw [abs_sub_lt_iff]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- ch29-027 (恒等式の部分): a = √(2mpq)γ のとき 022 の積分は Θ(γ)。 -/
theorem th_29_027_eq (m : ℕ) (p γ : ℝ) (hv : 0 < mpq m p) :
    1 / √(2 * π * mpq m p) *
      ∫ z in (-(√(2 * mpq m p) * γ))..(√(2 * mpq m p) * γ), exp (-(z ^ 2) / (2 * mpq m p))
      = Θ γ := by
  rw [th_29_024 m p _ hv, th_29_025 m p _ γ hv rfl]

/-- 積分形の de Moivre–Laplace 定理 (外部公理): p ∈ (0, 1)、γ > 0 なら
|n − mp| < √(2mpq) γ の確率は m → ∞ で Θ(γ) に近づく。 -/
axiom ax_normal_approx (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) (hγ : 0 < γ) :
  Tendsto (fun m : ℕ => probWithin m p (√(2 * mpq m p) * γ)) atTop (𝓝 (Θ γ))

theorem mpq_pos (m : ℕ) (hm : 1 ≤ m) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < mpq m p := by
  unfold mpq q
  have : (0 : ℝ) < m := by exact_mod_cast hm
  have : 0 < 1 - p := by linarith
  positivity

/-- ch29-027 (外部公理依存): 「is measured by 2/√π ∫_0^γ e^{−t²} dt」。 -/
theorem th_29_027 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun m : ℕ => probWithin m p (√(2 * mpq m p) * γ)) atTop
      (𝓝 (2 / √π * ∫ t in (0 : ℝ)..γ, exp (-(t ^ 2)))) :=
  ax_normal_approx p hp0 hp1 γ hγ

/-- ch29-022 (外部公理依存): 確率と 022 の積分 (a = √(2mpq)γ) の差は m → ∞ で 0。 -/
theorem th_29_022 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun m : ℕ => probWithin m p (√(2 * mpq m p) * γ) -
      1 / √(2 * π * mpq m p) *
        ∫ z in (-(√(2 * mpq m p) * γ))..(√(2 * mpq m p) * γ), exp (-(z ^ 2) / (2 * mpq m p)))
      atTop (𝓝 0) := by
  have h := (ax_normal_approx p hp0 hp1 γ hγ).sub_const (Θ γ)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [th_29_027_eq m p γ (mpq_pos m hm hp0 hp1)]

/-! ## 028・029: 脚注 -/

/-- ch29-028: 整数の誤差は h と h + 1 の間にない。 -/
theorem th_29_028 (h n : ℤ) : ¬ (h < n ∧ n < h + 1) := by omega

/-- ch29-028: 連続変数への置き換えは (h, h + 1) に正の確率を与える。 -/
theorem th_29_028_pos (m : ℕ) (p : ℝ) (hv : 0 < mpq m p) (h : ℝ) :
    0 < ∫ z in h..(h + 1), gauss m p z := by
  have hc : Continuous (fun z => gauss m p z) := by unfold gauss; fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) _ (by linarith)
  intro z _
  unfold gauss
  have : 0 < √(2 * π * mpq m p) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- ch29-029: 補正項 e^{−γ²}/√(2πmpq) は限界 a = √(2mpq)γ での密度の値。 -/
theorem th_29_029 (m : ℕ) (p γ : ℝ) (hv : 0 < mpq m p) :
    exp (-(γ ^ 2)) / √(2 * π * mpq m p) = gauss m p (√(2 * mpq m p) * γ) := by
  unfold gauss
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  have : -(2 * mpq m p * γ ^ 2) / (2 * mpq m p) = -(γ ^ 2) := by field_simp
  rw [this]; ring

/-- ch29-029: 補正項は m → ∞ で 0。 -/
theorem th_29_029_vanish (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) :
    Tendsto (fun m : ℕ => exp (-(γ ^ 2)) / √(2 * π * mpq m p)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  apply tendsto_sqrt_atTop.comp
  have hq0 : 0 < q p := by unfold q; linarith
  have hk : 0 < 2 * π * (p * q p) := by positivity
  have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hk
  refine this.congr (fun m => ?_)
  unfold mpq; ring

/-- ch29-029 (外部公理依存): 「more precision」の形も同じ極限 Θ(γ) を持つ。 -/
theorem th_29_029_lim (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun m : ℕ => probWithin m p (√(2 * mpq m p) * γ) -
      (Θ γ + exp (-(γ ^ 2)) / √(2 * π * mpq m p))) atTop (𝓝 0) := by
  have h := ((ax_normal_approx p hp0 hp1 γ hγ).sub_const (Θ γ)).sub (th_29_029_vanish p hp0 hp1 γ)
  rw [sub_self, sub_zero] at h
  refine h.congr (fun m => ?_)
  ring

/-! ## 030・032: 比率の形 -/

theorem sqrt_div_m (m : ℕ) (hm : 0 < m) (p : ℝ) :
    √(2 * mpq m p) / m = √(2 * p * q p / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : 2 * p * q p / m = 2 * mpq m p / (m : ℝ) ^ 2 := by unfold mpq; field_simp
  rw [this, sqrt_div' _ (by positivity), Real.sqrt_sq hm'.le]

/-- ch29-030: (mp ± √(2mpq)γ)/m = p ± √(2pq/m)γ。 -/
theorem th_29_030 (m : ℕ) (hm : 0 < m) (p γ : ℝ) :
    (m * p + √(2 * mpq m p) * γ) / m = p + √(2 * p * q p / m) * γ ∧
    (m * p - √(2 * mpq m p) * γ) / m = p - √(2 * p * q p / m) * γ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← sqrt_div_m m hm p]
  constructor <;> field_simp

/-- Θ は狭義増加。 -/
theorem Θ_strictMono : StrictMono Θ := by
  intro s t hst
  unfold Θ
  have hi := fun x y => cont_exp_neg_sq.intervalIntegrable (μ := MeasureTheory.volume) x y
  have hpos : 0 < ∫ u in s..t, exp (-(u ^ 2)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hi s t) (fun x _ => exp_pos _) hst
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s t)]
  have : 0 < 2 / √π := by have := Real.sqrt_pos.mpr pi_pos; positivity
  nlinarith

/-- ch29-032: √(2pq/m) = √(2pq)/√m (精度は事例の数の平方根に反比例)。比率の偏差 b を固定すると
Θ(b/√(2pq/m)) は m について増加、絶対偏差 a を固定すると Θ(a/√(2mpq)) は減少。 -/
theorem th_29_032 (p : ℝ) (hpq : 0 < p * q p) (b a : ℝ) (hb : 0 < b) (ha : 0 < a)
    (m₁ m₂ : ℕ) (h1 : 1 ≤ m₁) (h12 : m₁ ≤ m₂) :
    √(2 * p * q p / m₁) = √(2 * p * q p) / √m₁ ∧
    Θ (b / √(2 * p * q p / m₁)) ≤ Θ (b / √(2 * p * q p / m₂)) ∧
    Θ (a / √(2 * mpq m₂ p)) ≤ Θ (a / √(2 * mpq m₁ p)) := by
  have hm1 : (1 : ℝ) ≤ m₁ := by exact_mod_cast h1
  have hm12 : (m₁ : ℝ) ≤ m₂ := by exact_mod_cast h12
  have hk : 0 < 2 * p * q p := by linarith
  refine ⟨sqrt_div (by linarith) _, ?_, ?_⟩
  · apply Θ_strictMono.monotone
    apply div_le_div_of_nonneg_left hb.le
    · apply Real.sqrt_pos.mpr; apply div_pos hk; linarith
    · apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left hk.le (by linarith) hm12
  · apply Θ_strictMono.monotone
    apply div_le_div_of_nonneg_left ha.le
    · apply Real.sqrt_pos.mpr; unfold mpq; nlinarith
    · apply Real.sqrt_le_sqrt; unfold mpq; nlinarith

/-! ## 034・035: Bernoulli の言明 (§3) -/

/-- 二項分布の分散 Σ T(n)(n − mp)² = mpq (Mathlib bernsteinPolynomial.variance を p で評価)。 -/
theorem variance_bterm (m : ℕ) (p : ℝ) :
    ∑ n ∈ range (m + 1), bterm m p n * ((n : ℝ) - m * p) ^ 2 = mpq m p := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.variance ℝ m)
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, nsmul_eq_mul, bernsteinPolynomial] at h
  unfold mpq q
  rw [← h]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold bterm q
  ring

/-- ch29-034・035: Bernoulli の言明。p = r/t、c < 1 なら、十分多くの試行で
比率 n/m が (r − 1)/t と (r + 1)/t の間にある確率は c より大きい。 -/
theorem th_29_034 (r t : ℕ) (ht : 0 < t) (hrt : r ≤ t) (c : ℝ) (hc : c < 1) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      c < ∑ n ∈ (range (m + 1)).filter
        (fun n : ℕ => ((r : ℝ) - 1) / t < (n : ℝ) / m ∧ (n : ℝ) / m < ((r : ℝ) + 1) / t),
          bterm m ((r : ℝ) / t) n := by
  set p : ℝ := (r : ℝ) / t with hpdef
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [div_le_one ht']; exact_mod_cast hrt
  refine ⟨⌈(t : ℝ) ^ 2 / (1 - c)⌉₊ + 1, fun m hm => ?_⟩
  have hceil := Nat.le_ceil ((t : ℝ) ^ 2 / (1 - c))
  have hmR : (⌈(t : ℝ) ^ 2 / (1 - c)⌉₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm
  have hc1 : 0 < 1 - c := by linarith
  have hm0 : (0 : ℝ) < m := by
    have : (0 : ℝ) ≤ (t : ℝ) ^ 2 / (1 - c) := by positivity
    linarith
  have hmt : (t : ℝ) ^ 2 / m < 1 - c := by
    rw [div_lt_iff₀ hm0]
    have := (div_lt_iff₀ hc1).mp (by linarith : (t : ℝ) ^ 2 / (1 - c) < m)
    linarith
  set P : ℕ → Prop := fun n => ((r : ℝ) - 1) / t < (n : ℝ) / m ∧ (n : ℝ) / m < ((r : ℝ) + 1) / t
  have hsplit := Finset.sum_filter_add_sum_filter_not (range (m + 1)) P (bterm m p)
  rw [th_29_005_one] at hsplit
  -- 外側の各項: (m/t)² ≤ (n − mp)²
  have hout : ∀ n ∈ (range (m + 1)).filter (fun n => ¬ P n),
      bterm m p n * ((m : ℝ) / t) ^ 2 ≤ bterm m p n * ((n : ℝ) - m * p) ^ 2 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    apply mul_le_mul_of_nonneg_left _ (bterm_nonneg m hp0 hp1 n)
    have hnP := hn.2
    simp only [P, not_and_or, not_lt] at hnP
    have hmt' : (0 : ℝ) ≤ m / t := by positivity
    rcases hnP with h | h
    · rw [div_le_div_iff₀ hm0 ht'] at h
      have : (m : ℝ) / t ≤ m * p - n := by
        rw [hpdef, div_le_iff₀ ht']; field_simp; nlinarith
      nlinarith
    · rw [div_le_div_iff₀ ht' hm0] at h
      have : (m : ℝ) / t ≤ n - m * p := by
        rw [hpdef, div_le_iff₀ ht']; field_simp; nlinarith
      nlinarith
  have hsum_out : (∑ n ∈ (range (m + 1)).filter (fun n => ¬ P n), bterm m p n) * ((m : ℝ) / t) ^ 2
      ≤ mpq m p := by
    rw [Finset.sum_mul, ← variance_bterm m p]
    calc _ ≤ ∑ n ∈ (range (m + 1)).filter (fun n => ¬ P n), bterm m p n * ((n : ℝ) - m * p) ^ 2 :=
          Finset.sum_le_sum hout
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => mul_nonneg (bterm_nonneg m hp0 hp1 n) (sq_nonneg _))
  have hpq : p * q p ≤ 1 := by unfold q; nlinarith
  have hbound : (∑ n ∈ (range (m + 1)).filter (fun n => ¬ P n), bterm m p n) ≤ (t : ℝ) ^ 2 / m := by
    have hmt2 : 0 < ((m : ℝ) / t) ^ 2 := by positivity
    rw [← mul_le_mul_iff_of_pos_right hmt2]
    calc _ ≤ mpq m p := hsum_out
      _ ≤ (m : ℝ) := by unfold mpq; nlinarith
      _ = (t : ℝ) ^ 2 / m * ((m : ℝ) / t) ^ 2 := by field_simp
  linarith

/-! ## 036〜039: §5 の硬貨 (二面とも表か二面とも裏) -/

/-- 二つの世界 (true: 二面とも表、false: 二面とも裏)、重み ½ ずつ。 -/
noncomputable def Pc (E : Bool → Prop) [DecidablePred E] : ℝ :=
  (if E true then 1 / 2 else 0) + (if E false then 1 / 2 else 0)

/-- i 回目に表が出るか (どの回も同じ面)。 -/
def heads (w : Bool) (_i : ℕ) : Bool := w

/-- k 回のうちの表の回数。 -/
def nHeads (w : Bool) (k : ℕ) : ℕ := if w then k else 0

/-- ch29-036: どの回も表の確率は ½。 -/
theorem th_29_036_half (i : ℕ) : Pc (fun w => heads w i = true) = 1 / 2 := by
  simp [Pc, heads]

/-- ch29-036: 2m 回で m 回表の確率は 0。二項の項 C(2m, m)(½)^{2m} は正。 -/
theorem th_29_036 (m : ℕ) (hm : 1 ≤ m) :
    Pc (fun w => nHeads w (2 * m) = m) = 0 ∧ 0 < bterm (2 * m) (1 / 2) m := by
  constructor
  · have h1 : ¬ (2 * m = m) := by omega
    have h2 : ¬ (0 = m) := by omega
    simp [Pc, nHeads, h1, h2]
  · unfold bterm q
    have : 0 < (2 * m).choose m := Nat.choose_pos (by omega)
    have : (0 : ℝ) < ((2 * m).choose m : ℝ) := by exact_mod_cast this
    positivity

/-- ch29-037: 2m 回表か 0 回かは確実。 -/
theorem th_29_037 (m : ℕ) : Pc (fun w => nHeads w (2 * m) = 2 * m ∨ nHeads w (2 * m) = 0) = 1 := by
  simp [Pc, nHeads]; norm_num

/-- ch29-038: r 回続けて表の確率は ½ で、p^r = (½)^r ではない (r ≥ 2)。 -/
theorem th_29_038 (r : ℕ) (hr : 2 ≤ r) :
    Pc (fun w => ∀ i < r, heads w i = true) = 1 / 2 ∧ (1 / 2 : ℝ) ≠ (1 / 2) ^ r := by
  constructor
  · have hf : ¬ (∀ i < r, heads false i = true) := fun h => by simpa [heads] using h 0 (by omega)
    have ht : ∀ i < r, heads true i = true := fun i _ => rfl
    simp only [Pc, if_pos ht, if_neg hf]; norm_num
  · intro h
    have : (1 / 2 : ℝ) ^ r ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
    rw [← h] at this; norm_num at this

/-- ch29-039: 最初の r − 1 回が表だと知れば r 回目の表の確率は 1 (単独では ½)。 -/
theorem th_29_039 (r : ℕ) (hr : 2 ≤ r) :
    Pc (fun w => heads w (r - 1) = true ∧ ∀ i < r - 1, heads w i = true) /
      Pc (fun w => ∀ i < r - 1, heads w i = true) = 1 ∧
    Pc (fun w => heads w (r - 1) = true) = 1 / 2 := by
  have hf : ¬ (∀ i < r - 1, heads false i = true) := fun h => by simpa [heads] using h 0 (by omega)
  have ht : ∀ i < r - 1, heads true i = true := fun i _ => rfl
  have hf2 : ¬ (heads false (r - 1) = true ∧ ∀ i < r - 1, heads false i = true) := fun h => hf h.2
  have ht2 : heads true (r - 1) = true ∧ ∀ i < r - 1, heads true i = true := ⟨rfl, ht⟩
  refine ⟨?_, th_29_036_half _⟩
  simp only [Pc, if_pos ht, if_neg hf, if_pos ht2, if_neg hf2]; norm_num

/-! ## 040: Θ の限界と短い系列 -/

theorem integrable_exp_neg_sq : MeasureTheory.Integrable (fun u : ℝ => exp (-(u ^ 2))) := by
  have := integrable_exp_neg_mul_sq (b := 1) one_pos
  simpa using this

/-- ch29-040: Θ(γ) → 1 (γ → ∞)。Mathlib の Gauss 積分から。 -/
theorem th_29_040_lim : Tendsto Θ atTop (𝓝 1) := by
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := MeasureTheory.volume) 0
    integrable_exp_neg_sq.integrableOn tendsto_id
  have hI : ∫ u in Set.Ioi (0 : ℝ), exp (-(u ^ 2)) = √π / 2 := by
    have := integral_gaussian_Ioi 1
    simp only [neg_mul, one_mul, div_one] at this
    exact this
  rw [hI] at h
  have h2 := h.const_mul (2 / √π)
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  rw [show 2 / √π * (√π / 2) = 1 by field_simp] at h2
  exact h2

/-- ch29-040: 0 < Θ(γ) < 1 (γ > 0)。Θ は確実性に達しない。 -/
theorem th_29_040 (γ : ℝ) (hγ : 0 < γ) : 0 < Θ γ ∧ Θ γ < 1 := by
  have h0 : Θ 0 = 0 := by simp [Θ]
  have hle : ∀ x, Θ x ≤ 1 := fun x =>
    ge_of_tendsto th_29_040_lim (eventually_ge_atTop x |>.mono fun y hy => Θ_strictMono.monotone hy)
  refine ⟨h0 ▸ Θ_strictMono hγ, lt_of_lt_of_le (Θ_strictMono (lt_add_one γ)) (hle _)⟩

/-- ch29-040 (数値評価): 短い系列 (m = 1、p = ½) では確率は 0 か 1 で、どの γ > 0 でも Θ(γ) と違う。 -/
theorem th_29_040_short (γ : ℝ) (hγ : 0 < γ) :
    probWithin 1 (1 / 2) (√(2 * mpq 1 (1 / 2)) * γ) ≠ Θ γ := by
  have hΘ := th_29_040 γ hγ
  have h01 : probWithin 1 (1 / 2) (√(2 * mpq 1 (1 / 2)) * γ) = 0 ∨
      probWithin 1 (1 / 2) (√(2 * mpq 1 (1 / 2)) * γ) = 1 := by
    unfold probWithin
    generalize √(2 * mpq 1 (1 / 2)) * γ = A
    by_cases ha : (1 / 2 : ℝ) < A
    · right
      rw [Finset.filter_true_of_mem]
      · exact th_29_005_one 1 (1 / 2)
      · intro n hn
        rw [Finset.mem_range] at hn
        interval_cases n <;> norm_num <;> linarith
    · left
      rw [Finset.filter_false_of_mem]
      · simp
      · intro n hn
        rw [Finset.mem_range] at hn
        interval_cases n <;> norm_num <;> linarith
  rcases h01 with h | h <;> rw [h] <;> intro h' <;> linarith [hΘ.1, hΘ.2]

/-! ## 外部公理の前提 p < 1 の必要性 -/

/-- ax_normal_approx の前提 p < 1 は外せない: p = 1 なら mpq = 0 で、|n − m| < 0 となる n は無いので
左辺はどの m でも 0、一方 Θ(γ) > 0 (γ > 0) だから Θ(γ) には近づかない。 -/
theorem nec_ax_normal_approx_p1 (γ : ℝ) (hγ : 0 < γ) :
    (∀ m : ℕ, probWithin m 1 (√(2 * mpq m 1) * γ) = 0) ∧
    ¬ Tendsto (fun m : ℕ => probWithin m 1 (√(2 * mpq m 1) * γ)) atTop (𝓝 (Θ γ)) := by
  have h0 : ∀ m : ℕ, probWithin m 1 (√(2 * mpq m 1) * γ) = 0 := by
    intro m
    have hv : mpq m 1 = 0 := by unfold mpq q; ring
    unfold probWithin
    rw [hv, mul_zero, Real.sqrt_zero, zero_mul, Finset.filter_false_of_mem]
    · simp
    · intro n _; exact not_lt.mpr (abs_nonneg _)
  refine ⟨h0, fun h => ?_⟩
  simp only [h0] at h
  have := tendsto_nhds_unique tendsto_const_nhds h
  linarith [(th_29_040 γ hγ).1]

end KeynesXXIXb

/-! ## #print axioms -/
-- 記法 (定義のみ)
#print axioms KeynesXXIXb.q
#print axioms KeynesXXIXb.bterm
#print axioms KeynesXXIXb.hdev
#print axioms KeynesXXIXb.nearest
#print axioms KeynesXXIXb.mpq
#print axioms KeynesXXIXb.gauss
#print axioms KeynesXXIXb.Θ
#print axioms KeynesXXIXb.probWithin
-- 002・005・007
#print axioms KeynesXXIXb.th_29_002
#print axioms KeynesXXIXb.bterm_nonneg
#print axioms KeynesXXIXb.th_29_005
#print axioms KeynesXXIXb.th_29_005_one
#print axioms KeynesXXIXb.th_29_005_pmf
#print axioms KeynesXXIXb.th_29_007
-- 008・009・010
#print axioms KeynesXXIXb.bterm_ratio
#print axioms KeynesXXIXb.step_up
#print axioms KeynesXXIXb.step_down
#print axioms KeynesXXIXb.th_29_mode
#print axioms KeynesXXIXb.th_29_009
#print axioms KeynesXXIXb.th_29_008
#print axioms KeynesXXIXb.nec_29_010
#print axioms KeynesXXIXb.nec_29_010_small
#print axioms KeynesXXIXb.th_29_010_fix
-- 011・012
#print axioms KeynesXXIXb.th_29_011
#print axioms KeynesXXIXb.tendsto_mul_left_nat
#print axioms KeynesXXIXb.th_29_012_h0
#print axioms KeynesXXIXb.th_29_012
-- 013・014・015
#print axioms KeynesXXIXb.th_29_013
#print axioms KeynesXXIXb.th_29_013_strict
#print axioms KeynesXXIXb.th_29_014
#print axioms KeynesXXIXb.th_29_015
#print axioms KeynesXXIXb.th_29_015_asym
-- 016・017
#print axioms KeynesXXIXb.th_29_016
#print axioms KeynesXXIXb.th_29_016_lim
-- 020
#print axioms KeynesXXIXb.th_29_020
#print axioms KeynesXXIXb.th_29_020_one
-- 022〜027
#print axioms KeynesXXIXb.cont_gaussexp
#print axioms KeynesXXIXb.cont_exp_neg_sq
#print axioms KeynesXXIXb.th_29_023
#print axioms KeynesXXIXb.integral_even
#print axioms KeynesXXIXb.th_29_024_v
#print axioms KeynesXXIXb.th_29_024
#print axioms KeynesXXIXb.th_29_025
#print axioms KeynesXXIXb.th_29_026
#print axioms KeynesXXIXb.th_29_027_eq
#print axioms KeynesXXIXb.mpq_pos
#print axioms KeynesXXIXb.th_29_027
#print axioms KeynesXXIXb.th_29_022
-- 028・029
#print axioms KeynesXXIXb.th_29_028
#print axioms KeynesXXIXb.th_29_028_pos
#print axioms KeynesXXIXb.th_29_029
#print axioms KeynesXXIXb.th_29_029_vanish
#print axioms KeynesXXIXb.th_29_029_lim
-- 030・032
#print axioms KeynesXXIXb.sqrt_div_m
#print axioms KeynesXXIXb.th_29_030
#print axioms KeynesXXIXb.Θ_strictMono
#print axioms KeynesXXIXb.th_29_032
-- 034・035
#print axioms KeynesXXIXb.variance_bterm
#print axioms KeynesXXIXb.th_29_034
-- 036〜039
#print axioms KeynesXXIXb.Pc
#print axioms KeynesXXIXb.th_29_036_half
#print axioms KeynesXXIXb.th_29_036
#print axioms KeynesXXIXb.th_29_037
#print axioms KeynesXXIXb.th_29_038
#print axioms KeynesXXIXb.th_29_039
-- 040
#print axioms KeynesXXIXb.integrable_exp_neg_sq
#print axioms KeynesXXIXb.th_29_040_lim
#print axioms KeynesXXIXb.th_29_040
#print axioms KeynesXXIXb.th_29_040_short
-- 外部公理の前提 p < 1 の必要性
#print axioms KeynesXXIXb.nec_ax_normal_approx_p1
