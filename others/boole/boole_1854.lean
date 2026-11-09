/-
# others/boole/boole_1854.lean — Boole の挑戦問題 (1851) と Boole の解 (1854)

**比較用。docs/全数台帳 に対応する行は無く、判定数 (check_all の [3]) にも数えない。**
『確率論』の印刷行 (ch17-002 Boole の方程式、ch17-003 その限界、ch17-005 Wilbraham) は
従来どおり台帳側 (phase10d th_17_56_l002・l005) で扱う。本ファイルは Boole 自身の解を
Keynes の記号 (c₁, c₂, p₁, p₂, u) で置き、その性質を算術として証明するだけで、Keynes の
公理 (KeynesI) を一切使わない (import Mathlib のみ)。Keynes との比較は
compare_keynes_56.lean で行う。

## 典拠 (未照合)
  Boole の原著 (1851 Camb. & Dublin Math. J. 6; 1853/1854 Phil. Mag. 4th ser. 7, 8;
  *Laws of Thought* (1854) pp. 321–326) は materials/原著/ に未入手。方程式と限界は
  Keynes の転記 (folio 187、1921 年版の頁画像) から取った。原著との照合は未了 (未照合)。
  Boole の一般法を「data の事象を独立な単純事象とみなし、論理条件 V の下に条件付ける」と
  読む部分 (§ 3 の積の形) は二次文献の読み (Hailperin) によるもので、これも未照合。

## 記号 (folio 186–187 の問題の言明)
  c_r = 原因 A_r の à priori probability、p_r = A_r があるとき E が伴う確率、
  u = E の確率 (求めるもの)。E は A₁, A₂ のどちらも無ければ起こらない。

## 内容
  § 1 方程式 (folio 187 の印刷形) と分母を払った形 F、Boole の限界、Boole の解。
  § 2 解の存在 (中間値の定理) と一意性 (u < 1 の範囲)。
  § 3 構成要素 (constituents) の 7 つの確率 k₁…k₇ と Boole の「理想的」条件
      (k₄k₇ = k₅k₆, k₁k₇ = k₂k₃)。この 2 条件から方程式が出る (root_of_ideal)。
      2 条件は積の形 (data の 4 事象に独立な重みを置き V で正規化) と同値 (正の重みのとき)。
  § 4 Keynes の批判「Boole's equations do not reduce to this simplified form」(folio 187)
      の算術形: u = c₁p₁ + c₂p₂ が根なら c₁p₁ = 0 か c₂p₂ = 0 (u ≠ 1)。
  § 5 数値の場合: c₁ = c₂ = p₁ = p₂ = 1/2 で F(1/4) = 1/16, F(1/2) = −1/32;
      c₁ = c₂ = 1/3, p₁ = p₂ = 1 で u = 5/9 が解。

## 実行方法
  lake env lean others/boole/boole_1854.lean
  (check_all は -R . -o で一時ディレクトリに olean を作り、compare_keynes_56.lean から
  import する。)
-/

import Mathlib

namespace Boole

/-! ## § 1 方程式・限界・解 (folio 187) -/

/-- Boole の方程式の左辺 [1 − c₁(1 − p₁) − u][1 − c₂(1 − p₂) − u] / (1 − u)
(folio 187 の Keynes の転記どおり)。 -/
noncomputable def lhs (c₁ c₂ p₁ p₂ u : ℝ) : ℝ :=
  (1 - c₁ * (1 - p₁) - u) * (1 - c₂ * (1 - p₂) - u) / (1 - u)

/-- Boole の方程式の右辺 (u − c₁p₁)(u − c₂p₂) / (c₁p₁ + c₂p₂ − u) (folio 187)。 -/
noncomputable def rhs (c₁ c₂ p₁ p₂ u : ℝ) : ℝ :=
  (u - c₁ * p₁) * (u - c₂ * p₂) / (c₁ * p₁ + c₂ * p₂ - u)

/-- Boole の方程式 (印刷形; 台帳 ch17-002 と同じ式)。 -/
def Equation (c₁ c₂ p₁ p₂ u : ℝ) : Prop := lhs c₁ c₂ p₁ p₂ u = rhs c₁ c₂ p₁ p₂ u

/-- 分母を払った形 F(u) = A·B·k₁ − (1 − u)·k₃·k₂
(A = 1 − c₁(1 − p₁) − u, B = 1 − c₂(1 − p₂) − u, k₁ = c₁p₁ + c₂p₂ − u,
k₃ = u − c₁p₁, k₂ = u − c₂p₂)。 -/
def F (c₁ c₂ p₁ p₂ u : ℝ) : ℝ :=
  (1 - c₁ * (1 - p₁) - u) * (1 - c₂ * (1 - p₂) - u) * (c₁ * p₁ + c₂ * p₂ - u)
    - (1 - u) * (u - c₁ * p₁) * (u - c₂ * p₂)

/-- 分母を払った方程式の根。 -/
def Root (c₁ c₂ p₁ p₂ u : ℝ) : Prop := F c₁ c₂ p₁ p₂ u = 0

/-- Boole の限界 (folio 187「not less than c₁p₁ and c₂p₂ and not greater than
1 − c₁(1 − p₁), 1 − c₂(1 − p₂), or c₁p₁ + c₂p₂」; 台帳 ch17-003)。 -/
def Limits (c₁ c₂ p₁ p₂ u : ℝ) : Prop :=
  c₁ * p₁ ≤ u ∧ c₂ * p₂ ≤ u ∧ u ≤ 1 - c₁ * (1 - p₁) ∧ u ≤ 1 - c₂ * (1 - p₂)
    ∧ u ≤ c₁ * p₁ + c₂ * p₂

/-- **Boole の解** (folio 187「u is that root of the equation which is not less than …」):
u は方程式 (分母を払った形) の根で、Boole の限界の中にある。 -/
def solution (c₁ c₂ p₁ p₂ u : ℝ) : Prop := Root c₁ c₂ p₁ p₂ u ∧ Limits c₁ c₂ p₁ p₂ u

/-- data の範囲: c_r, p_r ∈ [0, 1]。 -/
def Data (c₁ c₂ p₁ p₂ : ℝ) : Prop :=
  0 ≤ c₁ ∧ c₁ ≤ 1 ∧ 0 ≤ c₂ ∧ c₂ ≤ 1 ∧ 0 ≤ p₁ ∧ p₁ ≤ 1 ∧ 0 ≤ p₂ ∧ p₂ ≤ 1

/-- 限界の区間が空でないこと: 下限 max{c₁p₁, c₂p₂} ⩽ 上限 min{…}。 -/
def Possible (c₁ c₂ p₁ p₂ : ℝ) : Prop :=
  max (c₁ * p₁) (c₂ * p₂)
    ≤ min (c₁ * p₁ + c₂ * p₂) (min (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂)))

/-- 分母が 0 でなければ、印刷形の方程式と分母を払った形は同値。 -/
theorem equation_iff_root (c₁ c₂ p₁ p₂ u : ℝ) (h1 : 1 - u ≠ 0)
    (h2 : c₁ * p₁ + c₂ * p₂ - u ≠ 0) :
    Equation c₁ c₂ p₁ p₂ u ↔ Root c₁ c₂ p₁ p₂ u := by
  unfold Equation lhs rhs Root F
  rw [div_eq_div_iff h1 h2]
  constructor <;> intro H <;> linear_combination H

/-- 限界の言い直し: Limits ↔ 下限 ⩽ u ⩽ 上限。 -/
theorem limits_iff (c₁ c₂ p₁ p₂ u : ℝ) :
    Limits c₁ c₂ p₁ p₂ u ↔
      (max (c₁ * p₁) (c₂ * p₂) ≤ u
        ∧ u ≤ min (c₁ * p₁ + c₂ * p₂) (min (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂)))) := by
  unfold Limits
  simp only [max_le_iff, le_min_iff]
  tauto

/-! ## § 2 解の存在と一意性 -/

/-- **解の存在**: data が範囲内で限界の区間が空でなければ、Boole の解がある
(F は下限で ⩾ 0、上限で ⩽ 0; 中間値の定理)。 -/
theorem exists_solution (c₁ c₂ p₁ p₂ : ℝ) (hd : Data c₁ c₂ p₁ p₂)
    (hp : Possible c₁ c₂ p₁ p₂) : ∃ u, solution c₁ c₂ p₁ p₂ u := by
  obtain ⟨hc1, hc1', hc2, hc2', hp1, hp1', hp2, hp2'⟩ := hd
  set lo := max (c₁ * p₁) (c₂ * p₂) with hlo
  set hi := min (c₁ * p₁ + c₂ * p₂) (min (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂))) with hhi
  have hm1 : 0 ≤ c₁ * (1 - p₁) := mul_nonneg hc1 (by linarith)
  have hm2 : 0 ≤ c₂ * (1 - p₂) := mul_nonneg hc2 (by linarith)
  have hcp1 : 0 ≤ c₁ * p₁ := mul_nonneg hc1 hp1
  have hcp2 : 0 ≤ c₂ * p₂ := mul_nonneg hc2 hp2
  have hhi1 : hi ≤ c₁ * p₁ + c₂ * p₂ := min_le_left _ _
  have hhi2 : hi ≤ 1 - c₁ * (1 - p₁) := (min_le_right _ _).trans (min_le_left _ _)
  have hhi3 : hi ≤ 1 - c₂ * (1 - p₂) := (min_le_right _ _).trans (min_le_right _ _)
  have hlo1 : c₁ * p₁ ≤ lo := le_max_left _ _
  have hlo2 : c₂ * p₂ ≤ lo := le_max_right _ _
  have hle : lo ≤ hi := hp
  -- F(lo) ⩾ 0
  have Flo : 0 ≤ F c₁ c₂ p₁ p₂ lo := by
    have hz : (lo - c₁ * p₁) * (lo - c₂ * p₂) = 0 := by
      rcases max_choice (c₁ * p₁) (c₂ * p₂) with h | h
      · rw [← hlo] at h; rw [h]; ring
      · rw [← hlo] at h; rw [h]; ring
    have hA : 0 ≤ 1 - c₁ * (1 - p₁) - lo := by linarith
    have hB : 0 ≤ 1 - c₂ * (1 - p₂) - lo := by linarith
    have hk : 0 ≤ c₁ * p₁ + c₂ * p₂ - lo := by linarith
    have h3 : (1 - lo) * (lo - c₁ * p₁) * (lo - c₂ * p₂) = 0 := by
      rw [mul_assoc, hz, mul_zero]
    unfold F
    rw [h3, sub_zero]
    exact mul_nonneg (mul_nonneg hA hB) hk
  -- F(hi) ⩽ 0
  have Fhi : F c₁ c₂ p₁ p₂ hi ≤ 0 := by
    have hz : (1 - c₁ * (1 - p₁) - hi) * (1 - c₂ * (1 - p₂) - hi)
        * (c₁ * p₁ + c₂ * p₂ - hi) = 0 := by
      rcases min_choice (c₁ * p₁ + c₂ * p₂) (min (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂)))
        with h | h
      · rw [← hhi] at h; rw [h]; ring
      · rw [← hhi] at h
        rcases min_choice (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂)) with h' | h'
        · rw [h, h']; ring
        · rw [h, h']; ring
    have h1 : 0 ≤ 1 - hi := by linarith
    have h2 : 0 ≤ hi - c₁ * p₁ := by linarith
    have h3 : 0 ≤ hi - c₂ * p₂ := by linarith
    unfold F
    rw [hz, zero_sub, neg_nonpos]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hcont : ContinuousOn (F c₁ c₂ p₁ p₂) (Set.Icc lo hi) := by
    unfold F; fun_prop
  obtain ⟨u, ⟨hu1, hu2⟩, hFu⟩ :=
    intermediate_value_Icc' hle hcont (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨Fhi, Flo⟩)
  refine ⟨u, hFu, ?_⟩
  exact (limits_iff c₁ c₂ p₁ p₂ u).mpr ⟨hu1, hu2⟩

/-- 一意性の核 (原子 a = c₁p₁, b = c₂p₂, m = c₁(1 − p₁), n = c₂(1 − p₂) で書いた形):
限界の中にある二つの根 u < v (v < 1) は両立しない。 -/
theorem unique_core (a b m n u v : ℝ) (hm : 0 ≤ m)
    (Ru : (1 - m - u) * (1 - n - u) * (a + b - u) - (1 - u) * (u - a) * (u - b) = 0)
    (Rv : (1 - m - v) * (1 - n - v) * (a + b - v) - (1 - v) * (v - a) * (v - b) = 0)
    (u1 : a ≤ u) (u2 : b ≤ u)
    (v3 : v ≤ 1 - m) (v4 : v ≤ 1 - n) (v5 : v ≤ a + b)
    (hv1 : v < 1) (huv : u < v) : False := by
  have hsu : 0 < 1 - u := by linarith
  have hsv : 0 < 1 - v := by linarith
  have i1 : (1 - u) * (1 - m - v) ≤ (1 - v) * (1 - m - u) := by
    have e : (1 - v) * (1 - m - u) - (1 - u) * (1 - m - v) = m * (v - u) := by ring
    have := mul_nonneg hm (show 0 ≤ v - u by linarith)
    linarith
  have i2 : (1 - n - v) * (a + b - v) ≤ (1 - n - u) * (a + b - u) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have i3 : (1 - u) * (1 - m - v) * ((1 - n - v) * (a + b - v))
      ≤ (1 - v) * (1 - m - u) * ((1 - n - u) * (a + b - u)) :=
    mul_le_mul i1 i2 (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg hsv.le (by linarith))
  have e1 : (1 - u) * (1 - m - v) * ((1 - n - v) * (a + b - v))
      = (1 - u) * ((1 - v) * (v - a) * (v - b)) := by linear_combination (1 - u) * Rv
  have e2 : (1 - v) * (1 - m - u) * ((1 - n - u) * (a + b - u))
      = (1 - v) * ((1 - u) * (u - a) * (u - b)) := by linear_combination (1 - v) * Ru
  have hpos : 0 < (v - a) * (v - b) - (u - a) * (u - b) := by
    have e : (v - a) * (v - b) - (u - a) * (u - b) = (v - u) * ((u - a) + (u - b) + (v - u)) := by
      ring
    rw [e]
    exact mul_pos (by linarith) (by linarith)
  have h4 := mul_pos (mul_pos hsu hsv) hpos
  have e3 : (1 - u) * (1 - v) * ((v - a) * (v - b) - (u - a) * (u - b))
      = (1 - u) * ((1 - v) * (v - a) * (v - b)) - (1 - v) * ((1 - u) * (u - a) * (u - b)) := by
    ring
  linarith

/-- **解の一意性** (u < 1 の範囲): c₁(1 − p₁) ⩾ 0 のとき、Boole の限界の中で 1 未満の根は
高々一つ (Keynes の「that root」)。証明: (1 − m − u)/(1 − u)・(1 − n − u)・(c₁p₁ + c₂p₂ − u) は
u について非増加、(u − c₁p₁)(u − c₂p₂) は狭義増加 (unique_core)。 -/
theorem solution_unique (c₁ c₂ p₁ p₂ u v : ℝ) (hm1 : 0 ≤ c₁ * (1 - p₁))
    (hu : solution c₁ c₂ p₁ p₂ u) (hv : solution c₁ c₂ p₁ p₂ v)
    (hu1 : u < 1) (hv1 : v < 1) : u = v := by
  obtain ⟨Ru, ⟨u1, u2, u3, u4, u5⟩⟩ := hu
  obtain ⟨Rv, ⟨v1, v2, v3, v4, v5⟩⟩ := hv
  unfold Root F at Ru Rv
  rcases lt_trichotomy u v with h | h | h
  · exact (unique_core _ _ _ _ u v hm1 Ru Rv u1 u2 v3 v4 v5 hv1 h).elim
  · exact h
  · exact (unique_core _ _ _ _ v u hm1 Rv Ru v1 v2 u3 u4 u5 hu1 h).elim

/-! ## § 3 構成要素と Boole の「理想的」条件 (未照合の読み)

事象 A₁, A₂, E の構成要素 (constituents) のうち E·Ā₁·Ā₂ は data で不可能。残り 7 つの確率:
  k₁ = E A₁ A₂, k₂ = E A₁ Ā₂, k₃ = E Ā₁ A₂, k₄ = Ē A₁ A₂, k₅ = Ē A₁ Ā₂, k₆ = Ē Ā₁ A₂,
  k₇ = Ē Ā₁ Ā₂。
data は c₁ = k₁ + k₂ + k₄ + k₅, c₂ = k₁ + k₃ + k₄ + k₆, c₁p₁ = k₁ + k₂, c₂p₂ = k₁ + k₃,
u = k₁ + k₂ + k₃ (総和 1)。data の 5 つの値に対して 7 つの未知数が残る (Keynes の y, z)。 -/

/-- Boole の「理想的」条件 (この問題の場合): Ē の下で A₁ と A₂ は独立 (k₄k₇ = k₅k₆) かつ
交差比の条件 k₁k₇ = k₂k₃。 -/
def Ideal (k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℝ) : Prop := k₄ * k₇ = k₅ * k₆ ∧ k₁ * k₇ = k₂ * k₃

/-- 積の形: data の 4 事象 A₁, A₂, A₁E, A₂E に独立な重み (オッズ) α, β, γ, δ を置き、
論理条件 V が許す 7 つの構成要素に積を割り振って正規化したもの
(Boole の一般法の「単純事象を独立とみなし V に条件付ける」の読み; 未照合)。 -/
def ProductForm (k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℝ) : Prop :=
  ∃ α β γ δ t : ℝ, 0 < t ∧ k₁ = t * α * β * γ * δ ∧ k₂ = t * α * γ ∧ k₃ = t * β * δ
    ∧ k₄ = t * α * β ∧ k₅ = t * α ∧ k₆ = t * β ∧ k₇ = t

/-- 積の形ならば理想的条件。 -/
theorem ideal_of_product (k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℝ) (H : ProductForm k₁ k₂ k₃ k₄ k₅ k₆ k₇) :
    Ideal k₁ k₂ k₃ k₄ k₅ k₆ k₇ := by
  obtain ⟨α, β, γ, δ, t, -, h1, h2, h3, h4, h5, h6, h7⟩ := H
  subst h1 h2 h3 h4 h5 h6 h7
  constructor <;> ring

/-- 理想的条件 (k₅, k₆, k₇ > 0) ならば積の形 (α = k₅/k₇, β = k₆/k₇, γ = k₂/k₅, δ = k₃/k₆)。 -/
theorem product_of_ideal (k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℝ) (h5 : 0 < k₅) (h6 : 0 < k₆) (h7 : 0 < k₇)
    (H : Ideal k₁ k₂ k₃ k₄ k₅ k₆ k₇) : ProductForm k₁ k₂ k₃ k₄ k₅ k₆ k₇ := by
  obtain ⟨hY, hX⟩ := H
  refine ⟨k₅ / k₇, k₆ / k₇, k₂ / k₅, k₃ / k₆, k₇, h7, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · field_simp; linear_combination hX
  · field_simp
  · field_simp
  · field_simp; linear_combination hY
  · field_simp
  · field_simp

/-- **理想的条件から Boole の方程式** (純算術): 構成要素の確率が data を与え、総和が 1 で、
理想的条件を満たせば、u = k₁ + k₂ + k₃ は分母を払った方程式の根。 -/
theorem root_of_ideal (c₁ c₂ p₁ p₂ u k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℝ)
    (hc₁ : c₁ = k₁ + k₂ + k₄ + k₅) (hc₂ : c₂ = k₁ + k₃ + k₄ + k₆)
    (hcp₁ : c₁ * p₁ = k₁ + k₂) (hcp₂ : c₂ * p₂ = k₁ + k₃) (hu : u = k₁ + k₂ + k₃)
    (hsum : k₁ + k₂ + k₃ + k₄ + k₅ + k₆ + k₇ = 1)
    (H : Ideal k₁ k₂ k₃ k₄ k₅ k₆ k₇) : Root c₁ c₂ p₁ p₂ u := by
  obtain ⟨hY, hX⟩ := H
  have m₁ : c₁ * (1 - p₁) = k₄ + k₅ := by linear_combination hc₁ - hcp₁
  have m₂ : c₂ * (1 - p₂) = k₄ + k₆ := by linear_combination hc₂ - hcp₂
  have h7 : k₇ = 1 - (k₁ + k₂ + k₃ + k₄ + k₅ + k₆) := by linear_combination hsum
  unfold Root F
  rw [m₁, m₂, hcp₁, hcp₂, hu]
  subst h7
  linear_combination (1 - k₁ - k₂ - k₃) * hX - k₁ * hY

/-! ## § 4 Keynes の批判 (folio 187): 排反の場合の値 c₁p₁ + c₂p₂ に「reduce しない」 -/

/-- u = c₁p₁ + c₂p₂ が方程式 (分母を払った形) の根になるのは、u = 1 か c₁p₁ = 0 か
c₂p₂ = 0 のときに限る。 -/
theorem root_at_sum (c₁ c₂ p₁ p₂ : ℝ) (hR : Root c₁ c₂ p₁ p₂ (c₁ * p₁ + c₂ * p₂))
    (h1 : c₁ * p₁ + c₂ * p₂ ≠ 1) : c₁ * p₁ = 0 ∨ c₂ * p₂ = 0 := by
  unfold Root F at hR
  have e : (1 - (c₁ * p₁ + c₂ * p₂)) * (c₂ * p₂) * (c₁ * p₁) = 0 := by
    linear_combination -hR
  rcases mul_eq_zero.mp e with e' | e'
  · rcases mul_eq_zero.mp e' with e'' | e''
    · exact absurd (by linarith) h1
    · exact Or.inr e''
  · exact Or.inl e'

/-! ## § 5 数値の場合 -/

/-- c₁ = c₂ = p₁ = p₂ = 1/2 で F(1/4) = 1/16 (≠ 0)。 -/
theorem F_half_quarter : F (1/2) (1/2) (1/2) (1/2) (1/4) = 1/16 := by
  unfold F; norm_num

/-- c₁ = c₂ = p₁ = p₂ = 1/2 で F(1/2) = −1/32 (≠ 0)。 -/
theorem F_half_half : F (1/2) (1/2) (1/2) (1/2) (1/2) = -1/32 := by
  unfold F; norm_num

/-- c₁ = c₂ = p₁ = p₂ = 1/2 の Boole の解は 1/4 と 1/2 の間に一つあり、両端ではない。 -/
theorem half_solution :
    ∃ u, solution (1/2) (1/2) (1/2) (1/2) u ∧ 1/4 < u ∧ u < 1/2 := by
  have hd : Data (1/2) (1/2) (1/2) (1/2) := by unfold Data; norm_num
  have hp : Possible (1/2) (1/2) (1/2) (1/2) := by
    unfold Possible; norm_num
  obtain ⟨u, hu⟩ := exists_solution _ _ _ _ hd hp
  refine ⟨u, hu, ?_, ?_⟩
  · obtain ⟨hR, h1, -, -, -, -⟩ := hu
    rcases (show (1:ℝ)/2 * (1/2) ≤ u by linarith).lt_or_eq with h | h
    · norm_num at h; linarith
    · rw [← h] at hR; unfold Root at hR; norm_num [F] at hR
  · obtain ⟨hR, -, -, -, -, h5⟩ := hu
    rcases (show u ≤ (1:ℝ)/2 * (1/2) + 1/2 * (1/2) by linarith).lt_or_eq with h | h
    · norm_num at h; linarith
    · rw [h] at hR; unfold Root at hR; norm_num [F] at hR

/-- c₁ = c₂ = 1/3, p₁ = p₂ = 1 では u = 5/9 が Boole の解。 -/
theorem third_solution : solution (1/3) (1/3) 1 1 (5/9) := by
  refine ⟨?_, ?_⟩
  · unfold Root F; norm_num
  · unfold Limits; norm_num

end Boole

/-! # 監査クエリ (判定数には数えない) -/

#print axioms Boole.equation_iff_root
#print axioms Boole.limits_iff
#print axioms Boole.exists_solution
#print axioms Boole.solution_unique
#print axioms Boole.ideal_of_product
#print axioms Boole.product_of_ideal
#print axioms Boole.root_of_ideal
#print axioms Boole.root_at_sum
#print axioms Boole.F_half_quarter
#print axioms Boole.F_half_half
#print axioms Boole.half_solution
#print axioms Boole.third_solution
