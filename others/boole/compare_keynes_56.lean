/-
# others/boole/compare_keynes_56.lean — Boole の解と Keynes (56)–(56.5) の比較

**比較用。docs/全数台帳 に対応する行は無く、判定数 (check_all の [3]) にも数えない。**
phases/ と others/ を結ぶのは本ファイルだけ。phases/keynes_part_ii_phase16a_boole_challenge
(Keynes の (56)–(56.5) を KeynesI 担体で証明したもの) と others/boole/boole_1854 (Boole の
方程式と解の算術) を import し、両者を比べる。phases/ は others/ を import しない
(check_all の [1i] で検査)。

## 層の区別 (Boole あり/なしは区別できるか)
  (1) import の層: Keynes の定理 (th_17_56_*) は phases/ にあり、Boole の公理を置く本ファイルを
      見ない。依存は構造上ありえない。
  (2) #print axioms の層: Boole の前提は `Boole.ax_*` の名前付き公理として置く。
      § 7 の run_cmd が、(56.1)–(56.5) の #print axioms に `Boole.` で始まる名前が無いこと、
      solution_data には有ることを検査し、外れればコンパイルが落ちる。
  (3) 模型の層: Keynes の公理 13 本をすべて満たし、data の前提 (Cons h, e/ā₁ā₂h = 0) も
      満たすが、Boole の理想的条件が偽で Boole の方程式も偽になる模型 (§ 5 exclusive_model)。
      よって Boole の解には Keynes の公理に無い前提が要る。

## 担体 (外延と内包)
  Boole の確率は事象のブール代数 (外延)、Keynes の確率関係は命題の上 (内包, KeynesI)。
  命題を真偽で同一視する担体 (Prop → Prop → ℝ) では data c₁ = 1/2 すら置けない
  (§ 6 prop_carrier_no_half; phase7i_model ext_forced と同じ経路)。そこで本ファイルは
  Boole の担体を KeynesI に埋め込まず、事象代数 (4 世界の部分集合; phase16a NoX の Ops) の上に
  「Keynes の公理を満たす一つの模型」を置き、その上で Keynes の区間と Boole の解を評価する。
  Keynes が Boole の問題に答えるときも、e/h を事象の値として読む (外延性を捨てる) ことに当たる。

## 結果
  § 2 solution_of_ideal: KeynesI の公理 + data の前提 + Boole の理想的条件 (Ideal) から
      Boole の解 (方程式の根で限界の中)。限界は Keynes の (56.1) (th_17_56_1_i) から来る。
      solution_data: 名前付きの Boole.A₁ … Boole.H と公理 Boole.ax_* の上の同じ結論。
  § 3 比較定理 1 (区間に入る) solution_between: Boole の解は Keynes の (56.1) の区間
      (th_17_56_1_cited) に入り、(56.2) の上限 p₁ + p₂ 以下、(56.5) の下限
      c₁p₁ + c₂p₂ − c₁c₂ 以上。(56.5) の下限は、(56.5) の前提 (原因の独立 a₁/a₂h = a₁/h)
      無しに出る (bound_565_of_ideal_i)。
  § 4 Wilbraham の形 u = c₁p₁ + c₂p₂ − z (z ⩽ c₁p₁, c₂p₂; folio 187 脚注 3) は Keynes の
      体系の定理 (wilbraham_of_keynes_i) で、Boole の解も満たす (wilbraham_of_solution)。
      区別は z を data から定めるか否かにある。
  § 5 比較定理 2 (追加前提が要る) boole_needs_premiss: Keynes の公理 13 本を満たす模型で
      Boole の方程式が偽。同じ data (c₁ = c₂ = p₁ = p₂ = 1/2) で u = 1/2 の模型と u = 1/4 の
      模型があり (undetermined)、Boole の根は 1/4 と 1/2 の間の第三の値 (half_solution)。
      Boole の前提は Keynes の公理と両立する (boole_model: 理想的条件を満たし u = 5/9)。
      (56.5) の下限も Keynes の公理だけからは出ない (bound_565_needs_premiss)。

## 未照合・未達
  Boole・Cayley・Wilbraham の原著は未入手 (materials/原著/ に無い)。Boole の方程式と限界、
  Wilbraham の形は Keynes の転記 (folio 187 本文と脚注 3) による。Cayley の解は Keynes の
  本文・脚注に式が無く、原著も無いので置いていない (未達)。

## 実行方法
  check_all は phase16a と boole_1854 を -R . -o で一時ディレクトリに olean にし、
  LEAN_PATH に足してから lake env lean で本ファイルを検査する。
-/

import phases.keynes_part_ii_phase16a_boole_challenge
import others.boole.boole_1854

namespace Boole

open KeynesI

/-! ## § 1 構成要素の確率 (KeynesI 担体) と分解 -/

/-- k₁ = ea₁a₂/h (Keynes の y)。 -/
noncomputable def K₁ (a₁ a₂ e h : IProp) : ℝ := PrI (iand e (iand a₁ a₂)) h
/-- k₂ = ea₁ā₂/h。 -/
noncomputable def K₂ (a₁ a₂ e h : IProp) : ℝ := PrI (iand e (iand a₁ (inot a₂))) h
/-- k₃ = eā₁a₂/h。 -/
noncomputable def K₃ (a₁ a₂ e h : IProp) : ℝ := PrI (iand e (iand (inot a₁) a₂)) h
/-- k₄ = ēa₁a₂/h。 -/
noncomputable def K₄ (a₁ a₂ e h : IProp) : ℝ := PrI (iand (inot e) (iand a₁ a₂)) h
/-- k₅ = ēa₁ā₂/h。 -/
noncomputable def K₅ (a₁ a₂ e h : IProp) : ℝ := PrI (iand (inot e) (iand a₁ (inot a₂))) h
/-- k₆ = ēā₁a₂/h。 -/
noncomputable def K₆ (a₁ a₂ e h : IProp) : ℝ := PrI (iand (inot e) (iand (inot a₁) a₂)) h
/-- k₇ = ēā₁ā₂/h。 -/
noncomputable def K₇ (a₁ a₂ e h : IProp) : ℝ := PrI (iand (inot e) (iand (inot a₁) (inot a₂))) h
/-- k₈ = eā₁ā₂/h (data で 0)。 -/
noncomputable def K₈ (a₁ a₂ e h : IProp) : ℝ := PrI (iand e (iand (inot a₁) (inot a₂))) h

/-- Boole の理想的条件を KeynesI 担体の上で。 -/
def IdealI (a₁ a₂ e h : IProp) : Prop :=
  Ideal (K₁ a₁ a₂ e h) (K₂ a₁ a₂ e h) (K₃ a₁ a₂ e h) (K₄ a₁ a₂ e h) (K₅ a₁ a₂ e h)
    (K₆ a₁ a₂ e h) (K₇ a₁ a₂ e h)

/-- 連言の可換 (代入原理 subst_taut 経由)。 -/
theorem pr_comm (p q h : IProp) (hc : Cons h) : PrI (iand p q) h = PrI (iand q p) h :=
  subst_taut (Form.conj (.var 0) (.var 1)) (Form.conj (.var 1) (.var 0))
    (fun n => match n with | 0 => p | _ => q) h hc
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])

/-- 連言の結合 (xy)z = x(yz)。 -/
theorem pr_assoc (x y z h : IProp) (hc : Cons h) :
    PrI (iand (iand x y) z) h = PrI (iand x (iand y z)) h :=
  subst_taut (Form.conj (Form.conj (.var 0) (.var 1)) (.var 2))
    (Form.conj (.var 0) (Form.conj (.var 1) (.var 2)))
    (fun n => match n with | 0 => x | 1 => y | _ => z) h hc
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
          simp [evalB, h0, h1, h2])

/-- 連言の結合と入れ替え (xy)z = x(zy)。 -/
theorem pr_assoc_swap (x y z h : IProp) (hc : Cons h) :
    PrI (iand (iand x y) z) h = PrI (iand x (iand z y)) h :=
  subst_taut (Form.conj (Form.conj (.var 0) (.var 1)) (.var 2))
    (Form.conj (.var 0) (Form.conj (.var 2) (.var 1)))
    (fun n => match n with | 0 => x | 1 => y | _ => z) h hc
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
          simp [evalB, h0, h1, h2])

/-- a₁/h = k₁ + k₂ + k₄ + k₅。 -/
theorem dec_a₁ (a₁ a₂ e h : IProp) (hc : Cons h) :
    PrI a₁ h = K₁ a₁ a₂ e h + K₂ a₁ a₂ e h + K₄ a₁ a₂ e h + K₅ a₁ a₂ e h := by
  have s1 := def_IX_i a₁ a₂ h
  have s2 := def_IX_i (iand a₁ a₂) e h
  have s3 := def_IX_i (iand a₁ (inot a₂)) e h
  have r1 := pr_comm (iand a₁ a₂) e h hc
  have r4 := pr_comm (iand a₁ a₂) (inot e) h hc
  have r2 := pr_comm (iand a₁ (inot a₂)) e h hc
  have r5 := pr_comm (iand a₁ (inot a₂)) (inot e) h hc
  unfold K₁ K₂ K₄ K₅
  linarith

/-- a₂/h = k₁ + k₃ + k₄ + k₆。 -/
theorem dec_a₂ (a₁ a₂ e h : IProp) (hc : Cons h) :
    PrI a₂ h = K₁ a₁ a₂ e h + K₃ a₁ a₂ e h + K₄ a₁ a₂ e h + K₆ a₁ a₂ e h := by
  have s1 := def_IX_i a₂ a₁ h
  have c1 := pr_comm a₂ a₁ h hc
  have c2 := pr_comm a₂ (inot a₁) h hc
  have s2 := def_IX_i (iand a₁ a₂) e h
  have s3 := def_IX_i (iand (inot a₁) a₂) e h
  have r1 := pr_comm (iand a₁ a₂) e h hc
  have r4 := pr_comm (iand a₁ a₂) (inot e) h hc
  have r3 := pr_comm (iand (inot a₁) a₂) e h hc
  have r6 := pr_comm (iand (inot a₁) a₂) (inot e) h hc
  unfold K₁ K₃ K₄ K₆
  linarith

/-- ea₁/h = k₁ + k₂。 -/
theorem dec_ea₁ (a₁ a₂ e h : IProp) (hc : Cons h) :
    PrI (iand e a₁) h = K₁ a₁ a₂ e h + K₂ a₁ a₂ e h := by
  have s := def_IX_i (iand e a₁) a₂ h
  have r1 := pr_assoc e a₁ a₂ h hc
  have r2 := pr_assoc e a₁ (inot a₂) h hc
  unfold K₁ K₂
  linarith

/-- ea₂/h = k₁ + k₃。 -/
theorem dec_ea₂ (a₁ a₂ e h : IProp) (hc : Cons h) :
    PrI (iand e a₂) h = K₁ a₁ a₂ e h + K₃ a₁ a₂ e h := by
  have s := def_IX_i (iand e a₂) a₁ h
  have r1 := pr_assoc_swap e a₂ a₁ h hc
  have r3 := pr_assoc_swap e a₂ (inot a₁) h hc
  unfold K₁ K₃
  linarith

/-- e/h = k₁ + k₂ + k₃ + k₈。 -/
theorem dec_e (a₁ a₂ e h : IProp) (hc : Cons h) :
    PrI e h = K₁ a₁ a₂ e h + K₂ a₁ a₂ e h + K₃ a₁ a₂ e h + K₈ a₁ a₂ e h := by
  have s := def_IX_i e a₁ h
  have d1 := dec_ea₁ a₁ a₂ e h hc
  have s' := def_IX_i (iand e (inot a₁)) a₂ h
  have r8 := pr_assoc e (inot a₁) (inot a₂) h hc
  have r3 := pr_assoc e (inot a₁) a₂ h hc
  unfold K₃ K₈
  linarith

/-- 構成要素の総和は 1。 -/
theorem dec_sum (a₁ a₂ e h : IProp) (hc : Cons h) :
    K₁ a₁ a₂ e h + K₂ a₁ a₂ e h + K₃ a₁ a₂ e h + K₄ a₁ a₂ e h + K₅ a₁ a₂ e h
      + K₆ a₁ a₂ e h + K₇ a₁ a₂ e h + K₈ a₁ a₂ e h = 1 := by
  have t := th_13_1_i a₁ h hc
  have d1 := dec_a₁ a₁ a₂ e h hc
  have s1 := def_IX_i (inot a₁) a₂ h
  have s2 := def_IX_i (iand (inot a₁) (inot a₂)) e h
  have s3 := def_IX_i (iand (inot a₁) a₂) e h
  have r8 := pr_comm (iand (inot a₁) (inot a₂)) e h hc
  have r7 := pr_comm (iand (inot a₁) (inot a₂)) (inot e) h hc
  have r3 := pr_comm (iand (inot a₁) a₂) e h hc
  have r6 := pr_comm (iand (inot a₁) a₂) (inot e) h hc
  unfold K₃ K₆ K₇ K₈
  linarith

/-- e/ā₁ā₂h = 0 ならば k₈ = 0 (Def. X 左形)。 -/
theorem K₈_zero (a₁ a₂ e h : IProp)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) : K₈ a₁ a₂ e h = 0 := by
  unfold K₈
  rw [def_X_left_i, hexh, zero_mul]

/-- c₁p₁ = a₁/h . e/a₁h = ea₁/h (Def. X 左形)。 -/
theorem cp_eq (a e h : IProp) : PrI a h * PrI e (iand a h) = PrI (iand e a) h := by
  rw [def_X_left_i e a h, mul_comm]

/-! ## § 2 Boole の解: Keynes の公理 + 理想的条件から -/

/-- **理想的条件から Boole の方程式** (KeynesI 担体): Cons h、e/ā₁ā₂h = 0、理想的条件の下で、
u = e/h は c₁ = a₁/h, c₂ = a₂/h, p₁ = e/a₁h, p₂ = e/a₂h の Boole の方程式の根。
#print axioms は KeynesI の公理だけ (Boole.ax_* は前提に取る)。 -/
theorem root_of_ideal_i (a₁ a₂ e h : IProp) (hc : Cons h)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) (hid : IdealI a₁ a₂ e h) :
    Root (PrI a₁ h) (PrI a₂ h) (PrI e (iand a₁ h)) (PrI e (iand a₂ h)) (PrI e h) := by
  have z := K₈_zero a₁ a₂ e h hexh
  have hsum := dec_sum a₁ a₂ e h hc
  refine root_of_ideal _ _ _ _ _ (K₁ a₁ a₂ e h) (K₂ a₁ a₂ e h) (K₃ a₁ a₂ e h) (K₄ a₁ a₂ e h)
    (K₅ a₁ a₂ e h) (K₆ a₁ a₂ e h) (K₇ a₁ a₂ e h) (dec_a₁ a₁ a₂ e h hc) (dec_a₂ a₁ a₂ e h hc)
    ?_ ?_ ?_ (by linarith) hid
  · rw [cp_eq]; exact dec_ea₁ a₁ a₂ e h hc
  · rw [cp_eq]; exact dec_ea₂ a₁ a₂ e h hc
  · rw [dec_e a₁ a₂ e h hc, z, add_zero]

/-- **Boole の解 (KeynesI 担体)**: 方程式の根であり、限界は Keynes の (56.1)
(th_17_56_1_i) から来る。 -/
theorem solution_of_ideal (a₁ a₂ e h : IProp) (hc : Cons h)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) (hid : IdealI a₁ a₂ e h) :
    solution (PrI a₁ h) (PrI a₂ h) (PrI e (iand a₁ h)) (PrI e (iand a₂ h)) (PrI e h) :=
  ⟨root_of_ideal_i a₁ a₂ e h hc hexh hid,
    (limits_iff _ _ _ _ _).mpr
      (th_17_56_1_i a₁ a₂ e h _ _ _ _ _ hc rfl rfl rfl rfl rfl hexh)⟩

/-! ### 名前付きの data と Boole の公理

外部公理 (Keynes の公理でないもの):
  A₁, A₂, E, H            : 問題の二つの原因・事象・data の名付け (内容を主張しない)。
  ax_data_cons            : H は矛盾する連言でない (公理 (i) の但し書きを H に当てはめたもの)。
  ax_exh                  : E/Ā₁Ā₂H = 0 (folio 187「E cannot appear in the absence of both」;
                            Keynes の hexh と同じ data で、Keynes 側では定理の前提に置く)。
  ax_ideal_ebar           : Boole の理想的条件その 1 (Ē の下で A₁ と A₂ は独立; k₄k₇ = k₅k₆)。
  ax_ideal_cross          : Boole の理想的条件その 2 (k₁k₇ = k₂k₃)。
Keynes の (56)–(56.5) が使わないのは ax_ideal_ebar・ax_ideal_cross の 2 本。 -/

axiom A₁ : IProp
axiom A₂ : IProp
axiom E : IProp
axiom H : IProp
axiom ax_data_cons : Cons H
axiom ax_exh : PrI E (iand (iand (inot A₁) (inot A₂)) H) = 0
axiom ax_ideal_ebar : K₄ A₁ A₂ E H * K₇ A₁ A₂ E H = K₅ A₁ A₂ E H * K₆ A₁ A₂ E H
axiom ax_ideal_cross : K₁ A₁ A₂ E H * K₇ A₁ A₂ E H = K₂ A₁ A₂ E H * K₃ A₁ A₂ E H

/-- **Boole の解 (名前付きの data の上)**: E/H は Boole の解。#print axioms に Boole.ax_* が出る。 -/
theorem solution_data :
    solution (PrI A₁ H) (PrI A₂ H) (PrI E (iand A₁ H)) (PrI E (iand A₂ H)) (PrI E H) :=
  solution_of_ideal A₁ A₂ E H ax_data_cons ax_exh ⟨ax_ideal_ebar, ax_ideal_cross⟩

/-! ## § 3 比較定理 1: Boole の解は Keynes の区間に入る -/

/-- Boole の根は (56.5) の下限 c₁p₁ + c₂p₂ − c₁c₂ 以上 (純算術; 原因の独立を仮定しない)。
恒等式 (1 − u)(c₁c₂ − k₁) = −F + k₁m₁m₂ + (1 − u)(k₂m₂ + m₁k₃ + m₁m₂) による
(k₁ = c₁p₁ + c₂p₂ − u, k₂ = u − c₂p₂, k₃ = u − c₁p₁, m_r = c_r(1 − p_r))。 -/
theorem solution_ge_565 (c₁ c₂ p₁ p₂ u : ℝ) (hd : Data c₁ c₂ p₁ p₂)
    (hs : solution c₁ c₂ p₁ p₂ u) : c₁ * p₁ + c₂ * p₂ - c₁ * c₂ ≤ u := by
  obtain ⟨hc1, hc1', hc2, hc2', hp1, hp1', hp2, hp2'⟩ := hd
  obtain ⟨hR, l1, l2, l3, l4, l5⟩ := hs
  unfold Root at hR
  have hm1 : 0 ≤ c₁ * (1 - p₁) := mul_nonneg hc1 (by linarith)
  have hm2 : 0 ≤ c₂ * (1 - p₂) := mul_nonneg hc2 (by linarith)
  have hk1 : 0 ≤ c₁ * p₁ + c₂ * p₂ - u := by linarith
  have hk2 : 0 ≤ u - c₂ * p₂ := by linarith
  have hk3 : 0 ≤ u - c₁ * p₁ := by linarith
  have hu1 : u ≤ 1 := by linarith
  have iden : (1 - u) * (c₁ * c₂ - (c₁ * p₁ + c₂ * p₂ - u))
      = - F c₁ c₂ p₁ p₂ u + (c₁ * p₁ + c₂ * p₂ - u) * (c₁ * (1 - p₁)) * (c₂ * (1 - p₂))
        + (1 - u) * ((u - c₂ * p₂) * (c₂ * (1 - p₂)) + (c₁ * (1 - p₁)) * (u - c₁ * p₁)
          + (c₁ * (1 - p₁)) * (c₂ * (1 - p₂))) := by
    unfold F; ring
  rcases hu1.lt_or_eq with hlt | heq
  · have hsu : 0 < 1 - u := by linarith
    have hr : 0 ≤ (c₁ * p₁ + c₂ * p₂ - u) * (c₁ * (1 - p₁)) * (c₂ * (1 - p₂))
        + (1 - u) * ((u - c₂ * p₂) * (c₂ * (1 - p₂)) + (c₁ * (1 - p₁)) * (u - c₁ * p₁)
          + (c₁ * (1 - p₁)) * (c₂ * (1 - p₂))) := by
      apply add_nonneg (mul_nonneg (mul_nonneg hk1 hm1) hm2)
      apply mul_nonneg hsu.le
      exact add_nonneg (add_nonneg (mul_nonneg hk2 hm2) (mul_nonneg hm1 hk3)) (mul_nonneg hm1 hm2)
    rw [hR, neg_zero, zero_add] at iden
    by_contra hneg
    have := mul_pos hsu (show 0 < -(c₁ * c₂ - (c₁ * p₁ + c₂ * p₂ - u)) by linarith)
    linarith
  · -- u = 1: m₁ = m₂ = 0 で c_r = c_r p_r、(1 − c₁)(1 − c₂) ⩾ 0
    subst heq
    have e1 : c₁ * (1 - p₁) = 0 := by linarith
    have e2 : c₂ * (1 - p₂) = 0 := by linarith
    have := mul_nonneg (show 0 ≤ 1 - c₁ by linarith) (show 0 ≤ 1 - c₂ by linarith)
    nlinarith [e1, e2]

/-- **比較定理 1 (区間に入る)**: data が範囲内なら、Boole の解 u は
(i) Keynes の (56.1) の区間 (th_17_56_1_cited の結論) にあり、
(ii) (56.2) の上限 p₁ + p₂ 以下 (修正形 ⩽)、
(iii) (56.5) の下限 c₁p₁ + c₂p₂ − c₁c₂ 以上 (修正形 ⩾; 原因の独立を仮定しない)。 -/
theorem solution_between (c₁ c₂ p₁ p₂ u : ℝ) (hd : Data c₁ c₂ p₁ p₂)
    (hs : solution c₁ c₂ p₁ p₂ u) :
    (max (c₁ * p₁) (c₂ * p₂) ≤ u
      ∧ u ≤ min (c₁ * p₁ + c₂ * p₂) (min (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂))))
    ∧ u ≤ p₁ + p₂ ∧ c₁ * p₁ + c₂ * p₂ - c₁ * c₂ ≤ u := by
  have h565 := solution_ge_565 c₁ c₂ p₁ p₂ u hd hs
  obtain ⟨hc1, hc1', hc2, hc2', hp1, hp1', hp2, hp2'⟩ := hd
  obtain ⟨-, l1, l2, l3, l4, l5⟩ := hs
  refine ⟨th_17_56_1_cited c₁ c₂ p₁ p₂ u l5 (by linarith) (by linarith) l1 l2, ?_, h565⟩
  have k1 : c₁ * p₁ ≤ p₁ := mul_le_of_le_one_left hp1 hc1'
  have k2 : c₂ * p₂ ≤ p₂ := mul_le_of_le_one_left hp2 hc2'
  linarith

/-- **(56.5) の下限を理想的条件から (KeynesI 担体)**: Cons h、e/ā₁ā₂h = 0、理想的条件の下で
u ⩾ c₁p₁ + c₂p₂ − c₁c₂。th_17_56_5_i の前提 a₁/a₂h = a₁/h を使わない。 -/
theorem bound_565_of_ideal_i (a₁ a₂ e h : IProp) (hc : Cons h)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) (hid : IdealI a₁ a₂ e h) :
    PrI e h ≥ PrI a₁ h * PrI e (iand a₁ h) + PrI a₂ h * PrI e (iand a₂ h)
      - PrI a₁ h * PrI a₂ h := by
  have hd : Data (PrI a₁ h) (PrI a₂ h) (PrI e (iand a₁ h)) (PrI e (iand a₂ h)) :=
    ⟨ax_range_lo_i _ _, ax_range_hi_i _ _, ax_range_lo_i _ _, ax_range_hi_i _ _,
      ax_range_lo_i _ _, ax_range_hi_i _ _, ax_range_lo_i _ _, ax_range_hi_i _ _⟩
  exact solution_ge_565 _ _ _ _ _ hd (solution_of_ideal a₁ a₂ e h hc hexh hid)

/-! ## § 4 Wilbraham の形 (folio 187 脚注 3) -/

/-- Wilbraham の形: u = c₁p₁ + c₂p₂ − z で z ⩽ c₁p₁, z ⩽ c₂p₂ (印刷の「less than」は ⩽ で;
台帳 ch17-005 と同じ読み)。 -/
def Wilbraham (c₁ c₂ p₁ p₂ u : ℝ) : Prop :=
  ∃ z, u = c₁ * p₁ + c₂ * p₂ - z ∧ z ≤ c₁ * p₁ ∧ z ≤ c₂ * p₂

/-- Wilbraham の形は Keynes の体系の定理 (z := ea₁a₂/h; ch17-022 th_17_56_l022_i から)。
Boole の公理を使わない。 -/
theorem wilbraham_of_keynes_i (a₁ a₂ e h : IProp) (hc : Cons h)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    Wilbraham (PrI a₁ h) (PrI a₂ h) (PrI e (iand a₁ h)) (PrI e (iand a₂ h)) (PrI e h) := by
  refine ⟨K₁ a₁ a₂ e h,
    th_17_56_l022_i a₁ a₂ e h _ _ _ _ _ _ hc rfl rfl rfl rfl rfl rfl hexh, ?_, ?_⟩
  · rw [cp_eq, dec_ea₁ a₁ a₂ e h hc]
    have := ax_range_lo_i (iand e (iand a₁ (inot a₂))) h
    unfold K₂; linarith
  · rw [cp_eq, dec_ea₂ a₁ a₂ e h hc]
    have := ax_range_lo_i (iand e (iand (inot a₁) a₂)) h
    unfold K₃; linarith

/-- Boole の解も Wilbraham の形を満たす (z := c₁p₁ + c₂p₂ − u)。 -/
theorem wilbraham_of_solution (c₁ c₂ p₁ p₂ u : ℝ) (hs : solution c₁ c₂ p₁ p₂ u) :
    Wilbraham c₁ c₂ p₁ p₂ u := by
  obtain ⟨-, l1, l2, -, -, -⟩ := hs
  exact ⟨c₁ * p₁ + c₂ * p₂ - u, by ring, by linarith, by linarith⟩

/-! ## § 5 比較定理 2: Boole の解には Keynes の公理に無い前提が要る (模型)

phase16a の NoX.Ops (4 世界の部分集合、条件 h ごとの重みの比) を使う。重みが h によらない
とき Def. X の両形が成り立ち、phase16a の公理 13 本がすべて成り立つ (sysK_fixed)。 -/

open NoX

/-- phase16a の公理 13 本 (def_X 以外の 11 本 = SysNoX と Def. X 両形) を場に写したもの。 -/
def SysK (S : Ops) : Prop :=
  SysNoX S
    ∧ (∀ p q h, S.pr (S.and_ p q) h = S.pr p (S.and_ q h) * S.pr q h)
    ∧ (∀ p q h, S.pr (S.and_ p q) h = S.pr q (S.and_ p h) * S.pr p h)

/-- 重み ω が h によらないとき Def. X 左形が成り立つ。 -/
theorem fixed_X_left (ω : W → ℝ) (hω : ∀ w, 0 < ω w) (p q h : M) :
    prw (fun _ => ω) (mand p q) h = prw (fun _ => ω) p (mand q h) * prw (fun _ => ω) q h := by
  by_cases hh : h = ∅
  · subst hh
    simp [prw, mand]
  by_cases hq : mand q h = ∅
  · have e : mand p q ∩ h = ∅ := by
      rw [show mand p q ∩ h = p ∩ mand q h by simp [mand, Finset.inter_assoc], hq,
        Finset.inter_empty]
    rw [hq, prw_of_empty, zero_mul, prw_of_ne hh, e]
    simp [mu]
  · have hqpos : 0 < mu ω (mand q h) := mu_pos hω (Finset.nonempty_iff_ne_empty.mpr hq)
    have hhpos : 0 < mu ω h := mu_pos hω (Finset.nonempty_iff_ne_empty.mpr hh)
    have e : mand p q ∩ h = p ∩ mand q h := by simp [mand, Finset.inter_assoc]
    rw [prw_of_ne hh, prw_of_ne hq, prw_of_ne hh, e]
    show mu ω (p ∩ mand q h) / mu ω h = mu ω (p ∩ mand q h) / mu ω (mand q h) * (mu ω (q ∩ h) / mu ω h)
    rw [show q ∩ h = mand q h from rfl]
    field_simp

/-- 重み ω が h によらないとき Def. X 右形が成り立つ。 -/
theorem fixed_X_right (ω : W → ℝ) (hω : ∀ w, 0 < ω w) (p q h : M) :
    prw (fun _ => ω) (mand p q) h = prw (fun _ => ω) q (mand p h) * prw (fun _ => ω) p h := by
  rw [show mand p q = mand q p from Finset.inter_comm p q]
  exact fixed_X_left ω hω q p h

/-- 重みが h によらない正の重みの模型は、phase16a の公理 13 本をすべて満たす。 -/
theorem sysK_fixed (ω : W → ℝ) (hω : ∀ w, 0 < ω w) : SysK (wOps (fun _ => ω)) :=
  ⟨wSysNoX (fun _ w => hω w), fixed_X_left ω hω, fixed_X_right ω hω⟩

/-- 「data の前提 (Cons h, e/ā₁ā₂h = 0) だけから Boole の方程式が出る」という言明を場 S の上で。 -/
def StmtBoole (S : Ops) : Prop :=
  ∀ a₁ a₂ e h : S.P, S.cons h → S.pr e (S.and_ (S.and_ (S.not_ a₁) (S.not_ a₂)) h) = 0 →
    Root (S.pr a₁ h) (S.pr a₂ h) (S.pr e (S.and_ a₁ h)) (S.pr e (S.and_ a₂ h)) (S.pr e h)

/-- 「data の前提だけから (56.5) の下限が出る」という言明を場 S の上で。 -/
def Stmt565 (S : Ops) : Prop :=
  ∀ a₁ a₂ e h : S.P, S.cons h → S.pr e (S.and_ (S.and_ (S.not_ a₁) (S.not_ a₂)) h) = 0 →
    S.pr a₁ h * S.pr e (S.and_ a₁ h) + S.pr a₂ h * S.pr e (S.and_ a₂ h)
      - S.pr a₁ h * S.pr a₂ h ≤ S.pr e h

/-- 場 S の上の構成要素の確率と理想的条件。 -/
def IdealS (S : Ops) (a₁ a₂ e h : S.P) : Prop :=
  Ideal (S.pr (S.and_ e (S.and_ a₁ a₂)) h) (S.pr (S.and_ e (S.and_ a₁ (S.not_ a₂))) h)
    (S.pr (S.and_ e (S.and_ (S.not_ a₁) a₂)) h) (S.pr (S.and_ (S.not_ e) (S.and_ a₁ a₂)) h)
    (S.pr (S.and_ (S.not_ e) (S.and_ a₁ (S.not_ a₂))) h)
    (S.pr (S.and_ (S.not_ e) (S.and_ (S.not_ a₁) a₂)) h)
    (S.pr (S.and_ (S.not_ e) (S.and_ (S.not_ a₁) (S.not_ a₂))) h)

/-! ### 一様な重みの模型 MU (4 世界、各 1) -/

/-- 一様な重み。 -/
def ωU : W → ℝ := fun _ => 1

/-- 一様な重みの模型。 -/
noncomputable abbrev MU : Ops := wOps (fun _ => ωU)

theorem sysK_MU : SysK MU := sysK_fixed ωU (fun _ => one_pos)

/-- 一様な重みでは x/h = |x ∩ h| / |h|。 -/
theorem prwU (p h : M) (hh : h ≠ ∅) :
    prw (fun _ => ωU) p h = ((p ∩ h).card : ℝ) / (h.card : ℝ) := by
  rw [prw_of_ne hh]
  simp [mu, ωU]

/-! ### 模型 1 (排反): a₁ = {0, 1}, a₂ = {2, 3}, e = {0, 2}, h = ⊤ (phase16a の a₁ₘ, a₂ₘ, eₘ)。
c₁ = c₂ = p₁ = p₂ = 1/2、u = 1/2 = c₁p₁ + c₂p₂ (Keynes の ch17-004 の場合)。 -/

theorem ex_c₁ : prw (fun _ => ωU) a₁ₘ mtrue = 1/2 := by
  rw [prwU _ _ (by decide), show (a₁ₘ ∩ mtrue).card = 2 by decide,
    show (mtrue : M).card = 4 by decide]; norm_num
theorem ex_c₂ : prw (fun _ => ωU) a₂ₘ mtrue = 1/2 := by
  rw [prwU _ _ (by decide), show (a₂ₘ ∩ mtrue).card = 2 by decide,
    show (mtrue : M).card = 4 by decide]; norm_num
theorem ex_p₁ : prw (fun _ => ωU) eₘ (mand a₁ₘ mtrue) = 1/2 := by
  rw [prwU _ _ (by decide), show (eₘ ∩ mand a₁ₘ mtrue).card = 1 by decide,
    show (mand a₁ₘ mtrue).card = 2 by decide]; norm_num
theorem ex_p₂ : prw (fun _ => ωU) eₘ (mand a₂ₘ mtrue) = 1/2 := by
  rw [prwU _ _ (by decide), show (eₘ ∩ mand a₂ₘ mtrue).card = 1 by decide,
    show (mand a₂ₘ mtrue).card = 2 by decide]; norm_num
theorem ex_u : prw (fun _ => ωU) eₘ mtrue = 1/2 := by
  rw [prwU _ _ (by decide), show (eₘ ∩ mtrue).card = 2 by decide,
    show (mtrue : M).card = 4 by decide]; norm_num
theorem ex_exh : prw (fun _ => ωU) eₘ (mand (mand (mnot a₁ₘ) (mnot a₂ₘ)) mtrue) = 0 := by
  rw [show mand (mand (mnot a₁ₘ) (mnot a₂ₘ)) mtrue = ∅ by decide, prw_of_empty]

/-- **比較定理 2 (追加前提が要る)**: 公理 13 本を満たす模型 MU で、Cons ⊤ と e/ā₁ā₂h = 0 が
成り立つのに、Boole の方程式は偽 (F(1/2) = −1/32 ≠ 0; Keynes の「Boole's equations do not
reduce to this simplified form」)。同じ模型で Boole の理想的条件も偽 (k₁k₇ = 0 ≠ 1/16 = k₂k₃)。 -/
theorem boole_needs_premiss : SysK MU ∧ ¬ StmtBoole MU ∧ ¬ IdealS MU a₁ₘ a₂ₘ eₘ mtrue := by
  refine ⟨sysK_MU, fun Hs => ?_, fun Hi => ?_⟩
  · have k := Hs a₁ₘ a₂ₘ eₘ mtrue model_cons_tru ex_exh
    change Root (prw (fun _ => ωU) a₁ₘ mtrue) (prw (fun _ => ωU) a₂ₘ mtrue)
      (prw (fun _ => ωU) eₘ (mand a₁ₘ mtrue)) (prw (fun _ => ωU) eₘ (mand a₂ₘ mtrue))
      (prw (fun _ => ωU) eₘ mtrue) at k
    rw [ex_c₁, ex_c₂, ex_p₁, ex_p₂, ex_u] at k
    unfold Root at k
    rw [F_half_half] at k
    norm_num at k
  · obtain ⟨-, hX⟩ := Hi
    change prw (fun _ => ωU) (mand eₘ (mand a₁ₘ a₂ₘ)) mtrue
        * prw (fun _ => ωU) (mand (mnot eₘ) (mand (mnot a₁ₘ) (mnot a₂ₘ))) mtrue
      = prw (fun _ => ωU) (mand eₘ (mand a₁ₘ (mnot a₂ₘ))) mtrue
        * prw (fun _ => ωU) (mand eₘ (mand (mnot a₁ₘ) a₂ₘ)) mtrue at hX
    rw [prwU _ _ (by decide), prwU _ _ (by decide), prwU _ _ (by decide),
      prwU _ _ (by decide),
      show (mand eₘ (mand a₁ₘ a₂ₘ) ∩ mtrue).card = 0 by decide,
      show (mand eₘ (mand a₁ₘ (mnot a₂ₘ)) ∩ mtrue).card = 1 by decide,
      show (mand eₘ (mand (mnot a₁ₘ) a₂ₘ) ∩ mtrue).card = 1 by decide,
      show (mtrue : M).card = 4 by decide] at hX
    norm_num at hX

/-! ### 模型 2 (独立): a₁ = {0, 1}, a₂ = {0, 2}, e = {0}, h = ⊤。
c₁ = c₂ = p₁ = p₂ = 1/2 (模型 1 と同じ data)、u = 1/4。 -/

/-- 模型 2 の a₂。 -/
def a₂ᵢ : M := {0, 2}
/-- 模型 2 の e。 -/
def eᵢ : M := {0}

theorem in_c₁ : prw (fun _ => ωU) a₁ₘ mtrue = 1/2 := ex_c₁
theorem in_c₂ : prw (fun _ => ωU) a₂ᵢ mtrue = 1/2 := by
  rw [prwU _ _ (by decide), show (a₂ᵢ ∩ mtrue).card = 2 by decide,
    show (mtrue : M).card = 4 by decide]; norm_num
theorem in_p₁ : prw (fun _ => ωU) eᵢ (mand a₁ₘ mtrue) = 1/2 := by
  rw [prwU _ _ (by decide), show (eᵢ ∩ mand a₁ₘ mtrue).card = 1 by decide,
    show (mand a₁ₘ mtrue).card = 2 by decide]; norm_num
theorem in_p₂ : prw (fun _ => ωU) eᵢ (mand a₂ᵢ mtrue) = 1/2 := by
  rw [prwU _ _ (by decide), show (eᵢ ∩ mand a₂ᵢ mtrue).card = 1 by decide,
    show (mand a₂ᵢ mtrue).card = 2 by decide]; norm_num
theorem in_u : prw (fun _ => ωU) eᵢ mtrue = 1/4 := by
  rw [prwU _ _ (by decide), show (eᵢ ∩ mtrue).card = 1 by decide,
    show (mtrue : M).card = 4 by decide]; norm_num
theorem in_exh : prw (fun _ => ωU) eᵢ (mand (mand (mnot a₁ₘ) (mnot a₂ᵢ)) mtrue) = 0 := by
  rw [prwU _ _ (by decide),
    show (eᵢ ∩ mand (mand (mnot a₁ₘ) (mnot a₂ᵢ)) mtrue).card = 0 by decide]; norm_num
/-- 模型 2 では原因が独立: a₁/a₂h = a₁/h = 1/2 ((56.5) の前提)。 -/
theorem in_indep : prw (fun _ => ωU) a₁ₘ (mand a₂ᵢ mtrue) = prw (fun _ => ωU) a₁ₘ mtrue := by
  rw [ex_c₁, prwU _ _ (by decide), show (a₁ₘ ∩ mand a₂ᵢ mtrue).card = 1 by decide,
    show (mand a₂ᵢ mtrue).card = 2 by decide]; norm_num

/-- **data は u を定めない**: 同じ模型 MU (公理 13 本を満たす) の中で、data
c₁ = c₂ = p₁ = p₂ = 1/2 と前提 (Cons ⊤, e/ā₁ā₂h = 0) が同じで、u = 1/2 (模型 1, 排反) と
u = 1/4 (模型 2, 独立) になる。どちらも Boole の根ではない (F(1/2) = −1/32, F(1/4) = 1/16)。
Boole の解は 1/4 と 1/2 の間の第三の値 (half_solution)。 -/
theorem undetermined :
    SysK MU
    ∧ (prw (fun _ => ωU) a₁ₘ mtrue = 1/2 ∧ prw (fun _ => ωU) a₂ₘ mtrue = 1/2
        ∧ prw (fun _ => ωU) eₘ (mand a₁ₘ mtrue) = 1/2
        ∧ prw (fun _ => ωU) eₘ (mand a₂ₘ mtrue) = 1/2 ∧ prw (fun _ => ωU) eₘ mtrue = 1/2)
    ∧ (prw (fun _ => ωU) a₁ₘ mtrue = 1/2 ∧ prw (fun _ => ωU) a₂ᵢ mtrue = 1/2
        ∧ prw (fun _ => ωU) eᵢ (mand a₁ₘ mtrue) = 1/2
        ∧ prw (fun _ => ωU) eᵢ (mand a₂ᵢ mtrue) = 1/2 ∧ prw (fun _ => ωU) eᵢ mtrue = 1/4)
    ∧ ¬ Root (1/2) (1/2) (1/2) (1/2) (1/2) ∧ ¬ Root (1/2) (1/2) (1/2) (1/2) (1/4)
    ∧ ∃ u, solution (1/2) (1/2) (1/2) (1/2) u ∧ 1/4 < u ∧ u < 1/2 := by
  refine ⟨sysK_MU, ⟨ex_c₁, ex_c₂, ex_p₁, ex_p₂, ex_u⟩, ⟨in_c₁, in_c₂, in_p₁, in_p₂, in_u⟩,
    ?_, ?_, half_solution⟩
  · unfold Root; rw [F_half_half]; norm_num
  · unfold Root; rw [F_half_quarter]; norm_num

/-! ### 模型 3 (Boole の理想的条件を満たす): 重み (1, 2, 2, 4)、世界 0 = EA₁A₂, 1 = EA₁Ā₂,
2 = EĀ₁A₂, 3 = ĒĀ₁Ā₂。a₁ = {0, 1}, a₂ = {0, 2}, e = {0, 1, 2}, h = ⊤。
c₁ = c₂ = 1/3, p₁ = p₂ = 1, u = 5/9 (Boole の解 third_solution)。 -/

/-- 重み (1, 2, 2, 4)。 -/
def ωB (w : W) : ℝ := if w = 0 then 1 else if w = 3 then 4 else 2

theorem ωB_pos : ∀ w, 0 < ωB w := by
  intro w; unfold ωB; split_ifs <;> norm_num

/-- 模型 3。 -/
noncomputable abbrev MB : Ops := wOps (fun _ => ωB)

/-- 模型 3 の e。 -/
def eB : M := {0, 1, 2}

theorem mu_ωB_univ : mu ωB mtrue = 9 := by
  simp [mu, ωB, mtrue, Fin.sum_univ_four]; norm_num

theorem bm_c₁ : prw (fun _ => ωB) a₁ₘ mtrue = 1/3 := by
  rw [prw_of_ne (by decide), show a₁ₘ ∩ mtrue = {0, 1} by decide]
  show mu ωB {0, 1} / mu ωB mtrue = 1/3
  rw [mu_ωB_univ]; simp [mu, ωB]; norm_num
theorem bm_c₂ : prw (fun _ => ωB) a₂ᵢ mtrue = 1/3 := by
  rw [prw_of_ne (by decide), show a₂ᵢ ∩ mtrue = {0, 2} by decide]
  show mu ωB {0, 2} / mu ωB mtrue = 1/3
  rw [mu_ωB_univ]; simp [mu, ωB]; norm_num
theorem bm_p₁ : prw (fun _ => ωB) eB (mand a₁ₘ mtrue) = 1 := by
  rw [prw_of_ne (by decide), show eB ∩ mand a₁ₘ mtrue = mand a₁ₘ mtrue by decide]
  exact div_self (mu_pos ωB_pos (by decide)).ne'
theorem bm_p₂ : prw (fun _ => ωB) eB (mand a₂ᵢ mtrue) = 1 := by
  rw [prw_of_ne (by decide), show eB ∩ mand a₂ᵢ mtrue = mand a₂ᵢ mtrue by decide]
  exact div_self (mu_pos ωB_pos (by decide)).ne'
theorem bm_u : prw (fun _ => ωB) eB mtrue = 5/9 := by
  rw [prw_of_ne (by decide), show eB ∩ mtrue = {0, 1, 2} by decide]
  show mu ωB {0, 1, 2} / mu ωB mtrue = 5/9
  rw [mu_ωB_univ]; simp [mu, ωB]; norm_num
theorem bm_exh : prw (fun _ => ωB) eB (mand (mand (mnot a₁ₘ) (mnot a₂ᵢ)) mtrue) = 0 := by
  rw [prw_of_ne (by decide), show eB ∩ mand (mand (mnot a₁ₘ) (mnot a₂ᵢ)) mtrue = ∅ by decide]
  simp [mu]

/-- 模型 3 では Boole の理想的条件が成り立つ (k₄ = k₅ = k₆ = 0, k₁k₇ = 4/81 = k₂k₃)。 -/
theorem bm_ideal : IdealS MB a₁ₘ a₂ᵢ eB mtrue := by
  have z : ∀ x : M, x ∩ mtrue = ∅ → prw (fun _ => ωB) x mtrue = 0 := by
    intro x hx; rw [prw_of_ne (by decide), hx]; simp [mu]
  have val : ∀ (x : M) (s : M), x ∩ mtrue = s →
      prw (fun _ => ωB) x mtrue = mu ωB s / 9 := by
    intro x s hx; rw [prw_of_ne (by decide), hx]; show mu ωB s / mu ωB mtrue = _
    rw [mu_ωB_univ]
  refine ⟨?_, ?_⟩
  · change prw (fun _ => ωB) (mand (mnot eB) (mand a₁ₘ a₂ᵢ)) mtrue
        * prw (fun _ => ωB) (mand (mnot eB) (mand (mnot a₁ₘ) (mnot a₂ᵢ))) mtrue
      = prw (fun _ => ωB) (mand (mnot eB) (mand a₁ₘ (mnot a₂ᵢ))) mtrue
        * prw (fun _ => ωB) (mand (mnot eB) (mand (mnot a₁ₘ) a₂ᵢ)) mtrue
    rw [z (mand (mnot eB) (mand a₁ₘ a₂ᵢ)) (by decide),
      z (mand (mnot eB) (mand a₁ₘ (mnot a₂ᵢ))) (by decide),
      z (mand (mnot eB) (mand (mnot a₁ₘ) a₂ᵢ)) (by decide)]; ring
  · change prw (fun _ => ωB) (mand eB (mand a₁ₘ a₂ᵢ)) mtrue
        * prw (fun _ => ωB) (mand (mnot eB) (mand (mnot a₁ₘ) (mnot a₂ᵢ))) mtrue
      = prw (fun _ => ωB) (mand eB (mand a₁ₘ (mnot a₂ᵢ))) mtrue
        * prw (fun _ => ωB) (mand eB (mand (mnot a₁ₘ) a₂ᵢ)) mtrue
    rw [val _ {0} (by decide), val _ {3} (by decide), val _ {1} (by decide),
      val _ {2} (by decide)]
    simp [mu, ωB]; norm_num

/-- **Boole の前提は Keynes の公理と両立する**: 公理 13 本を満たす模型 MB で、Cons ⊤、
e/ā₁ā₂h = 0、Boole の理想的条件が成り立ち、u = 5/9 は data (1/3, 1/3, 1, 1) の Boole の解。
Keynes の (56.1) の区間 [1/3, 2/3] にも入る。 -/
theorem boole_model :
    SysK MB ∧ IdealS MB a₁ₘ a₂ᵢ eB mtrue
    ∧ prw (fun _ => ωB) eB (mand (mand (mnot a₁ₘ) (mnot a₂ᵢ)) mtrue) = 0
    ∧ solution (prw (fun _ => ωB) a₁ₘ mtrue) (prw (fun _ => ωB) a₂ᵢ mtrue)
        (prw (fun _ => ωB) eB (mand a₁ₘ mtrue)) (prw (fun _ => ωB) eB (mand a₂ᵢ mtrue))
        (prw (fun _ => ωB) eB mtrue) := by
  refine ⟨sysK_fixed ωB ωB_pos, bm_ideal, bm_exh, ?_⟩
  rw [bm_c₁, bm_c₂, bm_p₁, bm_p₂, bm_u]
  exact third_solution

/-! ### 模型 4 (従属): a₁ = a₂ = e = {0, 1}, h = ⊤。c₁ = c₂ = 1/2, p₁ = p₂ = 1, u = 1/2 だが
c₁p₁ + c₂p₂ − c₁c₂ = 3/4。(56.5) の下限は前提 (原因の独立か Boole の理想的条件) 無しには出ない。 -/

/-- **(56.5) の下限は Keynes の公理だけからは出ない**: 公理 13 本を満たす模型 MU で、
Cons ⊤ と e/ā₁ā₂h = 0 が成り立つのに u = 1/2 < 3/4。 -/
theorem bound_565_needs_premiss : SysK MU ∧ ¬ Stmt565 MU := by
  refine ⟨sysK_MU, fun Hs => ?_⟩
  have hexh : prw (fun _ => ωU) a₁ₘ (mand (mand (mnot a₁ₘ) (mnot a₁ₘ)) mtrue) = 0 := by
    rw [prwU _ _ (by decide),
      show (a₁ₘ ∩ mand (mand (mnot a₁ₘ) (mnot a₁ₘ)) mtrue).card = 0 by decide]; norm_num
  have k := Hs a₁ₘ a₁ₘ a₁ₘ mtrue model_cons_tru hexh
  change prw (fun _ => ωU) a₁ₘ mtrue * prw (fun _ => ωU) a₁ₘ (mand a₁ₘ mtrue)
      + prw (fun _ => ωU) a₁ₘ mtrue * prw (fun _ => ωU) a₁ₘ (mand a₁ₘ mtrue)
      - prw (fun _ => ωU) a₁ₘ mtrue * prw (fun _ => ωU) a₁ₘ mtrue
    ≤ prw (fun _ => ωU) a₁ₘ mtrue at k
  have hp : prw (fun _ => ωU) a₁ₘ (mand a₁ₘ mtrue) = 1 := by
    rw [prwU _ _ (by decide), show (a₁ₘ ∩ mand a₁ₘ mtrue).card = 2 by decide,
      show (mand a₁ₘ mtrue).card = 2 by decide]; norm_num
  rw [ex_c₁, hp] at k
  norm_num at k

/-! ## § 6 外延 (真偽) の担体では data を置けない -/

/-- 命題を真偽で同一視する担体 Prop → Prop → ℝ では、True/h = 1 と Def. IX だけで値は {0, 1} に
強制され (phase7i_model ext_forced と同じ経路)、data c₁ = 1/2 を置けない。Boole の問題を
Keynes の公理の模型で評価するには、事象代数 (世界の集合) の担体を経由する必要がある。 -/
theorem prop_carrier_no_half :
    ¬ ∃ (Pr : Prop → Prop → ℝ), (∀ h : Prop, Pr True h = 1)
      ∧ (∀ p q h : Prop, Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h)
      ∧ ∃ a h : Prop, Pr a h = 1/2 := by
  rintro ⟨Pr, ht, hIX, a, h, ha⟩
  have hF : Pr False h = 0 := by
    have s := hIX False False h
    rw [show (False ∧ ¬False) = False from propext (by tauto),
      show (False ∧ False) = False from propext (by tauto)] at s
    linarith
  by_cases hp : a
  · rw [show a = True from propext (iff_true_intro hp), ht] at ha; norm_num at ha
  · rw [show a = False from propext (iff_false_intro hp), hF] at ha; norm_num at ha

end Boole

/-! ## § 7 依存公理の検査 (外れればコンパイルが落ちる) -/

open Lean in
/-- 定数 n の依存公理に `Boole.` で始まる名前があるか。 -/
def Boole.usesBooleAxiom (n : Name) : CoreM Bool := do
  let axs ← collectAxioms n
  return axs.any (fun a => (`Boole).isPrefixOf a)

open Lean Elab Command in
run_cmd liftCoreM do
  -- Keynes の (56)–(56.5) (phase16a) は Boole の公理に依存しない
  for n in [``KeynesI.th_17_56_raw_i, ``KeynesI.th_17_56_l022_i, ``KeynesI.th_17_56_1_i,
      ``KeynesI.th_17_56_1_cited, ``KeynesI.th_17_56_2_i, ``KeynesI.th_17_56_3_i,
      ``KeynesI.th_17_56_4_i, ``KeynesI.th_17_56_l036_i, ``KeynesI.th_17_56_5_i,
      -- 本ファイルの「前提を仮定に取る」形も Boole の公理に依存しない
      ``Boole.root_of_ideal_i, ``Boole.solution_of_ideal, ``Boole.bound_565_of_ideal_i,
      ``Boole.wilbraham_of_keynes_i, ``Boole.solution_between, ``Boole.boole_needs_premiss,
      ``Boole.undetermined, ``Boole.boole_model, ``Boole.bound_565_needs_premiss] do
    if ← Boole.usesBooleAxiom n then
      throwError "{n} が Boole の公理に依存している"
  -- 名前付きの data の上の Boole の解は Boole の公理に依存する
  unless ← Boole.usesBooleAxiom ``Boole.solution_data do
    throwError "Boole.solution_data が Boole の公理に依存していない"

/-! # 監査クエリ (判定数には数えない) -/

-- Keynes の (56)–(56.5) (phase16a; Boole.* が出ないこと)
#print axioms KeynesI.th_17_56_1_i
#print axioms KeynesI.th_17_56_1_cited
#print axioms KeynesI.th_17_56_2_i
#print axioms KeynesI.th_17_56_3_i
#print axioms KeynesI.th_17_56_4_i
#print axioms KeynesI.th_17_56_5_i
-- § 1 分解
#print axioms Boole.pr_comm
#print axioms Boole.pr_assoc
#print axioms Boole.pr_assoc_swap
#print axioms Boole.dec_a₁
#print axioms Boole.dec_a₂
#print axioms Boole.dec_ea₁
#print axioms Boole.dec_ea₂
#print axioms Boole.dec_e
#print axioms Boole.dec_sum
#print axioms Boole.K₈_zero
#print axioms Boole.cp_eq
-- § 2 Boole の解
#print axioms Boole.root_of_ideal_i
#print axioms Boole.solution_of_ideal
#print axioms Boole.solution_data
-- § 3 比較定理 1
#print axioms Boole.solution_ge_565
#print axioms Boole.solution_between
#print axioms Boole.bound_565_of_ideal_i
-- § 4 Wilbraham
#print axioms Boole.wilbraham_of_keynes_i
#print axioms Boole.wilbraham_of_solution
-- § 5 比較定理 2 (模型; Lean 標準の公理のみのはず)
#print axioms Boole.fixed_X_left
#print axioms Boole.fixed_X_right
#print axioms Boole.sysK_fixed
#print axioms Boole.boole_needs_premiss
#print axioms Boole.undetermined
#print axioms Boole.in_indep
#print axioms Boole.bm_ideal
#print axioms Boole.boole_model
#print axioms Boole.bound_565_needs_premiss
-- § 6 外延の担体
#print axioms Boole.prop_carrier_no_half
