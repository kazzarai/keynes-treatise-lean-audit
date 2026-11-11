/-
# others/gt12/interval_decision.lean — (56.1) の区間の上の投資決定: 内側・沈黙・慣習・血気

**これは Keynes の式ではなく、Keynes の (56.1) の区間の上に報告者が置いた決定モデルである。**
帰属: 区間の読み Brady (2004)、α 規準 Hurwicz (1951)、血気 = 幅しか持たない確率の下の衝動
新井 (2015)。『確率論』の印刷行ではないので docs/全数台帳 に対応する行は無く、判定数
(check_all の [3]) にも数えない。『一般理論』第 12 章の本文は公理化も引用もしない。
骨格は phases/keynes_part_ii_phase16a_boole_challenge (th_17_56_*) と
others/boole/compare_keynes_56 (B46・B47) の定理に載せる。

## 設定
  (56) の data: a₁/h = c₁, a₂/h = c₂, e/a₁h = p₁, e/a₂h = p₂, e/ā₁ā₂h = 0, Cons h (DataI)。
  u := e/h。L := max(c₁p₁, c₂p₂)、U := min(c₁p₁ + c₂p₂, 1 − c₁(1 − p₁), 1 − c₂(1 − p₂))
  ((56.1) の区間、th_17_56_1_i の結論の形と同じ並び)。
  投資の規準: 必要確率 k (供給価格 ÷ 見込み収益)。Invest u k := k ≤ u。
  模型の側では data を DataS、公理 13 本を Boole.SysK (compare_keynes_56) で書く。

## 定理名と依頼の項目の対応 (依存公理の欄: K = KeynesI の公理と Lean 標準の公理のみ、
## 模 = Lean 標準の公理のみ (模型・算術)、B = Boole.ax_* を含む)
  | 項目 | 定理 | 依存 |
  |---|---|---|
  | 1 内側 | interval_i, invest_of_le_L, not_invest_of_U_lt, L_le_U_of_data | K |
  | 2 沈黙 | silence, silence_half, endpoints_realized | 模 |
  | 3 慣習 (定義) | Convention, convention_decides | K |
  | 3(a) Boole の理想的条件 | conv_boole_value, conv_boole (i), conv_boole_consistent (ii), conv_boole_not_forced (iii) | K / 模 / 模 |
  | 3(a) data 版 | conv_boole_data | **B** (これだけ) |
  | 3(b) 排反 ea₁a₂/h = 0 | excl_of_disjoint, conv_excl_value, conv_excl (i), conv_excl_consistent (ii), conv_excl_not_forced (iii) | K / K / K / 模 / 模 |
  | 3(c) 独立 + e/a₁a₂h = w | conv_indep_value, conv_indep (i), conv_indep_consistent (ii), conv_indep_not_forced (iii) | K / K / 模 / 模 |
  | 3 慣習を替えると u が飛ぶ | conventions_disagree, conventions_flip_decision | K |
  | 4(i) 区間内・単調 | blood_in_interval, blood_mono, blood_in_interval_i | 模 / 模 / K |
  | 4(ii) 閾値の式 | blood_threshold | 模 |
  | 4(iii) data 不変で反転 | blood_flip, blood_flip_exists | 模 |
  | 4(iv) α は定まらない | alpha_unique, alpha_not_determined | 模 |
  | 5 数値例 | half_L, half_U, boole_half_solution, boole_half_unique, boole_half_value, half_excl_value, half_indep_value, half_threshold, half_blood_mid, boole_half_alpha, boole_half_invest | 模 (boole_half_value・half_excl_value・half_indep_value は K) |
  § 8 の run_cmd が上の依存の区別を検査し、外れればコンパイルが落ちる。

## 読み
  1 内側: k ⩽ L なら公理と data から Invest、U < k なら ¬Invest (KeynesI の定理なので、
    公理 13 本と data を満たすどの模型でも成り立つ)。
  2 沈黙: L < k ⩽ U では、公理 13 本と data を満たす模型が Invest と ¬Invest の両方を与える
    (c = p = 1/2 で u = 1/4 = L の模型と u = 1/2 = U の模型; B47 undetermined)。
  3 慣習: data に足すと u を一意に定める前提。三つの実例 (Boole の理想的条件、排反、独立 + 値)
    は、どれも無矛盾 (模型あり) で、公理と data からは出ず (偽の模型あり)、同じ data
    c = p = 1/2 に u = (3 − √2)/4, 1/2, 1/4 という違う値を与える。k = 3/8 では排反と Boole の
    慣習で Invest、独立 (w = 1) の慣習で ¬Invest。
  4 血気: u_α := L + α(U − L)。data を固定したまま α だけで決定が反転し、α は data と公理からは
    定まらない (u = L の模型は α = 0、u = U の模型は α = 1)。上の三つの慣習は α の特定の値
    (c = p = 1/2 で Boole 2 − √2、排反 1、独立 0) に当たる。

## 未達・限界
  区間の両端の実現 (u = L の模型と u = U の模型) は c = p = 1/2 の data でだけ示した
  (一般の data での両端の実現は 4 世界の模型では足りず、未達)。Boole の慣習の無矛盾性の模型は
  B47 boole_model (data 1/3, 1/3, 1, 1) で、c = p = 1/2 の data で理想的条件を満たす模型は
  置いていない (根 (3 − √2)/4 が無理数なので有理の重みの有限模型には無い)。
  Boole の慣習の一意性は U < 1 の範囲 (Boole.solution_unique の u < 1 から)。

## 実行方法
  check_all は phase16a、boole_1854、compare_keynes_56 を -R . -o で一時ディレクトリに olean にし、
  LEAN_PATH に足してから lake env lean で本ファイルを検査する。
-/

import phases.keynes_part_ii_phase16a_boole_challenge
import others.boole.compare_keynes_56

namespace GT12

open KeynesI KeynesI.NoX

/-! ## § 1 設定: data・区間・投資の規準 -/

/-- (56) の data (KeynesI 担体): Cons h、a₁/h = c₁, a₂/h = c₂, e/a₁h = p₁, e/a₂h = p₂、
e/ā₁ā₂h = 0。 -/
structure DataI (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ : ℝ) : Prop where
  cons : Cons h
  hc₁ : PrI a₁ h = c₁
  hc₂ : PrI a₂ h = c₂
  hp₁ : PrI e (iand a₁ h) = p₁
  hp₂ : PrI e (iand a₂ h) = p₂
  hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0

/-- (56.1) の区間の下端 L = max(c₁p₁, c₂p₂)。 -/
noncomputable def L (c₁ c₂ p₁ p₂ : ℝ) : ℝ := max (c₁ * p₁) (c₂ * p₂)

/-- (56.1) の区間の上端 U = min(c₁p₁ + c₂p₂, 1 − c₁(1 − p₁), 1 − c₂(1 − p₂))
(th_17_56_1_i の結論と同じ並び)。 -/
noncomputable def U (c₁ c₂ p₁ p₂ : ℝ) : ℝ :=
  min (c₁ * p₁ + c₂ * p₂) (min (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂)))

/-- 投資の規準: 必要確率 k (供給価格 ÷ 見込み収益) に対し、u が k 以上なら投資する。 -/
def Invest (u k : ℝ) : Prop := k ≤ u

/-- (56) の data (模型の側): 場 S の上で DataI と同じ 6 条件。 -/
def DataS (S : Ops) (a₁ a₂ e h : S.P) (c₁ c₂ p₁ p₂ : ℝ) : Prop :=
  S.cons h ∧ S.pr a₁ h = c₁ ∧ S.pr a₂ h = c₂ ∧ S.pr e (S.and_ a₁ h) = p₁
    ∧ S.pr e (S.and_ a₂ h) = p₂ ∧ S.pr e (S.and_ (S.and_ (S.not_ a₁) (S.not_ a₂)) h) = 0

/-! ## § 2 内側 (計算できる): 項目 1 -/

/-- **(56.1) の区間** (th_17_56_1_i): data の下で L ⩽ u ⩽ U。 -/
theorem interval_i {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ : ℝ} (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) :
    L c₁ c₂ p₁ p₂ ≤ PrI e h ∧ PrI e h ≤ U c₁ c₂ p₁ p₂ :=
  th_17_56_1_i a₁ a₂ e h c₁ c₂ p₁ p₂ _ hd.cons hd.hc₁ hd.hc₂ hd.hp₁ hd.hp₂ rfl hd.hexh

/-- data があれば区間は空でない (L ⩽ U)。 -/
theorem L_le_U_of_data {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ : ℝ}
    (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) : L c₁ c₂ p₁ p₂ ≤ U c₁ c₂ p₁ p₂ :=
  (interval_i hd).1.trans (interval_i hd).2

/-- **内側その 1**: k ⩽ L なら公理と data から Invest。 -/
theorem invest_of_le_L {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ k : ℝ}
    (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) (hk : k ≤ L c₁ c₂ p₁ p₂) : Invest (PrI e h) k :=
  hk.trans (interval_i hd).1

/-- **内側その 2**: U < k なら公理と data から ¬Invest。 -/
theorem not_invest_of_U_lt {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ k : ℝ}
    (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) (hk : U c₁ c₂ p₁ p₂ < k) : ¬ Invest (PrI e h) k :=
  fun hi => absurd (hi.trans (interval_i hd).2) (not_le.mpr hk)

/-! ## § 3 沈黙 (論理は決めない): 項目 2

B47 の模型 MU (4 世界、一様な重み; 公理 13 本を満たす sysK_MU) の中の二つの組:
模型 1 (排反) a₁ = {0, 1}, a₂ = {2, 3}, e = {0, 2} で u = 1/2、
模型 2 (独立) a₁ = {0, 1}, a₂ = {0, 2}, e = {0} で u = 1/4。data はどちらも c = p = 1/2。 -/

/-- c = p = 1/2 で L = 1/4。 -/
theorem half_L : L (1/2) (1/2) (1/2) (1/2) = 1/4 := by
  unfold L; norm_num

/-- c = p = 1/2 で U = 1/2。 -/
theorem half_U : U (1/2) (1/2) (1/2) (1/2) = 1/2 := by
  unfold U; norm_num

/-- 模型 1 (排反) は c = p = 1/2 の data を満たす。 -/
theorem data_m1 : DataS Boole.MU a₁ₘ a₂ₘ eₘ mtrue (1/2) (1/2) (1/2) (1/2) :=
  ⟨model_cons_tru, Boole.ex_c₁, Boole.ex_c₂, Boole.ex_p₁, Boole.ex_p₂, Boole.ex_exh⟩

/-- 模型 2 (独立) は c = p = 1/2 の data を満たす。 -/
theorem data_m2 : DataS Boole.MU a₁ₘ Boole.a₂ᵢ Boole.eᵢ mtrue (1/2) (1/2) (1/2) (1/2) :=
  ⟨model_cons_tru, Boole.in_c₁, Boole.in_c₂, Boole.in_p₁, Boole.in_p₂, Boole.in_exh⟩

/-- 模型 1 の u = 1/2。 -/
theorem u_m1 : Boole.MU.pr eₘ mtrue = 1/2 := Boole.ex_u

/-- 模型 2 の u = 1/4。 -/
theorem u_m2 : Boole.MU.pr Boole.eᵢ mtrue = 1/4 := Boole.in_u

/-- **区間の両端が実現する**: 公理 13 本を満たす模型 MU で、c = p = 1/2 の data の下に
u = L (模型 2) と u = U (模型 1) がある。 -/
theorem endpoints_realized :
    Boole.SysK Boole.MU
    ∧ DataS Boole.MU a₁ₘ Boole.a₂ᵢ Boole.eᵢ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ Boole.MU.pr Boole.eᵢ mtrue = L (1/2) (1/2) (1/2) (1/2)
    ∧ DataS Boole.MU a₁ₘ a₂ₘ eₘ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ Boole.MU.pr eₘ mtrue = U (1/2) (1/2) (1/2) (1/2) := by
  refine ⟨Boole.sysK_MU, data_m2, ?_, data_m1, ?_⟩
  · rw [u_m2, half_L]
  · rw [u_m1, half_U]

/-- **沈黙 (c = p = 1/2)**: L < k ⩽ U のどの k でも、公理 13 本と data を満たす模型 1 で Invest、
模型 2 で ¬Invest。 -/
theorem silence_half (k : ℝ) (hL : L (1/2) (1/2) (1/2) (1/2) < k)
    (hU : k ≤ U (1/2) (1/2) (1/2) (1/2)) :
    Invest (Boole.MU.pr eₘ mtrue) k ∧ ¬ Invest (Boole.MU.pr Boole.eᵢ mtrue) k := by
  rw [half_L] at hL
  rw [half_U] at hU
  unfold Invest
  rw [u_m1, u_m2]
  exact ⟨hU, not_le.mpr hL⟩

/-- **沈黙**: L < k ⩽ U となる data と k があり、公理 13 本と data を満たす模型が二つあって、
一方で Invest、他方で ¬Invest (c = p = 1/2, k = 3/8)。 -/
theorem silence :
    ∃ c₁ c₂ p₁ p₂ k : ℝ, L c₁ c₂ p₁ p₂ < k ∧ k ≤ U c₁ c₂ p₁ p₂
      ∧ ∃ (S : Ops) (a₁ a₂ e h a₁' a₂' e' h' : S.P), Boole.SysK S
        ∧ DataS S a₁ a₂ e h c₁ c₂ p₁ p₂ ∧ DataS S a₁' a₂' e' h' c₁ c₂ p₁ p₂
        ∧ Invest (S.pr e h) k ∧ ¬ Invest (S.pr e' h') k := by
  have hL : L (1/2) (1/2) (1/2) (1/2) < 3/8 := by rw [half_L]; norm_num
  have hU : (3/8 : ℝ) ≤ U (1/2) (1/2) (1/2) (1/2) := by rw [half_U]; norm_num
  exact ⟨1/2, 1/2, 1/2, 1/2, 3/8, hL, hU, Boole.MU, a₁ₘ, a₂ₘ, eₘ, mtrue,
    a₁ₘ, Boole.a₂ᵢ, Boole.eᵢ, mtrue, Boole.sysK_MU, data_m1, data_m2, silence_half _ hL hU⟩

/-! ## § 4 慣習 = 一点化する追加前提: 項目 3 -/

/-- **慣習** (定義域 D): 前提 C を data に足すと u が一意に定まる、すなわち data の値が同じで
D を満たす二つの組がともに C を満たせば、u = e/h は等しい。 -/
def Convention (D : ℝ → ℝ → ℝ → ℝ → Prop) (C : IProp → IProp → IProp → IProp → Prop) : Prop :=
  ∀ (a₁ a₂ e h a₁' a₂' e' h' : IProp) (c₁ c₂ p₁ p₂ : ℝ), D c₁ c₂ p₁ p₂ →
    DataI a₁ a₂ e h c₁ c₂ p₁ p₂ → DataI a₁' a₂' e' h' c₁ c₂ p₁ p₂ →
    C a₁ a₂ e h → C a₁' a₂' e' h' → PrI e h = PrI e' h'

/-- 慣習の下では決定が一意: 同じ data と同じ慣習の二つの組は、どの k でも同じ決定を与える。 -/
theorem convention_decides {D : ℝ → ℝ → ℝ → ℝ → Prop} {C : IProp → IProp → IProp → IProp → Prop}
    (hC : Convention D C) {a₁ a₂ e h a₁' a₂' e' h' : IProp} {c₁ c₂ p₁ p₂ : ℝ}
    (hD : D c₁ c₂ p₁ p₂) (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) (hd' : DataI a₁' a₂' e' h' c₁ c₂ p₁ p₂)
    (hc : C a₁ a₂ e h) (hc' : C a₁' a₂' e' h') (k : ℝ) :
    Invest (PrI e h) k ↔ Invest (PrI e' h') k := by
  rw [hC a₁ a₂ e h a₁' a₂' e' h' c₁ c₂ p₁ p₂ hD hd hd' hc hc']

/-! ### (a) Boole の理想的条件 (B47 solution_of_ideal・solution_unique) -/

/-- 慣習 (a) の前提: Boole の理想的条件 (compare_keynes_56 の IdealI)。 -/
def CBoole (a₁ a₂ e h : IProp) : Prop := Boole.IdealI a₁ a₂ e h

/-- 慣習 (a) の定義域: 区間の上端が 1 未満 (Boole.solution_unique の u < 1 を出すため)。 -/
def DBoole (c₁ c₂ p₁ p₂ : ℝ) : Prop := U c₁ c₂ p₁ p₂ < 1

/-- data と理想的条件の下で u は data の Boole の解 (solution_of_ideal)。 -/
theorem conv_boole_value {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ : ℝ}
    (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) (hc : CBoole a₁ a₂ e h) :
    Boole.solution c₁ c₂ p₁ p₂ (PrI e h) := by
  have s := Boole.solution_of_ideal a₁ a₂ e h hd.cons hd.hexh hc
  rwa [hd.hc₁, hd.hc₂, hd.hp₁, hd.hp₂] at s

/-- c₁(1 − p₁) ⩾ 0 (範囲公理から; solution_unique の前提)。 -/
theorem m₁_nonneg {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ : ℝ} (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) :
    0 ≤ c₁ * (1 - p₁) := by
  have h0 := ax_range_lo_i a₁ h
  have h1 := ax_range_hi_i e (iand a₁ h)
  rw [hd.hc₁] at h0
  rw [hd.hp₁] at h1
  exact mul_nonneg h0 (by linarith)

/-- **慣習 (a) (i)**: Boole の理想的条件は (U < 1 の範囲で) 慣習 — u を一意に定める
(solution_of_ideal と Boole.solution_unique)。 -/
theorem conv_boole : Convention DBoole CBoole := by
  intro a₁ a₂ e h a₁' a₂' e' h' c₁ c₂ p₁ p₂ hD hd hd' hc hc'
  have s := conv_boole_value hd hc
  have s' := conv_boole_value hd' hc'
  exact Boole.solution_unique c₁ c₂ p₁ p₂ _ _ (m₁_nonneg hd) s s'
    (lt_of_le_of_lt (interval_i hd).2 hD) (lt_of_le_of_lt (interval_i hd').2 hD)

/-- **慣習 (a) の data 版**: 名前付きの data Boole.A₁ … Boole.H と公理 Boole.ax_* の上で、E/H は
Boole の解で、U < 1 なら解はそれだけ。#print axioms に Boole.ax_* が出る (本ファイルでこれだけ)。 -/
theorem conv_boole_data :
    Boole.solution (PrI Boole.A₁ Boole.H) (PrI Boole.A₂ Boole.H) (PrI Boole.E (iand Boole.A₁ Boole.H))
      (PrI Boole.E (iand Boole.A₂ Boole.H)) (PrI Boole.E Boole.H)
    ∧ (DBoole (PrI Boole.A₁ Boole.H) (PrI Boole.A₂ Boole.H) (PrI Boole.E (iand Boole.A₁ Boole.H))
          (PrI Boole.E (iand Boole.A₂ Boole.H)) →
        ∀ v, Boole.solution (PrI Boole.A₁ Boole.H) (PrI Boole.A₂ Boole.H)
          (PrI Boole.E (iand Boole.A₁ Boole.H)) (PrI Boole.E (iand Boole.A₂ Boole.H)) v →
          v < 1 → PrI Boole.E Boole.H = v) := by
  have hd : DataI Boole.A₁ Boole.A₂ Boole.E Boole.H _ _ _ _ :=
    ⟨Boole.ax_data_cons, rfl, rfl, rfl, rfl, Boole.ax_exh⟩
  refine ⟨Boole.solution_data, fun hD v hv hv1 => ?_⟩
  exact Boole.solution_unique _ _ _ _ _ _ (m₁_nonneg hd) Boole.solution_data hv
    (lt_of_le_of_lt (interval_i hd).2 hD) hv1

/-- 場 S の上の data の Boole の解 (模型の側の値)。 -/
def SolS (S : Ops) (a₁ a₂ e h : S.P) : Prop :=
  Boole.solution (S.pr a₁ h) (S.pr a₂ h) (S.pr e (S.and_ a₁ h)) (S.pr e (S.and_ a₂ h)) (S.pr e h)

/-- **慣習 (a) (ii) 無矛盾**: 公理 13 本を満たす模型 MB (B47 boole_model) で、data
(1/3, 1/3, 1, 1) と理想的条件が成り立ち、u = 5/9 は Boole の解。 -/
theorem conv_boole_consistent :
    Boole.SysK Boole.MB
    ∧ DataS Boole.MB a₁ₘ Boole.a₂ᵢ Boole.eB mtrue (1/3) (1/3) 1 1
    ∧ Boole.IdealS Boole.MB a₁ₘ Boole.a₂ᵢ Boole.eB mtrue
    ∧ Boole.MB.pr Boole.eB mtrue = 5/9 ∧ SolS Boole.MB a₁ₘ Boole.a₂ᵢ Boole.eB mtrue := by
  obtain ⟨h1, h2, h3, h4⟩ := Boole.boole_model
  exact ⟨h1, ⟨model_cons_tru, Boole.bm_c₁, Boole.bm_c₂, Boole.bm_p₁, Boole.bm_p₂, h3⟩, h2,
    Boole.bm_u, h4⟩

/-- **慣習 (a) (iii) 公理と data からは出ない**: 公理 13 本を満たす模型 MU の模型 1 で、data
(c = p = 1/2) が成り立つのに理想的条件は偽 (B47 boole_needs_premiss)。 -/
theorem conv_boole_not_forced :
    Boole.SysK Boole.MU ∧ DataS Boole.MU a₁ₘ a₂ₘ eₘ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ ¬ Boole.IdealS Boole.MU a₁ₘ a₂ₘ eₘ mtrue :=
  ⟨Boole.sysK_MU, data_m1, Boole.boole_needs_premiss.2.2⟩

/-! ### (b) 原因の排反 ea₁a₂/h = 0 (ch17-004 の値) -/

/-- 慣習 (b) の前提: ea₁a₂/h = 0 (Keynes の y = 0)。 -/
def CExcl (a₁ a₂ e h : IProp) : Prop := PrI (iand e (iand a₁ a₂)) h = 0

/-- ch17-004 の前提 a₁a₂/h = 0 は慣習 (b) の前提 ea₁a₂/h = 0 を与える (Def. X 左形)。 -/
theorem excl_of_disjoint (a₁ a₂ e h : IProp) (hx : PrI (iand a₁ a₂) h = 0) : CExcl a₁ a₂ e h := by
  unfold CExcl
  rw [def_X_left_i, hx, mul_zero]

/-- data と排反の下で u = c₁p₁ + c₂p₂ (th_17_56_l022_i で y = 0)。 -/
theorem conv_excl_value {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ : ℝ}
    (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) (hc : CExcl a₁ a₂ e h) :
    PrI e h = c₁ * p₁ + c₂ * p₂ := by
  have := th_17_56_l022_i a₁ a₂ e h c₁ c₂ p₁ p₂ _ _ hd.cons hd.hc₁ hd.hc₂ hd.hp₁ hd.hp₂ rfl hc
    hd.hexh
  linarith

/-- **慣習 (b) (i)**: 排反は慣習 (定義域の制限なし)。 -/
theorem conv_excl : Convention (fun _ _ _ _ => True) CExcl := by
  intro a₁ a₂ e h a₁' a₂' e' h' c₁ c₂ p₁ p₂ _ hd hd' hc hc'
  rw [conv_excl_value hd hc, conv_excl_value hd' hc']

/-- 模型 1 で ea₁a₂/h = 0。 -/
theorem excl_m1 : Boole.MU.pr (Boole.MU.and_ eₘ (Boole.MU.and_ a₁ₘ a₂ₘ)) mtrue = 0 := by
  change prw (fun _ => Boole.ωU) (mand eₘ (mand a₁ₘ a₂ₘ)) mtrue = 0
  rw [Boole.prwU _ _ (by decide), show (mand eₘ (mand a₁ₘ a₂ₘ) ∩ mtrue).card = 0 by decide]
  norm_num

/-- 模型 2 で ea₁a₂/h = 1/4。 -/
theorem excl_m2 :
    Boole.MU.pr (Boole.MU.and_ Boole.eᵢ (Boole.MU.and_ a₁ₘ Boole.a₂ᵢ)) mtrue = 1/4 := by
  change prw (fun _ => Boole.ωU) (mand Boole.eᵢ (mand a₁ₘ Boole.a₂ᵢ)) mtrue = 1/4
  rw [Boole.prwU _ _ (by decide), show (mand Boole.eᵢ (mand a₁ₘ Boole.a₂ᵢ) ∩ mtrue).card = 1 by decide,
    show (mtrue : M).card = 4 by decide]
  norm_num

/-- **慣習 (b) (ii) 無矛盾**: 模型 1 は公理 13 本・data (c = p = 1/2)・排反を満たし、u = 1/2。 -/
theorem conv_excl_consistent :
    Boole.SysK Boole.MU ∧ DataS Boole.MU a₁ₘ a₂ₘ eₘ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ Boole.MU.pr (Boole.MU.and_ eₘ (Boole.MU.and_ a₁ₘ a₂ₘ)) mtrue = 0
    ∧ Boole.MU.pr eₘ mtrue = 1/2 :=
  ⟨Boole.sysK_MU, data_m1, excl_m1, u_m1⟩

/-- **慣習 (b) (iii) 公理と data からは出ない**: 模型 2 は公理 13 本と data (c = p = 1/2) を
満たすが ea₁a₂/h = 1/4 ≠ 0。 -/
theorem conv_excl_not_forced :
    Boole.SysK Boole.MU ∧ DataS Boole.MU a₁ₘ Boole.a₂ᵢ Boole.eᵢ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ Boole.MU.pr (Boole.MU.and_ Boole.eᵢ (Boole.MU.and_ a₁ₘ Boole.a₂ᵢ)) mtrue ≠ 0 :=
  ⟨Boole.sysK_MU, data_m2, by rw [excl_m2]; norm_num⟩

/-! ### (c) 原因の独立 ((56.5) の前提) と e/a₁a₂h の値 -/

/-- 慣習 (c) の前提 (値 w): a₁/a₂h = a₁/h ((56.5) の前提) かつ e/a₁a₂h = w。 -/
def CIndep (w : ℝ) (a₁ a₂ e h : IProp) : Prop :=
  PrI a₁ (iand a₂ h) = PrI a₁ h ∧ PrI e (iand (iand a₁ a₂) h) = w

/-- data と独立 + 値 w の下で u = c₁p₁ + c₂p₂ − c₁c₂w (th_17_56_l036_i)。 -/
theorem conv_indep_value {w : ℝ} {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ : ℝ}
    (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) (hc : CIndep w a₁ a₂ e h) :
    PrI e h = c₁ * p₁ + c₂ * p₂ - c₁ * c₂ * w := by
  have := th_17_56_l036_i a₁ a₂ e h c₁ c₂ p₁ p₂ _ hd.cons hd.hc₁ hd.hc₂ hd.hp₁ hd.hp₂ rfl
    hd.hexh hc.1
  rw [this, hc.2]

/-- **慣習 (c) (i)**: 独立 + 値 w は慣習 (定義域の制限なし)。 -/
theorem conv_indep (w : ℝ) : Convention (fun _ _ _ _ => True) (CIndep w) := by
  intro a₁ a₂ e h a₁' a₂' e' h' c₁ c₂ p₁ p₂ _ hd hd' hc hc'
  rw [conv_indep_value hd hc, conv_indep_value hd' hc']

/-- 模型 2 で e/a₁a₂h = 1。 -/
theorem indep_val_m2 :
    Boole.MU.pr Boole.eᵢ (Boole.MU.and_ (Boole.MU.and_ a₁ₘ Boole.a₂ᵢ) mtrue) = 1 := by
  change prw (fun _ => Boole.ωU) Boole.eᵢ (mand (mand a₁ₘ Boole.a₂ᵢ) mtrue) = 1
  rw [Boole.prwU _ _ (by decide), show (Boole.eᵢ ∩ mand (mand a₁ₘ Boole.a₂ᵢ) mtrue).card = 1 by decide,
    show (mand (mand a₁ₘ Boole.a₂ᵢ) mtrue).card = 1 by decide]
  norm_num

/-- 模型 1 で a₁/a₂h = 0 ≠ 1/2 = a₁/h (原因は独立でない)。 -/
theorem not_indep_m1 :
    Boole.MU.pr a₁ₘ (Boole.MU.and_ a₂ₘ mtrue) ≠ Boole.MU.pr a₁ₘ mtrue := by
  change prw (fun _ => Boole.ωU) a₁ₘ (mand a₂ₘ mtrue) ≠ prw (fun _ => Boole.ωU) a₁ₘ mtrue
  rw [Boole.ex_c₁, Boole.prwU _ _ (by decide), show (a₁ₘ ∩ mand a₂ₘ mtrue).card = 0 by decide]
  norm_num

/-- **慣習 (c) (ii) 無矛盾**: 模型 2 は公理 13 本・data (c = p = 1/2)・独立・e/a₁a₂h = 1 を
満たし、u = 1/4。 -/
theorem conv_indep_consistent :
    Boole.SysK Boole.MU ∧ DataS Boole.MU a₁ₘ Boole.a₂ᵢ Boole.eᵢ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ Boole.MU.pr a₁ₘ (Boole.MU.and_ Boole.a₂ᵢ mtrue) = Boole.MU.pr a₁ₘ mtrue
    ∧ Boole.MU.pr Boole.eᵢ (Boole.MU.and_ (Boole.MU.and_ a₁ₘ Boole.a₂ᵢ) mtrue) = 1
    ∧ Boole.MU.pr Boole.eᵢ mtrue = 1/4 :=
  ⟨Boole.sysK_MU, data_m2, Boole.in_indep, indep_val_m2, u_m2⟩

/-- **慣習 (c) (iii) 公理と data からは出ない**: 模型 1 は公理 13 本と data (c = p = 1/2) を
満たすが、原因の独立が偽。 -/
theorem conv_indep_not_forced :
    Boole.SysK Boole.MU ∧ DataS Boole.MU a₁ₘ a₂ₘ eₘ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ Boole.MU.pr a₁ₘ (Boole.MU.and_ a₂ₘ mtrue) ≠ Boole.MU.pr a₁ₘ mtrue :=
  ⟨Boole.sysK_MU, data_m1, not_indep_m1⟩

/-! ### 慣習を替えると評価が飛ぶ (c = p = 1/2) -/

/-- c = p = 1/2 の Boole の根 (3 − √2)/4 (分母を払った方程式は 16u² − 24u + 7 = 0 と同値)。 -/
theorem boole_half_solution :
    Boole.solution (1/2) (1/2) (1/2) (1/2) ((3 - √2) / 4) := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have h1 : 1 ≤ √2 := by nlinarith
  have h2 : √2 ≤ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · unfold Boole.Root Boole.F
    linear_combination (1/32 : ℝ) * hs
  · unfold Boole.Limits
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- c = p = 1/2 の Boole の解はただ一つで (3 − √2)/4。 -/
theorem boole_half_unique (v : ℝ) (hv : Boole.solution (1/2) (1/2) (1/2) (1/2) v) :
    v = (3 - √2) / 4 := by
  have hv1 : v < 1 := by obtain ⟨-, -, -, -, -, h5⟩ := hv; linarith
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  exact Boole.solution_unique _ _ _ _ _ _ (by norm_num) hv boole_half_solution hv1 (by linarith)

/-- c = p = 1/2 の data と Boole の理想的条件の下で u = (3 − √2)/4。 -/
theorem boole_half_value {a₁ a₂ e h : IProp} (hd : DataI a₁ a₂ e h (1/2) (1/2) (1/2) (1/2))
    (hc : CBoole a₁ a₂ e h) : PrI e h = (3 - √2) / 4 :=
  boole_half_unique _ (conv_boole_value hd hc)

/-- c = p = 1/2 の data と排反の下で u = 1/2。 -/
theorem half_excl_value {a₁ a₂ e h : IProp} (hd : DataI a₁ a₂ e h (1/2) (1/2) (1/2) (1/2))
    (hc : CExcl a₁ a₂ e h) : PrI e h = 1/2 := by
  rw [conv_excl_value hd hc]; norm_num

/-- c = p = 1/2 の data と独立 + e/a₁a₂h = 1 の下で u = 1/4。 -/
theorem half_indep_value {a₁ a₂ e h : IProp} (hd : DataI a₁ a₂ e h (1/2) (1/2) (1/2) (1/2))
    (hc : CIndep 1 a₁ a₂ e h) : PrI e h = 1/4 := by
  rw [conv_indep_value hd hc]; norm_num

/-- **三つの慣習は同じ data に違う u を与える**: c = p = 1/2 の data で、Boole の理想的条件の組は
u = (3 − √2)/4、排反の組は u = 1/2、独立 + e/a₁a₂h = 1 の組は u = 1/4 で、三つは互いに異なる。 -/
theorem conventions_disagree {a₁ a₂ e h a₁' a₂' e' h' a₁'' a₂'' e'' h'' : IProp}
    (hd : DataI a₁ a₂ e h (1/2) (1/2) (1/2) (1/2))
    (hd' : DataI a₁' a₂' e' h' (1/2) (1/2) (1/2) (1/2))
    (hd'' : DataI a₁'' a₂'' e'' h'' (1/2) (1/2) (1/2) (1/2))
    (hb : CBoole a₁ a₂ e h) (hx : CExcl a₁' a₂' e' h') (hi : CIndep 1 a₁'' a₂'' e'' h'') :
    PrI e h = (3 - √2) / 4 ∧ PrI e' h' = 1/2 ∧ PrI e'' h'' = 1/4
      ∧ PrI e h ≠ PrI e' h' ∧ PrI e h ≠ PrI e'' h'' ∧ PrI e' h' ≠ PrI e'' h'' := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have h1 : 1 < √2 := by nlinarith
  have h2 : √2 < 2 := by nlinarith
  rw [boole_half_value hd hb, half_excl_value hd' hx, half_indep_value hd'' hi]
  refine ⟨rfl, rfl, rfl, ?_, ?_, by norm_num⟩
  · intro H; linarith
  · intro H; linarith

/-- **慣習を替えると決定が反転する**: c = p = 1/2、k = 3/8 で、排反と Boole の慣習の組は Invest、
独立 + e/a₁a₂h = 1 の慣習の組は ¬Invest。 -/
theorem conventions_flip_decision {a₁ a₂ e h a₁' a₂' e' h' a₁'' a₂'' e'' h'' : IProp}
    (hd : DataI a₁ a₂ e h (1/2) (1/2) (1/2) (1/2))
    (hd' : DataI a₁' a₂' e' h' (1/2) (1/2) (1/2) (1/2))
    (hd'' : DataI a₁'' a₂'' e'' h'' (1/2) (1/2) (1/2) (1/2))
    (hb : CBoole a₁ a₂ e h) (hx : CExcl a₁' a₂' e' h') (hi : CIndep 1 a₁'' a₂'' e'' h'') :
    Invest (PrI e h) (3/8) ∧ Invest (PrI e' h') (3/8) ∧ ¬ Invest (PrI e'' h'') (3/8) := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have h2 : √2 ≤ 3/2 := by nlinarith
  unfold Invest
  rw [boole_half_value hd hb, half_excl_value hd' hx, half_indep_value hd'' hi]
  refine ⟨by linarith, by norm_num, by norm_num⟩

/-! ## § 5 血気 = 区間内の位置: 項目 4 -/

/-- 血気の位置 α での評価 u_α := L + α(U − L)。 -/
noncomputable def uα (c₁ c₂ p₁ p₂ α : ℝ) : ℝ :=
  L c₁ c₂ p₁ p₂ + α * (U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂)

/-- 投資の閾値 (k − L)/(U − L)。 -/
noncomputable def threshold (c₁ c₂ p₁ p₂ k : ℝ) : ℝ :=
  (k - L c₁ c₂ p₁ p₂) / (U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂)

/-- **4 (i) 区間内**: L ⩽ U なら、α ∈ [0, 1] の u_α は区間 [L, U] にある。 -/
theorem blood_in_interval {c₁ c₂ p₁ p₂ α : ℝ} (hLU : L c₁ c₂ p₁ p₂ ≤ U c₁ c₂ p₁ p₂)
    (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    L c₁ c₂ p₁ p₂ ≤ uα c₁ c₂ p₁ p₂ α ∧ uα c₁ c₂ p₁ p₂ α ≤ U c₁ c₂ p₁ p₂ := by
  unfold uα
  have hw : 0 ≤ U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂ := by linarith
  have k1 : 0 ≤ α * (U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂) := mul_nonneg h0 hw
  have k2 : α * (U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂) ≤ 1 * (U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂) :=
    mul_le_mul_of_nonneg_right h1 hw
  constructor <;> linarith

/-- **4 (i) 単調**: L ⩽ U なら、u_α は α について単調。 -/
theorem blood_mono {c₁ c₂ p₁ p₂ : ℝ} (hLU : L c₁ c₂ p₁ p₂ ≤ U c₁ c₂ p₁ p₂) :
    Monotone (uα c₁ c₂ p₁ p₂) := by
  intro α β hαβ
  unfold uα
  have := mul_le_mul_of_nonneg_right hαβ (show 0 ≤ U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂ by linarith)
  linarith

/-- **4 (i) を data の下で** (KeynesI): data があれば、α ∈ [0, 1] の u_α は (56.1) の区間にある。 -/
theorem blood_in_interval_i {a₁ a₂ e h : IProp} {c₁ c₂ p₁ p₂ α : ℝ}
    (hd : DataI a₁ a₂ e h c₁ c₂ p₁ p₂) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    L c₁ c₂ p₁ p₂ ≤ uα c₁ c₂ p₁ p₂ α ∧ uα c₁ c₂ p₁ p₂ α ≤ U c₁ c₂ p₁ p₂ :=
  blood_in_interval (L_le_U_of_data hd) h0 h1

/-- **4 (ii) 閾値の式**: L < k ⩽ U のとき、Invest (u_α) k ↔ α ⩾ (k − L)/(U − L)。 -/
theorem blood_threshold {c₁ c₂ p₁ p₂ k : ℝ} (hL : L c₁ c₂ p₁ p₂ < k) (hU : k ≤ U c₁ c₂ p₁ p₂)
    (α : ℝ) : Invest (uα c₁ c₂ p₁ p₂ α) k ↔ threshold c₁ c₂ p₁ p₂ k ≤ α := by
  unfold Invest uα threshold
  have hw : 0 < U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂ := by linarith
  rw [div_le_iff₀ hw]
  constructor <;> intro H <;> linarith

/-- 閾値は (0, 1] にある (L < k ⩽ U のとき)。 -/
theorem threshold_mem {c₁ c₂ p₁ p₂ k : ℝ} (hL : L c₁ c₂ p₁ p₂ < k) (hU : k ≤ U c₁ c₂ p₁ p₂) :
    0 < threshold c₁ c₂ p₁ p₂ k ∧ threshold c₁ c₂ p₁ p₂ k ≤ 1 := by
  unfold threshold
  have hw : 0 < U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂ := by linarith
  exact ⟨div_pos (by linarith) hw, (div_le_one hw).mpr (by linarith)⟩

/-- **4 (iii) data 不変で決定が反転**: L < k ⩽ U のとき、data (c, p, k) を固定したまま、
閾値以上の α では Invest、閾値未満の α' では ¬Invest。 -/
theorem blood_flip {c₁ c₂ p₁ p₂ k : ℝ} (hL : L c₁ c₂ p₁ p₂ < k) (hU : k ≤ U c₁ c₂ p₁ p₂)
    {α α' : ℝ} (hα : threshold c₁ c₂ p₁ p₂ k ≤ α) (hα' : α' < threshold c₁ c₂ p₁ p₂ k) :
    Invest (uα c₁ c₂ p₁ p₂ α) k ∧ ¬ Invest (uα c₁ c₂ p₁ p₂ α') k :=
  ⟨(blood_threshold hL hU α).mpr hα, fun H => absurd ((blood_threshold hL hU α').mp H) (not_le.mpr hα')⟩

/-- **4 (iii) の存在形**: L < k ⩽ U なら、[0, 1] の中に α' < α があり、α を α' に下げると
Invest が ¬Invest に変わる (α = 1, α' = 0)。 -/
theorem blood_flip_exists {c₁ c₂ p₁ p₂ k : ℝ} (hL : L c₁ c₂ p₁ p₂ < k) (hU : k ≤ U c₁ c₂ p₁ p₂) :
    ∃ α α' : ℝ, 0 ≤ α' ∧ α' < α ∧ α ≤ 1
      ∧ Invest (uα c₁ c₂ p₁ p₂ α) k ∧ ¬ Invest (uα c₁ c₂ p₁ p₂ α') k := by
  obtain ⟨t0, t1⟩ := threshold_mem hL hU
  exact ⟨1, 0, le_refl 0, one_pos, le_refl 1, blood_flip hL hU t1 t0⟩

/-- L < U なら u_α = u となる α はただ一つ: α = (u − L)/(U − L)。 -/
theorem alpha_unique {c₁ c₂ p₁ p₂ u : ℝ} (hLU : L c₁ c₂ p₁ p₂ < U c₁ c₂ p₁ p₂) (α : ℝ) :
    uα c₁ c₂ p₁ p₂ α = u ↔ α = (u - L c₁ c₂ p₁ p₂) / (U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂) := by
  unfold uα
  have hw : U c₁ c₂ p₁ p₂ - L c₁ c₂ p₁ p₂ ≠ 0 := by linarith
  rw [eq_div_iff hw]
  constructor <;> intro H <;> linarith

/-- **4 (iv) α は data と公理から定まらない**: 公理 13 本と同じ data (c = p = 1/2) を満たす二つの
模型で、u = 1/4 の模型 2 は α = 0 にだけ、u = 1/2 の模型 1 は α = 1 にだけ対応する。 -/
theorem alpha_not_determined :
    Boole.SysK Boole.MU
    ∧ DataS Boole.MU a₁ₘ Boole.a₂ᵢ Boole.eᵢ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ DataS Boole.MU a₁ₘ a₂ₘ eₘ mtrue (1/2) (1/2) (1/2) (1/2)
    ∧ (∀ α, uα (1/2) (1/2) (1/2) (1/2) α = Boole.MU.pr Boole.eᵢ mtrue ↔ α = 0)
    ∧ (∀ α, uα (1/2) (1/2) (1/2) (1/2) α = Boole.MU.pr eₘ mtrue ↔ α = 1) := by
  have hLU : L (1/2) (1/2) (1/2) (1/2) < U (1/2) (1/2) (1/2) (1/2) := by
    rw [half_L, half_U]; norm_num
  refine ⟨Boole.sysK_MU, data_m2, data_m1, fun α => ?_, fun α => ?_⟩
  · rw [alpha_unique hLU, u_m2, half_L, half_U]; norm_num
  · rw [alpha_unique hLU, u_m1, half_L, half_U]; norm_num

/-! ## § 6 数値例 (c₁ = c₂ = p₁ = p₂ = 1/2): 項目 5

L = 1/4 (half_L)、U = 1/2 (half_U)、Boole の根 (3 − √2)/4 ≈ 0.396 (boole_half_solution;
B47 half_solution の区間 (1/4, 1/2) に入る)、排反の慣習で u = 1/2 (half_excl_value)、
独立 + e/a₁a₂h = 1 の慣習で u = 1/4 (half_indep_value)、k = 3/8 の閾値 α = 1/2。 -/

/-- k = 3/8 の閾値は α = 1/2。 -/
theorem half_threshold : threshold (1/2) (1/2) (1/2) (1/2) (3/8) = 1/2 := by
  unfold threshold; rw [half_L, half_U]; norm_num

/-- α = 1/2 の血気の評価は u = 3/8 (閾値ちょうど)。 -/
theorem half_blood_mid : uα (1/2) (1/2) (1/2) (1/2) (1/2) = 3/8 := by
  unfold uα; rw [half_L, half_U]; norm_num

/-- Boole の根は B47 half_solution の区間 (1/4, 1/2) の内部にあり、Boole の慣習は血気の位置
α = 2 − √2 (≈ 0.586) に当たる。 -/
theorem boole_half_alpha :
    1/4 < (3 - √2) / 4 ∧ (3 - √2) / 4 < 1/2
    ∧ uα (1/2) (1/2) (1/2) (1/2) (2 - √2) = (3 - √2) / 4 := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have h1 : 1 < √2 := by nlinarith
  have h2 : √2 < 2 := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩
  unfold uα; rw [half_L, half_U]; ring

/-- Boole の慣習の評価 (3 − √2)/4 は k = 3/8 の閾値を越える (Invest)、α = 2 − √2 ⩾ 1/2。 -/
theorem boole_half_invest :
    Invest ((3 - √2) / 4) (3/8) ∧ threshold (1/2) (1/2) (1/2) (1/2) (3/8) ≤ 2 - √2 := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have h2 : √2 ≤ 3/2 := by nlinarith
  rw [half_threshold]
  unfold Invest
  constructor <;> linarith

end GT12

/-! ## § 8 依存公理の検査 (外れればコンパイルが落ちる) -/

open Lean in
/-- 定数 n の依存公理に、名前空間 ns で始まる名前があるか。 -/
def GT12.usesPrefix (ns n : Name) : CoreM Bool := do
  let axs ← collectAxioms n
  return axs.any (fun a => ns.isPrefixOf a)

open Lean in
/-- 定数 n の依存公理が Lean 標準の 3 本 (propext, Classical.choice, Quot.sound) だけか。 -/
def GT12.onlyStd (n : Name) : CoreM Bool := do
  let axs ← collectAxioms n
  return axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)

open Lean Elab Command in
run_cmd liftCoreM do
  -- K: KeynesI の公理と Lean 標準の公理のみ (Boole.ax_* を含まない)
  for n in [``GT12.interval_i, ``GT12.L_le_U_of_data, ``GT12.invest_of_le_L,
      ``GT12.not_invest_of_U_lt, ``GT12.convention_decides, ``GT12.conv_boole_value,
      ``GT12.m₁_nonneg, ``GT12.conv_boole, ``GT12.excl_of_disjoint, ``GT12.conv_excl_value,
      ``GT12.conv_excl, ``GT12.conv_indep_value, ``GT12.conv_indep, ``GT12.boole_half_value,
      ``GT12.half_excl_value, ``GT12.half_indep_value, ``GT12.conventions_disagree,
      ``GT12.conventions_flip_decision, ``GT12.blood_in_interval_i] do
    if ← GT12.usesPrefix `Boole n then
      throwError "{n} が Boole の公理に依存している"
    unless ← GT12.usesPrefix `KeynesI n do
      throwError "{n} が KeynesI の公理に依存していない (K 欄の想定と違う)"
  -- 模: Lean 標準の公理のみ (模型・算術)
  for n in [``GT12.half_L, ``GT12.half_U, ``GT12.data_m1, ``GT12.data_m2, ``GT12.u_m1,
      ``GT12.u_m2, ``GT12.endpoints_realized, ``GT12.silence_half, ``GT12.silence,
      ``GT12.conv_boole_consistent, ``GT12.conv_boole_not_forced, ``GT12.excl_m1,
      ``GT12.excl_m2, ``GT12.conv_excl_consistent, ``GT12.conv_excl_not_forced,
      ``GT12.indep_val_m2, ``GT12.not_indep_m1, ``GT12.conv_indep_consistent,
      ``GT12.conv_indep_not_forced, ``GT12.boole_half_solution, ``GT12.boole_half_unique,
      ``GT12.blood_in_interval, ``GT12.blood_mono, ``GT12.blood_threshold, ``GT12.threshold_mem,
      ``GT12.blood_flip, ``GT12.blood_flip_exists, ``GT12.alpha_unique,
      ``GT12.alpha_not_determined, ``GT12.half_threshold, ``GT12.half_blood_mid,
      ``GT12.boole_half_alpha, ``GT12.boole_half_invest] do
    unless ← GT12.onlyStd n do
      throwError "{n} が Lean 標準以外の公理に依存している"
  -- B: 3(a) の data 版だけが Boole.ax_* に依存する
  unless ← GT12.usesPrefix `Boole ``GT12.conv_boole_data do
    throwError "GT12.conv_boole_data が Boole の公理に依存していない"

/-! # 監査クエリ (判定数には数えない) -/

-- 1 内側 (K)
#print axioms GT12.interval_i
#print axioms GT12.L_le_U_of_data
#print axioms GT12.invest_of_le_L
#print axioms GT12.not_invest_of_U_lt
-- 2 沈黙 (模)
#print axioms GT12.half_L
#print axioms GT12.half_U
#print axioms GT12.data_m1
#print axioms GT12.data_m2
#print axioms GT12.endpoints_realized
#print axioms GT12.silence_half
#print axioms GT12.silence
-- 3 慣習
#print axioms GT12.convention_decides
#print axioms GT12.conv_boole_value
#print axioms GT12.m₁_nonneg
#print axioms GT12.conv_boole
#print axioms GT12.conv_boole_data
#print axioms GT12.conv_boole_consistent
#print axioms GT12.conv_boole_not_forced
#print axioms GT12.excl_of_disjoint
#print axioms GT12.conv_excl_value
#print axioms GT12.conv_excl
#print axioms GT12.excl_m1
#print axioms GT12.excl_m2
#print axioms GT12.conv_excl_consistent
#print axioms GT12.conv_excl_not_forced
#print axioms GT12.conv_indep_value
#print axioms GT12.conv_indep
#print axioms GT12.indep_val_m2
#print axioms GT12.not_indep_m1
#print axioms GT12.conv_indep_consistent
#print axioms GT12.conv_indep_not_forced
#print axioms GT12.boole_half_solution
#print axioms GT12.boole_half_unique
#print axioms GT12.boole_half_value
#print axioms GT12.half_excl_value
#print axioms GT12.half_indep_value
#print axioms GT12.conventions_disagree
#print axioms GT12.conventions_flip_decision
-- 4 血気
#print axioms GT12.blood_in_interval
#print axioms GT12.blood_mono
#print axioms GT12.blood_in_interval_i
#print axioms GT12.blood_threshold
#print axioms GT12.threshold_mem
#print axioms GT12.blood_flip
#print axioms GT12.blood_flip_exists
#print axioms GT12.alpha_unique
#print axioms GT12.alpha_not_determined
-- 5 数値例
#print axioms GT12.half_threshold
#print axioms GT12.half_blood_mid
#print axioms GT12.boole_half_alpha
#print axioms GT12.boole_half_invest
