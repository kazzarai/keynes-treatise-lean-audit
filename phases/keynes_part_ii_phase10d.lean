/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 10d
#
# **第17章 (folio 186–214): 全数台帳 ch17.md の「未」101 本の定理化**
#
# ## 対象
#   docs/全数台帳/ch17.md の式行のうち Lean 欄が「未」だった 101 本。§2 の (56)–(58) の
#   証明途中行・記号の約束、§3–§12 (1911 JRSS 論文の再録と 1921 加筆層) の代入行・中間行。
#   各定理の docstring 冒頭に台帳の行 ID (ch17-NNN) と folio を書く。定理名の `lNNN` は
#   行 ID の番号。
#
# ## 基準
#   1921 Macmillan 初版の頁画像 (img_all/folio_186–214.png、原寸 hires/) が唯一の基準。
#   folio 190 の上バーの範囲は原寸切り出しで確認した (ch17-044–050, 057–060)。
#
# ## 担体
#   第 I 部 (§2, (56)–(58)): KeynesI 担体 (IProp, PrI, Cons; phase6c と同形の公理、公理 (i)
#   の但し書き付き)。`Prop → Prop → ℝ` 型の確率関係は新設しない (CLAUDE.md 不変条件 3)。
#   Keynes の並置 (eā₁ā₂ など) は iand の入れ子で書く: 結論側は「e と否定の連言 N の連言、
#   その後ろに正の原因 aᵣ」 (iand (iand e N) aᵣ)、N = ā₁…ā_k は左入れ子 (nb)。
#   前提側の並置は Keynes の書いた順に入れ子にする (本公理系には前提側の置換が無いので、
#   Keynes が二つの順で書く前提 (ch17-078 と ch17-081) は二つの仮定として置く)。
#   第 II 部 (§3–§12): 誤差法則は phase9x と同じく実関数の上で述べる。phase9x の定理は
#   import しない (不変条件 2) ので、使う補題 (停留条件の一般形、(i)-6 の三段、
#   (ii)-9 の反駁など) は本ファイルに写して証明し直す。
#
# ## 印刷形が成り立たない行 (✎: 反例と修正形の両方を置く)
#   ch17-059, 070 (57.1)(57.4): 印刷の前提は対独立 aᵣ/a_sh = aᵣ/h。相互独立の形
#     ā₁…ā_{r−1}/aᵣh = Π(1 − c_s) を前提にすれば成り立つ (修正形)。対独立だけでは
#     成り立たない: 4 点一様の有限モデル (a₃ = a₁ と a₂ の排他的論理和) で
#     n₃ = 1/2 ≠ 3/8、e/h = 3/4 ≠ 7/8 (Erratum57)。所見候補。
#   ch17-072 (57.5): e/h = Σcᵣpᵣ は近似 (「squares and products may be neglected」)。
#     等式としては偽 (Erratum57: 3/4 ≠ 1)。修正形は 0 ≤ Σcᵣpᵣ − e/h ≤ Σ_r cᵣ Σ_{s<r} c_s。
#   ch17-098 (58.3): ε′ の指数 n は n − 1 (ch17-097 の F と同じ指数の誤り; Erratum58 と
#     同じ値 a = 1/2, p = 3/4, n = 1 で反駁)。
#   ch17-161 (ii)-9: ∫φ₁′(z)/z dz = φ(log z) は符号が逆 (phase9x ii_9 と同じ反駁を写す)。
#   ch17-212 N2: 左辺 φ(x) (右辺は z)。修正形は φ(z) の Maclaurin 級数 (解析関数)。
#   ch17-215, 216, 217 N3–N4: z⁴ を無視した近似の「=」。等式としては偽。修正形は
#     o(z³) の評価と z⁴ の差の評価。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase10d.lean
-/

import Mathlib

open Finset

/-! # 第 I 部: KeynesI 担体 — §2 の (56)–(58) -/

namespace KeynesI

/-! ## 内包的キャリアと公理 (phase6c と同形) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 `Cons h`: 「h は矛盾する連言でない」(folio 135、公理 (i))。 -/
axiom Cons : IProp → Prop

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- Def. VIII (folio 134) 双条件読み、但し書き付き (phase6c と同形)。 -/
axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- Def. VIII 印刷どおり (→ のみ; phase6c と同形)。 -/
axiom def_VIII_i_src (a b h : IProp) :
    PrI b (iand a h) = 1 → PrI a (iand b h) = 1 → PrI (iiff a b) h = 1

/-- 命題論理の構文 (phase6c と同形)。 -/
inductive Form : Type where
  | var  : ℕ → Form
  | tru  : Form
  | fls  : Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | neg  : Form → Form
  | iffF : Form → Form → Form

def evalB (v : ℕ → Bool) : Form → Bool
  | .var n    => v n
  | .tru      => true
  | .fls      => false
  | .conj f g => evalB v f && evalB v g
  | .disj f g => evalB v f || evalB v g
  | .neg f    => !(evalB v f)
  | .iffF f g => evalB v f == evalB v g

def Taut (f : Form) : Prop := ∀ v : ℕ → Bool, evalB v f = true

noncomputable def interp (env : ℕ → IProp) : Form → IProp
  | .var n    => env n
  | .tru      => itrue
  | .fls      => inot itrue
  | .conj f g => iand (interp env f) (interp env g)
  | .disj f g => ior (interp env f) (interp env g)
  | .neg f    => inot (interp env f)
  | .iffF f g => iiff (interp env f) (interp env g)

/-- Ax.(iii) 但し書き付き (phase6c と同形)。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

axiom cons_true : Cons itrue
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0
/-- a/h ≠ 0 かつ h 整合ならば ah 整合 (phase6c と同形; Def. VI の逆向き、(10) folio 140)。 -/
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## phase6c の定理の写し (補完律 (1)、Th.(12)、代入原理、加法定理 (24)) -/

theorem itrue_certain (h : IProp) (hc : Cons h) : PrI itrue h = 1 :=
  ax_iii_taut Form.tru (fun _ => itrue) h hc (fun _ => rfl)

theorem true_conj (a h : IProp) (hc : Cons h) : PrI (iand itrue a) h = PrI a h := by
  have hr := def_X_left_i itrue a h
  by_cases ha : PrI a h = 0
  · rw [ha, mul_zero] at hr
    rw [hr, ha]
  · have hca : Cons (iand a h) := cons_of_pos a h ha hc
    rw [itrue_certain (iand a h) hca, one_mul] at hr
    exact hr

/-- 第13章の式 (1) (folio 139): a/h + ā/h = 1。 -/
theorem th_13_1_i (a h : IProp) (hc : Cons h) : PrI a h + PrI (inot a) h = 1 := by
  have step := def_IX_i itrue a h
  rw [true_conj (inot a) h hc, true_conj a h hc, itrue_certain h hc] at step
  linarith

theorem taut_neg_zero (f : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.neg f)) : PrI (interp env f) h = 0 := by
  have h1 : PrI (inot (interp env f)) h = 1 := ax_iii_taut (Form.neg f) env h hc ht
  have h2 := th_13_1_i (interp env f) h hc
  linarith

theorem conj_neg_cert_zero (x E h : IProp) (hc : Cons h) (hE : PrI E h = 1) :
    PrI (iand x (inot E)) h = 0 := by
  have h1 := th_13_1_i E h hc
  have hnE : PrI (inot E) h = 0 := by linarith
  rw [def_X_left_i x (inot E) h, hnE, mul_zero]

/-- Th.(12) (folio 141) の短い証明 (phase6c th_12_i_short の写し; def_VIII_i を用いない)。 -/
theorem th_12_i_short (a b h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h := by
  have hba : PrI (iand b (inot a)) h = 0 := by
    have s := def_IX_i (iand b (inot a)) (iiff a b) h
    have z1 := conj_neg_cert_zero (iand b (inot a)) (iiff a b) h hc hcert
    have z2 : PrI (iand (iand b (inot a)) (iiff a b)) h = 0 :=
      taut_neg_zero
        (Form.conj (Form.conj (Form.var 1) (Form.neg (Form.var 0)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h hc
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  have hab : PrI (iand a (inot b)) h = 0 := by
    have s := def_IX_i (iand a (inot b)) (iiff a b) h
    have z1 := conj_neg_cert_zero (iand a (inot b)) (iiff a b) h hc hcert
    have z2 : PrI (iand (iand a (inot b)) (iiff a b)) h = 0 :=
      taut_neg_zero
        (Form.conj (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h hc
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  have e1 := def_IX_i a b h
  have e2 := def_IX_i b a h
  have e3 := def_X_left_i a b h
  have e4 := def_X_right_i b a h
  linarith

/-- 代入原理 (phase6c subst_taut の写し; th_12_i_short 経由)。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i_short _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-- Th.(24) (folio 144) 加法定理 (phase6c th_24_i の写し)。 -/
theorem th_24_i (a b h : IProp) (hc : Cons h) :
    PrI (ior a b) h = PrI a h + PrI b h - PrI (iand a b) h := by
  have step1 := def_IX_i (ior a b) b h
  have e1 : PrI (iand (ior a b) (inot b)) h = PrI (iand a (inot b)) h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.neg (Form.var 1)))
      (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
      (fun n => match n with | 0 => a | _ => b) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have e2 : PrI (iand (ior a b) b) h = PrI b h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.var 1))
      (Form.var 1)
      (fun n => match n with | 0 => a | _ => b) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have step3 := def_IX_i a b h
  linarith [step1, e1, e2, step3]

/-! ## 結論側の並置の付け替え (公理 (iii) の恒真式による代入) -/

/-- 結合: ((xy)z)/h = (x(yz))/h。 -/
theorem conj_assoc_i (x y z h : IProp) (hc : Cons h) :
    PrI (iand (iand x y) z) h = PrI (iand x (iand y z)) h :=
  subst_taut (Form.conj (Form.conj (.var 0) (.var 1)) (.var 2))
    (Form.conj (.var 0) (Form.conj (.var 1) (.var 2)))
    (fun n => match n with | 0 => x | 1 => y | _ => z) h hc
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> simp [evalB, h0, h1, h2])

/-- 交換と結合: (x(yz))/h = ((xz)y)/h。 -/
theorem conj_swap_i (x y z h : IProp) (hc : Cons h) :
    PrI (iand x (iand y z)) h = PrI (iand (iand x z) y) h :=
  subst_taut (Form.conj (.var 0) (Form.conj (.var 1) (.var 2)))
    (Form.conj (Form.conj (.var 0) (.var 2)) (.var 1))
    (fun n => match n with | 0 => x | 1 => y | _ => z) h hc
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> simp [evalB, h0, h1, h2])

/-- 二重否定: ((x ā̄) y)/h = ((x a) y)/h。 -/
theorem conj_dneg_i (x a y h : IProp) (hc : Cons h) :
    PrI (iand (iand x (inot (inot a))) y) h = PrI (iand (iand x a) y) h :=
  subst_taut (Form.conj (Form.conj (.var 0) (Form.neg (Form.neg (.var 1)))) (.var 2))
    (Form.conj (Form.conj (.var 0) (.var 1)) (.var 2))
    (fun n => match n with | 0 => x | 1 => a | _ => y) h hc
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> simp [evalB, h0, h1, h2])

/-! ## (56) (folio 187–189): 二つの原因の問題 (Boole / Wilbraham / McColl) -/

/-- (56) の生の分解 (Keynes の (a₁ + a₂)/eh = 1 と (24) の経路を、結論側の代入で書いたもの):
e/ā₁ā₂h = 0 (ch17-013) ならば e/h = ea₁/h + ea₂/h − ea₁a₂/h。以下の定理の補題。 -/
theorem th_17_56_raw_i (a₁ a₂ e h : IProp) (hc : Cons h)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    PrI e h = PrI (iand e a₁) h + PrI (iand e a₂) h - PrI (iand e (iand a₁ a₂)) h := by
  have s1 := def_IX_i e (ior a₁ a₂) h
  have e1 : PrI (iand e (inot (ior a₁ a₂))) h = PrI (iand e (iand (inot a₁) (inot a₂))) h :=
    subst_taut (Form.conj (.var 0) (Form.neg (Form.disj (.var 1) (.var 2))))
      (Form.conj (.var 0) (Form.conj (Form.neg (.var 1)) (Form.neg (.var 2))))
      (fun n => match n with | 0 => e | 1 => a₁ | _ => a₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  have z1 : PrI (iand e (iand (inot a₁) (inot a₂))) h = 0 := by
    rw [def_X_left_i, hexh, zero_mul]
  have e2 : PrI (iand e (ior a₁ a₂)) h = PrI (ior (iand e a₁) (iand e a₂)) h :=
    subst_taut (Form.conj (.var 0) (Form.disj (.var 1) (.var 2)))
      (Form.disj (Form.conj (.var 0) (.var 1)) (Form.conj (.var 0) (.var 2)))
      (fun n => match n with | 0 => e | 1 => a₁ | _ => a₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  have t24 := th_24_i (iand e a₁) (iand e a₂) h hc
  have e3 : PrI (iand (iand e a₁) (iand e a₂)) h = PrI (iand e (iand a₁ a₂)) h :=
    subst_taut (Form.conj (Form.conj (.var 0) (.var 1)) (Form.conj (.var 0) (.var 2)))
      (Form.conj (.var 0) (Form.conj (.var 1) (.var 2)))
      (fun n => match n with | 0 => e | 1 => a₁ | _ => a₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  linarith

/-- **ch17-002 (folio 187)** Boole の方程式 (引用)
[1 − c₁(1 − p₁) − u][1 − c₂(1 − p₂) − u] ÷ (1 − u) = (u − c₁p₁)(u − c₂p₂) ÷ (c₁p₁ + c₂p₂ − u)
の分母を払った形。原因が排反なときの正しい解 u = c₁p₁ + c₂p₂ (ch17-004) を代入すると、
この方程式は c₁p₁ · c₂p₂ · (1 − u) = 0 のときに限って成り立つ — Keynes の「Boole's
equations do not reduce to this」。印刷の分数形は u = c₁p₁ + c₂p₂ で右辺の分母が 0 になる。 -/
theorem th_17_56_l002 (c₁ c₂ p₁ p₂ u : ℝ) (hu : u = c₁ * p₁ + c₂ * p₂) :
    (1 - c₁ * (1 - p₁) - u) * (1 - c₂ * (1 - p₂) - u) * (c₁ * p₁ + c₂ * p₂ - u)
        = (u - c₁ * p₁) * (u - c₂ * p₂) * (1 - u)
      ↔ c₁ * p₁ * (c₂ * p₂) * (1 - u) = 0 := by
  subst hu
  constructor
  · intro hh; linear_combination -hh
  · intro hh; linear_combination -hh

/-- **ch17-004 (folio 187)** 原因が排反 (a₁a₂/h = 0) のとき u = c₁p₁ + c₂p₂。
前提は ch17-006–009, 011 の記号の約束と e/ā₁ā₂h = 0 (ch17-013)。 -/
theorem th_17_56_l004 (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0)
    (hexcl : PrI (iand a₁ a₂) h = 0) :
    u = c₁ * p₁ + c₂ * p₂ := by
  have raw := th_17_56_raw_i a₁ a₂ e h hc hexh
  have x1 := def_X_left_i e a₁ h
  have x2 := def_X_left_i e a₂ h
  have x3 := def_X_left_i e (iand a₁ a₂) h
  rw [hexcl, mul_zero] at x3
  rw [hp₁, hc₁] at x1
  rw [hp₂, hc₂] at x2
  rw [← hu]
  linarith

/-- **ch17-005 (folio 187 脚注 3)** Wilbraham の解 u = c₁p₁ + c₂p₂ − z (引用)。z を
ea₁a₂/h と同定すると成り立ち、z は c₁p₁ と c₂p₂ のどちらも超えない (印刷の「less than」は
狭義だが、ea₁a₂/h = ea₁/h となる場合があるので ≤ で述べる)。 -/
theorem th_17_56_l005 (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u z : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0)
    (hz : PrI (iand e (iand a₁ a₂)) h = z) :
    u = c₁ * p₁ + c₂ * p₂ - z ∧ z ≤ c₁ * p₁ ∧ z ≤ c₂ * p₂ := by
  have raw := th_17_56_raw_i a₁ a₂ e h hc hexh
  have x1 := def_X_left_i e a₁ h
  have x2 := def_X_left_i e a₂ h
  rw [hp₁, hc₁] at x1
  rw [hp₂, hc₂] at x2
  -- z ≤ ea₁/h: e(a₁a₂) ≡ (ea₁)a₂、Def. IX で (ea₁)ā₂/h ≥ 0 を足す
  have k1 : PrI (iand e (iand a₁ a₂)) h = PrI (iand (iand e a₁) a₂) h :=
    (conj_assoc_i e a₁ a₂ h hc).symm
  have s1 := def_IX_i (iand e a₁) a₂ h
  have l1 := ax_range_lo_i (iand (iand e a₁) (inot a₂)) h
  -- z ≤ ea₂/h: e(a₁a₂) ≡ (ea₂)a₁
  have k2 : PrI (iand e (iand a₁ a₂)) h = PrI (iand (iand e a₂) a₁) h :=
    conj_swap_i e a₁ a₂ h hc
  have s2 := def_IX_i (iand e a₂) a₁ h
  have l2 := ax_range_lo_i (iand (iand e a₂) (inot a₁)) h
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **ch17-013, 014, 015 (folio 188)** e/ā₁ā₂h = 0 (前提) ならば ā₁ā₂/eh = 0、ただし
e/h = 0 の場合を除く (「unless e/h = 0」を選言で)。Def. X の左右二形のみ。 -/
theorem th_17_56_l014 (a₁ a₂ e h : IProp)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    PrI (iand (inot a₁) (inot a₂)) (iand e h) = 0 ∨ PrI e h = 0 := by
  have l := def_X_left_i (iand (inot a₁) (inot a₂)) e h
  have r := def_X_right_i (iand (inot a₁) (inot a₂)) e h
  rw [hexh, zero_mul] at r
  rw [r] at l
  exact mul_eq_zero.mp l.symm

/-- **ch17-017 (folio 188)** (a₁ + a₂)/eh = 1 (ch17-016) から (24) で
a₁/eh + a₂/eh = 1 + a₁a₂/eh。但し書き Cons (eh) は (24) の代入原理の姿。 -/
theorem th_17_56_l017 (a₁ a₂ e h : IProp) (hc : Cons (iand e h))
    (h016 : PrI (ior a₁ a₂) (iand e h) = 1) :
    PrI a₁ (iand e h) + PrI a₂ (iand e h) = 1 + PrI (iand a₁ a₂) (iand e h) := by
  have := th_24_i a₁ a₂ (iand e h) hc
  linarith

/-- **ch17-006, 007, 008, 009, 011, 018 (folio 188)** 記号の約束 a₁/h = c₁, a₂/h = c₂,
e/a₁h = p₁, e/a₂h = p₂, e/h = u の下で a₁/eh = c₁p₁/u かつ a₂/eh = c₂p₂/u (u ≠ 0)。 -/
theorem th_17_56_l018 (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hu0 : u ≠ 0) :
    PrI a₁ (iand e h) = c₁ * p₁ / u ∧ PrI a₂ (iand e h) = c₂ * p₂ / u := by
  have l1 := def_X_left_i a₁ e h
  have r1 := def_X_right_i a₁ e h
  have l2 := def_X_left_i a₂ e h
  have r2 := def_X_right_i a₂ e h
  rw [hc₁, hp₁, hu] at *
  rw [hc₂, hp₂] at *
  constructor
  · rw [eq_div_iff hu0]; linarith
  · rw [eq_div_iff hu0]; linarith

/-- **ch17-012, 020, 021 (folio 188)** a₁a₂/eh = z, ea₁a₂/h = y (記号の約束) の下で
y = a₁a₂/eh . e/h = uz。 -/
theorem th_17_56_l021 (a₁ a₂ e h : IProp) (u z y : ℝ) (hu : PrI e h = u)
    (hz : PrI (iand a₁ a₂) (iand e h) = z) (hy : PrI (iand e (iand a₁ a₂)) h = y) :
    y = PrI (iand a₁ a₂) (iand e h) * PrI e h
      ∧ PrI (iand a₁ a₂) (iand e h) * PrI e h = u * z := by
  have r := def_X_right_i e (iand a₁ a₂) h
  refine ⟨by rw [← hy, r], by rw [hz, hu, mul_comm]⟩

/-- **ch17-023 (folio 188)** y ⩾ 0 (y = ea₁a₂/h; 範囲公理)。 -/
theorem th_17_56_l023 (a₁ a₂ e h : IProp) (y : ℝ) (hy : PrI (iand e (iand a₁ a₂)) h = y) :
    y ≥ 0 := by
  rw [← hy]; exact ax_range_lo_i _ _

/-- **ch17-025 (folio 188)** 連鎖 e/h = eā₁/h + ea₁/h ⩽ ā₁/h + ea₁/h ⩽ 1 − c₁ + c₁p₁
(by (24.2) and (4))。第 2 の ⩽ は実際には等号。 -/
theorem th_17_56_l025 (a₁ e h : IProp) (c₁ p₁ : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hp₁ : PrI e (iand a₁ h) = p₁) :
    PrI e h = PrI (iand e (inot a₁)) h + PrI (iand e a₁) h
      ∧ PrI (iand e (inot a₁)) h + PrI (iand e a₁) h ≤ PrI (inot a₁) h + PrI (iand e a₁) h
      ∧ PrI (inot a₁) h + PrI (iand e a₁) h ≤ 1 - c₁ + c₁ * p₁ := by
  have s := def_IX_i e a₁ h
  have x1 := def_X_left_i e (inot a₁) h
  have hle := ax_range_hi_i e (iand (inot a₁) h)
  have hlo := ax_range_lo_i (inot a₁) h
  have x2 := def_X_left_i e a₁ h
  have c := th_13_1_i a₁ h hc
  rw [hp₁, hc₁] at x2
  refine ⟨by linarith, ?_, ?_⟩
  · have : PrI e (iand (inot a₁) h) * PrI (inot a₁) h ≤ PrI (inot a₁) h :=
      mul_le_of_le_one_left hlo hle
    linarith
  · rw [hc₁] at c
    linarith

/-- **ch17-035 (folio 189)** (56.5) の独立 a₁/a₂h = a₁/h (ch17-034) の下で
y = ea₁a₂/h = e/a₁a₂h . a₁/a₂h . a₂/h = e/a₁a₂h . c₁c₂。 -/
theorem th_17_56_l035 (a₁ a₂ e h : IProp) (c₁ c₂ y : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hind : PrI a₁ (iand a₂ h) = PrI a₁ h) (hy : PrI (iand e (iand a₁ a₂)) h = y) :
    y = PrI (iand e (iand a₁ a₂)) h
      ∧ PrI (iand e (iand a₁ a₂)) h
          = PrI e (iand (iand a₁ a₂) h) * PrI a₁ (iand a₂ h) * PrI a₂ h
      ∧ PrI e (iand (iand a₁ a₂) h) * PrI a₁ (iand a₂ h) * PrI a₂ h
          = PrI e (iand (iand a₁ a₂) h) * (c₁ * c₂) := by
  have x1 := def_X_left_i e (iand a₁ a₂) h
  have x2 := def_X_left_i a₁ a₂ h
  refine ⟨hy.symm, by rw [x1, x2]; ring, by rw [hind, hc₁, hc₂]; ring⟩

/-- **ch17-036 (folio 189)** ∴ u = c₁p₁ + c₂p₂ − c₁c₂ . e/a₁a₂h ((56.5) の独立の下)。 -/
theorem th_17_56_l036 (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0)
    (hind : PrI a₁ (iand a₂ h) = PrI a₁ h) :
    u = c₁ * p₁ + c₂ * p₂ - c₁ * c₂ * PrI e (iand (iand a₁ a₂) h) := by
  have raw := th_17_56_raw_i a₁ a₂ e h hc hexh
  have y := (th_17_56_l035 a₁ a₂ e h c₁ c₂ _ hc₁ hc₂ hind rfl).2
  have x1 := def_X_left_i e a₁ h
  have x2 := def_X_left_i e a₂ h
  rw [hp₁, hc₁] at x1
  rw [hp₂, hc₂] at x2
  rw [← hu]
  linarith [y.1, y.2]

/-! ## (57) (folio 189–191): n 個の原因 — n = 2, 3 の具体行

並置の書き方: ā₁ā₂ = iand ā₁ ā₂、ā₁ā₂ā₃ = iand (iand ā₁ ā₂) ā₃ (左入れ子)、
eā₁ā₂ = iand e (iand ā₁ ā₂)、eā₁ā₂a₃ = iand (iand e (iand ā₁ ā₂)) a₃、
上バー ‾(ā₁ā₂) = inot (iand ā₁ ā₂) (folio 190 原寸でバーは ā₁ā₂ の上のみ)。 -/

/-- **ch17-039 (folio 189)** (57) (i.): e/h = eā₁/h + ea₁/h = eā₁/h + e/a₁h . a₁/h
= eā₁/h + c₁p₁。 -/
theorem th_17_57_l039 (a₁ e h : IProp) (c₁ p₁ : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hp₁ : PrI e (iand a₁ h) = p₁) :
    PrI e h = PrI (iand e (inot a₁)) h + PrI (iand e a₁) h
      ∧ PrI (iand e (inot a₁)) h + PrI (iand e a₁) h
          = PrI (iand e (inot a₁)) h + PrI e (iand a₁ h) * PrI a₁ h
      ∧ PrI (iand e (inot a₁)) h + PrI e (iand a₁ h) * PrI a₁ h
          = PrI (iand e (inot a₁)) h + c₁ * p₁ := by
  have s := def_IX_i e a₁ h
  have x := def_X_left_i e a₁ h
  refine ⟨by linarith, by rw [x], by rw [hc₁, hp₁, mul_comm]⟩

/-- **ch17-040 (folio 189)** eā₁/h = eā₁ā₂/h + eā₁/a₂h . a₂/h = eā₁ā₂/h + c₂ . eā₁/a₂h。 -/
theorem th_17_57_l040 (a₁ a₂ e h : IProp) (c₂ : ℝ) (hc : Cons h) (hc₂ : PrI a₂ h = c₂) :
    PrI (iand e (inot a₁)) h
        = PrI (iand e (iand (inot a₁) (inot a₂))) h
          + PrI (iand e (inot a₁)) (iand a₂ h) * PrI a₂ h
      ∧ PrI (iand e (iand (inot a₁) (inot a₂))) h
          + PrI (iand e (inot a₁)) (iand a₂ h) * PrI a₂ h
        = PrI (iand e (iand (inot a₁) (inot a₂))) h
          + c₂ * PrI (iand e (inot a₁)) (iand a₂ h) := by
  have s := def_IX_i (iand e (inot a₁)) a₂ h
  have x := def_X_left_i (iand e (inot a₁)) a₂ h
  have k := conj_assoc_i e (inot a₁) (inot a₂) h hc
  refine ⟨by linarith, by rw [hc₂, mul_comm]⟩

/-- **ch17-041 (folio 189)** eā₁/a₂h = e/a₂h − ea₁/a₂h = p₂ − (1/c₂) . ea₁a₂/h (c₂ ≠ 0)。 -/
theorem th_17_57_l041 (a₁ a₂ e h : IProp) (c₂ p₂ : ℝ)
    (hc₂ : PrI a₂ h = c₂) (hc₂0 : c₂ ≠ 0) (hp₂ : PrI e (iand a₂ h) = p₂) :
    PrI (iand e (inot a₁)) (iand a₂ h) = PrI e (iand a₂ h) - PrI (iand e a₁) (iand a₂ h)
      ∧ PrI e (iand a₂ h) - PrI (iand e a₁) (iand a₂ h)
          = p₂ - (1 / c₂) * PrI (iand (iand e a₁) a₂) h := by
  have s := def_IX_i e a₁ (iand a₂ h)
  have x := def_X_left_i (iand e a₁) a₂ h
  refine ⟨by linarith, ?_⟩
  rw [x, hp₂, hc₂]
  field_simp

/-- **ch17-042 (folio 190)** ∴ e/h = eā₁ā₂/h + c₁p₁ + c₂p₂ − ea₁a₂/h。 -/
theorem th_17_57_l042 (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) :
    PrI e h = PrI (iand e (iand (inot a₁) (inot a₂))) h + c₁ * p₁ + c₂ * p₂
      - PrI (iand (iand e a₁) a₂) h := by
  have l39 := th_17_57_l039 a₁ e h c₁ p₁ hc₁ hp₁
  have l40 := th_17_57_l040 a₁ a₂ e h c₂ hc hc₂
  have s := def_IX_i e a₁ (iand a₂ h)
  have x := def_X_left_i (iand e a₁) a₂ h
  rw [hp₂] at s
  rw [hc₂] at x
  have : c₂ * PrI (iand e (inot a₁)) (iand a₂ h)
      = c₂ * p₂ - PrI (iand (iand e a₁) a₂) h := by
    rw [x]; linear_combination c₂ * s
  linarith [l39.1, l39.2.1, l39.2.2, l40.1, l40.2]

/-- **ch17-043 (folio 190)** eā₁ā₂/h = eā₁ā₂ā₃/h + eā₁ā₂a₃/h。 -/
theorem th_17_57_l043 (a₁ a₂ a₃ e h : IProp) (hc : Cons h) :
    PrI (iand e (iand (inot a₁) (inot a₂))) h
      = PrI (iand e (iand (iand (inot a₁) (inot a₂)) (inot a₃))) h
        + PrI (iand (iand e (iand (inot a₁) (inot a₂))) a₃) h := by
  have s := def_IX_i (iand e (iand (inot a₁) (inot a₂))) a₃ h
  have k := conj_assoc_i e (iand (inot a₁) (inot a₂)) (inot a₃) h hc
  linarith

/-- **ch17-044 (folio 190)** eā₁ā₂a₃/h = eā₁ā₂/a₃h . c₃ = c₃{e/a₃h − e‾(ā₁ā₂)/a₃h}。 -/
theorem th_17_57_l044 (a₁ a₂ a₃ e h : IProp) (c₃ : ℝ) (hc₃ : PrI a₃ h = c₃) :
    PrI (iand (iand e (iand (inot a₁) (inot a₂))) a₃) h
        = PrI (iand e (iand (inot a₁) (inot a₂))) (iand a₃ h) * c₃
      ∧ PrI (iand e (iand (inot a₁) (inot a₂))) (iand a₃ h) * c₃
        = c₃ * (PrI e (iand a₃ h)
            - PrI (iand e (inot (iand (inot a₁) (inot a₂)))) (iand a₃ h)) := by
  have x := def_X_left_i (iand e (iand (inot a₁) (inot a₂))) a₃ h
  have s := def_IX_i e (iand (inot a₁) (inot a₂)) (iand a₃ h)
  refine ⟨by rw [x, hc₃], by linear_combination c₃ * s⟩

/-- **ch17-045 (folio 190)** = c₃p₃ − e‾(ā₁ā₂)a₃/h。 -/
theorem th_17_57_l045 (a₁ a₂ a₃ e h : IProp) (c₃ p₃ : ℝ)
    (hc₃ : PrI a₃ h = c₃) (hp₃ : PrI e (iand a₃ h) = p₃) :
    PrI (iand (iand e (iand (inot a₁) (inot a₂))) a₃) h
      = c₃ * p₃ - PrI (iand (iand e (inot (iand (inot a₁) (inot a₂)))) a₃) h := by
  have l44 := th_17_57_l044 a₁ a₂ a₃ e h c₃ hc₃
  have x := def_X_left_i (iand e (inot (iand (inot a₁) (inot a₂)))) a₃ h
  rw [hc₃] at x
  rw [l44.1, l44.2, ← hp₃, x]
  ring

/-- **ch17-046 (folio 190)** ∴ e/h = eā₁ā₂ā₃/h + c₁p₁ + c₂p₂ + c₃p₃ − e‾(ā₁)a₂/h
− e‾(ā₁ā₂)a₃/h (印刷の第 1 の補正項は ā₁ の上にさらにバー)。 -/
theorem th_17_57_l046 (a₁ a₂ a₃ e h : IProp) (c₁ c₂ c₃ p₁ p₂ p₃ : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂) (hc₃ : PrI a₃ h = c₃)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂)
    (hp₃ : PrI e (iand a₃ h) = p₃) :
    PrI e h = PrI (iand e (iand (iand (inot a₁) (inot a₂)) (inot a₃))) h
      + c₁ * p₁ + c₂ * p₂ + c₃ * p₃
      - PrI (iand (iand e (inot (inot a₁))) a₂) h
      - PrI (iand (iand e (inot (iand (inot a₁) (inot a₂)))) a₃) h := by
  have l42 := th_17_57_l042 a₁ a₂ e h c₁ c₂ p₁ p₂ hc hc₁ hc₂ hp₁ hp₂
  have l43 := th_17_57_l043 a₁ a₂ a₃ e h hc
  have l45 := th_17_57_l045 a₁ a₂ a₃ e h c₃ p₃ hc₃ hp₃
  have dn := conj_dneg_i e a₁ a₂ h hc
  linarith

/-! ## (57) の一般行 (folio 190)

ā₁…ā_k を nb a k (左入れ子、k ≥ 1)、eā₁…ā_k を iand e (nb a k) と書く。 -/

/-- ā₁ā₂ … ā_k (k ≥ 1; nb a 0 は使わない)。 -/
noncomputable def nb (a : ℕ → IProp) : ℕ → IProp
  | 0 => itrue
  | 1 => inot (a 1)
  | (k + 2) => iand (nb a (k + 1)) (inot (a (k + 2)))

theorem nb_succ (a : ℕ → IProp) (k : ℕ) (hk : 1 ≤ k) :
    nb a (k + 1) = iand (nb a k) (inot (a (k + 1))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-- **ch17-047 (folio 190)** eā₁…ā_{r−1}/h = eā₁…ā_{r−1}āᵣ/h + eā₁…ā_{r−1}aᵣ/h (r ≥ 2)。 -/
theorem th_17_57_l047 (a : ℕ → IProp) (e h : IProp) (hc : Cons h) (r : ℕ) (hr : 2 ≤ r) :
    PrI (iand e (nb a (r - 1))) h
      = PrI (iand e (nb a r)) h + PrI (iand (iand e (nb a (r - 1))) (a r)) h := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, nb_succ a k (by omega)]
  have s := def_IX_i (iand e (nb a k)) (a (k + 1)) h
  have kk := conj_assoc_i e (nb a k) (inot (a (k + 1))) h hc
  linarith

/-- **ch17-048 (folio 190)** = eā₁…āᵣ/h + eā₁…ā_{r−1}/aᵣh . cᵣ。 -/
theorem th_17_57_l048 (a : ℕ → IProp) (c : ℕ → ℝ) (e h : IProp) (hc : Cons h) (r : ℕ)
    (hr : 2 ≤ r) (hcr : PrI (a r) h = c r) :
    PrI (iand e (nb a (r - 1))) h
      = PrI (iand e (nb a r)) h + PrI (iand e (nb a (r - 1))) (iand (a r) h) * c r := by
  rw [th_17_57_l047 a e h hc r hr, def_X_left_i (iand e (nb a (r - 1))) (a r) h, hcr]

/-- **ch17-049 (folio 190)** = eā₁…āᵣ/h + cᵣ{e/aᵣh − e‾(ā₁…ā_{r−1})/aᵣh}。 -/
theorem th_17_57_l049 (a : ℕ → IProp) (c : ℕ → ℝ) (e h : IProp) (hc : Cons h) (r : ℕ)
    (hr : 2 ≤ r) (hcr : PrI (a r) h = c r) :
    PrI (iand e (nb a (r - 1))) h
      = PrI (iand e (nb a r)) h
        + c r * (PrI e (iand (a r) h)
            - PrI (iand e (inot (nb a (r - 1)))) (iand (a r) h)) := by
  rw [th_17_57_l048 a c e h hc r hr hcr]
  have s := def_IX_i e (nb a (r - 1)) (iand (a r) h)
  linear_combination c r * s

/-- **ch17-050 (folio 190)** = eā₁…āᵣ/h + cᵣpᵣ − e‾(ā₁…ā_{r−1})aᵣ/h。 -/
theorem th_17_57_l050 (a : ℕ → IProp) (c p : ℕ → ℝ) (e h : IProp) (hc : Cons h) (r : ℕ)
    (hr : 2 ≤ r) (hcr : PrI (a r) h = c r) (hpr : PrI e (iand (a r) h) = p r) :
    PrI (iand e (nb a (r - 1))) h
      = PrI (iand e (nb a r)) h + c r * p r
        - PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h := by
  rw [th_17_57_l049 a c e h hc r hr hcr, hpr,
    def_X_left_i (iand e (inot (nb a (r - 1)))) (a r) h, hcr]
  ring

/-- **ch17-051 (folio 190)** ∴ finally e/h = eā₁…āₙ/h + Σ₁ⁿ cᵣpᵣ − Σ₂ⁿ e‾(ā₁…ā_{r−1})aᵣ/h
(印刷の Σ₂ⁿ の項は eā … ā_{r−1}aᵣ と ā の添字 1 を欠く)。 -/
theorem th_17_57_l051 (a : ℕ → IProp) (c p : ℕ → ℝ) (e h : IProp) (hc : Cons h)
    (hcr : ∀ r, PrI (a r) h = c r) (hpr : ∀ r, PrI e (iand (a r) h) = p r)
    (n : ℕ) (hn : 1 ≤ n) :
    PrI e h = PrI (iand e (nb a n)) h + ∑ r ∈ Icc 1 n, c r * p r
      - ∑ r ∈ Icc 2 n, PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h := by
  induction n, hn using Nat.le_induction with
  | base =>
      have l39 := th_17_57_l039 (a 1) e h (c 1) (p 1) (hcr 1) (hpr 1)
      simp only [Icc_self, sum_singleton, show Icc 2 1 = (∅ : Finset ℕ) by rfl, sum_empty]
      show PrI e h = PrI (iand e (inot (a 1))) h + c 1 * p 1 - 0
      linarith [l39.1, l39.2.1, l39.2.2]
  | succ n hn ih =>
      have l50 := th_17_57_l050 a c p e h hc (n + 1) (by omega) (hcr (n + 1)) (hpr (n + 1))
      rw [Nat.add_sub_cancel] at l50
      rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
      linarith

/-- **ch17-054 (folio 190)** nᵣ = e‾(ā₁…ā_{r−1})aᵣ/h (記号の約束) と網羅 eā₁…āₙ/h = 0 の下で
(iii.) e/h = Σ₁ⁿ cᵣpᵣ − Σ₂ⁿ nᵣ。 -/
theorem th_17_57_l054 (a : ℕ → IProp) (c p nn : ℕ → ℝ) (e h : IProp) (hc : Cons h)
    (hcr : ∀ r, PrI (a r) h = c r) (hpr : ∀ r, PrI e (iand (a r) h) = p r)
    (hnr : ∀ r, PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h = nn r)
    (n : ℕ) (hn : 1 ≤ n) (hexh : PrI (iand e (nb a n)) h = 0) :
    PrI e h = ∑ r ∈ Icc 1 n, c r * p r - ∑ r ∈ Icc 2 n, nn r := by
  rw [th_17_57_l051 a c p e h hc hcr hpr n hn, hexh]
  simp only [hnr, zero_add]

/-! ## (57.1) (folio 190): 独立な原因 -/

/-- **ch17-057 (folio 190)** e‾(ā₁…ā_{r−1})aᵣ/h = e‾(ā₁…ā_{r−1})/aᵣh . cᵣ。 -/
theorem th_17_57_l057 (a : ℕ → IProp) (c : ℕ → ℝ) (e h : IProp) (r : ℕ)
    (hcr : PrI (a r) h = c r) :
    PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h
      = PrI (iand e (inot (nb a (r - 1)))) (iand (a r) h) * c r := by
  rw [def_X_left_i, hcr]

/-- (57.1) の一段 (補題): 任意の N について (e N̄ aᵣ)/h = cᵣ . e/N̄aᵣh . {1 − N/aᵣh}。
cᵣ = 0 なら両辺 0、cᵣ ≠ 0 なら aᵣh は整合 (cons_of_pos) で (1) が使える。 -/
theorem term57_i (N ar e h : IProp) (cr : ℝ) (hc : Cons h) (hcr : PrI ar h = cr) :
    PrI (iand (iand e (inot N)) ar) h
      = cr * PrI e (iand (inot N) (iand ar h)) * (1 - PrI N (iand ar h)) := by
  rw [def_X_left_i, def_X_left_i e (inot N) (iand ar h), hcr]
  by_cases h0 : cr = 0
  · rw [h0]; ring
  · have hca : Cons (iand ar h) := cons_of_pos ar h (by rw [hcr]; exact h0) hc
    have c1 := th_13_1_i N (iand ar h) hca
    have : PrI (inot N) (iand ar h) = 1 - PrI N (iand ar h) := by linarith
    rw [this]; ring

/-- **ch17-058 (folio 190)** = cᵣ . e/‾(ā₁…ā_{r−1})aᵣh {1 − ā₁…ā_{r−1}/aᵣh}。 -/
theorem th_17_57_l058 (a : ℕ → IProp) (c : ℕ → ℝ) (e h : IProp) (hc : Cons h) (r : ℕ)
    (hcr : PrI (a r) h = c r) :
    PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h
      = c r * PrI e (iand (inot (nb a (r - 1))) (iand (a r) h))
          * (1 - PrI (nb a (r - 1)) (iand (a r) h)) :=
  term57_i (nb a (r - 1)) (a r) e h (c r) hc hcr

/-- **ch17-059, 060 (folio 190) 修正形** mᵣ = e/‾(ā₁…ā_{r−1})aᵣh (記号の約束) の下で
e‾(ā₁…ā_{r−1})aᵣ/h = cᵣ[1 − Π_{s=1}^{r−1}(1 − c_s)] mᵣ。前提は**相互独立**の形
ā₁…ā_{r−1}/aᵣh = Π(1 − c_s) (phase7i IndepChain と同じ内容)。印刷の前提 aᵣ/a_sh = aᵣ/h
(対独立) だけでは成り立たない: Erratum57.th_17_57_l059_printed_fails。 -/
theorem th_17_57_l059 (a : ℕ → IProp) (c : ℕ → ℝ) (e h : IProp) (hc : Cons h) (r : ℕ)
    (m : ℝ) (hcr : PrI (a r) h = c r)
    (hmut : PrI (nb a (r - 1)) (iand (a r) h) = ∏ s ∈ Ico 1 r, (1 - c s))
    (hm : PrI e (iand (inot (nb a (r - 1))) (iand (a r) h)) = m) :
    PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h
      = c r * (1 - ∏ s ∈ Ico 1 r, (1 - c s)) * m := by
  rw [th_17_57_l058 a c e h hc r hcr, hmut, hm]
  ring

/-! ## (57.2)–(57.5) (folio 191) -/

/-- 補題: 0 ≤ c_s ≤ 1 なら 0 ≤ Π(1 − c_s) ≤ 1 かつ 1 − Π(1 − c_s) ≤ Σ c_s。 -/
theorem one_sub_prod_le_sum (S : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ s ∈ S, 0 ≤ c s ∧ c s ≤ 1) :
    0 ≤ ∏ s ∈ S, (1 - c s) ∧ ∏ s ∈ S, (1 - c s) ≤ 1
      ∧ 1 - ∏ s ∈ S, (1 - c s) ≤ ∑ s ∈ S, c s := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
      have hS : ∀ s ∈ S, 0 ≤ c s ∧ c s ≤ 1 := fun s hs => hc s (mem_insert_of_mem hs)
      obtain ⟨i1, i2, i3⟩ := ih hS
      obtain ⟨cx0, cx1⟩ := hc x (mem_insert_self x S)
      rw [prod_insert hx, sum_insert hx]
      refine ⟨mul_nonneg (by linarith) i1, ?_, ?_⟩
      · nlinarith
      · nlinarith

/-- (57.1) の一段の評価 (補題): 相互独立の下で 0 ≤ nᵣ ≤ cᵣ[1 − Π(1 − c_s)]。 -/
theorem nterm_bounds (a : ℕ → IProp) (c : ℕ → ℝ) (e h : IProp) (hc : Cons h) (r : ℕ)
    (hcr : PrI (a r) h = c r)
    (hmut : PrI (nb a (r - 1)) (iand (a r) h) = ∏ s ∈ Ico 1 r, (1 - c s)) :
    0 ≤ PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h
      ∧ PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h
          ≤ c r * (1 - ∏ s ∈ Ico 1 r, (1 - c s)) := by
  have l59 := th_17_57_l059 a c e h hc r _ hcr hmut rfl
  have m0 := ax_range_lo_i e (iand (inot (nb a (r - 1))) (iand (a r) h))
  have m1 := ax_range_hi_i e (iand (inot (nb a (r - 1))) (iand (a r) h))
  have c0 : 0 ≤ c r := hcr ▸ ax_range_lo_i (a r) h
  have P1 : ∏ s ∈ Ico 1 r, (1 - c s) ≤ 1 := hmut ▸ ax_range_hi_i _ _
  have k0 : 0 ≤ c r * (1 - ∏ s ∈ Ico 1 r, (1 - c s)) := mul_nonneg c0 (by linarith)
  rw [l59]
  exact ⟨mul_nonneg k0 m0, mul_le_of_le_one_right k0 m1⟩

/-- **ch17-067 (folio 191)** (57.3) e/h lies between the greatest of
{Σ₁ⁿ cᵣpᵣ − Σ₂ⁿ cᵣ[1 − Π₁^{r−1}(1 − c_s)], c₁p₁, …, cₙpₙ} and the least of
{Σ₁ⁿ cᵣpᵣ, 1 − c₁(1 − p₁), …, 1 − cₙ(1 − pₙ)}。語の between を連言で、独立を相互独立の形で。 -/
theorem th_17_57_l067 (a : ℕ → IProp) (c p : ℕ → ℝ) (e h : IProp) (hc : Cons h)
    (hcr : ∀ r, PrI (a r) h = c r) (hpr : ∀ r, PrI e (iand (a r) h) = p r)
    (n : ℕ) (hn : 1 ≤ n) (hexh : PrI (iand e (nb a n)) h = 0)
    (hmut : ∀ r ∈ Icc 2 n, PrI (nb a (r - 1)) (iand (a r) h) = ∏ s ∈ Ico 1 r, (1 - c s)) :
    (∑ r ∈ Icc 1 n, c r * p r - ∑ r ∈ Icc 2 n, c r * (1 - ∏ s ∈ Ico 1 r, (1 - c s))
        ≤ PrI e h)
      ∧ (∀ r ∈ Icc 1 n, c r * p r ≤ PrI e h)
      ∧ PrI e h ≤ ∑ r ∈ Icc 1 n, c r * p r
      ∧ (∀ r ∈ Icc 1 n, PrI e h ≤ 1 - c r * (1 - p r)) := by
  have l51 := th_17_57_l051 a c p e h hc hcr hpr n hn
  rw [hexh, zero_add] at l51
  have hb := fun r (hr : r ∈ Icc 2 n) => nterm_bounds a c e h hc r (hcr r) (hmut r hr)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ∑ r ∈ Icc 2 n, PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h
        ≤ ∑ r ∈ Icc 2 n, c r * (1 - ∏ s ∈ Ico 1 r, (1 - c s)) :=
      sum_le_sum (fun r hr => (hb r hr).2)
    linarith
  · intro r _
    have s := def_IX_i e (a r) h
    have x := def_X_left_i e (a r) h
    have l := ax_range_lo_i (iand e (inot (a r))) h
    rw [hpr r, hcr r] at x
    linarith
  · have : 0 ≤ ∑ r ∈ Icc 2 n, PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h :=
      sum_nonneg (fun r hr => (hb r hr).1)
    linarith
  · intro r _
    have s := def_IX_i e (a r) h
    have x := def_X_left_i e (a r) h
    have x' := def_X_left_i e (inot (a r)) h
    have hle := ax_range_hi_i e (iand (inot (a r)) h)
    have hlo := ax_range_lo_i (inot (a r)) h
    have c1 := th_13_1_i (a r) h hc
    rw [hpr r, hcr r] at x
    rw [hcr r] at c1
    have : PrI e (iand (inot (a r)) h) * PrI (inot (a r)) h ≤ PrI (inot (a r)) h :=
      mul_le_of_le_one_left hlo hle
    linarith

/-- (57.4) の一段 (補題): e/aᵣh = 1 なら e N̄ aᵣ/h = cᵣ . N̄/aᵣh (Def. IX・X と (1))。 -/
theorem term57_4_i (N ar e h : IProp) (cr : ℝ) (hc : Cons h) (hcr : PrI ar h = cr)
    (hp1 : PrI e (iand ar h) = 1) :
    PrI (iand (iand e (inot N)) ar) h = cr * (1 - PrI N (iand ar h)) := by
  rw [def_X_left_i, hcr]
  by_cases h0 : cr = 0
  · rw [h0]; ring
  · have hca : Cons (iand ar h) := cons_of_pos ar h (by rw [hcr]; exact h0) hc
    have c1 := th_13_1_i e (iand ar h) hca
    have cN := th_13_1_i N (iand ar h) hca
    rw [hp1] at c1
    have s := def_IX_i (inot N) e (iand ar h)
    have x1 := def_X_left_i (inot N) (inot e) (iand ar h)
    have x2 := def_X_right_i (inot N) e (iand ar h)
    have x3 := def_X_left_i e (inot N) (iand ar h)
    have hne : PrI (inot e) (iand ar h) = 0 := by linarith
    rw [hne, mul_zero] at x1
    have : PrI (iand e (inot N)) (iand ar h) = 1 - PrI N (iand ar h) := by
      rw [x3, ← x2]; linarith
    rw [this]; ring

/-- **ch17-069 (folio 191)** pᵣ = 1 なら mᵣ = 1。mᵣ = e/‾(ā₁…ā_{r−1})aᵣh が存在する
範囲 (前提 ‾(ā₁…ā_{r−1})aᵣh が矛盾しない; 公理 (i) の但し書き) で、
‾(ā₁…ā_{r−1})/aᵣh ≠ 0 と aᵣ/h ≠ 0 を前提に置く。 -/
theorem th_17_57_l069 (a : ℕ → IProp) (e h : IProp) (hc : Cons h) (r : ℕ)
    (hcr0 : PrI (a r) h ≠ 0) (hp1 : PrI e (iand (a r) h) = 1)
    (hN : PrI (inot (nb a (r - 1))) (iand (a r) h) ≠ 0) :
    PrI e (iand (inot (nb a (r - 1))) (iand (a r) h)) = 1 := by
  set N := nb a (r - 1)
  have hca : Cons (iand (a r) h) := cons_of_pos (a r) h hcr0 hc
  have c1 := th_13_1_i e (iand (a r) h) hca
  rw [hp1] at c1
  have s := def_IX_i (inot N) e (iand (a r) h)
  have x1 := def_X_left_i (inot N) (inot e) (iand (a r) h)
  have x2 := def_X_right_i (inot N) e (iand (a r) h)
  have hne : PrI (inot e) (iand (a r) h) = 0 := by linarith
  rw [hne, mul_zero] at x1
  have key : (PrI e (iand (inot N) (iand (a r) h)) - 1) * PrI (inot N) (iand (a r) h) = 0 := by
    linarith
  rcases mul_eq_zero.mp key with h1 | h1
  · linarith
  · exact absurd h1 hN

/-- **ch17-068, 070 (folio 191) 修正形** (57.4) p₁ = p₂ = … = pₙ = 1 のとき
e/h = Σ_{r=1}^{n} cᵣ − Σ_{r=2}^{n} cᵣ[1 − Π_{s=1}^{r−1}(1 − c_s)]。前提の独立は相互独立の形。
印刷の対独立だけでは成り立たない: Erratum57.th_17_57_l070_printed_fails。 -/
theorem th_17_57_l070 (a : ℕ → IProp) (c p : ℕ → ℝ) (e h : IProp) (hc : Cons h)
    (hcr : ∀ r, PrI (a r) h = c r) (hpr : ∀ r, PrI e (iand (a r) h) = p r)
    (n : ℕ) (hn : 1 ≤ n) (hexh : PrI (iand e (nb a n)) h = 0)
    (hmut : ∀ r ∈ Icc 2 n, PrI (nb a (r - 1)) (iand (a r) h) = ∏ s ∈ Ico 1 r, (1 - c s))
    (h068 : ∀ r ∈ Icc 1 n, p r = 1) :
    PrI e h = ∑ r ∈ Icc 1 n, c r - ∑ r ∈ Icc 2 n, c r * (1 - ∏ s ∈ Ico 1 r, (1 - c s)) := by
  have l51 := th_17_57_l051 a c p e h hc hcr hpr n hn
  rw [hexh, zero_add] at l51
  rw [l51]
  have e1 : ∑ r ∈ Icc 1 n, c r * p r = ∑ r ∈ Icc 1 n, c r :=
    sum_congr rfl (fun r hr => by rw [h068 r hr, mul_one])
  have e2 : ∑ r ∈ Icc 2 n, PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h
      = ∑ r ∈ Icc 2 n, c r * (1 - ∏ s ∈ Ico 1 r, (1 - c s)) := by
    refine sum_congr rfl (fun r hr => ?_)
    have hr1 : r ∈ Icc 1 n := by simp only [mem_Icc] at hr ⊢; omega
    have hp1 : PrI e (iand (a r) h) = 1 := by rw [hpr r, h068 r hr1]
    rw [term57_4_i (nb a (r - 1)) (a r) e h (c r) hc (hcr r) hp1, hmut r hr]
  rw [e1, e2]

/-- **ch17-072 (folio 191) 修正形** (57.5) 「squares and products may be neglected」の
近似 e/h = Σcᵣpᵣ を、無視した積の和による誤差評価で述べる:
0 ≤ Σ₁ⁿ cᵣpᵣ − e/h ≤ Σ₂ⁿ cᵣ Σ_{s=1}^{r−1} c_s (相互独立の下)。印刷の等式そのものは偽:
Erratum57.th_17_57_l072_printed_fails。 -/
theorem th_17_57_l072 (a : ℕ → IProp) (c p : ℕ → ℝ) (e h : IProp) (hc : Cons h)
    (hcr : ∀ r, PrI (a r) h = c r) (hpr : ∀ r, PrI e (iand (a r) h) = p r)
    (n : ℕ) (hn : 1 ≤ n) (hexh : PrI (iand e (nb a n)) h = 0)
    (hmut : ∀ r ∈ Icc 2 n, PrI (nb a (r - 1)) (iand (a r) h) = ∏ s ∈ Ico 1 r, (1 - c s)) :
    0 ≤ ∑ r ∈ Icc 1 n, c r * p r - PrI e h
      ∧ ∑ r ∈ Icc 1 n, c r * p r - PrI e h ≤ ∑ r ∈ Icc 2 n, c r * ∑ s ∈ Ico 1 r, c s := by
  have l51 := th_17_57_l051 a c p e h hc hcr hpr n hn
  rw [hexh, zero_add] at l51
  have hb := fun r (hr : r ∈ Icc 2 n) => nterm_bounds a c e h hc r (hcr r) (hmut r hr)
  constructor
  · have : 0 ≤ ∑ r ∈ Icc 2 n, PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h :=
      sum_nonneg (fun r hr => (hb r hr).1)
    linarith
  · have : ∑ r ∈ Icc 2 n, PrI (iand (iand e (inot (nb a (r - 1)))) (a r)) h
        ≤ ∑ r ∈ Icc 2 n, c r * ∑ s ∈ Ico 1 r, c s := by
      refine sum_le_sum (fun r hr => le_trans (hb r hr).2 ?_)
      have c0 : 0 ≤ c r := hcr r ▸ ax_range_lo_i (a r) h
      have hcs : ∀ s ∈ Ico 1 r, 0 ≤ c s ∧ c s ≤ 1 :=
        fun s _ => ⟨hcr s ▸ ax_range_lo_i (a s) h, hcr s ▸ ax_range_hi_i (a s) h⟩
      exact mul_le_mul_of_nonneg_left (one_sub_prod_le_sum (Ico 1 r) c hcs).2.2 c0
    linarith

/-! ## (58) (folio 192–193): Boole の問題 X — 自然現象の逐次の生起

x₁x₂ … x_k を xc x k (左入れ子、k ≥ 1) と書く。Keynes は前提側の並置を二つの順で書く:
ch17-078 は x_s/x_r … x_t t̄h (連鎖が先)、ch17-081 は xᵣ/t̄x₁ … x_{r−1}h (t̄ が先)。
本公理系には前提側の置換が無いので、Boole の暗黙の仮定 (ch17-078 脚注) とその確実側の
対応物を、Keynes が使う二つの順でそれぞれ仮定に置く (構造体 Boole58)。 -/

/-- x₁x₂ … x_k (k ≥ 1; xc x 0 は使わない)。 -/
noncomputable def xc (x : ℕ → IProp) : ℕ → IProp
  | 0 => itrue
  | 1 => x 1
  | (k + 2) => iand (xc x (k + 1)) (x (k + 2))

theorem xc_succ (x : ℕ → IProp) (k : ℕ) (hk : 1 ≤ k) :
    xc x (k + 1) = iand (xc x k) (x (k + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-- (58) の前提 (ch17-076 の xᵣ/h = p, t/h = a, xᵣ/th = 1 と、Keynes が証明の中で使う
Boole の仮定)。certX は ch17-081 の「xᵣt/x₁…x_{r−1}h = t/x₁…x_{r−1}h」、certC は
ch17-083 の「x₁…x_{r−1}t/h = a」が使う確実性、neg078 は ch17-078 の印刷の形、
neg081 は ch17-081–082 が使う同じ仮定の t̄ が先の順。 -/
structure Boole58 (x : ℕ → IProp) (t h : IProp) (p a : ℝ) : Prop where
  cons : Cons h
  ha1 : a ≠ 1
  hxh : ∀ r, PrI (x r) h = p
  hta : PrI t h = a
  hxt : ∀ r, PrI (x r) (iand t h) = 1
  certX : ∀ r k, 1 ≤ k → PrI (x r) (iand t (iand (xc x k) h)) = 1
  certC : ∀ k, 1 ≤ k → PrI (xc x k) (iand t h) = 1
  neg078 : ∀ s k, 1 ≤ k →
    PrI (x s) (iand (xc x k) (iand (inot t) h)) = PrI (x s) (iand (inot t) h)
  neg081 : ∀ s k, 1 ≤ k →
    PrI (x s) (iand (inot t) (iand (xc x k) h)) = PrI (x s) (iand (inot t) h)

/-- **ch17-079 (folio 192)** x_s/t̄h = x_s t̄/h ÷ t̄/h = (x_s/h − x_s t/h) ÷ t̄/h = (p − a)/(1 − a)。
前提は ch17-076 (xᵣ/h = p, t/h = a, xᵣ/th = 1) と a ≠ 1 (t̄/h ≠ 0)。 -/
theorem th_17_58_l079 (xs t h : IProp) (p a : ℝ) (hc : Cons h) (ha1 : a ≠ 1)
    (hxh : PrI xs h = p) (hta : PrI t h = a) (hxt : PrI xs (iand t h) = 1) :
    PrI xs (iand (inot t) h) = PrI (iand xs (inot t)) h / PrI (inot t) h
      ∧ PrI (iand xs (inot t)) h / PrI (inot t) h
          = (PrI xs h - PrI (iand xs t) h) / PrI (inot t) h
      ∧ (PrI xs h - PrI (iand xs t) h) / PrI (inot t) h = (p - a) / (1 - a) := by
  have c1 := th_13_1_i t h hc
  have hnt : PrI (inot t) h = 1 - a := by rw [hta] at c1; linarith
  have hnt0 : PrI (inot t) h ≠ 0 := by rw [hnt]; intro h0; exact ha1 (by linarith)
  have xl := def_X_left_i xs (inot t) h
  have s := def_IX_i xs t h
  have x2 := def_X_left_i xs t h
  rw [hxt, hta, one_mul] at x2
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff hnt0, xl]
  · congr 1; linarith
  · rw [hxh, x2, hnt]

theorem q58 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a) (s : ℕ) :
    PrI (x s) (iand (inot t) h) = (p - a) / (1 - a) := by
  have := th_17_58_l079 (x s) t h p a B.cons B.ha1 (B.hxh s) B.hta (B.hxt s)
  rw [this.1, this.2.1, this.2.2]

theorem chain_pos58 (x : ℕ → IProp) (h : IProp) (y : ℕ → ℝ) (hy1 : PrI (x 1) h = y 1)
    (hy : ∀ r, 2 ≤ r → PrI (x r) (iand (xc x (r - 1)) h) = y r) :
    ∀ k, 1 ≤ k → PrI (xc x k) h = ∏ i ∈ Icc 1 k, y i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp only [Icc_self, prod_singleton]; exact hy1
  | succ k hk ih =>
      rw [xc_succ x k hk, def_X_right_i, prod_Icc_succ_top (by omega), ih]
      have := hy (k + 1) (by omega)
      rw [Nat.add_sub_cancel] at this
      rw [this, mul_comm]

theorem chain_neg58 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a) :
    ∀ k, 1 ≤ k → PrI (xc x k) (iand (inot t) h) = ((p - a) / (1 - a)) ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rw [pow_one]; exact q58 B 1
  | succ k hk ih =>
      rw [xc_succ x k hk, def_X_right_i, B.neg078 (k + 1) k hk, q58 B, ih, pow_succ]
      ring

/-- 閉形式 x₁…x_k/h = a + (p − a)((p − a)/(1 − a))^{k−1} (補題; phase7h th_17_58_closed の
KeynesI 版)。 -/
theorem closed58 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a) :
    ∀ k, 1 ≤ k → PrI (xc x k) h = a + (p - a) * ((p - a) / (1 - a)) ^ (k - 1) := by
  intro k hk
  have s := def_IX_i (xc x k) t h
  have x1 := def_X_left_i (xc x k) t h
  have x2 := def_X_left_i (xc x k) (inot t) h
  have c1 := th_13_1_i t h B.cons
  rw [B.certC k hk, B.hta, one_mul] at x1
  rw [chain_neg58 B k hk] at x2
  have hnt : PrI (inot t) h = 1 - a := by rw [B.hta] at c1; linarith
  rw [hnt] at x2
  have h1a : (1 - a) ≠ 0 := fun h0 => B.ha1 (by linarith)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ] at *
  have : ((p - a) / (1 - a)) ^ j * ((p - a) / (1 - a)) * (1 - a)
      = (p - a) * ((p - a) / (1 - a)) ^ j := by field_simp
  linarith

/-- **ch17-080 (folio 192)** xᵣ/x₁…x_{r−1}h = xᵣt/x₁…x_{r−1}h + xᵣt̄/x₁…x_{r−1}h (Def. IX)。 -/
theorem th_17_58_l080 (x : ℕ → IProp) (t h : IProp) (r : ℕ) :
    PrI (x r) (iand (xc x (r - 1)) h)
      = PrI (iand (x r) t) (iand (xc x (r - 1)) h)
        + PrI (iand (x r) (inot t)) (iand (xc x (r - 1)) h) := by
  have := def_IX_i (x r) t (iand (xc x (r - 1)) h)
  linarith

/-- **ch17-081 (folio 192)** = t/x₁…x_{r−1}h + xᵣ/t̄x₁…x_{r−1}h . t̄/x₁…x_{r−1}h
(t の下で xᵣ は確実: certX)。 -/
theorem th_17_58_l081 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a)
    (r : ℕ) (hr : 2 ≤ r) :
    PrI (x r) (iand (xc x (r - 1)) h)
      = PrI t (iand (xc x (r - 1)) h)
        + PrI (x r) (iand (inot t) (iand (xc x (r - 1)) h))
          * PrI (inot t) (iand (xc x (r - 1)) h) := by
  rw [th_17_58_l080 x t h r, def_X_left_i (x r) t, def_X_left_i (x r) (inot t),
    B.certX r (r - 1) (by omega), one_mul]

/-- **ch17-082 (folio 192)** = x₁…x_{r−1}t/h ÷ x₁…x_{r−1}/h
+ ((p − a)/(1 − a)) . (x₁…x_{r−1}/t̄h . t̄/h ÷ x₁…x_{r−1}/h)。 -/
theorem th_17_58_l082 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a)
    (r : ℕ) (hr : 2 ≤ r) (hC : PrI (xc x (r - 1)) h ≠ 0) :
    PrI (x r) (iand (xc x (r - 1)) h)
      = PrI (iand (xc x (r - 1)) t) h / PrI (xc x (r - 1)) h
        + ((p - a) / (1 - a))
          * (PrI (xc x (r - 1)) (iand (inot t) h) * PrI (inot t) h / PrI (xc x (r - 1)) h) := by
  rw [th_17_58_l081 B r hr, B.neg081 r (r - 1) (by omega), q58 B]
  have r1 := def_X_right_i (xc x (r - 1)) t h
  have r2 := def_X_right_i (xc x (r - 1)) (inot t) h
  have l2 := def_X_left_i (xc x (r - 1)) (inot t) h
  rw [r1, ← l2, r2]
  field_simp

/-- **ch17-077, 083 (folio 192)** y_{n+1} = x_{n+1}/x₁…xₙh (記号の約束) の下で
= a ÷ (y₁y₂…y_{r−1}) + ((p − a)/(1 − a)) . (((p − a)/(1 − a))^{r−1}(1 − a) ÷ (y₁y₂…y_{r−1}))。 -/
theorem th_17_58_l083 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a)
    (y : ℕ → ℝ) (hy1 : PrI (x 1) h = y 1)
    (hy : ∀ r, 2 ≤ r → PrI (x r) (iand (xc x (r - 1)) h) = y r)
    (r : ℕ) (hr : 2 ≤ r) (hC : PrI (xc x (r - 1)) h ≠ 0) :
    PrI (x r) (iand (xc x (r - 1)) h)
      = a / ∏ i ∈ Icc 1 (r - 1), y i
        + ((p - a) / (1 - a))
          * (((p - a) / (1 - a)) ^ (r - 1) * (1 - a) / ∏ i ∈ Icc 1 (r - 1), y i) := by
  rw [th_17_58_l082 B r hr hC, ← chain_pos58 x h y hy1 hy (r - 1) (by omega),
    chain_neg58 B (r - 1) (by omega)]
  have x1 := def_X_left_i (xc x (r - 1)) t h
  rw [B.certC (r - 1) (by omega), B.hta, one_mul] at x1
  have c1 := th_13_1_i t h B.cons
  have hnt : PrI (inot t) h = 1 - a := by rw [B.hta] at c1; linarith
  rw [x1, hnt]

/-- **ch17-084 (folio 192)** yᵣ = (a + (p − a)((p − a)/(1 − a))^{r−1}) ÷ (y₁y₂…y_{r−1})。 -/
theorem th_17_58_l084 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a)
    (y : ℕ → ℝ) (hy1 : PrI (x 1) h = y 1)
    (hy : ∀ r, 2 ≤ r → PrI (x r) (iand (xc x (r - 1)) h) = y r)
    (r : ℕ) (hr : 2 ≤ r) (hC : PrI (xc x (r - 1)) h ≠ 0) :
    y r = (a + (p - a) * ((p - a) / (1 - a)) ^ (r - 1)) / ∏ i ∈ Icc 1 (r - 1), y i := by
  rw [← hy r hr, th_17_58_l083 B y hy1 hy r hr hC]
  have h1a : (1 - a) ≠ 0 := fun h0 => B.ha1 (by linarith)
  obtain ⟨j, hj⟩ : ∃ j, r - 1 = j + 1 := ⟨r - 2, by omega⟩
  rw [hj, pow_succ]
  field_simp

/-- **ch17-085 (folio 192)** y₁ = p and y₂ = (a + (p − a)((p − a)/(1 − a))) ÷ y₁ (y₁ ≠ 0)。 -/
theorem th_17_58_l085 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a)
    (y : ℕ → ℝ) (hy1 : PrI (x 1) h = y 1)
    (hy : ∀ r, 2 ≤ r → PrI (x r) (iand (xc x (r - 1)) h) = y r) (hp0 : p ≠ 0) :
    y 1 = p ∧ y 2 = (a + (p - a) * ((p - a) / (1 - a))) / y 1 := by
  have e1 : y 1 = p := by rw [← hy1, B.hxh 1]
  refine ⟨e1, ?_⟩
  have hC : PrI (xc x (2 - 1)) h ≠ 0 := by
    show PrI (x 1) h ≠ 0
    rw [B.hxh 1]; exact hp0
  have := th_17_58_l084 B y hy1 hy 2 le_rfl hC
  simpa using this

/-- 補題: y_n = x₁…x_n/h ÷ x₁…x_{n−1}/h (n ≥ 2; Def. X 右形)。 -/
theorem y_ratio58 (x : ℕ → IProp) (h : IProp) (y : ℕ → ℝ)
    (hy : ∀ r, 2 ≤ r → PrI (x r) (iand (xc x (r - 1)) h) = y r)
    (n : ℕ) (hn : 2 ≤ n) (hC : PrI (xc x (n - 1)) h ≠ 0) :
    y n = PrI (xc x n) h / PrI (xc x (n - 1)) h := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hC ⊢
  rw [eq_div_iff hC, xc_succ x j (by omega), def_X_right_i]
  have := hy (j + 1) hn
  rw [Nat.add_sub_cancel] at this
  rw [this]

/-- **ch17-093, 094 (folio 193)** yₙ = 1 − ε, where
ε = (p − a)[1 − (p − a)/(1 − a)]((p − a)/(1 − a))^{n−2} ÷ (a + (p − a)((p − a)/(1 − a))^{n−2})
(n ≥ 2; 0 < a < 1, a ≤ p で分母は正)。 -/
theorem th_17_58_l093 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a)
    (y : ℕ → ℝ) (hy : ∀ r, 2 ≤ r → PrI (x r) (iand (xc x (r - 1)) h) = y r)
    (ha0 : 0 < a) (ha1 : a < 1) (hpa : a ≤ p) (n : ℕ) (hn : 2 ≤ n) (ε : ℝ)
    (h094 : ε = (p - a) * (1 - (p - a) / (1 - a)) * ((p - a) / (1 - a)) ^ (n - 2)
        / (a + (p - a) * ((p - a) / (1 - a)) ^ (n - 2))) :
    y n = 1 - ε := by
  have hq0 : 0 ≤ (p - a) / (1 - a) := div_nonneg (by linarith) (by linarith)
  have hf : ∀ k, 0 < a + (p - a) * ((p - a) / (1 - a)) ^ k := fun k =>
    add_pos_of_pos_of_nonneg ha0 (mul_nonneg (by linarith) (pow_nonneg hq0 k))
  have hC := closed58 B (n - 1) (by omega)
  have hC0 : PrI (xc x (n - 1)) h ≠ 0 := by rw [hC]; exact (hf _).ne'
  rw [y_ratio58 x h y hy n hn hC0, hC, closed58 B n (by omega), h094]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have e1 : j + 2 - 1 - 1 = j := by omega
  have e2 : j + 2 - 1 = j + 1 := by omega
  have e3 : j + 2 - 2 = j := by omega
  rw [e1, e2, e3, pow_succ]
  have := (hf j).ne'
  field_simp
  ring

/-- **ch17-095 (folio 193)** ε < η: 任意の η > 0 に対し ε < η となる n がある
(a が 0 でない限り; 0 < a ≤ p < 1)。 -/
theorem th_17_58_l095 (p a : ℝ) (ha0 : 0 < a) (hpa : a ≤ p) (hp1 : p < 1) (η : ℝ) (hη : 0 < η) :
    ∃ n, 2 ≤ n ∧ (p - a) * (1 - (p - a) / (1 - a)) * ((p - a) / (1 - a)) ^ (n - 2)
        / (a + (p - a) * ((p - a) / (1 - a)) ^ (n - 2)) < η := by
  have ha1 : 0 < 1 - a := by linarith
  set q := (p - a) / (1 - a) with hqdef
  have hq0 : 0 ≤ q := div_nonneg (by linarith) ha1.le
  have hq1 : q < 1 := by rw [hqdef, div_lt_one ha1]; linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos hη ha0) hq1
  refine ⟨k + 2, by omega, ?_⟩
  rw [show k + 2 - 2 = k by omega]
  have hqk : 0 ≤ q ^ k := pow_nonneg hq0 k
  have hden : a ≤ a + (p - a) * q ^ k := by nlinarith
  have hnum : (p - a) * (1 - q) * q ^ k ≤ q ^ k := by
    have h1 : (p - a) * (1 - q) ≤ 1 := by nlinarith
    nlinarith
  have hpos : 0 < a + (p - a) * q ^ k := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- **ch17-096 (folio 193)** t/x₁…xₙh = x₁…xₙ/th . t/h ÷ x₁…xₙ/h = a ÷ (y₁y₂…yₙ)。 -/
theorem th_17_58_l096 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a)
    (y : ℕ → ℝ) (hy1 : PrI (x 1) h = y 1)
    (hy : ∀ r, 2 ≤ r → PrI (x r) (iand (xc x (r - 1)) h) = y r)
    (n : ℕ) (hn : 1 ≤ n) (hC : PrI (xc x n) h ≠ 0) :
    PrI t (iand (xc x n) h) = PrI (xc x n) (iand t h) * PrI t h / PrI (xc x n) h
      ∧ PrI (xc x n) (iand t h) * PrI t h / PrI (xc x n) h = a / ∏ i ∈ Icc 1 n, y i := by
  have r1 := def_X_right_i (xc x n) t h
  have l1 := def_X_left_i (xc x n) t h
  refine ⟨by rw [eq_div_iff hC, ← l1, r1], ?_⟩
  rw [B.certC n hn, B.hta, one_mul, chain_pos58 x h y hy1 hy n hn]

/-- **ch17-098 (folio 193) 修正形** tₙ = t/x₁…xₙh = 1 − ε′, ε′ = (p − a)((p − a)/(1 − a))^{n−1}
÷ (a + (p − a)((p − a)/(1 − a))^{n−1})。印刷の指数 n (ch17-097 と同じ) は n − 1 が正しい:
th_17_58_l098_printed_fails。 -/
theorem th_17_58_l098 {x : ℕ → IProp} {t h : IProp} {p a : ℝ} (B : Boole58 x t h p a)
    (ha0 : 0 < a) (ha1 : a < 1) (hpa : a ≤ p) (n : ℕ) (hn : 1 ≤ n) :
    PrI t (iand (xc x n) h)
      = 1 - (p - a) * ((p - a) / (1 - a)) ^ (n - 1)
          / (a + (p - a) * ((p - a) / (1 - a)) ^ (n - 1)) := by
  have hq0 : 0 ≤ (p - a) / (1 - a) := div_nonneg (by linarith) (by linarith)
  have hf : 0 < a + (p - a) * ((p - a) / (1 - a)) ^ (n - 1) :=
    add_pos_of_pos_of_nonneg ha0 (mul_nonneg (by linarith) (pow_nonneg hq0 _))
  have hC := closed58 B n hn
  have r1 := def_X_right_i (xc x n) t h
  have l1 := def_X_left_i (xc x n) t h
  rw [B.certC n hn, B.hta, one_mul] at l1
  rw [hC] at r1
  have key : PrI t (iand (xc x n) h) * (a + (p - a) * ((p - a) / (1 - a)) ^ (n - 1)) = a := by
    linarith
  have ht : PrI t (iand (xc x n) h) = a / (a + (p - a) * ((p - a) / (1 - a)) ^ (n - 1)) := by
    rw [eq_div_iff hf.ne']; exact key
  rw [ht]
  field_simp
  ring

/-- **ch17-098 印刷形の反駁** a = 1/2, p = 3/4, n = 1 (Erratum58 と同じ値) で
t₁ = 2/3 だが、印刷の 1 − ε′ (指数 n) は 4/5。 -/
theorem th_17_58_l098_printed_fails {x : ℕ → IProp} {t h : IProp}
    (B : Boole58 x t h (3 / 4) (1 / 2)) :
    PrI t (iand (xc x 1) h)
      ≠ 1 - (3 / 4 - 1 / 2) * ((3 / 4 - 1 / 2) / (1 - 1 / 2)) ^ 1
          / (1 / 2 + (3 / 4 - 1 / 2) * ((3 / 4 - 1 / 2) / (1 - 1 / 2)) ^ 1) := by
  rw [th_17_58_l098 B (by norm_num) (by norm_num) (by norm_num) 1 le_rfl]
  norm_num

end KeynesI

/-! # 対独立の反例 (folio 190–191, (57.1)(57.4)(57.5))

4 点一様の有限モデル (phase7i の Erratum58 と同じく ℚ の計算): 世界 0–3、
a₁ = {2, 3}, a₂ = {1, 3}, a₃ = {1, 2} (a₃ は a₁ と a₂ の排他的論理和)、e = a₁ ∨ a₂ ∨ a₃、
P(X|Y) = |X ∩ Y| / |Y|。印刷の (57.1) の前提 aᵣ/a_sh = aᵣ/h (r ≠ s) はすべて成り立つが、
相互独立 ā₁ā₂/a₃h = Π(1 − c_s) は成り立たない (左辺 0、右辺 1/4)。 -/

namespace Erratum57

def Ω : Finset (Fin 4) := Finset.univ
def A1 : Finset (Fin 4) := {2, 3}
def A2 : Finset (Fin 4) := {1, 3}
def A3 : Finset (Fin 4) := {1, 2}
/-- 否定 x̄ = Ω \ x。 -/
def neg (X : Finset (Fin 4)) : Finset (Fin 4) := Ω \ X
/-- e = a₁ ∨ a₂ ∨ a₃ (原因のどれかがあれば事象は必ず生じる: pᵣ = 1)。 -/
def E : Finset (Fin 4) := A1 ∪ A2 ∪ A3
def N2 : Finset (Fin 4) := neg A1 ∩ neg A2
def N3 : Finset (Fin 4) := N2 ∩ neg A3

/-- 条件付き確率 X/Y = |X ∩ Y| / |Y|。 -/
def P (X Y : Finset (Fin 4)) : ℚ := ((X ∩ Y).card : ℚ) / (Y.card : ℚ)

theorem cards :
    Ω.card = 4 ∧ A1.card = 2 ∧ A2.card = 2 ∧ A3.card = 2
    ∧ (A1 ∩ Ω).card = 2 ∧ (A2 ∩ Ω).card = 2 ∧ (A3 ∩ Ω).card = 2
    ∧ (A1 ∩ A2).card = 1 ∧ (A2 ∩ A1).card = 1 ∧ (A1 ∩ A3).card = 1 ∧ (A3 ∩ A1).card = 1
    ∧ (A2 ∩ A3).card = 1 ∧ (A3 ∩ A2).card = 1
    ∧ (E ∩ neg N2 ∩ A3 ∩ Ω).card = 2 ∧ (neg N2 ∩ A3).card = 2 ∧ (E ∩ (neg N2 ∩ A3)).card = 2
    ∧ (E ∩ Ω).card = 3 ∧ (E ∩ A1).card = 2 ∧ (E ∩ A2).card = 2 ∧ (E ∩ A3).card = 2
    ∧ (E ∩ N3 ∩ Ω).card = 0 ∧ ((A1 ∪ A2) ∩ Ω).card = 3 ∧ ((A1 ∪ A2) ∩ A1).card = 2
    ∧ ((A1 ∪ A2) ∩ A2).card = 2 ∧ (N2 ∩ A3).card = 0 := by
  decide

/-- 印刷の (57.1) の前提 aᵣ/a_sh = aᵣ/h (r ≠ s) はこのモデルで成り立つ。一方
ā₁ā₂/a₃h = 0 ≠ 1/4 = (1 − c₁)(1 − c₂) (相互独立は成り立たない)。 -/
theorem th_17_57_pairwise_only :
    (P A1 A2 = P A1 Ω ∧ P A2 A1 = P A2 Ω ∧ P A1 A3 = P A1 Ω
      ∧ P A3 A1 = P A3 Ω ∧ P A2 A3 = P A2 Ω ∧ P A3 A2 = P A3 Ω)
    ∧ P N2 A3 = 0 ∧ (1 - P A1 Ω) * (1 - P A2 Ω) = 1 / 4 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, -, -, -, -, -, -, -, -, -,
    h24⟩ := cards
  simp only [P, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h24]
  norm_num

/-- **ch17-059 印刷形の反駁** 対独立だけでは
e‾(ā₁ā₂)a₃/h = c₃[1 − (1 − c₁)(1 − c₂)]m₃ が成り立たない: 左辺 1/2、右辺 3/8 (m₃ = 1)。 -/
theorem th_17_57_l059_printed_fails :
    P (E ∩ neg N2 ∩ A3) Ω = 1 / 2
      ∧ P A3 Ω * (1 - (1 - P A1 Ω) * (1 - P A2 Ω)) * P E (neg N2 ∩ A3) = 3 / 8
      ∧ P (E ∩ neg N2 ∩ A3) Ω
          ≠ P A3 Ω * (1 - (1 - P A1 Ω) * (1 - P A2 Ω)) * P E (neg N2 ∩ A3) := by
  obtain ⟨h0, -, -, -, h4, h5, h6, -, -, -, -, -, -, h13, h14, h15, -⟩ := cards
  simp only [P, h0, h4, h5, h6, h13, h14, h15]
  norm_num

/-- **ch17-070 印刷形の反駁** 網羅 (eā₁ā₂ā₃/h = 0) と p₁ = p₂ = p₃ = 1 と対独立の下で、
e/h = 3/4 だが印刷の Σcᵣ − Σ₂³ cᵣ[1 − Π_{s<r}(1 − c_s)] = 7/8。 -/
theorem th_17_57_l070_printed_fails :
    P (E ∩ N3) Ω = 0 ∧ P E A1 = 1 ∧ P E A2 = 1 ∧ P E A3 = 1
      ∧ P E Ω = 3 / 4
      ∧ (P A1 Ω + P A2 Ω + P A3 Ω) - P A2 Ω * (1 - (1 - P A1 Ω))
          - P A3 Ω * (1 - (1 - P A1 Ω) * (1 - P A2 Ω)) = 7 / 8
      ∧ P E Ω ≠ (P A1 Ω + P A2 Ω + P A3 Ω) - P A2 Ω * (1 - (1 - P A1 Ω))
          - P A3 Ω * (1 - (1 - P A1 Ω) * (1 - P A2 Ω)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -, -, -, -, -, -, -, -, -, h16, h17, h18, h19, h20, -⟩ :=
    cards
  simp only [P, h0, h1, h2, h3, h4, h5, h6, h16, h17, h18, h19, h20]
  norm_num

/-- **ch17-072 印刷形の反駁** (57.5) の e/h = Σcᵣpᵣ は等式としては偽: 独立な二つの原因
a₁, a₂ (c₁ = c₂ = 1/2) と e = a₁ ∨ a₂ で e/h = 3/4、Σcᵣpᵣ = 1。 -/
theorem th_17_57_l072_printed_fails :
    P A1 A2 = P A1 Ω ∧ P (A1 ∪ A2) A1 = 1 ∧ P (A1 ∪ A2) A2 = 1
      ∧ P (A1 ∪ A2) Ω = 3 / 4
      ∧ P (A1 ∪ A2) Ω ≠ P A1 Ω * P (A1 ∪ A2) A1 + P A2 Ω * P (A1 ∪ A2) A2 := by
  obtain ⟨h0, h1, h2, -, h4, h5, -, h7, -, -, -, -, -, -, -, -, -, -, -, -, -, h21, h22, h23,
    -⟩ := cards
  simp only [P, h0, h1, h2, h4, h5, h7, h21, h22, h23]
  norm_num

end Erratum57

/-! # 第 I 部の続き: U8 (folio 196) -/

namespace KeynesI

/-- **ch17-109 (folio 196)** U8: x_q/a_sh = f(y_q, b_s) (前提)。この仮定の下で尤度
Π_q x_q/a_sh は Π_q f(y_q, b_s) に等しく、b_s の比較 (最大化) は Π f(y_q, b_s) の比較に
置き換わる (「we have to find the value of b_s … which makes Π f(y_q, y) a maximum」)。 -/
theorem th_17_U8_l109 {m n : ℕ} (x : Fin m → IProp) (a : Fin n → IProp) (h : IProp)
    (f : ℝ → ℝ → ℝ) (y : Fin m → ℝ) (b : Fin n → ℝ)
    (h109 : ∀ q s, PrI (x q) (iand (a s) h) = f (y q) (b s)) :
    (∀ s, ∏ q, PrI (x q) (iand (a s) h) = ∏ q, f (y q) (b s))
      ∧ (∀ s s', ∏ q, PrI (x q) (iand (a s') h) ≤ ∏ q, PrI (x q) (iand (a s) h)
          ↔ ∏ q, f (y q) (b s') ≤ ∏ q, f (y q) (b s)) := by
  have e : ∀ s, ∏ q, PrI (x q) (iand (a s) h) = ∏ q, f (y q) (b s) :=
    fun s => prod_congr rfl (fun q _ => h109 q s)
  exact ⟨e, fun s s' => by rw [e s, e s']⟩

end KeynesI

/-! # 第 II 部: 誤差法則 (§3–§12, folio 196–210) — 実関数の上で -/

namespace KeynesLawOfError

/-! ## phase9x の補題の写し (本ファイルで証明し直す) -/

/-- 停留条件の一般形 (phase9x th_17_1911_1_src の写し): 指数 E_q の微分が c·θ_q (c ≠ 0) なら、
対数尤度 Σ log(A e^{E_q}) の停留条件は Σθ_q = 0 と同値。 -/
theorem stationary_general {m : ℕ} (A c : ℝ) (E : Fin m → ℝ → ℝ) (θ : Fin m → ℝ) (t : ℝ)
    (hA : 0 < A) (hc : c ≠ 0) (hE : ∀ q, HasDerivAt (E q) (c * θ q) t) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (E q s))) t = 0 ↔ ∑ q, θ q = 0 := by
  have hfun : (fun s => ∑ q, Real.log (A * Real.exp (E q s)))
      = fun s => ∑ q, (Real.log A + E q s) := by
    funext s
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hd : HasDerivAt (fun s => ∑ q, (Real.log A + E q s)) (∑ q, (0 + c * θ q)) t := by
    have := HasDerivAt.sum (u := Finset.univ) (A := fun q s => Real.log A + E q s)
      (A' := fun q => 0 + c * θ q) (x := t)
      (fun q _ => (hasDerivAt_const t (Real.log A)).add (hE q))
    convert this using 1
    funext s
    simp [Finset.sum_apply]
  rw [hfun, hd.deriv]
  simp only [zero_add, ← Finset.mul_sum]
  constructor
  · intro hh
    rcases mul_eq_zero.mp hh with h0 | h0
    · exact absurd h0 hc
    · exact h0
  · intro hh
    rw [hh, mul_zero]

/-- 区間 (0, ∞) で微分 0 なら定数 (積分定数の補題)。 -/
theorem const_on_pos (g : ℝ → ℝ) (hg : ∀ s, 0 < s → HasDerivAt g 0 s) :
    ∀ s, 0 < s → g s = g 1 := by
  intro s hs
  have hdiff : DifferentiableOn ℝ g (Set.Ioi 0) :=
    fun x hx => (hg x hx).differentiableAt.differentiableWithinAt
  have hd0 : (Set.Ioi (0 : ℝ)).EqOn (deriv g) 0 := fun x hx => (hg x hx).deriv
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hd0
    (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr one_pos)

/-- |s − y_q| の微分 (y ≠ y_q; phase9x th_17_1911_iv_3_src の中の補題の写し)。 -/
theorem hasDerivAt_abs_sub (yq t : ℝ) (hne : t ≠ yq) :
    HasDerivAt (fun s => |s - yq|) ((t - yq) / |t - yq|) t := by
  rcases lt_or_gt_of_ne hne with h | h
  · have := (hasDerivAt_abs_neg (sub_neg.mpr h)).comp t ((hasDerivAt_id' t).sub_const yq)
    convert this using 1
    rw [abs_of_neg (sub_neg.mpr h), div_neg, div_self (sub_ne_zero.mpr hne)]
    norm_num
  · have := (hasDerivAt_abs_pos (sub_pos.mpr h)).comp t ((hasDerivAt_id' t).sub_const yq)
    convert this using 1
    rw [abs_of_pos (sub_pos.mpr h), div_self (sub_ne_zero.mpr hne)]
    norm_num

/-- (i)-6 の第 1 段 (phase9x th_17_1911_i_6_src の写し)。 -/
theorem i6_deriv (φ φ' φ'' ψ θ θ' : ℝ → ℝ)
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (φ'' t) t)
    (hθ : ∀ u, HasDerivAt θ (θ' u) u)
    (hid : ∀ t yq, φ' t * (t - yq) - φ t + ψ yq = θ ((t - yq)^2)) :
    (∀ t yq, t ≠ yq → φ'' t = 2 * θ' ((t - yq)^2)) ∧ (∀ u v, 0 < u → 0 < v → θ' u = θ' v) := by
  have hdiff : ∀ t yq, t ≠ yq → φ'' t = 2 * θ' ((t - yq)^2) := by
    intro t yq hty
    have hL : HasDerivAt (fun s => φ' s * (s - yq) - φ s + ψ yq) (φ'' t * (t - yq)) t := by
      have key : HasDerivAt (fun s => φ' s * (s - yq) - φ s)
          ((φ'' t * (t - yq) + φ' t * 1) - φ' t) t :=
        ((hφ' t).mul ((hasDerivAt_id' t).sub_const yq)).sub (hφ t)
      have := key.add_const (ψ yq)
      convert this using 1
      ring
    have hR : HasDerivAt (fun s => θ ((s - yq)^2))
        (θ' ((t - yq)^2) * (2 * (t - yq))) t := by
      have hin : HasDerivAt (fun s => (s - yq)^2) (2 * (t - yq)) t := by
        have := ((hasDerivAt_id' t).sub_const yq).pow 2
        convert this using 1
        ring
      exact (hθ _).comp t hin
    have hfun : (fun s => φ' s * (s - yq) - φ s + ψ yq) = fun s => θ ((s - yq)^2) := by
      funext s
      exact hid s yq
    rw [hfun] at hL
    have huniq := hL.unique hR
    have hmul : (φ'' t - 2 * θ' ((t - yq)^2)) * (t - yq) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h0 | h0
    · linarith
    · exact absurd (sub_eq_zero.mp h0) hty
  refine ⟨hdiff, fun u v hu hv => ?_⟩
  have hsu := Real.sqrt_pos.mpr hu
  have hsv := Real.sqrt_pos.mpr hv
  have hu' := hdiff 0 (-Real.sqrt u) (by linarith)
  have hv' := hdiff 0 (-Real.sqrt v) (by linarith)
  rw [show (0 - -Real.sqrt u)^2 = u by rw [sub_neg_eq_add, zero_add, Real.sq_sqrt hu.le]] at hu'
  rw [show (0 - -Real.sqrt v)^2 = v by rw [sub_neg_eq_add, zero_add, Real.sq_sqrt hv.le]] at hv'
  linarith

/-- (i)-6 の積分 (phase9x th_17_1911_i_6_integrate の写し)。 -/
theorem i6_integrate (θ θ' : ℝ → ℝ) (c : ℝ)
    (hθ : ∀ u, HasDerivAt θ (θ' u) u) (hconst : ∀ u, 0 < u → θ' u = c) :
    ∀ u, 0 ≤ u → θ u = c * u + θ 0 := by
  intro u hu
  have hg : ∀ s, 0 < s → HasDerivAt (fun s => θ s - c * s) 0 s := by
    intro s hs
    have := (hθ s).sub ((hasDerivAt_id' s).const_mul c)
    rw [hconst s hs] at this
    convert this using 1
    ring
  rcases eq_or_lt_of_le hu with h0 | hpos
  · rw [← h0]; ring
  · have hcont : ContinuousOn (fun s => θ s - c * s) (Set.Icc 0 u) :=
      fun s _ => ((hθ s).sub ((hasDerivAt_id' s).const_mul c)).continuousAt.continuousWithinAt
    have hder : ∀ s ∈ Set.Ioo 0 u, HasDerivAt (fun s => θ s - c * s) 0 s :=
      fun s hs => hg s hs.1
    have := exists_hasDerivAt_eq_slope (fun s => θ s - c * s) (fun _ => 0) hpos hcont hder
    obtain ⟨ξ, _, hξ⟩ := this
    have h1 : ((θ u - c * u) - (θ 0 - c * 0)) / (u - 0) = 0 := hξ.symm
    rcases div_eq_zero_iff.mp h1 with h2 | h2
    · linarith
    · linarith

/-- (i)-6 の符号 (phase9x th_17_1911_i_6_sign の写し)。 -/
theorem i6_sign (B c θ0 : ℝ) (hB : 0 < B)
    (hle : ∀ u, 0 ≤ u → B * Real.exp (c * u + θ0) ≤ 1) : c ≤ 0 := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc
  exfalso
  set u := (|θ0| + |Real.log B| + 1) / c with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 := hle u hu0
  have h2 : Real.log (B * Real.exp (c * u + θ0)) ≤ Real.log 1 :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at h2
  have h3 : c * u = |θ0| + |Real.log B| + 1 := by
    rw [hu]; field_simp
  have h4 := neg_abs_le (Real.log B)
  have h5 := neg_abs_le θ0
  linarith

/-! ## §4 脚注、(i) 算術平均 (folio 196–198) -/

/-- **ch17-114 (folio 196 脚注 1)** e_q = b_s − y_q (Gauss: 誤差)。誤差の和が 0 となる値は
算術平均: Σ e_q = 0 ⟺ b_s = (Σ y_q)/m。 -/
theorem th_17_N1_l114 {m : ℕ} (hm : 0 < m) (y : Fin m → ℝ) (b : ℝ) (e : Fin m → ℝ)
    (h114 : ∀ q, e q = b - y q) :
    ∑ q, e q = 0 ↔ b = (∑ q, y q) / m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [h114]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, eq_div_iff hm']
  constructor <;> intro hh <;> linarith

/-- **ch17-122 (folio 197)** f′_q/f_q = φ″(y)(y − y_q) (ch17-121) を積分して
log f_q = ∫φ″(y)(y − y_q)dy + ψ(y_q)。∫ を原始関数 G (G′ = φ″(y)(y − y_q)) で、ψ(y_q) を
積分定数で表す。 -/
theorem th_17_i_l122 (f f' φ'' G : ℝ → ℝ) (yq : ℝ)
    (hpos : ∀ s, 0 < f s) (hf : ∀ s, HasDerivAt f (f' s) s)
    (h121 : ∀ s, f' s / f s = φ'' s * (s - yq))
    (hG : ∀ s, HasDerivAt G (φ'' s * (s - yq)) s) :
    ∃ ψyq : ℝ, ∀ s, Real.log (f s) = G s + ψyq := by
  have hd : ∀ s, HasDerivAt (fun s => Real.log (f s) - G s) 0 s := by
    intro s
    have := ((hf s).log (hpos s).ne').sub (hG s)
    convert this using 1
    rw [h121 s]; ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv)
  refine ⟨Real.log (f 0) - G 0, fun s => ?_⟩
  have := hconst s 0
  simp only at this
  linarith

/-- **ch17-125, 126 (folio 197)** φ(y) = −k²y², ψ(y_q) = −k²y_q² + log A を
f_q = e^{φ′(y)(y − y_q) − φ(y) + ψ(y_q)} (ch17-124) に代入すると f_q = Ae^{−k²(y − y_q)²}。
φ′ は φ の微分 (HasDerivAt) として与え、その値 −2k²y は代入から導く。 -/
theorem th_17_i_l125 (A k yq : ℝ) (hA : 0 < A) (φ φ' ψ : ℝ → ℝ)
    (hφd : ∀ s, HasDerivAt φ (φ' s) s)
    (h125 : ∀ s, φ s = -(k^2) * s^2) (h126 : ψ yq = -(k^2) * yq^2 + Real.log A) (t : ℝ) :
    Real.exp (φ' t * (t - yq) - φ t + ψ yq) = A * Real.exp (-(k^2) * (t - yq)^2) := by
  have hφfun : φ = fun s => -(k^2) * s^2 := funext h125
  have hd : HasDerivAt (fun s => -(k^2) * s^2) (-(k^2) * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul (-(k^2))
    convert this using 1
    ring
  have hφ' : φ' t = -(k^2) * (2 * t) := by
    have := hφd t
    rw [hφfun] at this
    exact this.unique hd
  have hexp : φ' t * (t - yq) - φ t + ψ yq = -(k^2) * (t - yq)^2 + Real.log A := by
    rw [hφ', h125, h126]; ring
  rw [hexp, Real.exp_add, Real.exp_log hA, mul_comm]

/-- **ch17-132 (folio 198)** ∴ (d/d(y − y_q)²)θ(y − y_q)² = −k² (k は定数)。
(i)-6 の恒等式 φ′(y)(y − y_q) − φ(y) + ψ(y_q) = θ(y − y_q)² から θ′ は定数、
法則 Be^{θ} ≤ 1 (範囲) からその定数は負でない数の符号を変えたもの −k²。 -/
theorem th_17_i_l132 (φ φ' φ'' ψ θ θ' : ℝ → ℝ) (B : ℝ) (hB : 0 < B)
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (φ'' t) t)
    (hθ : ∀ u, HasDerivAt θ (θ' u) u)
    (hid : ∀ t yq, φ' t * (t - yq) - φ t + ψ yq = θ ((t - yq)^2))
    (hle : ∀ u, 0 ≤ u → B * Real.exp (θ u) ≤ 1) :
    ∃ k : ℝ, ∀ t yq, t ≠ yq → θ' ((t - yq)^2) = -(k^2) := by
  obtain ⟨_, hconst⟩ := i6_deriv φ φ' φ'' ψ θ θ' hφ hφ' hθ hid
  have hc : ∀ u, 0 < u → θ' u = θ' 1 := fun u hu => hconst u 1 hu one_pos
  have hint := i6_integrate θ θ' (θ' 1) hθ hc
  have hsign : θ' 1 ≤ 0 :=
    i6_sign B (θ' 1) (θ 0) hB (fun u hu => by rw [← hint u hu]; exact hle u hu)
  refine ⟨Real.sqrt (-(θ' 1)), fun t yq hty => ?_⟩
  rw [Real.sq_sqrt (by linarith), neg_neg]
  exact hc _ (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hty))))

/-- **ch17-135 (folio 198)** A = BC: Be^{θ(u)} で θ(u) = −k²u + log C (ch17-133) なら
Be^{θ(u)} = Ae^{−k²u}。 -/
theorem th_17_i_l135 (A B C k u : ℝ) (hC : 0 < C) (h135 : A = B * C) :
    B * Real.exp (-(k^2) * u + Real.log C) = A * Real.exp (-(k^2) * u) := by
  rw [Real.exp_add, Real.exp_log hC, h135]; ring

/-! ## (ii) 幾何平均 (folio 198–200) -/

/-- **ch17-136 (folio 198)** Σ f′_q/f_q = 0 must be equivalent to Π_{q=1}^{m} y_q = yᵐ:
f_q に (7) の形を代入した対数尤度の停留条件 ⟺ Π y_q = yᵐ (y, y_q > 0)。 -/
theorem th_17_ii_l136 {m : ℕ} (A : ℝ) (φ' φ'' Φ ψ : ℝ → ℝ) (y : Fin m → ℝ)
    (hy : ∀ q, 0 < y q) (t : ℝ) (ht : 0 < t)
    (hA : 0 < A) (h2 : HasDerivAt φ' (φ'' t) t) (hΦ : HasDerivAt Φ (φ' t / t) t)
    (hne : φ'' t ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (φ' s * Real.log (y q / s) + Φ s + ψ (y q)))) t = 0
      ↔ ∏ q, y q = t ^ m := by
  rw [stationary_general A (φ'' t) (fun q s => φ' s * Real.log (y q / s) + Φ s + ψ (y q))
    (fun q => Real.log (y q / t)) t hA hne (fun q => ?_)]
  · have hprod : 0 < ∏ q, y q := Finset.prod_pos (fun q _ => hy q)
    have hsum : (∑ q, Real.log (y q / t)) = Real.log (∏ q, y q) - m * Real.log t := by
      rw [Real.log_prod (fun q _ => (hy q).ne')]
      simp_rw [Real.log_div (hy _).ne' ht.ne']
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [hsum, sub_eq_zero, ← Real.log_pow]
    constructor
    · intro hh
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hprod) (Set.mem_Ioi.mpr (pow_pos ht m)) hh
    · intro hh; rw [hh]
  · have hlog : HasDerivAt (fun s => Real.log (y q / s)) (-(1 / t)) t := by
      have : HasDerivAt (fun s => Real.log (y q) - Real.log s) (0 - t⁻¹) t :=
        (hasDerivAt_const t (Real.log (y q))).sub (Real.hasDerivAt_log ht.ne')
      have hfun : (fun s => Real.log (y q / s)) =ᶠ[nhds t]
          fun s => Real.log (y q) - Real.log s := by
        filter_upwards [lt_mem_nhds ht] with s hs
        rw [Real.log_div (hy q).ne' hs.ne']
      rw [show -(1 / t) = 0 - t⁻¹ by ring]
      exact this.congr_of_eventuallyEq hfun
    have key := ((h2.mul hlog).add hΦ).add_const (ψ (y q))
    convert key using 1
    field_simp
    ring

/-- **ch17-141, 142 (folio 198)** φ′(y) = −ky, ψ(y_q) = 0 を (7) に代入すると
f_q = A(y/y_q)^{ky}e^{−ky}。∫(φ′(y)/y)dy = −ky + C の積分定数 C は A に吸収する。 -/
theorem th_17_ii_l141 (A k yq : ℝ) (hyq : 0 < yq) (φ' Φ ψ : ℝ → ℝ)
    (h141 : ∀ s, φ' s = -k * s) (hΦ : ∀ s, 0 < s → HasDerivAt Φ (φ' s / s) s)
    (h142 : ψ yq = 0) :
    ∃ C : ℝ, ∀ s, 0 < s →
      A * Real.exp (φ' s * Real.log (yq / s) + Φ s + ψ yq)
        = (A * Real.exp C) * (s / yq) ^ (k * s) * Real.exp (-k * s) := by
  have hg : ∀ s, 0 < s → HasDerivAt (fun s => Φ s + k * s) 0 s := by
    intro s hs
    have := (hΦ s hs).add ((hasDerivAt_id' s).const_mul k)
    convert this using 1
    rw [h141 s]; field_simp; ring
  have hc := const_on_pos _ hg
  refine ⟨Φ 1 + k * 1, fun s hs => ?_⟩
  have hΦs : Φ s = -k * s + (Φ 1 + k * 1) := by
    have := hc s hs; simp only at this; linarith
  rw [h141 s, hΦs, h142, Real.rpow_def_of_pos (div_pos hs hyq), Real.log_div hs.ne' hyq.ne',
    Real.log_div hyq.ne' hs.ne']
  simp only [mul_assoc]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- **ch17-144 (folio 199)** l_q = log y_q が正規法則 f(l_q, l) = Ae^{−k²(l_q − l)²} に従うなら
(前提)、y_q の法則は Ae^{−k²(log y_q − log y)²} = Ae^{−k²(log(y_q/y))²}。 -/
theorem th_17_ii_l144 (A k yq t : ℝ) (hyq : 0 < yq) (ht : 0 < t) (F : ℝ → ℝ → ℝ)
    (h144 : ∀ lq l, F lq l = A * Real.exp (-(k^2) * (lq - l)^2)) :
    F (Real.log yq) (Real.log t) = A * Real.exp (-(k^2) * (Real.log yq - Real.log t)^2)
      ∧ F (Real.log yq) (Real.log t) = A * Real.exp (-(k^2) * (Real.log (yq / t))^2) := by
  rw [h144, Real.log_div hyq.ne' ht.ne']
  exact ⟨rfl, rfl⟩

/-- **ch17-147, 148 (folio 199)** ψ(y_q) = −k²(log y_q)², φ′(y) = 2k² log y を (7) に代入すると
f_q = Ae^{−k²(log(y_q/y))²} (∫(2k² log y / y)dy = k²(log y)² + C の C は A に吸収)。 -/
theorem th_17_ii_l147 (A k yq : ℝ) (hyq : 0 < yq) (φ' Φ ψ : ℝ → ℝ)
    (h148 : ∀ s, φ' s = 2 * k^2 * Real.log s) (hΦ : ∀ s, 0 < s → HasDerivAt Φ (φ' s / s) s)
    (h147 : ψ yq = -(k^2) * (Real.log yq)^2) :
    ∃ C : ℝ, ∀ s, 0 < s →
      A * Real.exp (φ' s * Real.log (yq / s) + Φ s + ψ yq)
        = (A * Real.exp C) * Real.exp (-(k^2) * (Real.log (yq / s))^2) := by
  have hg : ∀ s, 0 < s → HasDerivAt (fun s => Φ s - k^2 * (Real.log s)^2) 0 s := by
    intro s hs
    have h1 := ((Real.hasDerivAt_log hs.ne').pow 2).const_mul (k^2)
    have := (hΦ s hs).sub h1
    convert this using 1
    rw [h148 s]; field_simp; ring
  have hc := const_on_pos _ hg
  refine ⟨Φ 1 - k^2 * (Real.log 1)^2, fun s hs => ?_⟩
  have hΦs : Φ s = k^2 * (Real.log s)^2 + (Φ 1 - k^2 * (Real.log 1)^2) := by
    have := hc s hs; simp only at this; linarith
  rw [h148 s, hΦs, h147, mul_assoc A, ← Real.exp_add, Real.log_div hyq.ne' hs.ne']
  congr 2
  ring

/-- **ch17-150 (folio 199)** 連鎖の第 2 行:
Ae^{2k² log y log(y_q/y) + k²(log y)² − k²(log y_q)²}
= Ae^{2k² log y log y_q − 2k²(log y)² + k²(log y)² − k²(log y_q)²} = Ae^{−k²(log(y_q/y))²}
(第 1 行の ∫2k²(log y/y)dy は k²(log y)² と評価済み)。 -/
theorem th_17_ii_l150 (A k t yq : ℝ) (ht : 0 < t) (hyq : 0 < yq) :
    A * Real.exp (2 * k^2 * Real.log t * Real.log (yq / t) + k^2 * (Real.log t)^2
        - k^2 * (Real.log yq)^2)
      = A * Real.exp (2 * k^2 * Real.log t * Real.log yq - 2 * k^2 * (Real.log t)^2
          + k^2 * (Real.log t)^2 - k^2 * (Real.log yq)^2)
    ∧ A * Real.exp (2 * k^2 * Real.log t * Real.log yq - 2 * k^2 * (Real.log t)^2
          + k^2 * (Real.log t)^2 - k^2 * (Real.log yq)^2)
      = A * Real.exp (-(k^2) * (Real.log (yq / t))^2) := by
  rw [Real.log_div hyq.ne' ht.ne']
  constructor <;> congr 2 <;> ring

/-- **ch17-152 (folio 199)** Kapteyn: z = F(y) (前提) で z が正規法則に従うとき、
法則 Ae^{−k²(z(y_q) − z(y))²} の停留条件は Σ(F(y_q) − F(y)) = 0 (F′(y) ≠ 0)。 -/
theorem th_17_ii_l152 {m : ℕ} (A k : ℝ) (hA : 0 < A) (hk : k ≠ 0) (F F' z : ℝ → ℝ)
    (h152 : ∀ s, z s = F s) (y : Fin m → ℝ) (t : ℝ) (hF : HasDerivAt F (F' t) t)
    (hF' : F' t ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * (z (y q) - z s)^2))) t = 0
      ↔ ∑ q, (F (y q) - F t) = 0 := by
  simp only [h152]
  refine stationary_general A (2 * k^2 * F' t) (fun q s => -(k^2) * (F (y q) - F s)^2)
    (fun q => F (y q) - F t) t hA
    (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hk)) hF') (fun q => ?_)
  have := (((hasDerivAt_const t (F (y q))).sub hF).pow 2).const_mul (-(k^2))
  convert this using 1
  simp only [Pi.sub_apply]
  ring

/-- **ch17-154, 155 (folio 200)** log y = l, log y_q = l_q と書くと、幾何法則
A(y/y_q)^{k²y}e^{−k²y} は算術法則 Ae^{k²eˡ(l − l_q) − k²eˡ} になる。 -/
theorem th_17_ii_l154 (A k t yq l lq : ℝ) (ht : 0 < t) (hyq : 0 < yq)
    (h154 : Real.log t = l) (h155 : Real.log yq = lq) :
    A * (t / yq) ^ (k^2 * t) * Real.exp (-(k^2) * t)
      = A * Real.exp (k^2 * Real.exp l * (l - lq) - k^2 * Real.exp l) := by
  rw [← h154, ← h155, Real.rpow_def_of_pos (div_pos ht hyq), Real.log_div ht.ne' hyq.ne',
    Real.exp_log ht]
  simp only [mul_assoc]
  rw [← Real.exp_add]
  congr 2
  ring

/-- **ch17-157, 158 (folio 200)** φ(l) = k²eˡ, ψ(l_q) = 0 を (5) に代入すると
f_q = Ae^{k²eˡ(l − l_q) − k²eˡ}。 -/
theorem th_17_ii_l157 (A k l lq : ℝ) (φ φ' ψ : ℝ → ℝ) (hφd : ∀ s, HasDerivAt φ (φ' s) s)
    (h157 : ∀ s, φ s = k^2 * Real.exp s) (h158 : ψ lq = 0) :
    A * Real.exp (φ' l * (l - lq) - φ l + ψ lq)
      = A * Real.exp (k^2 * Real.exp l * (l - lq) - k^2 * Real.exp l) := by
  have hφfun : φ = fun s => k^2 * Real.exp s := funext h157
  have hφ' : φ' l = k^2 * Real.exp l := by
    have := hφd l
    rw [hφfun] at this
    exact this.unique ((Real.hasDerivAt_exp l).const_mul (k^2))
  rw [hφ', h157, h158, add_zero]

/-- **ch17-160 (folio 200)** 算術法則 (5) に対応する幾何法則
f_q = Ae^{φ₁′(z) log(z_q/z) + ∫(φ₁(z)/z)dz + ψ₁(z_q)}。積分項は印刷ではプライムなしの φ₁
(phase9x の T-3) だが、直後の where 行 (ch17-161) の ∫(φ₁′(z)/z)dz で読む (Φ₁′ = φ₁′/z)。
対応は ch17-161 の修正形 (φ₁′(z) = −φ′(log z), Φ₁(z) = −φ(log z), ψ₁(z_q) = ψ(log z_q)) で:
y = log z の算術法則と z の幾何法則は一致する。 -/
theorem th_17_ii_l160 (A : ℝ) (φ φ' ψ φ₁' Φ₁ ψ₁ : ℝ → ℝ) (z zq : ℝ) (hz : 0 < z)
    (hzq : 0 < zq) (hφ : HasDerivAt φ (φ' (Real.log z)) (Real.log z))
    (hφ₁ : ∀ w, φ₁' w = -φ' (Real.log w)) (hΦ₁ : ∀ w, Φ₁ w = -φ (Real.log w))
    (hψ₁ : ∀ w, ψ₁ w = ψ (Real.log w)) :
    HasDerivAt Φ₁ (φ₁' z / z) z
      ∧ A * Real.exp (φ' (Real.log z) * (Real.log z - Real.log zq) - φ (Real.log z)
          + ψ (Real.log zq))
        = A * Real.exp (φ₁' z * Real.log (zq / z) + Φ₁ z + ψ₁ zq) := by
  constructor
  · have hfun : Φ₁ = fun w => -φ (Real.log w) := funext hΦ₁
    rw [hfun, hφ₁]
    have := (hφ.comp z (Real.hasDerivAt_log hz.ne')).neg
    convert this using 1
    field_simp
  · rw [hφ₁, hΦ₁, hψ₁, Real.log_div hzq.ne' hz.ne']
    congr 2
    ring

/-- (ii)-9 の同定の帰結 (phase9x th_17_1911_ii_9_src の写し): 印刷の
「∫φ₁′(z)/z dz = φ(log z)」は φ₁′(z) = φ′(log z) を強いる。 -/
theorem ii9_identify (φ φ' φ₁' Φ₁ : ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (hφ : HasDerivAt φ (φ' (Real.log z)) (Real.log z))
    (hΦ : HasDerivAt Φ₁ (φ₁' z / z) z)
    (hprinted : ∀ w, 0 < w → Φ₁ w = φ (Real.log w)) :
    φ₁' z = φ' (Real.log z) := by
  have h1 : HasDerivAt (fun w => φ (Real.log w)) (φ' (Real.log z) * z⁻¹) z :=
    hφ.comp z (Real.hasDerivAt_log hz.ne')
  have hfun : Φ₁ =ᶠ[nhds z] fun w => φ (Real.log w) := by
    filter_upwards [lt_mem_nhds hz] with w hw
    exact hprinted w hw
  have h2 : HasDerivAt Φ₁ (φ' (Real.log z) * z⁻¹) z := h1.congr_of_eventuallyEq hfun
  have := hΦ.unique h2
  field_simp at this
  linarith

/-- **ch17-161 (folio 200) 印刷形の反駁** (phase9x th_17_1911_ii_9_printed_fails の写し):
印刷の「∫(φ₁′(z)/z)dz = φ(log z)」を仮定すると、Keynes 自身の例 φ(l) = k²eˡ (ch17-157) で
z = 1, z_q = e のとき算術法則の指数 −2k² と幾何法則の指数 2k² が一致しない (k ≠ 0)。 -/
theorem th_17_ii_l161_printed_fails (k : ℝ) (hk : k ≠ 0) (φ₁' Φ₁ : ℝ → ℝ)
    (hΦ : ∀ z, 0 < z → HasDerivAt Φ₁ (φ₁' z / z) z)
    (hprinted : ∀ w, 0 < w → Φ₁ w = k^2 * Real.exp (Real.log w)) :
    ∃ z zq : ℝ, 0 < z ∧ 0 < zq ∧
      (k^2 * Real.exp (Real.log z)) * (Real.log z - Real.log zq) - k^2 * Real.exp (Real.log z)
        ≠ φ₁' z * Real.log (zq / z) + Φ₁ z := by
  refine ⟨1, Real.exp 1, one_pos, Real.exp_pos 1, ?_⟩
  have hφ : HasDerivAt (fun l => k^2 * Real.exp l) (k^2 * Real.exp (Real.log 1)) (Real.log 1) :=
    (Real.hasDerivAt_exp _).const_mul (k^2)
  have h1 : φ₁' 1 = k^2 * Real.exp (Real.log 1) :=
    ii9_identify (fun l => k^2 * Real.exp l) (fun l => k^2 * Real.exp l) φ₁' Φ₁ 1
      one_pos hφ (hΦ 1 one_pos) hprinted
  rw [h1, hprinted 1 one_pos]
  simp only [Real.log_one, Real.exp_zero, Real.log_exp, div_one, mul_one, zero_sub]
  intro h
  have hk2 : k^2 = 0 := by linarith
  exact hk (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk2)

/-- **ch17-161 (folio 200) 修正形** y = log z, y_q = log z_q, ∫(φ₁′(z)/z)dz = −φ(log z)
(φ₁′(z) = −φ′(log z))、ψ₁(z_q) = ψ(log z_q) のとき、算術法則の指数と幾何法則の指数は一致し、
−φ(log z) は確かに ∫(φ₁′(z)/z)dz (微分が φ₁′(z)/z)。印刷の符号 (+φ(log z)) は逆。 -/
theorem th_17_ii_l161 (φ φ' ψ φ₁' Φ₁ ψ₁ : ℝ → ℝ) (z zq y yq : ℝ) (hz : 0 < z) (hzq : 0 < zq)
    (hφ : HasDerivAt φ (φ' (Real.log z)) (Real.log z))
    (hy : y = Real.log z) (hyq : yq = Real.log zq)
    (hφ₁ : ∀ w, φ₁' w = -φ' (Real.log w)) (hΦ₁ : ∀ w, Φ₁ w = -φ (Real.log w))
    (hψ₁ : ∀ w, ψ₁ w = ψ (Real.log w)) :
    HasDerivAt Φ₁ (φ₁' z / z) z
      ∧ φ' y * (y - yq) - φ y + ψ yq = φ₁' z * Real.log (zq / z) + Φ₁ z + ψ₁ zq := by
  have h160 := th_17_ii_l160 1 φ φ' ψ φ₁' Φ₁ ψ₁ z zq hz hzq hφ hφ₁ hΦ₁ hψ₁
  refine ⟨h160.1, ?_⟩
  rw [hy, hyq, hφ₁, hΦ₁, hψ₁, Real.log_div hzq.ne' hz.ne']
  ring

/-! ## (iii) 調和平均・(iv) 中央値 (folio 200–202) -/

/-- **ch17-164, 165 (folio 200)** φ′(y) = −k²y², ψ(y_q) = −k²y_q を (10) に代入すると
f_q = Ae^{−k²(y − y_q)²/y_q} (∫(φ′(y)/y²)dy = −k²y + C の C は A に吸収)。
印刷の次行 ch17-166 は第 1 の指数の負号を欠く (phase9x の反駁)。 -/
theorem th_17_iii_l164 (A k yq : ℝ) (hyq : 0 < yq) (φ' Φ ψ : ℝ → ℝ)
    (h164 : ∀ s, φ' s = -(k^2) * s^2) (hΦ : ∀ s, 0 < s → HasDerivAt Φ (φ' s / s^2) s)
    (h165 : ψ yq = -(k^2) * yq) :
    ∃ C : ℝ, ∀ s, 0 < s →
      A * Real.exp (φ' s * (yq⁻¹ - s⁻¹) - Φ s + ψ yq)
        = (A * Real.exp C) * Real.exp (-(k^2) * (s - yq)^2 / yq) := by
  have hg : ∀ s, 0 < s → HasDerivAt (fun s => Φ s + k^2 * s) 0 s := by
    intro s hs
    have := (hΦ s hs).add ((hasDerivAt_id' s).const_mul (k^2))
    convert this using 1
    rw [h164 s]; field_simp; ring
  have hc := const_on_pos _ hg
  refine ⟨-(Φ 1 + k^2 * 1), fun s hs => ?_⟩
  have hΦs : Φ s = -(k^2) * s + (Φ 1 + k^2 * 1) := by
    have := hc s hs; simp only at this; linarith
  rw [h164 s, hΦs, h165, mul_assoc A, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- **ch17-170 (folio 201)** ∣y − y_q∣ = z_q (記号の約束) の下で、Σ z_q が最小なら
Σ(y − y_q)/z_q = 0 (y ≠ y_q)。 -/
theorem th_17_iv_l170 {m : ℕ} (y : Fin m → ℝ) (t : ℝ) (z : Fin m → ℝ → ℝ)
    (h170 : ∀ q s, |s - y q| = z q s) (hne : ∀ q, t ≠ y q)
    (hmin : IsLocalMin (fun s => ∑ q, z q s) t) :
    ∑ q, (t - y q) / z q t = 0 := by
  simp only [← h170] at hmin ⊢
  have hd : HasDerivAt (fun s => ∑ q, |s - y q|) (∑ q, (t - y q) / |t - y q|) t := by
    have := HasDerivAt.sum (u := Finset.univ) (A := fun q s => |s - y q|)
      (A' := fun q => (t - y q) / |t - y q|) (x := t)
      (fun q _ => hasDerivAt_abs_sub (y q) t (hne q))
    convert this using 1
    funext s
    simp [Finset.sum_apply]
  exact hmin.hasDerivAt_eq_zero hd

/-- **ch17-173 (folio 201)** f_q = Ae^{∫((y − y_q)/z_q)φ″(y)dy + ψ(y_q)} の停留条件は
Σ(y − y_q)/z_q = 0。∫ を原始関数 E_q (E_q′ = ((y − y_q)/z_q)φ″(y)) で、z_q を ∣y − y_q∣ で。 -/
theorem th_17_iv_l173 {m : ℕ} (A : ℝ) (φ'' ψ : ℝ → ℝ) (E : Fin m → ℝ → ℝ) (y : Fin m → ℝ)
    (t : ℝ) (hA : 0 < A) (hφ'' : φ'' t ≠ 0)
    (hE : ∀ q, HasDerivAt (E q) ((t - y q) / |t - y q| * φ'' t) t) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (E q s + ψ (y q)))) t = 0
      ↔ ∑ q, (t - y q) / |t - y q| = 0 :=
  stationary_general A (φ'' t) (fun q s => E q s + ψ (y q)) (fun q => (t - y q) / |t - y q|)
    t hA hφ'' (fun q => by
      have := (hE q).add_const (ψ (y q))
      convert this using 1
      ring)

/-- **ch17-174, 175 (folio 201)** φ″(y) = −k² (φ′ の積分定数は Keynes どおり 0)、
ψ(y_q) = ((y − y_q)/z_q)k²y_q、z_q = ∣y − y_q∣ を (12) に代入すると f_q = Ae^{−k²z_q}。
(この ψ は y − y_q の符号に依り、y_q だけの関数でない — phase9x の観察。) -/
theorem th_17_iv_l174 (A k t yq z : ℝ) (hne : t ≠ yq) (φ' φ'' ψ : ℝ → ℝ)
    (hd : ∀ s, HasDerivAt φ' (φ'' s) s) (h174 : ∀ s, φ'' s = -(k^2)) (h0 : φ' 0 = 0)
    (hz : |t - yq| = z) (h175 : ψ yq = ((t - yq) / z) * (k^2 * yq)) :
    A * Real.exp (φ' t * ((t - yq) / z) + ψ yq) = A * Real.exp (-(k^2) * z) := by
  have hg : ∀ s, HasDerivAt (fun s => φ' s + k^2 * s) 0 s := by
    intro s
    have := (hd s).add ((hasDerivAt_id' s).const_mul (k^2))
    convert this using 1
    rw [h174 s]; ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt)
    (fun s => (hg s).deriv)
  have hφt : φ' t = -(k^2) * t := by
    have := hconst t 0
    simp only [h0] at this
    linarith
  rw [hφt, h175, ← hz]
  congr 2
  have h0' : |t - yq| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hsq : (t - yq)^2 = |t - yq|^2 := (sq_abs _).symm
  field_simp
  linear_combination (-(k^2)) * hsq

/-- **ch17-178 (folio 202)** Laplace: z = φ(y) (z は誤差 y の確率; 前提)。Laplace の結果
φ(y) = (m/2)e^{−m∣y∣} の下で z = (m/2)e^{−my} (y ≥ 0; ch17-179 の修正形の値)。 -/
theorem th_17_iv_l178 (mm y z : ℝ) (φ : ℝ → ℝ) (hφ : ∀ w, φ w = (mm / 2) * Real.exp (-mm * |w|))
    (h178 : z = φ y) (hy : 0 ≤ y) :
    z = (mm / 2) * Real.exp (-mm * y) := by
  rw [h178, hφ, abs_of_nonneg hy]

/-! ## (vi) 対称誤差法則の特殊形・(3)・1921 加筆層 (folio 203–210) -/

/-- **ch17-187 (folio 203)** f(y − y_q)² = (y − y_q)² (前提) なら (2) の法則は
Ae^{−k²(y − y_q)²} = Ae^{−k²z_q²} で、停留条件は Σ(y − y_q) = 0 (算術平均)。 -/
theorem th_17_vi_l187 {m : ℕ} (A k : ℝ) (hA : 0 < A) (hk : k ≠ 0) (F : ℝ → ℝ)
    (y : Fin m → ℝ) (t : ℝ) (h187 : ∀ q s, F ((s - y q)^2) = (s - y q)^2) :
    (∀ q, A * Real.exp (-(k^2) * F ((t - y q)^2)) = A * Real.exp (-(k^2) * |t - y q|^2))
      ∧ (deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * F ((s - y q)^2)))) t = 0
          ↔ ∑ q, (t - y q) = 0) := by
  constructor
  · intro q; rw [h187, sq_abs]
  · simp only [h187]
    refine stationary_general A (-2 * k^2) (fun q s => -(k^2) * (s - y q)^2)
      (fun q => t - y q) t hA
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk)) (fun q => ?_)
    have := (((hasDerivAt_id' t).sub_const (y q)).pow 2).const_mul (-(k^2))
    convert this using 1
    ring

/-- **ch17-188 (folio 203)** f(y − y_q)² = +√((y − y_q)²) (前提) なら法則は Ae^{−k²∣y − y_q∣}
で、停留条件は Σ(y − y_q)/∣y − y_q∣ = 0 (中央値; y ≠ y_q)。 -/
theorem th_17_vi_l188 {m : ℕ} (A k : ℝ) (hA : 0 < A) (hk : k ≠ 0) (F : ℝ → ℝ)
    (y : Fin m → ℝ) (t : ℝ) (hne : ∀ q, t ≠ y q)
    (h188 : ∀ q s, F ((s - y q)^2) = Real.sqrt ((s - y q)^2)) :
    (∀ q, A * Real.exp (-(k^2) * F ((t - y q)^2)) = A * Real.exp (-(k^2) * |t - y q|))
      ∧ (deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * F ((s - y q)^2)))) t = 0
          ↔ ∑ q, (t - y q) / |t - y q| = 0) := by
  simp only [h188, Real.sqrt_sq_eq_abs]
  refine ⟨by simp, ?_⟩
  refine stationary_general A (-(k^2)) (fun q s => -(k^2) * |s - y q|)
    (fun q => (t - y q) / |t - y q|) t hA (neg_ne_zero.mpr (pow_ne_zero 2 hk)) (fun q => ?_)
  exact (hasDerivAt_abs_sub (y q) t (hne q)).const_mul (-(k^2))

/-- **ch17-189 (folio 203)** f(y − y_q)² = (y − y_q)⁴ (前提) なら法則は Ae^{−k²(y − y_q)⁴} で、
停留条件は Σ(y − y_q)³ = 0 (印刷の my³ − 3y²Σy_q + 3yΣy_q² − Σy_q³ = 0 の展開前)。 -/
theorem th_17_vi_l189 {m : ℕ} (A k : ℝ) (hA : 0 < A) (hk : k ≠ 0) (F : ℝ → ℝ)
    (y : Fin m → ℝ) (t : ℝ) (h189 : ∀ q s, F ((s - y q)^2) = (s - y q)^4) :
    (∀ q, A * Real.exp (-(k^2) * F ((t - y q)^2)) = A * Real.exp (-(k^2) * (t - y q)^4))
      ∧ (deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * F ((s - y q)^2)))) t = 0
          ↔ ∑ q, (t - y q)^3 = 0) := by
  simp only [h189]
  refine ⟨by simp, ?_⟩
  refine stationary_general A (-4 * k^2) (fun q s => -(k^2) * (s - y q)^4)
    (fun q => (t - y q)^3) t hA (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk)) (fun q => ?_)
  have := (((hasDerivAt_id' t).sub_const (y q)).pow 4).const_mul (-(k^2))
  convert this using 1
  ring

/-- **ch17-192 (folio 203)** f(y − y_q)² = log (y − y_q)² (前提) なら法則は
A ÷ (y − y_q)^{2k²} (y ≠ y_q; 2k² 乗する数は z_q = ∣y − y_q∣ と読む — phase9x vi_4_law と同じ)。 -/
theorem th_17_vi_l192 (A k t yq : ℝ) (hne : t ≠ yq) (F : ℝ → ℝ)
    (h192 : F ((t - yq)^2) = Real.log ((t - yq)^2)) :
    A * Real.exp (-(k^2) * F ((t - yq)^2)) = A / |t - yq| ^ (2 * k^2) := by
  have hpos : 0 < |t - yq| := abs_pos.mpr (sub_ne_zero.mpr hne)
  rw [h192, ← sq_abs (t - yq), Real.rpow_def_of_pos hpos, Real.log_pow, div_eq_mul_inv,
    ← Real.exp_neg]
  congr 2
  push_cast
  ring

/-- **ch17-201 (folio 204)** (3) z_q = ∣y − y_q∣ (記号の約束) の下で、法則 Ae^{−k²z_q²} の
停留条件は Σ(y − y_q) = 0 (算術平均)。 -/
theorem th_17_3_l201 {m : ℕ} (A k : ℝ) (hA : 0 < A) (hk : k ≠ 0) (y : Fin m → ℝ) (t : ℝ)
    (z : Fin m → ℝ → ℝ) (h201 : ∀ q s, z q s = |s - y q|) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * (z q s)^2))) t = 0
      ↔ ∑ q, (t - y q) = 0 := by
  simp only [h201, sq_abs]
  refine stationary_general A (-2 * k^2) (fun q s => -(k^2) * (s - y q)^2)
    (fun q => t - y q) t hA (mul_ne_zero (by norm_num) (pow_ne_zero 2 hk)) (fun q => ?_)
  have := (((hasDerivAt_id' t).sub_const (y q)).pow 2).const_mul (-(k^2))
  convert this using 1
  ring

/-- **ch17-212 (folio 207) 印刷形の反駁** N2「φ(x) = φ(0) + zφ′(0) + (z²/2!)φ″(0) + …」は
左辺が x (右辺は z)。x ≠ z では偽: φ(w) = w, x = 1, z = 0 で右辺の級数の和は 0、左辺は 1。 -/
theorem th_17_N2_l212_printed_fails :
    ∃ (φ : ℝ → ℝ) (x z : ℝ),
      ¬ HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ) * iteratedDeriv n φ 0) (φ x) := by
  refine ⟨fun w => w, 1, 0, fun hs => ?_⟩
  have h0 : (fun n : ℕ => (0 : ℝ) ^ n / (n.factorial : ℝ) * iteratedDeriv n (fun w : ℝ => w) 0)
      = fun _ => 0 := by
    funext n
    cases n with
    | zero => simp
    | succ n => simp
  rw [h0] at hs
  have := hs.unique hasSum_zero
  norm_num at this

/-- **ch17-212 (folio 207) 修正形** φ(z) = φ(0) + zφ′(0) + (z²/2!)φ″(0) + (z³/3!)φ‴(0) + …
(φ が 0 のまわりで冪級数に展開できる範囲; Maclaurin)。 -/
theorem th_17_N2_l212 (φ : ℝ → ℝ) (p : FormalMultilinearSeries ℝ ℝ ℝ) (r : ENNReal)
    (hφ : HasFPowerSeriesOnBall φ p 0 r) (z : ℝ) (hz : z ∈ Metric.eball (0 : ℝ) r) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ) * iteratedDeriv n φ 0) (φ z) := by
  have := hφ.hasSum_iteratedFDeriv hz
  rw [zero_add] at this
  convert this using 1
  funext n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, smul_eq_mul]
  field_simp

/-- **ch17-215 (folio 207) 印刷形の反駁** 「z⁴ を無視して φ(z) = φ(0) + ½z²φ″(0)」は
等式としては偽: 偶関数 φ(w) = w⁴ で φ(1) = 1、右辺は 0。 -/
theorem th_17_N3_l215_printed_fails :
    ∃ φ φ' φ'' : ℝ → ℝ, (∀ z, φ z = φ (-z)) ∧ (∀ z, HasDerivAt φ (φ' z) z)
      ∧ (∀ z, HasDerivAt φ' (φ'' z) z) ∧ φ 1 ≠ φ 0 + (1 / 2) * 1 ^ 2 * φ'' 0 := by
  refine ⟨fun w => w ^ 4, fun w => 4 * w ^ 3, fun w => 12 * w ^ 2, fun z => by ring,
    fun z => ?_, fun z => ?_, by norm_num⟩
  · have := hasDerivAt_pow 4 z
    convert this using 1
  · have := (hasDerivAt_pow 3 z).const_mul 4
    convert this using 1
    ring

/-- **ch17-215 (folio 207) 修正形** 三回連続微分可能な偶関数 φ について
φ(z) − (φ(0) + ½z²φ″(0)) = o(z³) (z → 0)。φ′(0) = φ‴(0) = 0 は偶関数性から導く (N3)。 -/
theorem th_17_N3_l215 (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (heven : ∀ z, φ z = φ (-z)) :
    (fun z => φ z - (φ 0 + (1 / 2) * z ^ 2 * iteratedDeriv 2 φ 0))
      =o[nhds 0] (fun z => z ^ 3) := by
  have hT := taylor_isLittleO_univ (x₀ := 0) (n := 3) hφ
  have hodd : ∀ n, Odd n → iteratedDeriv n φ 0 = 0 := by
    intro n hn
    have h1 := iteratedDeriv_comp_neg n φ 0
    have hfun : (fun x => φ (-x)) = φ := funext (fun x => (heven x).symm)
    rw [hfun, neg_zero, hn.neg_one_pow, smul_eq_mul] at h1
    linarith
  have hval : ∀ z, taylorWithinEval φ 3 Set.univ 0 z
      = φ 0 + (1 / 2) * z ^ 2 * iteratedDeriv 2 φ 0 := by
    intro z
    rw [taylor_within_apply]
    simp only [iteratedDerivWithin_univ, Finset.sum_range_succ, Finset.sum_range_zero,
      sub_zero, smul_eq_mul]
    rw [hodd 1 odd_one, hodd 3 (by decide)]
    simp [Nat.factorial]
  have hfun : (fun x => φ x - taylorWithinEval φ 3 Set.univ 0 x)
      = (fun z => φ z - (φ 0 + (1 / 2) * z ^ 2 * iteratedDeriv 2 φ 0)) :=
    funext (fun z => by rw [hval z])
  rw [hfun] at hT
  simpa only [sub_zero] using hT

/-- **ch17-216 (folio 207) 印刷形の反駁** 「a + bz² = ae^{bz²/a}」は等式としては偽:
a = b = z = 1 で 2 ≠ e。 -/
theorem th_17_N4_l216_printed_fails :
    ∃ a b z : ℝ, 0 < a ∧ a + b * z ^ 2 ≠ a * Real.exp (b * z ^ 2 / a) := by
  refine ⟨1, 1, 1, one_pos, fun h => ?_⟩
  have h2 : Real.exp 1 = 2 := by norm_num at h; linarith
  have := Real.exp_one_gt_d9
  linarith

/-- **ch17-216 (folio 207) 修正形** (phase9x th_17_1921_N4_order の写し) u = bz²/a, ∣u∣ ≤ 1 のとき
∣ae^{bz²/a} − (a + bz²)∣ ≤ b²z⁴/a: 差は z⁴ の大きさ。 -/
theorem th_17_N4_l216 (a b z : ℝ) (ha : 0 < a) (hu : |b * z^2 / a| ≤ 1) :
    |a * Real.exp (b * z^2 / a) - (a + b * z^2)| ≤ b^2 * z^4 / a := by
  have h := Real.abs_exp_sub_one_sub_id_le hu
  have h1 : a * Real.exp (b * z^2 / a) - (a + b * z^2)
      = a * (Real.exp (b * z^2 / a) - 1 - b * z^2 / a) := by
    field_simp
    ring
  rw [h1, abs_mul, abs_of_pos ha]
  calc a * |Real.exp (b * z^2 / a) - 1 - b * z^2 / a| ≤ a * (b * z^2 / a)^2 :=
        mul_le_mul_of_nonneg_left h ha.le
    _ = b^2 * z^4 / a := by
        field_simp

/-- **ch17-217 (folio 207) 印刷形の反駁** 「φ(z) = ae^{bz²/a}」(a = φ(0), b = ½φ″(0)) は
等式としては偽: 偶関数 φ(w) = 1 + w² で φ(1) = 2 ≠ e。 -/
theorem th_17_N4_l217_printed_fails :
    ∃ φ φ' φ'' : ℝ → ℝ, (∀ z, φ z = φ (-z)) ∧ (∀ z, HasDerivAt φ (φ' z) z)
      ∧ (∀ z, HasDerivAt φ' (φ'' z) z)
      ∧ φ 1 ≠ φ 0 * Real.exp ((1 / 2) * φ'' 0 * 1 ^ 2 / φ 0) := by
  refine ⟨fun w => 1 + w ^ 2, fun w => 2 * w, fun _ => 2, fun z => by ring,
    fun z => ?_, fun z => ?_, fun h => ?_⟩
  · have := (hasDerivAt_pow 2 z).const_add 1
    convert this using 1
    ring
  · have := (hasDerivAt_id' z).const_mul 2
    convert this using 1
    ring
  · have h2 : Real.exp 1 = 2 := by norm_num at h; linarith
    have := Real.exp_one_gt_d9
    linarith

/-- **ch17-217 (folio 207) 修正形** a > 0, ∣bz²/a∣ ≤ 1 のとき
∣φ(z) − ae^{bz²/a}∣ ≤ ∣φ(z) − (a + bz²)∣ + b²z⁴/a。a = φ(0), b = ½φ″(0) なら第 1 項は
th_17_N3_l215 により o(z³)、第 2 項は z⁴ の大きさ。 -/
theorem th_17_N4_l217 (φ : ℝ → ℝ) (a b z : ℝ) (ha : 0 < a) (hu : |b * z^2 / a| ≤ 1) :
    |φ z - a * Real.exp (b * z^2 / a)| ≤ |φ z - (a + b * z^2)| + b^2 * z^4 / a := by
  have h1 := th_17_N4_l216 a b z ha hu
  have h2 := abs_sub_le (φ z) (a + b * z^2) (a * Real.exp (b * z^2 / a))
  rw [abs_sub_comm (a + b * z^2)] at h2
  linarith

/-- **ch17-222 (folio 208)** N5: 観測値 x_r² に算術平均の原理を当てると、x² の最確値 X は
Σ(X − x_r²) = 0 ⟺ X = (1/n)Σx_r²。 -/
theorem th_17_N5_l222 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (X : ℝ) :
    ∑ r, (X - (x r)^2) = 0 ↔ X = (1 / n) * ∑ r, (x r)^2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  constructor
  · intro hh; field_simp; linarith
  · intro hh; rw [hh]; field_simp; ring

/-- **ch17-223 (folio 208)** N5: ((1/n)Σx_r)² ≠ (1/n)Σx_r² — 「一般には」の意味で:
等号は観測値がすべて等しいときに限る (印刷の ≠ は全称ではない; n ≥ 1)。 -/
theorem th_17_N5_l223 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ((1 / n) * ∑ r, x r)^2 ≠ (1 / n) * ∑ r, (x r)^2 ↔ ∃ r s, x r ≠ x s := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set μ := (1 / (n : ℝ)) * ∑ r, x r with hμ
  have hs : ∑ r, x r = n * μ := by rw [hμ]; field_simp
  have hexp : ∑ r, (x r - μ)^2 = ∑ r, (x r)^2 - 2 * μ * ∑ r, x r + n * μ^2 := by
    have : ∀ r, (x r - μ)^2 = (x r)^2 - 2 * μ * x r + μ^2 := fun r => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have key : (1 / (n : ℝ)) * ∑ r, (x r)^2 - μ^2 = (1 / n) * ∑ r, (x r - μ)^2 := by
    rw [hexp, hs]; field_simp; ring
  have hiff : μ^2 = (1 / (n : ℝ)) * ∑ r, (x r)^2 ↔ ∀ r, x r = μ := by
    constructor
    · intro h0
      have h1 : (1 / (n : ℝ)) * ∑ r, (x r - μ)^2 = 0 := by rw [← key]; linarith
      have h2 : ∑ r, (x r - μ)^2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h (one_div_ne_zero hn')
        · exact h
      intro r
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg (x r - μ))).mp h2 r
        (Finset.mem_univ r)
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    · intro hall
      have h2 : ∑ r, (x r - μ)^2 = 0 :=
        Finset.sum_eq_zero (fun r _ => by rw [hall r]; ring)
      rw [h2, mul_zero] at key
      linarith
  rw [Ne, hiff]
  constructor
  · intro h
    push Not at h
    obtain ⟨r, hr⟩ := h
    by_contra hc
    push Not at hc
    apply hr
    have : ∑ s, x s = n * x r := by
      rw [Finset.sum_congr rfl (fun s _ => hc s r), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hμ, this]
    field_simp
  · rintro ⟨r, s, hrs⟩ hall
    exact hrs (by rw [hall r, hall s])

/-- **ch17-224 (folio 208)** N5: (1/n)Σf(x_r) ≠ f((1/n)Σx_r) — 「一般には」の意味で:
そのような f があるのは観測値がすべて等しくはないときに限る (n ≥ 1)。 -/
theorem th_17_N5_l224 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (∃ f : ℝ → ℝ, (1 / n) * ∑ r, f (x r) ≠ f ((1 / n) * ∑ r, x r)) ↔ ∃ r s, x r ≠ x s := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · rintro ⟨f, hf⟩
    by_contra hc
    push Not at hc
    apply hf
    set r0 : Fin n := ⟨0, hn⟩
    have e1 : ∑ r, f (x r) = n * f (x r0) := by
      rw [Finset.sum_congr rfl (fun r _ => by rw [hc r r0]), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e2 : ∑ r, x r = n * x r0 := by
      rw [Finset.sum_congr rfl (fun r _ => hc r r0), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [e1, e2]
    field_simp
  · intro h
    refine ⟨fun u => u^2, fun heq => ?_⟩
    exact (th_17_N5_l223 hn x).mpr h heq.symm

/-- **ch17-226, 227, 228, 229 (folio 210)** N6: 観測方程式
a₁x₁ + a₂x₂ + … + aᵣxᵣ = V₁, b₁x₁ + … + bᵣxᵣ = V₂, …, k₁x₁ + … + kᵣxᵣ = Vₙ (n > r)。
係数 a, b, …, k を行列 A の行で書く。n > r なら、どんな係数についても、どの x でも
満たせない観測値 V がある (「there may be no precise solution whatever」)。 -/
theorem th_17_N6_l226 {n r : ℕ} (h229 : r < n) (A : Fin n → Fin r → ℝ) :
    ∃ V : Fin n → ℝ, ¬ ∃ x : Fin r → ℝ, ∀ i, ∑ j, A i j * x j = V i := by
  let L : (Fin r → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin (Matrix.of A)
  have hne : LinearMap.range L ≠ ⊤ := by
    intro htop
    have h1 := LinearMap.finrank_range_le L
    rw [htop, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨V, hV⟩ : ∃ V, V ∉ LinearMap.range L := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.mpr (fun v _ => hall v))
  refine ⟨V, fun ⟨x, hx⟩ => hV ⟨x, ?_⟩⟩
  funext i
  simp [L, Matrix.mulVec, dotProduct, hx i]

/-- **ch17-230 (folio 210)** N7: 正規法則 y = ke^{−h²x²} (前提; 係数 k と指数の h は別の文字)。
誤差 x = s − y_q についてこの法則の対数尤度の停留条件は Σ(y − y_q) = 0 (算術平均)。 -/
theorem th_17_N7_l230 {m : ℕ} (k h : ℝ) (hk : 0 < k) (hh : h ≠ 0) (g : ℝ → ℝ)
    (h230 : ∀ x, g x = k * Real.exp (-(h^2) * x^2)) (y : Fin m → ℝ) (t : ℝ) :
    deriv (fun s => ∑ q, Real.log (g (s - y q))) t = 0 ↔ ∑ q, (t - y q) = 0 := by
  simp only [h230]
  refine stationary_general k (-2 * h^2) (fun q s => -(h^2) * (s - y q)^2)
    (fun q => t - y q) t hk (mul_ne_zero (by norm_num) (pow_ne_zero 2 hh)) (fun q => ?_)
  have := (((hasDerivAt_id' t).sub_const (y q)).pow 2).const_mul (-(h^2))
  convert this using 1
  ring

end KeynesLawOfError

/-! # 監査クエリ (全定理) -/

-- 補題 (phase6c・phase9x の写しを含む) も含め、本ファイルの theorem をすべて列挙する。
-- 第 I 部の定理は KeynesI の公理のみ、Erratum57 と KeynesLawOfError は Lean 標準の
-- propext / Classical.choice / Quot.sound のみに依ることを確かめる。
#print axioms KeynesI.itrue_certain
#print axioms KeynesI.true_conj
#print axioms KeynesI.th_13_1_i
#print axioms KeynesI.taut_neg_zero
#print axioms KeynesI.conj_neg_cert_zero
#print axioms KeynesI.th_12_i_short
#print axioms KeynesI.subst_taut
#print axioms KeynesI.th_24_i
#print axioms KeynesI.conj_assoc_i
#print axioms KeynesI.conj_swap_i
#print axioms KeynesI.conj_dneg_i
#print axioms KeynesI.th_17_56_raw_i
#print axioms KeynesI.th_17_56_l002
#print axioms KeynesI.th_17_56_l004
#print axioms KeynesI.th_17_56_l005
#print axioms KeynesI.th_17_56_l014
#print axioms KeynesI.th_17_56_l017
#print axioms KeynesI.th_17_56_l018
#print axioms KeynesI.th_17_56_l021
#print axioms KeynesI.th_17_56_l023
#print axioms KeynesI.th_17_56_l025
#print axioms KeynesI.th_17_56_l035
#print axioms KeynesI.th_17_56_l036
#print axioms KeynesI.th_17_57_l039
#print axioms KeynesI.th_17_57_l040
#print axioms KeynesI.th_17_57_l041
#print axioms KeynesI.th_17_57_l042
#print axioms KeynesI.th_17_57_l043
#print axioms KeynesI.th_17_57_l044
#print axioms KeynesI.th_17_57_l045
#print axioms KeynesI.th_17_57_l046
#print axioms KeynesI.nb_succ
#print axioms KeynesI.th_17_57_l047
#print axioms KeynesI.th_17_57_l048
#print axioms KeynesI.th_17_57_l049
#print axioms KeynesI.th_17_57_l050
#print axioms KeynesI.th_17_57_l051
#print axioms KeynesI.th_17_57_l054
#print axioms KeynesI.th_17_57_l057
#print axioms KeynesI.term57_i
#print axioms KeynesI.th_17_57_l058
#print axioms KeynesI.th_17_57_l059
#print axioms KeynesI.one_sub_prod_le_sum
#print axioms KeynesI.nterm_bounds
#print axioms KeynesI.th_17_57_l067
#print axioms KeynesI.term57_4_i
#print axioms KeynesI.th_17_57_l069
#print axioms KeynesI.th_17_57_l070
#print axioms KeynesI.th_17_57_l072
#print axioms KeynesI.xc_succ
#print axioms KeynesI.th_17_58_l079
#print axioms KeynesI.q58
#print axioms KeynesI.chain_pos58
#print axioms KeynesI.chain_neg58
#print axioms KeynesI.closed58
#print axioms KeynesI.th_17_58_l080
#print axioms KeynesI.th_17_58_l081
#print axioms KeynesI.th_17_58_l082
#print axioms KeynesI.th_17_58_l083
#print axioms KeynesI.th_17_58_l084
#print axioms KeynesI.th_17_58_l085
#print axioms KeynesI.y_ratio58
#print axioms KeynesI.th_17_58_l093
#print axioms KeynesI.th_17_58_l095
#print axioms KeynesI.th_17_58_l096
#print axioms KeynesI.th_17_58_l098
#print axioms KeynesI.th_17_58_l098_printed_fails
#print axioms Erratum57.cards
#print axioms Erratum57.th_17_57_pairwise_only
#print axioms Erratum57.th_17_57_l059_printed_fails
#print axioms Erratum57.th_17_57_l070_printed_fails
#print axioms Erratum57.th_17_57_l072_printed_fails
#print axioms KeynesI.th_17_U8_l109
#print axioms KeynesLawOfError.stationary_general
#print axioms KeynesLawOfError.const_on_pos
#print axioms KeynesLawOfError.hasDerivAt_abs_sub
#print axioms KeynesLawOfError.i6_deriv
#print axioms KeynesLawOfError.i6_integrate
#print axioms KeynesLawOfError.i6_sign
#print axioms KeynesLawOfError.th_17_N1_l114
#print axioms KeynesLawOfError.th_17_i_l122
#print axioms KeynesLawOfError.th_17_i_l125
#print axioms KeynesLawOfError.th_17_i_l132
#print axioms KeynesLawOfError.th_17_i_l135
#print axioms KeynesLawOfError.th_17_ii_l136
#print axioms KeynesLawOfError.th_17_ii_l141
#print axioms KeynesLawOfError.th_17_ii_l144
#print axioms KeynesLawOfError.th_17_ii_l147
#print axioms KeynesLawOfError.th_17_ii_l150
#print axioms KeynesLawOfError.th_17_ii_l152
#print axioms KeynesLawOfError.th_17_ii_l154
#print axioms KeynesLawOfError.th_17_ii_l157
#print axioms KeynesLawOfError.th_17_ii_l160
#print axioms KeynesLawOfError.ii9_identify
#print axioms KeynesLawOfError.th_17_ii_l161_printed_fails
#print axioms KeynesLawOfError.th_17_ii_l161
#print axioms KeynesLawOfError.th_17_iii_l164
#print axioms KeynesLawOfError.th_17_iv_l170
#print axioms KeynesLawOfError.th_17_iv_l173
#print axioms KeynesLawOfError.th_17_iv_l174
#print axioms KeynesLawOfError.th_17_iv_l178
#print axioms KeynesLawOfError.th_17_vi_l187
#print axioms KeynesLawOfError.th_17_vi_l188
#print axioms KeynesLawOfError.th_17_vi_l189
#print axioms KeynesLawOfError.th_17_vi_l192
#print axioms KeynesLawOfError.th_17_3_l201
#print axioms KeynesLawOfError.th_17_N2_l212_printed_fails
#print axioms KeynesLawOfError.th_17_N2_l212
#print axioms KeynesLawOfError.th_17_N3_l215_printed_fails
#print axioms KeynesLawOfError.th_17_N3_l215
#print axioms KeynesLawOfError.th_17_N4_l216_printed_fails
#print axioms KeynesLawOfError.th_17_N4_l216
#print axioms KeynesLawOfError.th_17_N4_l217_printed_fails
#print axioms KeynesLawOfError.th_17_N4_l217
#print axioms KeynesLawOfError.th_17_N5_l222
#print axioms KeynesLawOfError.th_17_N5_l223
#print axioms KeynesLawOfError.th_17_N5_l224
#print axioms KeynesLawOfError.th_17_N6_l226
#print axioms KeynesLawOfError.th_17_N7_l230
