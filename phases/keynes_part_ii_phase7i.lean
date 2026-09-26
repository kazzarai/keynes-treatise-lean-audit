/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7i
#
# 新井一成・Claude共著、2026年9月26日
# **1921年初版頁画像との三者照合 (画像 / Gutenberg tex / Lean) の後始末**
#
# ## 経緯
#   2026-09-26、Macmillan 1921 初版 (Cornell 蔵書スキャン、archive.org
#   cu31924014110435) の頁画像を唯一の基準として台帳 100 項目を再照合した。
#   佐藤訳画像 + Gutenberg tex による 7f 照合では捕捉できなかった逸脱が
#   13 本 (Lean の定理文が印刷命題と一致しない) と、原著側の新規正誤候補
#   5 本が見つかった。本ファイルはその全件を**印刷形そのまま**の定理として
#   再形式化し、原著側の誤りは (34) と同じ規律 — 印刷形の機械反駁 + 修正形の
#   検証 — で確定させる。
#
# ## 原則
#   基準は 1921 年版の印刷。tex・佐藤訳・既存 Lean はすべて補助。
#   一本の逸脱も残さない。
#
# ## 収録 (印刷 folio = 1921年版の印字頁)
#   A. 印刷形の再定理化 (旧 Lean が印刷命題と異なっていたもの)
#     (2)(3) folio 139 — 選言形 (a/h<1 ∨ a/h=1), (a/h>0 ∨ a/h=0)
#     (10)   folio 140 — 三項等式 ab/h = b/ah = b/h の両方
#     (11)   folio 141 — 結論は a/h = 1 (旧 Lean は a/bh = 1)
#     (37)   folio 148 — 前提は連鎖条件付き確率の等値 (旧 Lean は全証拠定数)
#     (38.1) folio 148 — 一般二択 a₁/bh + a₂/bh = 1 (旧 Lean は a₂ := ā₁)
#     (43)   folio 151 — 分離因子の係数恒等式そのもの (2 例とも)
#     (46.2) folio 153 — 2 文字・二択の正しい形 (印刷の添字は不整合、下記 B)
#     (49.1) folio 155 — 排反網羅な選択肢に対する係数分解 + 単調性の系 (2 文字)
#     (56.4) folio 189 — 下限と 2 つの上限
#     (57.1) folio 190 — Π 係数つきの等式そのもの (独立性の下)
#     (57.2) folio 191 — 下限 c_rp_r と上限 1−c_r(1−p_r), Σc_rp_r (独立性なし)
#     (57.3) folio 191 — Π 係数形の下界 (独立性の下)
#   B. 原著側の誤り (印刷形の機械反駁)
#     (35)   folio 148 — 非狭義の前提では結論が破れる (8 領域反例)
#     (46.1) folio 152 — (x/h)ⁿ の因子欠落: 比例関係が破れる (8 領域反例)
#     (52)(53) folio 162 — 狭義不等号は等号事例で破れる
#     (58.2) folio 193 — 分子の因子 (1−q) が一つ不足 (a=1/2, p=3/4, n=2)
#     (58.3) folio 193 — 閉形式の指数が一つ過大 (n=1 で a/p にならない)
#     (46.2) は添字の不整合 (Π^{n−1} と (x/h)^{−n}) で、解釈を固定しない限り
#     反駁できない → 正しい形 (A) のみ与える
#   C. 撤回: (33) の「原典散文が証明と逆向き」(7d ヘッダ) は Gutenberg の
#     転記誤り ("not more") であり、1921 年版は "not less" で整合。正誤表から外す。
#
# ## 実行方法 (Mac ローカル)
#   lake env lean phases/keynes_part_ii_phase7i.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (継承) -/

axiom Pr : Prop → Prop → ℝ
axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1
axiom def_IX (p q h : Prop) :
    Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h
axiom def_X_left (p q h : Prop) :
    Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h
axiom def_X_right (p q h : Prop) :
    Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h
axiom ax_range_lo (α h : Prop) : 0 ≤ Pr α h
axiom ax_range_hi (α h : Prop) : Pr α h ≤ 1

/-! ## リスト補助補題 (Mathlib の補題名に依存しない自前版) -/

theorem list_sum_div {α : Type} (f : α → ℝ) (c : ℝ) :
    ∀ xs : List α, (xs.map f).sum / c = (xs.map (fun x => f x / c)).sum := by
  intro xs
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [add_div, ih]

theorem list_sum_congr {α : Type} (f g : α → ℝ) :
    ∀ xs : List α, (∀ x ∈ xs, f x = g x) → (xs.map f).sum = (xs.map g).sum := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons y ys ih =>
      intro hfg
      simp only [List.map_cons, List.sum_cons]
      rw [hfg y List.mem_cons_self,
          ih (fun x hx => hfg x (List.mem_cons_of_mem y hx))]

theorem list_sum_le {α : Type} (f g : α → ℝ) :
    ∀ xs : List α, (∀ x ∈ xs, f x ≤ g x) → (xs.map f).sum ≤ (xs.map g).sum := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons y ys ih =>
      intro hfg
      simp only [List.map_cons, List.sum_cons]
      have h1 := hfg y List.mem_cons_self
      have h2 := ih (fun x hx => hfg x (List.mem_cons_of_mem y hx))
      linarith

theorem list_sum_nonneg' {α : Type} (f : α → ℝ) :
    ∀ xs : List α, (∀ x ∈ xs, 0 ≤ f x) → 0 ≤ (xs.map f).sum := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons y ys ih =>
      intro hf
      simp only [List.map_cons, List.sum_cons]
      have h1 := hf y List.mem_cons_self
      have h2 := ih (fun x hx => hf x (List.mem_cons_of_mem y hx))
      linarith

/-- 恒等式 w·A·B = w + (wA − w) + (wB − w) + w(A−1)(B−1) のリスト和版。 -/
theorem list_sum_expand {α : Type} (w A B : α → ℝ) :
    ∀ xs : List α,
      (xs.map (fun x => w x * A x * B x)).sum
        = (xs.map w).sum
          + ((xs.map (fun x => w x * A x)).sum - (xs.map w).sum)
          + ((xs.map (fun x => w x * B x)).sum - (xs.map w).sum)
          + (xs.map (fun x => w x * ((A x - 1) * (B x - 1)))).sum := by
  intro xs
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons]
      have key : w y * A y * B y
          = w y + (w y * A y - w y) + (w y * B y - w y) + w y * ((A y - 1) * (B y - 1)) := by
        ring
      linarith [ih, key]

/-! ## 補助補題 (6b/7h から継承) -/

theorem th_13_1 (α h : Prop) : Pr α h + Pr (¬α) h = 1 := by
  have step := def_IX True α h
  have e1 : (True ∧ ¬α) ↔ ¬α := by tauto
  have e2 : (True ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, ax_iii_true] at step
  linarith

theorem pr_false (h : Prop) : Pr False h = 0 := by
  have step := def_IX False False h
  have e1 : (False ∧ ¬False) ↔ False := by tauto
  have e2 : (False ∧ False) ↔ False := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at step
  linarith

theorem th_24 (α β h : Prop) :
    Pr (α ∨ β) h = Pr α h + Pr β h - Pr (α ∧ β) h := by
  have step1 : Pr ((α ∨ β) ∧ ¬β) h + Pr ((α ∨ β) ∧ β) h = Pr (α ∨ β) h :=
    def_IX (α ∨ β) β h
  have eq1 : ((α ∨ β) ∧ ¬β) ↔ (α ∧ ¬β) := by tauto
  have eq2 : ((α ∨ β) ∧ β) ↔ β := by tauto
  rw [ax_iii_op _ _ h eq1, ax_iii_op _ _ h eq2] at step1
  have step3 : Pr (α ∧ ¬β) h + Pr (α ∧ β) h = Pr α h :=
    def_IX α β h
  linarith

theorem pr_conj_le_left (α y h : Prop) : Pr (α ∧ y) h ≤ Pr α h := by
  have h9 := def_IX α y h
  have hlo := ax_range_lo (α ∧ ¬y) h
  linarith

theorem pr_conj_le_right (α y h : Prop) : Pr (α ∧ y) h ≤ Pr y h := by
  have h9 := def_IX y α h
  have hlo := ax_range_lo (y ∧ ¬α) h
  have e : (y ∧ α) ↔ (α ∧ y) := by tauto
  rw [ax_iii_op _ _ h e] at h9
  linarith

theorem th_13_7 (α β h k : Prop) (hmul : Pr α h * Pr β k = 1) :
    Pr α h = 1 ∧ Pr β k = 1 := by
  have hx0 := ax_range_lo α h
  have hx1 := ax_range_hi α h
  have hy0 := ax_range_lo β k
  have hy1 := ax_range_hi β k
  have k1 : Pr α h * Pr β k ≤ Pr β k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hy0]
  have k2 : Pr α h * Pr β k ≤ Pr α h := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hy1)]
  constructor <;> linarith

def bigAnd : List Prop → Prop
  | [] => True
  | p :: rest => p ∧ bigAnd rest

/-! ## A. 印刷形の再定理化 -/

/-- **(2) 印刷形** (folio 139): `a/h < 1 or a/h = 1` — by IV. -/
theorem th_13_2_src (α h : Prop) : Pr α h < 1 ∨ Pr α h = 1 :=
  lt_or_eq_of_le (ax_range_hi α h)

/-- **(3) 印刷形** (folio 139): `a/h > 0 or a/h = 0` — by V. -/
theorem th_13_3_src (α h : Prop) : 0 < Pr α h ∨ Pr α h = 0 := by
  rcases lt_or_eq_of_le (ax_range_lo α h) with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr heq.symm

/-- **(10) 印刷形** (folio 140): `If a/h = 1, ab/h = b/ah = b/h`.
旧 th_13_10 は `ab/h = b/h` のみ。ここでは三項等式の両方を与える。
(印刷の「unless b/h = 0」は不要: 中項の等式は X から直ちに出る。) -/
theorem th_13_10_src (α b h : Prop) (hcert : Pr α h = 1) :
    Pr (α ∧ b) h = Pr b (α ∧ h) ∧ Pr b (α ∧ h) = Pr b h := by
  have hX := def_X_right α b h
  rw [hcert, mul_one] at hX
  have hcompl := th_13_1 α h
  have hneg : Pr (¬α) h = 0 := by linarith
  have h9 := def_IX b α h
  have hz : Pr (b ∧ ¬α) h = 0 := by
    have hub := pr_conj_le_right b (¬α) h
    have hlo := ax_range_lo (b ∧ ¬α) h
    linarith
  have e : (b ∧ α) ↔ (α ∧ b) := by tauto
  rw [ax_iii_op _ _ h e] at h9
  constructor
  · exact hX
  · linarith

/-- **(11) 印刷形** (folio 141): `If ab/h = 1, a/h = 1` — by X. and (7).
旧 th_13_11 の結論 `a/bh = 1` は別命題 (こちらも成立するので併記)。 -/
theorem th_13_11_src (α b h : Prop) (h1 : Pr (α ∧ b) h = 1) :
    Pr α h = 1 ∧ Pr α (b ∧ h) = 1 := by
  have hr := def_X_right α b h
  rw [h1] at hr
  have hl := def_X_left α b h
  rw [h1] at hl
  exact ⟨(th_13_7 b α (α ∧ h) h hr.symm).2, (th_13_7 α b (b ∧ h) h hl.symm).1⟩

/-- 連鎖条件付き確率の等値 (印刷 (37) の前提そのもの):
リスト `[pₙ, …, p₁]` に対し `p₁/h = v, p₂/p₁h = v, …` を再帰的に述べる
(各要素はそれより後ろの要素の連言を条件とする)。 -/
def ChainEq (h : Prop) (v : ℝ) : List Prop → Prop
  | [] => True
  | p :: rest => Pr p (bigAnd rest ∧ h) = v ∧ ChainEq h v rest

/-- **(37) 印刷形** (folio 148): `If p₁/h = p₂/p₁h = p₃/p₁p₂h = …,
p₁p₂p₃…pₙ/h = {p₁/h}ⁿ` — by repeated applications of X.
旧 th_14_37_full の前提 `∀ p ∈ l, ∀ e, Pr p e = v` は印刷より大幅に強い。
ここでは印刷どおり、連鎖の各段の条件付き確率の等値だけを仮定する。 -/
theorem th_14_37_src (h : Prop) (v : ℝ) :
    ∀ l : List Prop, ChainEq h v l → Pr (bigAnd l) h = v ^ l.length := by
  intro l
  induction l with
  | nil =>
      intro _
      simp only [bigAnd, List.length_nil, pow_zero]
      exact ax_iii_true h
  | cons p rest ih =>
      intro hc
      rcases hc with ⟨hp, hrest⟩
      simp only [bigAnd, List.length_cons]
      rw [def_X_left p (bigAnd rest) h, hp, ih hrest]
      ring

/-- **(38.1) 印刷形** (folio 148–149): `If a₁/h = p₁, a₂/h = p₂, b/a₁h = q₁,
b/a₂h = q₂, and a₁/bh + a₂/bh = 1, then a₁/bh = p₁q₁/(p₁q₁ + p₂q₂)`
(and a₂/bh = p₂q₂/(p₁q₁ + p₂q₂)).
a₂ は自由な命題 (旧 th_14_48_binary は a₂ := ā₁ の特殊化)。
除算のため b/h ≠ 0 を要する (印刷 (38) の「provided bh is consistent」)。 -/
theorem th_14_38_1_src (a₁ a₂ b h : Prop) (p₁ p₂ q₁ q₂ : ℝ)
    (hp₁ : Pr a₁ h = p₁) (hp₂ : Pr a₂ h = p₂)
    (hq₁ : Pr b (a₁ ∧ h) = q₁) (hq₂ : Pr b (a₂ ∧ h) = q₂)
    (hsum : Pr a₁ (b ∧ h) + Pr a₂ (b ∧ h) = 1)
    (hb : Pr b h ≠ 0) :
    Pr a₁ (b ∧ h) = p₁ * q₁ / (p₁ * q₁ + p₂ * q₂) ∧
    Pr a₂ (b ∧ h) = p₂ * q₂ / (p₁ * q₁ + p₂ * q₂) := by
  have e₁l := def_X_left a₁ b h
  have e₁r := def_X_right a₁ b h
  have e₂l := def_X_left a₂ b h
  have e₂r := def_X_right a₂ b h
  rw [hq₁, hp₁] at e₁r
  rw [hq₂, hp₂] at e₂r
  have k₁ : Pr a₁ (b ∧ h) * Pr b h = p₁ * q₁ := by rw [← e₁l, e₁r]; ring
  have k₂ : Pr a₂ (b ∧ h) * Pr b h = p₂ * q₂ := by rw [← e₂l, e₂r]; ring
  have hS : Pr b h = p₁ * q₁ + p₂ * q₂ := by
    have : (Pr a₁ (b ∧ h) + Pr a₂ (b ∧ h)) * Pr b h = p₁ * q₁ + p₂ * q₂ := by
      rw [add_mul, k₁, k₂]
    rw [hsum, one_mul] at this
    exact this
  have hS0 : p₁ * q₁ + p₂ * q₂ ≠ 0 := by rw [← hS]; exact hb
  constructor
  · rw [eq_div_iff hS0, ← hS]; exact k₁
  · rw [eq_div_iff hS0, ← hS]; exact k₂

/-! ### 係数 (Def. XV/XVI, folio 150–151) -/

/-- 2 項係数 {p^h q} = pq/h ÷ (p/h · q/h)。 -/
noncomputable def coef2 (p q h : Prop) : ℝ :=
  Pr (p ∧ q) h / (Pr p h * Pr q h)

/-- 3 項係数 {p^h q^h r} = pqr/h ÷ (p/h · q/h · r/h)。 -/
noncomputable def coef3 (p q r h : Prop) : ℝ :=
  Pr (p ∧ (q ∧ r)) h / (Pr p h * Pr q h * Pr r h)

/-- 4 項係数 {p^h q^h r^h s}。 -/
noncomputable def coef4 (p q r s h : Prop) : ℝ :=
  Pr (p ∧ (q ∧ (r ∧ s))) h / (Pr p h * Pr q h * Pr r h * Pr s h)

/-- **(43) 印刷形** (folio 151): `{ab^h cd^h e} · {a^h b} = {a^h b^h cd^h e}`
— 「分離因子は乗数として、被乗数の中で結合されている項を分離する」。
{ab^h cd^h e} は 3 項係数 coef3 (a∧b) (c∧d) e、{a^h b^h cd^h e} は
4 項係数 coef4 a b (c∧d) e。分母因子は非零を要する。 -/
theorem th_14_43_src (a b c d e h : Prop)
    (hab : Pr (a ∧ b) h ≠ 0) (ha : Pr a h ≠ 0) (hb : Pr b h ≠ 0)
    (hcd : Pr (c ∧ d) h ≠ 0) (he : Pr e h ≠ 0) :
    coef3 (a ∧ b) (c ∧ d) e h * coef2 a b h = coef4 a b (c ∧ d) e h := by
  unfold coef3 coef2 coef4
  have eassoc : ((a ∧ b) ∧ ((c ∧ d) ∧ e)) ↔ (a ∧ (b ∧ ((c ∧ d) ∧ e))) := by tauto
  rw [ax_iii_op _ _ h eassoc]
  field_simp
  try ring

/-- **(43) 第 2 例** (folio 151): `{abc^h d^h ef} · {ab^h c} · {a^h b} = {a^h b^h c^h d^h ef}`. -/
theorem th_14_43_src_2 (a b c d e f h : Prop)
    (habc : Pr (a ∧ (b ∧ c)) h ≠ 0) (hab : Pr (a ∧ b) h ≠ 0)
    (ha : Pr a h ≠ 0) (hb : Pr b h ≠ 0) (hc : Pr c h ≠ 0)
    (hd : Pr d h ≠ 0) (hef : Pr (e ∧ f) h ≠ 0) :
    coef3 (a ∧ (b ∧ c)) d (e ∧ f) h * coef2 (a ∧ b) c h * coef2 a b h
      = Pr (a ∧ (b ∧ (c ∧ (d ∧ (e ∧ f))))) h
          / (Pr a h * Pr b h * Pr c h * Pr d h * Pr (e ∧ f) h) := by
  unfold coef3 coef2
  have e1 : ((a ∧ (b ∧ c)) ∧ (d ∧ (e ∧ f))) ↔ (a ∧ (b ∧ (c ∧ (d ∧ (e ∧ f))))) := by tauto
  have e2 : ((a ∧ b) ∧ c) ↔ (a ∧ (b ∧ c)) := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2]
  field_simp
  try ring

/-- **(46.2) の正しい形・2 文字二択版** (folio 153 の添字を整合させたもの)。
文字 a, b (n+1 = 2, n = 1)、選択肢 x, x̄ について、
T(x') := (x'/h)⁻¹ {a^{x'h} b} x'/ah · x'/bh とおくと
`x/hab · (T(x) + T(x̄)) = T(x)` — すなわち x/hab = T(x)/(T(x)+T(x̄))。
(印刷の Π^{n−1} は n=1 で空積となり左辺に一致しない。) 分母因子は非零を要する。 -/
theorem th_14_46_2_src2 (a b x h : Prop)
    (hx : Pr x h ≠ 0) (hnx : Pr (¬x) h ≠ 0)
    (ha : Pr a h ≠ 0) (hb : Pr b h ≠ 0)
    (hax : Pr a (x ∧ h) ≠ 0) (hbx : Pr b (x ∧ h) ≠ 0)
    (hanx : Pr a (¬x ∧ h) ≠ 0) (hbnx : Pr b (¬x ∧ h) ≠ 0)
    (hab : Pr (a ∧ b) h ≠ 0) :
    Pr x ((a ∧ b) ∧ h)
      * ((Pr x h)⁻¹ * coef2 a b (x ∧ h) * Pr x (a ∧ h) * Pr x (b ∧ h)
         + (Pr (¬x) h)⁻¹ * coef2 a b (¬x ∧ h) * Pr (¬x) (a ∧ h) * Pr (¬x) (b ∧ h))
      = (Pr x h)⁻¹ * coef2 a b (x ∧ h) * Pr x (a ∧ h) * Pr x (b ∧ h) := by
  -- 条件付き量を h 上の同時確率に還元する
  have r1 : Pr x (a ∧ h) = Pr (a ∧ x) h / Pr a h := by
    rw [eq_div_iff ha]; exact (def_X_right a x h).symm
  have r2 : Pr x (b ∧ h) = Pr (b ∧ x) h / Pr b h := by
    rw [eq_div_iff hb]; exact (def_X_right b x h).symm
  have r3 : Pr (¬x) (a ∧ h) = Pr (a ∧ ¬x) h / Pr a h := by
    rw [eq_div_iff ha]; exact (def_X_right a (¬x) h).symm
  have r4 : Pr (¬x) (b ∧ h) = Pr (b ∧ ¬x) h / Pr b h := by
    rw [eq_div_iff hb]; exact (def_X_right b (¬x) h).symm
  have s1 : Pr (a ∧ b) (x ∧ h) = Pr ((a ∧ b) ∧ x) h / Pr x h := by
    rw [eq_div_iff hx]; exact (def_X_left (a ∧ b) x h).symm
  have s2 : Pr a (x ∧ h) = Pr (a ∧ x) h / Pr x h := by
    rw [eq_div_iff hx]; exact (def_X_left a x h).symm
  have s3 : Pr b (x ∧ h) = Pr (b ∧ x) h / Pr x h := by
    rw [eq_div_iff hx]; exact (def_X_left b x h).symm
  have s4 : Pr (a ∧ b) (¬x ∧ h) = Pr ((a ∧ b) ∧ ¬x) h / Pr (¬x) h := by
    rw [eq_div_iff hnx]; exact (def_X_left (a ∧ b) (¬x) h).symm
  have s5 : Pr a (¬x ∧ h) = Pr (a ∧ ¬x) h / Pr (¬x) h := by
    rw [eq_div_iff hnx]; exact (def_X_left a (¬x) h).symm
  have s6 : Pr b (¬x ∧ h) = Pr (b ∧ ¬x) h / Pr (¬x) h := by
    rw [eq_div_iff hnx]; exact (def_X_left b (¬x) h).symm
  have t1 : Pr x ((a ∧ b) ∧ h) = Pr ((a ∧ b) ∧ x) h / Pr (a ∧ b) h := by
    rw [eq_div_iff hab]; exact (def_X_right (a ∧ b) x h).symm
  have hax' : Pr (a ∧ x) h ≠ 0 := by
    rw [def_X_left a x h]; exact mul_ne_zero hax hx
  have hbx' : Pr (b ∧ x) h ≠ 0 := by
    rw [def_X_left b x h]; exact mul_ne_zero hbx hx
  have hanx' : Pr (a ∧ ¬x) h ≠ 0 := by
    rw [def_X_left a (¬x) h]; exact mul_ne_zero hanx hnx
  have hbnx' : Pr (b ∧ ¬x) h ≠ 0 := by
    rw [def_X_left b (¬x) h]; exact mul_ne_zero hbnx hnx
  have hsplit : Pr ((a ∧ b) ∧ ¬x) h + Pr ((a ∧ b) ∧ x) h = Pr (a ∧ b) h :=
    def_IX (a ∧ b) x h
  have hsum0 : Pr ((a ∧ b) ∧ ¬x) h + Pr ((a ∧ b) ∧ x) h ≠ 0 := by rw [hsplit]; exact hab
  unfold coef2
  rw [t1, r1, r2, r3, r4, s1, s2, s3, s4, s5, s6, ← hsplit]
  field_simp
  try ring

/-- **(49.1) 印刷形・2 文字版** (folio 155): 排反網羅な選択肢 x, x', x'' … に対し
`{a^h b} = Σ_x x/h · {a^{xh} b} · {a^h x}{b^h x}`。
選択肢は「h の下で排反かつ網羅」を、任意の命題 P について
`P/h = Σ_x Px/h` (印刷の証明が (24.7) から使う分割) として仮定する。 -/
theorem th_14_49_1_src2 (a b h : Prop) (xs : List Prop)
    (hpart : ∀ P : Prop, Pr P h = (xs.map (fun x => Pr (P ∧ x) h)).sum)
    (ha : Pr a h ≠ 0) (hb : Pr b h ≠ 0)
    (hx : ∀ x ∈ xs, Pr x h ≠ 0 ∧ Pr a (x ∧ h) ≠ 0 ∧ Pr b (x ∧ h) ≠ 0) :
    coef2 a b h
      = (xs.map (fun x => Pr x h * coef2 a b (x ∧ h) * coef2 a x h * coef2 b x h)).sum := by
  have hterm : ∀ x ∈ xs,
      Pr ((a ∧ b) ∧ x) h / (Pr a h * Pr b h)
        = Pr x h * coef2 a b (x ∧ h) * coef2 a x h * coef2 b x h := by
    intro x hxm
    rcases hx x hxm with ⟨hx0, hax, hbx⟩
    unfold coef2
    rw [def_X_left (a ∧ b) x h, def_X_left a x h, def_X_left b x h]
    field_simp
    try ring
  unfold coef2
  rw [hpart (a ∧ b), list_sum_div (fun x => Pr ((a ∧ b) ∧ x) h) (Pr a h * Pr b h)]
  apply list_sum_congr
  intro x hxm
  have := hterm x hxm
  unfold coef2 at this
  exact this

/-- **(49.1) 系・2 文字版** (folio 155): 各 x で {a^{xh}b} ≥ 1 かつ
({a^h x} − 1) と ({b^h x} − 1) が同符号なら {a^h b} ≥ 1 — 「単位から増加」。
鍵は Σ_x x/h·{a^h x} = 1 (加重平均が 1) で、積の和は
1 + Σ x/h ({a^h x}−1)({b^h x}−1) となる。 -/
theorem th_14_49_1_cor2 (a b h : Prop) (xs : List Prop)
    (hpart : ∀ P : Prop, Pr P h = (xs.map (fun x => Pr (P ∧ x) h)).sum)
    (ha : Pr a h ≠ 0) (hb : Pr b h ≠ 0)
    (hx : ∀ x ∈ xs, Pr x h ≠ 0 ∧ Pr a (x ∧ h) ≠ 0 ∧ Pr b (x ∧ h) ≠ 0)
    (hge : ∀ x ∈ xs, 1 ≤ coef2 a b (x ∧ h))
    (hsign : ∀ x ∈ xs, 0 ≤ (coef2 a x h - 1) * (coef2 b x h - 1)) :
    1 ≤ coef2 a b h := by
  rw [th_14_49_1_src2 a b h xs hpart ha hb hx]
  -- (1) 各項の下界: x/h·{a^h x}{b^h x} ≤ 項
  have hca : ∀ x, 0 ≤ coef2 a x h := by
    intro x; unfold coef2
    exact div_nonneg (ax_range_lo _ _) (mul_nonneg (ax_range_lo _ _) (ax_range_lo _ _))
  have hcb : ∀ x, 0 ≤ coef2 b x h := by
    intro x; unfold coef2
    exact div_nonneg (ax_range_lo _ _) (mul_nonneg (ax_range_lo _ _) (ax_range_lo _ _))
  have hlow : ∀ x ∈ xs,
      Pr x h * coef2 a x h * coef2 b x h
        ≤ Pr x h * coef2 a b (x ∧ h) * coef2 a x h * coef2 b x h := by
    intro x hxm
    have hW : 0 ≤ Pr x h * coef2 a x h * coef2 b x h :=
      mul_nonneg (mul_nonneg (ax_range_lo x h) (hca x)) (hcb x)
    have hre : Pr x h * coef2 a b (x ∧ h) * coef2 a x h * coef2 b x h
        = coef2 a b (x ∧ h) * (Pr x h * coef2 a x h * coef2 b x h) := by ring
    rw [hre]
    exact le_mul_of_one_le_left hW (hge x hxm)
  have step1 := list_sum_le _ _ xs hlow
  -- (2) 加重平均: Σ x/h = 1, Σ x/h·{a^h x} = 1, Σ x/h·{b^h x} = 1
  have hw1 : (xs.map (fun x => Pr x h)).sum = 1 := by
    have hT := hpart True
    rw [ax_iii_true] at hT
    rw [hT]
    apply list_sum_congr
    intro x _
    have e : (True ∧ x) ↔ x := by tauto
    exact (ax_iii_op _ _ h e).symm
  have hwa : (xs.map (fun x => Pr x h * coef2 a x h)).sum = 1 := by
    have h1 : (xs.map (fun x => Pr x h * coef2 a x h)).sum
        = (xs.map (fun x => Pr (a ∧ x) h / Pr a h)).sum := by
      apply list_sum_congr
      intro x hxm
      rcases hx x hxm with ⟨hx0, -, -⟩
      unfold coef2
      field_simp
      try ring
    rw [h1, ← list_sum_div (fun x => Pr (a ∧ x) h) (Pr a h), ← hpart a]
    exact div_self ha
  have hwb : (xs.map (fun x => Pr x h * coef2 b x h)).sum = 1 := by
    have h1 : (xs.map (fun x => Pr x h * coef2 b x h)).sum
        = (xs.map (fun x => Pr (b ∧ x) h / Pr b h)).sum := by
      apply list_sum_congr
      intro x hxm
      rcases hx x hxm with ⟨hx0, -, -⟩
      unfold coef2
      field_simp
      try ring
    rw [h1, ← list_sum_div (fun x => Pr (b ∧ x) h) (Pr b h), ← hpart b]
    exact div_self hb
  -- (3) 展開恒等式と符号条件
  have hex : (xs.map (fun x => Pr x h * coef2 a x h * coef2 b x h)).sum
      = (xs.map (fun x => Pr x h)).sum
        + ((xs.map (fun x => Pr x h * coef2 a x h)).sum - (xs.map (fun x => Pr x h)).sum)
        + ((xs.map (fun x => Pr x h * coef2 b x h)).sum - (xs.map (fun x => Pr x h)).sum)
        + (xs.map (fun x => Pr x h * ((coef2 a x h - 1) * (coef2 b x h - 1)))).sum :=
    list_sum_expand (fun x => Pr x h) (fun x => coef2 a x h) (fun x => coef2 b x h) xs
  have hS : 0 ≤ (xs.map (fun x => Pr x h * ((coef2 a x h - 1) * (coef2 b x h - 1)))).sum := by
    apply list_sum_nonneg'
    intro x hxm
    exact mul_nonneg (ax_range_lo x h) (hsign x hxm)
  linarith [hex, hw1, hwa, hwb, hS, step1]

/-! ### 第 17 章 (56)(57) 系 -/

theorem th_17_56_raw (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1) :
    Pr E h = Pr (α₁ ∧ E) h + Pr (α₂ ∧ E) h - Pr ((α₁ ∧ α₂) ∧ E) h := by
  have key : Pr ((α₁ ∨ α₂) ∧ E) h = Pr (α₁ ∨ α₂) (E ∧ h) * Pr E h :=
    def_X_left (α₁ ∨ α₂) E h
  rw [hexh, one_mul] at key
  have expand := th_24 (α₁ ∧ E) (α₂ ∧ E) h
  have e1 : ((α₁ ∧ E) ∨ (α₂ ∧ E)) ↔ ((α₁ ∨ α₂) ∧ E) := by tauto
  have e2 : ((α₁ ∧ E) ∧ (α₂ ∧ E)) ↔ ((α₁ ∧ α₂) ∧ E) := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at expand
  linarith

/-- **(56.4) 印刷形** (folio 189): `c₁p₁ ⩽ u ⩽ c₁p₁ + c₂, u ⩽ c₁p₁ + 1 − c₁`
(p₂ を消去した限界)。印刷の 3 項は「下限 1 つと上限 2 つ」として読む:
第 3 項を第 2 項に連鎖させる読み (c₂ ⩽ 1 − c₁) は c₁ + c₂ ⩽ 1 を要し、
(56) の設定 (原因の重なりを許す) からは出ない。旧 th_17_56_4 は中央の 1 本のみ。 -/
theorem th_17_56_4_src (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1) :
    Pr E (α₁ ∧ h) * Pr α₁ h ≤ Pr E h ∧
    Pr E h ≤ Pr E (α₁ ∧ h) * Pr α₁ h + Pr α₂ h ∧
    Pr E h ≤ Pr E (α₁ ∧ h) * Pr α₁ h + 1 - Pr α₁ h := by
  have raw := th_17_56_raw α₁ α₂ E h hexh
  have d1 : Pr (α₁ ∧ E) h = Pr E (α₁ ∧ h) * Pr α₁ h := def_X_right α₁ E h
  have hB : Pr (α₂ ∧ E) h ≤ Pr α₂ h := pr_conj_le_left α₂ E h
  have hC0 := ax_range_lo ((α₁ ∧ α₂) ∧ E) h
  -- 下限: E/h = α₁E/h + ¬α₁E/h ≥ α₁E/h
  have hsplit := def_IX E α₁ h
  have e0 : (E ∧ α₁) ↔ (α₁ ∧ E) := by tauto
  rw [ax_iii_op _ _ h e0] at hsplit
  have hlo := ax_range_lo (E ∧ ¬α₁) h
  -- 上限 2: ¬α₁E/h ≤ ¬α₁/h = 1 − α₁/h
  have hup := pr_conj_le_left (¬α₁) E h
  have e1 : (¬α₁ ∧ E) ↔ (E ∧ ¬α₁) := by tauto
  rw [ax_iii_op _ _ h e1] at hup
  have hcompl := th_13_1 α₁ h
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- (57)(i) の一段: E∧N /h = E∧a /h − (E∧a)∧¬N /h + E∧(N∧¬a) /h (7h と同一)。 -/
theorem th_17_57_step (E N a h : Prop) :
    Pr (E ∧ N) h
      = Pr (E ∧ a) h - Pr ((E ∧ a) ∧ ¬N) h + Pr (E ∧ (N ∧ ¬a)) h := by
  have s1 := def_IX (E ∧ N) a h
  have s2 := def_IX (E ∧ a) N h
  have e1 : ((E ∧ N) ∧ a) ↔ ((E ∧ a) ∧ N) := by tauto
  have e2 : ((E ∧ N) ∧ ¬a) ↔ (E ∧ (N ∧ ¬a)) := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at s1
  linarith

/-- ブール分解 (7h と同一): (57)(i) をリストに沿って展開。 -/
noncomputable def booleDecomp (E h : Prop) : List Prop → Prop → ℝ
  | [], N => Pr (E ∧ N) h
  | a :: rest, N =>
      Pr (E ∧ a) h - Pr ((E ∧ a) ∧ ¬N) h + booleDecomp E h rest (N ∧ ¬a)

/-- 否定連鎖の末尾: negChain l N = N ∧ ¬a₁ ∧ … ∧ ¬aₙ。 -/
def negChain : List Prop → Prop → Prop
  | [], N => N
  | a :: rest, N => negChain rest (N ∧ ¬a)

theorem th_17_57_i_src (E h : Prop) : ∀ (l : List Prop) (N : Prop),
    Pr (E ∧ N) h = booleDecomp E h l N := by
  intro l
  induction l with
  | nil => intro N; rfl
  | cons a rest ih =>
      intro N
      simp only [booleDecomp]
      rw [← ih (N ∧ ¬a)]
      exact th_17_57_step E N a h

/-- 印刷 (57.1) が実際に用いる独立性: 各段 r で
「先行原因がすべて欠ける確率 (a_r h の下)」 = Π_{s<r}(1 − c_s)。
再帰的に、N = 先行原因の否定の連言、P = Π(1 − c_s) の累積として述べる。
(印刷は a_r/a_sh = a_r/h からこれを導くが、そこは対独立から相互独立への
飛躍であり、ここでは使われる形を直接仮定する。) -/
def IndepChain (h : Prop) : List Prop → Prop → ℝ → Prop
  | [], _, _ => True
  | a :: rest, N, P => Pr N (a ∧ h) = P ∧ IndepChain h rest (N ∧ ¬a) (P * (1 - Pr a h))

/-- 印刷 (57.1) の右辺: Σ_r c_r p_r − Σ_r c_r[1 − Π_{s<r}(1−c_s)] m_r、
m_r := e/‾(ā₁…ā_{r−1}) a_r h (= Pr E ((¬N ∧ a_r) ∧ h))。r=1 の補正項は 1−P = 0 で消える。 -/
noncomputable def keynes57_1 (E h : Prop) : List Prop → Prop → ℝ → ℝ
  | [], _, _ => 0
  | a :: rest, N, P =>
      Pr a h * Pr E (a ∧ h) - Pr a h * (1 - P) * Pr E ((¬N ∧ a) ∧ h)
        + keynes57_1 E h rest (N ∧ ¬a) (P * (1 - Pr a h))

/-- 一段の変形: (E∧a)∧¬N /h = c · (1 − P) · m (独立性の一段の下)。 -/
theorem th_17_57_1_term (E N a h : Prop) (P : ℝ) (hN : Pr N (a ∧ h) = P) :
    Pr ((E ∧ a) ∧ ¬N) h = Pr a h * (1 - P) * Pr E ((¬N ∧ a) ∧ h) := by
  have e : ((E ∧ a) ∧ ¬N) ↔ ((¬N ∧ a) ∧ E) := by tauto
  rw [ax_iii_op _ _ h e, def_X_right (¬N ∧ a) E h, def_X_left (¬N) a h]
  have hc := th_13_1 N (a ∧ h)
  rw [hN] at hc
  have : Pr (¬N) (a ∧ h) = 1 - P := by linarith
  rw [this]
  ring

theorem th_17_57_1_general (E h : Prop) : ∀ (l : List Prop) (N : Prop) (P : ℝ),
    IndepChain h l N P →
    booleDecomp E h l N = keynes57_1 E h l N P + Pr (E ∧ negChain l N) h := by
  intro l
  induction l with
  | nil =>
      intro N P _
      simp only [booleDecomp, keynes57_1, negChain]
      ring
  | cons a rest ih =>
      intro N P hind
      rcases hind with ⟨hN, hrest⟩
      simp only [booleDecomp, keynes57_1, negChain]
      rw [ih (N ∧ ¬a) (P * (1 - Pr a h)) hrest, th_17_57_1_term E N a h P hN,
          def_X_left E a h]
      ring

/-- **(57.1) 印刷形** (folio 190): 原因が網羅的 (e ā₁…āₙ/h = 0) かつ独立なら
`e/h = Σ_{r=1}^{n} c_r p_r − Σ_{r=2}^{n} c_r[1 − Π_{s=1}^{r−1}(1−c_s)] m_r`。
旧 6a の th_17_57_1 は対積和による下界不等式で、印刷の等式ではなかった。 -/
theorem th_17_57_1_src (E h : Prop) (l : List Prop)
    (hind : IndepChain h l True 1)
    (hexh : Pr (E ∧ negChain l True) h = 0) :
    Pr E h = keynes57_1 E h l True 1 := by
  have hE : Pr E h = Pr (E ∧ True) h := by
    have e : E ↔ (E ∧ True) := by tauto
    exact ax_iii_op _ _ h e
  rw [hE, th_17_57_i_src E h l True, th_17_57_1_general E h l True 1 hind, hexh]
  ring

/-- ブール分解の上界: 補正項 ≥ 0 なので booleDecomp ≤ Σ E∧a_r/h + 末尾。 -/
theorem booleDecomp_le (E h : Prop) : ∀ (l : List Prop) (N : Prop),
    booleDecomp E h l N ≤ (l.map (fun a => Pr (E ∧ a) h)).sum + Pr (E ∧ negChain l N) h := by
  intro l
  induction l with
  | nil => intro N; simp only [booleDecomp, negChain, List.map_nil, List.sum_nil]; linarith
  | cons a rest ih =>
      intro N
      simp only [booleDecomp, negChain, List.map_cons, List.sum_cons]
      have h0 := ax_range_lo ((E ∧ a) ∧ ¬N) h
      have := ih (N ∧ ¬a)
      linarith

/-- **(57.2) 印刷形** (folio 191): 独立性を仮定せず、(i.) から各 r について
`e/h ⩾ c_r p_r` と `e/h ⩽ 1 − c_r(1 − p_r)`、(ii.) から `e/h ⩽ Σ c_r p_r`。
旧 th_17_56_1 系は下限のみ、上限は独立性つきの別定理に散在していた。 -/
theorem th_17_57_2_src (E h : Prop) (l : List Prop)
    (hexh : Pr (E ∧ negChain l True) h = 0) :
    (∀ a ∈ l, Pr a h * Pr E (a ∧ h) ≤ Pr E h ∧
              Pr E h ≤ 1 - Pr a h * (1 - Pr E (a ∧ h))) ∧
    Pr E h ≤ (l.map (fun a => Pr a h * Pr E (a ∧ h))).sum := by
  constructor
  · intro a _
    have hsplit := def_IX E a h
    have hEa : Pr (E ∧ a) h = Pr E (a ∧ h) * Pr a h := def_X_left E a h
    have hlo := ax_range_lo (E ∧ ¬a) h
    have hup := pr_conj_le_left (¬a) E h
    have e1 : (¬a ∧ E) ↔ (E ∧ ¬a) := by tauto
    rw [ax_iii_op _ _ h e1] at hup
    have hcompl := th_13_1 a h
    constructor
    · nlinarith [hsplit, hEa, hlo]
    · nlinarith [hsplit, hEa, hup, hcompl]
  · have hE : Pr E h = Pr (E ∧ True) h := by
      have e : E ↔ (E ∧ True) := by tauto
      exact ax_iii_op _ _ h e
    rw [hE, th_17_57_i_src E h l True]
    have hb := booleDecomp_le E h l True
    rw [hexh, add_zero] at hb
    have hs : (l.map (fun a => Pr (E ∧ a) h)).sum
        = (l.map (fun a => Pr a h * Pr E (a ∧ h))).sum := by
      apply list_sum_congr
      intro a _
      rw [def_X_left E a h]; ring
    linarith [hb, hs]

/-- (57.3) の下界の右辺: Σ c_r p_r − Σ_{r≥2} c_r[1 − Π_{s<r}(1−c_s)] (m_r を 1 に置換)。 -/
noncomputable def keynes57_3 (E h : Prop) : List Prop → ℝ → ℝ
  | [], _ => 0
  | a :: rest, P =>
      Pr a h * Pr E (a ∧ h) - Pr a h * (1 - P) + keynes57_3 E h rest (P * (1 - Pr a h))

theorem keynes57_1_ge (E h : Prop) : ∀ (l : List Prop) (N : Prop) (P : ℝ),
    IndepChain h l N P → keynes57_3 E h l P ≤ keynes57_1 E h l N P := by
  intro l
  induction l with
  | nil => intro N P _; simp only [keynes57_1, keynes57_3]; linarith
  | cons a rest ih =>
      intro N P hind
      rcases hind with ⟨hN, hrest⟩
      simp only [keynes57_1, keynes57_3]
      have hP0 : 0 ≤ P := by rw [← hN]; exact ax_range_lo _ _
      have hP1 : P ≤ 1 := by rw [← hN]; exact ax_range_hi _ _
      have hm := ax_range_hi E ((¬N ∧ a) ∧ h)
      have hc := ax_range_lo a h
      have htail := ih (N ∧ ¬a) (P * (1 - Pr a h)) hrest
      have key : Pr a h * (1 - P) * Pr E ((¬N ∧ a) ∧ h) ≤ Pr a h * (1 - P) := by
        have : 0 ≤ Pr a h * (1 - P) := mul_nonneg hc (by linarith)
        nlinarith [this, hm]
      linarith

/-- **(57.3) 印刷形** (folio 191): 独立なら
`e/h ⩾ Σ c_r p_r − Σ_{r=2}^{n} c_r[1 − Π_{s<r}(1−c_s)]`
(印刷の Π 係数形の下界そのもの)。旧 6a は対積和による緩い下界。 -/
theorem th_17_57_3_src (E h : Prop) (l : List Prop)
    (hind : IndepChain h l True 1)
    (hexh : Pr (E ∧ negChain l True) h = 0) :
    keynes57_3 E h l 1 ≤ Pr E h := by
  rw [th_17_57_1_src E h l hind hexh]
  exact keynes57_1_ge E h l True 1 hind

/-! ## B. 原著側の誤り — 印刷形の機械反駁 -/

/-- **(52) の狭義不等号は導出不能** (folio 162): n+1 = 2 個の命題を両方 True に
とると `x₁x₂/h = x₁/h + x₂/h − 1` で等号。印刷「always greater than」は破れる。 -/
theorem th_15_52_strict_fails (h : Prop) :
    ¬ (Pr (True ∧ True) h > Pr True h + Pr True h - 1) := by
  have e : (True ∧ True) ↔ True := by tauto
  rw [ax_iii_op _ _ h e, ax_iii_true]
  norm_num

/-- **(53) の狭義不等号は導出不能** (folio 162): y := x で
`xy/h + x̄ȳ/h = x/h − y/h + 1` の等号 (両辺 1)。印刷「always less than」は破れる。 -/
theorem th_15_53_strict_fails (x h : Prop) :
    Pr (x ∧ x) h + Pr (¬x ∧ ¬x) h = Pr x h - Pr x h + 1 := by
  have e1 : (x ∧ x) ↔ x := by tauto
  have e2 : (¬x ∧ ¬x) ↔ ¬x := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2]
  have := th_13_1 x h
  linarith

/-- **(58.2) の正しい差分公式** (folio 193): G(k) := a + b·q^{k−1} (b = p − a) とおくと
`y_{n+1} − y_n = G(n+1)/G(n) − G(n)/G(n−1)` の分子は
`G(n+1)G(n−1) − G(n)² = a·b·q^{n−2}·(1 − q)²` — 因子 (1−q) は **2 乗**。
(m = n − 2 として述べる。) -/
theorem th_17_58_2_numerator (a b q : ℝ) (m : ℕ) :
    (a + b * q ^ (m + 2)) * (a + b * q ^ m) - (a + b * q ^ (m + 1)) ^ 2
      = a * b * q ^ m * (1 - q) ^ 2 := by
  ring

end Keynes

/-! ## B (続) — (58.2)(58.3) の印刷形の数値反駁 (a = 1/2, p = 3/4, q = 1/2) -/

namespace Erratum58

def a : ℚ := 1/2
def p : ℚ := 3/4
def q : ℚ := (p - a) / (1 - a)          -- = 1/2
/-- G(k) := a + (p − a) q^{k−1} = y₁ y₂ … y_k (連鎖確率の積、G(1) = p)。 -/
def G (k : ℕ) : ℚ := a + (p - a) * q ^ (k - 1)

theorem q_val : q = 1/2 := by norm_num [q, p, a]
theorem G_vals : G 1 = 3/4 ∧ G 2 = 5/8 ∧ G 3 = 9/16 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [G, q, p, a]

/-- **(58.2) 印刷形は偽**: n = 2 で実際の差 y₃ − y₂ = G(3)/G(2) − G(2)/G(1) = 1/15、
印刷の式 a(p−a)q^{n−2}(1−q)/(G(2)G(1)) = 2/15。 -/
theorem printed_58_2_false :
    G 3 / G 2 - G 2 / G 1 = 1/15 ∧
    a * (p - a) * q ^ (2 - 2) * (1 - q) / (G 2 * G 1) = 2/15 ∧
    G 3 / G 2 - G 2 / G 1 ≠ a * (p - a) * q ^ (2 - 2) * (1 - q) / (G 2 * G 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [G, q, p, a]

/-- **修正形 ((1−q)²) は一致**: a(p−a)q^{n−2}(1−q)²/(G(2)G(1)) = 1/15。 -/
theorem corrected_58_2_holds :
    G 3 / G 2 - G 2 / G 1 = a * (p - a) * q ^ (2 - 2) * (1 - q) ^ 2 / (G 2 * G 1) := by
  norm_num [G, q, p, a]

/-- **(58.3) 印刷形は偽**: t₁ = a/y₁ = a/p = 2/3 だが、印刷の閉形式
a/[a + (p−a)q^n] は n = 1 で 4/5。正しい指数 n−1 では a/G(1) = 2/3。 -/
theorem printed_58_3_false :
    a / p = 2/3 ∧ a / (a + (p - a) * q ^ 1) = 4/5 ∧ a / p ≠ a / (a + (p - a) * q ^ 1) ∧
    a / G 1 = a / p := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [G, q, p, a]

end Erratum58


/-! ## B (続) — (35) の反例モデル: 印刷の非狭義前提では結論が破れる -/

namespace Erratum35Countermodel

/-
8 領域 (a, x, h₁ の真偽の組) の質量、総質量 50:
  a x h₁ = 6,  a x ¬h₁ = 9,  a ¬x h₁ = 4,  a ¬x ¬h₁ = 6,
  ¬a x h₁ = 4, ¬a x ¬h₁ = 6, ¬a ¬x h₁ = 6, ¬a ¬x ¬h₁ = 9.
周辺: a = 25, x = 25, h₁ = 20, a∧x = 15, a∧h₁ = 10, x∧h₁ = 10, a∧x∧h₁ = 6。
条件付き確率は質量比。h₁ は a に対して (x の有無にかかわらず) 無関連。
-/

def total : ℚ := 50
def mA : ℚ := 25
def mX : ℚ := 25
def mH : ℚ := 20
def mAX : ℚ := 15
def mAH : ℚ := 10
def mXH : ℚ := 10
def mAXH : ℚ := 6

def A : ℚ := mA / total       -- a/h      = 1/2
def B : ℚ := mAX / mX         -- a/hx     = 3/5
def C : ℚ := mAH / mH         -- a/hh₁    = 1/2
def D : ℚ := mAXH / mXH       -- a/hh₁x   = 3/5

theorem masses_positive :
    0 < total ∧ 0 < mA ∧ 0 < mX ∧ 0 < mH ∧ 0 < mAX ∧ 0 < mAH ∧ 0 < mXH ∧ 0 < mAXH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [total, mA, mX, mH, mAX, mAH, mXH, mAXH]

/-- 8 領域の質量は非負で総和 50 (モデルが実際の確率分布であること)。 -/
theorem regions_consistent :
    (6 : ℚ) + 9 + 4 + 6 + 4 + 6 + 6 + 9 = total ∧
    (6 : ℚ) + 9 + 4 + 6 = mA ∧ (6 : ℚ) + 9 + 4 + 6 = mX ∧ (6 : ℚ) + 4 + 4 + 6 = mH ∧
    (6 : ℚ) + 9 = mAX ∧ (6 : ℚ) + 4 = mAH ∧ (6 : ℚ) + 4 = mXH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [total, mA, mX, mH, mAX, mAH, mXH]

/-- Def.X の関連インスタンス (標準条件付き確率であることの検査)。 -/
theorem model_satisfies_X_instances :
    B * (mX / total) = mAX / total ∧ C * (mH / total) = mAH / total ∧
    D * (mXH / total) = mAXH / total := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [A, B, C, D, total, mA, mX, mH, mAX, mAH, mXH, mAXH]

/-- **印刷 (35) の前提は全て成立**: x は a/h に好都合 (A < B)、
x は h₁x より好都合ではない (B ⩽ D、印刷の非狭義 "not more favourable")、
x は a/hh₁ に対するのに劣らず a/h に好都合 (B/A ⩾ D/C ⇔ B·C ⩾ D·A)。 -/
theorem hypotheses_of_35_hold : A < B ∧ B ≤ D ∧ B * C ≥ D * A := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [A, B, C, D, total, mA, mX, mH, mAX, mAH, mXH, mAXH]

/-- **結論は破れる**: h₁ は a/h に好都合でない (C = A = 1/2)。
狭義形 (B < D、7b th_14_35) では前提が満たされず、反例は消える —
すなわち印刷の非狭義前提が過剰で、狭義化が最小修復。 -/
theorem conclusion_of_35_fails : ¬ (A < C) := by
  norm_num [A, C, total, mA, mH, mAH]

end Erratum35Countermodel

/-! ## B (続) — (46.1) の反例モデル: (x/h)ⁿ を落とした比例関係は破れる -/

namespace Erratum46_1Countermodel

/-
文字 a, b (n + 1 = 2, n = 1)、選択肢 x, x̄。8 領域の質量、総質量 16:
  x:  ab = 3, a¬b = 3, ¬ab = 3, ¬a¬b = 3   (x の質量 12)
  x̄:  ab = 1, a¬b = 1, ¬ab = 1, ¬a¬b = 1   (x̄ の質量 4)
どちらの選択肢の下でも a, b は独立 (係数 {a^{xh}b} = {a^{x̄h}b} = 1)。
事前確率 x/h = 3/4, x̄/h = 1/4 が異なることが要点。
-/

def total : ℚ := 16
def mX : ℚ := 12
def mNX : ℚ := 4
def mA : ℚ := 8
def mB : ℚ := 8
def mABX : ℚ := 3
def mABNX : ℚ := 1
def mAX : ℚ := 6
def mBX : ℚ := 6
def mANX : ℚ := 2
def mBNX : ℚ := 2
def mAB : ℚ := 4

-- 左辺: x/hab, x̄/hab
def L_x : ℚ := mABX / mAB           -- 3/4
def L_nx : ℚ := mABNX / mAB         -- 1/4
-- 係数 {a^{xh} b} = (ab/xh) / (a/xh · b/xh)
def K_x : ℚ := (mABX / mX) / ((mAX / mX) * (mBX / mX))       -- 1
def K_nx : ℚ := (mABNX / mNX) / ((mANX / mNX) * (mBNX / mNX)) -- 1
-- x/ah, x/bh, x̄/ah, x̄/bh
def xa : ℚ := mAX / mA   -- 3/4
def xb : ℚ := mBX / mB   -- 3/4
def nxa : ℚ := mANX / mA -- 1/4
def nxb : ℚ := mBNX / mB -- 1/4
-- 事前
def px : ℚ := mX / total   -- 3/4
def pnx : ℚ := mNX / total -- 1/4

/-- 印刷 (46.1) の右辺 R(x') := {a^{x'h}b} · x'/ah · x'/bh。 -/
def R_x : ℚ := K_x * xa * xb
def R_nx : ℚ := K_nx * nxa * nxb

/-- **印刷 (46.1) の比例関係は破れる**: x/hab : x̄/hab = 3 : 1 だが
R(x) : R(x̄) = 9 : 1。 -/
theorem printed_46_1_false : L_x * R_nx ≠ L_nx * R_x := by
  norm_num [L_x, L_nx, R_x, R_nx, K_x, K_nx, xa, xb, nxa, nxb,
            mABX, mABNX, mAB, mX, mNX, mAX, mBX, mANX, mBNX, mA, mB]

/-- **(46) の正しい形 (因子 (x/h)ⁿ つき) は成立**:
(x/h)·x/hab : (x̄/h)·x̄/hab = R(x) : R(x̄)。 -/
theorem corrected_46_holds : (px * L_x) * R_nx = (pnx * L_nx) * R_x := by
  norm_num [px, pnx, L_x, L_nx, R_x, R_nx, K_x, K_nx, xa, xb, nxa, nxb,
            mABX, mABNX, mAB, mX, mNX, mAX, mBX, mANX, mBNX, mA, mB, total]

end Erratum46_1Countermodel

/-! ## 依存公理の全数監査 -/

#print axioms Keynes.th_13_2_src
#print axioms Keynes.th_13_3_src
#print axioms Keynes.th_13_10_src
#print axioms Keynes.th_13_11_src
#print axioms Keynes.th_14_37_src
#print axioms Keynes.th_14_38_1_src
#print axioms Keynes.th_14_43_src
#print axioms Keynes.th_14_43_src_2
#print axioms Keynes.th_14_46_2_src2
#print axioms Keynes.th_14_49_1_src2
#print axioms Keynes.th_14_49_1_cor2
#print axioms Keynes.th_17_56_4_src
#print axioms Keynes.th_17_57_1_src
#print axioms Keynes.th_17_57_2_src
#print axioms Keynes.th_17_57_3_src
#print axioms Keynes.th_15_52_strict_fails
#print axioms Keynes.th_15_53_strict_fails
#print axioms Keynes.th_17_58_2_numerator
#print axioms Erratum58.printed_58_2_false
#print axioms Erratum58.corrected_58_2_holds
#print axioms Erratum58.printed_58_3_false
#print axioms Erratum35Countermodel.hypotheses_of_35_hold
#print axioms Erratum35Countermodel.conclusion_of_35_fails
#print axioms Erratum46_1Countermodel.printed_46_1_false
#print axioms Erratum46_1Countermodel.corrected_46_holds
