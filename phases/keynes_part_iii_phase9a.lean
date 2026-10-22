/-
# Keynes (1921) *A Treatise on Probability* Part III — Lean 4 Phase 9a
# 第 XX 章「事例の増加の価値、または純粋帰納」 F20.1–F20.21

基準: 1921 年 Macmillan 初版の印刷ページ (folio 235–238)。第 XXII 章 folio 254 の
条件式 (E-III-2) もここで機械判定する。

## 命題集合と確率集合の扱い
Part III は phase6c の内包版公理群 (`IProp`, `PrI`) の部分集合の上に符号化する
(def_XI_i は置かない)。`Prop → Prop → ℝ` 型の確率関係は propext + 古典論理の下で
退化する (phase8d `V_collapse`) ので用いない。

## 証拠の括弧付け (本ファイルの読みの規約)
Keynes の `hx_1x_2 . . . x_n` は前提の並置であり結合の順序を持たない。内包版では
一つの括弧付けを固定する必要がある。本ファイルでは
  x_1x_2 . . . x_n  :=  C n   (C 0 = itrue, C (n+1) = x_{n+1} ∧ C n)
  hx_1 . . . x_n    :=  C n ∧ h
と読む。証拠側の括弧の付け替え (結合・交換) は公理ではなく、Def.X の左右両形と
認証代入から「前提が不可能でない」(x_1…x_n/h ≠ 0) 条件付きで導く
(`pr_evidence_assoc`, `pr_evidence_comm`)。Keynes 自身の Th.(12.1) (folio 141) も
同種の条件付きである。この規約の下で:
  * 主経路: F20.11 の第 1 等式 p_n · (x_1…x_n/h) = p_0 を証拠側の置換なしに導き、
    F20.6/F20.7 の乗法形・除法形を「x_1…x_{n−1}/h ≠ 0」条件付きの系として得る。
  * 印刷経路: F20.6 の 4 段 (証拠 hx_1…x_{n−1} に対する g と x_n の乗法定理) は、
    証拠側の置換補題を使って第 2 段に g を復した形 (`th_20_6_cor`) で再現する。
    印刷の第 2 段 (分子 x_n/hx_1…x_{n−1}、g 脱落 = E-III-1) は p_n = 1 のときに
    限って成り立つことを示す (`th_20_6_src`)。
  * F20.1 は印刷形 `x_r/gh = 1` (r ≥ 1) のまま仮定し、導出で要る `x_1…x_n/gh = 1` は
    Keynes の Th.(9) (folio 140: a/h = 1 かつ bh が不整合でなければ a/bh = 1)
    の内包版 `th_13_9_i` を経て得る。

## 実数解析
極限 (F20.12, F20.15–F20.18, F20.20) は Mathlib の `Filter.Tendsto` で述べる。
Keynes 自身の極限の定義 (folio 237 脚注 2, F20.18) を `KeynesLimit` として書き、
`Filter.Tendsto` と同値であることを示す。

## 足した前提の必要性
Keynes が明示しない前提 (p_{n−1} > 0、x_1…x_n/h ≠ 0、分母 ≠ 0、p_0 > 0) については、
落としたときに何が起きるかを (1) 公理群の中の定理として、(2) 本章の関係式を満たす
数値の例として、本ファイル末尾に残す。(2) は 7i の Erratum と同じ水準 (関係式の
数値例) であり、公理群のモデルではない (末尾の「公理群の検査」を参照)。

## 検査
  lake env lean phases/keynes_part_iii_phase9a.lean
  bash tools/check_all.sh phases/keynes_part_iii_phase9a.lean
-/

import Mathlib

namespace KeynesI

/-! ## 内包版の命題集合と結合子 (phase6c の部分集合) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-! ## Keynes 操作公理群 (内包版、phase6c の部分集合: def_XI_i を置かない) -/

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1
axiom def_VIII_i (a b h : IProp) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-! ## 深い埋め込み: 構文・評価・トートロジー (phase6c と同じ定義) -/

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

axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Taut f → PrI (interp env f) h = 1

/-- **Th.(12) 内包版** (phase6c から移植)。 -/
theorem th_12_i (a b h : IProp) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h := by
  obtain ⟨hba, hab⟩ := (def_VIII_i a b h).mp hcert
  have hl := def_X_left_i a b h
  have hr := def_X_right_i a b h
  rw [hab, one_mul] at hl
  rw [hba, one_mul] at hr
  linarith

theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i _ _ h (ax_iii_taut (Form.iffF f g) env h ht)

theorem itrue_certain (h : IProp) : PrI itrue h = 1 :=
  ax_iii_taut Form.tru (fun _ => itrue) h (fun _ => rfl)

/-- **Th.(13.1) 内包版** 補完律 (phase6c から移植)。 -/
theorem th_13_1_i (a h : IProp) : PrI a h + PrI (inot a) h = 1 := by
  have step := def_IX_i itrue a h
  have e1 : PrI (iand itrue (inot a)) h = PrI (inot a) h :=
    subst_taut (Form.conj Form.tru (Form.neg (Form.var 0))) (Form.neg (Form.var 0))
      (fun _ => a) h (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have e2 : PrI (iand itrue a) h = PrI a h :=
    subst_taut (Form.conj Form.tru (Form.var 0)) (Form.var 0)
      (fun _ => a) h (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have e3 := itrue_certain h
  linarith [step, e1, e2, e3]

/-! ## 第 XIII 章 Th.(9)(10) の内包版 (本ファイルで新たに証明) -/

/-- **Th.(13.10) 内包版** (folio 140): a/k = 1 ならば ba/k = b/k。
証明: Def.IX で b を a と ā に分け、bā/k = b/āk · ā/k = 0 (補完律)。 -/
theorem th_13_10_i (a b k : IProp) (ha : PrI a k = 1) :
    PrI (iand b a) k = PrI b k := by
  have hIX := def_IX_i b a k
  have hneg : PrI (inot a) k = 0 := by linarith [th_13_1_i a k]
  have hXl := def_X_left_i b (inot a) k
  rw [hneg, mul_zero] at hXl
  linarith

/-- **Th.(13.9) 内包版** (folio 140): a/k = 1 かつ bk が不整合でない
(b/k ≠ 0) ならば a/bk = 1。Def.X 右形 ba/k = a/bk · b/k と Th.(10)。 -/
theorem th_13_9_i (a b k : IProp) (ha : PrI a k = 1) (hb : PrI b k ≠ 0) :
    PrI a (iand b k) = 1 := by
  have h10 := th_13_10_i a b k ha
  have hXr := def_X_right_i b a k
  rw [h10] at hXr
  have : PrI a (iand b k) * PrI b k = 1 * PrI b k := by linarith
  exact mul_right_cancel₀ hb this

/-- 確実な命題 (itrue) を証拠に添えても確率は変わらない: g/(⊤ ∧ h) = g/h。
Def.X 左形 (g ∧ ⊤)/h = g/(⊤ ∧ h) · ⊤/h と認証代入 (g ∧ ⊤ ↔ g)。 -/
theorem pr_iand_itrue_evidence (g h : IProp) : PrI g (iand itrue h) = PrI g h := by
  have hXl := def_X_left_i g itrue h
  rw [itrue_certain, mul_one] at hXl
  have e : PrI (iand g itrue) h = PrI g h :=
    subst_taut (Form.conj (Form.var 0) Form.tru) (Form.var 0)
      (fun _ => g) h (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  linarith

/-! ## 証拠側の括弧の付け替え (前提が不可能でない条件付き)

Keynes の記法 `a/bch` は証拠 bc の結合順序を持たない。内包版では
`a/((b ∧ c) ∧ h)` と `a/(b ∧ (c ∧ h))`、および `a/(b ∧ (c ∧ h))` と `a/(c ∧ (b ∧ h))`
を区別する。両者の一致は、Def.X の左右両形と認証代入から、証拠 bc が h の下で
不可能でない (bc/h ≠ 0) 条件付きで導ける。 -/

/-- 証拠側の結合: (b ∧ c)/h ≠ 0 ならば a/((b ∧ c) ∧ h) = a/(b ∧ (c ∧ h))。
証明: (a ∧ (b ∧ c))/h = a/((b ∧ c) ∧ h) · (b ∧ c)/h (Def.X 左形)、
((a ∧ b) ∧ c)/h = a/(b ∧ (c ∧ h)) · b/(c ∧ h) · c/h (Def.X 左形 2 回) で、
b/(c ∧ h) · c/h = (b ∧ c)/h、左辺どうしは認証代入 (結合律) で等しい。 -/
theorem pr_evidence_assoc (a b c h : IProp) (hbc : PrI (iand b c) h ≠ 0) :
    PrI a (iand (iand b c) h) = PrI a (iand b (iand c h)) := by
  have h1 := def_X_left_i a (iand b c) h
  have h2 := def_X_left_i (iand a b) c h
  have h3 := def_X_left_i a b (iand c h)
  have h4 := def_X_left_i b c h
  have e : PrI (iand a (iand b c)) h = PrI (iand (iand a b) c) h :=
    subst_taut (Form.conj (Form.var 0) (Form.conj (Form.var 1) (Form.var 2)))
      (Form.conj (Form.conj (Form.var 0) (Form.var 1)) (Form.var 2))
      (fun i => match i with | 0 => a | 1 => b | _ => c) h
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
          simp [evalB, h0, h1, h2])
  have : PrI a (iand (iand b c) h) * PrI (iand b c) h
      = PrI a (iand b (iand c h)) * PrI (iand b c) h := by
    rw [← h1, e, h2, h3, h4]; ring
  exact mul_right_cancel₀ hbc this

/-- 証拠側の交換: (b ∧ c)/h ≠ 0 ならば a/(b ∧ (c ∧ h)) = a/(c ∧ (b ∧ h))。
証明: ((a ∧ b) ∧ c)/h = a/(b ∧ (c ∧ h)) · (b ∧ c)/h、
((a ∧ c) ∧ b)/h = a/(c ∧ (b ∧ h)) · (c ∧ b)/h、認証代入で両左辺と (b ∧ c)/h = (c ∧ b)/h。 -/
theorem pr_evidence_comm (a b c h : IProp) (hbc : PrI (iand b c) h ≠ 0) :
    PrI a (iand b (iand c h)) = PrI a (iand c (iand b h)) := by
  have h1 := def_X_left_i (iand a b) c h
  have h2 := def_X_left_i a b (iand c h)
  have h3 := def_X_left_i b c h
  have h1' := def_X_left_i (iand a c) b h
  have h2' := def_X_left_i a c (iand b h)
  have h3' := def_X_left_i c b h
  have e : PrI (iand (iand a b) c) h = PrI (iand (iand a c) b) h :=
    subst_taut (Form.conj (Form.conj (Form.var 0) (Form.var 1)) (Form.var 2))
      (Form.conj (Form.conj (Form.var 0) (Form.var 2)) (Form.var 1))
      (fun i => match i with | 0 => a | 1 => b | _ => c) h
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
          simp [evalB, h0, h1, h2])
  have ebc : PrI (iand b c) h = PrI (iand c b) h :=
    subst_taut (Form.conj (Form.var 1) (Form.var 2)) (Form.conj (Form.var 2) (Form.var 1))
      (fun i => match i with | 0 => a | 1 => b | _ => c) h
      (by intro v; cases h1 : v 1 <;> cases h2 : v 2 <;> simp [evalB, h1, h2])
  have : PrI a (iand b (iand c h)) * PrI (iand b c) h
      = PrI a (iand c (iand b h)) * PrI (iand b c) h := by
    calc PrI a (iand b (iand c h)) * PrI (iand b c) h
        = PrI (iand (iand a b) c) h := by rw [h1, h2, h3]; ring
      _ = PrI (iand (iand a c) b) h := e
      _ = PrI a (iand c (iand b h)) * PrI (iand c b) h := by rw [h1', h2', h3']; ring
      _ = PrI a (iand c (iand b h)) * PrI (iand b c) h := by rw [ebc]
  exact mul_right_cancel₀ hbc this

/-! ## 第 XX 章 §3 の設定 (F20.1–F20.5)

h: 探究の一般的な事前データ、g: 確立したい一般化、x_1 x_2 . . . x_n: g の事例。
`x 0` は使わない (印刷の事例の添字は 1 から)。 -/

section PureInduction

open Filter Topology

/-- x_1 x_2 . . . x_n (事例の結合)。`C x 0 = itrue`, `C x (n+1) = x_{n+1} ∧ C x n`。 -/
noncomputable def C (x : ℕ → IProp) : ℕ → IProp
  | 0 => itrue
  | n + 1 => iand (x (n + 1)) (C x n)

/-- **F20.4** (folio 235): p_n = g/hx_1x_2 . . . x_n。 -/
noncomputable def p (h g : IProp) (x : ℕ → IProp) (n : ℕ) : ℝ :=
  PrI g (iand (C x n) h)

/-- **F20.5** (folio 235): y_{n+1} = x_{n+1}/hx_1x_2 . . . x_n。
添字 0 の値 `y h x 0 = 1` は印刷にない約束で、どの定理も使わない。 -/
noncomputable def y (h : IProp) (x : ℕ → IProp) : ℕ → ℝ
  | 0 => 1
  | n + 1 => PrI (x (n + 1)) (iand (C x n) h)

/-- x_1x_2 . . . x_n/h (F20.10 の左辺)。 -/
noncomputable def J (h : IProp) (x : ℕ → IProp) (n : ℕ) : ℝ := PrI (C x n) h

/-- x_1x_2 . . . x_n/ḡh (F20.11 最終形の分母第 2 項の因子)。 -/
noncomputable def Q (h g : IProp) (x : ℕ → IProp) (n : ℕ) : ℝ :=
  PrI (C x n) (iand (inot g) h)

/-- x_{r+1}/x_1x_2 . . . x_r ḡh (F20.15 の左辺、r+1 番目の事例)。
添字 0 の値 `q h g x 0 = 1` は印刷にない約束で、どの定理も使わない。 -/
noncomputable def q (h g : IProp) (x : ℕ → IProp) : ℕ → ℝ
  | 0 => 1
  | n + 1 => PrI (x (n + 1)) (iand (C x n) (iand (inot g) h))

/-- **F20.1** (folio 235、印刷形): `x_1/gh = 1, x_2/gh = 1 . . . x_n/gh = 1`
— g が与えられれば各事例の真が従う。印刷どおり添字 1 以上の全事例について仮定する
(`x 0` には何も仮定しない)。 -/
def Instances (h g : IProp) (x : ℕ → IProp) : Prop := ∀ r, PrI (x (r + 1)) (iand g h) = 1

/-- **F20.3** (folio 235): `x_1/h = x_2/h = . . . = x_n/h`。台帳の注記どおり、以下の
導出では一切使われない (どの定理もこれを仮定に取らない)。記録のために述語として置く。 -/
def EquallyLikely (h : IProp) (x : ℕ → IProp) : Prop :=
  ∀ r s, PrI (x (r + 1)) h = PrI (x (s + 1)) h

variable {h g : IProp} {x : ℕ → IProp}

/-! ## 基本補題 -/

/-- p_0 = g/h (F20.7 末尾の定義 `p_0 = g/h` と、本ファイルの `p h g x 0` の一致)。 -/
theorem p_zero : p h g x 0 = PrI g h := pr_iand_itrue_evidence g h

theorem J_zero : J h x 0 = 1 := itrue_certain h

theorem Q_zero : Q h g x 0 = 1 := itrue_certain _

theorem J_nonneg (n : ℕ) : 0 ≤ J h x n := ax_range_lo_i _ _

theorem Q_nonneg (n : ℕ) : 0 ≤ Q h g x n := ax_range_lo_i _ _

theorem p_nonneg (n : ℕ) : 0 ≤ p h g x n := ax_range_lo_i _ _

theorem y_le_one (n : ℕ) : y h x (n + 1) ≤ 1 := ax_range_hi_i _ _

theorem y_nonneg (n : ℕ) : 0 ≤ y h x (n + 1) := ax_range_lo_i _ _

theorem q_nonneg (n : ℕ) : 0 ≤ q h g x (n + 1) := ax_range_lo_i _ _

/-- **F20.10** 第 1–2 段 (folio 236): x_1 . . . x_{n+1}/h = y_{n+1} · x_1 . . . x_n/h。
Def.X 左形そのもの。 -/
theorem J_succ (n : ℕ) : J h x (n + 1) = y h x (n + 1) * J h x n :=
  def_X_left_i _ _ _

/-- **F20.16** の第 1 等式 (folio 237 脚注 1):
x_1 . . . x_{n+1}/ḡh = x_{n+1}/x_1 . . . x_n ḡh · x_1 . . . x_n/ḡh。Def.X 左形。 -/
theorem Q_succ (n : ℕ) : Q h g x (n + 1) = q h g x (n + 1) * Q h g x n :=
  def_X_left_i _ _ _

/-- x_1 . . . x_n/gh = 1: g が各事例を含意するなら結合も含意する。
帰納の各段で Th.(13.9) 内包版を使う (bgh が不整合でないことは帰納法の仮定 = 1 から)。 -/
theorem conj_certain (hx : Instances h g x) : ∀ n, PrI (C x n) (iand g h) = 1
  | 0 => itrue_certain _
  | n + 1 => by
      have ih := conj_certain hx n
      have hXl := def_X_left_i (x (n + 1)) (C x n) (iand g h)
      have h9 := th_13_9_i (x (n + 1)) (C x n) (iand g h) (hx n)
        (by rw [ih]; exact one_ne_zero)
      show PrI (iand (x (n + 1)) (C x n)) (iand g h) = 1
      rw [hXl, h9, ih, mul_one]

/-! ## F20.10, F20.11 第 1 等式, F20.7, F20.6, F20.9 -/

/-- **F20.10** (folio 236): x_1x_2 . . . x_n/h = y_n y_{n-1} . . . y_1。 -/
theorem th_20_10_src (n : ℕ) :
    J h x n = ∏ i ∈ Finset.range n, y h x (i + 1) := by
  induction n with
  | zero => simp [J_zero]
  | succ n ih => rw [J_succ, ih, Finset.prod_range_succ, mul_comm]

/-- **F20.11** 第 1 等式の乗法形: p_n · x_1 . . . x_n/h = p_0。
Def.X の左形 (g x_1…x_n)/h = g/hx_1…x_n · x_1…x_n/h と右形
(g x_1…x_n)/h = x_1…x_n/gh · g/h、および x_1…x_n/gh = 1 (F20.1)。
本ファイルの主経路では F20.6/F20.7 をこの等式の系として得る (ヘッダ参照)。 -/
theorem th_20_11_first (hx : Instances h g x) (n : ℕ) :
    p h g x n * J h x n = PrI g h := by
  have hl := def_X_left_i g (C x n) h
  have hr := def_X_right_i g (C x n) h
  rw [conj_certain hx n, one_mul] at hr
  unfold p J
  rw [← hl, hr]

/-- **F20.7** (folio 235): p_n = 1/(y_1y_2 . . . y_n) · p_0, p_0 = g/h。印刷の除法形。
条件 y_1…y_n ≠ 0 (= x_1…x_n/h ≠ 0、前提 hx_1…x_n が不可能でない)。 -/
theorem th_20_7_src (hx : Instances h g x) (n : ℕ)
    (hy : ∏ i ∈ Finset.range n, y h x (i + 1) ≠ 0) :
    p h g x n = 1 / (∏ i ∈ Finset.range n, y h x (i + 1)) * PrI g h := by
  have e := th_20_11_first hx n
  rw [th_20_10_src] at e
  field_simp
  linarith

/-- **F20.6** (folio 235) 乗法形: p_{n+1} · y_{n+1} = p_n、
条件 x_1…x_n/h ≠ 0。F20.11 第 1 等式を n と n+1 で比べて得る。 -/
theorem th_20_6 (hx : Instances h g x) (n : ℕ) (hJ : J h x n ≠ 0) :
    p h g x (n + 1) * y h x (n + 1) = p h g x n := by
  have a := th_20_11_first hx (n + 1)
  have b := th_20_11_first hx n
  rw [J_succ] at a
  have : p h g x (n + 1) * y h x (n + 1) * J h x n = p h g x n * J h x n := by
    rw [mul_assoc, a, b]
  exact mul_right_cancel₀ hJ this

/-- **F20.6/F20.7** 第 1・3・4 段の連鎖 (印刷の第 2 段を経ない): p_{n+1}/p_n = 1/y_{n+1}
(印刷は p_n/p_{n-1} = 1/y_n)。条件 x_1…x_n/h ≠ 0 かつ p_n ≠ 0。 -/
theorem th_20_6_lines134 (hx : Instances h g x) (n : ℕ) (hJ : J h x n ≠ 0)
    (hp : p h g x n ≠ 0) :
    p h g x (n + 1) / p h g x n = 1 / y h x (n + 1) := by
  have e := th_20_6 hx n hJ
  have hy : y h x (n + 1) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e; exact hp e.symm
  rw [div_eq_div_iff hp hy, one_mul]
  exact e

/-! ### F20.6 の印刷経路 (folio 235、4 段) と E-III-1

印刷の 4 段 (添字を n+1 にずらして書く):
  p_{n+1}/p_n = g/hx_1…x_{n+1} / g/hx_1…x_n                                   (第 1 段)
              = x_{n+1}/hx_1…x_n / (g/hx_1…x_n · x_{n+1}/hx_1…x_n)              (第 2 段、印刷)
              = x_{n+1}/ghx_1…x_n / x_{n+1}/hx_1…x_n                            (第 3 段)
              = 1/y_{n+1}                                                        (第 4 段)
第 2 段の分子は印刷では `x_n/hx_1…x_{n−1}` で、第 1 段・第 3 段と整合するには
結合確率 `g x_n/hx_1…x_{n−1}` でなければならない (g 脱落、台帳の誤植フラグ 1)。 -/

/-- 結合確率 g x_{n+1}/hx_1…x_n = p_{n+1} · y_{n+1}。Def.X 左形と証拠側の結合
(条件 x_1…x_{n+1}/h ≠ 0)。 -/
theorem joint_eq (n : ℕ) (hJ : J h x (n + 1) ≠ 0) :
    PrI (iand g (x (n + 1))) (iand (C x n) h) = p h g x (n + 1) * y h x (n + 1) := by
  have hXl := def_X_left_i g (x (n + 1)) (iand (C x n) h)
  have ha := pr_evidence_assoc g (x (n + 1)) (C x n) h hJ
  unfold p y
  rw [hXl, ← ha]
  rfl

/-- **F20.6 訂正形** (folio 235、第 2 段の分子に g を復した 4 段):
第 1 段 = 第 2 段 (g x_{n+1}/hx_1…x_n を分子とする)、第 2 段 = 第 3 段、第 3 段 = 第 4 段。
条件: p_0 ≠ 0 (第 3 段で x_{n+1}/ghx_1…x_n に移るとき gx_1…x_n/h = p_0 ≠ 0 が要る) と
x_1…x_{n+1}/h ≠ 0 (前提 hx_1…x_{n+1} が不可能でない)。 -/
theorem th_20_6_cor (hx : Instances h g x) (n : ℕ) (hp0 : PrI g h ≠ 0)
    (hJ : J h x (n + 1) ≠ 0) :
    p h g x (n + 1) / p h g x n
        = PrI (iand g (x (n + 1))) (iand (C x n) h) / (p h g x n * y h x (n + 1)) ∧
    PrI (iand g (x (n + 1))) (iand (C x n) h) / (p h g x n * y h x (n + 1))
        = PrI (x (n + 1)) (iand g (iand (C x n) h)) / y h x (n + 1) ∧
    PrI (x (n + 1)) (iand g (iand (C x n) h)) / y h x (n + 1) = 1 / y h x (n + 1) := by
  have hy : y h x (n + 1) ≠ 0 := by
    intro h0; apply hJ; rw [J_succ, h0, zero_mul]
  have hpn : p h g x n ≠ 0 := by
    intro h0; apply hp0; rw [← th_20_11_first hx n, h0, zero_mul]
  have hjoint := joint_eq (g := g) n hJ
  have hXr := def_X_right_i g (x (n + 1)) (iand (C x n) h)
  have hp_def : PrI g (iand (C x n) h) = p h g x n := rfl
  have hcert : PrI (x (n + 1)) (iand g (iand (C x n) h)) = 1 := by
    have hgC : PrI (iand g (C x n)) h ≠ 0 := by
      rw [def_X_right_i g (C x n) h, conj_certain hx n, one_mul]; exact hp0
    rw [pr_evidence_comm (x (n + 1)) g (C x n) h hgC]
    exact th_13_9_i _ _ _ (hx n) (by rw [conj_certain hx n]; exact one_ne_zero)
  refine ⟨?_, ?_, ?_⟩
  · rw [hjoint, mul_div_mul_right _ _ hy]
  · rw [hXr, hp_def, mul_comm (PrI (x (n + 1)) _) (p h g x n), mul_div_mul_left _ _ hpn]
  · rw [hcert]

/-- **F20.6 印刷形の第 2 段** (folio 235、E-III-1): 印刷の分子 x_{n+1}/hx_1…x_n (g 脱落) の
ままでは、第 2 段の右辺は y_{n+1}/(p_n · y_{n+1}) = 1/p_n であり、第 1 段 p_{n+1}/p_n と
等しいのは p_{n+1} = 1 のとき、かつそのときに限る。すなわち印刷の第 2 段は
「どの事例も一般化を確実にする」と主張しており、p_{n+1} ≠ 1 なら偽である。
条件は `th_20_6_cor` と同じ。 -/
theorem th_20_6_src (hx : Instances h g x) (n : ℕ) (hp0 : PrI g h ≠ 0)
    (hJ : J h x (n + 1) ≠ 0) :
    p h g x (n + 1) / p h g x n = y h x (n + 1) / (p h g x n * y h x (n + 1)) ↔
      p h g x (n + 1) = 1 := by
  have hJn : J h x n ≠ 0 := by
    intro h0; apply hJ; rw [J_succ, h0, mul_zero]
  have hy : y h x (n + 1) ≠ 0 := by
    intro h0; apply hJ; rw [J_succ, h0, zero_mul]
  have hpn : p h g x n ≠ 0 := by
    intro h0; apply hp0; rw [← th_20_11_first hx n, h0, zero_mul]
  have e := th_20_6 hx n hJn
  have hr : y h x (n + 1) / (p h g x n * y h x (n + 1)) = 1 / p h g x n := by
    field_simp
  rw [hr, th_20_6_lines134 hx n hJn hpn, one_div, one_div, inv_inj]
  constructor
  · intro hyp
    rw [hyp] at e
    exact mul_right_cancel₀ hpn (by rw [e, one_mul])
  · intro h1
    rw [h1, one_mul] at e
    exact e

/-- **F20.9** (folio 236): `p_n > p_{n-1} so long as y_n ≠ 1`。
Keynes が明示しない前提 p_n > 0 と x_1…x_n/h ≠ 0 を付す (台帳 F20.9 注記)。
両前提の必要性は `th_20_9_needs_p_pos`, `th_20_9_J_zero`, `Witness_F20_9_J` を参照。 -/
theorem th_20_9_src (hx : Instances h g x) (n : ℕ) (hJ : J h x n ≠ 0)
    (hp : 0 < p h g x n) (hy : y h x (n + 1) ≠ 1) :
    p h g x n < p h g x (n + 1) := by
  have e := th_20_6 hx n hJ
  have hy1 : y h x (n + 1) < 1 := lt_of_le_of_ne (y_le_one n) hy
  have hy0 := y_nonneg (h := h) (x := x) n
  have hp1 : 0 < p h g x (n + 1) := by
    by_contra hc
    have hc' : p h g x (n + 1) ≤ 0 := not_lt.mp hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc' hy0]
  nlinarith [mul_lt_mul_of_pos_left hy1 hp1]

/-- **F20.9** の双条件形: 同じ前提の下で p_n > p_{n-1} であることと y_n ≠ 1 とは同値
(y_n = 1 なら p_n = p_{n-1})。 -/
theorem th_20_9_iff (hx : Instances h g x) (n : ℕ) (hJ : J h x n ≠ 0)
    (hp : 0 < p h g x n) :
    p h g x n < p h g x (n + 1) ↔ y h x (n + 1) ≠ 1 := by
  constructor
  · intro hlt hy1
    have e := th_20_6 hx n hJ
    rw [hy1, mul_one] at e
    rw [e] at hlt
    exact lt_irrefl _ hlt
  · exact th_20_9_src hx n hJ hp

/-- **F20.9 の前提 p_{n-1} > 0 の必要性** (公理群の中で): F20.1 と y_n ≠ 0 のもとで
p_{n-1} = 0 ならば p_n = 0 (乗法形 F20.6 から) で、p_n > p_{n-1} は成り立たない。 -/
theorem th_20_9_needs_p_pos (hx : Instances h g x) (n : ℕ) (hJ : J h x n ≠ 0)
    (hy : y h x (n + 1) ≠ 0) (hp : p h g x n = 0) :
    ¬ (p h g x n < p h g x (n + 1)) := by
  have e := th_20_6 hx n hJ
  rw [hp] at e ⊢
  have h0 : p h g x (n + 1) = 0 := by
    rcases mul_eq_zero.mp e with h0 | h0
    · exact h0
    · exact absurd h0 hy
  rw [h0]
  exact lt_irrefl 0

/-- **F20.9 の前提 x_1…x_n/h ≠ 0 を落とすと**: x_1…x_n/h = 0 ならば p_0 = 0 (一般化は
事前に不可能) で、以後の x_1…x_m/h もすべて 0。p_n, p_{n+1} は公理群で定まらない
(関係式の数値例は `Witness_F20_9_J`)。 -/
theorem th_20_9_J_zero (hx : Instances h g x) (n : ℕ) (hJ : J h x n = 0) :
    PrI g h = 0 ∧ J h x (n + 1) = 0 :=
  ⟨by rw [← th_20_11_first hx n, hJ, mul_zero], by rw [J_succ, hJ, mul_zero]⟩

/-- **F20.13** (folio 236 脚注 1): `Since p_n > p_{n-1} so long as y_n ≠ 1` — F20.9 の再掲。 -/
theorem th_20_13_src (hx : Instances h g x) (n : ℕ) (hJ : J h x n ≠ 0)
    (hp : 0 < p h g x n) (hy : y h x (n + 1) ≠ 1) :
    p h g x n < p h g x (n + 1) :=
  th_20_9_src hx n hJ hp hy

/-! ## S-III-1: 訳書の条件「y_n > 1」は空条件 (訳書は未照合)

佐藤訳 p. 273 が「y_n > 1」と印刷しているという報告は本ファイルでは未照合である
(本ファイルの作成時に訳書の該当頁を確認していない)。初版 folio 236 は `y_n ≠ 1`。
以下はもし訳書が「y_n > 1」なら何が起きるかの判定である。 -/

/-- **S-III-1**: 「y_n > 1」は確率の上限 (ax_range_hi) に反し、どの n についても成り立たない。 -/
theorem th_S_III_1 (n : ℕ) : ¬ (1 < y h x (n + 1)) :=
  not_lt.mpr (y_le_one n)

/-- S-III-1 の帰結: 「y_n > 1 であるかぎり p_n > p_{n-1}」は前件が常に偽なので
いかなる仮定もなしに空虚に成り立つ (主張として内容を持たない)。 -/
theorem th_S_III_1_vacuous (n : ℕ) (hy : 1 < y h x (n + 1)) :
    p h g x n < p h g x (n + 1) :=
  absurd hy (th_S_III_1 n)

/-! ## F20.11 閉形式 (folio 236) -/

/-- **F20.11** 第 2–4 段: x_1…x_n/h = x_1…x_n g/h + x_1…x_n ḡ/h (加法定理 = Def.IX の
g/ḡ 分解) = g/h + x_1…x_n/ḡh · ḡ/h = p_0 + x_1…x_n/ḡh (1 − p_0)。
x_1…x_n g/h = x_1…x_n/gh · g/h = 1 · p_0 は F20.1 (conj_certain) による。 -/
theorem th_20_11_denom (hx : Instances h g x) (n : ℕ) :
    J h x n = PrI g h + Q h g x n * (1 - PrI g h) := by
  have hIX := def_IX_i (C x n) g h
  have h1 := def_X_left_i (C x n) g h
  rw [conj_certain hx n, one_mul] at h1
  have h2 := def_X_left_i (C x n) (inot g) h
  have h3 := th_13_1_i g h
  have hneg : PrI (inot g) h = 1 - PrI g h := by linarith
  rw [hneg] at h2
  unfold J Q
  linarith

/-- **F20.11** 最終形 (folio 236、印刷形):
p_n = p_0 / (p_0 + x_1x_2 . . . x_n/ḡh (1 − p_0))。条件: 分母 ≠ 0
(必要性は `th_20_11_den_zero`, `Witness_F20_11_den`)。 -/
theorem th_20_11_src (hx : Instances h g x) (n : ℕ)
    (hden : PrI g h + Q h g x n * (1 - PrI g h) ≠ 0) :
    p h g x n = PrI g h / (PrI g h + Q h g x n * (1 - PrI g h)) := by
  have a := th_20_11_first hx n
  rw [th_20_11_denom hx n] at a
  rw [eq_div_iff hden]
  exact a

/-- **F20.11 の分母 ≠ 0 を落とすと**: 分母 = 0 は p_0 = 0 かつ x_1…x_n/ḡh = 0 と同値で、
そのとき x_1…x_n/h = 0 (前提 hx_1…x_n が不可能) となり、p_n は公理群で定まらない。 -/
theorem th_20_11_den_zero (hx : Instances h g x) (n : ℕ)
    (hden : PrI g h + Q h g x n * (1 - PrI g h) = 0) :
    PrI g h = 0 ∧ Q h g x n = 0 ∧ J h x n = 0 := by
  have h0 := ax_range_lo_i g h
  have h1 := ax_range_hi_i g h
  have hQ := Q_nonneg (h := h) (g := g) (x := x) n
  have hprod : 0 ≤ Q h g x n * (1 - PrI g h) := mul_nonneg hQ (by linarith)
  have hp0 : PrI g h = 0 := by linarith
  have hQ0 : Q h g x n = 0 := by
    rw [hp0, zero_add, sub_zero, mul_one] at hden
    exact hden
  refine ⟨hp0, hQ0, ?_⟩
  rw [th_20_11_denom hx n, hp0, hQ0]
  ring

/-- p_0 > 0 ならば分母は p_0 以上で、特に 0 でない (Q_n ≥ 0, 1 − p_0 ≥ 0)。 -/
theorem denom_ge_p0 (n : ℕ) :
    PrI g h ≤ PrI g h + Q h g x n * (1 - PrI g h) := by
  have hq := Q_nonneg (h := h) (g := g) (x := x) n
  have h1 := ax_range_hi_i g h
  nlinarith

/-! ## F20.12, F20.14: 極限への移行 -/

/-- 補題: p_0 > 0 かつ x_1…x_n/ḡh → 0 ならば p_n → 1。
F20.11 の閉形式と Mathlib の商の極限。 -/
theorem limit_of_Q (hx : Instances h g x) (hp0 : 0 < PrI g h)
    (hQ : Tendsto (Q h g x) atTop (𝓝 0)) :
    Tendsto (p h g x) atTop (𝓝 1) := by
  have hden : ∀ n, PrI g h + Q h g x n * (1 - PrI g h) ≠ 0 :=
    fun n => ne_of_gt (lt_of_lt_of_le hp0 (denom_ge_p0 n))
  have hD : Tendsto (fun n => PrI g h + Q h g x n * (1 - PrI g h)) atTop
      (𝓝 (PrI g h + 0 * (1 - PrI g h))) :=
    tendsto_const_nhds.add (hQ.mul_const _)
  rw [zero_mul, add_zero] at hD
  have hdiv : Tendsto (fun n => PrI g h / (PrI g h + Q h g x n * (1 - PrI g h))) atTop
      (𝓝 (PrI g h / PrI g h)) :=
    tendsto_const_nhds.div hD (ne_of_gt hp0)
  rw [div_self (ne_of_gt hp0)] at hdiv
  refine hdiv.congr fun n => ?_
  exact (th_20_11_src hx n (hden n)).symm

/-- **F20.12** (folio 236): `This approaches unity as a limit, if x_1x_2 . . . x_n/ḡh . 1/p_0
approaches zero as a limit, when n increases.` 条件 p_0 > 0 を付す
(必要性は `th_20_12_p0_zero`)。 -/
theorem th_20_12_src (hx : Instances h g x) (hp0 : 0 < PrI g h)
    (hQ : Tendsto (fun n => Q h g x n * (1 / PrI g h)) atTop (𝓝 0)) :
    Tendsto (p h g x) atTop (𝓝 1) := by
  apply limit_of_Q hx hp0
  have := hQ.mul_const (PrI g h)
  rw [zero_mul] at this
  refine this.congr fun n => ?_
  field_simp

/-- **F20.12 の前提 p_0 > 0 を落とすと** (公理群の中で): p_0 = 0 のとき、F20.12 の仮定
x_1…x_n/ḡh · 1/p_0 → 0 は (1/0 = 0 の約束で) 自動的に成り立つが、
各 x_1…x_n/ḡh ≠ 0 である限り p_n = 0 で、p_n → 1 は成り立たない。 -/
theorem th_20_12_p0_zero (hx : Instances h g x) (hp0 : PrI g h = 0)
    (hQ : ∀ n, Q h g x n ≠ 0) :
    Tendsto (fun n => Q h g x n * (1 / PrI g h)) atTop (𝓝 0) ∧
    (∀ n, p h g x n = 0) ∧ ¬ Tendsto (p h g x) atTop (𝓝 1) := by
  have hp : ∀ n, p h g x n = 0 := fun n => by
    have e := th_20_11_first hx n
    rw [hp0, th_20_11_denom hx n, hp0, zero_add, sub_zero, mul_one] at e
    exact (mul_eq_zero.mp e).resolve_right (hQ n)
  refine ⟨?_, hp, ?_⟩
  · simp [hp0]
  · intro ht
    have h0 : Tendsto (p h g x) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (0 : ℝ))).congr fun n => (hp n).symm
    have := tendsto_nhds_unique ht h0
    norm_num at this

/-- **F20.14** (folio 237): 「x_1…x_n/ḡh が p_0 に比べて小さくなる」は F20.12 の言い換え。
p_0 > 0 の下で、x_1…x_n/ḡh · 1/p_0 → 0 と x_1…x_n/ḡh → 0 は同値。 -/
theorem th_20_14 (hp0 : 0 < PrI g h) :
    Tendsto (fun n => Q h g x n * (1 / PrI g h)) atTop (𝓝 0) ↔
      Tendsto (Q h g x) atTop (𝓝 0) := by
  constructor
  · intro hQ
    have := hQ.mul_const (PrI g h)
    rw [zero_mul] at this
    refine this.congr fun n => ?_
    field_simp
  · intro hQ
    have := hQ.mul_const (1 / PrI g h)
    rwa [zero_mul] at this

/-! ## F20.15–F20.17: 極限定理とその脚注証明 (folio 237) -/

/-- **F20.16** の包含形 (≤ 版): 条件 x_{r+1}/x_1…x_r ḡh ≤ 1 − ε (全 r) の下で
x_1x_2 . . . x_n/ḡh ≤ (1 − ε)^n。乗法定理と不等式の帰納。 -/
theorem th_20_16_le {ε : ℝ} (hε1 : ε ≤ 1)
    (hq : ∀ r, q h g x (r + 1) ≤ 1 - ε) (n : ℕ) :
    Q h g x n ≤ (1 - ε) ^ n := by
  induction n with
  | zero => rw [Q_zero, pow_zero]
  | succ n ih =>
      rw [Q_succ, pow_succ']
      exact mul_le_mul (hq n) ih (Q_nonneg n) (by linarith)

-- 次の定理に限り未使用前提の警告を止める (印刷の前提 p_0 > η を置くため、下記参照)。
set_option linter.unusedVariables false in
/-- **F20.16** (folio 237 脚注 1、印刷形):
`x_1x_2 . . . x_n/ḡh = x_n/x_1x_2 . . . x_{n-1}ḡh . x_1x_2 . . . x_{n-1}/ḡh < (1 − ε)^n,
where ε is finite and p_0 > η where η is finite.`
前提は印刷どおり x_r/x_1…x_{r−1}ḡh < 1 − ε (全 r) と p_0 > η、結論は n ≥ 1 について
等式 (Def.X 左形) と狭義不等式。ε ≤ 1 は前提から出る (0 ≤ x_1/ḡh < 1 − ε)。
印刷の前提 p_0 > η は表示式の導出には使われない (脚注の次文 F20.17 の前提であり、
`th_20_17_bound` で使う)。 -/
theorem th_20_16_src {ε η : ℝ} (hq : ∀ r, q h g x (r + 1) < 1 - ε) (hp0 : η < PrI g h)
    (n : ℕ) (hn : 1 ≤ n) :
    Q h g x n = q h g x n * Q h g x (n - 1) ∧ Q h g x n < (1 - ε) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hε1 : 0 < 1 - ε := lt_of_le_of_lt (q_nonneg (h := h) (g := g) (x := x) 0) (hq 0)
  refine ⟨by rw [Nat.add_sub_cancel]; exact Q_succ m, ?_⟩
  rw [Q_succ, pow_succ']
  have hle := th_20_16_le (by linarith) (fun r => (hq r).le) m
  have hQ := Q_nonneg (h := h) (g := g) (x := x) m
  rcases hQ.lt_or_eq with hpos | hzero
  · calc q h g x (m + 1) * Q h g x m < (1 - ε) * Q h g x m :=
          mul_lt_mul_of_pos_right (hq m) hpos
      _ ≤ (1 - ε) * (1 - ε) ^ m := mul_le_mul_of_nonneg_left hle hε1.le
  · rw [← hzero, mul_zero]
    exact mul_pos hε1 (pow_pos hε1 m)

/-- **F20.20** 用の一般化: s 以降の r についてのみ条件を課すと
x_1…x_{s+m}/ḡh ≤ x_1…x_s/ḡh · (1 − ε)^m。 -/
theorem Q_le_of_tail {ε : ℝ} (hε1 : ε ≤ 1) (s : ℕ)
    (hq : ∀ r, s ≤ r → q h g x (r + 1) ≤ 1 - ε) :
    ∀ m, Q h g x (s + m) ≤ Q h g x s * (1 - ε) ^ m
  | 0 => by rw [add_zero, pow_zero, mul_one]
  | m + 1 => by
      have ih := Q_le_of_tail hε1 s hq m
      rw [← add_assoc, Q_succ, pow_succ']
      calc q h g x (s + m + 1) * Q h g x (s + m)
          ≤ (1 - ε) * (Q h g x s * (1 - ε) ^ m) :=
            mul_le_mul (hq (s + m) (Nat.le_add_right s m)) ih (Q_nonneg _) (by linarith)
        _ = Q h g x s * ((1 - ε) * (1 - ε) ^ m) := by ring

/-- **F20.17** 前半 (folio 237 脚注 1): (1 − ε)^n → 0 (0 < ε ≤ 1)。 -/
theorem th_20_17_pow {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Tendsto (fun n : ℕ => (1 - ε) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

/-- **F20.17** (folio 237 脚注 1、印刷形): `There is always, under these conditions, some
finite value of n such that both (1 − ε)^n and (1 − ε)^n/η are less than any given finite
quantity, however small.` ε, η は有限確率 (0 < ε ≤ 1, 0 < η)。
(Mathlib の x/0 = 0 の約束の下では η = 0 でも式自体は成り立つが、印刷の読みに従い
0 < η を前提に置き、証明でも (1 − ε)^n < δη から (1 − ε)^n/η < δ を出すのに使う。) -/
theorem th_20_17_src {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, (1 - ε) ^ n < δ ∧ (1 - ε) ^ n / η < δ := by
  have hpos : 0 < min δ (δ * η) := lt_min hδ (mul_pos hδ hη)
  obtain ⟨N, hN⟩ := ((th_20_17_pow hε hε1).eventually_lt_const hpos).exists
  refine ⟨N, lt_of_lt_of_le hN (min_le_left _ _), ?_⟩
  rw [div_lt_iff₀ hη]
  exact lt_of_lt_of_le hN (min_le_right _ _)

/-- **F20.17** の評価 (台帳 F20.17 主張): F20.11 分母第 2 項を p_0 で割ったもの
x_1…x_n/ḡh (1 − p_0)/p_0 は (1 − ε)^n/η で上から抑えられる (p_0 ≥ η > 0)。 -/
theorem th_20_17_bound {ε η : ℝ} (hε1 : ε ≤ 1) (hη : 0 < η) (hp0 : η ≤ PrI g h)
    (hq : ∀ r, q h g x (r + 1) ≤ 1 - ε) (n : ℕ) :
    Q h g x n * (1 - PrI g h) / PrI g h ≤ (1 - ε) ^ n / η := by
  have hQ := Q_nonneg (h := h) (g := g) (x := x) n
  have h1 := ax_range_hi_i g h
  have hle := th_20_16_le hε1 hq n
  have hnum : Q h g x n * (1 - PrI g h) ≤ (1 - ε) ^ n := by nlinarith
  exact div_le_div₀ (le_trans hQ hle) hnum hη hp0

/-- **F20.15** (folio 237、包含形): ∀ r, x_{r+1}/x_1…x_r ḡh ≤ 1 − ε かつ p_0 ≥ η
(ε, η は有限確率: 0 < ε ≤ 1, 0 < η) ならば p_n → 1。 -/
theorem th_20_15 (hx : Instances h g x) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hp0 : η ≤ PrI g h)
    (hq : ∀ r, q h g x (r + 1) ≤ 1 - ε) :
    Tendsto (p h g x) atTop (𝓝 1) := by
  apply limit_of_Q hx (lt_of_lt_of_le hη hp0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (th_20_17_pow hε hε1)
    (fun n => Q_nonneg n) (th_20_16_le hε1 hq)

/-- **F20.15** (folio 237、印刷形): `x_r/x_1x_2 . . . x_{r-1}ḡh < 1 − ε for all values of r,
and p_0 > η` (狭義不等号)。包含形の系。 -/
theorem th_20_15_src (hx : Instances h g x) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hp0 : η < PrI g h)
    (hq : ∀ r, q h g x (r + 1) < 1 - ε) :
    Tendsto (p h g x) atTop (𝓝 1) :=
  th_20_15 hx hε hε1 hη hp0.le (fun r => (hq r).le)

/-- **F20.19** (folio 238 §6、言語的再掲): (1) x_r/x_1…x_{r−1}ḡh が確実性から有限量だけ
離れている (∃ ε, 0 < ε ≤ 1, …)、(2) p_0 が不可能性から有限量だけ離れている (∃ η > 0, η ≤ p_0)。 -/
theorem th_20_19_src (hx : Instances h g x)
    (h1 : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ r, q h g x (r + 1) ≤ 1 - ε)
    (h2 : ∃ η : ℝ, 0 < η ∧ η ≤ PrI g h) :
    Tendsto (p h g x) atTop (𝓝 1) := by
  obtain ⟨ε, hε, hε1, hq⟩ := h1
  obtain ⟨η, hη, hp0⟩ := h2
  exact th_20_15 hx hε hε1 hη hp0 hq

/-! ## F20.18: Keynes 自身の極限の定義 (folio 237 脚注 2) -/

/-- 確実性の測度 γ。数値確率の尺度では γ = 1。 -/
noncomputable def γ_certainty : ℝ := 1

/-- **F20.18** (folio 237 脚注 2): `a series of probabilities p_1p_2 . . . p_r approaches a
limit L, if, given any positive finite number ε however small, a positive integer n can
always be found such that for all values of r greater than n the difference between L and
p_r is less than ε . γ`。 -/
def KeynesLimit (p : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∀ r, n < r → |L - p r| < ε * γ_certainty

/-- **F20.18** と Mathlib の `Filter.Tendsto` の一致。 -/
theorem th_20_18_src (p : ℕ → ℝ) (L : ℝ) :
    KeynesLimit p L ↔ Tendsto p atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro H ε hε
    obtain ⟨n, -, hn⟩ := H ε hε
    refine ⟨n + 1, fun r hr => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    simpa [γ_certainty] using hn r (by omega)
  · intro H ε hε
    obtain ⟨N, hN⟩ := H ε hε
    refine ⟨N + 1, Nat.succ_pos N, fun r hr => ?_⟩
    rw [γ_certainty, mul_one, abs_sub_comm, ← Real.dist_eq]
    exact hN r (by omega)

/-! ## F20.20: §6 の一般化 (folio 238) -/

/-- **F20.20** (folio 238 §6): (1) 指定された値 s を超える r について
x_r/x_1…x_{r−1}ḡh ≤ 1 − ε、(2) p_s (最初の s 事例を知った上での一般化の確率) ≥ η > 0、
かつ前提 hx_1…x_s が不可能でない (x_1…x_s/h ≠ 0) ならば p_n → 1。
Keynes は「exactly similar argument」と述べて証明を省く。ここでは p_0 = p_s · x_1…x_s/h > 0
を F20.11 第 1 等式から取り出し、x_1…x_n/ḡh ≤ x_1…x_s/ḡh (1 − ε)^{n−s} で挟む。
足した前提 x_1…x_s/h ≠ 0 の必要性は `th_20_20_Js_zero`, `Witness_F20_20_Js`。 -/
theorem th_20_20_src (hx : Instances h g x) (s : ℕ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hJs : J h x s ≠ 0) (hps : η ≤ p h g x s)
    (hq : ∀ r, s ≤ r → q h g x (r + 1) ≤ 1 - ε) :
    Tendsto (p h g x) atTop (𝓝 1) := by
  have hp0 : 0 < PrI g h := by
    rw [← th_20_11_first hx s]
    have hJpos : 0 < J h x s := lt_of_le_of_ne (J_nonneg s) (Ne.symm hJs)
    exact mul_pos (lt_of_lt_of_le hη hps) hJpos
  apply limit_of_Q hx hp0
  have hb : Tendsto (fun n : ℕ => Q h g x s * (1 - ε) ^ (n - s)) atTop (𝓝 (Q h g x s * 0)) :=
    ((th_20_17_pow hε hε1).comp (tendsto_sub_atTop_nat s)).const_mul _
  rw [mul_zero] at hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun n => Q_nonneg n) ?_
  rw [eventually_atTop]
  refine ⟨s, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left]
  exact Q_le_of_tail hε1 s hq m

/-- **F20.20 の前提 x_1…x_s/h ≠ 0 を落とすと** (公理群の中で): x_1…x_s/h = 0 ならば
p_0 = 0 で、以後の x_1…x_{s+m}/h もすべて 0。p_s ≥ η > 0 から p_0 > 0 は出ず、
p_n (n ≥ s) は公理群で定まらない (関係式の数値例は `Witness_F20_20_Js`)。 -/
theorem th_20_20_Js_zero (hx : Instances h g x) (s : ℕ) (hJs : J h x s = 0) :
    PrI g h = 0 ∧ ∀ m, J h x (s + m) = 0 := by
  refine ⟨by rw [← th_20_11_first hx s, hJs, mul_zero], ?_⟩
  intro m
  induction m with
  | zero => rw [add_zero]; exact hJs
  | succ m ih => rw [← add_assoc, J_succ, ih, mul_zero]

/-! ## E-III-2: 第 XXII 章 folio 254 の条件式 `x_r/x_1x_2 . . . x_{r-1}ḡh = 1 − ε`

folio 254 は `g/h = p_0, where p_0 is finite`, `x_r/gh = 1, etc.`, および
`x_r/x_1x_2 . . . x_{r-1}ḡh = 1 − ε, where ε is finite` を置き、「第 XX 章の議論により」
極限が出るとする。第 XX 章 (folio 237) の条件は `< 1 − ε` である。機械判定: -/

/-- **E-III-2 (a)**: 等号版は、同じ ε について第 XX 章の印刷前提 `< 1 − ε` を満たさない。 -/
theorem th_E_III_2_not_lt {ε : ℝ} (hq : ∀ r, q h g x (r + 1) = 1 - ε) (r : ℕ) :
    ¬ (q h g x (r + 1) < 1 - ε) := by
  rw [hq r]
  exact lt_irrefl _

/-- **E-III-2 (b)**: 等号版では x_1…x_n/ḡh = (1 − ε)^n が等式で定まる
(F20.16 の第 1 等式の帰納)。 -/
theorem th_22_254_eq_exact {ε : ℝ} (hq : ∀ r, q h g x (r + 1) = 1 - ε) (n : ℕ) :
    Q h g x n = (1 - ε) ^ n := by
  induction n with
  | zero => rw [Q_zero, pow_zero]
  | succ n ih => rw [Q_succ, pow_succ', hq, ih]

/-- **E-III-2 (b) の帰結**: 等号版からは脚注 F20.16 の狭義不等式 `< (1 − ε)^n` が
反証される (等式が成り立つので狭義不等式は成り立たない)。 -/
theorem th_E_III_2_refutes_F20_16 {ε : ℝ} (hq : ∀ r, q h g x (r + 1) = 1 - ε) (n : ℕ) :
    ¬ (Q h g x n < (1 - ε) ^ n) := by
  rw [th_22_254_eq_exact hq n]
  exact lt_irrefl _

/-- **E-III-2 (c)**: 極限そのものは、ε/2 を取れば第 XX 章の印刷形 `th_20_15_src`
(前提 `< 1 − ε/2`, `p_0 > η`) から出る。folio 254 の等号は結論を壊さない。 -/
theorem th_22_254_eq_src (hx : Instances h g x) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hp0 : η < PrI g h)
    (hq : ∀ r, q h g x (r + 1) = 1 - ε) :
    Tendsto (p h g x) atTop (𝓝 1) :=
  th_20_15_src hx (ε := ε / 2) (by linarith) (by linarith) hη hp0
    (fun r => by rw [hq r]; linarith)

/-- **E-III-2 (d)**: 等号版は包含形 (≤) の前提を含意する。 -/
theorem th_E_III_2_eq_imp_le {ε : ℝ} (hq : ∀ r, q h g x (r + 1) = 1 - ε) :
    ∀ r, q h g x (r + 1) ≤ 1 - ε :=
  fun r => (hq r).le

/-! ## F20.8, F20.21 (形式化対象外、記録のみ)

* F20.8 (folio 235 脚注 1): `φ(x) ≡ 'x can be inferred from h', f(x) ≡ x, then g(φ, f) ≡ h`。
  一般化を関数記法 g(φ, f) で扱う第 XVIII–XIX 章の枠組みを要し、本ファイルの公理群の
  外にある (台帳: needs extra principle)。
* F20.21 (folio 238 §7): 逆確率に基づく帰納原理の「証明」は p_0 の大きさに関する不当な
  仮定で損なわれているという批判。記号は p_0 のみで、形式化対象ではない (台帳: no)。
  F20.15/F20.20 が p_0 (または p_s) の下界 η を仮定に明示していることが、この批判の
  機械的な対応物である。 -/

end PureInduction

/-! ## 公理群の検査 (要裁定): 本ファイルの公理群 (= phase6c の部分集合) は不整合

Keynes 第 XII 章の公理 (i) は「h が不整合な連言でない」場合に限って確率関係 a/h を
置く (folio 未照合: 本リポジトリの画像は folio 139 から)。本ファイルと phase6c の
`def_VIII_i` と `ax_iii_taut` はこの但し書きを持たず、任意の証拠 h について成り立つと
述べる。両者を不整合な証拠 `(¬⊤) ∧ ⊤` に適用すると矛盾する:
  * a ↔ a は恒真なので (a ≡ a)/h = 1 (ax_iii_taut)、Def.VIII (→) から a/(a ∧ h) = 1。
    a = ¬⊤ とすると (¬⊤)/((¬⊤) ∧ ⊤) = 1。
  * 補完律 (th_13_1_i) と ⊤/k = 1 から、任意の k について (¬⊤)/k = 0。
したがって本ファイル (および phase6c, 9a の前身) の全定理は、公理群が矛盾する以上
内容を持たない。修復 (def_VIII_i の → 向きか ax_iii_taut に「証拠が不整合でない」条件を
付す) は phase6c の管轄であり、司令塔の裁定を要する。 -/

/-- a ↔ a の確実性と Def.VIII (→) から a/(a ∧ h) = 1 — a が不整合でも。 -/
theorem pr_self_evidence (a h : IProp) : PrI a (iand a h) = 1 := by
  have ht : PrI (iiff a a) h = 1 :=
    ax_iii_taut (Form.iffF (Form.var 0) (Form.var 0)) (fun _ => a) h
      (by intro v; simp [evalB])
  exact ((def_VIII_i a a h).mp ht).2

/-- **公理群の不整合**: (¬⊤)/((¬⊤) ∧ ⊤) は `pr_self_evidence` で 1、補完律で 0。 -/
theorem th_6c_axioms_inconsistent : False := by
  have h1 := pr_self_evidence (inot itrue) itrue
  have h2 := th_13_1_i itrue (iand (inot itrue) itrue)
  rw [itrue_certain] at h2
  linarith

end KeynesI

/-! ## 関係式の数値例 (7i の Erratum と同じ水準)

以下は本章の関係式 (F20.6 乗法形、F20.10 第 1–2 段、F20.11 第 1 等式・分母の分解、
F20.16 第 1 等式) を実数の等式として満たす数値の例で、落とした前提の下で結論が
破れることを示す。公理群 KeynesI のモデルではない (上記のとおりモデルは存在しない)。 -/

/-! ### E-III-1 (folio 235、F20.6 第 2 段の分子で g 脱落) の数値例 -/

namespace ErratumE_III_1

/-- p_0 = 1/8, p_1 = 1/4, p_2 = 1/2 と、F20.6 乗法形 p_n y_n = p_{n−1} を満たす
y_1 = y_2 = 1/2。 -/
def p0 : ℚ := 1 / 8
def p1 : ℚ := 1 / 4
def p2 : ℚ := 1 / 2
def y1 : ℚ := 1 / 2
def y2 : ℚ := 1 / 2

/-- 関係式: F20.6 乗法形 (p_1 y_1 = p_0, p_2 y_2 = p_1) と確率の範囲。 -/
theorem relations :
    p1 * y1 = p0 ∧ p2 * y2 = p1 ∧
    (0 ≤ p0 ∧ p0 ≤ 1) ∧ (0 ≤ p1 ∧ p1 ≤ 1) ∧ (0 ≤ p2 ∧ p2 ≤ 1) ∧
    (0 ≤ y1 ∧ y1 ≤ 1) ∧ (0 ≤ y2 ∧ y2 ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [p0, p1, p2, y1, y2]

/-- **印刷の第 2 段は偽** (n = 2): 印刷の分子 x_2/hx_1 = y_2 のままでは右辺は
y_2/(p_1 · y_2) = 4 だが、第 1 段 p_2/p_1 = 2。 -/
theorem printed_line2_false :
    p2 / p1 = 2 ∧ y2 / (p1 * y2) = 4 ∧ p2 / p1 ≠ y2 / (p1 * y2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [p1, p2, y2]

/-- **訂正形は一致** (n = 2): 分子を結合確率 g x_2/hx_1 = x_2/ghx_1 · g/hx_1 = 1 · p_1 に
直すと右辺は p_1/(p_1 · y_2) = 1/y_2 = 2 = p_2/p_1。 -/
theorem corrected_line2_holds :
    p2 / p1 = (1 * p1) / (p1 * y2) ∧ (1 * p1) / (p1 * y2) = 1 / y2 := by
  refine ⟨?_, ?_⟩ <;> norm_num [p1, p2, y2]

end ErratumE_III_1

/-! ### F20.9 の前提 x_1…x_n/h ≠ 0 を落とした数値例 -/

namespace Witness_F20_9_J

/-- p_0 = 0, x_1…x_n/h = x_1…x_{n+1}/h = 0 (前提が不可能), p_n = 1/2, p_{n+1} = 1/4,
y_{n+1} = 1/2。 -/
def p0 : ℚ := 0
def Jn : ℚ := 0
def Jn1 : ℚ := 0
def pn : ℚ := 1 / 2
def pn1 : ℚ := 1 / 4
def yn1 : ℚ := 1 / 2

/-- 関係式: F20.11 第 1 等式 (p_n · x_1…x_n/h = p_0、n と n+1)、F20.10 第 1–2 段
(x_1…x_{n+1}/h = y_{n+1} · x_1…x_n/h)、範囲。 -/
theorem relations :
    pn * Jn = p0 ∧ pn1 * Jn1 = p0 ∧ Jn1 = yn1 * Jn ∧
    (0 ≤ p0 ∧ p0 ≤ 1) ∧ (0 ≤ Jn ∧ Jn ≤ 1) ∧ (0 ≤ Jn1 ∧ Jn1 ≤ 1) ∧
    (0 ≤ pn ∧ pn ≤ 1) ∧ (0 ≤ pn1 ∧ pn1 ≤ 1) ∧ (0 ≤ yn1 ∧ yn1 ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [p0, Jn, Jn1, pn, pn1, yn1]

/-- F20.9 の残りの前提 (y_{n+1} ≠ 1, p_n > 0) は成り立ち、x_1…x_n/h = 0 で、
結論 p_n < p_{n+1} は破れる。 -/
theorem hypotheses_hold_conclusion_fails :
    yn1 ≠ 1 ∧ 0 < pn ∧ Jn = 0 ∧ ¬ (pn < pn1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [Jn, pn, pn1, yn1]

end Witness_F20_9_J

/-! ### F20.11 の分母 ≠ 0 を落とした数値例 -/

namespace Witness_F20_11_den

/-- p_0 = 0, x_1…x_n/ḡh = 0, x_1…x_n/h = 0 (前提が不可能), p_n = 1/2。 -/
def p0 : ℚ := 0
def Qn : ℚ := 0
def Jn : ℚ := 0
def pn : ℚ := 1 / 2

/-- 関係式: F20.11 第 1 等式 (p_n · x_1…x_n/h = p_0) と分母の分解
(x_1…x_n/h = p_0 + x_1…x_n/ḡh (1 − p_0))、範囲。 -/
theorem relations :
    pn * Jn = p0 ∧ Jn = p0 + Qn * (1 - p0) ∧
    (0 ≤ p0 ∧ p0 ≤ 1) ∧ (0 ≤ Qn ∧ Qn ≤ 1) ∧ (0 ≤ Jn ∧ Jn ≤ 1) ∧ (0 ≤ pn ∧ pn ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [p0, Qn, Jn, pn]

/-- 分母 = 0 で、印刷の閉形式 p_n = p_0/(p_0 + x_1…x_n/ḡh (1 − p_0)) は破れる
(右辺は 0/0 = 0 の約束で 0、左辺は 1/2)。 -/
theorem denominator_zero_formula_fails :
    p0 + Qn * (1 - p0) = 0 ∧ pn ≠ p0 / (p0 + Qn * (1 - p0)) := by
  refine ⟨?_, ?_⟩ <;> norm_num [p0, Qn, pn]

end Witness_F20_11_den

/-! ### F20.20 の前提 x_1…x_s/h ≠ 0 を落とした数値例 (s = 1) -/

namespace Witness_F20_20_Js

open Filter Topology

/-- s = 1。p = (0, 1/2, 1/2, …), x_1…x_n/h = x_1…x_n/ḡh = (1, 0, 0, …),
y_1 = 0 (x_1 は h の下で不可能), y_n = 1/2 (n ≥ 2), q_n = 0 (n ≥ 1)。 -/
noncomputable def p (n : ℕ) : ℝ := if n = 0 then 0 else 1 / 2
noncomputable def J (n : ℕ) : ℝ := if n = 0 then 1 else 0
noncomputable def Q (n : ℕ) : ℝ := if n = 0 then 1 else 0
noncomputable def y (n : ℕ) : ℝ := if n = 1 then 0 else 1 / 2
noncomputable def q (_ : ℕ) : ℝ := 0

/-- 関係式: F20.10 第 1–2 段、F20.11 第 1 等式、F20.11 分母の分解、F20.16 第 1 等式、範囲。 -/
theorem relations :
    (∀ n, J (n + 1) = y (n + 1) * J n) ∧ (∀ n, p n * J n = p 0) ∧
    (∀ n, J n = p 0 + Q n * (1 - p 0)) ∧ (∀ n, Q (n + 1) = q (n + 1) * Q n) ∧
    (∀ n, 0 ≤ p n ∧ p n ≤ 1) ∧ (∀ n, 0 ≤ J n ∧ J n ≤ 1) ∧ (∀ n, 0 ≤ Q n ∧ Q n ≤ 1) ∧
    (∀ n, 0 ≤ y n ∧ y n ≤ 1) ∧ (∀ n, 0 ≤ q n ∧ q n ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro n <;>
    rcases n with _ | _ | n <;> simp [p, J, Q, y, q] <;> norm_num

/-- F20.20 の前提 (ε = η = 1/2, s = 1): 0 < ε ≤ 1, 0 < η, η ≤ p_1, r ≥ 1 で q_{r+1} ≤ 1 − ε
は成り立ち、x_1/h = 0 (落とした前提が破れる)。 -/
theorem hypotheses_hold :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 ∧ (1 / 2 : ℝ) ≤ p 1 ∧
    (∀ r, 1 ≤ r → q (r + 1) ≤ 1 - 1 / 2) ∧ J 1 = 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num [p], fun r _ => by norm_num [q], by simp [J]⟩

/-- 結論 p_n → 1 は破れる: p_n = 1/2 (n ≥ 1) なので極限は 1/2。 -/
theorem conclusion_fails : ¬ Tendsto p atTop (𝓝 1) := by
  intro ht
  have h2 : Tendsto p atTop (𝓝 (1 / 2)) := by
    refine (tendsto_const_nhds (x := (1 / 2 : ℝ))).congr' ?_
    rw [EventuallyEq, eventually_atTop]
    exact ⟨1, fun n hn => by simp [p, Nat.pos_iff_ne_zero.mp hn]⟩
  have := tendsto_nhds_unique ht h2
  norm_num at this

end Witness_F20_20_Js

/-! ## 監査クエリ -/

#print axioms KeynesI.th_13_10_i
#print axioms KeynesI.th_13_9_i
#print axioms KeynesI.pr_iand_itrue_evidence
#print axioms KeynesI.pr_evidence_assoc
#print axioms KeynesI.pr_evidence_comm
#print axioms KeynesI.p_zero
#print axioms KeynesI.J_succ
#print axioms KeynesI.Q_succ
#print axioms KeynesI.conj_certain
#print axioms KeynesI.th_20_10_src
#print axioms KeynesI.th_20_11_first
#print axioms KeynesI.th_20_7_src
#print axioms KeynesI.th_20_6
#print axioms KeynesI.th_20_6_lines134
#print axioms KeynesI.joint_eq
#print axioms KeynesI.th_20_6_cor
#print axioms KeynesI.th_20_6_src
#print axioms KeynesI.th_20_9_src
#print axioms KeynesI.th_20_9_iff
#print axioms KeynesI.th_20_9_needs_p_pos
#print axioms KeynesI.th_20_9_J_zero
#print axioms KeynesI.th_20_13_src
#print axioms KeynesI.th_S_III_1
#print axioms KeynesI.th_S_III_1_vacuous
#print axioms KeynesI.th_20_11_denom
#print axioms KeynesI.th_20_11_src
#print axioms KeynesI.th_20_11_den_zero
#print axioms KeynesI.limit_of_Q
#print axioms KeynesI.th_20_12_src
#print axioms KeynesI.th_20_12_p0_zero
#print axioms KeynesI.th_20_14
#print axioms KeynesI.th_20_16_le
#print axioms KeynesI.th_20_16_src
#print axioms KeynesI.Q_le_of_tail
#print axioms KeynesI.th_20_17_pow
#print axioms KeynesI.th_20_17_src
#print axioms KeynesI.th_20_17_bound
#print axioms KeynesI.th_20_15
#print axioms KeynesI.th_20_15_src
#print axioms KeynesI.th_20_19_src
#print axioms KeynesI.th_20_18_src
#print axioms KeynesI.th_20_20_src
#print axioms KeynesI.th_20_20_Js_zero
#print axioms KeynesI.th_E_III_2_not_lt
#print axioms KeynesI.th_22_254_eq_exact
#print axioms KeynesI.th_E_III_2_refutes_F20_16
#print axioms KeynesI.th_22_254_eq_src
#print axioms KeynesI.th_E_III_2_eq_imp_le
#print axioms KeynesI.pr_self_evidence
#print axioms KeynesI.th_6c_axioms_inconsistent
#print axioms ErratumE_III_1.relations
#print axioms ErratumE_III_1.printed_line2_false
#print axioms ErratumE_III_1.corrected_line2_holds
#print axioms Witness_F20_9_J.relations
#print axioms Witness_F20_9_J.hypotheses_hold_conclusion_fails
#print axioms Witness_F20_11_den.relations
#print axioms Witness_F20_11_den.denominator_zero_formula_fails
#print axioms Witness_F20_20_Js.relations
#print axioms Witness_F20_20_Js.hypotheses_hold
#print axioms Witness_F20_20_Js.conclusion_fails
