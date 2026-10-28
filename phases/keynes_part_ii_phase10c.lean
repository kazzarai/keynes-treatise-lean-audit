/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 10c
#
# 第 XIV 章 (蓋然的推論の基本定理、folio 144–157) の証明途中行と付録の引用式を
# 1 行 1 本の定理にする (全数台帳 docs/全数台帳/ch14.md の Lean 欄「未」121 行)。
# 1921 Macmillan 初版の頁 (folio) が唯一の基準。定理名 `th_14_rNNN` の NNN は
# 台帳の行 ID ch14-NNN。
#
# ## 担体
#   phase6c の KeynesI (IProp・PrI・Cons、公理 (i) の但し書き付き) をそのまま写す
#   (B09 修復後の公理群)。`Prop → Prop → ℝ` 型の確率は置かない。
#   phase6c の初期定理 (補完律 (1)・Th.(12)・代入原理・加法定理 (24)) も写す。
#   代入原理は def_VIII_i を用いない th_12_i_short 経由にする。
#
# ## 書き方の約束
#   * 連鎖の行 (「= …」「≥ …」で始まる行) は、連鎖の頭 (左辺) とその行の右辺の
#     関係として述べる。
#   * 「h が矛盾する連言でない」は Cons h。正値性は cons_of_pos_src から出す。
#   * 公理系に前提側の置換 (公理 (ii)) が無いので、前提の連言の順序は Def. X の
#     出す形 (q ∧ h) に従う。印刷の順序と違う行は台帳で ≈ とする。
#   * (26)(29) 系は h (印刷では前提そのもの) に共通前提 k (または h) を足した形で述べる
#     ((13.1) ā/a = 0 は前提 a ∧ k の形でしか導けないため)。ただし (13.1) を使わない
#     ch14-037 ((24) の当てはめ) は印刷どおりの前提 h で述べる。
#   * 仮定をそのまま返すだけの行 (ch14-024・026・097・204) と記号の名付けだけの行
#     (ch14-218・219) は定理にしない (台帳は 未)。where … の名付けの行 (ch14-034・124・
#     125・226) は定理の前提 (hX・hp・hq・hA) に写すが、台帳の Lean 欄からは外す (未)。
#   * 印刷に無い前提を足した定理は台帳で ✓ にしない: ch14-225 の hB (B = b/ε) は ≈、
#     ch14-175 の hconst (x/h が選択肢によらない) は外すと偽なので台帳は 未。
#   * n 個の命題 abc… はリストの右結合連言 conjL、Σ・Π はリスト上の和・積。
#   * 比例式 u : u′ : u″ … = v : v′ : v″ … と ∝ は Proportional (共通の 0 でない
#     比例定数がある) で述べる。
#   * 数値の反例 (✎ の行と、本文自身が誤りとする簡略形) は 3 命題の有限頻度モデル
#     (ℚ、namespace Ch14Models) で示す。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase10c.lean
-/

import Mathlib

namespace KeynesI

/-! ## 担体と公理 (phase6c の写し、B09 修復後) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 (公理 (i) の但し書き、folio 135)。 -/
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

axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)
axiom def_VIII_i_src (a b h : IProp) :
    PrI b (iand a h) = 1 → PrI a (iand b h) = 1 → PrI (iiff a b) h = 1

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
    Cons h → Taut f → PrI (interp env f) h = 1

axiom cons_true : Cons itrue
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## phase6c の初期定理 (写し) -/

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

/-- 補完律 (第13章の式 (1)、folio 139)。 -/
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

/-- Th.(12) (folio 141)、def_VIII_i を用いない短い証明 (phase6c の th_12_i_short)。 -/
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

/-- 代入原理 (論証的同値な結論は同じ確率)。th_12_i_short 経由。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i_short _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-- 3 変数の環境。 -/
noncomputable def env3 (a b c : IProp) : ℕ → IProp :=
  fun n => match n with | 0 => a | 1 => b | _ => c

/-- 加法定理 (24) (folio 144)、phase6c の th_24_i。 -/
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

/-! ## 補助定理 (本章の証明で繰り返し使う一歩) -/

/-- ah が整合ならば a/h > 0 (Def. VI の対偶と公理 (v.) の範囲)。 -/
theorem pos_of_cons (a h : IProp) (hc : Cons (iand a h)) : 0 < PrI a h :=
  lt_of_le_of_ne (ax_range_lo_i a h) (Ne.symm (cons_of_pos_src a h hc))

/-- ā/h = 1 − a/h ((1) の言い換え)。 -/
theorem pr_not (a h : IProp) (hc : Cons h) : PrI (inot a) h = 1 - PrI a h := by
  have := th_13_1_i a h hc; linarith

/-- 連言の交換 ab/h = ba/h (公理 (iii) の代入)。 -/
theorem pr_comm (p q h : IProp) (hc : Cons h) :
    PrI (iand p q) h = PrI (iand q p) h :=
  subst_taut (Form.conj (Form.var 0) (Form.var 1)) (Form.conj (Form.var 1) (Form.var 0))
    (env3 p q p) h hc
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])

/-- ab/h ≤ a/h (Def. IX と公理 (v.) の範囲)。 -/
theorem conj_le_left (p q h : IProp) : PrI (iand p q) h ≤ PrI p h := by
  have := def_IX_i p q h; have := ax_range_lo_i (iand p (inot q)) h; linarith

/-- ab/h ≤ b/h。 -/
theorem conj_le_right (p q h : IProp) (hc : Cons h) : PrI (iand p q) h ≤ PrI q h := by
  rw [pr_comm p q h hc]; exact conj_le_left q p h

/-- **(8)** (folio 140) の後半: a/h = 0 ならば a/bh = 0 (bh が整合なら)。 -/
theorem th_8_i (a b h : IProp) (h0 : PrI a h = 0) (hcb : Cons (iand b h)) :
    PrI a (iand b h) = 0 := by
  have hx := def_X_left_i a b h
  have hle := conj_le_left a b h
  have hlo := ax_range_lo_i (iand a b) h
  have hab : PrI (iand a b) h = 0 := by linarith
  have hb := cons_of_pos_src b h hcb
  rw [hab] at hx
  rcases mul_eq_zero.mp hx.symm with h1 | h1
  · exact h1
  · exact absurd h1 hb

/-- **(9)** (folio 140): a/h = 1 ならば a/bh = 1 (bh が整合なら)。 -/
theorem th_9_i (a b h : IProp) (h1 : PrI a h = 1) (hc : Cons h) (hcb : Cons (iand b h)) :
    PrI a (iand b h) = 1 := by
  have hn : PrI (inot a) h = 0 := by have := th_13_1_i a h hc; linarith
  have hn' := th_8_i (inot a) b h hn hcb
  have := th_13_1_i a (iand b h) hcb
  linarith

/-- Bayes の一歩: a/bh · b/h = b/ah · a/h (Def. X の両形)。 -/
theorem bayes_mul (a b h : IProp) :
    PrI a (iand b h) * PrI b h = PrI b (iand a h) * PrI a h := by
  rw [← def_X_left_i, ← def_X_right_i]


/-- 真理値表で恒真式を確かめる (3 変数)。 -/
macro "taut3" : tactic =>
  `(tactic| (intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
      simp [evalB, h0, h1, h2]))

/-- (27) の一歩: (x + y)/H = 0 ならば x/H = 0 (H 整合)。 -/
theorem zero_of_disj_zero (x y H : IProp) (hc : Cons H) (h0 : PrI (ior x y) H = 0) :
    PrI x H = 0 := by
  have e := th_24_i x y H hc
  have h1 := conj_le_right x y H hc
  have h2 := ax_range_lo_i x H
  linarith

/-- (27.1) の一歩: x/H = 0 かつ y/H = 0 ならば (x + y)/H = 0。 -/
theorem disj_zero (x y H : IProp) (hc : Cons H) (hx : PrI x H = 0) (hy : PrI y H = 0) :
    PrI (ior x y) H = 0 := by
  have e := th_24_i x y H hc
  have h1 := conj_le_left x y H
  have h2 := ax_range_lo_i (iand x y) H
  linarith

/-- Th.(13) の前提 a ∧ h 版 (phase6c の th_13_13_conj_i、def_VIII_i を用いる)。 -/
theorem th_13_13_conj_i (a h : IProp) (hc : Cons h) (hca : Cons (iand a h)) :
    PrI a (iand a h) = 1 := by
  have hcert : PrI (iiff a a) h = 1 :=
    ax_iii_taut (Form.iffF (Form.var 0) (Form.var 0)) (fun _ => a) h hc
      (by intro v; simp [evalB])
  exact ((def_VIII_i a a h hca hca).mp hcert).1

/-! ## §2 (24) の証明 (folio 144) -/

/-- ch14-002 (folio 144): (a + b)āb/h + (a + b)(āb の上にバー)/h = (a + b)/h
(IX で a に (a + b)、b に āb を書く)。 -/
theorem th_14_r002 (a b h : IProp) :
    PrI (iand (ior a b) (iand (inot a) b)) h
      + PrI (iand (ior a b) (inot (iand (inot a) b))) h = PrI (ior a b) h := by
  have := def_IX_i (ior a b) (iand (inot a) b) h
  linarith

/-- ch14-003 (folio 144): āb/h + (a + b)(a + b̄)/h = (a + b)/h  by (iii.)。 -/
theorem th_14_r003 (a b h : IProp) (hc : Cons h) :
    PrI (iand (inot a) b) h + PrI (iand (ior a b) (ior a (inot b))) h
      = PrI (ior a b) h := by
  have e0 := th_14_r002 a b h
  have e1 : PrI (iand (ior a b) (iand (inot a) b)) h = PrI (iand (inot a) b) h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1))
        (Form.conj (Form.neg (Form.var 0)) (Form.var 1)))
      (Form.conj (Form.neg (Form.var 0)) (Form.var 1)) (env3 a b a) h hc (by taut3)
  have e2 : PrI (iand (ior a b) (inot (iand (inot a) b))) h
      = PrI (iand (ior a b) (ior a (inot b))) h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1))
        (Form.neg (Form.conj (Form.neg (Form.var 0)) (Form.var 1))))
      (Form.conj (Form.disj (Form.var 0) (Form.var 1))
        (Form.disj (Form.var 0) (Form.neg (Form.var 1)))) (env3 a b a) h hc (by taut3)
  linarith

/-- ch14-004 (folio 144): ā/bh . b/h + a/h = (a + b)/h  by (iii.) and IX.
(āb/h を Def. X で ā/bh . b/h に開く。) -/
theorem th_14_r004 (a b h : IProp) (hc : Cons h) :
    PrI (inot a) (iand b h) * PrI b h + PrI a h = PrI (ior a b) h := by
  have e0 := th_14_r003 a b h hc
  have e1 : PrI (iand (ior a b) (ior a (inot b))) h = PrI a h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1))
        (Form.disj (Form.var 0) (Form.neg (Form.var 1))))
      (Form.var 0) (env3 a b a) h hc (by taut3)
  have e2 := def_X_left_i (inot a) b h
  linarith

/-- ch14-005 (folio 144): (a + b)/h = a/h + (1 − a/bh) . b/h。 -/
theorem th_14_r005 (a b h : IProp) (hc : Cons h) :
    PrI (ior a b) h = PrI a h + (1 - PrI a (iand b h)) * PrI b h := by
  have e0 := th_14_r004 a b h hc
  by_cases hb : PrI b h = 0
  · rw [hb] at e0 ⊢; linarith
  · have hcb := cons_of_pos b h hb hc
    rw [pr_not a (iand b h) hcb] at e0
    linarith

/-- ch14-006 (folio 144): 連鎖の 2 行目 = a/h + b/h − ab/h
(連鎖の頭 (a + b)/h との等式)。 -/
theorem th_14_r006 (a b h : IProp) (hc : Cons h) :
    PrI (ior a b) h = PrI a h + PrI b h - PrI (iand a b) h := by
  have e0 := th_14_r005 a b h hc
  have e1 := def_X_left_i a b h
  rw [e0, e1]; ring

/-! ## §2 (24.2)(24.4) (folio 144–145) -/

/-- ch14-012 (folio 144): ab + āb ≡ b  by (iii.) (公理 (iii) の形 (… ≡ …)/h = 1)。 -/
theorem th_14_r012 (a b h : IProp) (hc : Cons h) :
    PrI (iiff (ior (iand a b) (iand (inot a) b)) b) h = 1 :=
  ax_iii_taut
    (Form.iffF (Form.disj (Form.conj (Form.var 0) (Form.var 1))
      (Form.conj (Form.neg (Form.var 0)) (Form.var 1))) (Form.var 1))
    (env3 a b a) h hc (by taut3)

/-- ch14-013 (folio 144): aāb/h = 0  by (19) and (8)。 -/
theorem th_14_r013 (a b h : IProp) (hc : Cons h) :
    PrI (iand a (iand (inot a) b)) h = 0 :=
  taut_neg_zero (Form.conj (Form.var 0) (Form.conj (Form.neg (Form.var 0)) (Form.var 1)))
    (env3 a b a) h hc (by taut3)

/-- ch14-015 (folio 145): (24.4) 第 1 行 (a + b + c)/h = (a + b)/h + c/h − (ac + bc)/h。 -/
theorem th_14_r015 (a b c h : IProp) (hc : Cons h) :
    PrI (ior (ior a b) c) h
      = PrI (ior a b) h + PrI c h - PrI (ior (iand a c) (iand b c)) h := by
  have e0 := th_24_i (ior a b) c h hc
  have e1 : PrI (iand (ior a b) c) h = PrI (ior (iand a c) (iand b c)) h :=
    subst_taut (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.var 2))
      (Form.disj (Form.conj (Form.var 0) (Form.var 2)) (Form.conj (Form.var 1) (Form.var 2)))
      (env3 a b c) h hc (by taut3)
  rw [e0, e1]

/-! ## 選言・連言のリスト ((24.6)(24.7)(25) の p₁ + p₂ + … + pₙ と abc …) -/

/-- n 個の命題の連言 abc … (右結合)。空リストは ⊤。 -/
noncomputable def conjL : List IProp → IProp
  | [] => itrue
  | [a] => a
  | a :: b :: l => iand a (conjL (b :: l))

/-- n 個の命題の選言 p₁ + p₂ + … + pₙ (右結合)。空リストは ⊤ の否定。 -/
noncomputable def disjL : List IProp → IProp
  | [] => inot itrue
  | [a] => a
  | a :: b :: l => ior a (disjL (b :: l))

/-- (24.7) の「exclusive and exhaustive alternatives」(folio 145):
p_sp_t/h = 0 (全ての対) かつ (p₁ + p₂ + … + pₙ)/h = 1。 -/
def ExclExh (ps : List IProp) (h : IProp) : Prop :=
  ps.Pairwise (fun p q => PrI (iand p q) h = 0) ∧ PrI (disjL ps) h = 1

theorem falsum_zero (h : IProp) (hc : Cons h) : PrI (inot itrue) h = 0 := by
  have := pr_not itrue h hc; rw [itrue_certain h hc] at this; linarith

/-- p ∧ (q₁ + … + qₙ) の確率は、各 pqᵣ/h = 0 なら 0。 -/
theorem conj_disjL_zero (p h : IProp) (hc : Cons h) :
    ∀ l : List IProp, (∀ q ∈ l, PrI (iand p q) h = 0) → PrI (iand p (disjL l)) h = 0
  | [], _ => by
      have h1 := conj_le_right p (inot itrue) h hc
      have h2 := ax_range_lo_i (iand p (inot itrue)) h
      have h3 := falsum_zero h hc
      simp only [disjL]; linarith
  | [q], hq => by simpa [disjL] using hq q (by simp)
  | q :: r :: l, hq => by
      have ih := conj_disjL_zero p h hc (r :: l)
        (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))
      have hpq := hq q (by simp)
      have e1 : PrI (iand p (ior q (disjL (r :: l)))) h
          = PrI (ior (iand p q) (iand p (disjL (r :: l)))) h :=
        subst_taut (Form.conj (Form.var 0) (Form.disj (Form.var 1) (Form.var 2)))
          (Form.disj (Form.conj (Form.var 0) (Form.var 1)) (Form.conj (Form.var 0) (Form.var 2)))
          (env3 p q (disjL (r :: l))) h hc (by taut3)
      have e2 := disj_zero _ _ h hc hpq ih
      simp only [disjL]
      rw [e1, e2]

/-- (24.6) のリスト形: p_sp_t/h = 0 (全ての対) ならば (p₁ + … + pₙ)/h = Σ pᵣ/h。 -/
theorem disjL_sum (h : IProp) (hc : Cons h) :
    ∀ l : List IProp, l.Pairwise (fun p q => PrI (iand p q) h = 0) →
      PrI (disjL l) h = (l.map (fun p => PrI p h)).sum
  | [], _ => by simp [disjL, falsum_zero h hc]
  | [p], _ => by simp [disjL]
  | p :: q :: l, hpw => by
      obtain ⟨hp, hrest⟩ := List.pairwise_cons.mp hpw
      have ih := disjL_sum h hc (q :: l) hrest
      have hz := conj_disjL_zero p h hc (q :: l) hp
      have e := th_24_i p (disjL (q :: l)) h hc
      simp only [disjL, List.map_cons, List.sum_cons] at e ih ⊢
      rw [e, ih, hz]; ring

theorem list_sum_mul_right (f : IProp → ℝ) (c : ℝ) :
    ∀ l : List IProp, (l.map (fun x => f x * c)).sum = (l.map f).sum * c
  | [] => by simp
  | x :: l => by simp [list_sum_mul_right f c l, add_mul]

theorem list_sum_zero (f : IProp → ℝ) :
    ∀ l : List IProp, (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => by simp
  | x :: l, hl => by
      simp [hl x (by simp), list_sum_zero f l (fun y hy => hl y (List.mem_cons_of_mem _ hy))]

/-- 排反・網羅の性質は整合な ah に移る ((8)(9))。 -/
theorem exclExh_premiss (ps : List IProp) (a h : IProp) (hc : Cons h)
    (hca : Cons (iand a h)) (hE : ExclExh ps h) : ExclExh ps (iand a h) :=
  ⟨hE.1.imp (fun hpq => th_8_i _ a h hpq hca), th_9_i _ a h hE.2 hc hca⟩

/-- (24.7) のリスト形: Σ pᵣ/h = 1。 -/
theorem exclExh_sum (ps : List IProp) (h : IProp) (hc : Cons h) (hE : ExclExh ps h) :
    (ps.map (fun p => PrI p h)).sum = 1 := by
  rw [← disjL_sum h hc ps hE.1, hE.2]

/-- **(25)** のリスト形 (folio 145): a/h = Σ pᵣa/h。ah が矛盾する場合も含む。 -/
theorem th_25_i (ps : List IProp) (a h : IProp) (hc : Cons h) (hE : ExclExh ps h) :
    PrI a h = (ps.map (fun p => PrI (iand p a) h)).sum := by
  by_cases ha : PrI a h = 0
  · rw [ha, list_sum_zero _ ps]
    intro p _
    have h1 := conj_le_right p a h hc
    have h2 := ax_range_lo_i (iand p a) h
    linarith
  · have hca := cons_of_pos a h ha hc
    have hs := exclExh_sum ps (iand a h) hca (exclExh_premiss ps a h hc hca hE)
    have e : (ps.map (fun p => PrI (iand p a) h))
        = ps.map (fun p => PrI p (iand a h) * PrI a h) := by
      apply List.map_congr_left; intro p _; exact def_X_left_i p a h
    rw [e, list_sum_mul_right, hs, one_mul]

/-! ## §2 (25) の証明 (folio 145) -/

/- ch14-024 ((p₁ + … + pₙ)/h = 1 by hypothesis) と ch14-026 (p_sp_t/h = 0 by hypothesis) は
仮定 ExclExh の再掲なので定理にしない (台帳は 未)。 -/

/-- ch14-025 (folio 145): ∴ (p₁ + p₂ + … + pₙ)/ah = 1 by (9) if ah is not inconsistent。 -/
theorem th_14_r025 (ps : List IProp) (a h : IProp) (hc : Cons h)
    (hca : Cons (iand a h)) (hE : ExclExh ps h) : PrI (disjL ps) (iand a h) = 1 :=
  th_9_i _ a h hE.2 hc hca

/-- ch14-027 (folio 145): ∴ p_sp_t/ah = 0 by (9), if ah is not inconsistent
(Lean は (8) の後半で導く)。 -/
theorem th_14_r027 (ps : List IProp) (a h : IProp) (hca : Cons (iand a h))
    (hE : ExclExh ps h) : ps.Pairwise (fun p q => PrI (iand p q) (iand a h) = 0) :=
  hE.1.imp (fun hpq => th_8_i _ a h hpq hca)

/-- ch14-028 (folio 145): Σ₁ⁿ pᵣ/ah = (p₁ + p₂ + … + pₙ)/ah  by (24.6)。 -/
theorem th_14_r028 (ps : List IProp) (a h : IProp) (hca : Cons (iand a h))
    (hE : ExclExh ps h) :
    (ps.map (fun p => PrI p (iand a h))).sum = PrI (disjL ps) (iand a h) :=
  (disjL_sum (iand a h) hca ps (th_14_r027 ps a h hca hE)).symm

/-- ch14-029 (folio 145): 連鎖の 2 行目 = 1 (Σ₁ⁿ pᵣ/ah = 1)。 -/
theorem th_14_r029 (ps : List IProp) (a h : IProp) (hc : Cons h)
    (hca : Cons (iand a h)) (hE : ExclExh ps h) :
    (ps.map (fun p => PrI p (iand a h))).sum = 1 := by
  rw [th_14_r028 ps a h hca hE, th_14_r025 ps a h hc hca hE]

/-- ch14-030 (folio 145): pᵣa/h = pᵣ/ah . a/h。 -/
theorem th_14_r030 (p a h : IProp) : PrI (iand p a) h = PrI p (iand a h) * PrI a h :=
  def_X_left_i p a h

/-- ch14-031 (folio 145): Σ₁ⁿ pᵣa/h = a/h . Σ₁ⁿ pᵣ/ah。 -/
theorem th_14_r031 (ps : List IProp) (a h : IProp) :
    (ps.map (fun p => PrI (iand p a) h)).sum
      = PrI a h * (ps.map (fun p => PrI p (iand a h))).sum := by
  have e : (ps.map (fun p => PrI (iand p a) h))
      = ps.map (fun p => PrI p (iand a h) * PrI a h) := by
    apply List.map_congr_left; intro p _; exact th_14_r030 p a h
  rw [e, list_sum_mul_right, mul_comm]

/-- ch14-032 (folio 145): ∴ a/h = Σ₁ⁿ pᵣa/h, if ah is not inconsistent。 -/
theorem th_14_r032 (ps : List IProp) (a h : IProp) (hc : Cons h)
    (hca : Cons (iand a h)) (hE : ExclExh ps h) :
    PrI a h = (ps.map (fun p => PrI (iand p a) h)).sum := by
  rw [th_14_r031, th_14_r029 ps a h hc hca hE, mul_one]

/-- ch14-033 (folio 145): If ah is inconsistent, i.e. if a/h = 0
(for h is by hypothesis consistent)。 -/
theorem th_14_r033 (a h : IProp) (hc : Cons h) (hna : ¬ Cons (iand a h)) :
    PrI a h = 0 := by
  by_contra ha; exact hna (cons_of_pos a h ha hc)

/-- (25.1) (folio 145): If pᵣa/h = Xᵣ, pᵣ/ah = Xᵣ / Σ₁ⁿ Xᵣ
(Xᵣ を pᵣ の関数 X pᵣ で)。名付けの行 ch14-034 (pᵣa/h = Xᵣ) は前提 hX に写すだけなので
台帳では 未 (定義のみ)。 -/
theorem th_14_r034 (ps : List IProp) (a h : IProp) (X : IProp → ℝ) (hc : Cons h)
    (hca : Cons (iand a h)) (hE : ExclExh ps h)
    (hX : ∀ p ∈ ps, PrI (iand p a) h = X p) (p : IProp) (hp : p ∈ ps) :
    PrI p (iand a h) = X p / (ps.map X).sum := by
  have hs : (ps.map X).sum = PrI a h := by
    rw [th_25_i ps a h hc hE]
    apply congrArg; apply List.map_congr_left; intro q hq; exact (hX q hq).symm
  have ha := cons_of_pos_src a h hca
  rw [hs, ← hX p hp, th_14_r030 p a h]
  field_simp

/-! ## §2 (26)–(28) の証明 (folio 146) -/

/-- ch14-037 (folio 146): (a + h̄)/h = a/h + h̄/h − ah̄/h by (24) (印刷どおりの前提 h)。 -/
theorem th_14_r037 (a h : IProp) (hc : Cons h) :
    PrI (ior a (inot h)) h = PrI a h + PrI (inot h) h - PrI (iand a (inot h)) h :=
  th_24_i a (inot h) h hc

/-- ch14-038 (folio 146): 連鎖の 2 行目 = a/h  by (13.1) and (8)
((a + h̄)/h = a/h、前提 h に共通前提 k を足した h ∧ k の形)。 -/
theorem th_14_r038 (a h k : IProp) (hk : Cons k) (hck : Cons (iand h k)) :
    PrI (ior a (inot h)) (iand h k) = PrI a (iand h k) := by
  have e := th_24_i a (inot h) (iand h k) hck
  have h1 := th_13_13_conj_i h k hk hck
  have hn : PrI (inot h) (iand h k) = 0 := by
    have := pr_not h (iand h k) hck; linarith
  have h2 := conj_le_right a (inot h) (iand h k) hck
  have h3 := ax_range_lo_i (iand a (inot h)) (iand h k)
  linarith

/-- ch14-042 (folio 146): a/h + [b/h − ab/h] = 0, by (24) and hypothesis。 -/
theorem th_14_r042 (a b h : IProp) (hc : Cons h) (h0 : PrI (ior a b) h = 0) :
    PrI a h + (PrI b h - PrI (iand a b) h) = 0 := by
  have := th_24_i a b h hc; linarith

/-- ch14-043 (folio 146): ∴ a/h = 0  by (v.)。 -/
theorem th_14_r043 (a b h : IProp) (hc : Cons h) (h0 : PrI (ior a b) h = 0) :
    PrI a h = 0 := by
  have e := th_14_r042 a b h hc h0
  have h1 := conj_le_right a b h hc
  have h2 := ax_range_lo_i a h
  linarith

/-- ch14-049 (folio 146): (a + b̄)/h = a/h + b̄ā/h  by (24.3)。 -/
theorem th_14_r049 (a b h : IProp) (hc : Cons h) :
    PrI (ior a (inot b)) h = PrI a h + PrI (iand (inot b) (inot a)) h := by
  have e1 := th_24_i a (inot b) h hc
  have e2 := def_IX_i (inot b) a h
  have e3 := pr_comm (inot b) a h hc
  linarith

/-- ch14-050 (folio 146): (a + b̄)/h = a/h = 1  by (1.1) and (8)、仮定 a/h = 1 のもとで。 -/
theorem th_14_r050 (a b h : IProp) (hc : Cons h) (h1 : PrI a h = 1) :
    PrI (ior a (inot b)) h = PrI a h ∧ PrI a h = 1 := by
  refine ⟨?_, h1⟩
  have e := th_14_r049 a b h hc
  have hn : PrI (inot a) h = 0 := by have := pr_not a h hc; linarith
  have h2 := conj_le_right (inot b) (inot a) h hc
  have h3 := ax_range_lo_i (iand (inot b) (inot a)) h
  linarith

/-! ## §2 (29)–(29.3) (folio 146) — 前提 h₁, h₂, h₁ + h₂ に共通前提 h を足した形 -/

/-- ch14-055 (folio 146): ā/(h₁ + h₂) = 0 (a/(h₁ + h₂) = 1 から)。 -/
theorem th_14_r055 (a h₁ h₂ h : IProp) (hc12 : Cons (iand (ior h₁ h₂) h))
    (h1 : PrI a (iand (ior h₁ h₂) h) = 1) : PrI (inot a) (iand (ior h₁ h₂) h) = 0 := by
  have := pr_not a _ hc12; linarith

/-- (ā(h₁ + h₂))/h = 0 (a/(h₁ + h₂) = 1 から、Def. X)。 -/
theorem conj_disj_zero_base (a h₁ h₂ h : IProp) (hc12 : Cons (iand (ior h₁ h₂) h))
    (h1 : PrI a (iand (ior h₁ h₂) h) = 1) : PrI (iand (inot a) (ior h₁ h₂)) h = 0 := by
  rw [def_X_left_i, th_14_r055 a h₁ h₂ h hc12 h1, zero_mul]

/-- ch14-056 (folio 146): ∴ ā(h₁ + h₂)/h₁ = 0  by (15)。 -/
theorem th_14_r056 (a h₁ h₂ h : IProp) (hc12 : Cons (iand (ior h₁ h₂) h))
    (hc1 : Cons (iand h₁ h)) (h1 : PrI a (iand (ior h₁ h₂) h) = 1) :
    PrI (iand (inot a) (ior h₁ h₂)) (iand h₁ h) = 0 :=
  th_8_i _ h₁ h (conj_disj_zero_base a h₁ h₂ h hc12 h1) hc1

/-- ch14-057 (folio 146): Hence āh₁/h₁ = 0  by (27)。 -/
theorem th_14_r057 (a h₁ h₂ h : IProp) (hc12 : Cons (iand (ior h₁ h₂) h))
    (hc1 : Cons (iand h₁ h)) (h1 : PrI a (iand (ior h₁ h₂) h) = 1) :
    PrI (iand (inot a) h₁) (iand h₁ h) = 0 := by
  have e0 := th_14_r056 a h₁ h₂ h hc12 hc1 h1
  have e1 : PrI (iand (inot a) (ior h₁ h₂)) (iand h₁ h)
      = PrI (ior (iand (inot a) h₁) (iand (inot a) h₂)) (iand h₁ h) :=
    subst_taut (Form.conj (Form.neg (Form.var 0)) (Form.disj (Form.var 1) (Form.var 2)))
      (Form.disj (Form.conj (Form.neg (Form.var 0)) (Form.var 1))
        (Form.conj (Form.neg (Form.var 0)) (Form.var 2)))
      (env3 a h₁ h₂) _ hc1 (by taut3)
  rw [e1] at e0
  exact zero_of_disj_zero _ _ _ hc1 e0

/-- (ā(h₁ + h₂))/h = (āh₁ + āh₂)/h。 -/
theorem conj_disj_distrib (a h₁ h₂ H : IProp) (hc : Cons H) :
    PrI (iand (inot a) (ior h₁ h₂)) H
      = PrI (ior (iand (inot a) h₁) (iand (inot a) h₂)) H :=
  subst_taut (Form.conj (Form.neg (Form.var 0)) (Form.disj (Form.var 1) (Form.var 2)))
    (Form.disj (Form.conj (Form.neg (Form.var 0)) (Form.var 1))
      (Form.conj (Form.neg (Form.var 0)) (Form.var 2)))
    (env3 a h₁ h₂) H hc (by taut3)

/-- **(29)** (folio 146、共通前提 h を足した形): a/(h₁ + h₂) = 1 ならば a/h₁ = 1。 -/
theorem th_29_i (a h₁ h₂ h : IProp) (hc : Cons h) (hc12 : Cons (iand (ior h₁ h₂) h))
    (hc1 : Cons (iand h₁ h)) (h1 : PrI a (iand (ior h₁ h₂) h) = 1) :
    PrI a (iand h₁ h) = 1 := by
  have e0 := conj_disj_zero_base a h₁ h₂ h hc12 h1
  rw [conj_disj_distrib a h₁ h₂ h hc] at e0
  have e1 := zero_of_disj_zero _ _ _ hc e0
  rw [def_X_left_i] at e1
  have hne := cons_of_pos_src h₁ h hc1
  have e2 : PrI (inot a) (iand h₁ h) = 0 := by
    rcases mul_eq_zero.mp e1 with e | e
    · exact e
    · exact absurd e hne
  have := pr_not a _ hc1; linarith

/-- a/h₁ = 1 ならば āh₁/h = 0 (h₁/h = 0 の場合も含む)。 -/
theorem not_conj_zero_of_cert (a h₁ h : IProp) (hc : Cons h)
    (h1 : PrI a (iand h₁ h) = 1) : PrI (iand (inot a) h₁) h = 0 := by
  by_cases hz : PrI h₁ h = 0
  · have := conj_le_right (inot a) h₁ h hc
    have := ax_range_lo_i (iand (inot a) h₁) h
    linarith
  · have hc1 := cons_of_pos h₁ h hz hc
    rw [def_X_left_i]
    have : PrI (inot a) (iand h₁ h) = 0 := by have := pr_not a _ hc1; linarith
    rw [this, zero_mul]

/-- ch14-061 (folio 146): As in (20) āh₁/(h₁ + h₂) = 0 and āh₂/(h₁ + h₂) = 0。 -/
theorem th_14_r061 (a h₁ h₂ h : IProp) (hc : Cons h) (hc12 : Cons (iand (ior h₁ h₂) h))
    (h1 : PrI a (iand h₁ h) = 1) (h2 : PrI a (iand h₂ h) = 1) :
    PrI (iand (inot a) h₁) (iand (ior h₁ h₂) h) = 0 ∧
      PrI (iand (inot a) h₂) (iand (ior h₁ h₂) h) = 0 := by
  have hne := cons_of_pos_src (ior h₁ h₂) h hc12
  constructor
  · have e0 := def_X_left_i (iand (inot a) h₁) (ior h₁ h₂) h
    have e1 : PrI (iand (iand (inot a) h₁) (ior h₁ h₂)) h = PrI (iand (inot a) h₁) h :=
      subst_taut (Form.conj (Form.conj (Form.neg (Form.var 0)) (Form.var 1))
          (Form.disj (Form.var 1) (Form.var 2)))
        (Form.conj (Form.neg (Form.var 0)) (Form.var 1)) (env3 a h₁ h₂) h hc (by taut3)
    rw [e1, not_conj_zero_of_cert a h₁ h hc h1] at e0
    rcases mul_eq_zero.mp e0.symm with e | e
    · exact e
    · exact absurd e hne
  · have e0 := def_X_left_i (iand (inot a) h₂) (ior h₁ h₂) h
    have e1 : PrI (iand (iand (inot a) h₂) (ior h₁ h₂)) h = PrI (iand (inot a) h₂) h :=
      subst_taut (Form.conj (Form.conj (Form.neg (Form.var 0)) (Form.var 2))
          (Form.disj (Form.var 1) (Form.var 2)))
        (Form.conj (Form.neg (Form.var 0)) (Form.var 2)) (env3 a h₁ h₂) h hc (by taut3)
    rw [e1, not_conj_zero_of_cert a h₂ h hc h2] at e0
    rcases mul_eq_zero.mp e0.symm with e | e
    · exact e
    · exact absurd e hne

/-- ch14-062 (folio 146): Hence ā(h₁ + h₂)/(h₁ + h₂) = 0  by (27.1)。 -/
theorem th_14_r062 (a h₁ h₂ h : IProp) (hc : Cons h) (hc12 : Cons (iand (ior h₁ h₂) h))
    (h1 : PrI a (iand h₁ h) = 1) (h2 : PrI a (iand h₂ h) = 1) :
    PrI (iand (inot a) (ior h₁ h₂)) (iand (ior h₁ h₂) h) = 0 := by
  obtain ⟨e1, e2⟩ := th_14_r061 a h₁ h₂ h hc hc12 h1 h2
  rw [conj_disj_distrib a h₁ h₂ _ hc12]
  exact disj_zero _ _ _ hc12 e1 e2

/-- ch14-058, ch14-059, ch14-060 (folio 146): **(29.1)** If a/h₁ = 1 and a/h₂ = 1,
a/(h₁ + h₂) = 1 (共通前提 h を足した形)。 -/
theorem th_14_r060 (a h₁ h₂ h : IProp) (hc : Cons h) (hc12 : Cons (iand (ior h₁ h₂) h))
    (h1 : PrI a (iand h₁ h) = 1) (h2 : PrI a (iand h₂ h) = 1) :
    PrI a (iand (ior h₁ h₂) h) = 1 := by
  have e0 : PrI (iand (inot a) (ior h₁ h₂)) h = 0 := by
    rw [conj_disj_distrib a h₁ h₂ h hc]
    exact disj_zero _ _ _ hc (not_conj_zero_of_cert a h₁ h hc h1)
      (not_conj_zero_of_cert a h₂ h hc h2)
  rw [def_X_left_i] at e0
  have hne := cons_of_pos_src (ior h₁ h₂) h hc12
  have e2 : PrI (inot a) (iand (ior h₁ h₂) h) = 0 := by
    rcases mul_eq_zero.mp e0 with e | e
    · exact e
    · exact absurd e hne
  have := pr_not a _ hc12; linarith

/-- ch14-063, ch14-064 (folio 146): **(29.2)** If a/(h₁ + h₂) = 0, a/h₁ = 0
(This follows from (29)、共通前提 h を足した形)。 -/
theorem th_14_r064 (a h₁ h₂ h : IProp) (hc : Cons h) (hc12 : Cons (iand (ior h₁ h₂) h))
    (hc1 : Cons (iand h₁ h)) (h0 : PrI a (iand (ior h₁ h₂) h) = 0) :
    PrI a (iand h₁ h) = 0 := by
  have hn : PrI (inot a) (iand (ior h₁ h₂) h) = 1 := by
    have := pr_not a _ hc12; linarith
  have := th_29_i (inot a) h₁ h₂ h hc hc12 hc1 hn
  have := pr_not a _ hc1; linarith

/-- ch14-065, ch14-066, ch14-067 (folio 146): **(29.3)** If a/h₁ = 0 and a/h₂ = 0,
a/(h₁ + h₂) = 0 (This follows from (29.1)、共通前提 h を足した形)。 -/
theorem th_14_r067 (a h₁ h₂ h : IProp) (hc : Cons h) (hc12 : Cons (iand (ior h₁ h₂) h))
    (hc1 : Cons (iand h₁ h)) (hc2 : Cons (iand h₂ h))
    (h1 : PrI a (iand h₁ h) = 0) (h2 : PrI a (iand h₂ h) = 0) :
    PrI a (iand (ior h₁ h₂) h) = 0 := by
  have n1 : PrI (inot a) (iand h₁ h) = 1 := by have := pr_not a _ hc1; linarith
  have n2 : PrI (inot a) (iand h₂ h) = 1 := by have := pr_not a _ hc2; linarith
  have := th_14_r060 (inot a) h₁ h₂ h hc hc12 n1 n2
  have := pr_not a _ hc12; linarith

end KeynesI

namespace KeynesI

/-! ## §3 (30)(31) の証明 (folio 146–147) -/

/-- ch14-070 (folio 146): a/h₁ = ah₂/h₁ + ah̄₂/h₁  by (24.2)。 -/
theorem th_14_r070 (a h₁ h₂ : IProp) :
    PrI a h₁ = PrI (iand a h₂) h₁ + PrI (iand a (inot h₂)) h₁ := by
  have := def_IX_i a h₂ h₁; linarith

/-- ch14-071 (folio 146): = a/h₁h₂ . h₂/h₁ + a/h₁h̄₂ . h̄₂/h₁
(連鎖の頭 a/h₁ との等式; 前提 h₁h₂ は Def. X の出す形 h₂ ∧ h₁)。 -/
theorem th_14_r071 (a h₁ h₂ : IProp) :
    PrI a h₁ = PrI a (iand h₂ h₁) * PrI h₂ h₁
      + PrI a (iand (inot h₂) h₁) * PrI (inot h₂) h₁ := by
  rw [th_14_r070 a h₁ h₂, def_X_left_i a h₂ h₁, def_X_left_i a (inot h₂) h₁]

/-- ch14-072 (folio 146): = a/h₁ . h₂/h₁ + a/h₁h̄₂ . h̄₂/h₁ (仮定 a/h₁h₂ = a/h₁)。 -/
theorem th_14_r072 (a h₁ h₂ : IProp) (hirr : PrI a (iand h₂ h₁) = PrI a h₁) :
    PrI a h₁ = PrI a h₁ * PrI h₂ h₁ + PrI a (iand (inot h₂) h₁) * PrI (inot h₂) h₁ := by
  have := th_14_r071 a h₁ h₂; rw [hirr] at this; exact this

/-- ch14-073 (folio 146): ∴ a/h₁ . h̄₂/h₁ = a/h₁h̄₂ . h̄₂/h₁。 -/
theorem th_14_r073 (a h₁ h₂ : IProp) (hc : Cons h₁)
    (hirr : PrI a (iand h₂ h₁) = PrI a h₁) :
    PrI a h₁ * PrI (inot h₂) h₁ = PrI a (iand (inot h₂) h₁) * PrI (inot h₂) h₁ := by
  have e := th_14_r072 a h₁ h₂ hirr
  rw [pr_not h₂ h₁ hc] at e ⊢
  linarith

/-- ch14-074 (folio 146): whence a/h₁ = a/h₁h̄₂, unless h̄₂/h₁ = 0。 -/
theorem th_14_r074 (a h₁ h₂ : IProp) (hc : Cons h₁)
    (hirr : PrI a (iand h₂ h₁) = PrI a h₁) (hne : PrI (inot h₂) h₁ ≠ 0) :
    PrI a h₁ = PrI a (iand (inot h₂) h₁) :=
  mul_right_cancel₀ hne (th_14_r073 a h₁ h₂ hc hirr)

/-- ch14-075 (folio 146): unless h̄₂/h₁ = 0, i.e. if h₁h̄₂ is not inconsistent
(h̄₂/h₁ = 0 ならば h₁h̄₂ は矛盾する)。 -/
theorem th_14_r075 (h₁ h₂ : IProp) (h0 : PrI (inot h₂) h₁ = 0) :
    ¬ Cons (iand (inot h₂) h₁) :=
  fun hc => cons_of_pos_src _ _ hc h0

/-- ch14-078 (folio 147): a₂/a₁h . a₁/h = a₁/a₂h . a₂/h  by X。 -/
theorem th_14_r078 (a₁ a₂ h : IProp) :
    PrI a₂ (iand a₁ h) * PrI a₁ h = PrI a₁ (iand a₂ h) * PrI a₂ h :=
  bayes_mul a₂ a₁ h

/-! ## §4 (32)–(35) (folio 147–148) -/

/-- ch14-082 (folio 147): ah is consistent since, otherwise, a/hh₁ = a/h = 0
(前提 hh₁ は h₁ ∧ h)。 -/
theorem th_14_r082 (a h₁ h : IProp) (hc : Cons h) (hc1 : Cons (iand h₁ h))
    (hna : ¬ Cons (iand a h)) : PrI a (iand h₁ h) = PrI a h ∧ PrI a h = 0 := by
  have ha : PrI a h = 0 := by
    by_contra hne; exact hna (cons_of_pos a h hne hc)
  exact ⟨by rw [th_8_i a h₁ h ha hc1, ha], ha⟩

/-- ch14-083 (folio 147): a/h . h₁/ah = a/hh₁ . h₁/h  by X。 -/
theorem th_14_r083 (a h₁ h : IProp) :
    PrI a h * PrI h₁ (iand a h) = PrI a (iand h₁ h) * PrI h₁ h := by
  rw [bayes_mul a h₁ h]; ring

/-- ch14-084 (folio 147): > a/h . h₁/h  by hypothesis
(連鎖の頭 a/h . h₁/ah との不等式)。 -/
theorem th_14_r084 (a h₁ h : IProp) (hc1 : Cons (iand h₁ h))
    (hfav : PrI a (iand h₁ h) > PrI a h) :
    PrI a h * PrI h₁ (iand a h) > PrI a h * PrI h₁ h := by
  rw [th_14_r083]
  exact mul_lt_mul_of_pos_right hfav (pos_of_cons h₁ h hc1)

/-- ch14-085 (folio 147): so that h₁/ah > h₁/h。 -/
theorem th_14_r085 (a h₁ h : IProp) (hc1 : Cons (iand h₁ h))
    (hfav : PrI a (iand h₁ h) > PrI a h) : PrI h₁ (iand a h) > PrI h₁ h := by
  have hpos : 0 < PrI a h := by
    rcases lt_or_eq_of_le (ax_range_lo_i a h) with hp | hz
    · exact hp
    · have := th_8_i a h₁ h hz.symm hc1; linarith
  exact lt_of_mul_lt_mul_left (th_14_r084 a h₁ h hc1 hfav) hpos.le

/-- 影響係数 {aʰb} (Def. XV、folio 150): ab/h ÷ (a/h . b/h)。 -/
noncomputable def coef2 (a b h : IProp) : ℝ := PrI (iand a b) h / (PrI a h * PrI b h)

/-- a/bh ÷ a/h = {aʰb} (b/h ≠ 0)。 -/
theorem ratio_eq_coef2 (a b h : IProp) (hb : PrI b h ≠ 0) :
    PrI a (iand b h) / PrI a h = coef2 a b h := by
  unfold coef2
  rw [def_X_left_i, mul_div_mul_right _ _ hb]

/-- ch14-086 (folio 147): p is more favourable to a/h than q is to b/h, if
a/ph ÷ a/h > b/qh ÷ b/h, i.e. if … the coefficient of influence of p on a/h is greater
than the coefficient of influence of q on b/h (前提 ph は p ∧ h)。 -/
theorem th_14_r086 (a b p q h : IProp) (hcp : Cons (iand p h)) (hcq : Cons (iand q h)) :
    PrI a (iand p h) / PrI a h > PrI b (iand q h) / PrI b h
      ↔ coef2 a p h > coef2 b q h := by
  rw [ratio_eq_coef2 a p h (cons_of_pos_src p h hcp),
    ratio_eq_coef2 b q h (cons_of_pos_src q h hcq)]

/-- ch14-088 (folio 147): (33) の証明 a/hh₁ = a/h . (a/hx ÷ a/h) . (a/hh₁x ÷ a/hx) .
(a/hh₁ ÷ a/hh₁x) (分母が 0 でないとき; 前提の連言は印刷の順)。 -/
theorem th_14_r088 (a h h₁ x : IProp) (ha : PrI a h ≠ 0) (hx : PrI a (iand h x) ≠ 0)
    (hx1 : PrI a (iand (iand h h₁) x) ≠ 0) :
    PrI a (iand h h₁) = PrI a h * (PrI a (iand h x) / PrI a h)
      * (PrI a (iand (iand h h₁) x) / PrI a (iand h x))
      * (PrI a (iand h h₁) / PrI a (iand (iand h h₁) x)) := by
  field_simp

/-- ch14-091 (folio 148) の印刷形の右辺 (x/hh₁a ÷ x/ha) . (h₁/ha ÷ h₁/hax) は
X により恒等的に 1 (前提 hh₁a を h₁ ∧ (a ∧ h)、hax を x ∧ (a ∧ h) で)。 -/
theorem th_14_r091_rhs_one (a x h₁ h : IProp) (hv : PrI x (iand a h) ≠ 0)
    (hu : PrI h₁ (iand x (iand a h)) ≠ 0) :
    (PrI x (iand h₁ (iand a h)) / PrI x (iand a h))
      * (PrI h₁ (iand a h) / PrI h₁ (iand x (iand a h))) = 1 := by
  have e := bayes_mul x h₁ (iand a h)
  rw [div_mul_div_comm, e, mul_comm (PrI h₁ (iand x (iand a h)))]
  exact div_self (mul_ne_zero hv hu)

/-- ch14-091 の印刷形の左辺は a/hh₁ ÷ a/hx に縮む。よって印刷形は
a/hh₁ = a/hx と同値 (右辺が 1 なので)。 -/
theorem th_14_r091_printed_iff (a x h₁ h : IProp) (hv : PrI x (iand a h) ≠ 0)
    (hu : PrI h₁ (iand x (iand a h)) ≠ 0) (hD : PrI a (iand x (iand h₁ h)) ≠ 0)
    (hB : PrI a (iand x h) ≠ 0) :
    ((PrI a (iand x (iand h₁ h)) / PrI a (iand x h))
        * (PrI a (iand h₁ h) / PrI a (iand x (iand h₁ h)))
      = (PrI x (iand h₁ (iand a h)) / PrI x (iand a h))
        * (PrI h₁ (iand a h) / PrI h₁ (iand x (iand a h))))
      ↔ PrI a (iand h₁ h) = PrI a (iand x h) := by
  rw [th_14_r091_rhs_one a x h₁ h hv hu]
  have e : (PrI a (iand x (iand h₁ h)) / PrI a (iand x h))
      * (PrI a (iand h₁ h) / PrI a (iand x (iand h₁ h)))
      = PrI a (iand h₁ h) / PrI a (iand x h) := by field_simp
  rw [e, div_eq_one_iff_eq hB]

/-- ch14-091 の修正形 (✎): (a/hh₁x ÷ a/hx) . (a/hh₁ ÷ a/hh₁x)
= (h₁/ah ÷ h₁/h) . (x/h ÷ x/ah) — 逆原理 (38) を仮説 h₁, x・データ a で並べ替えた形
(phase7d の D3 と同じ修正)。 -/
theorem th_14_r091_cor (a x h₁ h : IProp) (ha : PrI a h ≠ 0) (h1 : PrI h₁ h ≠ 0)
    (hxh : PrI x h ≠ 0) (hxa : PrI x (iand a h) ≠ 0)
    (hD : PrI a (iand x (iand h₁ h)) ≠ 0) (h1a : PrI h₁ (iand a h) ≠ 0) :
    (PrI a (iand x (iand h₁ h)) / PrI a (iand x h))
        * (PrI a (iand h₁ h) / PrI a (iand x (iand h₁ h)))
      = (PrI h₁ (iand a h) / PrI h₁ h) * (PrI x h / PrI x (iand a h)) := by
  have e1 := bayes_mul a h₁ h
  have e2 := bayes_mul a x h
  have hB : PrI a (iand x h) ≠ 0 := by
    intro hz; rw [hz, zero_mul] at e2
    exact mul_ne_zero hxa ha e2.symm
  have hC : PrI a (iand h₁ h) = PrI h₁ (iand a h) * PrI a h / PrI h₁ h := by
    field_simp; linarith
  have hB' : PrI a (iand x h) = PrI x (iand a h) * PrI a h / PrI x h := by
    field_simp; linarith
  rw [hC, hB']
  field_simp

/-- ch14-093 (folio 148): (35) の証明 a/hh₁ = a/h . {(a/h ÷ a/hx) . (a/hh₁x ÷ a/h)} .
{(a/hx ÷ a/h) . (a/hh₁ ÷ a/hh₁x)} (分母が 0 でないとき)。 -/
theorem th_14_r093 (a h h₁ x : IProp) (ha : PrI a h ≠ 0) (hx : PrI a (iand h x) ≠ 0)
    (hx1 : PrI a (iand (iand h h₁) x) ≠ 0) :
    PrI a (iand h h₁) = PrI a h
      * ((PrI a h / PrI a (iand h x)) * (PrI a (iand (iand h h₁) x) / PrI a h))
      * ((PrI a (iand h x) / PrI a h) * (PrI a (iand h h₁) / PrI a (iand (iand h h₁) x))) := by
  field_simp

/-! ## §5 (36)(37) (folio 148) -/

/-- Def. XIII (folio 138): a₁/a₂h = a₁/h かつ a₂/a₁h = a₂/h のとき a₁/h と a₂/h は独立。 -/
def Independent (a₁ a₂ h : IProp) : Prop :=
  PrI a₁ (iand a₂ h) = PrI a₁ h ∧ PrI a₂ (iand a₁ h) = PrI a₂ h

/-- ch14-096 (folio 148): a₁a₂/h = a₁/a₂h . a₂/h = a₂/a₁h . a₁/h  by X。 -/
theorem th_14_r096 (a₁ a₂ h : IProp) :
    PrI (iand a₁ a₂) h = PrI a₁ (iand a₂ h) * PrI a₂ h ∧
      PrI a₁ (iand a₂ h) * PrI a₂ h = PrI a₂ (iand a₁ h) * PrI a₁ h :=
  ⟨def_X_left_i a₁ a₂ h, bayes_mul a₁ a₂ h⟩

/- ch14-097 (a₁/a₂h = a₁/h and a₂/a₁h = a₂/h by XIII) は仮定 Independent の再掲なので
定理にしない (台帳は 未)。 -/

/-- ch14-098 (folio 148): Therefore a₁a₂/h = a₁/h . a₂/h。 -/
theorem th_14_r098 (a₁ a₂ h : IProp) (hind : Independent a₁ a₂ h) :
    PrI (iand a₁ a₂) h = PrI a₁ h * PrI a₂ h := by
  rw [def_X_left_i, hind.1]

/-- 連鎖の積 p₁/h . p₂/p₁h . p₃/p₁p₂h …(前提は p₂ ∧ (p₁ ∧ h) の順に積む)。 -/
noncomputable def chainProd : IProp → List IProp → ℝ
  | _, [] => 1
  | H, [p] => PrI p H
  | H, p :: q :: l => PrI p H * chainProd (iand p H) (q :: l)

/-- ch14-101 (folio 148): p₁p₂p₃ … /h = p₁/h . p₂/p₁h . p₃/p₁p₂h …
by repeated applications of X。 -/
theorem th_14_r101 : ∀ (H p : IProp) (l : List IProp),
    PrI (conjL (p :: l)) H = chainProd H (p :: l)
  | H, p, [] => by simp [conjL, chainProd]
  | H, p, q :: l => by
      simp only [conjL, chainProd]
      rw [def_X_right_i, th_14_r101 (iand p H) q l]; ring

/-! ## §6 (38)(38.2) (folio 148–149) -/

/-- ch14-103 (folio 148): a₁/bh . b/h = b/a₁h . a₁/h。 -/
theorem th_14_r103 (a₁ b h : IProp) :
    PrI a₁ (iand b h) * PrI b h = PrI b (iand a₁ h) * PrI a₁ h := bayes_mul a₁ b h

/-- ch14-104 (folio 148): a₂/bh . b/h = b/a₂h . a₂/h  by X。 -/
theorem th_14_r104 (a₂ b h : IProp) :
    PrI a₂ (iand b h) * PrI b h = PrI b (iand a₂ h) * PrI a₂ h := bayes_mul a₂ b h

/-- ch14-105 (folio 148): since b/h ≠ 0, unless bh is inconsistent。 -/
theorem th_14_r105 (b h : IProp) (hcb : Cons (iand b h)) : PrI b h ≠ 0 :=
  cons_of_pos_src b h hcb

/-- ch14-113, ch14-114, ch14-115 (folio 149): **(38.2)** If a₁/h = a₂/h the above
reduces to a₁/bh = q₁ / (q₁ + q₂), a₂/bh = q₂ / (q₁ + q₂) ((38.1) の前提のもとで)。 -/
theorem th_14_r114 (a₁ a₂ b h : IProp) (q₁ q₂ : ℝ)
    (hq₁ : PrI b (iand a₁ h) = q₁) (hq₂ : PrI b (iand a₂ h) = q₂)
    (hsum : PrI a₁ (iand b h) + PrI a₂ (iand b h) = 1)
    (heq : PrI a₁ h = PrI a₂ h) (hca : Cons (iand a₁ h)) (hcb : Cons (iand b h)) :
    PrI a₁ (iand b h) = q₁ / (q₁ + q₂) ∧ PrI a₂ (iand b h) = q₂ / (q₁ + q₂) := by
  have hp : PrI a₁ h ≠ 0 := cons_of_pos_src _ _ hca
  have hb : PrI b h ≠ 0 := cons_of_pos_src _ _ hcb
  have e1 := bayes_mul a₁ b h
  have e2 := bayes_mul a₂ b h
  rw [hq₁] at e1; rw [hq₂, ← heq] at e2
  have hB : PrI b h = (q₁ + q₂) * PrI a₁ h := by
    linear_combination e1 + e2 - PrI b h * hsum
  have hq : q₁ + q₂ ≠ 0 := by
    intro hz; rw [hz, zero_mul] at hB; exact hb hB
  constructor
  · rw [eq_div_iff hq]
    have h3 : (PrI a₁ (iand b h) * (q₁ + q₂) - q₁) * PrI a₁ h = 0 := by
      linear_combination e1 - PrI a₁ (iand b h) * hB
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 hp
  · rw [eq_div_iff hq]
    have h3 : (PrI a₂ (iand b h) * (q₁ + q₂) - q₂) * PrI a₁ h = 0 := by
      linear_combination e2 - PrI a₂ (iand b h) * hB
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 hp

/-- ch14-116 (folio 149): since a₁/h ≠ 0, unless a₁h is inconsistent。 -/
theorem th_14_r116 (a₁ h : IProp) (hca : Cons (iand a₁ h)) : PrI a₁ h ≠ 0 :=
  cons_of_pos_src a₁ h hca

/-! ## §7 (39)(40) (folio 150) -/

/-- (24.2) の形: aH/h + āH/h = H/h。 -/
theorem pr_split (a H h : IProp) (hc : Cons h) :
    PrI (iand a H) h + PrI (iand (inot a) H) h = PrI H h := by
  have e := def_IX_i H a h
  rw [pr_comm H (inot a) h hc, pr_comm H a h hc] at e
  linarith

/-- ch14-120 (folio 150): (39) a/h₁h₂h = ah₁h₂/h ÷ h₁h₂/h
= ah₁h₂/h ÷ (ah₁h₂/h + āh₁h₂/h)  by X. and (24.2)。 -/
theorem th_14_r120 (a h₁ h₂ h : IProp) (hc : Cons h)
    (hc12 : Cons (iand (iand h₁ h₂) h)) :
    PrI a (iand (iand h₁ h₂) h) = PrI (iand a (iand h₁ h₂)) h / PrI (iand h₁ h₂) h ∧
      PrI (iand a (iand h₁ h₂)) h / PrI (iand h₁ h₂) h
        = PrI (iand a (iand h₁ h₂)) h
          / (PrI (iand a (iand h₁ h₂)) h + PrI (iand (inot a) (iand h₁ h₂)) h) := by
  have hne := cons_of_pos_src _ _ hc12
  refine ⟨?_, by rw [pr_split a (iand h₁ h₂) h hc]⟩
  rw [def_X_left_i, mul_div_cancel_right₀ _ hne]

/-- ch14-122 (folio 150): (40) a/h₁h₂ = ah₁/h₂ ÷ (ah₁/h₂ + āh₁/h₂)
= h₁/ah₂ . q ÷ (h₁/ah₂ . q + h₁/āh₂ . (1 − q)), where q = a/h₂。
名付けの行 ch14-125 (q = a/h₂) は前提 hq に写すだけなので台帳では 未 (定義のみ)。 -/
theorem th_14_r122 (a h₁ h₂ : IProp) (q : ℝ) (hq : q = PrI a h₂) (hc2 : Cons h₂)
    (hc12 : Cons (iand h₁ h₂)) :
    PrI a (iand h₁ h₂) = PrI (iand a h₁) h₂ / (PrI (iand a h₁) h₂ + PrI (iand (inot a) h₁) h₂) ∧
      PrI (iand a h₁) h₂ / (PrI (iand a h₁) h₂ + PrI (iand (inot a) h₁) h₂)
        = PrI h₁ (iand a h₂) * q
          / (PrI h₁ (iand a h₂) * q + PrI h₁ (iand (inot a) h₂) * (1 - q)) := by
  have hne := cons_of_pos_src _ _ hc12
  have hs := pr_split a h₁ h₂ hc2
  constructor
  · rw [hs, def_X_left_i, mul_div_cancel_right₀ _ hne]
  · rw [def_X_right_i a h₁ h₂, def_X_right_i (inot a) h₁ h₂, pr_not a h₂ hc2, hq]

/-- (40) の第 2 行 (folio 150)
a/h₁h₂ = h₂/ah₁ . p ÷ (h₂/ah₁ . p + h₂/āh₁ . (1 − p)), where p = a/h₁ (前提 h₁h₂ は h₂ ∧ h₁)。
名付けの行 ch14-124 (p = a/h₁) は前提 hp に写すだけなので台帳では 未 (定義のみ)。 -/
theorem th_14_r124 (a h₁ h₂ : IProp) (p : ℝ) (hp : p = PrI a h₁) (hc1 : Cons h₁)
    (hc21 : Cons (iand h₂ h₁)) :
    PrI a (iand h₂ h₁) = PrI h₂ (iand a h₁) * p
      / (PrI h₂ (iand a h₁) * p + PrI h₂ (iand (inot a) h₁) * (1 - p)) := by
  obtain ⟨e1, e2⟩ := th_14_r122 a h₂ h₁ p hp hc1 hc21
  rw [e1, e2]

/-! ## §8 (41)–(45) (folio 150–151) -/

/-- {aʰbʰc} (3 項の影響係数): abc/h ÷ (a/h . b/h . c/h)。 -/
noncomputable def coef3 (a b c h : IProp) : ℝ :=
  PrI (iand (iand a b) c) h / (PrI a h * PrI b h * PrI c h)

/-- 4 項の影響係数 {aʰbʰcʰd}。 -/
noncomputable def coef4 (a b c d h : IProp) : ℝ :=
  PrI (iand (iand (iand a b) c) d) h / (PrI a h * PrI b h * PrI c h * PrI d h)

/-- 1 項の係数 {ab} (区切りの無い係数): ab/h ÷ ab/h。 -/
noncomputable def coef1 (X h : IProp) : ℝ := PrI X h / PrI X h

/-- ch14-131 (folio 150): Def. XVI {aʰb} · {abʰc} = {aʰbʰc}
({…} を比で定義し、積の等式を定理として)。 -/
theorem th_14_r131 (a b c h : IProp) :
    coef2 a b h * coef2 (iand a b) c h = coef3 a b c h := by
  unfold coef2 coef3
  by_cases hab : PrI (iand a b) h = 0
  · have h1 := conj_le_left (iand a b) c h
    have h2 := ax_range_lo_i (iand (iand a b) c) h
    have h3 : PrI (iand (iand a b) c) h = 0 := by linarith
    rw [hab, h3]; simp
  · rw [div_mul_div_comm,
      show PrI a h * PrI b h * (PrI (iand a b) h * PrI c h)
        = PrI (iand a b) h * (PrI a h * PrI b h * PrI c h) by ring,
      mul_div_mul_left _ _ hab]

/-- (41) 一般: ab/h = {aʰb} . a/h . b/h (a/h . b/h = 0 の場合も含む)。 -/
theorem coef2_joint (a b h : IProp) (hc : Cons h) :
    PrI (iand a b) h = coef2 a b h * PrI a h * PrI b h := by
  unfold coef2
  by_cases hz : PrI a h * PrI b h = 0
  · have h1 := conj_le_left a b h
    have h2 := conj_le_right a b h hc
    have h3 := ax_range_lo_i (iand a b) h
    rcases mul_eq_zero.mp hz with e | e
    · have : PrI (iand a b) h = 0 := by linarith
      rw [this, e]; simp
    · have : PrI (iand a b) h = 0 := by linarith
      rw [this, e]; simp
  · rw [mul_assoc, div_mul_cancel₀ _ hz]

/-- ch14-134 (folio 150): since ab/h = a/bh . b/h。 -/
theorem th_14_r134 (a b h : IProp) : PrI (iand a b) h = PrI a (iand b h) * PrI b h :=
  def_X_left_i a b h

/-- ch14-138 (folio 151): abc/h = {abʰc}ab/h . c/h  by (41)。 -/
theorem th_14_r138 (a b c h : IProp) (hc : Cons h) :
    PrI (iand (iand a b) c) h = coef2 (iand a b) c h * PrI (iand a b) h * PrI c h :=
  coef2_joint (iand a b) c h hc

/-- ch14-139 (folio 151): 連鎖の 2 行目 = {abʰc} . {aʰb} . a/h . b/h . c/h  by (41)。 -/
theorem th_14_r139 (a b c h : IProp) (hc : Cons h) :
    PrI (iand (iand a b) c) h
      = coef2 (iand a b) c h * coef2 a b h * PrI a h * PrI b h * PrI c h := by
  rw [th_14_r138 a b c h hc, coef2_joint a b h hc]; ring

/-- ch14-142 (folio 151): since a/bh . b/h = b/ah . a/h。 -/
theorem th_14_r142 (a b h : IProp) :
    PrI a (iand b h) * PrI b h = PrI b (iand a h) * PrI a h := bayes_mul a b h

/-- ch14-144 (folio 151): since a/h . b/h . c/h = a/h . c/h . b/h。 -/
theorem th_14_r144 (a b c h : IProp) :
    PrI a h * PrI b h * PrI c h = PrI a h * PrI c h * PrI b h := by ring

/-- (41) の 3 項版: XYZ/h = {XʰYʰZ} . X/h . Y/h . Z/h。 -/
theorem coef3_joint (X Y Z h : IProp) (hc : Cons h) :
    PrI (iand (iand X Y) Z) h = coef3 X Y Z h * PrI X h * PrI Y h * PrI Z h := by
  unfold coef3
  by_cases hz : PrI X h * PrI Y h * PrI Z h = 0
  · have h1 := conj_le_left (iand X Y) Z h
    have h2 := conj_le_right (iand X Y) Z h hc
    have h3 := conj_le_left X Y h
    have h4 := conj_le_right X Y h hc
    have h5 := ax_range_lo_i (iand (iand X Y) Z) h
    have : PrI (iand (iand X Y) Z) h = 0 := by
      rcases mul_eq_zero.mp hz with e | e
      · rcases mul_eq_zero.mp e with e | e <;> linarith
      · linarith
    rw [this]; simp
  · rw [mul_assoc, mul_assoc, ← mul_assoc (PrI X h), div_mul_cancel₀ _ hz]

/-- (41) の 4 項版。 -/
theorem coef4_joint (W X Y Z h : IProp) (hc : Cons h) :
    PrI (iand (iand (iand W X) Y) Z) h
      = coef4 W X Y Z h * PrI W h * PrI X h * PrI Y h * PrI Z h := by
  unfold coef4
  by_cases hz : PrI W h * PrI X h * PrI Y h * PrI Z h = 0
  · have h1 := conj_le_left (iand (iand W X) Y) Z h
    have h2 := conj_le_right (iand (iand W X) Y) Z h hc
    have h3 := conj_le_left (iand W X) Y h
    have h4 := conj_le_right (iand W X) Y h hc
    have h6 := conj_le_left W X h
    have h7 := conj_le_right W X h hc
    have h5 := ax_range_lo_i (iand (iand (iand W X) Y) Z) h
    have : PrI (iand (iand (iand W X) Y) Z) h = 0 := by
      rcases mul_eq_zero.mp hz with e | e
      · rcases mul_eq_zero.mp e with e | e
        · rcases mul_eq_zero.mp e with e | e <;> linarith
        · linarith
      · linarith
    rw [this]; simp
  · rw [show PrI (iand (iand (iand W X) Y) Z) h / (PrI W h * PrI X h * PrI Y h * PrI Z h)
          * PrI W h * PrI X h * PrI Y h * PrI Z h
        = PrI (iand (iand (iand W X) Y) Z) h / (PrI W h * PrI X h * PrI Y h * PrI Z h)
          * (PrI W h * PrI X h * PrI Y h * PrI Z h) by ring,
      div_mul_cancel₀ _ hz]

/-- ch14-148 (folio 151): abcde/h = {abʰcdʰe} . ab/h . cd/h . e/h
(abcde は塊 ab, cd, e の連言)。 -/
theorem th_14_r148 (a b c d e h : IProp) (hc : Cons h) :
    PrI (iand (iand (iand a b) (iand c d)) e) h
      = coef3 (iand a b) (iand c d) e h * PrI (iand a b) h * PrI (iand c d) h * PrI e h :=
  coef3_joint _ _ _ h hc

/-- ch14-149 (folio 151): 連鎖の 2 行目
= {abʰcdʰe} . {aʰb} . a/h . b/h . cd/h . e/h。 -/
theorem th_14_r149 (a b c d e h : IProp) (hc : Cons h) :
    PrI (iand (iand (iand a b) (iand c d)) e) h
      = coef3 (iand a b) (iand c d) e h * coef2 a b h
        * PrI a h * PrI b h * PrI (iand c d) h * PrI e h := by
  rw [th_14_r148 a b c d e h hc, coef2_joint a b h hc]; ring

/-- ch14-150 (folio 151): and also abcde/h = {aʰbʰcdʰe} . a/h . b/h . cd/h . e/h。 -/
theorem th_14_r150 (a b c d e h : IProp) (hc : Cons h) :
    PrI (iand (iand (iand a b) (iand c d)) e) h
      = coef4 a b (iand c d) e h * PrI a h * PrI b h * PrI (iand c d) h * PrI e h :=
  coef4_joint a b (iand c d) e h hc

/-- ch14-152 (folio 151): (44) {aʰb} . {ab} = {aʰb}。 -/
theorem th_14_r152 (a b h : IProp) : coef2 a b h * coef1 (iand a b) h = coef2 a b h := by
  unfold coef1 coef2
  by_cases hz : PrI (iand a b) h = 0
  · rw [hz]; simp
  · rw [div_self hz, mul_one]

/-- ch14-153 (folio 151): For ab/h = {ab}ab/h。 -/
theorem th_14_r153 (a b h : IProp) : PrI (iand a b) h = coef1 (iand a b) h * PrI (iand a b) h := by
  unfold coef1
  by_cases hz : PrI (iand a b) h = 0
  · rw [hz]; simp
  · rw [div_self hz, one_mul]

/-- ch14-154 (folio 151): we may put {ab} = 1 (ab/h ≠ 0 のとき)。 -/
theorem th_14_r154 (a b h : IProp) (hz : PrI (iand a b) h ≠ 0) : coef1 (iand a b) h = 1 :=
  div_self hz

/-- ch14-158 (folio 151): (45) aab/h = ab/h  by (vi.) and (12)
(Lean は公理 (iii) の恒真式 aa ≡ a の代入で導く)。 -/
theorem th_14_r158 (a b h : IProp) (hc : Cons h) :
    PrI (iand (iand a a) b) h = PrI (iand a b) h :=
  subst_taut (Form.conj (Form.conj (Form.var 0) (Form.var 0)) (Form.var 1))
    (Form.conj (Form.var 0) (Form.var 1)) (env3 a b a) h hc (by taut3)

end KeynesI

namespace KeynesI

/-! ## §8 (46)–(49.1) の道具: リスト上の積・係数・比例 -/

/-- Π: リスト上の積。 -/
noncomputable def prodL (f : IProp → ℝ) (l : List IProp) : ℝ := (l.map f).prod

/-- {a^{H}b^{H}c^{H} …}: 全ての項を区切った影響係数 abc …/H ÷ (a/H . b/H . c/H …)。 -/
noncomputable def coefL (ds : List IProp) (H : IProp) : ℝ :=
  PrI (conjL ds) H / prodL (fun d => PrI d H) ds

/-- 比例式 u : u′ : u″ : … = v : v′ : v″ : … と u ∝ v (選択肢 i を動かしたとき、
共通の 0 でない比例定数がある)。 -/
def Proportional {ι : Type} (u v : ι → ℝ) : Prop :=
  ∃ k : ℝ, k ≠ 0 ∧ ∀ i, u i = k * v i

theorem prodL_nil (f : IProp → ℝ) : prodL f [] = 1 := rfl
theorem prodL_cons (f : IProp → ℝ) (d : IProp) (l : List IProp) :
    prodL f (d :: l) = f d * prodL f l := by simp [prodL]

theorem prodL_mul (f g : IProp → ℝ) :
    ∀ l : List IProp, prodL (fun d => f d * g d) l = prodL f l * prodL g l
  | [] => by simp [prodL]
  | d :: l => by rw [prodL_cons, prodL_cons, prodL_cons, prodL_mul f g l]; ring

theorem prodL_div (f g : IProp → ℝ) :
    ∀ l : List IProp, prodL (fun d => f d / g d) l = prodL f l / prodL g l
  | [] => by simp [prodL]
  | d :: l => by rw [prodL_cons, prodL_cons, prodL_cons, prodL_div f g l, div_mul_div_comm]

theorem prodL_const (c : ℝ) : ∀ l : List IProp, prodL (fun _ => c) l = c ^ l.length
  | [] => by simp [prodL]
  | d :: l => by rw [prodL_cons, prodL_const c l]; simp [pow_succ]; ring

theorem prodL_congr (f g : IProp → ℝ) :
    ∀ l : List IProp, (∀ d ∈ l, f d = g d) → prodL f l = prodL g l
  | [], _ => rfl
  | d :: l, h => by
      rw [prodL_cons, prodL_cons, h d (by simp),
        prodL_congr f g l (fun e he => h e (List.mem_cons_of_mem _ he))]

theorem prodL_ne_zero (f : IProp → ℝ) :
    ∀ l : List IProp, (∀ d ∈ l, f d ≠ 0) → prodL f l ≠ 0
  | [], _ => by simp [prodL]
  | d :: l, h => by
      rw [prodL_cons]
      exact mul_ne_zero (h d (by simp)) (prodL_ne_zero f l (fun e he => h e (List.mem_cons_of_mem _ he)))

theorem prodL_nonneg (f : IProp → ℝ) :
    ∀ l : List IProp, (∀ d ∈ l, 0 ≤ f d) → 0 ≤ prodL f l
  | [], _ => by simp [prodL]
  | d :: l, h => by
      rw [prodL_cons]
      exact mul_nonneg (h d (by simp)) (prodL_nonneg f l (fun e he => h e (List.mem_cons_of_mem _ he)))

theorem prodL_pos (f : IProp → ℝ) :
    ∀ l : List IProp, (∀ d ∈ l, 0 < f d) → 0 < prodL f l
  | [], _ => by simp [prodL]
  | d :: l, h => by
      rw [prodL_cons]
      exact mul_pos (h d (by simp)) (prodL_pos f l (fun e he => h e (List.mem_cons_of_mem _ he)))

theorem prodL_ge_one (f : IProp → ℝ) :
    ∀ l : List IProp, (∀ d ∈ l, 1 ≤ f d) → 1 ≤ prodL f l
  | [], _ => by simp [prodL]
  | d :: l, h => by
      rw [prodL_cons]
      exact one_le_mul_of_one_le_of_one_le (h d (by simp))
        (prodL_ge_one f l (fun e he => h e (List.mem_cons_of_mem _ he)))

theorem prodL_le_one (f : IProp → ℝ) :
    ∀ l : List IProp, (∀ d ∈ l, 0 ≤ f d ∧ f d ≤ 1) → prodL f l ≤ 1
  | [], _ => by simp [prodL]
  | d :: l, h => by
      rw [prodL_cons]
      have h1 := h d (by simp)
      have h2 := prodL_le_one f l (fun e he => h e (List.mem_cons_of_mem _ he))
      have h3 := prodL_nonneg f l (fun e he => (h e (List.mem_cons_of_mem _ he)).1)
      nlinarith

theorem prodL_gt_one (f : IProp → ℝ) :
    ∀ l : List IProp, l ≠ [] → (∀ d ∈ l, 1 < f d) → 1 < prodL f l
  | [], hne, _ => absurd rfl hne
  | d :: l, _, h => by
      rw [prodL_cons]
      have h1 := h d (by simp)
      have h2 := prodL_ge_one f l (fun e he => (h e (List.mem_cons_of_mem _ he)).le)
      nlinarith

theorem prodL_lt_one (f : IProp → ℝ) :
    ∀ l : List IProp, l ≠ [] → (∀ d ∈ l, 0 ≤ f d ∧ f d < 1) → prodL f l < 1
  | [], hne, _ => absurd rfl hne
  | d :: l, _, h => by
      rw [prodL_cons]
      have h1 := h d (by simp)
      have h2 := prodL_le_one f l (fun e he => ⟨(h e (List.mem_cons_of_mem _ he)).1,
        (h e (List.mem_cons_of_mem _ he)).2.le⟩)
      have h3 := prodL_nonneg f l (fun e he => (h e (List.mem_cons_of_mem _ he)).1)
      nlinarith

/-- abc …/H ≤ d/H (d が abc … の一つのとき)。 -/
theorem conjL_le (H : IProp) (hc : Cons H) :
    ∀ l : List IProp, ∀ d ∈ l, PrI (conjL l) H ≤ PrI d H
  | [], d, hd => by simp at hd
  | [e], d, hd => by simp at hd; subst hd; simp [conjL]
  | e :: f :: l, d, hd => by
      simp only [conjL]
      rcases List.mem_cons.mp hd with h1 | h1
      · subst h1; exact conj_le_left _ _ _
      · exact le_trans (conj_le_right _ _ _ hc) (conjL_le H hc (f :: l) d h1)

/-- **(41.2)** のリスト形: abc …/H = {a^{H}b^{H}c^{H} …} . a/H . b/H . c/H …
(積が 0 の場合も含む)。 -/
theorem coefL_joint (ds : List IProp) (H : IProp) (hc : Cons H) :
    PrI (conjL ds) H = coefL ds H * prodL (fun d => PrI d H) ds := by
  unfold coefL
  by_cases hz : prodL (fun d => PrI d H) ds = 0
  · rw [hz, div_zero, zero_mul]
    unfold prodL at hz
    obtain ⟨d, hd, hd0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hz)
    have := conjL_le H hc ds d hd
    have := ax_range_lo_i (conjL ds) H
    linarith
  · rw [div_mul_cancel₀ _ hz]

/-- Π x/dh . Π d/h = (x/h)^{n+1} . Π d/xh (Def. X を項ごとに; 割り算なし)。 -/
theorem prod_inverse (x h : IProp) :
    ∀ ds : List IProp,
      prodL (fun d => PrI x (iand d h)) ds * prodL (fun d => PrI d h) ds
        = PrI x h ^ ds.length * prodL (fun d => PrI d (iand x h)) ds
  | [] => by simp [prodL]
  | d :: l => by
      rw [prodL_cons, prodL_cons, prodL_cons, List.length_cons, pow_succ]
      have e := bayes_mul x d h
      have ih := prod_inverse x h l
      calc PrI x (iand d h) * prodL (fun d => PrI x (iand d h)) l
            * (PrI d h * prodL (fun d => PrI d h) l)
          = (PrI x (iand d h) * PrI d h)
            * (prodL (fun d => PrI x (iand d h)) l * prodL (fun d => PrI d h) l) := by ring
        _ = (PrI d (iand x h) * PrI x h)
            * (PrI x h ^ l.length * prodL (fun d => PrI d (iand x h)) l) := by rw [e, ih]
        _ = PrI x h ^ l.length * PrI x h
            * (PrI d (iand x h) * prodL (fun d => PrI d (iand x h)) l) := by ring

/-- 累積公式の一点: (x/h)ⁿ . x/habc … = (Π d/h ÷ abc …/h) . {a^{xh}b^{xh}c …} . Π x/dh。 -/
theorem cum_point (x h : IProp) (ds : List IProp) (n : ℕ) (hlen : ds.length = n + 1)
    (hcx : Cons (iand x h)) (hcD : Cons (iand (conjL ds) h)) :
    PrI x h ^ n * PrI x (iand (conjL ds) h)
      = prodL (fun d => PrI d h) ds / PrI (conjL ds) h
        * (coefL ds (iand x h) * prodL (fun d => PrI x (iand d h)) ds) := by
  have hD := cons_of_pos_src _ _ hcD
  have e1 := bayes_mul x (conjL ds) h
  have e2 := coefL_joint ds (iand x h) hcx
  have e3 := prod_inverse x h ds
  rw [hlen] at e3
  have hx : PrI x (iand (conjL ds) h)
      = PrI (conjL ds) (iand x h) * PrI x h / PrI (conjL ds) h := by
    field_simp; linarith
  rw [hx, e2]
  field_simp
  linear_combination (-coefL ds (iand x h)) * e3

/-! ## §8 (46) の証明 (folio 151–152) -/

/-- ch14-160 (folio 151): (46) x/ah : x′/ah : x″/ah : …
= x/h . a/xh : x′/h . a/x′h : x″/h . a/x″h : …  by (38)。 -/
theorem th_14_r160 {ι : Type} (x : ι → IProp) (a h : IProp) (hca : Cons (iand a h)) :
    Proportional (fun i => PrI (x i) (iand a h)) (fun i => PrI (x i) h * PrI a (iand (x i) h)) := by
  have ha := cons_of_pos_src a h hca
  refine ⟨(PrI a h)⁻¹, inv_ne_zero ha, fun i => ?_⟩
  have e := bayes_mul (x i) a h
  field_simp
  linarith

/-- ch14-162 の修正形 (✎): x/ah . x/bh . x/ch … : x′/ah . x′/bh . x′/ch … : …
= (x/h)^{n+1}a/xh . b/xh … : (x′/h)^{n+1}a/x′h . b/x′h … : …(n + 1 個の命題 a, b, c …;
連鎖の頭 ch14-161 の x′/a, x′/b, x′/c … を x′/ah, x′/bh, x′/ch … に)。
印刷形は Printed46Line2、反例は Ch14Models.printed_46_line2_false。 -/
theorem th_14_r162_cor {ι : Type} (x : ι → IProp) (h : IProp) (ds : List IProp) (n : ℕ)
    (hlen : ds.length = n + 1) (hd : ∀ d ∈ ds, Cons (iand d h)) :
    Proportional (fun i => prodL (fun d => PrI (x i) (iand d h)) ds)
      (fun i => PrI (x i) h ^ (n + 1) * prodL (fun d => PrI d (iand (x i) h)) ds) := by
  have hP := prodL_ne_zero (fun d => PrI d h) ds (fun d hm => cons_of_pos_src d h (hd d hm))
  refine ⟨(prodL (fun d => PrI d h) ds)⁻¹, inv_ne_zero hP, fun i => ?_⟩
  have e := prod_inverse (x i) h ds
  rw [hlen] at e
  field_simp
  linarith

/-- ch14-161 の印刷どおりの連鎖の頭: x/ah . x/bh . x/ch … : x′/a . x′/b . x′/c … :
x″/a . x″/b . x″/c … : …(選択肢 x = x 0 だけ前提に h があり、x′, x″ … = x i (i ≥ 1) の
前提には h が無い; 印刷の「x′b/」は x′/b と読む)。 -/
noncomputable def head46Printed (x : ℕ → IProp) (h : IProp) (ds : List IProp) (i : ℕ) : ℝ :=
  if i = 0 then prodL (fun d => PrI (x i) (iand d h)) ds else prodL (fun d => PrI (x i) d) ds

/-- ch14-162 の印刷形 (folio 151) を定理文の形の命題として: x/ah . x/bh . x/ch … :
x′/a . x′/b . x′/c … : … = (x/h)^{n+1}a/xh . b/xh … : (x′/h)^{n+1}a/x′h . b/x′h … : …。 -/
def Printed46Line2 (x : ℕ → IProp) (h : IProp) (ds : List IProp) (n : ℕ) : Prop :=
  Proportional (head46Printed x h ds)
    (fun i => PrI (x i) h ^ (n + 1) * prodL (fun d => PrI d (iand (x i) h)) ds)

/-- ch14-162 の印刷形が言っていること: x/ah . x/bh … ≠ 0 のとき、印刷形は
「x′, x″ … の全てで x′/a . x′/b … = x′/ah . x′/bh …」と同値 (前提から h を落としても
積が変わらない場合に限って成り立つ)。 -/
theorem th_14_r162_printed_iff (x : ℕ → IProp) (h : IProp) (ds : List IProp) (n : ℕ)
    (hlen : ds.length = n + 1) (hd : ∀ d ∈ ds, Cons (iand d h))
    (h0 : prodL (fun d => PrI (x 0) (iand d h)) ds ≠ 0) :
    Printed46Line2 x h ds n ↔
      ∀ i, i ≠ 0 → prodL (fun d => PrI (x i) d) ds = prodL (fun d => PrI (x i) (iand d h)) ds := by
  obtain ⟨K, hK0, hK⟩ := th_14_r162_cor x h ds n hlen hd
  unfold Printed46Line2 head46Printed
  constructor
  · rintro ⟨k, _, hk⟩ i hi
    have e0 := hk 0
    have e0' := hK 0
    dsimp only at e0 e0'
    simp only [↓reduceIte] at e0
    have hv0 : PrI (x 0) h ^ (n + 1) * prodL (fun d => PrI d (iand (x 0) h)) ds ≠ 0 := by
      intro hz; rw [hz, mul_zero] at e0'; exact h0 e0'
    have hkK : k = K := mul_right_cancel₀ hv0 (e0.symm.trans e0')
    have ei := hk i
    have eKi := hK i
    dsimp only at ei eKi
    simp only [if_neg hi] at ei
    rw [ei, hkK, ← eKi]
  · intro hall
    refine ⟨K, hK0, fun i => ?_⟩
    by_cases hi : i = 0
    · subst hi; have e := hK 0; dsimp only at e ⊢; simp only [↓reduceIte]; exact e
    · have e := hK i; dsimp only at e ⊢; simp only [if_neg hi]; rw [hall i hi]; exact e

/-- ch14-165 (folio 152): Π^{n+1}x/ah : Π^{n+1}x′/ah : … = (x/h)^{n+1}Π^{n+1}a/xh :
(x′/h)^{n+1}Π^{n+1}a/x′h : …(連鎖の頭 ch14-164 は x′/ah の形で印刷)。 -/
theorem th_14_r165 {ι : Type} (x : ι → IProp) (h : IProp) (ds : List IProp) (n : ℕ)
    (hlen : ds.length = n + 1) (hd : ∀ d ∈ ds, Cons (iand d h)) :
    Proportional (fun i => prodL (fun d => PrI (x i) (iand d h)) ds)
      (fun i => PrI (x i) h ^ (n + 1) * prodL (fun d => PrI d (iand (x i) h)) ds) :=
  th_14_r162_cor x h ds n hlen hd

/-- ch14-167 (folio 152): x/habc … : x′/habc … : … = x/h . (abc …)/xh : x′/h . (abc …)/x′h : …
by (38) (前提 habc … は abc … ∧ h)。 -/
theorem th_14_r167 {ι : Type} (x : ι → IProp) (h : IProp) (ds : List IProp)
    (hcD : Cons (iand (conjL ds) h)) :
    Proportional (fun i => PrI (x i) (iand (conjL ds) h))
      (fun i => PrI (x i) h * PrI (conjL ds) (iand (x i) h)) :=
  th_14_r160 x (conjL ds) h hcD

/-- ch14-168 (folio 152): abc … /xh = {a^{xh}b^{xh}c …}Π^{n+1}a/xh  by (41.2)。 -/
theorem th_14_r168 (x h : IProp) (ds : List IProp) (hcx : Cons (iand x h)) :
    PrI (conjL ds) (iand x h) = coefL ds (iand x h) * prodL (fun d => PrI d (iand x h)) ds :=
  coefL_joint ds (iand x h) hcx

/-- ch14-170 (folio 152): ∴ (x/h)ⁿ . x/habc … : (x′/h)ⁿ . x′/habc … : …
= {a^{xh}b^{xh}c …}x/ah . x/bh . x/ch … : {a^{x′h}b^{x′h}c …}x′/ah . x′/bh . x′/ch … : …。 -/
theorem th_14_r170 {ι : Type} (x : ι → IProp) (h : IProp) (ds : List IProp) (n : ℕ)
    (hlen : ds.length = n + 1) (hcx : ∀ i, Cons (iand (x i) h))
    (hd : ∀ d ∈ ds, Cons (iand d h)) (hcD : Cons (iand (conjL ds) h)) :
    Proportional (fun i => PrI (x i) h ^ n * PrI (x i) (iand (conjL ds) h))
      (fun i => coefL ds (iand (x i) h) * prodL (fun d => PrI (x i) (iand d h)) ds) := by
  have hP := prodL_ne_zero (fun d => PrI d h) ds (fun d hm => cons_of_pos_src d h (hd d hm))
  have hD := cons_of_pos_src _ _ hcD
  exact ⟨prodL (fun d => PrI d h) ds / PrI (conjL ds) h, div_ne_zero hP hD,
    fun i => cum_point (x i) h ds n hlen (hcx i) hcD⟩

/-- ch14-171 (folio 152): which may be written
(x/h)ⁿ . x/habc … ∝ {a^{xh}b^{xh}c …} . x/ah . x/bh . x/ch …。 -/
theorem th_14_r171 {ι : Type} (x : ι → IProp) (h : IProp) (ds : List IProp) (n : ℕ)
    (hlen : ds.length = n + 1) (hcx : ∀ i, Cons (iand (x i) h))
    (hd : ∀ d ∈ ds, Cons (iand d h)) (hcD : Cons (iand (conjL ds) h)) :
    Proportional (fun i => PrI (x i) h ^ n * PrI (x i) (iand (conjL ds) h))
      (fun i => coefL ds (iand (x i) h) * prodL (fun d => PrI (x i) (iand d h)) ds) :=
  th_14_r170 x h ds n hlen hcx hd hcD

/-- ch14-174 (folio 152): 係数 {a^{xh}b^{xh}c …}, … が全て 1 と仮定すると
(x/h)ⁿx/habc … ∝ x/ah . x/bh . x/ch …。 -/
theorem th_14_r174 {ι : Type} (x : ι → IProp) (h : IProp) (ds : List IProp) (n : ℕ)
    (hlen : ds.length = n + 1) (hcx : ∀ i, Cons (iand (x i) h))
    (hd : ∀ d ∈ ds, Cons (iand d h)) (hcD : Cons (iand (conjL ds) h))
    (hunit : ∀ i, coefL ds (iand (x i) h) = 1) :
    Proportional (fun i => PrI (x i) h ^ n * PrI (x i) (iand (conjL ds) h))
      (fun i => prodL (fun d => PrI (x i) (iand d h)) ds) := by
  obtain ⟨k, hk, hp⟩ := th_14_r170 x h ds n hlen hcx hd hcD
  exact ⟨k, hk, fun i => by have e := hp i; simp only [hunit i, one_mul] at e; exact e⟩

/-- ch14-175 (folio 152): x/habc … ∝ x/ah . x/bh . x/ch …(因子 (x/h)ⁿ を落とした形)。
本文自身が「特別の条件の下でなければ誤り」とする形。ここでは特別の条件
(係数が全て 1、かつ x/h が選択肢によらない) の下での成立を示す。
一般には成り立たないことは Ch14Models.simplified_46_fails。
本文は特別の条件を述べていないので、前提 hconst (x/h が選択肢によらない) は印刷に無い。
hconst を外すと一般には偽 (上の反例) なので、台帳 ch14-175 は 未。 -/
theorem th_14_r175 {ι : Type} (x : ι → IProp) (h : IProp) (ds : List IProp) (n : ℕ)
    (hlen : ds.length = n + 1) (hcx : ∀ i, Cons (iand (x i) h))
    (hd : ∀ d ∈ ds, Cons (iand d h)) (hcD : Cons (iand (conjL ds) h))
    (hunit : ∀ i, coefL ds (iand (x i) h) = 1) (c : ℝ) (hconst : ∀ i, PrI (x i) h = c)
    (hc0 : c ≠ 0) :
    Proportional (fun i => PrI (x i) (iand (conjL ds) h))
      (fun i => prodL (fun d => PrI (x i) (iand d h)) ds) := by
  obtain ⟨k, hk, hp⟩ := th_14_r174 x h ds n hlen hcx hd hcD hunit
  refine ⟨k / c ^ n, div_ne_zero hk (pow_ne_zero n hc0), fun i => ?_⟩
  have e := hp i
  simp only [hconst i] at e
  field_simp
  linarith

/-! ## §8 (46.2) の証明 (folio 153) -/

/-- ch14-180 (folio 153): Σx′/habc … = 1  by (24.7)。 -/
theorem th_14_r180 (xs ds : List IProp) (h : IProp) (hc : Cons h)
    (hcD : Cons (iand (conjL ds) h)) (hE : ExclExh xs h) :
    (xs.map (fun x => PrI x (iand (conjL ds) h))).sum = 1 :=
  exclExh_sum xs _ hcD (exclExh_premiss xs (conjL ds) h hc hcD hE)

/-- ch14-179 の修正形 (✎): x/habc … ∝ (x/h)^{−n}{a^{xh}b^{xh}c …}Π^{n+1}x/ah
(印刷の Π^{n−1} を Π^{n+1} に)。印刷形の反例は Ch14Models.printed_46_2_prop_false。 -/
theorem th_14_r179_cor {ι : Type} (x : ι → IProp) (h : IProp) (ds : List IProp) (n : ℕ)
    (hlen : ds.length = n + 1) (hcx : ∀ i, Cons (iand (x i) h))
    (hd : ∀ d ∈ ds, Cons (iand d h)) (hcD : Cons (iand (conjL ds) h)) :
    Proportional (fun i => PrI (x i) (iand (conjL ds) h))
      (fun i => PrI (x i) h ^ (-(n : ℤ)) * coefL ds (iand (x i) h)
        * prodL (fun d => PrI (x i) (iand d h)) ds) := by
  obtain ⟨k, hk, hp⟩ := th_14_r170 x h ds n hlen hcx hd hcD
  refine ⟨k, hk, fun i => ?_⟩
  have hx := cons_of_pos_src _ _ (hcx i)
  have e : PrI (x i) h ^ n * PrI (x i) (iand (conjL ds) h)
      = k * (coefL ds (iand (x i) h) * prodL (fun d => PrI (x i) (iand d h)) ds) := hp i
  show PrI (x i) (iand (conjL ds) h) = k * (PrI (x i) h ^ (-(n : ℤ)) * coefL ds (iand (x i) h)
    * prodL (fun d => PrI (x i) (iand d h)) ds)
  rw [zpow_neg, zpow_natCast]
  field_simp
  linear_combination e

/-- ch14-178 の修正形 (✎): (46.2) x/habc … = (x/h)^{−n} . {a^{xh}b^{xh}c …}Π^{n+1}x/ah
÷ Σ[(x′/h)^{−n} . {a^{x′h}b^{x′h}c …}Π^{n+1}x′/ah] (x, x′, x″ … は排反・網羅)。
印刷形 (Π^{n−1}) の反例は Ch14Models.printed_46_2_false。 -/
theorem th_14_r178_cor (xs ds : List IProp) (h : IProp) (n : ℕ) (hlen : ds.length = n + 1)
    (hc : Cons h) (hE : ExclExh xs h) (hcx : ∀ x ∈ xs, Cons (iand x h))
    (hd : ∀ d ∈ ds, Cons (iand d h)) (hcD : Cons (iand (conjL ds) h))
    (x : IProp) (hx : x ∈ xs) :
    PrI x (iand (conjL ds) h)
      = PrI x h ^ (-(n : ℤ)) * coefL ds (iand x h) * prodL (fun d => PrI x (iand d h)) ds
        / (xs.map (fun x' => PrI x' h ^ (-(n : ℤ)) * coefL ds (iand x' h)
            * prodL (fun d => PrI x' (iand d h)) ds)).sum := by
  set k := prodL (fun d => PrI d h) ds / PrI (conjL ds) h with hkdef
  have hP := prodL_ne_zero (fun d => PrI d h) ds (fun d hm => cons_of_pos_src d h (hd d hm))
  have hD := cons_of_pos_src _ _ hcD
  have hk : k ≠ 0 := div_ne_zero hP hD
  have pt : ∀ y ∈ xs, PrI y (iand (conjL ds) h)
      = k * (PrI y h ^ (-(n : ℤ)) * coefL ds (iand y h) * prodL (fun d => PrI y (iand d h)) ds) := by
    intro y hy
    have hy0 := cons_of_pos_src _ _ (hcx y hy)
    have e := cum_point y h ds n hlen (hcx y hy) hcD
    rw [zpow_neg, zpow_natCast]
    rw [← hkdef] at e
    field_simp
    linarith
  have hs := th_14_r180 xs ds h hc hcD hE
  have hsum : (xs.map (fun x => PrI x (iand (conjL ds) h))).sum
      = (xs.map (fun x' => PrI x' h ^ (-(n : ℤ)) * coefL ds (iand x' h)
            * prodL (fun d => PrI x' (iand d h)) ds)).sum * k := by
    rw [← list_sum_mul_right]
    apply congrArg; apply List.map_congr_left; intro y hy; rw [pt y hy]; ring
  rw [hs] at hsum
  have hS : (xs.map (fun x' => PrI x' h ^ (-(n : ℤ)) * coefL ds (iand x' h)
            * prodL (fun d => PrI x' (iand d h)) ds)).sum ≠ 0 := by
    intro hz; rw [hz, zero_mul] at hsum; exact one_ne_zero hsum
  rw [pt x hx, eq_div_iff hS]
  linear_combination (-(PrI x h ^ (-(n : ℤ)) * coefL ds (iand x h)
    * prodL (fun d => PrI x (iand d h)) ds)) * hsum

/-! ## §8 (47) の証明 (folio 153) -/

/-- ch14-183 (folio 153): For abc … x/h = x/h . abc … /xh。 -/
theorem th_14_r183 (x h : IProp) (ds : List IProp) :
    PrI (iand (conjL ds) x) h = PrI x h * PrI (conjL ds) (iand x h) := by
  rw [def_X_left_i, mul_comm]

/-- ch14-184 (folio 153): ∴ abc … x/h ÷ (abc … /h . x/h) = abc … /xh ÷ abc … /h
= (a/h . b/h . c/h … ÷ abc … /h) . (abc … /xh ÷ (a/xh . b/xh . c/xh …))
. [a/xh ÷ a/h . b/xh ÷ b/h …](第 2 行 ch14-185 の続きを含む連鎖)。 -/
theorem th_14_r184 (x h : IProp) (ds : List IProp) (hx : PrI x h ≠ 0)
    (hP : prodL (fun d => PrI d h) ds ≠ 0)
    (hQ : prodL (fun d => PrI d (iand x h)) ds ≠ 0) :
    PrI (iand (conjL ds) x) h / (PrI (conjL ds) h * PrI x h)
        = PrI (conjL ds) (iand x h) / PrI (conjL ds) h ∧
      PrI (conjL ds) (iand x h) / PrI (conjL ds) h
        = (prodL (fun d => PrI d h) ds / PrI (conjL ds) h)
          * (PrI (conjL ds) (iand x h) / prodL (fun d => PrI d (iand x h)) ds)
          * prodL (fun d => PrI d (iand x h) / PrI d h) ds := by
  constructor
  · rw [th_14_r183, mul_comm (PrI (conjL ds) h), mul_div_mul_left _ _ hx]
  · rw [prodL_div]
    by_cases hD : PrI (conjL ds) h = 0
    · rw [hD]; simp
    · field_simp

/-- ch14-186 (folio 153): since a/xh ÷ a/h = x/ah ÷ x/h, etc.。 -/
theorem th_14_r186 (a x h : IProp) (ha : PrI a h ≠ 0) (hx : PrI x h ≠ 0) :
    PrI a (iand x h) / PrI a h = PrI x (iand a h) / PrI x h := by
  have e := bayes_mul a x h
  rw [div_eq_div_iff ha hx]
  linarith

/-! ## §8 (48.1) (folio 154) -/

/-- ch14-190 (folio 154): (48.1) x/habcd … ÷ x̄/habcd … : x/hbcd … ÷ x̄/hbcd …
= ({a^{xh}bcd …} · x/ah) ÷ ({a^{x̄h}bcd …} · x̄/ah) : x/h ÷ x̄/h
(B は bcd … の連言、比 R₁ : R₂ = S₁ : S₂ を R₁/R₂ = S₁/S₂ で; 前提 habcd … は (a ∧ B) ∧ h)。 -/
theorem th_14_r190 (x a B h : IProp)
    (hx : PrI x h ≠ 0) (hnx : PrI (inot x) h ≠ 0) (ha : PrI a h ≠ 0)
    (hJ : PrI (iand a B) h ≠ 0) (hBh : PrI B h ≠ 0)
    (hJx : PrI (iand a B) (iand x h) ≠ 0) (hJnx : PrI (iand a B) (iand (inot x) h) ≠ 0)
    (hBx : PrI B (iand x h) ≠ 0) (hBnx : PrI B (iand (inot x) h) ≠ 0) :
    (PrI x (iand (iand a B) h) / PrI (inot x) (iand (iand a B) h))
        / (PrI x (iand B h) / PrI (inot x) (iand B h))
      = ((coef2 a B (iand x h) * PrI x (iand a h))
          / (coef2 a B (iand (inot x) h) * PrI (inot x) (iand a h)))
        / (PrI x h / PrI (inot x) h) := by
  have hu : PrI a (iand x h) ≠ 0 := by
    intro hz
    have := conj_le_left a B (iand x h)
    have := ax_range_lo_i (iand a B) (iand x h)
    exact hJx (by linarith)
  have hv : PrI a (iand (inot x) h) ≠ 0 := by
    intro hz
    have := conj_le_left a B (iand (inot x) h)
    have := ax_range_lo_i (iand a B) (iand (inot x) h)
    exact hJnx (by linarith)
  have e1 : PrI x (iand (iand a B) h) = PrI (iand a B) (iand x h) * PrI x h / PrI (iand a B) h := by
    rw [eq_div_iff hJ]; exact bayes_mul x (iand a B) h
  have e2 : PrI (inot x) (iand (iand a B) h)
      = PrI (iand a B) (iand (inot x) h) * PrI (inot x) h / PrI (iand a B) h := by
    rw [eq_div_iff hJ]; exact bayes_mul (inot x) (iand a B) h
  have e3 : PrI x (iand B h) = PrI B (iand x h) * PrI x h / PrI B h := by
    rw [eq_div_iff hBh]; exact bayes_mul x B h
  have e4 : PrI (inot x) (iand B h) = PrI B (iand (inot x) h) * PrI (inot x) h / PrI B h := by
    rw [eq_div_iff hBh]; exact bayes_mul (inot x) B h
  have e5 : PrI x (iand a h) = PrI a (iand x h) * PrI x h / PrI a h := by
    rw [eq_div_iff ha]; exact bayes_mul x a h
  have e6 : PrI (inot x) (iand a h) = PrI a (iand (inot x) h) * PrI (inot x) h / PrI a h := by
    rw [eq_div_iff ha]; exact bayes_mul (inot x) a h
  rw [e1, e2, e3, e4, e5, e6]
  unfold coef2
  field_simp

/-! ## §8 (49) の証明 (folio 154) -/

/-- ch14-195 (folio 154): abc … /h = xabc … /h + x̄abc … /h  by (24.2)。 -/
theorem th_14_r195 (x h : IProp) (ds : List IProp) (hc : Cons h) :
    PrI (conjL ds) h = PrI (iand x (conjL ds)) h + PrI (iand (inot x) (conjL ds)) h :=
  (pr_split x (conjL ds) h hc).symm

/-- ch14-196 (folio 154): = x/h . abc … /xh + x̄/h . abc … /x̄h。 -/
theorem th_14_r196 (x h : IProp) (ds : List IProp) (hc : Cons h) :
    PrI (conjL ds) h = PrI x h * PrI (conjL ds) (iand x h)
      + PrI (inot x) h * PrI (conjL ds) (iand (inot x) h) := by
  rw [th_14_r195 x h ds hc, def_X_right_i, def_X_right_i]; ring

/-- 係数 ≮ 1 ならば abc …/H ≥ Π d/H。 -/
theorem joint_ge_prod (ds : List IProp) (H : IProp) (hc : Cons H)
    (hK : ¬ coefL ds H < 1) :
    prodL (fun d => PrI d H) ds ≤ PrI (conjL ds) H := by
  rw [coefL_joint ds H hc]
  have hQ := prodL_nonneg (fun d => PrI d H) ds (fun d _ => ax_range_lo_i d H)
  have hK' : 1 ≤ coefL ds H := not_lt.mp hK
  nlinarith

/-- ch14-197 (folio 154): ≥ x/h . Πa/xh . b/xh … + x̄/h Πa/x̄h . b/x̄h …
(since {a^{xh}b^{xh}c …} and {a^{x̄h}b^{x̄h}c …} are not less than unity;
連鎖の頭 abc …/h との不等式)。 -/
theorem th_14_r197 (x h : IProp) (ds : List IProp) (hc : Cons h)
    (hcx : Cons (iand x h)) (hcnx : Cons (iand (inot x) h))
    (hK : ¬ coefL ds (iand x h) < 1) (hK' : ¬ coefL ds (iand (inot x) h) < 1) :
    PrI (conjL ds) h ≥ PrI x h * prodL (fun d => PrI d (iand x h)) ds
      + PrI (inot x) h * prodL (fun d => PrI d (iand (inot x) h)) ds := by
  rw [th_14_r196 x h ds hc]
  have h1 := joint_ge_prod ds _ hcx hK
  have h2 := joint_ge_prod ds _ hcnx hK'
  have h3 := ax_range_lo_i x h
  have h4 := ax_range_lo_i (inot x) h
  nlinarith

/-- ch14-198 (folio 154): ≥ x/h . Π[ax/h ÷ x/h . bx/h ÷ x/h …]
+ x̄/h . Π[ax̄/h ÷ x̄/h . bx̄/h ÷ x̄/h …]。 -/
theorem th_14_r198 (x h : IProp) (ds : List IProp) (hc : Cons h)
    (hcx : Cons (iand x h)) (hcnx : Cons (iand (inot x) h))
    (hK : ¬ coefL ds (iand x h) < 1) (hK' : ¬ coefL ds (iand (inot x) h) < 1) :
    PrI (conjL ds) h ≥ PrI x h * prodL (fun d => PrI (iand d x) h / PrI x h) ds
      + PrI (inot x) h * prodL (fun d => PrI (iand d (inot x)) h / PrI (inot x) h) ds := by
  have hx := cons_of_pos_src _ _ hcx
  have hnx := cons_of_pos_src _ _ hcnx
  have e1 := prodL_congr (fun d => PrI (iand d x) h / PrI x h) (fun d => PrI d (iand x h)) ds
    (fun d _ => by beta_reduce; rw [def_X_left_i, mul_div_cancel_right₀ _ hx])
  have e2 := prodL_congr (fun d => PrI (iand d (inot x)) h / PrI (inot x) h)
    (fun d => PrI d (iand (inot x) h)) ds
    (fun d _ => by beta_reduce; rw [def_X_left_i, mul_div_cancel_right₀ _ hnx])
  rw [e1, e2]
  exact th_14_r197 x h ds hc hcx hcnx hK hK'

/-- Π d/xh = Π (x/dh ÷ x/h) . Π d/h。 -/
theorem prod_d_xh (x h : IProp) (ds : List IProp) (hx : PrI x h ≠ 0) :
    prodL (fun d => PrI d (iand x h)) ds
      = prodL (fun d => PrI x (iand d h) / PrI x h) ds * prodL (fun d => PrI d h) ds := by
  rw [prodL_div, prodL_const]
  have e := prod_inverse x h ds
  field_simp
  linarith

/-- ch14-199 の修正形 (✎): ∴ abc … /h ÷ Π[a/h . b/h …]
≥ x/h . Π[x/ah ÷ x/h . x/bh ÷ x/h …] + x̄/h . Π[x̄/ah ÷ x̄/h . x̄/bh ÷ x̄/h …]
(第 2 行 ch14-200 の続きを含む; 印刷の x/bx を x/bh に)。
印刷形 (x/bx) の反例は Ch14Models.printed_49_line4_false。 -/
theorem th_14_r199_cor (x h : IProp) (ds : List IProp) (hc : Cons h)
    (hcx : Cons (iand x h)) (hcnx : Cons (iand (inot x) h))
    (hd : ∀ d ∈ ds, Cons (iand d h))
    (hK : ¬ coefL ds (iand x h) < 1) (hK' : ¬ coefL ds (iand (inot x) h) < 1) :
    PrI (conjL ds) h / prodL (fun d => PrI d h) ds
      ≥ PrI x h * prodL (fun d => PrI x (iand d h) / PrI x h) ds
        + PrI (inot x) h * prodL (fun d => PrI (inot x) (iand d h) / PrI (inot x) h) ds := by
  have hx := cons_of_pos_src _ _ hcx
  have hnx := cons_of_pos_src _ _ hcnx
  have hP := prodL_pos (fun d => PrI d h) ds (fun d hm => pos_of_cons d h (hd d hm))
  have e := th_14_r197 x h ds hc hcx hcnx hK hK'
  rw [prod_d_xh x h ds hx, prod_d_xh (inot x) h ds hnx] at e
  rw [ge_iff_le, le_div_iff₀ hP]
  linarith

/-- ch14-203 (folio 154): Now G > G′ since x/ah > x/h, etc., and x̄/ah < x̄/h, etc.
(G = Π[x/ah ÷ x/h …]、G′ = Π[x̄/ah ÷ x̄/h …] は k の手前までの証拠についての積;
証拠が 1 つ以上あるとき)。 -/
theorem th_14_r203 (x h : IProp) (l : List IProp) (hl : l ≠ []) (hc : Cons h)
    (hcx : Cons (iand x h)) (hcnx : Cons (iand (inot x) h))
    (hd : ∀ d ∈ l, Cons (iand d h)) (hfav : ∀ d ∈ l, PrI x (iand d h) > PrI x h) :
    prodL (fun d => PrI x (iand d h) / PrI x h) l
      > prodL (fun d => PrI (inot x) (iand d h) / PrI (inot x) h) l := by
  have hx := pos_of_cons x h hcx
  have hnx := pos_of_cons (inot x) h hcnx
  have g1 := prodL_gt_one (fun d => PrI x (iand d h) / PrI x h) l hl
    (fun d hm => by rw [lt_div_iff₀ hx, one_mul]; exact hfav d hm)
  have g2 := prodL_lt_one (fun d => PrI (inot x) (iand d h) / PrI (inot x) h) l hl
    (fun d hm => by
      refine ⟨div_nonneg (ax_range_lo_i _ _) hnx.le, ?_⟩
      rw [div_lt_iff₀ hnx, one_mul, pr_not x _ (hd d hm), pr_not x h hc]
      linarith [hfav d hm])
  linarith

/- ch14-204 (since x/ah > x/h, etc.) は (49) の仮定「x/kh > x/h where k is any of the data」の
再掲なので定理にしない (台帳は 未)。 -/

/-- ch14-205 (folio 154): and x̄/ah < x̄/h, etc.。 -/
theorem th_14_r205 (x a h : IProp) (hc : Cons h) (hca : Cons (iand a h))
    (hfav : PrI x (iand a h) > PrI x h) : PrI (inot x) (iand a h) < PrI (inot x) h := by
  rw [pr_not x _ hca, pr_not x h hc]; linarith

/-- ch14-207 (folio 154): ∴ G (x/kh − x/h) > G′(x̄/h − x̄/kh)。 -/
theorem th_14_r207 (x k h : IProp) (G G' : ℝ) (hc : Cons h) (hck : Cons (iand k h))
    (hfav : PrI x (iand k h) > PrI x h) (hG : G > G') :
    G * (PrI x (iand k h) - PrI x h) > G' * (PrI (inot x) h - PrI (inot x) (iand k h)) := by
  have e : PrI (inot x) h - PrI (inot x) (iand k h) = PrI x (iand k h) - PrI x h := by
    rw [pr_not x _ hck, pr_not x h hc]; ring
  rw [e]
  exact mul_lt_mul_of_pos_right hG (by linarith)

/-- ch14-208 (folio 154): i.e. x/kh . G + x̄/kh . G′ > x/h . G + x̄/h . G′。 -/
theorem th_14_r208 (x k h : IProp) (G G' : ℝ) (hc : Cons h) (hck : Cons (iand k h))
    (hfav : PrI x (iand k h) > PrI x h) (hG : G > G') :
    PrI x (iand k h) * G + PrI (inot x) (iand k h) * G'
      > PrI x h * G + PrI (inot x) h * G' := by
  have := th_14_r207 x k h G G' hc hck hfav hG
  nlinarith

/-! ## §8 (49.1) (folio 155) -/

theorem list_sum_add (f g : IProp → ℝ) :
    ∀ l : List IProp, (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum
  | [] => by simp
  | x :: l => by simp [list_sum_add f g l]; ring

theorem list_sum_le (f g : IProp → ℝ) :
    ∀ l : List IProp, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | x :: l, h => by
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h x (by simp)) (list_sum_le f g l (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem list_sum_congr (f g : IProp → ℝ) :
    ∀ l : List IProp, (∀ x ∈ l, f x = g x) → (l.map f).sum = (l.map g).sum := by
  intro l h; apply congrArg; exact List.map_congr_left h

/-- d/xh = {dʰx} . d/h (Def. XV の形、x/h ≠ 0 のとき)。 -/
theorem d_xh_coef (d x h : IProp) (hx : PrI x h ≠ 0) (hd : PrI d h ≠ 0) :
    PrI d (iand x h) = coef2 d x h * PrI d h := by
  unfold coef2
  rw [def_X_left_i]
  field_simp

/-- ch14-210 (folio 155): (49.1) {aʰbʰcʰ …} = x/h . {a^{xh}b^{xh}c …}{aʰx}{bʰx}{cʰx} …
+ x′/h . {a^{x′h}b^{x′h}c …}{aʰx′}{bʰx′}{cʰx′} … + …(第 2・3 行 ch14-211, 212 の和を含む;
x, x′, x″ … は排反・網羅)。 -/
theorem th_14_r210 (xs ds : List IProp) (h : IProp) (hc : Cons h) (hE : ExclExh xs h)
    (hcx : ∀ x ∈ xs, Cons (iand x h)) (hd : ∀ d ∈ ds, Cons (iand d h)) :
    coefL ds h = (xs.map (fun x => PrI x h * coefL ds (iand x h)
      * prodL (fun d => coef2 d x h) ds)).sum := by
  have hP := prodL_ne_zero (fun d => PrI d h) ds (fun d hm => cons_of_pos_src d h (hd d hm))
  have e0 := th_25_i xs (conjL ds) h hc hE
  have e1 : (xs.map (fun x => PrI (iand x (conjL ds)) h))
      = xs.map (fun x => PrI x h * coefL ds (iand x h) * prodL (fun d => coef2 d x h) ds
          * prodL (fun d => PrI d h) ds) := by
    apply List.map_congr_left
    intro x hx
    have hx0 := cons_of_pos_src _ _ (hcx x hx)
    rw [def_X_right_i, coefL_joint ds (iand x h) (hcx x hx),
      prodL_congr (fun d => PrI d (iand x h)) (fun d => coef2 d x h * PrI d h) ds
        (fun d hm => d_xh_coef d x h hx0 (cons_of_pos_src d h (hd d hm))),
      prodL_mul]
    ring
  rw [e1, list_sum_mul_right] at e0
  rw [show coefL ds h = PrI (conjL ds) h / prodL (fun d => PrI d h) ds from rfl, e0,
    mul_div_cancel_right₀ _ hP]

/-- Σ_x x/h . {dʰx} = 1 (d/h ≠ 0)。 -/
theorem sum_w_coef (xs : List IProp) (d h : IProp) (hc : Cons h) (hE : ExclExh xs h)
    (hcx : ∀ x ∈ xs, Cons (iand x h)) (hd : PrI d h ≠ 0) :
    (xs.map (fun x => PrI x h * coef2 d x h)).sum = 1 := by
  have e0 := th_25_i xs d h hc hE
  have e1 : (xs.map (fun x => PrI x h * coef2 d x h))
      = xs.map (fun x => PrI (iand x d) h * (PrI d h)⁻¹) := by
    apply List.map_congr_left
    intro x hx
    have hx0 := cons_of_pos_src _ _ (hcx x hx)
    unfold coef2
    rw [pr_comm d x h hc]
    field_simp
  rw [e1, list_sum_mul_right, ← e0, mul_inv_cancel₀ hd]

/-- Σ w_x Π_d u(d, x) ≥ 1 (Σ w_x u(d, x) = 1、Σ w = 1、x ごとに u(·, x) − 1 の符号が揃う)。 -/
theorem cheb_ge_one (xs : List IProp) (w : IProp → ℝ) (u : IProp → IProp → ℝ)
    (hw : ∀ x ∈ xs, 0 ≤ w x) (hw1 : (xs.map w).sum = 1) :
    ∀ l : List IProp, (∀ d ∈ l, (xs.map (fun x => w x * u d x)).sum = 1) →
      (∀ x ∈ xs, (∀ d ∈ l, 1 ≤ u d x) ∨ (∀ d ∈ l, 0 ≤ u d x ∧ u d x ≤ 1)) →
      1 ≤ (xs.map (fun x => w x * prodL (fun d => u d x) l)).sum
  | [], _, _ => by
      have : (xs.map (fun x => w x * prodL (fun d => u d x) [])) = xs.map w := by
        apply List.map_congr_left; intro x _; simp [prodL]
      rw [this, hw1]
  | d :: l, hu, hs => by
      have ih := cheb_ge_one xs w u hw hw1 l
        (fun e he => hu e (List.mem_cons_of_mem _ he))
        (fun x hx => (hs x hx).imp (fun h e he => h e (List.mem_cons_of_mem _ he))
          (fun h e he => h e (List.mem_cons_of_mem _ he)))
      have hd1 := hu d (by simp)
      have e : (xs.map (fun x => w x * prodL (fun d => u d x) (d :: l)))
          = xs.map (fun x => (w x * prodL (fun d => u d x) l
              + w x * ((u d x - 1) * (prodL (fun d => u d x) l - 1)))
              + (w x * u d x - w x)) := by
        apply List.map_congr_left; intro x _; rw [prodL_cons]; ring
      have hnn : 0 ≤ (xs.map (fun x => w x * ((u d x - 1) * (prodL (fun d => u d x) l - 1)))).sum := by
        apply List.sum_nonneg
        intro t ht
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
        apply mul_nonneg (hw x hx)
        rcases hs x hx with h1 | h1
        · have a1 := h1 d (by simp)
          have a2 := prodL_ge_one (fun d => u d x) l (fun e he => h1 e (List.mem_cons_of_mem _ he))
          nlinarith
        · have a1 := h1 d (by simp)
          have a2 := prodL_le_one (fun d => u d x) l (fun e he => h1 e (List.mem_cons_of_mem _ he))
          nlinarith
      have hz : (xs.map (fun x => w x * u d x - w x)).sum = 0 := by
        have := list_sum_add (fun x => w x * u d x) (fun x => - w x) xs
        simp only [← sub_eq_add_neg] at this
        rw [this, hd1]
        have : (xs.map (fun x => - w x)).sum = - (xs.map w).sum := by
          rw [show (fun x => - w x) = (fun x => w x * (-1)) by funext x; ring,
            list_sum_mul_right]; ring
        rw [this, hw1]; ring
      rw [e, list_sum_add, list_sum_add, hz]
      linarith

/-- ch14-213 (folio 155): if {a^{xh}b^{xh}c …} etc. ≮ 1, and if {aʰx} − 1, {bʰx − 1},
{cʰx − 1}, etc., have the same sign, then {aʰbʰc …} is … from unity
(1 ≤ {aʰbʰc …} を n 文字で; 文字数とともに増えることのうち、1 からの下界の部分)。 -/
theorem th_14_r213 (xs ds : List IProp) (h : IProp) (hc : Cons h) (hE : ExclExh xs h)
    (hcx : ∀ x ∈ xs, Cons (iand x h)) (hd : ∀ d ∈ ds, Cons (iand d h))
    (hK : ∀ x ∈ xs, ¬ coefL ds (iand x h) < 1)
    (hsign : ∀ x ∈ xs, (∀ d ∈ ds, 1 ≤ coef2 d x h) ∨ (∀ d ∈ ds, coef2 d x h ≤ 1)) :
    1 ≤ coefL ds h := by
  rw [th_14_r210 xs ds h hc hE hcx hd]
  have hnn : ∀ d x, 0 ≤ coef2 d x h := fun d x =>
    div_nonneg (ax_range_lo_i _ _) (mul_nonneg (ax_range_lo_i _ _) (ax_range_lo_i _ _))
  have hcheb := cheb_ge_one xs (fun x => PrI x h) (fun d x => coef2 d x h)
    (fun x _ => ax_range_lo_i x h) (exclExh_sum xs h hc hE) ds
    (fun d hm => sum_w_coef xs d h hc hE hcx (cons_of_pos_src d h (hd d hm)))
    (fun x hx => (hsign x hx).imp id (fun h1 d hm => ⟨hnn d x, h1 d hm⟩))
  refine le_trans hcheb (list_sum_le _ _ xs (fun x hx => ?_))
  have hK1 : 1 ≤ coefL ds (iand x h) := not_lt.mp (hK x hx)
  have hP := prodL_nonneg (fun d => coef2 d x h) ds (fun d _ => hnn d x)
  have hw := ax_range_lo_i x h
  have : 0 ≤ PrI x h * prodL (fun d => coef2 d x h) ds := mul_nonneg hw hP
  nlinarith

/-! ## 付録 (folio 155–157): McColl と Czuber の記号 -/

/-- McColl の a/ε (à priori 前提 h に対する a の確率)。 -/
noncomputable def mcE (a h : IProp) : ℝ := PrI a h
/-- McColl の a/b (前提 h に b を加えたときの a の確率)。 -/
noncomputable def mcC (a b h : IProp) : ℝ := PrI a (iand b h)
/-- McColl の δ a/b (= a/b − a/ε、文 b への a の依存)。 -/
noncomputable def mcDelta (a b h : IProp) : ℝ := mcC a b h - mcE a h

/- ch14-218 (Thus a/ε = a/h) と ch14-219 (and a/b = a/bh) は McColl の記号の名付け
(上の mcE・mcC の定義そのもの) なので定理にしない (台帳は 未、定義のみ)。 -/

/-- ch14-222 (folio 156): Thus δ a/b = 0, where, in my terminology, b is irrelevant to a
on evidence h。 -/
theorem th_14_r222 (a b h : IProp) : mcDelta a b h = 0 ↔ PrI a (iand b h) = PrI a h := by
  unfold mcDelta mcC mcE; constructor <;> intro e <;> linarith

/-- ch14-223 (folio 156): ab/ε = a/ε . b/a = b/ε . a/b。 -/
theorem th_14_r223 (a b h : IProp) :
    mcE (iand a b) h = mcE a h * mcC b a h ∧ mcE a h * mcC b a h = mcE b h * mcC a b h := by
  unfold mcE mcC
  refine ⟨by rw [def_X_right_i]; ring, ?_⟩
  rw [mul_comm, ← def_X_right_i, def_X_left_i]; ring

/-- ch14-224 (folio 156): (a + b)/ε = a/ε + b/ε − ab/ε。 -/
theorem th_14_r224 (a b h : IProp) (hc : Cons h) :
    mcE (ior a b) h = mcE a h + mcE b h - mcE (iand a b) h := th_24_i a b h hc

/-- ch14-225 (folio 156): Also δ a/b = (A/B) δ b/a, where A = a/ε。
B は印刷に定義が無く、前提 hB で b/ε と補った (台帳は ≈)。
名付けの行 ch14-226 (A = a/ε) は前提 hA に写すだけなので台帳では 未 (定義のみ)。 -/
theorem th_14_r225 (a b h : IProp) (A B : ℝ) (hA : A = mcE a h) (hB : B = mcE b h)
    (hcb : Cons (iand b h)) : mcDelta a b h = (A / B) * mcDelta b a h := by
  have hb := cons_of_pos_src b h hcb
  have e := bayes_mul a b h
  unfold mcDelta mcC mcE at *
  rw [hA, hB]
  field_simp
  linarith

/-- ch14-227 (folio 156): He arrives … at the inverse formula
cᵣ/v = (cᵣ/ε . v/cᵣ) ÷ Σ_{r=1}^{r=n} cᵣ/ε . v/cᵣ (c₁ … cₙ は v の互いに排反な原因で、
v のあらゆる原因を含む: 前提 vh に対して排反・網羅)。 -/
theorem th_14_r227 (cs : List IProp) (v h : IProp) (hcv : Cons (iand v h))
    (hE : ExclExh cs (iand v h)) (c : IProp) :
    mcC c v h = (mcE c h * mcC v c h) / (cs.map (fun c' => mcE c' h * mcC v c' h)).sum := by
  have hv := cons_of_pos_src v h hcv
  have hs := exclExh_sum cs (iand v h) hcv hE
  have e : (cs.map (fun c' => mcE c' h * mcC v c' h))
      = cs.map (fun c' => PrI c' (iand v h) * PrI v h) := by
    apply List.map_congr_left; intro c' _
    unfold mcE mcC; rw [bayes_mul]; ring
  rw [e, list_sum_mul_right, hs, one_mul]
  unfold mcE mcC
  rw [eq_div_iff hv, bayes_mul]; ring

/-- ch14-228 (folio 156): a/b = (a/ε . b/a) ÷ (a/ε . b/a + ā/ε . b/ā)。 -/
theorem th_14_r228 (a b h : IProp) (hc : Cons h) (hcb : Cons (iand b h)) :
    mcC a b h = (mcE a h * mcC b a h) / (mcE a h * mcC b a h + mcE (inot a) h * mcC b (inot a) h) := by
  have hb := cons_of_pos_src b h hcb
  have hs := pr_split a b h hc
  rw [def_X_right_i a b h, def_X_right_i (inot a) b h] at hs
  unfold mcE mcC
  rw [show PrI a h * PrI b (iand a h) + PrI (inot a) h * PrI b (iand (inot a) h) = PrI b h by
    linarith]
  rw [eq_div_iff hb, bayes_mul]; ring

/-- Czuber の W(E) (前提 h に対する事象 E の確率)。 -/
noncomputable def czW (E h : IProp) : ℝ := PrI E h
/-- Czuber の W_F(E) (事象 F が起きたときの E の確率)。 -/
noncomputable def czWF (E F h : IProp) : ℝ := PrI E (iand F h)

/-- ch14-230 (folio 157): W_F(E) = W_F̄(E) as the criterion of the independence of the
events E and F (W_F(E) = W(E) と同値)。 -/
theorem th_14_r230 (E F h : IProp) (hc : Cons h) (hcnF : Cons (iand (inot F) h)) :
    czWF E F h = czWF E (inot F) h ↔ czWF E F h = czW E h := by
  have hnF := cons_of_pos_src _ _ hcnF
  have hs := pr_split F E h hc
  rw [def_X_right_i F E h, def_X_right_i (inot F) E h, pr_not F h hc] at hs
  rw [pr_not F h hc] at hnF
  unfold czWF czW
  constructor
  · intro e; rw [e] at hs ⊢; linarith
  · intro e
    have : (PrI E (iand F h) - PrI E (iand (inot F) h)) * (1 - PrI F h) = 0 := by
      rw [← e] at hs; linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hnF

/-- ch14-231 (folio 157): W_F(E) = 1, as the expression of the fact that E is a necessary
consequence of F ((F̄ + E)/h = 1 と同値)。 -/
theorem th_14_r231 (E F h : IProp) (hc : Cons h) (hcF : Cons (iand F h)) :
    czWF E F h = 1 ↔ PrI (ior (inot F) E) h = 1 := by
  have hF := cons_of_pos_src _ _ hcF
  have e1 := th_24_i (inot F) E h hc
  have e2 := pr_split F E h hc
  have e3 := pr_not F h hc
  rw [def_X_right_i F E h] at e2
  have e4 : PrI (ior (inot F) E) h = 1 - PrI F h + PrI E (iand F h) * PrI F h := by linarith
  unfold czWF
  rw [e4]
  constructor
  · intro e; rw [e]; ring
  · intro e
    have : (PrI E (iand F h) - 1) * PrI F h = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hF

end KeynesI

/-! ## 数値の反例モデル (ℚ、公理を用いない計算のみ)

3 命題の 8 個の世界 (p, q, r ∈ Bool) に重み w を置いた有限頻度モデル。条件付きの
確率は重みの比 C w f g = M(f ∧ g) / M(g) (前提 h は全世界)。重みが正の世界をもつ
連言が整合 (Cons) にあたる。 -/

namespace Ch14Models

/-- 述語 f を満たす世界の重みの和。 -/
def M (w : Bool → Bool → Bool → ℚ) (f : Bool → Bool → Bool → Bool) : ℚ :=
  ∑ p : Bool, ∑ q : Bool, ∑ r : Bool, if f p q r then w p q r else 0

/-- 条件付きの確率 f/g h (重みの比)。 -/
def C (w : Bool → Bool → Bool → ℚ) (f g : Bool → Bool → Bool → Bool) : ℚ :=
  M w (fun p q r => f p q r && g p q r) / M w g

def T : Bool → Bool → Bool → Bool := fun _ _ _ => true
def P1 : Bool → Bool → Bool → Bool := fun p _ _ => p
def N1 : Bool → Bool → Bool → Bool := fun p _ _ => !p
def P2 : Bool → Bool → Bool → Bool := fun _ q _ => q
def P3 : Bool → Bool → Bool → Bool := fun _ _ r => r
def P12 : Bool → Bool → Bool → Bool := fun p q _ => p && q
def P23 : Bool → Bool → Bool → Bool := fun _ q r => q && r
def P32 : Bool → Bool → Bool → Bool := fun _ q r => r && q
def P31 : Bool → Bool → Bool → Bool := fun p _ r => r && p

/-! ### (34) の証明行 ch14-091 — 世界の座標 (a, x, h₁)、重み (2, 1, 1, 2)
(phase7d の Erratum34Countermodel と同じ配置) -/

def w34 : Bool → Bool → Bool → ℚ
  | true, true, true => 2
  | true, false, false => 1
  | false, true, false => 1
  | false, false, true => 2
  | _, _, _ => 0

/-- **ch14-091 の印刷形は偽**: (a/hh₁x ÷ a/hx) . (a/hh₁ ÷ a/hh₁x) = 3/4 だが
(x/hh₁a ÷ x/ha) . (h₁/ha ÷ h₁/hax) = 1。 -/
theorem printed_34_false :
    (C w34 P1 P32 / C w34 P1 P2) * (C w34 P1 P3 / C w34 P1 P32)
      ≠ (C w34 P2 P31 / C w34 P2 P1) * (C w34 P3 P1 / C w34 P3 P12) := by
  norm_num [C, M, w34, Fintype.sum_bool, P1, P2, P3, P12, P31, P32]

/-- 同じモデルで修正形 (h₁/ah ÷ h₁/h) . (x/h ÷ x/ah) は左辺と一致する。 -/
theorem corrected_34_holds :
    (C w34 P1 P32 / C w34 P1 P2) * (C w34 P1 P3 / C w34 P1 P32)
      = (C w34 P3 P1 / C w34 P3 T) * (C w34 P2 T / C w34 P2 P1) := by
  norm_num [C, M, w34, Fintype.sum_bool, T, P1, P2, P3, P12, P31, P32]

/-! ### (49) の証明 4 行目 ch14-199 — 座標 (x, a, b)、x/h = 1/2、x のもとで a, b は
独立に 3/4、x̄ のもとで独立に 1/4 (重み ×32) -/

def w49 : Bool → Bool → Bool → ℚ
  | true, true, true => 9
  | true, true, false => 3
  | true, false, true => 3
  | true, false, false => 1
  | false, true, true => 1
  | false, true, false => 3
  | false, false, true => 3
  | false, false, false => 9

/-- (49) の仮定がこのモデルで成り立つ: {a^{xh}b^{xh}} ≮ 1、{a^{x̄h}b^{x̄h}} ≮ 1、
x/ah > x/h、x/bh > x/h。 -/
theorem hyp_49_hold :
    ¬ (C w49 P23 P1 / (C w49 P2 P1 * C w49 P3 P1) < 1) ∧
      ¬ (C w49 P23 N1 / (C w49 P2 N1 * C w49 P3 N1) < 1) ∧
      C w49 P1 T < C w49 P1 P2 ∧ C w49 P1 T < C w49 P1 P3 := by
  norm_num [C, M, w49, Fintype.sum_bool, T, P1, N1, P2, P3, P23]

/-- **ch14-199 の印刷形は偽**: 印刷どおり x/bx (= 1) を入れると、
abc …/h ÷ Π[a/h . b/h] = 5/4 は x/h . Π[x/ah ÷ x/h . x/bx ÷ x/h] + x̄/h . Π[…] = 13/8
以上でない。 -/
theorem printed_49_line4_false :
    ¬ (C w49 P23 T / (C w49 P2 T * C w49 P3 T)
      ≥ C w49 P1 T * ((C w49 P1 P2 / C w49 P1 T) * (C w49 P1 P31 / C w49 P1 T))
        + C w49 N1 T * ((C w49 N1 P2 / C w49 N1 T) * (C w49 N1 P3 / C w49 N1 T))) := by
  norm_num [C, M, w49, Fintype.sum_bool, T, P1, N1, P2, P3, P23, P31]

/-- 同じモデルで修正形 (x/bh) は成り立つ (等号)。 -/
theorem corrected_49_line4_holds :
    C w49 P23 T / (C w49 P2 T * C w49 P3 T)
      ≥ C w49 P1 T * ((C w49 P1 P2 / C w49 P1 T) * (C w49 P1 P3 / C w49 P1 T))
        + C w49 N1 T * ((C w49 N1 P2 / C w49 N1 T) * (C w49 N1 P3 / C w49 N1 T)) := by
  norm_num [C, M, w49, Fintype.sum_bool, T, P1, N1, P2, P3, P23]

/-! ### (46)–(46.2) — 座標 (x, a, b)、x の世界は重み 3、x̄ の世界は重み 1
(a, b は x とも互いとも独立; 係数は 1 だが x/h = 3/4 ≠ x̄/h) -/

def w46 : Bool → Bool → Bool → ℚ
  | true, _, _ => 3
  | false, _, _ => 1

/-- 係数 {a^{xh}b^{xh}}, {a^{x̄h}b^{x̄h}} は共に 1。 -/
theorem coef_unity_46 :
    C w46 P23 P1 / (C w46 P2 P1 * C w46 P3 P1) = 1 ∧
      C w46 P23 N1 / (C w46 P2 N1 * C w46 P3 N1) = 1 := by
  norm_num [C, M, w46, Fintype.sum_bool, P1, N1, P2, P3, P23]

/-- **ch14-175 (本文自身が誤りとする簡略形) は一般には成り立たない**:
係数が 1 でも x/hab ∝ x/ah . x/bh は偽 (x/h が選択肢で違うとき)。 -/
theorem simplified_46_fails :
    ¬ ∃ k : ℚ, C w46 P1 P23 = k * (C w46 P1 P2 * C w46 P1 P3) ∧
      C w46 N1 P23 = k * (C w46 N1 P2 * C w46 N1 P3) := by
  rintro ⟨k, h1, h2⟩
  norm_num [C, M, w46, Fintype.sum_bool, P1, N1, P2, P3, P23] at h1 h2
  linarith

/-- **ch14-178 の印刷形 (Π^{n−1}、n = 1 で空積) は偽**: 印刷どおりなら
x/hab = (x/h)^{−1}{…} ÷ Σ[(x′/h)^{−1}{…}] = 1/4 だが実際は 3/4。 -/
theorem printed_46_2_false :
    C w46 P1 P23 ≠ ((C w46 P1 T)⁻¹ * 1) / ((C w46 P1 T)⁻¹ * 1 + (C w46 N1 T)⁻¹ * 1) := by
  norm_num [C, M, w46, Fintype.sum_bool, T, P1, N1, P23]

/-- 同じモデルで修正形 (Π^{n+1}) は成り立つ。 -/
theorem corrected_46_2_holds :
    C w46 P1 P23
      = ((C w46 P1 T)⁻¹ * 1 * (C w46 P1 P2 * C w46 P1 P3))
        / ((C w46 P1 T)⁻¹ * 1 * (C w46 P1 P2 * C w46 P1 P3)
          + (C w46 N1 T)⁻¹ * 1 * (C w46 N1 P2 * C w46 N1 P3)) := by
  norm_num [C, M, w46, Fintype.sum_bool, T, P1, N1, P2, P3, P23]

/-- **ch14-179 の印刷形 (Π^{n−1}、n = 1) は偽**: x/hab ∝ (x/h)^{−1}{…} でない。 -/
theorem printed_46_2_prop_false :
    ¬ ∃ k : ℚ, C w46 P1 P23 = k * ((C w46 P1 T)⁻¹ * 1) ∧
      C w46 N1 P23 = k * ((C w46 N1 T)⁻¹ * 1) := by
  rintro ⟨k, h1, h2⟩
  norm_num [C, M, w46, Fintype.sum_bool, T, P1, N1, P23] at h1 h2
  linarith

/-! ### (46) 第 2 の比例式 ch14-162 — 座標 (x, a, b)、8 世界に一様な重み、前提 h は
「x または b」(全世界でない h を置かないと x′/a と x′/ah の違いが出ない)。n + 1 = 2 (a, b)、
選択肢は x と x′ = x̄ (x″, … も x̄ とすれば Printed46Line2 の一例) -/

def w1 : Bool → Bool → Bool → ℚ := fun _ _ _ => 1

/-- 前提 h = x + b。 -/
def Hxb : Bool → Bool → Bool → Bool := fun p _ r => p || r
/-- ah, bh, xh, x̄h。 -/
def AHxb : Bool → Bool → Bool → Bool := fun p q r => q && (p || r)
def BHxb : Bool → Bool → Bool → Bool := fun p _ r => r && (p || r)
def XHxb : Bool → Bool → Bool → Bool := fun p _ r => p && (p || r)
def NXHxb : Bool → Bool → Bool → Bool := fun p _ r => !p && (p || r)

/-- **ch14-162 の印刷形は偽**: x/ah . x/bh = 1/3、(x/h)² a/xh . b/xh = 1/9 から比例定数は 3
だが、印刷どおり h の無い x̄/a . x̄/b = 1/4 は 3 . (x̄/h)² a/x̄h . b/x̄h = 1/6 と違う。 -/
theorem printed_46_line2_false :
    ¬ ∃ k : ℚ, k ≠ 0 ∧
      C w1 P1 AHxb * C w1 P1 BHxb = k * (C w1 P1 Hxb ^ 2 * (C w1 P2 XHxb * C w1 P3 XHxb)) ∧
      C w1 N1 P2 * C w1 N1 P3 = k * (C w1 N1 Hxb ^ 2 * (C w1 P2 NXHxb * C w1 P3 NXHxb)) := by
  rintro ⟨k, _, h1, h2⟩
  simp only [C, M, w1, Fintype.sum_bool, P1, N1, P2, P3, Hxb, AHxb, BHxb, XHxb, NXHxb] at h1 h2
  norm_num at h1 h2
  linarith

/-- 同じモデルで修正形 (x̄/ah . x̄/bh) は比例定数 3 で成り立つ。 -/
theorem corrected_46_line2_holds :
    ∃ k : ℚ, k ≠ 0 ∧
      C w1 P1 AHxb * C w1 P1 BHxb = k * (C w1 P1 Hxb ^ 2 * (C w1 P2 XHxb * C w1 P3 XHxb)) ∧
      C w1 N1 AHxb * C w1 N1 BHxb = k * (C w1 N1 Hxb ^ 2 * (C w1 P2 NXHxb * C w1 P3 NXHxb)) :=
  ⟨3, by norm_num,
    by simp only [C, M, w1, Fintype.sum_bool, P1, P2, P3, Hxb, AHxb, BHxb, XHxb]; norm_num,
    by simp only [C, M, w1, Fintype.sum_bool, N1, P2, P3, Hxb, AHxb, BHxb, NXHxb]; norm_num⟩

/-! ### ch14-173 — 座標 (x, a, b)。w46 と同じ x 側に、x̄ 側だけ a と b が揃う重みを置く -/

def w173 : Bool → Bool → Bool → ℚ
  | true, _, _ => 1
  | false, true, true => 2
  | false, false, false => 2
  | false, _, _ => 0

/-- **ch14-173**: {a^{xh}b^{xh}c …} と {a^{x′h}b^{x′h}c …} は x′ ≡ x̄ のときでも関係しない:
二つのモデルで {a^{xh}b^{xh}} = 1 は同じだが {a^{x̄h}b^{x̄h}} は 1 と 2。 -/
theorem coefficients_unrelated :
    C w46 P23 P1 / (C w46 P2 P1 * C w46 P3 P1) = 1 ∧
      C w173 P23 P1 / (C w173 P2 P1 * C w173 P3 P1) = 1 ∧
      C w46 P23 N1 / (C w46 P2 N1 * C w46 P3 N1) = 1 ∧
      C w173 P23 N1 / (C w173 P2 N1 * C w173 P3 N1) = 2 := by
  norm_num [C, M, w46, w173, Fintype.sum_bool, P1, N1, P2, P3, P23]

end Ch14Models

/-! ## 監査クエリ

行定理 (th_14_rNNN) は台帳 ch14.md の行 ID ch14-NNN に対応する。✎ の行は _cor (修正形) と
Ch14Models の printed_… (印刷形の反例) の組。注目点:
  * 代入原理 (subst_taut) を使う行は ax_iii_taut と cons_of_pos (補完律 (1) の証明経由) を含む。
  * def_VIII_i を含むのは th_13_13_conj_i 経由の ch14-038 のみ (他は th_12_i_short 経由)。
  * Ch14Models の定理は KeynesI の公理を含まない (ℚ の計算のみ)。 -/

#print axioms KeynesI.th_14_r002
#print axioms KeynesI.th_14_r003
#print axioms KeynesI.th_14_r004
#print axioms KeynesI.th_14_r005
#print axioms KeynesI.th_14_r006
#print axioms KeynesI.th_14_r012
#print axioms KeynesI.th_14_r013
#print axioms KeynesI.th_14_r015
#print axioms KeynesI.th_14_r025
#print axioms KeynesI.th_14_r027
#print axioms KeynesI.th_14_r028
#print axioms KeynesI.th_14_r029
#print axioms KeynesI.th_14_r030
#print axioms KeynesI.th_14_r031
#print axioms KeynesI.th_14_r032
#print axioms KeynesI.th_14_r033
#print axioms KeynesI.th_14_r034
#print axioms KeynesI.th_14_r037
#print axioms KeynesI.th_14_r038
#print axioms KeynesI.th_14_r042
#print axioms KeynesI.th_14_r043
#print axioms KeynesI.th_14_r049
#print axioms KeynesI.th_14_r050
#print axioms KeynesI.th_14_r055
#print axioms KeynesI.th_14_r056
#print axioms KeynesI.th_14_r057
#print axioms KeynesI.th_14_r061
#print axioms KeynesI.th_14_r062
#print axioms KeynesI.th_14_r060
#print axioms KeynesI.th_14_r064
#print axioms KeynesI.th_14_r067
#print axioms KeynesI.th_14_r070
#print axioms KeynesI.th_14_r071
#print axioms KeynesI.th_14_r072
#print axioms KeynesI.th_14_r073
#print axioms KeynesI.th_14_r074
#print axioms KeynesI.th_14_r075
#print axioms KeynesI.th_14_r078
#print axioms KeynesI.th_14_r082
#print axioms KeynesI.th_14_r083
#print axioms KeynesI.th_14_r084
#print axioms KeynesI.th_14_r085
#print axioms KeynesI.th_14_r086
#print axioms KeynesI.th_14_r088
#print axioms KeynesI.th_14_r091_rhs_one
#print axioms KeynesI.th_14_r091_printed_iff
#print axioms KeynesI.th_14_r091_cor
#print axioms KeynesI.th_14_r093
#print axioms KeynesI.th_14_r096
#print axioms KeynesI.th_14_r098
#print axioms KeynesI.th_14_r101
#print axioms KeynesI.th_14_r103
#print axioms KeynesI.th_14_r104
#print axioms KeynesI.th_14_r105
#print axioms KeynesI.th_14_r114
#print axioms KeynesI.th_14_r116
#print axioms KeynesI.th_14_r120
#print axioms KeynesI.th_14_r122
#print axioms KeynesI.th_14_r124
#print axioms KeynesI.th_14_r131
#print axioms KeynesI.th_14_r134
#print axioms KeynesI.th_14_r138
#print axioms KeynesI.th_14_r139
#print axioms KeynesI.th_14_r142
#print axioms KeynesI.th_14_r144
#print axioms KeynesI.th_14_r148
#print axioms KeynesI.th_14_r149
#print axioms KeynesI.th_14_r150
#print axioms KeynesI.th_14_r152
#print axioms KeynesI.th_14_r153
#print axioms KeynesI.th_14_r154
#print axioms KeynesI.th_14_r158
#print axioms KeynesI.th_14_r160
#print axioms KeynesI.th_14_r162_cor
#print axioms KeynesI.th_14_r162_printed_iff
#print axioms KeynesI.th_14_r165
#print axioms KeynesI.th_14_r167
#print axioms KeynesI.th_14_r168
#print axioms KeynesI.th_14_r170
#print axioms KeynesI.th_14_r171
#print axioms KeynesI.th_14_r174
#print axioms KeynesI.th_14_r175
#print axioms KeynesI.th_14_r180
#print axioms KeynesI.th_14_r179_cor
#print axioms KeynesI.th_14_r178_cor
#print axioms KeynesI.th_14_r183
#print axioms KeynesI.th_14_r184
#print axioms KeynesI.th_14_r186
#print axioms KeynesI.th_14_r190
#print axioms KeynesI.th_14_r195
#print axioms KeynesI.th_14_r196
#print axioms KeynesI.th_14_r197
#print axioms KeynesI.th_14_r198
#print axioms KeynesI.th_14_r199_cor
#print axioms KeynesI.th_14_r203
#print axioms KeynesI.th_14_r205
#print axioms KeynesI.th_14_r207
#print axioms KeynesI.th_14_r208
#print axioms KeynesI.th_14_r210
#print axioms KeynesI.th_14_r213
#print axioms KeynesI.th_14_r222
#print axioms KeynesI.th_14_r223
#print axioms KeynesI.th_14_r224
#print axioms KeynesI.th_14_r225
#print axioms KeynesI.th_14_r227
#print axioms KeynesI.th_14_r228
#print axioms KeynesI.th_14_r230
#print axioms KeynesI.th_14_r231
#print axioms Ch14Models.printed_34_false
#print axioms Ch14Models.corrected_34_holds
#print axioms Ch14Models.hyp_49_hold
#print axioms Ch14Models.printed_49_line4_false
#print axioms Ch14Models.corrected_49_line4_holds
#print axioms Ch14Models.coef_unity_46
#print axioms Ch14Models.simplified_46_fails
#print axioms Ch14Models.printed_46_2_false
#print axioms Ch14Models.corrected_46_2_holds
#print axioms Ch14Models.printed_46_2_prop_false
#print axioms Ch14Models.printed_46_line2_false
#print axioms Ch14Models.corrected_46_line2_holds
#print axioms Ch14Models.coefficients_unrelated
