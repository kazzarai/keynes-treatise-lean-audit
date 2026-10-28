/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 10b
#
# 第13章 (The Fundamental Theorems of Necessary Inference, folio 139–143) の
# 証明途中行を 1 行ずつ定理にする。対象は docs/全数台帳/ch13.md で Lean 欄が
# 「未」だった式行 111 本 (行 ID は各定理の docstring に書く)。
#
# ## 担体
#   phase6c (B09 修復後) の内包的担体 KeynesI をそのまま写す: IProp・PrI・Cons、
#   Def. IX・X (左右)・XI、範囲、Def. VIII (双条件、但し書き付き) と印刷どおりの
#   片向き版、公理 (iii) の深い埋め込み (Form/evalB/Taut/interp, ax_iii_taut)、
#   整合性の公理 4 本。新しい公理は置かない。`Prop → Prop → ℝ` 型の Pr も置かない。
#
# ## 読み方 (行ごとの定理の書き方)
#   1. 各行は「その段で成り立つ関係」として 1 本の定理にする。仮定は、その行の
#      直前で本文が得ている関係 (前の行・言明の前件) と、公理 (i) の但し書き
#      (`Cons h` = 「h は矛盾する連言でない」) だけを置く。
#   2. 「A unless B」は選言 `A ∨ B` で書く。印刷の `>` はそのまま `>` で書く。
#   3. 前提 (premiss) は IProp の項なので、前提側の連言の順序や前提の置換 (公理
#      (ii)) は本公理系にない。印刷の前提 a, h₁, h₂ がそのまま項として書ける行
#      (例: (13) の a/a = aa/a、(15) の h/h₂) は印刷どおりに、背景を共有しないと
#      つながらない行は phase6b/7c と同じく背景 h を足した形 (a/h₁ を a/(h₁ ∧ h))
#      で書く。前者は台帳で ✓、後者と連言の順序が違う行は ≈。
#   4. 前提の連言の順序が行と行の間で入れ替わる継ぎ目 ((14)・(15)・(21)) は、
#      各行の定理はそれぞれ成り立つが、前の行の結論を次の行の仮定にそのまま
#      渡せない。継ぎ目は各定理の docstring に記す。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase10b.lean
-/

import Mathlib

namespace KeynesI

/-! ## 内包的担体と公理群 (phase6c と同一) -/

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

/-- Def. VIII 双条件読み、但し書き付き (phase6c と同一)。 -/
axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- Def. VIII 印刷どおり (→ のみ、phase6c と同一)。 -/
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

/-- 公理 (iii) の本体、但し書き付き (phase6c と同一)。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

axiom cons_true : Cons itrue
/-- Def. VI 印刷の向きの対偶 (folio 134)。 -/
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0
/-- Def. VI の逆向き ((10) folio 140 の用法)。 -/
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## 補助定理 (phase6c の再掲と、行の証明に使う一般形) -/

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

/-- (1) a/h + ā/h = 1 (phase6c の th_13_1_i の再掲)。 -/
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

/-- (12) の短い証明 (phase6c の th_12_i_short の再掲): (a≡b)/h = 1 ならば a/h = b/h。 -/
theorem eq_of_cert_iff (a b h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1) :
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

/-- 認証代入: 恒真な ↔ の両辺の解釈は、整合な前提の下で確率が等しい。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  eq_of_cert_iff _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-- 結論側の連言の可換: ab/h = ba/h (公理 (iii) と (12))。 -/
theorem conj_comm_i (p q h : IProp) (hc : Cons h) :
    PrI (iand p q) h = PrI (iand q p) h :=
  subst_taut (Form.conj (Form.var 0) (Form.var 1)) (Form.conj (Form.var 1) (Form.var 0))
    (fun n => match n with | 0 => p | _ => q) h hc
    (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])

/-- pq/h ≤ p/h (Def. IX と範囲)。 -/
theorem conj_le_left_i (p q h : IProp) : PrI (iand p q) h ≤ PrI p h := by
  have e := def_IX_i p q h
  have l := ax_range_lo_i (iand p (inot q)) h
  linarith

/-- pq/h ≤ q/h。 -/
theorem conj_le_right_i (p q h : IProp) (hc : Cons h) : PrI (iand p q) h ≤ PrI q h := by
  rw [conj_comm_i p q h hc]
  exact conj_le_left_i q p h

/-- f ∧ ¬g が恒偽ならば f/h ≤ g/h。 -/
theorem le_of_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.neg (Form.conj f (Form.neg g)))) :
    PrI (interp env f) h ≤ PrI (interp env g) h := by
  have e := def_IX_i (interp env f) (interp env g) h
  have z : PrI (iand (interp env f) (inot (interp env g))) h = 0 :=
    taut_neg_zero (Form.conj f (Form.neg g)) env h hc ht
  have le := conj_le_right_i (interp env f) (interp env g) h hc
  linarith

/-- b/h = 1 ならば x/bh = x/h ((1) の証明の「bh ≡ h … by (ii.)」の一歩を、
Def. IX・X と (1) で行う)。 -/
theorem prem_drop_cert (x b h : IProp) (hc : Cons h) (hb : PrI b h = 1) :
    PrI x (iand b h) = PrI x h := by
  have hx := def_X_left_i x b h
  rw [hb, mul_one] at hx
  have hnb : PrI (inot b) h = 0 := by have := th_13_1_i b h hc; linarith
  have h9 := def_IX_i x b h
  have hle := conj_le_right_i x (inot b) h hc
  have hlo := ax_range_lo_i (iand x (inot b)) h
  linarith

/-- (13) の背景 h 付きの形: ah が整合ならば a/ah = 1 (Def. X 右形・公理 (iii)・Def. VI)。 -/
theorem self_cert (a h : IProp) (hc : Cons h) (hca : Cons (iand a h)) :
    PrI a (iand a h) = 1 := by
  have hx := def_X_right_i a a h
  have e : PrI (iand a a) h = PrI a h :=
    subst_taut (Form.conj (Form.var 0) (Form.var 0)) (Form.var 0) (fun _ => a) h hc
      (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have ha := cons_of_pos_src a h hca
  rw [e] at hx
  have h2 : PrI a (iand a h) * PrI a h = 1 * PrI a h := by linarith
  exact mul_right_cancel₀ ha h2

/-- E/h = 1 かつ F/h = 1 ならば EF/h = 1。 -/
theorem conj_cert (E F h : IProp) (hc : Cons h) (hE : PrI E h = 1) (hF : PrI F h = 1) :
    PrI (iand E F) h = 1 := by
  have e := def_IX_i E F h
  have hnF : PrI (inot F) h = 0 := by have := th_13_1_i F h hc; linarith
  have le := conj_le_right_i E (inot F) h hc
  have lo := ax_range_lo_i (iand E (inot F)) h
  linarith

/-! ### 文脈への代入 (「principle of equivalence」、folio 141)

命題論理の文脈 f の変数 0 を a または b、変数 n+1 を ctx n と読む。 -/

def envAt (x : IProp) (ctx : ℕ → IProp) : ℕ → IProp
  | 0 => x
  | n + 1 => ctx n

def env2 (a b : IProp) (ctx : ℕ → IProp) : ℕ → IProp
  | 0 => a
  | 1 => b
  | n + 2 => ctx n

/-- 文脈の変数 0 をそのまま、変数 n+1 を n+2 に移す。 -/
def slotA : Form → Form
  | .var 0 => .var 0
  | .var (n + 1) => .var (n + 2)
  | .tru => .tru
  | .fls => .fls
  | .conj f g => .conj (slotA f) (slotA g)
  | .disj f g => .disj (slotA f) (slotA g)
  | .neg f => .neg (slotA f)
  | .iffF f g => .iffF (slotA f) (slotA g)

/-- 文脈の変数 0 を 1 に、変数 n+1 を n+2 に移す。 -/
def slotB : Form → Form
  | .var 0 => .var 1
  | .var (n + 1) => .var (n + 2)
  | .tru => .tru
  | .fls => .fls
  | .conj f g => .conj (slotB f) (slotB g)
  | .disj f g => .disj (slotB f) (slotB g)
  | .neg f => .neg (slotB f)
  | .iffF f g => .iffF (slotB f) (slotB g)

theorem interp_slotA (a b : IProp) (ctx : ℕ → IProp) (f : Form) :
    interp (env2 a b ctx) (slotA f) = interp (envAt a ctx) f := by
  induction f with
  | var n => cases n <;> rfl
  | tru => rfl
  | fls => rfl
  | conj f g ihf ihg => simp only [slotA, interp, ihf, ihg]
  | disj f g ihf ihg => simp only [slotA, interp, ihf, ihg]
  | neg f ih => simp only [slotA, interp, ih]
  | iffF f g ihf ihg => simp only [slotA, interp, ihf, ihg]

theorem interp_slotB (a b : IProp) (ctx : ℕ → IProp) (f : Form) :
    interp (env2 a b ctx) (slotB f) = interp (envAt b ctx) f := by
  induction f with
  | var n => cases n <;> rfl
  | tru => rfl
  | fls => rfl
  | conj f g ihf ihg => simp only [slotB, interp, ihf, ihg]
  | disj f g ihf ihg => simp only [slotB, interp, ihf, ihg]
  | neg f ih => simp only [slotB, interp, ih]
  | iffF f g ihf ihg => simp only [slotB, interp, ihf, ihg]

theorem eval_slot (v : ℕ → Bool) (hv : v 0 = v 1) (f : Form) :
    evalB v (slotA f) = evalB v (slotB f) := by
  induction f with
  | var n => cases n with
    | zero => simp only [slotA, slotB, evalB, hv]
    | succ n => rfl
  | tru => rfl
  | fls => rfl
  | conj f g ihf ihg => simp only [slotA, slotB, evalB, ihf, ihg]
  | disj f g ihf ihg => simp only [slotA, slotB, evalB, ihf, ihg]
  | neg f ih => simp only [slotA, slotB, evalB, ih]
  | iffF f g ihf ihg => simp only [slotA, slotB, evalB, ihf, ihg]

theorem taut_slot (f : Form) :
    Taut (Form.neg (Form.conj (Form.iffF (Form.var 0) (Form.var 1))
      (Form.neg (Form.iffF (slotA f) (slotB f))))) := by
  intro v
  by_cases hv : v 0 = v 1
  · simp [evalB, eval_slot v hv f]
  · simp [evalB, hv]

/-- (a≡b)/h = 1 ならば、文脈 f の中で a を b に替えた命題との同値も確実。 -/
theorem cert_ctx (a b h : IProp) (ctx : ℕ → IProp) (f : Form) (hc : Cons h)
    (hcert : PrI (iiff a b) h = 1) :
    PrI (iiff (interp (envAt a ctx) f) (interp (envAt b ctx) f)) h = 1 := by
  have hle := le_of_taut (Form.iffF (Form.var 0) (Form.var 1))
    (Form.iffF (slotA f) (slotB f)) (env2 a b ctx) h hc (taut_slot f)
  have e1 : interp (env2 a b ctx) (Form.iffF (Form.var 0) (Form.var 1)) = iiff a b := rfl
  have e2 : interp (env2 a b ctx) (Form.iffF (slotA f) (slotB f)) =
      iiff (interp (envAt a ctx) f) (interp (envAt b ctx) f) := by
    simp only [interp, interp_slotA, interp_slotB]
  rw [e1, e2, hcert] at hle
  exact le_antisymm (ax_range_hi_i _ _) hle

theorem subst_ctx (a b h : IProp) (ctx : ℕ → IProp) (f : Form) (hc : Cons h)
    (hcert : PrI (iiff a b) h = 1) :
    PrI (interp (envAt a ctx) f) h = PrI (interp (envAt b ctx) f) h :=
  eq_of_cert_iff _ _ h hc (cert_ctx a b h ctx f hc hcert)

/-- 前提側の置換: (a≡b)/h = 1 で ah が整合ならば x/ah = x/bh。公理 (ii) (folio 135)
の内容を、公理 (i) の但し書き (x/ah が存在する範囲) の下で Def. X と (12) から導く。 -/
theorem prem_subst (a b x h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1)
    (hca : Cons (iand a h)) : PrI x (iand a h) = PrI x (iand b h) := by
  have ha : PrI a h ≠ 0 := cons_of_pos_src a h hca
  have hab : PrI a h = PrI b h := eq_of_cert_iff a b h hc hcert
  have e : PrI (iand x a) h = PrI (iand x b) h :=
    subst_ctx a b h (fun _ => x) (Form.conj (Form.var 1) (Form.var 0)) hc hcert
  rw [def_X_left_i x a h, def_X_left_i x b h, ← hab] at e
  exact mul_right_cancel₀ ha e

/-! ## (1) の証明 (folio 139) -/

/-- ch13-002 (folio 139): ab/h + āb/h = b/h — 「For … by IX.」 -/
theorem th_13_1_r002 (a b h : IProp) (hc : Cons h) :
    PrI (iand a b) h + PrI (iand (inot a) b) h = PrI b h := by
  have e := def_IX_i b a h
  rw [conj_comm_i b (inot a) h hc, conj_comm_i b a h hc] at e
  linarith

/-- ch13-003 (folio 139): a/bh . b/h + ā/bh . b/h = b/h — 「by X.」 -/
theorem th_13_1_r003 (a b h : IProp) (hc : Cons h) :
    PrI a (iand b h) * PrI b h + PrI (inot a) (iand b h) * PrI b h = PrI b h := by
  rw [← def_X_left_i a b h, ← def_X_left_i (inot a) b h]
  exact th_13_1_r002 a b h hc

/-- ch13-004 (folio 139): Put b/h = 1, then a/bh + ā/bh = 1 — 「by (iv. b)」。 -/
theorem th_13_1_r004 (a b h : IProp) (hc : Cons h) (hb : PrI b h = 1) :
    PrI a (iand b h) + PrI (inot a) (iand b h) = 1 := by
  have e := th_13_1_r003 a b h hc
  simp only [hb, mul_one] at e
  exact e

/-- ch13-005 (folio 139): since b/h = 1, bh ≡ h — 「by (iii.)」。
等値 bh ≡ h を「h の下で (bh ≡ h) が確実」と読む。 -/
theorem th_13_1_r005 (b h : IProp) (hc : Cons h) (hb : PrI b h = 1) :
    PrI (iiff (iand b h) h) h = 1 := by
  have hnb : PrI (inot b) h = 0 := by have := th_13_1_i b h hc; linarith
  have hle : PrI (inot (iiff (iand b h) h)) h ≤ PrI (inot b) h :=
    le_of_taut (Form.neg (Form.iffF (Form.conj (Form.var 0) (Form.var 1)) (Form.var 1)))
      (Form.neg (Form.var 0)) (fun n => match n with | 0 => b | _ => h) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have hlo := ax_range_lo_i (inot (iiff (iand b h) h)) h
  have hcompl := th_13_1_i (iiff (iand b h) h) h hc
  linarith

/-- ch13-006 (folio 139): Thus a/h + ā/h = 1 — 「by (ii.)」。Keynes の経路どおり
b := ⊤ (確実な命題) とおき、ch13-004 の前提 ⊤h を h に戻す (prem_drop_cert)。 -/
theorem th_13_1_r006 (a h : IProp) (hc : Cons h) : PrI a h + PrI (inot a) h = 1 := by
  have e := th_13_1_r004 a itrue h hc (itrue_certain h hc)
  rw [prem_drop_cert a itrue h hc (itrue_certain h hc),
    prem_drop_cert (inot a) itrue h hc (itrue_certain h hc)] at e
  exact e

/-! ## (1.1)–(1.4) (folio 139) -/

/-- ch13-007, ch13-008 (folio 139): (1.1) If a/h = 1, ā/h = 0。 -/
theorem th_13_1_1 (a h : IProp) (hc : Cons h) (h1 : PrI a h = 1) : PrI (inot a) h = 0 := by
  have := th_13_1_i a h hc
  linarith

/-- ch13-009 (folio 139): a/h + ā/h = 1 — 「by (1),」。 -/
theorem th_13_1_1_r009 (a h : IProp) (hc : Cons h) : PrI a h + PrI (inot a) h = 1 :=
  th_13_1_i a h hc

/-- ch13-010 (folio 139): ∴ a/h + ā/h = a/h = a/h + 0 — 「by (iv. b),」(連鎖の二つの等号)。 -/
theorem th_13_1_1_r010 (a h : IProp) (hc : Cons h) (h1 : PrI a h = 1) :
    PrI a h + PrI (inot a) h = PrI a h ∧ PrI a h = PrI a h + 0 := by
  have := th_13_1_i a h hc
  constructor
  · linarith
  · ring

/-- ch13-011 (folio 139): ∴ ā/h = 0 — 「by (iv. c).」 -/
theorem th_13_1_1_r011 (a h : IProp) (hc : Cons h) (h1 : PrI a h = 1) :
    PrI (inot a) h = 0 := by
  have := (th_13_1_1_r010 a h hc h1).1
  linarith

/-- ch13-012, ch13-013 (folio 139): (1.2) Similarly, if ā/h = 1, a/h = 0。 -/
theorem th_13_1_2 (a h : IProp) (hc : Cons h) (h1 : PrI (inot a) h = 1) : PrI a h = 0 := by
  have := th_13_1_i a h hc
  linarith

/-- ch13-014, ch13-015 (folio 139): (1.3) If a/h = 0, ā/h = 1。 -/
theorem th_13_1_3 (a h : IProp) (hc : Cons h) (h0 : PrI a h = 0) : PrI (inot a) h = 1 := by
  have := th_13_1_i a h hc
  linarith

/-- ch13-016 (folio 139): a/h + ā/h = 1 — 「by (1),」((1.3) の証明内)。 -/
theorem th_13_1_3_r016 (a h : IProp) (hc : Cons h) : PrI a h + PrI (inot a) h = 1 :=
  th_13_1_i a h hc

/-- ch13-017 (folio 139): ∴ 0 + ā/h = 0 + 1 — 「by (iv. b),」。 -/
theorem th_13_1_3_r017 (a h : IProp) (hc : Cons h) (h0 : PrI a h = 0) :
    0 + PrI (inot a) h = 0 + 1 := by
  have := th_13_1_i a h hc
  rw [h0] at this
  linarith

/-- ch13-018 (folio 139): ∴ ā/h = 1 — 「by (iv. c).」 -/
theorem th_13_1_3_r018 (a h : IProp) (hc : Cons h) (h0 : PrI a h = 0) :
    PrI (inot a) h = 1 := by
  have := th_13_1_3_r017 a h hc h0
  linarith

/-- ch13-019, ch13-020 (folio 139): (1.4) Similarly, if ā/h = 0, a/h = 1。 -/
theorem th_13_1_4 (a h : IProp) (hc : Cons h) (h0 : PrI (inot a) h = 0) : PrI a h = 1 := by
  have := th_13_1_i a h hc
  linarith

/-! ## (5)–(7) の証明 (folio 140)

P, Q は確率関係 (relations of probability)。P := α/h、Q := β/k と書く。 -/

/-- ch13-027 (folio 140): P + Q > P unless Q = 0 — 「by (iv. b),」。 -/
theorem th_13_5_r027 (α β h k : IProp) :
    PrI α h + PrI β k > PrI α h ∨ PrI β k = 0 := by
  rcases (ax_range_lo_i β k).lt_or_eq with hq | hq
  · left; linarith
  · right; exact hq.symm

/-- ch13-028 (folio 140): P > 0 unless P = 0 — 「by V.」 -/
theorem th_13_5_r028 (α h : IProp) : PrI α h > 0 ∨ PrI α h = 0 := by
  rcases (ax_range_lo_i α h).lt_or_eq with hp | hp
  · left; exact hp
  · right; exact hp.symm

/-- ch13-029 (folio 140): ∴ P + Q > 0 unless Q = 0。 -/
theorem th_13_5_r029 (α β h k : IProp) :
    PrI α h + PrI β k > 0 ∨ PrI β k = 0 := by
  rcases (ax_range_lo_i β k).lt_or_eq with hq | hq
  · left; have := ax_range_lo_i α h; linarith
  · right; exact hq.symm

/-- ch13-030, ch13-031 (folio 140): Hence, if P + Q = 0, Q = 0。 -/
theorem th_13_5_r031 (α β h k : IProp) (hs : PrI α h + PrI β k = 0) : PrI β k = 0 := by
  rcases th_13_5_r029 α β h k with hp | hq
  · linarith
  · exact hq

/-- ch13-032 (folio 140): and similarly P = 0。 -/
theorem th_13_5_r032 (α β h k : IProp) (hs : PrI α h + PrI β k = 0) : PrI α h = 0 := by
  have := th_13_5_r031 α β h k hs
  linarith

/-- ch13-036 (folio 140): Q > 0 unless Q = 0 — 「by V.」 -/
theorem th_13_6_r036 (β k : IProp) : PrI β k > 0 ∨ PrI β k = 0 :=
  th_13_5_r028 β k

/-- ch13-037 (folio 140): PQ > P . 0 unless Q = 0 or P = 0 — 「by (iv. c),」。 -/
theorem th_13_6_r037 (α β h k : IProp) :
    PrI α h * PrI β k > PrI α h * 0 ∨ PrI β k = 0 ∨ PrI α h = 0 := by
  rcases (ax_range_lo_i β k).lt_or_eq with hq | hq
  · rcases (ax_range_lo_i α h).lt_or_eq with hp | hp
    · left; rw [mul_zero]; exact mul_pos hp hq
    · right; right; exact hp.symm
  · right; left; exact hq.symm

/-- ch13-038 (folio 140): i.e. PQ > 0 unless Q = 0 or P = 0 — 「by (iv. b).」 -/
theorem th_13_6_r038 (α β h k : IProp) :
    PrI α h * PrI β k > 0 ∨ PrI β k = 0 ∨ PrI α h = 0 := by
  have := th_13_6_r037 α β h k
  rwa [mul_zero] at this

/-- ch13-039 (folio 140): Whence, if PQ = 0, the result (P = 0 or Q = 0) follows。 -/
theorem th_13_6_r039 (α β h k : IProp) (hm : PrI α h * PrI β k = 0) :
    PrI α h = 0 ∨ PrI β k = 0 := by
  rcases th_13_6_r038 α β h k with hp | hq | hp
  · linarith
  · right; exact hq
  · left; exact hp

/-- ch13-043 (folio 140): PQ < P unless P = 0 or Q = 1 — 「by (iv. b),」。 -/
theorem th_13_7_r043 (α β h k : IProp) :
    PrI α h * PrI β k < PrI α h ∨ PrI α h = 0 ∨ PrI β k = 1 := by
  rcases (ax_range_lo_i α h).lt_or_eq with hp | hp
  · rcases (ax_range_hi_i β k).lt_or_eq with hq | hq
    · left; nlinarith [mul_pos hp (sub_pos.mpr hq)]
    · right; right; exact hq
  · right; left; exact hp.symm

/-- ch13-044 (folio 140): PQ = P if P = 0 or Q = 1 — 「by (iv. b),」。 -/
theorem th_13_7_r044 (α β h k : IProp) (hpq : PrI α h = 0 ∨ PrI β k = 1) :
    PrI α h * PrI β k = PrI α h := by
  rcases hpq with hp | hq
  · rw [hp, zero_mul]
  · rw [hq, mul_one]

/-- ch13-045 (folio 140): P < 1 unless P = 1 — 「by IV.,」。 -/
theorem th_13_7_r045 (α h : IProp) : PrI α h < 1 ∨ PrI α h = 1 :=
  (ax_range_hi_i α h).lt_or_eq

/-- ch13-046 (folio 140): ∴ PQ < 1 unless P = 1。 -/
theorem th_13_7_r046 (α β h k : IProp) : PrI α h * PrI β k < 1 ∨ PrI α h = 1 := by
  rcases th_13_7_r045 α h with hp | hp
  · left
    nlinarith [mul_le_mul_of_nonneg_left (ax_range_hi_i β k) (ax_range_lo_i α h)]
  · right; exact hp

/-- ch13-047 (folio 140): Hence P = 1 (PQ = 1 のとき)。 -/
theorem th_13_7_r047 (α β h k : IProp) (hm : PrI α h * PrI β k = 1) : PrI α h = 1 := by
  rcases th_13_7_r046 α β h k with hl | hp
  · linarith
  · exact hp

/-- ch13-048 (folio 140): similarly Q = 1。 -/
theorem th_13_7_r048 (α β h k : IProp) (hm : PrI α h * PrI β k = 1) : PrI β k = 1 := by
  have hm' : PrI β k * PrI α h = 1 := by rw [mul_comm]; exact hm
  exact th_13_7_r047 β α k h hm'

/-! ## (8)–(11) の証明 (folio 140–141) -/

/-- ch13-052 (folio 140): ab/h = b/ah . a/h = a/bh . b/h — 「by X.,」(連鎖)。 -/
theorem th_13_8_r052 (a b h : IProp) :
    PrI (iand a b) h = PrI b (iand a h) * PrI a h ∧
    PrI b (iand a h) * PrI a h = PrI a (iand b h) * PrI b h :=
  ⟨def_X_right_i a b h, by rw [← def_X_right_i a b h, def_X_left_i a b h]⟩

/-- ch13-053 (folio 140): since a/h = 0, b/ah . a/h = 0 — 「by (iv. b),」。 -/
theorem th_13_8_r053 (a b h : IProp) (h0 : PrI a h = 0) :
    PrI b (iand a h) * PrI a h = 0 := by
  rw [h0, mul_zero]

/-- ch13-054 (folio 140): ∴ ab/h = 0 and a/bh . b/h = 0。 -/
theorem th_13_8_r054 (a b h : IProp) (h0 : PrI a h = 0) :
    PrI (iand a b) h = 0 ∧ PrI a (iand b h) * PrI b h = 0 := by
  obtain ⟨e1, e2⟩ := th_13_8_r052 a b h
  have z := th_13_8_r053 a b h h0
  constructor
  · rw [e1, z]
  · rw [← e2, z]

/-- ch13-055 (folio 140): ∴ unless b/h = 0, a/bh = 0 — 「by (5),」(内容は (6) の積の場合)。 -/
theorem th_13_8_r055 (a b h : IProp) (h0 : PrI a h = 0) :
    PrI a (iand b h) = 0 ∨ PrI b h = 0 :=
  mul_eq_zero.mp (th_13_8_r054 a b h h0).2

/-- ch13-058 (folio 140): Since a/h = 1, ā/h = 0 — 「by (1.1),」。 -/
theorem th_13_9_r058 (a h : IProp) (hc : Cons h) (h1 : PrI a h = 1) : PrI (inot a) h = 0 :=
  th_13_1_1 a h hc h1

/-- ch13-059 (folio 140): ∴ ā/bh = 0 by (8) if bh is not inconsistent。 -/
theorem th_13_9_r059 (a b h : IProp) (hc : Cons h) (h1 : PrI a h = 1)
    (hcb : Cons (iand b h)) : PrI (inot a) (iand b h) = 0 := by
  have hb : PrI b h ≠ 0 := cons_of_pos_src b h hcb
  have hn := th_13_9_r058 a h hc h1
  have hx := def_X_left_i (inot a) b h
  have hle := conj_le_left_i (inot a) b h
  have hlo := ax_range_lo_i (iand (inot a) b) h
  have hz : PrI (iand (inot a) b) h = 0 := by linarith
  rw [hz] at hx
  rcases mul_eq_zero.mp hx.symm with h' | h'
  · exact h'
  · exact absurd h' hb

/-- ch13-060 (folio 140): whence a/bh = 1 — 「by (1.4).」 -/
theorem th_13_9_r060 (a b h : IProp) (hc : Cons h) (h1 : PrI a h = 1)
    (hcb : Cons (iand b h)) : PrI a (iand b h) = 1 :=
  th_13_1_4 a (iand b h) hcb (th_13_9_r059 a b h hc h1 hcb)

/-- ch13-063 (folio 140): ab/h = b/ah . a/h = a/bh . b/h — 「by X.」((10) の証明内)。 -/
theorem th_13_10_r063 (a b h : IProp) :
    PrI (iand a b) h = PrI b (iand a h) * PrI a h ∧
    PrI b (iand a h) * PrI a h = PrI a (iand b h) * PrI b h :=
  ⟨def_X_right_i a b h, by rw [← def_X_right_i a b h, def_X_left_i a b h]⟩

/-- ch13-064, ch13-065, ch13-066 (folio 140): Since a/h = 1, a/bh = 1 by (9) unless
b/h = 0。(9) の但し書き「bh が不整合でない」を b/h ≠ 0 から得る (cons_of_pos)。 -/
theorem th_13_10_r065 (a b h : IProp) (hc : Cons h) (h1 : PrI a h = 1) :
    PrI a (iand b h) = 1 ∨ PrI b h = 0 := by
  by_cases hb : PrI b h = 0
  · right; exact hb
  · left; exact th_13_9_r060 a b h hc h1 (cons_of_pos b h hb hc)

/-- ch13-067 (folio 140): ∴ b/ah . a/h = b/ah and a/bh . b/h = b/h — 「by (iv. b),」。
b/h = 0 のときは第 2 式の両辺が 0 なので、例外なしで成り立つ。 -/
theorem th_13_10_r067 (a b h : IProp) (hc : Cons h) (h1 : PrI a h = 1) :
    PrI b (iand a h) * PrI a h = PrI b (iand a h) ∧
    PrI a (iand b h) * PrI b h = PrI b h := by
  constructor
  · rw [h1, mul_one]
  · rcases th_13_10_r065 a b h hc h1 with ha | hb
    · rw [ha, one_mul]
    · rw [hb, mul_zero]

/-- ch13-068 (folio 140): whence the result (ab/h = b/ah = b/h), unless b/h = 0。 -/
theorem th_13_10_r068 (a b h : IProp) (hc : Cons h) (h1 : PrI a h = 1) :
    (PrI (iand a b) h = PrI b (iand a h) ∧ PrI b (iand a h) = PrI b h) ∨ PrI b h = 0 := by
  left
  obtain ⟨e1, e2⟩ := th_13_10_r063 a b h
  obtain ⟨f1, f2⟩ := th_13_10_r067 a b h hc h1
  constructor
  · rw [e1, f1]
  · rw [← f1, e2, f2]

/-- ch13-069 (folio 141): If b/h = 0, the result follows from (8)。 -/
theorem th_13_10_r069 (a b h : IProp) (h1 : PrI a h = 1) (h0 : PrI b h = 0) :
    PrI (iand a b) h = PrI b (iand a h) ∧ PrI b (iand a h) = PrI b h := by
  have hz : PrI (iand a b) h = 0 := by
    rw [def_X_left_i a b h, h0, mul_zero]
  have hx := def_X_right_i a b h
  rw [h1, mul_one] at hx
  constructor
  · exact hx
  · rw [← hx, hz, h0]

/-- ch13-072 (folio 141): ab/h = b/ah . a/h — 「For … by X.,」。 -/
theorem th_13_11_r072 (a b h : IProp) :
    PrI (iand a b) h = PrI b (iand a h) * PrI a h :=
  def_X_right_i a b h

/-- ch13-073 (folio 141): ∴ a/h = 1 — 「by (7).」(ab/h = 1 のとき)。 -/
theorem th_13_11_r073 (a b h : IProp) (h1 : PrI (iand a b) h = 1) : PrI a h = 1 := by
  rw [th_13_11_r072 a b h] at h1
  exact th_13_7_r048 b a (iand a h) h h1

/-! ## (12)・(12.1)・principle of equivalence (folio 141) -/

/-- ch13-076 (folio 141): b/ah . a/h = a/bh . b/h — 「by X.」 -/
theorem th_13_12_r076 (a b h : IProp) :
    PrI b (iand a h) * PrI a h = PrI a (iand b h) * PrI b h := by
  rw [← def_X_right_i a b h, def_X_left_i a b h]

/-- ch13-077 (folio 141): b/ah = 1, a/bh = 1 — 「by VIII.,」(Def. VIII を逆向きに使う)。
b/ah, a/bh が存在する範囲 (ah, bh が整合) を但し書きに置く (公理 (i))。 -/
theorem th_13_12_r077 (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h))
    (hcert : PrI (iiff a b) h = 1) :
    PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1 :=
  (def_VIII_i a b h hca hcb).mp hcert

/-- ch13-078 (folio 141): ∴ a/h = b/h — 「by (iv. b).」
ah, bh が整合な場合は ch13-076・077 (Keynes の経路)、a/h = 0 または b/h = 0 の
場合は Def. IX・X と (1) で閉じる。 -/
theorem th_13_12_r078 (a b h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1) :
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
  by_cases ha : PrI a h = 0
  · have s := def_IX_i b a h
    have x := def_X_left_i b a h
    rw [ha, mul_zero] at x
    linarith
  by_cases hb : PrI b h = 0
  · have s := def_IX_i a b h
    have x := def_X_left_i a b h
    rw [hb, mul_zero] at x
    linarith
  have hca : Cons (iand a h) := cons_of_pos a h ha hc
  have hcb : Cons (iand b h) := cons_of_pos b h hb hc
  obtain ⟨hba', hab'⟩ := th_13_12_r077 a b h hca hcb hcert
  have e := th_13_12_r076 a b h
  rw [hba', hab', one_mul, one_mul] at e
  exact e

/-- ch13-081 (folio 141): a/hx . x/h = x/ah . a/h (前提 hx を x ∧ h で)。 -/
theorem th_13_12_1_r081 (a x h : IProp) :
    PrI a (iand x h) * PrI x h = PrI x (iand a h) * PrI a h := by
  rw [← def_X_left_i a x h, def_X_right_i a x h]

/-- ch13-082 (folio 141): b/hx . x/h = x/bh . b/h — 「by X.,」(前提 hx を x ∧ h で)。 -/
theorem th_13_12_1_r082 (b x h : IProp) :
    PrI b (iand x h) * PrI x h = PrI x (iand b h) * PrI b h :=
  th_13_12_1_r081 b x h

/-- ch13-083 (folio 141): x/ah = x/bh — 「by (ii.),」。公理 (ii) の内容を、x/ah が
存在する範囲 (ah が整合、公理 (i)) で Def. X と (12) から導く。 -/
theorem th_13_12_1_r083 (a b x h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1)
    (hca : Cons (iand a h)) : PrI x (iand a h) = PrI x (iand b h) :=
  prem_subst a b x h hc hcert hca

/-- ch13-084 (folio 141): a/h = b/h — 「by (12),」。 -/
theorem th_13_12_1_r084 (a b h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h :=
  eq_of_cert_iff a b h hc hcert

/-- ch13-085 (folio 141): ∴ a/hx = b/hx unless x/h = 0 (前提 hx を x ∧ h で)。 -/
theorem th_13_12_1_r085 (a b x h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1) :
    PrI a (iand x h) = PrI b (iand x h) ∨ PrI x h = 0 := by
  by_cases hx : PrI x h = 0
  · right; exact hx
  · left
    have e : PrI (iand a x) h = PrI (iand b x) h :=
      subst_ctx a b h (fun _ => x) (Form.conj (Form.var 0) (Form.var 1)) hc hcert
    rw [def_X_left_i a x h, def_X_left_i b x h] at e
    exact mul_right_cancel₀ hx e

/-- ch13-086 (folio 141): if (a≡b)/h = 1, we can substitute a for b and vice versa,
wherever they occur in a probability whose premisses include h。
「wherever they occur」を命題論理の文脈 f (変数 0 が代入の位置、ほかは ctx) で書く。
結論側は無条件、前提側 (前提 f[a] ∧ h) は f[a] ∧ h が整合な範囲 (公理 (i))。 -/
theorem th_13_r086 (a b h : IProp) (ctx : ℕ → IProp) (f : Form) (hc : Cons h)
    (hcert : PrI (iiff a b) h = 1) :
    PrI (interp (envAt a ctx) f) h = PrI (interp (envAt b ctx) f) h ∧
    ∀ x : IProp, Cons (iand (interp (envAt a ctx) f) h) →
      PrI x (iand (interp (envAt a ctx) f) h) = PrI x (iand (interp (envAt b ctx) f) h) :=
  ⟨subst_ctx a b h ctx f hc hcert,
   fun x hca => prem_subst _ _ x h hc (cert_ctx a b h ctx f hc hcert) hca⟩

/-! ## (13) の証明 (folio 141) -/

/-- ch13-088 (folio 141): a/a = aa/a = a/aa . a/a — 「by (iii.), (12), and X.,」(連鎖)。
前提 a そのもので書く。「a が不整合でない」を Cons a で置く。 -/
theorem th_13_13_r088 (a : IProp) (hca : Cons a) :
    PrI a a = PrI (iand a a) a ∧ PrI (iand a a) a = PrI a (iand a a) * PrI a a :=
  ⟨subst_taut (Form.var 0) (Form.conj (Form.var 0) (Form.var 0)) (fun _ => a) a hca
    (by intro v; cases h0 : v 0 <;> simp [evalB, h0]),
   def_X_left_i a a a⟩

/-- ch13-089 (folio 141): whence a/aa = 1 by (ii.), unless a/a = 0。 -/
theorem th_13_13_r089 (a : IProp) (hca : Cons a) :
    PrI a (iand a a) = 1 ∨ PrI a a = 0 := by
  obtain ⟨e1, e2⟩ := th_13_13_r088 a hca
  by_cases h0 : PrI a a = 0
  · right; exact h0
  · left
    have h2 : PrI a (iand a a) * PrI a a = 1 * PrI a a := by linarith
    exact mul_right_cancel₀ h0 h2

/-- ch13-090 (folio 141): 例外 a/a = 0 は a が不整合のときに限る
(「unless a is inconsistent by … VI.」: aa ≡ a ゆえ aa も整合、Def. VI)。 -/
theorem th_13_13_r090 (a : IProp) (h0 : PrI a a = 0) : ¬ Cons a := by
  intro hca
  have hcaa : Cons (iand a a) :=
    (cons_iff_taut (Form.conj (Form.var 0) (Form.var 0)) (Form.var 0) (fun _ => a)
      (by intro v; cases h0 : v 0 <;> simp [evalB, h0])).mpr hca
  exact cons_of_pos_src a a hcaa h0

/-- ch13-091 (folio 141): i.e. a/a = 1, unless a is inconsistent。背景 h を足した形
a/ah で書く (前提 a そのものの形は、ch13-089 の a/aa から前提を aa から a に戻す
置換 (公理 (ii)) を要し、本公理系では導いていない)。 -/
theorem th_13_13_r091 (a h : IProp) (hc : Cons h) (hca : Cons (iand a h)) :
    PrI a (iand a h) = 1 :=
  self_cert a h hc hca

/-! ## (14) の証明 (folio 141)

f は「a と b に共通の仮定の群で、全ての群に含まれるとしたもの」。散文の条件
「f は a と b の前提に含まれる」を f/a = 1, f/b = 1 で書く。継ぎ目: ch13-096・098・101
は前提 f ∧ b (Def. X を背景 b で使う形)、ch13-097・100 は前提 b ∧ f (Def. X を
背景 f で使う形)。両者を結ぶには前提の連言の可換が要り、本公理系にはない。 -/

/-- ch13-096 (folio 141): a/b = a/bf and b/a = b/af — 「by (iii.) and (12),」。 -/
theorem th_13_14_r096 (a b f : IProp) (ha : Cons a) (hb : Cons b)
    (hfa : PrI f a = 1) (hfb : PrI f b = 1) :
    PrI a b = PrI a (iand f b) ∧ PrI b a = PrI b (iand f a) :=
  ⟨(prem_drop_cert a f b hb hfb).symm, (prem_drop_cert b f a ha hfa).symm⟩

/-- ch13-097 (folio 141): a/bf . b/f = b/af . a/f — 「by X.」 -/
theorem th_13_14_r097 (a b f : IProp) :
    PrI a (iand b f) * PrI b f = PrI b (iand a f) * PrI a f := by
  rw [← def_X_left_i a b f, def_X_right_i a b f]

/-- ch13-098 (folio 141): a/bf = 0 by hypothesis (a/b = 0 と ch13-096)。 -/
theorem th_13_14_r098 (a b f : IProp) (hb : Cons b) (hfb : PrI f b = 1)
    (h0 : PrI a b = 0) : PrI a (iand f b) = 0 := by
  rw [prem_drop_cert a f b hb hfb]
  exact h0

/-- ch13-099 (folio 141): a/f ≠ 0, since a is not inconsistent (Def. VI の対偶)。 -/
theorem th_13_14_r099 (a f : IProp) (hcaf : Cons (iand a f)) : PrI a f ≠ 0 :=
  cons_of_pos_src a f hcaf

/-- ch13-100 (folio 141): ∴ b/af = 0。 -/
theorem th_13_14_r100 (a b f : IProp) (h0 : PrI a (iand b f) = 0) (hcaf : Cons (iand a f)) :
    PrI b (iand a f) = 0 := by
  have e := th_13_14_r097 a b f
  rw [h0, zero_mul] at e
  rcases mul_eq_zero.mp e.symm with h' | h'
  · exact h'
  · exact absurd h' (th_13_14_r099 a f hcaf)

/-- ch13-101 (folio 141): whence b/a = 0 (ch13-096 の第 2 式で前提を af から a に戻す)。 -/
theorem th_13_14_r101 (a b f : IProp) (ha : Cons a) (hfa : PrI f a = 1)
    (h0 : PrI b (iand f a) = 0) : PrI b a = 0 := by
  rw [← prem_drop_cert b f a ha hfa]
  exact h0

/-! ## (15) の証明 (folio 141–142)

印刷の前提 h₂, h をそのまま項として書く。継ぎ目: ch13-106 で (8) が与えるのは
h₁/(h ∧ h₂)、ch13-104・108 の Def. X が要るのは h₁/(h₂ ∧ h)。 -/

/-- ch13-104 (folio 141): h₁h₂/h = h₁/h₂h . h₂/h — 「by II.,」(内容は Def. X)。 -/
theorem th_13_15_r104 (h₁ h₂ h : IProp) :
    PrI (iand h₁ h₂) h = PrI h₁ (iand h₂ h) * PrI h₂ h :=
  def_X_left_i h₁ h₂ h

/-- ch13-105, ch13-106, ch13-107 (folio 141): since h₁/h₂ = 0, h₁/h₂h = 0 by (8),
unless h/h₂ = 0。(8) が与える前提の連言は h ∧ h₂ (背景 h₂ に h を足す)。 -/
theorem th_13_15_r106 (h₁ h₂ h : IProp) (h0 : PrI h₁ h₂ = 0) :
    PrI h₁ (iand h h₂) = 0 ∨ PrI h h₂ = 0 := by
  have hz : PrI (iand h₁ h) h₂ = 0 :=
    le_antisymm (by have := conj_le_left_i h₁ h h₂; linarith) (ax_range_lo_i _ _)
  rw [def_X_left_i] at hz
  exact mul_eq_zero.mp hz

/-- ch13-108 (folio 141): whence the result by (iv. b), unless h/h₂ = 0。
ch13-104 の積 (前提 h₂ ∧ h) から。 -/
theorem th_13_15_r108 (h₁ h₂ h : IProp)
    (hd : PrI h₁ (iand h₂ h) = 0 ∨ PrI h h₂ = 0) :
    PrI (iand h₁ h₂) h = 0 ∨ PrI h h₂ = 0 := by
  rcases hd with h0 | h0
  · left; rw [th_13_15_r104, h0, zero_mul]
  · right; exact h0

/-- ch13-109 (folio 142): If h/h₂ = 0, h₂/h = 0 by (14), since h is not inconsistent。
(14) を phase6b と同じく共通の背景 k を足した形で使う (h/h₂ を h/(h₂ ∧ k))。 -/
theorem th_13_15_r109 (h₂ h k : IProp) (h0 : PrI h (iand h₂ k) = 0)
    (hchk : Cons (iand h k)) : PrI h₂ (iand h k) = 0 := by
  have hl := def_X_left_i h h₂ k
  have hr := def_X_right_i h h₂ k
  rw [h0, zero_mul] at hl
  rw [hl] at hr
  rcases mul_eq_zero.mp hr.symm with h' | h'
  · exact h'
  · exact absurd h' (cons_of_pos_src h k hchk)

/-- ch13-110 (folio 142): and hence h₁h₂/h = 0 — 「by (8).」(h₂/h = 0 のとき)。 -/
theorem th_13_15_r110 (h₁ h₂ h : IProp) (h0 : PrI h₂ h = 0) :
    PrI (iand h₁ h₂) h = 0 := by
  rw [th_13_15_r104, h0, mul_zero]

/-! ## (16)・(16.2)・群 (folio 142)

(16) は言明の Lean (7c/th_13_16) と同じく h₁/h₂ を h₁/(h₂ ∧ h) で書く。 -/

/-- ch13-115 (folio 142): h̄₁/h₂ = 0 — 「by (1),」(h₁/h₂ = 1 のとき)。 -/
theorem th_13_16_r115 (h₁ h₂ h : IProp) (hc2 : Cons (iand h₂ h))
    (h1 : PrI h₁ (iand h₂ h) = 1) : PrI (inot h₁) (iand h₂ h) = 0 :=
  th_13_1_1 h₁ (iand h₂ h) hc2 h1

/-- ch13-116 (folio 142): ∴ h̄₁h₂/h = 0 — 「by (15),」。 -/
theorem th_13_16_r116 (h₁ h₂ h : IProp) (h0 : PrI (inot h₁) (iand h₂ h) = 0) :
    PrI (iand (inot h₁) h₂) h = 0 := by
  rw [def_X_left_i, h0, zero_mul]

/-- ch13-117 (folio 142): ∴ (h̄₁h₂ の上にバー)/h = 1 — 「by (1.3),」。 -/
theorem th_13_16_r117 (h₁ h₂ h : IProp) (hc : Cons h) (h0 : PrI (iand (inot h₁) h₂) h = 0) :
    PrI (inot (iand (inot h₁) h₂)) h = 1 :=
  th_13_1_3 _ h hc h0

/-- ch13-118 (folio 142): ∴ (h₁ + h̄₂)/h = 1 — 「by (12) and (iii.).」 -/
theorem th_13_16_r118 (h₁ h₂ h : IProp) (hc : Cons h)
    (h1 : PrI (inot (iand (inot h₁) h₂)) h = 1) : PrI (ior h₁ (inot h₂)) h = 1 := by
  have e : PrI (inot (iand (inot h₁) h₂)) h = PrI (ior h₁ (inot h₂)) h :=
    subst_taut (Form.neg (Form.conj (Form.neg (Form.var 0)) (Form.var 1)))
      (Form.disj (Form.var 0) (Form.neg (Form.var 1)))
      (fun n => match n with | 0 => h₁ | _ => h₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  rw [← e]
  exact h1

/-- ch13-124 (folio 142): h̄₁h₂/h = 0, as in (16) ((h₁ + h̄₂)/h = 1 のとき)。 -/
theorem th_13_16_2_r124 (h₁ h₂ h : IProp) (hc : Cons h)
    (hcert : PrI (ior h₁ (inot h₂)) h = 1) : PrI (iand (inot h₁) h₂) h = 0 := by
  have e : PrI (inot (iand (inot h₁) h₂)) h = PrI (ior h₁ (inot h₂)) h :=
    subst_taut (Form.neg (Form.conj (Form.neg (Form.var 0)) (Form.var 1)))
      (Form.disj (Form.var 0) (Form.neg (Form.var 1)))
      (fun n => match n with | 0 => h₁ | _ => h₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have hc' := th_13_1_i (iand (inot h₁) h₂) h hc
  linarith

/-- ch13-125 (folio 142): ∴ h̄₁/h₂h = 0 by (15.1), since h₂h is not inconsistent。 -/
theorem th_13_16_2_r125 (h₁ h₂ h : IProp) (hc2 : Cons (iand h₂ h))
    (h0 : PrI (iand (inot h₁) h₂) h = 0) : PrI (inot h₁) (iand h₂ h) = 0 := by
  rw [def_X_left_i] at h0
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact h'
  · exact absurd h' (cons_of_pos_src h₂ h hc2)

/-- ch13-126 (folio 142): ∴ h₁/h₂h = 1 — 「by (1.4).」 -/
theorem th_13_16_2_r126 (h₁ h₂ h : IProp) (hc2 : Cons (iand h₂ h))
    (h0 : PrI (inot h₁) (iand h₂ h) = 0) : PrI h₁ (iand h₂ h) = 1 :=
  th_13_1_4 h₁ (iand h₂ h) hc2 h0

/-- ch13-129 (folio 142): if h₂ ⊃ h₁ and h₂ belong to a group, then h₁ also belongs
to this group。「群 g に属する」を「g の下で確実」で、⊃ を (16.1) の書き換えどおり
h₁ + h̄₂ で書く。 -/
theorem th_13_r129 (h₁ h₂ g : IProp) (hcg : Cons g)
    (himp : PrI (ior h₁ (inot h₂)) g = 1) (hm : PrI h₂ g = 1) : PrI h₁ g = 1 := by
  have hcc := conj_cert h₂ (ior h₁ (inot h₂)) g hcg hm himp
  have le : PrI (iand h₂ (ior h₁ (inot h₂))) g ≤ PrI h₁ g :=
    le_of_taut (Form.conj (Form.var 1) (Form.disj (Form.var 0) (Form.neg (Form.var 1))))
      (Form.var 0) (fun n => match n with | 0 => h₁ | _ => h₂) g hcg
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  exact le_antisymm (ax_range_hi_i _ _) (by linarith)

/-! ## (18)–(20) の証明 (folio 142–143)

a/a・ā/ā は (13) と同じく背景 h を足した a/ah・ā/āh で書く。「a が不整合」は
「ah が整合でない」(¬ Cons (a ∧ h)) で書く。 -/

/-- ch13-134 (folio 142): a/a = 1, unless a is inconsistent — 「by (13).」 -/
theorem th_13_18_r134 (a h : IProp) (hc : Cons h) (hca : Cons (iand a h)) :
    PrI a (iand a h) = 1 :=
  self_cert a h hc hca

/-- ch13-135 (folio 142): If a is inconsistent, a/h = 0, where h is not inconsistent。 -/
theorem th_13_18_r135 (a h : IProp) (hc : Cons h) (hna : ¬ Cons (iand a h)) :
    PrI a h = 0 := by
  by_contra hne
  exact hna (cons_of_pos a h hne hc)

/-- ch13-136 (folio 142): therefore ā/h = 1 — 「by (1.3).」 -/
theorem th_13_18_r136 (a h : IProp) (hc : Cons h) (hna : ¬ Cons (iand a h)) :
    PrI (inot a) h = 1 :=
  th_13_1_3 a h hc (th_13_18_r135 a h hc hna)

/-- ch13-137 (folio 142): and therefore ā/ā = 1 — 「by (13).」(a が不整合のとき)。 -/
theorem th_13_18_r137 (a h : IProp) (hc : Cons h) (hna : ¬ Cons (iand a h)) :
    PrI (inot a) (iand (inot a) h) = 1 := by
  have h1 := th_13_18_r136 a h hc hna
  have hne : PrI (inot a) h ≠ 0 := by rw [h1]; norm_num
  exact self_cert (inot a) h hc (cons_of_pos (inot a) h hne hc)

/-- ch13-139 (folio 142): ā/ā = 1 or a/a = 1 — 「by (18),」。 -/
theorem th_13_19_r139 (a h : IProp) (hc : Cons h) :
    PrI (inot a) (iand (inot a) h) = 1 ∨ PrI a (iand a h) = 1 := by
  by_cases hca : Cons (iand a h)
  · right; exact th_13_18_r134 a h hc hca
  · left; exact th_13_18_r137 a h hc hca

/-- ch13-140 (folio 142): ∴ a/ā = 0 or ā/a = 0 — 「by (1.1) and (1.2).」 -/
theorem th_13_19_r140 (a h : IProp) (hc : Cons h) :
    PrI a (iand (inot a) h) = 0 ∨ PrI (inot a) (iand a h) = 0 := by
  by_cases hca : Cons (iand a h)
  · right; exact th_13_1_1 a (iand a h) hca (th_13_18_r134 a h hc hca)
  · left
    have h1 := th_13_18_r136 a h hc hca
    have hne : PrI (inot a) h ≠ 0 := by rw [h1]; norm_num
    have hcn := cons_of_pos (inot a) h hne hc
    exact th_13_1_2 a (iand (inot a) h) hcn (th_13_18_r137 a h hc hca)

/-- ch13-141 (folio 142): In either case aā/h = 0 — 「by (15).」 -/
theorem th_13_19_r141 (a h : IProp) (hc : Cons h) : PrI (iand a (inot a)) h = 0 := by
  rcases th_13_19_r140 a h hc with h0 | h0
  · rw [def_X_left_i, h0, zero_mul]
  · rw [def_X_right_i, h0, zero_mul]

/-- ch13-143 (folio 143): (aā ≡ (a + ā の上にバー))/h = 1 — 「by (iii.),」。 -/
theorem th_13_20_r143 (a h : IProp) (hc : Cons h) :
    PrI (iiff (iand a (inot a)) (inot (ior a (inot a)))) h = 1 :=
  ax_iii_taut
    (Form.iffF (Form.conj (Form.var 0) (Form.neg (Form.var 0)))
      (Form.neg (Form.disj (Form.var 0) (Form.neg (Form.var 0)))))
    (fun _ => a) h hc (by intro v; cases h0 : v 0 <;> simp [evalB, h0])

/-- ch13-144 (folio 143): (a + ā の上にバー)/h = 0 — 「by (19) and (12),」。 -/
theorem th_13_20_r144 (a h : IProp) (hc : Cons h) : PrI (inot (ior a (inot a))) h = 0 := by
  rw [← eq_of_cert_iff _ _ h hc (th_13_20_r143 a h hc)]
  exact th_13_19_r141 a h hc

/-- ch13-145 (folio 143): ∴ (a + ā)/h = 1 — 「by (1.3).」 -/
theorem th_13_20_r145 (a h : IProp) (hc : Cons h) : PrI (ior a (inot a)) h = 1 := by
  have := th_13_1_i (ior a (inot a)) h hc
  have z := th_13_20_r144 a h hc
  linarith

/-! ## (21) の証明 (folio 143)

言明の Lean (6b/th_13_21) と同じく a/h₁ を a/(h₁ ∧ h)、a/h₁h₂ を a/(h₁ ∧ (h₂ ∧ h)) の
ように背景 h を足して書く。継ぎ目: ch13-154 は a/(h₁ ∧ (h₂ ∧ h))、ch13-155 は
a/(h₂ ∧ (h₁ ∧ h)) を扱い、印刷はこの二つを同じ a/h₁h₂ とする。ch13-156・157 は
前提の並べ替えを使わず、結論側の Def. IX・X と公理 (iii) で直接導く。 -/

/-- ch13-149 (folio 143): a/h₁h₂ . h₁/h₂ = h₁/ah₂ . a/h₂。 -/
theorem th_13_21_r149 (a h₁ h₂ h : IProp) :
    PrI a (iand h₁ (iand h₂ h)) * PrI h₁ (iand h₂ h) =
      PrI h₁ (iand a (iand h₂ h)) * PrI a (iand h₂ h) := by
  rw [← def_X_left_i a h₁ (iand h₂ h), def_X_right_i a h₁ (iand h₂ h)]

/-- ch13-150 (folio 143): ā/h₁h₂ . h₂/h₁ = h₂/āh₁ . ā/h₁ — 「by X.,」。 -/
theorem th_13_21_r150 (a h₁ h₂ h : IProp) :
    PrI (inot a) (iand h₂ (iand h₁ h)) * PrI h₂ (iand h₁ h) =
      PrI h₂ (iand (inot a) (iand h₁ h)) * PrI (inot a) (iand h₁ h) := by
  rw [← def_X_left_i (inot a) h₂ (iand h₁ h), def_X_right_i (inot a) h₂ (iand h₁ h)]

/-- ch13-151 (folio 143): ∴ a/h₁h₂ . h₁/h₂ = 0 and ā/h₁h₂ . h₂/h₁ = 0
(a/h₂ = 0, ā/h₁ = 0 のとき)。 -/
theorem th_13_21_r151 (a h₁ h₂ h : IProp) (h0 : PrI a (iand h₂ h) = 0)
    (hn : PrI (inot a) (iand h₁ h) = 0) :
    PrI a (iand h₁ (iand h₂ h)) * PrI h₁ (iand h₂ h) = 0 ∧
    PrI (inot a) (iand h₂ (iand h₁ h)) * PrI h₂ (iand h₁ h) = 0 := by
  constructor
  · rw [th_13_21_r149, h0, mul_zero]
  · rw [th_13_21_r150, hn, mul_zero]

/-- ch13-152 (folio 143): ā/h₁ = 0 — 「by hypothesis and (1),」。 -/
theorem th_13_21_r152 (a h₁ h : IProp) (hc1 : Cons (iand h₁ h))
    (h1 : PrI a (iand h₁ h) = 1) : PrI (inot a) (iand h₁ h) = 0 :=
  th_13_1_1 a (iand h₁ h) hc1 h1

/-- ch13-153, ch13-154 (folio 143): (a/h₂ = 0 ゆえ) ∴ a/h₁h₂ = 0 or h₁/h₂ = 0。 -/
theorem th_13_21_r154 (a h₁ h₂ h : IProp) (h0 : PrI a (iand h₂ h) = 0) :
    PrI a (iand h₁ (iand h₂ h)) = 0 ∨ PrI h₁ (iand h₂ h) = 0 := by
  have e := th_13_21_r149 a h₁ h₂ h
  rw [h0, mul_zero] at e
  exact mul_eq_zero.mp e

/-- ch13-155 (folio 143): and a/h₁h₂ = 1 or h₂/h₁ = 0 (ā/h₁ = 0 のとき)。
前提の連言は ch13-150 の Def. X が与える h₂ ∧ (h₁ ∧ h)。 -/
theorem th_13_21_r155 (a h₁ h₂ h : IProp) (hc1 : Cons (iand h₁ h))
    (hn : PrI (inot a) (iand h₁ h) = 0) :
    PrI a (iand h₂ (iand h₁ h)) = 1 ∨ PrI h₂ (iand h₁ h) = 0 := by
  by_cases hd : PrI h₂ (iand h₁ h) = 0
  · right; exact hd
  · left
    have hcd := cons_of_pos h₂ (iand h₁ h) hd hc1
    have e := th_13_21_r150 a h₁ h₂ h
    rw [hn, mul_zero] at e
    rcases mul_eq_zero.mp e with h' | h'
    · exact th_13_1_4 a _ hcd h'
    · exact absurd h' hd

/-- ch13-157 (folio 143): In either case h₁h₂/h = 0 — 「by (15).」
(a/h₁ = 1, a/h₂ = 0 から、結論側の Def. IX・X と公理 (iii) で)。 -/
theorem th_13_21_r157 (a h₁ h₂ h : IProp) (hc : Cons h) (h1 : PrI a (iand h₁ h) = 1)
    (h0 : PrI a (iand h₂ h) = 0) : PrI (iand h₁ h₂) h = 0 := by
  have z1 : PrI (iand a h₂) h = 0 := by rw [def_X_left_i, h0, zero_mul]
  have z2 : PrI (iand (inot a) h₁) h = 0 := by
    rw [def_X_left_i]
    by_cases hd : PrI h₁ h = 0
    · rw [hd, mul_zero]
    · rw [th_13_1_1 a (iand h₁ h) (cons_of_pos h₁ h hd hc) h1, zero_mul]
  have e := def_IX_i (iand h₁ h₂) a h
  have l1 : PrI (iand (iand h₁ h₂) (inot a)) h ≤ PrI (iand (inot a) h₁) h :=
    le_of_taut (Form.conj (Form.conj (Form.var 1) (Form.var 2)) (Form.neg (Form.var 0)))
      (Form.conj (Form.neg (Form.var 0)) (Form.var 1))
      (fun n => match n with | 0 => a | 1 => h₁ | _ => h₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
        simp [evalB, h0, h1, h2])
  have l2 : PrI (iand (iand h₁ h₂) a) h ≤ PrI (iand a h₂) h :=
    le_of_taut (Form.conj (Form.conj (Form.var 1) (Form.var 2)) (Form.var 0))
      (Form.conj (Form.var 0) (Form.var 2))
      (fun n => match n with | 0 => a | 1 => h₁ | _ => h₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
        simp [evalB, h0, h1, h2])
  have p1 := ax_range_lo_i (iand (iand h₁ h₂) (inot a)) h
  have p2 := ax_range_lo_i (iand (iand h₁ h₂) a) h
  linarith

/-- ch13-156 (folio 143): ∴ h₁/h₂ = 0 or h₂/h₁ = 0。
h₁ が整合 (a/h₁ = 1 の前提が存在する、公理 (i)) なので h₁/h ≠ 0、ch13-157 の
h₁h₂/h = 0 を Def. X 右形で割って h₂/h₁ = 0。 -/
theorem th_13_21_r156 (a h₁ h₂ h : IProp) (hc : Cons h) (hc1 : Cons (iand h₁ h))
    (h1 : PrI a (iand h₁ h) = 1) (h0 : PrI a (iand h₂ h) = 0) :
    PrI h₁ (iand h₂ h) = 0 ∨ PrI h₂ (iand h₁ h) = 0 := by
  right
  have z := th_13_21_r157 a h₁ h₂ h hc h1 h0
  rw [def_X_right_i] at z
  rcases mul_eq_zero.mp z with h' | h'
  · exact h'
  · exact absurd h' (cons_of_pos_src h₁ h hc1)

/-! ## (22)・(23) の証明 (folio 143)

言明の Lean (6b/th_13_22, th_13_23) と同じく a/h₁ を a/(h₁ ∧ h)、b/a を b/(a ∧ h) で書く。 -/

/-- ch13-161 (folio 143): ah₁/h = 0 by (15), ∴ h₁/ah . a/h = 0。 -/
theorem th_13_22_r161 (a h₁ h : IProp) (h0 : PrI a (iand h₁ h) = 0) :
    PrI (iand a h₁) h = 0 ∧ PrI h₁ (iand a h) * PrI a h = 0 := by
  have z : PrI (iand a h₁) h = 0 := by rw [def_X_left_i, h0, zero_mul]
  exact ⟨z, by rw [← def_X_right_i]; exact z⟩

/-- ch13-162 (folio 143): h₁/ah = 1 by (9), unless a/h = 0 (h₁/h = 1 のとき)。 -/
theorem th_13_22_r162 (a h₁ h : IProp) (hc : Cons h) (h1 : PrI h₁ h = 1) :
    PrI h₁ (iand a h) = 1 ∨ PrI a h = 0 :=
  th_13_10_r065 h₁ a h hc h1

/-- ch13-163 (folio 143): ∴ in any case a/h = 0。 -/
theorem th_13_22_r163 (a h₁ h : IProp) (hc : Cons h) (h0 : PrI a (iand h₁ h) = 0)
    (h1 : PrI h₁ h = 1) : PrI a h = 0 := by
  have z := (th_13_22_r161 a h₁ h h0).2
  rcases th_13_22_r162 a h₁ h hc h1 with h' | h'
  · rw [h', one_mul] at z; exact z
  · exact h'

/-- ch13-167 (folio 143): ab/h = 0 and āb/h = 0 — 「by (15),」(b/a = 0, b/ā = 0 のとき)。 -/
theorem th_13_23_r167 (a b h : IProp) (hc : Cons h) (h1 : PrI b (iand a h) = 0)
    (h2 : PrI b (iand (inot a) h) = 0) :
    PrI (iand a b) h = 0 ∧ PrI (iand (inot a) b) h = 0 := by
  constructor
  · rw [conj_comm_i a b h hc, def_X_left_i, h1, zero_mul]
  · rw [conj_comm_i (inot a) b h hc, def_X_left_i, h2, zero_mul]

/-- ch13-168 (folio 143): ∴ a/bh = 0 or b/h = 0。 -/
theorem th_13_23_r168 (a b h : IProp) (h0 : PrI (iand a b) h = 0) :
    PrI a (iand b h) = 0 ∨ PrI b h = 0 := by
  rw [def_X_left_i] at h0
  exact mul_eq_zero.mp h0

/-- ch13-169 (folio 143): ā/bh = 0 or b/h = 0 — 「by II. and (iv.),」(内容は Def. X)。 -/
theorem th_13_23_r169 (a b h : IProp) (h0 : PrI (iand (inot a) b) h = 0) :
    PrI (inot a) (iand b h) = 0 ∨ PrI b h = 0 :=
  th_13_23_r168 (inot a) b h h0

/-- ch13-170 (folio 143): whence b/h = 0 — 「by (1.4).」 -/
theorem th_13_23_r170 (a b h : IProp) (hc : Cons h) (h1 : PrI b (iand a h) = 0)
    (h2 : PrI b (iand (inot a) h) = 0) : PrI b h = 0 := by
  by_contra hb
  have hcb := cons_of_pos b h hb hc
  obtain ⟨z1, z2⟩ := th_13_23_r167 a b h hc h1 h2
  rcases th_13_23_r168 a b h z1 with e1 | e1
  · rcases th_13_23_r169 a b h z2 with e2 | e2
    · have := th_13_1_4 a (iand b h) hcb e2
      linarith
    · exact hb e2
  · exact hb e1

end KeynesI

/-! ## 監査クエリ -/

#print axioms KeynesI.th_13_1_r002
#print axioms KeynesI.th_13_1_r003
#print axioms KeynesI.th_13_1_r004
#print axioms KeynesI.th_13_1_r005
#print axioms KeynesI.th_13_1_r006
#print axioms KeynesI.th_13_1_1
#print axioms KeynesI.th_13_1_1_r009
#print axioms KeynesI.th_13_1_1_r010
#print axioms KeynesI.th_13_1_1_r011
#print axioms KeynesI.th_13_1_2
#print axioms KeynesI.th_13_1_3
#print axioms KeynesI.th_13_1_3_r016
#print axioms KeynesI.th_13_1_3_r017
#print axioms KeynesI.th_13_1_3_r018
#print axioms KeynesI.th_13_1_4
#print axioms KeynesI.th_13_5_r027
#print axioms KeynesI.th_13_5_r028
#print axioms KeynesI.th_13_5_r029
#print axioms KeynesI.th_13_5_r031
#print axioms KeynesI.th_13_5_r032
#print axioms KeynesI.th_13_6_r036
#print axioms KeynesI.th_13_6_r037
#print axioms KeynesI.th_13_6_r038
#print axioms KeynesI.th_13_6_r039
#print axioms KeynesI.th_13_7_r043
#print axioms KeynesI.th_13_7_r044
#print axioms KeynesI.th_13_7_r045
#print axioms KeynesI.th_13_7_r046
#print axioms KeynesI.th_13_7_r047
#print axioms KeynesI.th_13_7_r048
#print axioms KeynesI.th_13_8_r052
#print axioms KeynesI.th_13_8_r053
#print axioms KeynesI.th_13_8_r054
#print axioms KeynesI.th_13_8_r055
#print axioms KeynesI.th_13_9_r058
#print axioms KeynesI.th_13_9_r059
#print axioms KeynesI.th_13_9_r060
#print axioms KeynesI.th_13_10_r063
#print axioms KeynesI.th_13_10_r065
#print axioms KeynesI.th_13_10_r067
#print axioms KeynesI.th_13_10_r068
#print axioms KeynesI.th_13_10_r069
#print axioms KeynesI.th_13_11_r072
#print axioms KeynesI.th_13_11_r073
#print axioms KeynesI.th_13_12_r076
#print axioms KeynesI.th_13_12_r077
#print axioms KeynesI.th_13_12_r078
#print axioms KeynesI.th_13_12_1_r081
#print axioms KeynesI.th_13_12_1_r082
#print axioms KeynesI.th_13_12_1_r083
#print axioms KeynesI.th_13_12_1_r084
#print axioms KeynesI.th_13_12_1_r085
#print axioms KeynesI.th_13_r086
#print axioms KeynesI.th_13_13_r088
#print axioms KeynesI.th_13_13_r089
#print axioms KeynesI.th_13_13_r090
#print axioms KeynesI.th_13_13_r091
#print axioms KeynesI.th_13_14_r096
#print axioms KeynesI.th_13_14_r097
#print axioms KeynesI.th_13_14_r098
#print axioms KeynesI.th_13_14_r099
#print axioms KeynesI.th_13_14_r100
#print axioms KeynesI.th_13_14_r101
#print axioms KeynesI.th_13_15_r104
#print axioms KeynesI.th_13_15_r106
#print axioms KeynesI.th_13_15_r108
#print axioms KeynesI.th_13_15_r109
#print axioms KeynesI.th_13_15_r110
#print axioms KeynesI.th_13_16_r115
#print axioms KeynesI.th_13_16_r116
#print axioms KeynesI.th_13_16_r117
#print axioms KeynesI.th_13_16_r118
#print axioms KeynesI.th_13_16_2_r124
#print axioms KeynesI.th_13_16_2_r125
#print axioms KeynesI.th_13_16_2_r126
#print axioms KeynesI.th_13_r129
#print axioms KeynesI.th_13_18_r134
#print axioms KeynesI.th_13_18_r135
#print axioms KeynesI.th_13_18_r136
#print axioms KeynesI.th_13_18_r137
#print axioms KeynesI.th_13_19_r139
#print axioms KeynesI.th_13_19_r140
#print axioms KeynesI.th_13_19_r141
#print axioms KeynesI.th_13_20_r143
#print axioms KeynesI.th_13_20_r144
#print axioms KeynesI.th_13_20_r145
#print axioms KeynesI.th_13_21_r149
#print axioms KeynesI.th_13_21_r150
#print axioms KeynesI.th_13_21_r151
#print axioms KeynesI.th_13_21_r152
#print axioms KeynesI.th_13_21_r154
#print axioms KeynesI.th_13_21_r155
#print axioms KeynesI.th_13_21_r156
#print axioms KeynesI.th_13_21_r157
#print axioms KeynesI.th_13_22_r161
#print axioms KeynesI.th_13_22_r162
#print axioms KeynesI.th_13_22_r163
#print axioms KeynesI.th_13_23_r167
#print axioms KeynesI.th_13_23_r168
#print axioms KeynesI.th_13_23_r169
#print axioms KeynesI.th_13_23_r170
