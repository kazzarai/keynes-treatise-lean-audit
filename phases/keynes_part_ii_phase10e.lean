/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 10e
#
# 第15章 (Numerical Measurement and Approximation of Probabilities, folio 158–163)
# の式行のうち、docs/全数台帳/ch15.md で Lean 欄が「未」だった 49 本を 1 行ずつ
# 定理にする (行 ID は各定理の docstring に書く)。
#
# ## 担体
#   phase6c (B09 修復後) の内包的担体 KeynesI をそのまま写す: IProp・PrI・Cons、
#   Def. IX・X (左右)・XI、範囲、Def. VIII (双条件、但し書き付き) と印刷どおりの
#   片向き版、公理 (iii) の深い埋め込み (Form/evalB/Taut/interp, ax_iii_taut)、
#   整合性の公理 4 本。`Prop → Prop → ℝ` 型の Pr は置かない。
#
#   追加する公理は 1 本だけ: 第15章の公理 (vii.) (folio 159) の公理文 `ax_vii_i`。
#   「(vii.) If q and r are any finite integers and q<r, there exists a relation of
#    probability which can be expressed, by means of the convention of the foregoing
#    definitions, as q/r.」
#   q, r は自然数で読む (整数で読むと範囲の公理と衝突する: th_15_vii_int_reading_fails)。
#   関係が「存在する」ことを公理 (i) (folio 135) に従い、整合な前提 (Cons h) の上の
#   確率関係として書く。
#
#   外延担体 (Prop → Prop → ℝ) との関係: phase7i_model の `ext_forced` により、
#   ax_iii_true と Def. IX を持つ外延担体のどのモデルでも Pr p h は結論 p の真理値
#   (0 か 1) に固定される。したがって (vii.) の 0 < q < r の場合は外延担体では満たせ
#   ない (phase4 `Naive.collapse` はその q/r = 1/2 の場合)。本ファイルの (vii.) 関連の
#   行 (ch15-012・016・017・026・027) が内包担体 KeynesI 上にあるのはこのため。
#   ax_vii_i を加えた KeynesI の無矛盾性は機械検査していない (phase6c_model の有限
#   モデルは値 q/r を有限個しか実現しないので、そのままでは使えない)。
#
# ## 読み方 (行ごとの定理の書き方、phase10b と同じ)
#   1. 各行は「その段で成り立つ関係」として 1 本の定理にする。仮定は、その行の
#      直前で本文が得ている関係 (前の行・言明の前件) と、公理 (i) の但し書き
#      (`Cons h`) だけを置く。前件だけの行は、それを仮定に持つ定理を挙げる。
#   2. 定義 XVII–XIX の「r . a/h」は ℝ の積 `(r : ℝ) * PrI a h` で、
#      「a/h + a/h + … to r terms」は反復和 `addTimes r (PrI a h)` で書く。
#      両者を結ぶのが定義 XVII (addTimes_eq; phase4 の th_ax_xviii_absorbed と同内容)。
#   3. 「lies between A and B」は脚注 1 (folio 162: 「the term 'between' includes
#      the limits」) どおり ≤ 2 本で書く。印刷の狭義不等号 > が成り立たない行
#      ((52) の証明行) は、狭義形の反駁と ≥ 形の証明を両方置く。
#   4. 連鎖等式の行 (「= …」で始まる行) は、直前の項との等式と、連鎖の先頭
#      (a/f + b/h 等) との等式を連言で書く。
#   5. 印刷の添字 1 … n は Lean では 0 から数える (x₁ … x_{n+1} を conjN x n)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase10e.lean
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

/-! ## 第15章の公理 (vii.) (folio 159) -/

/-- **公理 (vii.)** (folio 159): 「If q and r are any finite integers and q<r, there
exists a relation of probability which can be expressed … as q/r.」
q, r は自然数。関係の存在は公理 (i) どおり整合な前提 h の上で述べる。 -/
axiom ax_vii_i (q r : ℕ) (hqr : q < r) :
    ∃ a h : IProp, Cons h ∧ PrI a h = (q : ℝ) / (r : ℝ)

/-! ## 補助定理 (phase6c / phase10b の再掲と、行の証明に使う一般形) -/

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

/-- 第13章 (1) a/h + ā/h = 1 (phase6c の th_13_1_i の再掲)。 -/
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

/-- 第13章 (12) の短い証明 (phase6c の th_12_i_short の再掲): (a≡b)/h = 1 ならば
a/h = b/h。 -/
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

/-- 結論側の連言の可換: pq/h = qp/h (公理 (iii) と (12))。 -/
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

/-- 第14章 (24) 加法定理 (phase6c の th_24_i の再掲): (a + b)/h = a/h + b/h − ab/h。 -/
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

/-- (51) の下限の一般形: x/h + y/h − 1 ≤ xy/h (Def. IX・(1)・範囲)。 -/
theorem conj_lower_i (x y h : IProp) (hc : Cons h) :
    PrI x h + PrI y h - 1 ≤ PrI (iand x y) h := by
  have e := def_IX_i x y h
  have le := conj_le_right_i x (inot y) h hc
  have c := th_13_1_i y h hc
  linarith

/-! ## 定義 XVII (folio 158) — 反復和 -/

/-- 「a/h + {a/h + [a/h + (a/h + … r terms)]}」の反復和。 -/
noncomputable def addTimes : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, P => P + addTimes n P

/-- 定義 XVII (folio 158): 反復和 r 項 = r . P (ℝ の積)。phase4 の
th_ax_xviii_absorbed と同内容 (Keynes の公理を使わない)。 -/
theorem addTimes_eq (P : ℝ) : ∀ n : ℕ, addTimes n P = (n : ℝ) * P := by
  intro n
  induction n with
  | zero => simp [addTimes]
  | succ k ih => simp only [addTimes, ih]; push_cast; ring

/-! ## 定義 XVIII・XIX と §2 の数値例 (folio 158) -/

/-- ch15-002, ch15-003 (folio 158): XVIII. If r . a/h = b/f, then a/h = (1/r) . b/f.
r ≠ 0 は「r terms」(r ≥ 1) の読み。 -/
theorem th_15_def_XVIII (a h b f : IProp) (r : ℕ) (hr : r ≠ 0)
    (H : (r : ℝ) * PrI a h = PrI b f) :
    PrI a h = (1 / (r : ℝ)) * PrI b f := by
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  rw [← H]
  field_simp

/-- ch15-004, ch15-005 (folio 158): XIX. If b/f = q . c/g, then (1/r) . b/f = (q/r) c/g。 -/
theorem th_15_def_XIX (b f c g : IProp) (q r : ℕ)
    (H : PrI b f = (q : ℝ) * PrI c g) :
    (1 / (r : ℝ)) * PrI b f = ((q : ℝ) / (r : ℝ)) * PrI c g := by
  rw [H]
  ring

/-- ch15-006 (folio 158): Thus if b/h = a/h + a/h + … to r terms, then the probability
b/h is said to be r times the probability a/h (前件 H; 結論は r . a/h)。 -/
theorem th_15_r006 (a b h : IProp) (r : ℕ) (H : PrI b h = addTimes r (PrI a h)) :
    PrI b h = (r : ℝ) * PrI a h := by
  rw [H, addTimes_eq]

/-- ch15-007, ch15-008 (前提)、ch15-009 (記法、結論) (folio 158): hence if ab/h = 0 and
a/h = b/h, the probability (a + b)/h is twice the probability a/h。加法定理 (24) から。 -/
theorem th_15_r009 (a b h : IProp) (hc : Cons h) (h0 : PrI (iand a b) h = 0)
    (heq : PrI a h = PrI b h) :
    PrI (ior a b) h = 2 * PrI a h := by
  rw [th_24_i a b h hc, h0, ← heq]
  ring

/-- ch15-010 (前提)、ch15-011 (folio 158): If a and b are exhaustive as well as exclusive
alternatives relatively to h, so that (a + b)/h = 1, … then a/h = b/h = ½ (連鎖を連言で)。 -/
theorem th_15_r011 (a b h : IProp) (hc : Cons h) (h0 : PrI (iand a b) h = 0)
    (heq : PrI a h = PrI b h) (h1 : PrI (ior a b) h = 1) :
    PrI a h = 1 / 2 ∧ PrI b h = 1 / 2 := by
  have e := th_15_r009 a b h hc h0 heq
  constructor <;> linarith

/-! ## 公理 (vii.) (folio 159) の読みの確認 -/

/-- ch15-012 の補足 (folio 159): 印刷の q<r 形と公理 (iii) (確実性 ⊤/⊤ = 1) を合わせると、
phase4 ax_mae・phase7g ax_vii の p ≤ n 形が出る (p = n の場合は値 1 = 確実性)。 -/
theorem th_15_vii_le (p n : ℕ) (hpn : p ≤ n) (hn : n ≠ 0) :
    ∃ a e : IProp, Cons e ∧ PrI a e = (p : ℝ) / (n : ℝ) := by
  rcases lt_or_eq_of_le hpn with hlt | heq
  · exact ax_vii_i p n hlt
  · refine ⟨itrue, itrue, cons_true, ?_⟩
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [itrue_certain itrue cons_true, heq, div_self hn']

/-- ch15-012 の補足 (folio 159): 「any finite integers」を ℤ で字義どおり読んだ形は範囲の
公理 (0 ≤ a/h) と両立しない (q = −1, r = 1)。ax_vii_i が q, r を自然数で読む理由。 -/
theorem th_15_vii_int_reading_fails :
    ¬ ∀ q r : ℤ, q < r → ∃ a e : IProp, PrI a e = (q : ℝ) / (r : ℝ) := by
  intro H
  obtain ⟨a, e, hv⟩ := H (-1) 1 (by norm_num)
  have lo := ax_range_lo_i a e
  rw [hv] at lo
  norm_num at lo

/-! ## (50) (folio 159) -/

/-- ch15-014, ch15-015 (前提)、ch15-016 (folio 159): (50) If a/f = 1/m and b/h = 1/n,
a/f + b/h = (m + n)/mn。和は ℝ の和 (関係としての存在は th_15_50_exists)。 -/
theorem th_15_50 (a f b h : IProp) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ha : PrI a f = 1 / (m : ℝ)) (hb : PrI b h = 1 / (n : ℝ)) :
    PrI a f + PrI b h = ((m : ℝ) + n) / ((m : ℝ) * n) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [ha, hb]
  field_simp
  ring

/-- ch15-017 (folio 159): Let the probability 1/mn = P, which exists by (vii.)。
1 < mn のとき (vii.) の q = 1, r = mn。 -/
theorem th_15_50_r017 (m n : ℕ) (hmn : 1 < m * n) :
    ∃ P : ℝ, 1 / ((m : ℝ) * n) = P ∧ ∃ p k : IProp, Cons k ∧ PrI p k = P := by
  obtain ⟨p, k, hk, hv⟩ := ax_vii_i 1 (m * n) hmn
  refine ⟨1 / ((m : ℝ) * n), rfl, p, k, hk, ?_⟩
  rw [hv]
  push_cast
  ring

/-- ch15-018 (folio 159): then n . P = 1/m = a/f — 「by (XIX.)」(連鎖を連言で)。 -/
theorem th_15_50_r018 (a f : IProp) (m n : ℕ) (hn : n ≠ 0) (P : ℝ)
    (hP : 1 / ((m : ℝ) * n) = P) (ha : PrI a f = 1 / (m : ℝ)) :
    (n : ℝ) * P = 1 / (m : ℝ) ∧ 1 / (m : ℝ) = PrI a f := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨?_, ha.symm⟩
  rw [← hP]
  field_simp

/-- ch15-019 (folio 159): and m . P = 1/n = b/h (連鎖を連言で)。 -/
theorem th_15_50_r019 (b h : IProp) (m n : ℕ) (hm : m ≠ 0) (P : ℝ)
    (hP : 1 / ((m : ℝ) * n) = P) (hb : PrI b h = 1 / (n : ℝ)) :
    (m : ℝ) * P = 1 / (n : ℝ) ∧ 1 / (n : ℝ) = PrI b h := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  refine ⟨?_, hb.symm⟩
  rw [← hP]
  field_simp

/-- ch15-020 (folio 159): ∴ a/f + b/h = n . P + m . P, if this probability exists。 -/
theorem th_15_50_r020 (a f b h : IProp) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (P : ℝ)
    (hP : 1 / ((m : ℝ) * n) = P)
    (ha : PrI a f = 1 / (m : ℝ)) (hb : PrI b h = 1 / (n : ℝ)) :
    PrI a f + PrI b h = (n : ℝ) * P + (m : ℝ) * P := by
  rw [← (th_15_50_r018 a f m n hn P hP ha).2, ← (th_15_50_r019 b h m n hm P hP hb).2,
    (th_15_50_r018 a f m n hn P hP ha).1, (th_15_50_r019 b h m n hm P hP hb).1]

/-- ch15-021 (folio 159): = P + P … to n terms + P + P … to m terms (定義 XVII)。
直前の項 n . P + m . P との等式と、連鎖の先頭 a/f + b/h との等式。 -/
theorem th_15_50_r021 (a f b h : IProp) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (P : ℝ)
    (hP : 1 / ((m : ℝ) * n) = P)
    (ha : PrI a f = 1 / (m : ℝ)) (hb : PrI b h = 1 / (n : ℝ)) :
    (n : ℝ) * P + (m : ℝ) * P = addTimes n P + addTimes m P ∧
    PrI a f + PrI b h = addTimes n P + addTimes m P := by
  have e : (n : ℝ) * P + (m : ℝ) * P = addTimes n P + addTimes m P := by
    rw [addTimes_eq, addTimes_eq]
  exact ⟨e, (th_15_50_r020 a f b h m n hm hn P hP ha hb).trans e⟩

/-- ch15-022 (folio 159): = P + P … to m + n terms。 -/
theorem th_15_50_r022 (a f b h : IProp) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (P : ℝ)
    (hP : 1 / ((m : ℝ) * n) = P)
    (ha : PrI a f = 1 / (m : ℝ)) (hb : PrI b h = 1 / (n : ℝ)) :
    addTimes n P + addTimes m P = addTimes (m + n) P ∧
    PrI a f + PrI b h = addTimes (m + n) P := by
  have e : addTimes n P + addTimes m P = addTimes (m + n) P := by
    rw [addTimes_eq, addTimes_eq, addTimes_eq]
    push_cast
    ring
  exact ⟨e, (th_15_50_r021 a f b h m n hm hn P hP ha hb).2.trans e⟩

/-- ch15-023 (folio 159): = (m + n)P = (m + n)/mn — 「by (XIX.)」。 -/
theorem th_15_50_r023 (a f b h : IProp) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (P : ℝ)
    (hP : 1 / ((m : ℝ) * n) = P)
    (ha : PrI a f = 1 / (m : ℝ)) (hb : PrI b h = 1 / (n : ℝ)) :
    addTimes (m + n) P = ((m : ℝ) + n) * P ∧
    ((m : ℝ) + n) * P = ((m : ℝ) + n) / ((m : ℝ) * n) ∧
    PrI a f + PrI b h = ((m : ℝ) + n) / ((m : ℝ) * n) := by
  have e1 : addTimes (m + n) P = ((m : ℝ) + n) * P := by
    rw [addTimes_eq]
    push_cast
    ring
  have e2 : ((m : ℝ) + n) * P = ((m : ℝ) + n) / ((m : ℝ) * n) := by
    rw [← hP]
    ring
  exact ⟨e1, e2, ((th_15_50_r022 a f b h m n hm hn P hP ha hb).2.trans e1).trans e2⟩

/-- (50) の末尾「This probability exists in virtue of (vii.)」(散文) と ch15-020 の
「if this probability exists」: m + n ≤ mn のとき値 (m + n)/mn の確率関係が存在する
((vii.) の q = m + n, r = mn; 等号の場合は確実性)。 -/
theorem th_15_50_exists (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hle : m + n ≤ m * n) :
    ∃ x k : IProp, Cons k ∧ PrI x k = ((m : ℝ) + n) / ((m : ℝ) * n) := by
  obtain ⟨x, k, hk, hv⟩ := th_15_vii_le (m + n) (m * n) hle (Nat.mul_ne_zero hm hn)
  exact ⟨x, k, hk, by rw [hv]; push_cast; ring⟩

/-! ## §4 数値的に測れる確率の条件 (folio 159–160) -/

/-- ch15-026, ch15-027 (前提) (folio 160): a₁/h₁ = a₂/h₂ = … = a_r/h_r、
a/h = Σ₁^q a_s/h_s、Σ₁^r a_s/h_s = 1 ならば a/h = q/r (条件が満たされれば
a/h は数値的に測れて q/r に等しい)。連鎖は ∀ s < r で、添字は 0 から。 -/
theorem th_15_r027 (a h : IProp) (A H : ℕ → IProp) (q r : ℕ) (hqr : q ≤ r) (hr : r ≠ 0)
    (h026 : ∀ s < r, PrI (A s) (H s) = PrI (A 0) (H 0))
    (h027a : PrI a h = ∑ s ∈ Finset.range q, PrI (A s) (H s))
    (h027b : ∑ s ∈ Finset.range r, PrI (A s) (H s) = 1) :
    PrI a h = (q : ℝ) / (r : ℝ) := by
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have sq : ∑ s ∈ Finset.range q, PrI (A s) (H s) = (q : ℝ) * PrI (A 0) (H 0) := by
    rw [Finset.sum_congr rfl (fun s hs => h026 s
      (lt_of_lt_of_le (Finset.mem_range.mp hs) hqr))]
    simp
  have sr : ∑ s ∈ Finset.range r, PrI (A s) (H s) = (r : ℝ) * PrI (A 0) (H 0) := by
    rw [Finset.sum_congr rfl (fun s hs => h026 s (Finset.mem_range.mp hs))]
    simp
  rw [h027a, sq]
  rw [sr] at h027b
  have hv : PrI (A 0) (H 0) = 1 / (r : ℝ) := by
    field_simp
    linarith
  rw [hv]
  ring

/-- ch15-026, ch15-027 (結論) (folio 160): 「It is necessary that there should exist
probabilities a₁/h₁, … a_r/h_r, such that …」。a/h = q/r (q ≤ r) ならば、(vii.) の
値 1/r の関係を r 個並べたものが条件を満たす (q ≤ r は証明に要らない)。 -/
theorem th_15_r027_nec (a h : IProp) (q r : ℕ) (hr : r ≠ 0)
    (ha : PrI a h = (q : ℝ) / (r : ℝ)) :
    ∃ A H : ℕ → IProp, (∀ s, Cons (H s)) ∧
      (∀ s < r, PrI (A s) (H s) = PrI (A 0) (H 0)) ∧
      PrI a h = ∑ s ∈ Finset.range q, PrI (A s) (H s) ∧
      ∑ s ∈ Finset.range r, PrI (A s) (H s) = 1 := by
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  obtain ⟨p, k, hk, hv⟩ := th_15_vii_le 1 r (Nat.one_le_iff_ne_zero.mpr hr) hr
  refine ⟨fun _ => p, fun _ => k, fun _ => hk, fun _ _ => rfl, ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [ha, hv]
    push_cast
    ring
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hv]
    push_cast
    field_simp

/-- ch15-028, ch15-029 (前提)、ch15-030 (folio 160): If a/h = q₁/r₁ and b/h = q₂/r₂,
it follows … that ab/h = q₁q₂/r₁r₂ — 独立な場合 (Def. XIII の a/bh = a/h) の向き。
第14章 (36) の数値の場合。 -/
theorem th_15_r030 (a b h : IProp) (q₁ r₁ q₂ r₂ : ℕ)
    (ha : PrI a h = (q₁ : ℝ) / r₁) (hb : PrI b h = (q₂ : ℝ) / r₂)
    (hind : PrI a (iand b h) = PrI a h) :
    PrI (iand a b) h = ((q₁ : ℝ) * q₂) / ((r₁ : ℝ) * r₂) := by
  rw [def_X_left_i a b h, hind, ha, hb]
  ring

/-- ch15-028, ch15-029 (前提)、ch15-030 (folio 160): 「… only if a/h and b/h are
independent arguments」の向き。ab/h = q₁q₂/r₁r₂ ならば Def. XIII の 2 式
a/bh = a/h、b/ah = b/h。a/h ≠ 0・b/h ≠ 0 は b/ah・a/bh が存在する範囲 (公理 (i))。 -/
theorem th_15_r030_only_if (a b h : IProp) (q₁ r₁ q₂ r₂ : ℕ)
    (ha : PrI a h = (q₁ : ℝ) / r₁) (hb : PrI b h = (q₂ : ℝ) / r₂)
    (ha0 : PrI a h ≠ 0) (hb0 : PrI b h ≠ 0)
    (hab : PrI (iand a b) h = ((q₁ : ℝ) * q₂) / ((r₁ : ℝ) * r₂)) :
    PrI a (iand b h) = PrI a h ∧ PrI b (iand a h) = PrI b h := by
  have hprod : PrI (iand a b) h = PrI a h * PrI b h := by
    rw [hab, ha, hb]
    ring
  constructor
  · have e := def_X_left_i a b h
    rw [hprod] at e
    exact (mul_right_cancel₀ hb0 e.symm)
  · have e := def_X_right_i a b h
    rw [hprod, mul_comm (PrI a h)] at e
    exact (mul_right_cancel₀ ha0 e.symm)

/-! ## (51) の証明と注意 (folio 162) -/

/-- ch15-033 (folio 162): xy/h = x/h − xȳ/h — 「by (24.2)」(Def. IX)。 -/
theorem th_15_51_r033 (x y h : IProp) :
    PrI (iand x y) h = PrI x h - PrI (iand x (inot y)) h := by
  have e := def_IX_i x y h
  linarith

/-- ch15-034 (folio 162): = x/h − ȳ/h . x/ȳh — 「by X.」
(直前の項との等式と、先頭 xy/h との等式)。 -/
theorem th_15_51_r034 (x y h : IProp) :
    PrI x h - PrI (iand x (inot y)) h = PrI x h - PrI (inot y) h * PrI x (iand (inot y) h) ∧
    PrI (iand x y) h = PrI x h - PrI (inot y) h * PrI x (iand (inot y) h) := by
  have e : PrI x h - PrI (iand x (inot y)) h
      = PrI x h - PrI (inot y) h * PrI x (iand (inot y) h) := by
    rw [def_X_left_i x (inot y) h, mul_comm]
  exact ⟨e, (th_15_51_r033 x y h).trans e⟩

/-- ch15-035 (folio 162): Now x/ȳh lies between 0 and 1 — 「by (2) and (3)」(範囲)。 -/
theorem th_15_51_r035 (x y h : IProp) :
    0 ≤ PrI x (iand (inot y) h) ∧ PrI x (iand (inot y) h) ≤ 1 :=
  ⟨ax_range_lo_i x (iand (inot y) h), ax_range_hi_i x (iand (inot y) h)⟩

/-- ch15-036 (folio 162): ∴ xy/h lies between x/h and x/h − ȳ/h。 -/
theorem th_15_51_r036 (x y h : IProp) :
    PrI x h - PrI (inot y) h ≤ PrI (iand x y) h ∧ PrI (iand x y) h ≤ PrI x h := by
  have e := (th_15_51_r034 x y h).2
  obtain ⟨t0, t1⟩ := th_15_51_r035 x y h
  have hy0 := ax_range_lo_i (inot y) h
  have p1 : 0 ≤ PrI (inot y) h * PrI x (iand (inot y) h) := mul_nonneg hy0 t0
  have p2 : PrI (inot y) h * PrI x (iand (inot y) h) ≤ PrI (inot y) h := by
    nlinarith
  constructor <;> linarith

/-- ch15-037 (folio 162): i.e. between x/h and x/h + y/h − 1 (ȳ/h = 1 − y/h、(1))。 -/
theorem th_15_51_r037 (x y h : IProp) (hc : Cons h) :
    PrI x h + PrI y h - 1 ≤ PrI (iand x y) h ∧ PrI (iand x y) h ≤ PrI x h := by
  have b := th_15_51_r036 x y h
  have c := th_13_1_i y h hc
  constructor <;> linarith [b.1, b.2]

/-- ch15-038 (folio 162): As xy/h ≮ 0, … (範囲)。 -/
theorem th_15_r038 (x y h : IProp) : ¬ (PrI (iand x y) h < 0) :=
  not_lt.mpr (ax_range_lo_i (iand x y) h)

/-- ch15-039 (前提) (folio 162): the above limits may be replaced by x/h and 0, if
x/h + y/h − 1 < 0 (下限 x/h + y/h − 1 を 0 に置き換えた限界)。 -/
theorem th_15_r039 (x y h : IProp) (hlt : PrI x h + PrI y h - 1 < 0) :
    max (PrI x h + PrI y h - 1) 0 = 0 ∧
    0 ≤ PrI (iand x y) h ∧ PrI (iand x y) h ≤ PrI x h :=
  ⟨max_eq_right hlt.le, ax_range_lo_i (iand x y) h, conj_le_left_i x y h⟩

/-- ch15-040 (folio 162): if y/h is nearly certain, xy/h = x/h nearly, quite
independently of whether or not x and y are independent。「nearly」を ε で:
y/h ≥ 1 − ε ならば |xy/h − x/h| ≤ ε (独立性の仮定なし)。 -/
theorem th_15_r040 (x y h : IProp) (hc : Cons h) (ε : ℝ) (hy : 1 - ε ≤ PrI y h) :
    |PrI (iand x y) h - PrI x h| ≤ ε := by
  have b := th_15_51_r037 x y h hc
  have hx := ax_range_hi_i x h
  rw [abs_le]
  constructor <;> linarith [b.1, b.2]

/-! ## (52) の証明 (folio 162) -/

/-- n+1 項の連言 x₀ x₁ … xₙ (印刷の x₁ x₂ … x_{n+1}、添字を 0 から)。
x₁ … x_{n+1} = (x₁ … xₙ) x_{n+1} の結合で積む。 -/
noncomputable def conjN (x : ℕ → IProp) : ℕ → IProp
  | 0 => x 0
  | n + 1 => iand (conjN x n) (x (n + 1))

/-- ch15-042 (folio 162) の包含形: x₁x₂ … x_{n+1}/h ≥ x₁x₂ … xₙ/h + x_{n+1}/h − 1
— 「For by (51)」。Lean の conjN x (n+1) が印刷の x₁ … x_{n+2} に当たる
(印刷の n ≥ 1 を Lean の n + 1 で)。 -/
theorem th_15_52_r042 (x : ℕ → IProp) (h : IProp) (hc : Cons h) (n : ℕ) :
    PrI (conjN x (n + 1)) h ≥ PrI (conjN x n) h + PrI (x (n + 1)) h - 1 :=
  conj_lower_i (conjN x n) (x (n + 1)) h hc

/-- ch15-042 (folio 162) の印刷形 (狭義 >) は成り立たない: x を全部 ⊤、h = ⊤ とすると
両辺 1 (COLLATION 分類 S、phase7i th_15_52_strict_fails と同じ等号の場合)。 -/
theorem th_15_52_r042_strict_fails :
    ¬ ∀ (x : ℕ → IProp) (h : IProp) (n : ℕ), Cons h →
      PrI (conjN x (n + 1)) h > PrI (conjN x n) h + PrI (x (n + 1)) h - 1 := by
  intro H
  have s := H (fun _ => itrue) itrue 0 cons_true
  have e2 : PrI (iand itrue itrue) itrue = 1 :=
    ax_iii_taut (Form.conj Form.tru Form.tru) (fun _ => itrue) itrue cons_true
      (fun _ => rfl)
  have e1 := itrue_certain itrue cons_true
  simp only [conjN] at s
  rw [e2, e1] at s
  norm_num at s

/-- ch15-043 (folio 162) の包含形: > x₁x₂ … x_{n−1}/h + xₙ/h + x_{n+1}/h − 2 を ≥ で
(直前の項との不等式と、先頭 x₁ … x_{n+1}/h との不等式)。「and so on」。 -/
theorem th_15_52_r043 (x : ℕ → IProp) (h : IProp) (hc : Cons h) (n : ℕ) :
    PrI (conjN x (n + 1)) h + PrI (x (n + 2)) h - 1 ≥
      PrI (conjN x n) h + PrI (x (n + 1)) h + PrI (x (n + 2)) h - 2 ∧
    PrI (conjN x (n + 2)) h ≥
      PrI (conjN x n) h + PrI (x (n + 1)) h + PrI (x (n + 2)) h - 2 := by
  have s1 := th_15_52_r042 x h hc n
  have s2 := th_15_52_r042 x h hc (n + 1)
  constructor <;> linarith

/-- ch15-043 (folio 162) の印刷形 (狭義 >) は成り立たない: x を全部 ⊤、h = ⊤ で両辺 1。 -/
theorem th_15_52_r043_strict_fails :
    ¬ ∀ (x : ℕ → IProp) (h : IProp) (n : ℕ), Cons h →
      PrI (conjN x (n + 2)) h >
        PrI (conjN x n) h + PrI (x (n + 1)) h + PrI (x (n + 2)) h - 2 := by
  intro H
  have s := H (fun _ => itrue) itrue 0 cons_true
  have e3 : PrI (iand (iand itrue itrue) itrue) itrue = 1 :=
    ax_iii_taut (Form.conj (Form.conj Form.tru Form.tru) Form.tru) (fun _ => itrue) itrue
      cons_true (fun _ => rfl)
  have e1 := itrue_certain itrue cons_true
  simp only [conjN] at s
  rw [e3, e1] at s
  norm_num at s

/-! ## (53) の証明 (folio 162) -/

/-- ch15-046 (folio 162): For as in (51) xy/h = x/h − xȳ/h (Def. IX)。 -/
theorem th_15_53_r046 (x y h : IProp) :
    PrI (iand x y) h = PrI x h - PrI (iand x (inot y)) h := by
  have e := def_IX_i x y h
  linarith

/-- ch15-047 (folio 162): and x̄ȳ/h = ȳ/h − xȳ/h (Def. IX と連言の可換)。 -/
theorem th_15_53_r047 (x y h : IProp) (hc : Cons h) :
    PrI (iand (inot x) (inot y)) h = PrI (inot y) h - PrI (iand x (inot y)) h := by
  have e := def_IX_i (inot y) x h
  rw [conj_comm_i (inot y) (inot x) h hc, conj_comm_i (inot y) x h hc] at e
  linarith

/-- ch15-048 (folio 162): ∴ xy/h + x̄ȳ/h = x/h − y/h + 1 − 2xȳ/h。 -/
theorem th_15_53_r048 (x y h : IProp) (hc : Cons h) :
    PrI (iand x y) h + PrI (iand (inot x) (inot y)) h
      = PrI x h - PrI y h + 1 - 2 * PrI (iand x (inot y)) h := by
  have e1 := th_15_53_r046 x y h
  have e2 := th_15_53_r047 x y h hc
  have c := th_13_1_i y h hc
  linarith

/-! ## (55) の証明 (folio 163)

λ, μ, ν, ρ, σ, τ, υ を lam mu nu rho sig tau ups と書く。方程式 (i.)–(vi.) は
h1–h6。各行は直前の行で得た関係を仮定に置く。 -/

/-- ch15-056 (folio 163): λ, μ, etc., must all lie between 0 and 1。
λ … υ が確率 (「represent probabilities」) であることを λ = PrI ℓ h 等で置く。 -/
theorem th_15_55_r056 (lam mu nu rho sig tau ups : ℝ) (pl pm pn pr ps pt pu h : IProp)
    (el : lam = PrI pl h) (em : mu = PrI pm h) (en : nu = PrI pn h)
    (er : rho = PrI pr h) (es : sig = PrI ps h) (et : tau = PrI pt h)
    (eu : ups = PrI pu h) :
    (0 ≤ lam ∧ lam ≤ 1) ∧ (0 ≤ mu ∧ mu ≤ 1) ∧ (0 ≤ nu ∧ nu ≤ 1) ∧
    (0 ≤ rho ∧ rho ≤ 1) ∧ (0 ≤ sig ∧ sig ≤ 1) ∧ (0 ≤ tau ∧ tau ≤ 1) ∧
    (0 ≤ ups ∧ ups ≤ 1) := by
  subst el em en er es et eu
  exact ⟨⟨ax_range_lo_i _ _, ax_range_hi_i _ _⟩, ⟨ax_range_lo_i _ _, ax_range_hi_i _ _⟩,
    ⟨ax_range_lo_i _ _, ax_range_hi_i _ _⟩, ⟨ax_range_lo_i _ _, ax_range_hi_i _ _⟩,
    ⟨ax_range_lo_i _ _, ax_range_hi_i _ _⟩, ⟨ax_range_lo_i _ _, ax_range_hi_i _ _⟩,
    ⟨ax_range_lo_i _ _, ax_range_hi_i _ _⟩⟩

/-- ch15-057 (folio 163): From (i.) and (iii.) σ = c − a。 -/
theorem th_15_55_r057 (lam nu sig a c : ℝ)
    (h1 : lam + nu = a) (h3 : lam + nu + sig = c) : sig = c - a := by
  linarith

/-- ch15-058 (folio 163): from (ii.) and (iii.) ν = c − b。 -/
theorem th_15_55_r058 (lam nu sig b c : ℝ)
    (h2 : lam + sig = b) (h3 : lam + nu + sig = c) : nu = c - b := by
  linarith

/-- ch15-059 (folio 163): From (i.), (ii.), and (iii.) λ = a + b − c。 -/
theorem th_15_55_r059 (lam nu sig a b c : ℝ)
    (h1 : lam + nu = a) (h2 : lam + sig = b) (h3 : lam + nu + sig = c) :
    lam = a + b - c := by
  linarith

/-- ch15-060 (folio 163): whence c − a ≥ 0, c − b ≥ 0, a + b − c ≥ 0
(ch15-057–059 と ch15-056 の下限)。 -/
theorem th_15_55_r060 (lam nu sig a b c : ℝ)
    (e057 : sig = c - a) (e058 : nu = c - b) (e059 : lam = a + b - c)
    (hsig : 0 ≤ sig) (hnu : 0 ≤ nu) (hlam : 0 ≤ lam) :
    c - a ≥ 0 ∧ c - b ≥ 0 ∧ a + b - c ≥ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- ch15-061 (folio 163): substituting for σ, ν, λ in (iv.), (v.), and (vi.)
μ + ρ = d − a, μ + τ = e − b, μ + ρ + τ + υ = 1 − c。 -/
theorem th_15_55_r061 (lam mu nu rho sig tau ups a b c d e : ℝ)
    (h4 : lam + mu + nu + rho = d) (h5 : lam + mu + sig + tau = e)
    (h6 : lam + mu + nu + rho + sig + tau + ups = 1)
    (e057 : sig = c - a) (e058 : nu = c - b) (e059 : lam = a + b - c) :
    mu + rho = d - a ∧ mu + tau = e - b ∧ mu + rho + tau + ups = 1 - c := by
  subst e057 e058 e059
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- ch15-062 (folio 163): whence ρ = d − a − μ, τ = e − b − μ,
υ = 1 − c − d + a − e + b + μ。 -/
theorem th_15_55_r062 (mu rho tau ups a b c d e : ℝ)
    (e1 : mu + rho = d - a) (e2 : mu + tau = e - b) (e3 : mu + rho + tau + ups = 1 - c) :
    rho = d - a - mu ∧ tau = e - b - mu ∧ ups = 1 - c - d + a - e + b + mu := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- ch15-063 (folio 163): ∴ d − a − μ ≥ 0, e − b − μ ≥ 0, 1 − c − d + a − e + b + μ ≥ 0
(ch15-062 と ch15-056 の下限)。 -/
theorem th_15_55_r063 (mu rho tau ups a b c d e : ℝ)
    (e1 : rho = d - a - mu) (e2 : tau = e - b - mu) (e3 : ups = 1 - c - d + a - e + b + mu)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau) (hups : 0 ≤ ups) :
    d - a - mu ≥ 0 ∧ e - b - mu ≥ 0 ∧ 1 - c - d + a - e + b + mu ≥ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- ch15-064 (folio 163): We have still to eliminate μ. μ ≤ d − a, μ ≤ e − b。 -/
theorem th_15_55_r064 (mu a b d e : ℝ)
    (g1 : d - a - mu ≥ 0) (g2 : e - b - mu ≥ 0) : mu ≤ d - a ∧ mu ≤ e - b := by
  constructor <;> linarith

/-- ch15-065 (folio 163): μ ≥ c + d + e − a − b − 1。 -/
theorem th_15_55_r065 (mu a b c d e : ℝ)
    (g3 : 1 - c - d + a - e + b + mu ≥ 0) : mu ≥ c + d + e - a - b - 1 := by
  linarith

/-- ch15-066 (folio 163): ∴ d − a ≥ c + d + e − a − b − 1 and e − b ≥ c + d + e − a − b − 1。 -/
theorem th_15_55_r066 (mu a b c d e : ℝ)
    (u1 : mu ≤ d - a) (u2 : mu ≤ e - b) (l : mu ≥ c + d + e - a - b - 1) :
    d - a ≥ c + d + e - a - b - 1 ∧ e - b ≥ c + d + e - a - b - 1 := by
  constructor <;> linarith

end KeynesI

/-! ## 監査クエリ (Phase 10e) -/

#print axioms KeynesI.addTimes_eq
#print axioms KeynesI.th_15_def_XVIII
#print axioms KeynesI.th_15_def_XIX
#print axioms KeynesI.th_15_r006
#print axioms KeynesI.th_15_r009
#print axioms KeynesI.th_15_r011
#print axioms KeynesI.th_15_vii_le
#print axioms KeynesI.th_15_vii_int_reading_fails
#print axioms KeynesI.th_15_50
#print axioms KeynesI.th_15_50_r017
#print axioms KeynesI.th_15_50_r018
#print axioms KeynesI.th_15_50_r019
#print axioms KeynesI.th_15_50_r020
#print axioms KeynesI.th_15_50_r021
#print axioms KeynesI.th_15_50_r022
#print axioms KeynesI.th_15_50_r023
#print axioms KeynesI.th_15_50_exists
#print axioms KeynesI.th_15_r027
#print axioms KeynesI.th_15_r027_nec
#print axioms KeynesI.th_15_r030
#print axioms KeynesI.th_15_r030_only_if
#print axioms KeynesI.th_15_51_r033
#print axioms KeynesI.th_15_51_r034
#print axioms KeynesI.th_15_51_r035
#print axioms KeynesI.th_15_51_r036
#print axioms KeynesI.th_15_51_r037
#print axioms KeynesI.th_15_r038
#print axioms KeynesI.th_15_r039
#print axioms KeynesI.th_15_r040
#print axioms KeynesI.th_15_52_r042
#print axioms KeynesI.th_15_52_r042_strict_fails
#print axioms KeynesI.th_15_52_r043
#print axioms KeynesI.th_15_52_r043_strict_fails
#print axioms KeynesI.th_15_53_r046
#print axioms KeynesI.th_15_53_r047
#print axioms KeynesI.th_15_53_r048
#print axioms KeynesI.th_15_55_r056
#print axioms KeynesI.th_15_55_r057
#print axioms KeynesI.th_15_55_r058
#print axioms KeynesI.th_15_55_r059
#print axioms KeynesI.th_15_55_r060
#print axioms KeynesI.th_15_55_r061
#print axioms KeynesI.th_15_55_r062
#print axioms KeynesI.th_15_55_r063
#print axioms KeynesI.th_15_55_r064
#print axioms KeynesI.th_15_55_r065
#print axioms KeynesI.th_15_55_r066
