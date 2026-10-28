/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 10h
#
# 第16章 (Observations on the Theorems of Chapter XIV. and their Developments,
# including Testimony, folio 164–185) の式行のうち、docs/全数台帳/ch16.md で Lean 欄が
# 「未」だった 88 本を 1 行ずつ定理にする (行 ID は各定理の docstring に書く)。
# ch16-002 ((36) の再掲) は既に ✓ (th_14_36) なので扱わない。
#
# ## 担体
#   phase6c (B09 修復後) の内包的担体 KeynesI をそのまま写す: IProp・PrI・Cons、
#   Def. IX・X (左右)・XI、範囲、Def. VIII (双条件、但し書き付き) と印刷どおりの
#   片向き版、公理 (iii) の深い埋め込み (Form/evalB/Taut/interp, ax_iii_taut)、
#   整合性の公理 4 本。新しい公理は置かない。`Prop → Prop → ℝ` 型の Pr は置かない。
#
# ## 読み方 (行ごとの定理の書き方、phase10b・10e と同じ)
#   1. 各行は「その段で成り立つ関係」として定理にする。仮定は、その行の直前で本文が
#      置いている関係 (前の行・言明の前件・「we may assume」の関係) と、公理 (i) の
#      但し書き (`Cons …`) と除法の但し書き (`… ≠ 0`) だけ。前件だけの行は、それを
#      仮定に持つ定理を台帳に挙げる (前提)。
#   2. 散文の条件 (Principle of Indifference、無関係性、「a follows from mᵢaᵢ」等) は
#      公理にせず、各定理の仮定として書く。英語の命題 (‘heads at first toss’ 等) は
#      IProp の原子 (定理の引数) で表し、名付けの行は def だけ置く (rfl の定理は置かず、
#      台帳では「未」、備考「定義のみ (名付け)」)。
#   3. 前提のコンマ区切り「(x, y, h)」とドット区切り「X(x) . h」は iand の右結合
#      `iand x (iand y h)` で書く。本公理系には前提の連言の可換も前提側の置換も無いので、
#      Def. X から出る前提の順序が印刷と違う箇所 (a₁a₂h を a₂(a₁h) 等) は台帳で ≈ とする。
#   4. 連鎖等式の行は、直前の項との等式と連鎖の先頭との等式を連言で書く。
#   5. 印刷の形が成り立たない行は、反駁と修正形を両方置く。Keynes 自身の式 (§17 の分母
#      (1 − x₂)) は台帳で ✎。Keynes が誤りとして引く他の著者の式 (Boole の Prob. x = p、
#      a/h₁h₂ = ½、Maxwell の X(x)Y(y)Z(z)/h = V(v)/h) に ✎ を当てるかは裁定待ちなので、
#      台帳では「未」とし、反駁の定理は所見候補の材料として置くだけにする。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase10h.lean
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

/-! ## 補助定理 (phase6c / phase10b / phase10e の再掲) -/

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

/-! ## 本章で使う一般形 (Def. IX・X・(1)・(iii) から) -/

/-- x/xk = 1 (前提に結論を含む場合)。Cons k と Cons (x∧k) のもとで。 -/
theorem self_certain (x k : IProp) (hk : Cons k) (hxk : Cons (iand x k)) :
    PrI x (iand x k) = 1 := by
  have e := def_X_right_i x x k
  have s : PrI (iand x x) k = PrI x k :=
    subst_taut (Form.conj (Form.var 0) (Form.var 0)) (Form.var 0) (fun _ => x) k hk
      (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have hx : PrI x k ≠ 0 := cons_of_pos_src x k hxk
  rw [s] at e
  exact mul_right_cancel₀ hx (by rw [one_mul]; exact e.symm)

/-- x/x̄k = 0。Cons k と Cons (x̄∧k) のもとで。 -/
theorem neg_premiss_zero (x k : IProp) (hk : Cons k) (hnk : Cons (iand (inot x) k)) :
    PrI x (iand (inot x) k) = 0 := by
  have e := def_X_right_i (inot x) x k
  have z : PrI (iand (inot x) x) k = 0 :=
    taut_neg_zero (Form.conj (Form.neg (Form.var 0)) (Form.var 0)) (fun _ => x) k hk
      (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have hn : PrI (inot x) k ≠ 0 := cons_of_pos_src (inot x) k hnk
  rw [z] at e
  exact (mul_eq_zero.mp e.symm).resolve_right hn

/-- a/mk = 1 かつ m/ak = 1 ならば a/k = m/k (Def. X の左右)。 -/
theorem follows_both (a m k : IProp) (ham : PrI a (iand m k) = 1)
    (hma : PrI m (iand a k) = 1) : PrI a k = PrI m k := by
  have e1 := def_X_left_i a m k
  have e2 := def_X_right_i a m k
  rw [ham, one_mul] at e1
  rw [hma, one_mul] at e2
  linarith

/-- x/k = 0 ならば、整合な y∧k を前提にしても x/yk = 0。 -/
theorem zero_transfer (x y k : IProp) (hx : PrI x k = 0) (hy : Cons (iand y k)) :
    PrI x (iand y k) = 0 := by
  have e := def_X_left_i x y k
  have le := conj_le_left_i x y k
  have lo := ax_range_lo_i (iand x y) k
  have z : PrI (iand x y) k = 0 := by linarith
  have hyne := cons_of_pos_src y k hy
  rw [z] at e
  exact (mul_eq_zero.mp e.symm).resolve_right hyne

/-- 結論側の置換: a/mk = 1 かつ m/ak = 1 ならば mX/k = aX/k。 -/
theorem conj_subst_mutual (m a X k : IProp) (hk : Cons k) (ham : PrI a (iand m k) = 1)
    (hma : PrI m (iand a k) = 1) : PrI (iand m X) k = PrI (iand a X) k := by
  have e1 := def_X_left_i a m k
  have e2 := def_X_left_i m a k
  rw [ham, one_mul] at e1
  rw [hma, one_mul] at e2
  have cm := conj_comm_i a m k hk
  have i1 := def_IX_i m a k
  have i2 := def_IX_i a m k
  have D : PrI (iand m (inot a)) k = 0 := by linarith
  have E : PrI (iand a (inot m)) k = 0 := by linarith
  have j1 := def_IX_i (iand m X) a k
  have j2 := def_IX_i (iand a X) m k
  have t1 : PrI (iand (iand m X) (inot a)) k = PrI (iand (iand m (inot a)) X) k :=
    subst_taut (Form.conj (Form.conj (Form.var 0) (Form.var 1)) (Form.neg (Form.var 2)))
      (Form.conj (Form.conj (Form.var 0) (Form.neg (Form.var 2))) (Form.var 1))
      (fun n => match n with | 0 => m | 1 => X | _ => a) k hk
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  have t2 : PrI (iand (iand a X) (inot m)) k = PrI (iand (iand a (inot m)) X) k :=
    subst_taut (Form.conj (Form.conj (Form.var 0) (Form.var 1)) (Form.neg (Form.var 2)))
      (Form.conj (Form.conj (Form.var 0) (Form.neg (Form.var 2))) (Form.var 1))
      (fun n => match n with | 0 => a | 1 => X | _ => m) k hk
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  have t3 : PrI (iand (iand m X) a) k = PrI (iand (iand a X) m) k :=
    subst_taut (Form.conj (Form.conj (Form.var 0) (Form.var 1)) (Form.var 2))
      (Form.conj (Form.conj (Form.var 2) (Form.var 1)) (Form.var 0))
      (fun n => match n with | 0 => m | 1 => X | _ => a) k hk
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  have l1 := conj_le_left_i (iand m (inot a)) X k
  have l2 := conj_le_left_i (iand a (inot m)) X k
  have z1 := ax_range_lo_i (iand (iand m X) (inot a)) k
  have z2 := ax_range_lo_i (iand (iand a X) (inot m)) k
  linarith

/-- 等確率・排反・網羅の二者は ½ ((24) から)。 -/
theorem half_of_indiff (x t h : IProp) (hc : Cons h) (hind : PrI x h = PrI t h)
    (hex : PrI (iand x t) h = 0) (hall : PrI (ior x t) h = 1) : PrI x h = 1 / 2 := by
  have e := th_24_i x t h hc
  linarith

/-! ## §6 (folio 168) — Boole の「Prob. x = p」 -/

/-- ch16-003 (folio 168): 「the data of a problem can be of the form, “Prob. x = p,” i.e.
that it is sufficient to state that the probability of a proposition is such and such,
without stating to what premisses this probability is referred」。前提を書かない読み
(どの整合な前提 e についても x/e = p) は、x と x̄ がそれぞれ整合に加えられる前提 k が
あれば成り立たない (他の著者の式の反駁; 台帳は未、所見候補の材料)。 -/
theorem th_16_r003_premissless_fails (x k : IProp) (hk : Cons k) (hxk : Cons (iand x k))
    (hnxk : Cons (iand (inot x) k)) :
    ¬ ∃ p : ℝ, ∀ e : IProp, Cons e → PrI x e = p := by
  rintro ⟨p, H⟩
  have h1 := H (iand x k) hxk
  have h0 := H (iand (inot x) k) hnxk
  rw [self_certain x k hk hxk] at h1
  rw [neg_premiss_zero x k hk hnxk] at h0
  linarith

/-- ch16-003 (folio 168) に対して: 前提を明示すると値は前提によって定まる
(x/xk = 1、x/x̄k = 0; 台帳は未、所見候補の材料)。 -/
theorem th_16_r003 (x k : IProp) (hk : Cons k) (hxk : Cons (iand x k))
    (hnxk : Cons (iand (inot x) k)) :
    PrI x (iand x k) = 1 ∧ PrI x (iand (inot x) k) = 0 :=
  ⟨self_certain x k hk hxk, neg_premiss_zero x k hk hnxk⟩

/-! ## §8 (folio 170) — 一枚の貨幣の「heads twice」 -/

/-- ch16-009 (folio 170) の名付け: ‘heads at first toss’ = h₁。第 n 投の表を原子
`heads n` で表す (定義のみ; 台帳は未)。 -/
noncomputable def coin_h₁ (heads : ℕ → IProp) : IProp := heads 1

/-- ch16-010 (folio 170) の名付け: ‘heads at second toss’ = h₂ (定義のみ; 台帳は未)。 -/
noncomputable def coin_h₂ (heads : ℕ → IProp) : IProp := heads 2

/-- ch16-011 (folio 170): Then h₁/h = h₂/h = ½ (連鎖を連言で)。前提は本文の「the initial
chances for heads and tails respectively at the first toss really are equal」(表と裏の
等確率) と、表・裏の排反・網羅 (散文の条件)。 -/
theorem th_16_r011 (heads tails : ℕ → IProp) (h : IProp) (hc : Cons h)
    (hind1 : PrI (coin_h₁ heads) h = PrI (tails 1) h)
    (hex1 : PrI (iand (coin_h₁ heads) (tails 1)) h = 0)
    (hall1 : PrI (ior (coin_h₁ heads) (tails 1)) h = 1)
    (hind2 : PrI (coin_h₂ heads) h = PrI (tails 2) h)
    (hex2 : PrI (iand (coin_h₂ heads) (tails 2)) h = 0)
    (hall2 : PrI (ior (coin_h₂ heads) (tails 2)) h = 1) :
    PrI (coin_h₁ heads) h = PrI (coin_h₂ heads) h ∧ PrI (coin_h₂ heads) h = 1 / 2 := by
  have e1 := half_of_indiff _ _ h hc hind1 hex1 hall1
  have e2 := half_of_indiff _ _ h hc hind2 hex2 hall2
  exact ⟨by rw [e1, e2], e2⟩

/-- ch16-012 (folio 170): and h₁h₂/h = h₂/h₁h . h₁/h (Def. X)。 -/
theorem th_16_r012 (heads : ℕ → IProp) (h : IProp) :
    PrI (iand (coin_h₁ heads) (coin_h₂ heads)) h =
      PrI (coin_h₂ heads) (iand (coin_h₁ heads) h) * PrI (coin_h₁ heads) h :=
  def_X_right_i _ _ _

/-- ch16-013・ch16-014 (folio 170): Hence h₁h₂/h = {h₁/h}² only if h₂/h₁h = h₂/h
(h₁/h = h₂/h = ½ のもとで、only if を ↔ で)。 -/
theorem th_16_r013 (heads : ℕ → IProp) (h : IProp)
    (h011a : PrI (coin_h₁ heads) h = 1 / 2) (h011b : PrI (coin_h₂ heads) h = 1 / 2) :
    PrI (iand (coin_h₁ heads) (coin_h₂ heads)) h = (PrI (coin_h₁ heads) h) ^ 2 ↔
      PrI (coin_h₂ heads) (iand (coin_h₁ heads) h) = PrI (coin_h₂ heads) h := by
  rw [th_16_r012, h011a, h011b]
  constructor <;> intro H <;> linarith

/-- ch16-014 (folio 170): h₂/h₁h = h₂/h ならば h₁h₂/h = {h₁/h}² (if の向き)。 -/
theorem th_16_r014 (heads : ℕ → IProp) (h : IProp)
    (h014 : PrI (coin_h₂ heads) (iand (coin_h₁ heads) h) = PrI (coin_h₂ heads) h)
    (h011a : PrI (coin_h₁ heads) h = 1 / 2) (h011b : PrI (coin_h₂ heads) h = 1 / 2) :
    PrI (iand (coin_h₁ heads) (coin_h₂ heads)) h = (PrI (coin_h₁ heads) h) ^ 2 :=
  (th_16_r013 heads h h011a h011b).mpr h014

/-! ## §8 (folio 171) — Laplace の二枚の貨幣

式での用法: h₁, h₂ は第 1 の貨幣の第 1 投・第 2 投の表、h₁′, h₂′ は第 2 の貨幣の同じ投の表
(t は裏)。h₁h₁′ + t₁t₁′ は「第 1 投で二枚が一致」で、+ は選言 ior。 -/

/-- ch16-018 (folio 171): (h₂h₂′ + t₂t₂′)(h₁h₁′ + t₁t₁′)/h
= (h₂h₂′ + t₂t₂′)/(h₁h₁′ + t₁t₁′, h) . (h₁h₁′ + t₁t₁′)/h (Def. X; 前提のコンマを iand で)。 -/
theorem th_16_r018 (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp) :
    PrI (iand (ior (iand H2 H2') (iand T2 T2')) (ior (iand H1 H1') (iand T1 T1'))) h =
      PrI (ior (iand H2 H2') (iand T2 T2')) (iand (ior (iand H1 H1') (iand T1 T1')) h) *
        PrI (ior (iand H1 H1') (iand T1 T1')) h :=
  def_X_left_i _ _ _

/-- ch16-021 (folio 171): and h₂h₂′t₂t₂′/h = 0。前提は表と裏の排反 h₂t₂/h = 0 (散文)。 -/
theorem th_16_r021 (H2 H2' T2 T2' h : IProp) (hc : Cons h)
    (hex : PrI (iand H2 T2) h = 0) :
    PrI (iand (iand H2 H2') (iand T2 T2')) h = 0 := by
  have s : PrI (iand (iand H2 H2') (iand T2 T2')) h =
      PrI (iand (iand H2 T2) (iand H2' T2')) h :=
    subst_taut
      (Form.conj (Form.conj (Form.var 0) (Form.var 1)) (Form.conj (Form.var 2) (Form.var 3)))
      (Form.conj (Form.conj (Form.var 0) (Form.var 2)) (Form.conj (Form.var 1) (Form.var 3)))
      (fun n => match n with | 0 => H2 | 1 => H2' | 2 => T2 | _ => T2') h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            cases h3 : v 3 <;> simp [evalB, h0, h1, h2, h3])
  have le := conj_le_left_i (iand H2 T2) (iand H2' T2') h
  have lo := ax_range_lo_i (iand (iand H2 H2') (iand T2 T2')) h
  linarith

/-- ch16-020 (前提 h020)、ch16-022 (folio 171): ∴ (h₂h₂′ + t₂t₂′)/(h₁h₁′ + t₁t₁′, h)
= 2 . h₂h₂′/(h₁h₁′ + t₁t₁′, h) — 「by (24.1)」。h020 は「by the Principle of Indifference」。 -/
theorem th_16_r022 (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp)
    (hcA : Cons (iand (ior (iand H1 H1') (iand T1 T1')) h))
    (hex2 : PrI (iand H2 T2) h = 0)
    (h020 : PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) =
      PrI (iand T2 T2') (iand (ior (iand H1 H1') (iand T1 T1')) h)) :
    PrI (ior (iand H2 H2') (iand T2 T2')) (iand (ior (iand H1 H1') (iand T1 T1')) h) =
      2 * PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) := by
  have e := th_24_i (iand H2 H2') (iand T2 T2') _ hcA
  have z := th_16_r021 H2 H2' T2 T2' _ hcA (zero_transfer _ _ h hex2 hcA)
  linarith

/-- ch16-023 (folio 171): Similarly (h₁h₁′ + t₁t₁′)/h = 2h₁h₁′/h。前提 h₁h₁′/h = t₁t₁′/h
(「Similarly」= 第 1 投についての Principle of Indifference) と排反 h₁t₁/h = 0。 -/
theorem th_16_r023 (H1 H1' T1 T1' h : IProp) (hc : Cons h)
    (hex1 : PrI (iand H1 T1) h = 0)
    (hind : PrI (iand H1 H1') h = PrI (iand T1 T1') h) :
    PrI (ior (iand H1 H1') (iand T1 T1')) h = 2 * PrI (iand H1 H1') h := by
  have e := th_24_i (iand H1 H1') (iand T1 T1') h hc
  have z := th_16_r021 H1 H1' T1 T1' h hc hex1
  linarith

/-- ch16-025 (folio 171): and h₁/h = h₁′/h = ½ by the Principle of Indifference
(連鎖を連言で; 前提は表と裏の等確率・排反・網羅)。 -/
theorem th_16_r025 (H1 H1' T1 T1' h : IProp) (hc : Cons h)
    (hind : PrI H1 h = PrI T1 h) (hex : PrI (iand H1 T1) h = 0)
    (hall : PrI (ior H1 T1) h = 1)
    (hind' : PrI H1' h = PrI T1' h) (hex' : PrI (iand H1' T1') h = 0)
    (hall' : PrI (ior H1' T1') h = 1) :
    PrI H1 h = PrI H1' h ∧ PrI H1' h = 1 / 2 := by
  have e1 := half_of_indiff _ _ h hc hind hex hall
  have e2 := half_of_indiff _ _ h hc hind' hex' hall'
  exact ⟨by rw [e1, e2], e2⟩

/-- ch16-024 (前提 h024)、ch16-025 (前提)、ch16-026 (folio 171): so that
(h₁h₁′ + t₁t₁′)/h = 2(½)² = ½ (連鎖を連言で)。 -/
theorem th_16_r026 (H1 H1' T1 T1' h : IProp) (hc : Cons h)
    (hex1 : PrI (iand H1 T1) h = 0)
    (hind : PrI (iand H1 H1') h = PrI (iand T1 T1') h)
    (h024 : PrI H1 (iand H1' h) = PrI H1 h)
    (h025a : PrI H1 h = 1 / 2) (h025b : PrI H1' h = 1 / 2) :
    PrI (ior (iand H1 H1') (iand T1 T1')) h = 2 * (1 / 2) ^ 2 ∧
      PrI (ior (iand H1 H1') (iand T1 T1')) h = 1 / 2 := by
  have e := def_X_left_i H1 H1' h
  rw [h024, h025a, h025b] at e
  rw [th_16_r023 H1 H1' T1 T1' h hc hex1 hind, e]
  norm_num

/-- §8 (folio 171) の本文の仮定をまとめた構造 (散文の条件: 表と裏の排反、
Principle of Indifference、貨幣どうしの無関係性)。 -/
structure LaplaceCoins (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp) : Prop where
  hc : Cons h
  hcA : Cons (iand (ior (iand H1 H1') (iand T1 T1')) h)
  hex1 : PrI (iand H1 T1) h = 0
  hex2 : PrI (iand H2 T2) h = 0
  h020 : PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) =
    PrI (iand T2 T2') (iand (ior (iand H1 H1') (iand T1 T1')) h)
  hind1 : PrI (iand H1 H1') h = PrI (iand T1 T1') h
  h024 : PrI H1 (iand H1' h) = PrI H1 h
  h025a : PrI H1 h = 1 / 2
  h025b : PrI H1' h = 1 / 2
  h030 : PrI H2' (iand (ior (iand H1 H1') (iand T1 T1')) h) = 1 / 2

/-- ch16-027 (folio 171): ∴ (h₂h₂′ + t₂t₂′)(h₁h₁′ + t₁t₁′)/h
= 2h₂h₂′/(h₁h₁′ + t₁t₁′, h) . ½。 -/
theorem th_16_r027 (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp)
    (L : LaplaceCoins H1 H1' T1 T1' H2 H2' T2 T2' h) :
    PrI (iand (ior (iand H2 H2') (iand T2 T2')) (ior (iand H1 H1') (iand T1 T1'))) h =
      2 * PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) * (1 / 2) := by
  rw [th_16_r018, th_16_r022 H1 H1' T1 T1' H2 H2' T2 T2' h L.hcA L.hex2 L.h020,
    (th_16_r026 H1 H1' T1 T1' h L.hc L.hex1 L.hind1 L.h024 L.h025a L.h025b).2]

/-- ch16-028 (folio 171): = h₂h₂′/(h₁h₁′ + t₁t₁′, h) (直前の項との等式と先頭との等式)。 -/
theorem th_16_r028 (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp)
    (L : LaplaceCoins H1 H1' T1 T1' H2 H2' T2 T2' h) :
    2 * PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) * (1 / 2) =
        PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) ∧
      PrI (iand (ior (iand H2 H2') (iand T2 T2')) (ior (iand H1 H1') (iand T1 T1'))) h =
        PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) := by
  have e : 2 * PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) * (1 / 2) =
      PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) := by ring
  exact ⟨e, (th_16_r027 H1 H1' T1 T1' H2 H2' T2 T2' h L).trans e⟩

/-- ch16-029 (folio 171): = ½h₂/(h₂′, h₁h₁′ + t₁t₁′, h) (Def. X と h₂′/(h₁h₁′ + t₁t₁′, h) = ½;
直前の項との等式と先頭との等式)。 -/
theorem th_16_r029 (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp)
    (L : LaplaceCoins H1 H1' T1 T1' H2 H2' T2 T2' h) :
    PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) =
        1 / 2 * PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) ∧
      PrI (iand (ior (iand H2 H2') (iand T2 T2')) (ior (iand H1 H1') (iand T1 T1'))) h =
        1 / 2 * PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) := by
  have e := def_X_left_i H2 H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)
  rw [L.h030] at e
  have e' : PrI (iand H2 H2') (iand (ior (iand H1 H1') (iand T1 T1')) h) =
      1 / 2 * PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) := by
    rw [e]; ring
  exact ⟨e', (th_16_r028 H1 H1' T1 T1' H2 H2' T2 T2' h L).2.trans e'⟩

/-- ch16-030 (folio 171): since, (h₁h₁′ + t₁t₁′) being irrelevant to h′₂/h,
h′₂/(h₁h₁′ + t₁t₁′, h) = h₂′/h = ½ (連鎖を連言で; 前提は無関係性 hirr と表・裏の
等確率・排反・網羅)。 -/
theorem th_16_r030 (H1 H1' T1 T1' H2' T2' h : IProp) (hc : Cons h)
    (hirr : PrI H2' (iand (ior (iand H1 H1') (iand T1 T1')) h) = PrI H2' h)
    (hind : PrI H2' h = PrI T2' h) (hex : PrI (iand H2' T2') h = 0)
    (hall : PrI (ior H2' T2') h = 1) :
    PrI H2' (iand (ior (iand H1 H1') (iand T1 T1')) h) = PrI H2' h ∧
      PrI H2' h = 1 / 2 :=
  ⟨hirr, half_of_indiff _ _ h hc hind hex hall⟩

/-- ch16-031 (前提 h031) (folio 171): Now h₂/(h₂′, h₁h₁′ + t₁t₁′, h) is greater than ½。
このとき二度続けての一致の確率は ¼ より大きい。 -/
theorem th_16_r031 (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp)
    (L : LaplaceCoins H1 H1' T1 T1' H2 H2' T2 T2' h)
    (h031 : PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) > 1 / 2) :
    PrI (iand (ior (iand H2 H2') (iand T2 T2')) (ior (iand H1 H1') (iand T1 T1'))) h >
      1 / 4 := by
  rw [(th_16_r029 H1 H1' T1 T1' H2 H2' T2 T2' h L).2]
  linarith

/-- ch16-033・ch16-034 (前提)、ch16-032 (folio 171): But it is less than h₂/h₁h: for we may
assume that h₂/(h₂′, h₁h₁′ + t₁t₁′, h) is less than h₂/(h₂′, h₁h₁′, h), and also that
h₂/(h₂′, h₁h₁′, h) = h₂/h₁h。 -/
theorem th_16_r032 (H1 H1' T1 T1' H2 H2' h : IProp)
    (h033 : PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) <
      PrI H2 (iand H2' (iand (iand H1 H1') h)))
    (h034 : PrI H2 (iand H2' (iand (iand H1 H1') h)) = PrI H2 (iand H1 h)) :
    PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) < PrI H2 (iand H1 h) :=
  h034 ▸ h033

/-- ch16-031–034 の帰結 (folio 171、記法行 ch16-035 の言明): Laplace の方法は h₁h₂/h よりも
¼ に近い確率を与える (¼ < 確率 < h₁h₂/h)。 -/
theorem th_16_r032_nearer (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp)
    (L : LaplaceCoins H1 H1' T1 T1' H2 H2' T2 T2' h)
    (h031 : PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) > 1 / 2)
    (h033 : PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) <
      PrI H2 (iand H2' (iand (iand H1 H1') h)))
    (h034 : PrI H2 (iand H2' (iand (iand H1 H1') h)) = PrI H2 (iand H1 h)) :
    1 / 4 <
        PrI (iand (ior (iand H2 H2') (iand T2 T2')) (ior (iand H1 H1') (iand T1 T1'))) h ∧
      PrI (iand (ior (iand H2 H2') (iand T2 T2')) (ior (iand H1 H1') (iand T1 T1'))) h <
        PrI (iand H1 H2) h := by
  have lo := th_16_r031 H1 H1' T1 T1' H2 H2' T2 T2' h L h031
  have lt := th_16_r032 H1 H1' T1 T1' H2 H2' h h033 h034
  have e := def_X_right_i H1 H2 h
  rw [L.h025a] at e
  refine ⟨lo, ?_⟩
  rw [(th_16_r029 H1 H1' T1 T1' H2 H2' T2 T2' h L).2, e]
  linarith

/-- ch16-036 (前提 h036) (folio 171): If h₂/(h₂′, h₁h₁′ + t₁t₁′, h) = ½, then the probability
is exactly ¼ (記法行 ch16-037)。 -/
theorem th_16_r036 (H1 H1' T1 T1' H2 H2' T2 T2' h : IProp)
    (L : LaplaceCoins H1 H1' T1 T1' H2 H2' T2 T2' h)
    (h036 : PrI H2 (iand H2' (iand (ior (iand H1 H1') (iand T1 T1')) h)) = 1 / 2) :
    PrI (iand (ior (iand H2 H2') (iand T2 T2')) (ior (iand H1 H1') (iand T1 T1'))) h =
      1 / 4 := by
  rw [(th_16_r029 H1 H1' T1 T1' H2 H2' T2 T2' h L).2, h036]
  norm_num

/-! ## §10 (folio 172–174) — Maxwell の速度分布

X(x), Y(y), Z(z), V(v) は「軸 X 方向の速度成分が x」等の命題 (ℝ で添字付けた IProp)、
φ は確率の関数。X(x)Y(y)Z(z) は `iand (X x) (iand (Y y) (Z z))`。 -/

/-- v = √(x² + y² + z²) のとき v² = x² + y² + z² (th_16_r057 の補題)。
ch16-046 (folio 172) の「where v² = …」は名付けの行で、台帳では未 (定義のみ)。 -/
theorem th_16_r046 (x y z : ℝ) :
    (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- ch16-057 (folio 173): where v² = x² + y² + z² (再掲; 非負の v は一意に定まる)。 -/
theorem th_16_r057 (x y z : ℝ) :
    ∃! v : ℝ, 0 ≤ v ∧ v ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
  refine ⟨Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2), ⟨Real.sqrt_nonneg _, th_16_r046 x y z⟩, ?_⟩
  rintro w ⟨hw0, hw⟩
  rw [← hw, Real.sqrt_sq hw0]

/-- ch16-050 (前提 h050)、ch16-051 (folio 173): Then if X(x)/h = φ(x) it is a justifiable
inference from the Principle of Indifference that Y(y)/h = φ(y)。Principle of Indifference
を軸の対称 Y(t)/h = X(t)/h の前提 hPI で書く。 -/
theorem th_16_r051 (X Y : ℝ → IProp) (φ : ℝ → ℝ) (h : IProp) (y : ℝ)
    (hPI : PrI (Y y) h = PrI (X y) h) (h050 : ∀ t, PrI (X t) h = φ t) :
    PrI (Y y) h = φ y := by
  rw [hPI, h050]

/-- ch16-052 (folio 173): and Z(z)/h = φ(z) (同上)。 -/
theorem th_16_r052 (X Z : ℝ → IProp) (φ : ℝ → ℝ) (h : IProp) (z : ℝ)
    (hPI : PrI (Z z) h = PrI (X z) h) (h050 : ∀ t, PrI (X t) h = φ t) :
    PrI (Z z) h = φ z := by
  rw [hPI, h050]

/-- ch16-050–052・054・055 (前提)、ch16-053 (folio 173): Maxwell infers from this that
X(x)Y(y)Z(z)/h = φ(x)φ(y)φ(z)。That is to say, he assumes that Y(y)/X(x) . h = Y(y)/h and
that Z(z)/Y(y) . X(x) . h = Z(z)/h。 -/
theorem th_16_r053 (X Y Z : ℝ → IProp) (φ : ℝ → ℝ) (h : IProp) (x y z : ℝ)
    (h050 : PrI (X x) h = φ x) (h051 : PrI (Y y) h = φ y) (h052 : PrI (Z z) h = φ z)
    (h054 : PrI (Y y) (iand (X x) h) = PrI (Y y) h)
    (h055 : PrI (Z z) (iand (Y y) (iand (X x) h)) = PrI (Z z) h) :
    PrI (iand (X x) (iand (Y y) (Z z))) h = φ x * φ y * φ z := by
  rw [def_X_right_i (X x) (iand (Y y) (Z z)) h, def_X_right_i (Y y) (Z z) (iand (X x) h),
    h055, h054, h050, h051, h052]
  ring

/-- ch16-045 (folio 172): Thus if F(v) represents the probability of a total velocity v, we
have φ(x)φ(y)φ(z) = F(v) (Maxwell の推論を前提 054・055・056 付きで)。「where
v² = x² + y² + z²」(ch16-046) は v の名付けで、この等式の導出には使わないので前提に置かない。 -/
theorem th_16_r045 (X Y Z V : ℝ → IProp) (φ F : ℝ → ℝ) (h : IProp) (x y z v : ℝ)
    (h050 : PrI (X x) h = φ x) (h051 : PrI (Y y) h = φ y) (h052 : PrI (Z z) h = φ z)
    (h054 : PrI (Y y) (iand (X x) h) = PrI (Y y) h)
    (h055 : PrI (Z z) (iand (Y y) (iand (X x) h)) = PrI (Z z) h)
    (h056 : PrI (iand (X x) (iand (Y y) (Z z))) h = PrI (V v) h)
    (hF : F v = PrI (V v) h) :
    φ x * φ y * φ z = F v := by
  rw [← th_16_r053 X Y Z φ h x y z h050 h051 h052 h054 h055, h056, hF]

/-- ch16-056 (folio 173) の分解: V(v) が X(x)Y(y)Z(z) から従う (「The latter follows from
the former」: V(v)/X(x)Y(y)Z(z)h = 1) とき、X(x)Y(y)Z(z)/h = V(v)/h は
V(v)·¬(X(x)Y(y)Z(z))/h = 0 と同値。 -/
theorem th_16_r056_iff (X Y Z V : ℝ → IProp) (h : IProp) (x y z v : ℝ)
    (hfol : PrI (V v) (iand (iand (X x) (iand (Y y) (Z z))) h) = 1) :
    PrI (iand (X x) (iand (Y y) (Z z))) h = PrI (V v) h ↔
      PrI (iand (V v) (inot (iand (X x) (iand (Y y) (Z z))))) h = 0 := by
  have e1 := def_X_left_i (V v) (iand (X x) (iand (Y y) (Z z))) h
  have e2 := def_IX_i (V v) (iand (X x) (iand (Y y) (Z z))) h
  rw [hfol, one_mul] at e1
  constructor <;> intro H <;> linarith

/-- ch16-056 (folio 173) に対して: X(x)Y(y)Z(z)/h ≤ V(v)/h (台帳は未、所見候補の材料;
ch16-060 の定理で使う)。 -/
theorem th_16_r056_le (X Y Z V : ℝ → IProp) (h : IProp) (x y z v : ℝ)
    (hfol : PrI (V v) (iand (iand (X x) (iand (Y y) (Z z))) h) = 1) :
    PrI (iand (X x) (iand (Y y) (Z z))) h ≤ PrI (V v) h := by
  have e1 := def_X_left_i (V v) (iand (X x) (iand (Y y) (Z z))) h
  have e2 := def_IX_i (V v) (iand (X x) (iand (Y y) (Z z))) h
  have lo := ax_range_lo_i (iand (V v) (inot (iand (X x) (iand (Y y) (Z z))))) h
  rw [hfol, one_mul] at e1
  linarith

/-- ch16-056 (folio 173) の反駁: 「There is more than one set of values x, y, z which will
yield the same value v」(V(v)·¬(X(x)Y(y)Z(z))/h > 0) のとき、Maxwell の
X(x)Y(y)Z(z)/h = V(v)/h は成り立たない (他の著者の式の反駁; 台帳は未、所見候補の材料)。 -/
theorem th_16_r056_fails (X Y Z V : ℝ → IProp) (h : IProp) (x y z v : ℝ)
    (hfol : PrI (V v) (iand (iand (X x) (iand (Y y) (Z z))) h) = 1)
    (hpos : 0 < PrI (iand (V v) (inot (iand (X x) (iand (Y y) (Z z))))) h) :
    PrI (iand (X x) (iand (Y y) (Z z))) h ≠ PrI (V v) h := by
  intro H
  have := (th_16_r056_iff X Y Z V h x y z v hfol).mp H
  linarith

/-- ch16-059 (folio 174): Thus the probability V(v)/h is much greater than the probability
X(x)Y(y)Z(z)/h (「much greater」を > で)。 -/
theorem th_16_r059 (X Y Z V : ℝ → IProp) (h : IProp) (x y z v : ℝ)
    (hfol : PrI (V v) (iand (iand (X x) (iand (Y y) (Z z))) h) = 1)
    (hpos : 0 < PrI (iand (V v) (inot (iand (X x) (iand (Y y) (Z z))))) h) :
    PrI (V v) h > PrI (iand (X x) (iand (Y y) (Z z))) h := by
  have e1 := def_X_left_i (V v) (iand (X x) (iand (Y y) (Z z))) h
  have e2 := def_IX_i (V v) (iand (X x) (iand (Y y) (Z z))) h
  rw [hfol, one_mul] at e1
  linarith

/-- ch16-060 (前提 h060) (folio 174): it is a legitimate extension of the preceding argument
to put V(v)/h = φ(v)。このとき (053 の前提のもとで) φ(x)φ(y)φ(z) ≤ φ(v) で、Maxwell の
等式 φ(x)φ(y)φ(z) = φ(v) は出ない。 -/
theorem th_16_r060 (X Y Z V : ℝ → IProp) (φ : ℝ → ℝ) (h : IProp) (x y z v : ℝ)
    (h050 : PrI (X x) h = φ x) (h051 : PrI (Y y) h = φ y) (h052 : PrI (Z z) h = φ z)
    (h054 : PrI (Y y) (iand (X x) h) = PrI (Y y) h)
    (h055 : PrI (Z z) (iand (Y y) (iand (X x) h)) = PrI (Z z) h)
    (hfol : PrI (V v) (iand (iand (X x) (iand (Y y) (Z z))) h) = 1)
    (h060 : PrI (V v) h = φ v) :
    φ x * φ y * φ z ≤ φ v := by
  rw [← th_16_r053 X Y Z φ h x y z h050 h051 h052 h054 h055, ← h060]
  exact th_16_r056_le X Y Z V h x y z v hfol

/-! ## §12 (folio 176) — Bayes の規則 -/

/-- ch16-063 (folio 176): this corresponds to ab/h = a/bh . b/h (Def. X)。 -/
theorem th_16_r063 (a b h : IProp) : PrI (iand a b) h = PrI a (iand b h) * PrI b h :=
  def_X_left_i a b h

/-- ch16-064 (folio 176): and therefore a/bh = ab/h ÷ b/h (公理 (i) の但し書き Cons (b∧h))。 -/
theorem th_16_r064 (a b h : IProp) (hcb : Cons (iand b h)) :
    PrI a (iand b h) = PrI (iand a b) h / PrI b h := by
  have hb := cons_of_pos_src b h hcb
  rw [eq_div_iff hb, th_16_r063]

/-- ch16-065・ch16-066 (前提)、ch16-067 (folio 176): for ab/h = P/N, b/h = b/N, a/bh = P/b
(Bayes の値 b を bN と書く)。 -/
theorem th_16_r067 (a b h : IProp) (P N bN : ℝ) (hcb : Cons (iand b h))
    (h065 : PrI (iand a b) h = P / N) (h066 : PrI b h = bN / N) :
    PrI a (iand b h) = P / bN := by
  have hb := cons_of_pos_src b h hcb
  have hN : N ≠ 0 := by
    intro hN
    rw [hN, div_zero] at h066
    exact hb h066
  have hbN : bN ≠ 0 := by
    intro hbN
    rw [hbN, zero_div] at h066
    exact hb h066
  rw [th_16_r064 a b h hcb, h065, h066]
  field_simp

/-! ## §13 (folio 177) — Donkin の原理 -/

/-- ch16-070・ch16-071 (前提)、ch16-072 (folio 177): p′ᵣ = hᵣ/aa′ = hᵣa′/a ÷ a′/a
= (a′/hᵣa . pᵣ) ÷ a′/a (連鎖の各段を連言で)。前提 aa′ は Def. X の形 a′∧a で書く。 -/
theorem th_16_r072 (a a' hr : IProp) (pr pr' : ℝ) (hca : Cons (iand a' a))
    (h070 : PrI hr a = pr) (h071 : PrI hr (iand a' a) = pr') :
    pr' = PrI hr (iand a' a) ∧
      PrI hr (iand a' a) = PrI (iand hr a') a / PrI a' a ∧
      PrI (iand hr a') a / PrI a' a = PrI a' (iand hr a) * pr / PrI a' a := by
  have ha := cons_of_pos_src a' a hca
  refine ⟨h071.symm, ?_, ?_⟩
  · rw [eq_div_iff ha, def_X_left_i hr a' a]
  · rw [def_X_right_i hr a' a, h070]

/-- ch16-074 (前提 h074)、ch16-073 (folio 177): ∴ p′ᵣ/pᵣ = p′ₛ/pₛ, if a′/hᵣa = a′/hₛa。 -/
theorem th_16_r073 (a a' hr hs : IProp) (pr pr' ps ps' : ℝ) (hca : Cons (iand a' a))
    (h070r : PrI hr a = pr) (h071r : PrI hr (iand a' a) = pr')
    (h070s : PrI hs a = ps) (h071s : PrI hs (iand a' a) = ps')
    (h074 : PrI a' (iand hr a) = PrI a' (iand hs a)) (hpr : pr ≠ 0) (hps : ps ≠ 0) :
    pr' / pr = ps' / ps := by
  have ha := cons_of_pos_src a' a hca
  obtain ⟨r1, r2, r3⟩ := th_16_r072 a a' hr pr pr' hca h070r h071r
  obtain ⟨s1, s2, s3⟩ := th_16_r072 a a' hs ps ps' hca h070s h071s
  rw [r1, r2, r3, s1, s2, s3, h074]
  field_simp

/-! ## §14 (folio 178) — (38·2) で事前確率が消える場合 -/

/-- ch16-075 (前提 p₁ = p₂) (folio 178): the à priori probabilities of the hypotheses a₁ and
a₂ drop out if p₁ = p₂。(38.1) の前提 (a₁/h = p₁, a₂/h = p₂, b/a₁h = q₁, b/a₂h = q₂,
a₁/bh + a₂/bh = 1) と Cons (b∧h) のもとで a₁/bh = q₁/(q₁ + q₂)、a₂/bh = q₂/(q₁ + q₂)。 -/
theorem th_16_r075 (a1 a2 b h : IProp) (p1 p2 q1 q2 : ℝ)
    (hp1 : PrI a1 h = p1) (hp2 : PrI a2 h = p2)
    (hq1 : PrI b (iand a1 h) = q1) (hq2 : PrI b (iand a2 h) = q2)
    (hsum : PrI a1 (iand b h) + PrI a2 (iand b h) = 1) (hcb : Cons (iand b h))
    (h075 : p1 = p2) (hp : p1 ≠ 0) :
    PrI a1 (iand b h) = q1 / (q1 + q2) ∧ PrI a2 (iand b h) = q2 / (q1 + q2) := by
  have hB := cons_of_pos_src b h hcb
  have s1 : PrI a1 (iand b h) * PrI b h = q1 * p1 := by
    rw [← def_X_left_i a1 b h, def_X_right_i a1 b h, hq1, hp1]
  have s2 : PrI a2 (iand b h) * PrI b h = q2 * p1 := by
    rw [← def_X_left_i a2 b h, def_X_right_i a2 b h, hq2, hp2, h075]
  have sB : PrI b h = p1 * (q1 + q2) := by
    have : PrI b h = PrI a1 (iand b h) * PrI b h + PrI a2 (iand b h) * PrI b h := by
      rw [← add_mul, hsum, one_mul]
    linarith
  have hq : q1 + q2 ≠ 0 := by
    intro hq
    rw [hq, mul_zero] at sB
    exact hB sB
  rw [sB] at s1 s2
  constructor
  · rw [eq_div_iff hq]
    apply mul_left_cancel₀ hp
    linear_combination s1
  · rw [eq_div_iff hq]
    apply mul_left_cancel₀ hp
    linear_combination s2

/-! ## §15 (folio 180) — Boole の例 -/

/-- ch16-085 (folio 180) の名付け: h₁ = A is black and B is black or white
(Ab = A is black、Bb・Bw = B is black・white; 定義のみ、台帳は未)。 -/
noncomputable def boole_h₁ (Ab Bb Bw : IProp) : IProp := iand Ab (ior Bb Bw)

/-- ch16-086 (folio 180) の名付け: h₂ = B is black and A is black or white (定義のみ)。 -/
noncomputable def boole_h₂ (Ab Bb Aw : IProp) : IProp := iand Bb (ior Ab Aw)

/-- ch16-087 (folio 180) の名付け: a = both A and B are black (定義のみ)。 -/
noncomputable def boole_a (Ab Bb : IProp) : IProp := iand Ab Bb

/-- ch16-084 (folio 180) に対して: この例では a/h₁h₂ = 1 (背景の資料 k を足し、
Cons k、Cons (h₂∧k)、Cons (h₁∧h₂∧k) のもとで; 台帳は未、所見候補の材料)。 -/
theorem th_16_r084 (Ab Bb Aw Bw k : IProp) (hk : Cons k)
    (hc2 : Cons (iand (boole_h₂ Ab Bb Aw) k))
    (hc12 : Cons (iand (boole_h₁ Ab Bb Bw) (iand (boole_h₂ Ab Bb Aw) k))) :
    PrI (boole_a Ab Bb) (iand (boole_h₁ Ab Bb Bw) (iand (boole_h₂ Ab Bb Aw) k)) = 1 := by
  unfold boole_h₁ boole_h₂ boole_a at *
  have z : PrI (iand (iand (iand Ab (ior Bb Bw)) (inot (iand Ab Bb))) (iand Bb (ior Ab Aw)))
      k = 0 :=
    taut_neg_zero
      (Form.conj (Form.conj (Form.conj (Form.var 0) (Form.disj (Form.var 1) (Form.var 2)))
          (Form.neg (Form.conj (Form.var 0) (Form.var 1))))
        (Form.conj (Form.var 1) (Form.disj (Form.var 0) (Form.var 3))))
      (fun n => match n with | 0 => Ab | 1 => Bb | 2 => Bw | _ => Aw) k hk
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            cases h3 : v 3 <;> simp [evalB, h0, h1, h2, h3])
  have e := def_X_left_i (iand (iand Ab (ior Bb Bw)) (inot (iand Ab Bb)))
    (iand Bb (ior Ab Aw)) k
  have hh2 := cons_of_pos_src _ k hc2
  rw [z] at e
  have z2 := (mul_eq_zero.mp e.symm).resolve_right hh2
  have i := def_IX_i (iand Ab (ior Bb Bw)) (iand Ab Bb) (iand (iand Bb (ior Ab Aw)) k)
  have x := def_X_right_i (iand Ab (ior Bb Bw)) (iand Ab Bb) (iand (iand Bb (ior Ab Aw)) k)
  have hh1 := cons_of_pos_src _ _ hc12
  have s : PrI (iand (iand Ab (ior Bb Bw)) (iand Ab Bb)) (iand (iand Bb (ior Ab Aw)) k) =
      PrI (iand Ab (ior Bb Bw)) (iand (iand Bb (ior Ab Aw)) k) := by linarith
  rw [s] at x
  exact mul_right_cancel₀ hh1 (by rw [one_mul]; exact x.symm)

/-- ch16-084 の反駁 (folio 180): If, that is to say, a/h₁ = ½ and a/h₂ = ½, he concludes
that a/h₁h₂ = ½。この例では a/h₁h₂ = ½ は成り立たない (背景の資料 k を足した形)。
反駁は a/h₁ と a/h₂ の値 (ch16-082・083) に依らないので、それらを前提に置かない
(他の著者の式の反駁; 台帳は 082–084 とも未、所見候補の材料)。 -/
theorem th_16_r084_fails (Ab Bb Aw Bw k : IProp) (hk : Cons k)
    (hc2 : Cons (iand (boole_h₂ Ab Bb Aw) k))
    (hc12 : Cons (iand (boole_h₁ Ab Bb Bw) (iand (boole_h₂ Ab Bb Aw) k))) :
    PrI (boole_a Ab Bb) (iand (boole_h₁ Ab Bb Bw) (iand (boole_h₂ Ab Bb Aw) k)) ≠ 1 / 2 := by
  rw [th_16_r084 Ab Bb Aw Bw k hk hc2 hc12]
  norm_num

/-! ## §16 (folio 181) — 二人の証人 (共謀なし)

a₁ = 「X₁ asserts a」、b₂ = 「X₂ asserts b」。前提 a₁b₂h は `iand a1 (iand b2 h)`。 -/

/-- ch16-091・ch16-092・ch16-096・ch16-097 (前提)、ch16-093 (folio 181):
ab/a₁b₂h = a/a₁h . b/b₂h = x₁x₂ (連鎖を連言で)。成り立つのは a/a₁bb₂h = a/a₁h かつ
b/a₁b₂h = b/b₂h のとき (本文の「unless」の条件を前提に置く)。 -/
theorem th_16_r093 (a b a1 b2 h : IProp) (x1 x2 : ℝ)
    (h091 : PrI a (iand a1 h) = x1) (h092 : PrI b (iand b2 h) = x2)
    (h096 : PrI a (iand b (iand a1 (iand b2 h))) = PrI a (iand a1 h))
    (h097 : PrI b (iand a1 (iand b2 h)) = PrI b (iand b2 h)) :
    PrI (iand a b) (iand a1 (iand b2 h)) = PrI a (iand a1 h) * PrI b (iand b2 h) ∧
      PrI (iand a b) (iand a1 (iand b2 h)) = x1 * x2 := by
  have e : PrI (iand a b) (iand a1 (iand b2 h)) = PrI a (iand a1 h) * PrI b (iand b2 h) := by
    rw [def_X_left_i a b (iand a1 (iand b2 h)), h096, h097]
  exact ⟨e, by rw [e, h091, h092]⟩

/-- ch16-094 (folio 181): But ab/a₁b₂h = a/a₁bb₂h . b/a₁b₂h (Def. X; 前提 a₁bb₂h は
b∧(a₁∧(b₂∧h)))。 -/
theorem th_16_r094 (a b a1 b2 h : IProp) :
    PrI (iand a b) (iand a1 (iand b2 h)) =
      PrI a (iand b (iand a1 (iand b2 h))) * PrI b (iand a1 (iand b2 h)) :=
  def_X_left_i _ _ _

/-- ch16-098 (folio 181): In the one extreme case, where the assertions of the two contradict
one another, ab/a₁b₂h = 0 (「contradict」を b = ā で)。 -/
theorem th_16_r098 (a b a1 b2 h : IProp) (hK : Cons (iand a1 (iand b2 h)))
    (hb : b = inot a) :
    PrI (iand a b) (iand a1 (iand b2 h)) = 0 := by
  rw [hb]
  exact taut_neg_zero (Form.conj (Form.var 0) (Form.neg (Form.var 0))) (fun _ => a) _ hK
    (by intro v; cases h0 : v 0 <;> simp [evalB, h0])

/-- ch16-099 (前提 h099)、ch16-100 (folio 181): where the two agree in the same assertion, i.e.
where a ≡ b, a/a₁bb₂h = 1 (≡ を (a ≡ b)/a₁b₂h = 1、Def. VIII で)。 -/
theorem th_16_r100 (a b a1 b2 h : IProp)
    (hca : Cons (iand a (iand a1 (iand b2 h)))) (hcb : Cons (iand b (iand a1 (iand b2 h))))
    (h099 : PrI (iiff a b) (iand a1 (iand b2 h)) = 1) :
    PrI a (iand b (iand a1 (iand b2 h))) = 1 :=
  ((def_VIII_i a b _ hca hcb).mp h099).2

/-- ch16-101 (folio 181): and not = a/a₁h (a/a₁h = x₁ ≠ 1 のとき)。 -/
theorem th_16_r101 (a b a1 b2 h : IProp) (x1 : ℝ)
    (hca : Cons (iand a (iand a1 (iand b2 h)))) (hcb : Cons (iand b (iand a1 (iand b2 h))))
    (h099 : PrI (iiff a b) (iand a1 (iand b2 h)) = 1)
    (h091 : PrI a (iand a1 h) = x1) (hx1 : x1 ≠ 1) :
    PrI a (iand b (iand a1 (iand b2 h))) ≠ PrI a (iand a1 h) := by
  rw [th_16_r100 a b a1 b2 h hca hcb h099, h091]
  exact fun H => hx1 H.symm

/-! ## §17 (folio 181–182) — 証人の一致

aᵢ = 「Xᵢ asserts a」、mᵢ = 「Xᵢ gives the correct answer」(原子)。第 1 の証人の前提
a₁h は `iand A1 h`、a₁a₂h は Def. X の形 `iand A2 (iand A1 h)` で書く。 -/

/-- ch16-102 (folio 181) の名付け: aᵢ = “Xᵢ asserts a in reply to the question”
(`asserts i a` を原子とする; 定義のみ、台帳は未)。 -/
noncomputable def wit_a (asserts : ℕ → IProp → IProp) (a : IProp) (i : ℕ) : IProp :=
  asserts i a

/-- ch16-103 (folio 181) の名付け: mᵢ = “Xᵢ gives the correct answer to the question.”
(定義のみ、台帳は未)。 -/
noncomputable def wit_m (correct : ℕ → IProp) (i : ℕ) : IProp := correct i

/-- ch16-105 (folio 181): m₁/a₁a₂h = m₁m₂/a₁a₂h = m₂/a₁a₂h (連鎖を連言で)。前提は
「the witnesses agree」と 107 から本文が得る m₂/m₁a₁a₂h = 1、m₁/m₂a₁a₂h = 1。 -/
theorem th_16_r105 (m1 m2 A1 A2 h : IProp)
    (hm12 : PrI m2 (iand m1 (iand A1 (iand A2 h))) = 1)
    (hm21 : PrI m1 (iand m2 (iand A1 (iand A2 h))) = 1) :
    PrI m1 (iand A1 (iand A2 h)) = PrI (iand m1 m2) (iand A1 (iand A2 h)) ∧
      PrI (iand m1 m2) (iand A1 (iand A2 h)) = PrI m2 (iand A1 (iand A2 h)) := by
  have e1 := def_X_right_i m1 m2 (iand A1 (iand A2 h))
  have e2 := def_X_left_i m1 m2 (iand A1 (iand A2 h))
  rw [hm12, one_mul] at e1
  rw [hm21, one_mul] at e2
  exact ⟨e1.symm, e2⟩

/-- ch16-107 (前提)、ch16-106 (folio 181): a/aᵢh = mᵢ/aᵢh; 前提 a/aᵢmᵢh = 1 (Lean の前提は
mᵢ∧(aᵢ∧h))、mᵢ/aaᵢh = 1 (「a follows from mᵢaᵢ and mᵢ follows from aaᵢ」)。 -/
theorem th_16_r106 (a A m h : IProp) (h107a : PrI a (iand m (iand A h)) = 1)
    (h107m : PrI m (iand a (iand A h)) = 1) :
    PrI a (iand A h) = PrI m (iand A h) :=
  follows_both a m (iand A h) h107a h107m

/-- ch16-110 (folio 182): a/a₁a₂h = m₁/a₁a₂h = m₁a₂/a₁h ÷ a₂/a₁h (連鎖を連言で;
前提 a₁a₂h を a₂∧(a₁∧h) で)。 -/
theorem th_16_r110 (a A1 A2 m1 h : IProp)
    (hK107a : PrI a (iand m1 (iand A2 (iand A1 h))) = 1)
    (hK107m : PrI m1 (iand a (iand A2 (iand A1 h))) = 1)
    (hA2 : PrI A2 (iand A1 h) ≠ 0) :
    PrI a (iand A2 (iand A1 h)) = PrI m1 (iand A2 (iand A1 h)) ∧
      PrI m1 (iand A2 (iand A1 h)) = PrI (iand m1 A2) (iand A1 h) / PrI A2 (iand A1 h) := by
  refine ⟨follows_both a m1 _ hK107a hK107m, ?_⟩
  rw [eq_div_iff hA2, def_X_left_i m1 A2 (iand A1 h)]

/-- ch16-104・ch16-107 (前提)、ch16-111 の修正形 (folio 182):
= (a₂/a₁m₁h . m₁/a₁h) ÷ (a₂a/a₁h + a₂ā/a₁h)
= (a₂/a₁ah . x₁) ÷ (a₂/a₁ah . x₁ + a₂/a₁āh . (1 − x₁))。
印刷の分母の (1 − x₂) は ā/a₁h = 1 − a/a₁h = 1 − x₁ から (1 − x₁) であるべき
(印刷形は th_16_r111_printed_iff・th_16_r111_model)。連鎖を連言で。 -/
theorem th_16_r111 (a A1 A2 m1 h : IProp) (x1 : ℝ) (hc : Cons (iand A1 h))
    (hA2 : PrI A2 (iand A1 h) ≠ 0)
    (hK107a : PrI a (iand m1 (iand A2 (iand A1 h))) = 1)
    (hK107m : PrI m1 (iand a (iand A2 (iand A1 h))) = 1)
    (h107a : PrI a (iand m1 (iand A1 h)) = 1) (h107m : PrI m1 (iand a (iand A1 h)) = 1)
    (h104 : PrI m1 (iand A1 h) = x1) :
    PrI (iand m1 A2) (iand A1 h) / PrI A2 (iand A1 h) =
        PrI A2 (iand m1 (iand A1 h)) * PrI m1 (iand A1 h) /
          (PrI (iand A2 a) (iand A1 h) + PrI (iand A2 (inot a)) (iand A1 h)) ∧
      PrI a (iand A2 (iand A1 h)) =
        PrI A2 (iand m1 (iand A1 h)) * PrI m1 (iand A1 h) /
          (PrI (iand A2 a) (iand A1 h) + PrI (iand A2 (inot a)) (iand A1 h)) ∧
      PrI a (iand A2 (iand A1 h)) =
        PrI A2 (iand a (iand A1 h)) * x1 /
          (PrI A2 (iand a (iand A1 h)) * x1 +
            PrI A2 (iand (inot a) (iand A1 h)) * (1 - x1)) := by
  obtain ⟨e1, e2⟩ := th_16_r110 a A1 A2 m1 h hK107a hK107m hA2
  have n1 := def_X_right_i m1 A2 (iand A1 h)
  have d1 : PrI A2 (iand A1 h) =
      PrI (iand A2 a) (iand A1 h) + PrI (iand A2 (inot a)) (iand A1 h) := by
    have := def_IX_i A2 a (iand A1 h)
    linarith
  have s1 := conj_subst_mutual m1 a A2 (iand A1 h) hc h107a h107m
  have n2 := def_X_right_i a A2 (iand A1 h)
  have ak := follows_both a m1 (iand A1 h) h107a h107m
  have d2 := def_X_left_i A2 a (iand A1 h)
  have d3 := def_X_left_i A2 (inot a) (iand A1 h)
  have na : PrI (inot a) (iand A1 h) = 1 - PrI a (iand A1 h) := by
    have := th_13_1_i a (iand A1 h) hc
    linarith
  have first : PrI (iand m1 A2) (iand A1 h) / PrI A2 (iand A1 h) =
      PrI A2 (iand m1 (iand A1 h)) * PrI m1 (iand A1 h) /
        (PrI (iand A2 a) (iand A1 h) + PrI (iand A2 (inot a)) (iand A1 h)) := by
    rw [← n1, ← d1]
  have num : PrI (iand m1 A2) (iand A1 h) = PrI A2 (iand a (iand A1 h)) * x1 := by
    rw [s1, n2, ak, h104]
  have den : PrI A2 (iand A1 h) = PrI A2 (iand a (iand A1 h)) * x1 +
      PrI A2 (iand (inot a) (iand A1 h)) * (1 - x1) := by
    rw [d1, d2, d3, na, ak, h104]
  refine ⟨first, by rw [e1, e2, first], ?_⟩
  rw [e1, e2, num, den]

/-- ch16-111 の分母: a₂/a₁h = a₂/a₁ah . x₁ + a₂/a₁āh . (1 − x₁) (Def. IX・X・(1))。 -/
theorem testimony_den (a A1 A2 m1 h : IProp) (x1 : ℝ) (hc : Cons (iand A1 h))
    (h107a : PrI a (iand m1 (iand A1 h)) = 1) (h107m : PrI m1 (iand a (iand A1 h)) = 1)
    (h104 : PrI m1 (iand A1 h) = x1) :
    PrI A2 (iand A1 h) = PrI A2 (iand a (iand A1 h)) * x1 +
      PrI A2 (iand (inot a) (iand A1 h)) * (1 - x1) := by
  have d1 := def_IX_i A2 a (iand A1 h)
  have ak := follows_both a m1 (iand A1 h) h107a h107m
  have na : PrI (inot a) (iand A1 h) = 1 - PrI a (iand A1 h) := by
    have := th_13_1_i a (iand A1 h) hc
    linarith
  rw [← d1, def_X_left_i A2 a (iand A1 h), def_X_left_i A2 (inot a) (iand A1 h), na, ak, h104]
  ring

/-- ch16-111 の印刷形 (分母 (1 − x₂)) の判定 (folio 182): 修正形の前提のもとで、
a₂/a₁ah . x₁ ≠ 0、a₂/a₁āh ≠ 0 ならば、印刷形が成り立つのは x₁ = x₂ のときに限る。 -/
theorem th_16_r111_printed_iff (a A1 A2 m1 h : IProp) (x1 x2 : ℝ) (hc : Cons (iand A1 h))
    (hA2 : PrI A2 (iand A1 h) ≠ 0)
    (hK107a : PrI a (iand m1 (iand A2 (iand A1 h))) = 1)
    (hK107m : PrI m1 (iand a (iand A2 (iand A1 h))) = 1)
    (h107a : PrI a (iand m1 (iand A1 h)) = 1) (h107m : PrI m1 (iand a (iand A1 h)) = 1)
    (h104 : PrI m1 (iand A1 h) = x1)
    (hRx : PrI A2 (iand a (iand A1 h)) * x1 ≠ 0)
    (hS : PrI A2 (iand (inot a) (iand A1 h)) ≠ 0) :
    PrI a (iand A2 (iand A1 h)) =
        PrI A2 (iand a (iand A1 h)) * x1 /
          (PrI A2 (iand a (iand A1 h)) * x1 +
            PrI A2 (iand (inot a) (iand A1 h)) * (1 - x2)) ↔ x1 = x2 := by
  obtain ⟨_, _, e3⟩ := th_16_r111 a A1 A2 m1 h x1 hc hA2 hK107a hK107m h107a h107m h104
  rw [e3]
  have hD1 := testimony_den a A1 A2 m1 h x1 hc h107a h107m h104 ▸ hA2
  set R := PrI A2 (iand a (iand A1 h))
  set S := PrI A2 (iand (inot a) (iand A1 h))
  constructor
  · intro H
    have hD2 : R * x1 + S * (1 - x2) ≠ 0 := by
      intro h0
      rw [h0, div_zero] at H
      exact hRx ((div_eq_zero_iff.mp H).resolve_right hD1)
    rw [div_eq_div_iff hD1 hD2] at H
    have : R * x1 * (S * (x1 - x2)) = 0 := by linear_combination H
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hRx
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hS
      · linarith
  · intro H
    rw [H]

/-! ### ch16-111 の印刷形の数値例 (ℚ 上)

KeynesI の公理系 (IProp・PrI) の模型ではなく、ℚ 上の有限の確率分布での数値例である。
三つの命題 a, a₁, a₂ の 8 世界に有理数の重みを置く (a/h = ½、a₁/ah = ¾、a₁/āh = ¼、
a₂/ah = ⅔、a₂/āh = ⅓、a₁ と a₂ は a のもとでも ā のもとでも独立)。答は a か ā の二つで、
mᵢ ≡ (aᵢ ≡ a)。この模型では 104 (x₁ = ¾, x₂ = ⅔)、106、108・109 (独立) が成り立ち、
a/a₁a₂h = 6/7、修正形の右辺 = 6/7、印刷形の右辺 = 9/11。 -/

/-- 世界 (a, a₁, a₂) の重み。 -/
def mdlW (a a1 a2 : Bool) : ℚ :=
  (1 / 2) * (if a then (if a1 then 3 / 4 else 1 / 4) else (if a1 then 1 / 4 else 3 / 4)) *
    (if a then (if a2 then 2 / 3 else 1 / 3) else (if a2 then 1 / 3 else 2 / 3))

/-- 述語 P の重みの和。 -/
def mdlMass (P : Bool → Bool → Bool → Bool) : ℚ :=
  (if P true true true then mdlW true true true else 0) +
  (if P true true false then mdlW true true false else 0) +
  (if P true false true then mdlW true false true else 0) +
  (if P true false false then mdlW true false false else 0) +
  (if P false true true then mdlW false true true else 0) +
  (if P false true false then mdlW false true false else 0) +
  (if P false false true then mdlW false false true else 0) +
  (if P false false false then mdlW false false false else 0)

/-- 条件付きの確率 P/Q。 -/
def mdlPr (P Q : Bool → Bool → Bool → Bool) : ℚ :=
  mdlMass (fun a a1 a2 => P a a1 a2 && Q a a1 a2) / mdlMass Q

/-- ch16-111 の印刷形の反例 (ℚ 上の数値例、KeynesI の模型ではない; folio 182):
x₁ = m₁/a₁h = ¾、x₂ = m₂/a₂h = ⅔、
a/aᵢh = mᵢ/aᵢh、独立 108・109 が成り立ち、a/a₁a₂h = 6/7 = 修正形の右辺、印刷形の右辺 = 9/11。
第 8・第 9 連言の a₂/a₁ah・a₂/a₁āh・x₁・x₂ は模型の mdlPr から計算する。 -/
theorem th_16_r111_model :
    mdlPr (fun a a1 _ => a1 == a) (fun _ a1 _ => a1) = 3 / 4 ∧
    mdlPr (fun a _ a2 => a2 == a) (fun _ _ a2 => a2) = 2 / 3 ∧
    mdlPr (fun a _ _ => a) (fun _ a1 _ => a1) = 3 / 4 ∧
    mdlPr (fun a _ _ => a) (fun _ _ a2 => a2) = 2 / 3 ∧
    mdlPr (fun _ _ a2 => a2) (fun a a1 _ => a && a1) = mdlPr (fun _ _ a2 => a2) (fun a _ _ => a) ∧
    mdlPr (fun _ _ a2 => a2) (fun a a1 _ => !a && a1) =
      mdlPr (fun _ _ a2 => a2) (fun a _ _ => !a) ∧
    mdlPr (fun a _ _ => a) (fun _ a1 a2 => a1 && a2) = 6 / 7 ∧
    mdlPr (fun _ _ a2 => a2) (fun a a1 _ => a && a1) *
        mdlPr (fun a a1 _ => a1 == a) (fun _ a1 _ => a1) /
        (mdlPr (fun _ _ a2 => a2) (fun a a1 _ => a && a1) *
            mdlPr (fun a a1 _ => a1 == a) (fun _ a1 _ => a1) +
          mdlPr (fun _ _ a2 => a2) (fun a a1 _ => !a && a1) *
            (1 - mdlPr (fun a a1 _ => a1 == a) (fun _ a1 _ => a1))) = 6 / 7 ∧
    mdlPr (fun _ _ a2 => a2) (fun a a1 _ => a && a1) *
        mdlPr (fun a a1 _ => a1 == a) (fun _ a1 _ => a1) /
        (mdlPr (fun _ _ a2 => a2) (fun a a1 _ => a && a1) *
            mdlPr (fun a a1 _ => a1 == a) (fun _ a1 _ => a1) +
          mdlPr (fun _ _ a2 => a2) (fun a a1 _ => !a && a1) *
            (1 - mdlPr (fun a _ a2 => a2 == a) (fun _ _ a2 => a2))) = 9 / 11 ∧
    (6 / 7 : ℚ) ≠ 9 / 11 := by
  simp only [mdlPr, mdlMass, mdlW]
  norm_num

/-- ch16-112 (記法) と ch16-113 (folio 182): If this is to be equal to
x₁x₂ ÷ (x₁x₂ + (1 − x₁)(1 − x₂)), we must have a₂/a₁ah ÷ a₂/a₁āh = x₂ ÷ (1 − x₂)
(修正形 th_16_r111 のもとで ↔; 0 < x₁, x₂ < 1、a₂/a₁ah, a₂/a₁āh > 0)。 -/
theorem th_16_r113 (a A1 A2 m1 h : IProp) (x1 x2 : ℝ) (hc : Cons (iand A1 h))
    (hA2 : PrI A2 (iand A1 h) ≠ 0)
    (hK107a : PrI a (iand m1 (iand A2 (iand A1 h))) = 1)
    (hK107m : PrI m1 (iand a (iand A2 (iand A1 h))) = 1)
    (h107a : PrI a (iand m1 (iand A1 h)) = 1) (h107m : PrI m1 (iand a (iand A1 h)) = 1)
    (h104 : PrI m1 (iand A1 h) = x1)
    (hx1 : 0 < x1) (hx1' : x1 < 1) (hx2 : 0 < x2) (hx2' : x2 < 1)
    (hR : 0 < PrI A2 (iand a (iand A1 h))) (hS : 0 < PrI A2 (iand (inot a) (iand A1 h))) :
    PrI a (iand A2 (iand A1 h)) = x1 * x2 / (x1 * x2 + (1 - x1) * (1 - x2)) ↔
      PrI A2 (iand a (iand A1 h)) / PrI A2 (iand (inot a) (iand A1 h)) = x2 / (1 - x2) := by
  rw [(th_16_r111 a A1 A2 m1 h x1 hc hA2 hK107a hK107m h107a h107m h104).2.2]
  set R := PrI A2 (iand a (iand A1 h))
  set S := PrI A2 (iand (inot a) (iand A1 h))
  have p1 : 0 < 1 - x1 := by linarith
  have p2 : 0 < 1 - x2 := by linarith
  have d1 : R * x1 + S * (1 - x1) ≠ 0 := by positivity
  have d2 : x1 * x2 + (1 - x1) * (1 - x2) ≠ 0 := by positivity
  rw [div_eq_div_iff d1 d2, div_eq_div_iff hS.ne' p2.ne']
  have key : R * x1 * (x1 * x2 + (1 - x1) * (1 - x2)) - x1 * x2 * (R * x1 + S * (1 - x1)) =
      x1 * (1 - x1) * (R * (1 - x2) - x2 * S) := by ring
  have hx : x1 * (1 - x1) ≠ 0 := by positivity
  constructor
  · intro H
    have : x1 * (1 - x1) * (R * (1 - x2) - x2 * S) = 0 := by rw [← key]; linarith
    have := (mul_eq_zero.mp this).resolve_left hx
    linarith
  · intro H
    have : x1 * (1 - x1) * (R * (1 - x2) - x2 * S) = 0 := by
      rw [show R * (1 - x2) - x2 * S = 0 by linarith, mul_zero]
    linarith

/-- ch16-108・ch16-109 (前提)、ch16-114 (folio 182): Now a₂/a₁ah ÷ a₂/a₁āh = a₂/ah ÷ a₂/āh
by the hypothesis of “independence” (a₂/a₁ah = a₂/ah、a₂/a₁āh = a₂/āh)。 -/
theorem th_16_r114 (a A1 A2 h : IProp)
    (h108 : PrI A2 (iand a (iand A1 h)) = PrI A2 (iand a h))
    (h109 : PrI A2 (iand (inot a) (iand A1 h)) = PrI A2 (iand (inot a) h)) :
    PrI A2 (iand a (iand A1 h)) / PrI A2 (iand (inot a) (iand A1 h)) =
      PrI A2 (iand a h) / PrI A2 (iand (inot a) h) := by
  rw [h108, h109]

/-- ch16-115 (folio 182): = (aa₂/h ÷ āa₂/h) . (ā/h ÷ a/h) = (a/a₂h ÷ ā/a₂h) . (ā/h ÷ a/h)
(連鎖の各段を連言で; 除法の但し書き ≠ 0)。 -/
theorem th_16_r115 (a A2 h : IProp) (hu : PrI a h ≠ 0) (hw : PrI (inot a) h ≠ 0)
    (hs : PrI A2 h ≠ 0) (hS : PrI A2 (iand (inot a) h) ≠ 0)
    (hQ : PrI (inot a) (iand A2 h) ≠ 0) :
    PrI A2 (iand a h) / PrI A2 (iand (inot a) h) =
        (PrI (iand a A2) h / PrI (iand (inot a) A2) h) * (PrI (inot a) h / PrI a h) ∧
      (PrI (iand a A2) h / PrI (iand (inot a) A2) h) * (PrI (inot a) h / PrI a h) =
        (PrI a (iand A2 h) / PrI (inot a) (iand A2 h)) * (PrI (inot a) h / PrI a h) := by
  constructor
  · rw [def_X_right_i a A2 h, def_X_right_i (inot a) A2 h]
    field_simp
  · rw [def_X_left_i a A2 h, def_X_left_i (inot a) A2 h]
    field_simp

/-- ch16-104・ch16-107 (前提、i = 2)、ch16-116 (folio 182): = (x₂ ÷ (1 − x₂)) . (ā/h ÷ a/h)
(直前の項との等式と、連鎖の先頭 a₂/a₁ah ÷ a₂/a₁āh との等式)。 -/
theorem th_16_r116 (a A1 A2 m2 h : IProp) (x2 : ℝ) (hc2 : Cons (iand A2 h))
    (h107a : PrI a (iand m2 (iand A2 h)) = 1) (h107m : PrI m2 (iand a (iand A2 h)) = 1)
    (h104 : PrI m2 (iand A2 h) = x2)
    (h108 : PrI A2 (iand a (iand A1 h)) = PrI A2 (iand a h))
    (h109 : PrI A2 (iand (inot a) (iand A1 h)) = PrI A2 (iand (inot a) h))
    (hu : PrI a h ≠ 0) (hw : PrI (inot a) h ≠ 0)
    (hs : PrI A2 h ≠ 0) (hS : PrI A2 (iand (inot a) h) ≠ 0)
    (hQ : PrI (inot a) (iand A2 h) ≠ 0) :
    (PrI a (iand A2 h) / PrI (inot a) (iand A2 h)) * (PrI (inot a) h / PrI a h) =
        (x2 / (1 - x2)) * (PrI (inot a) h / PrI a h) ∧
      PrI A2 (iand a (iand A1 h)) / PrI A2 (iand (inot a) (iand A1 h)) =
        (x2 / (1 - x2)) * (PrI (inot a) h / PrI a h) := by
  have P : PrI a (iand A2 h) = x2 := by
    rw [th_16_r106 a A2 m2 h h107a h107m, h104]
  have Q : PrI (inot a) (iand A2 h) = 1 - x2 := by
    have := th_13_1_i a (iand A2 h) hc2
    linarith
  have e : (PrI a (iand A2 h) / PrI (inot a) (iand A2 h)) * (PrI (inot a) h / PrI a h) =
      (x2 / (1 - x2)) * (PrI (inot a) h / PrI a h) := by rw [P, Q]
  obtain ⟨c1, c2⟩ := th_16_r115 a A2 h hu hw hs hS hQ
  exact ⟨e, by rw [th_16_r114 a A1 A2 h h108 h109, c1, c2, e]⟩

/-- ch16-117 (folio 182): the assumption which has tacitly slipped into the conventional
formula,—that a/h = ā/h = ½。(x₂ ÷ (1 − x₂)) . (ā/h ÷ a/h) = x₂ ÷ (1 − x₂) となるのは
a/h = ā/h = ½ のときに限る (連鎖を連言で)。 -/
theorem th_16_r117 (a h : IProp) (x2 : ℝ) (hc : Cons h) (hu : PrI a h ≠ 0)
    (hx2 : 0 < x2) (hx2' : x2 < 1) :
    (x2 / (1 - x2)) * (PrI (inot a) h / PrI a h) = x2 / (1 - x2) ↔
      PrI a h = 1 / 2 ∧ PrI (inot a) h = 1 / 2 := by
  have na := th_13_1_i a h hc
  have ht : x2 / (1 - x2) ≠ 0 := by
    have : 0 < 1 - x2 := by linarith
    positivity
  constructor
  · intro H
    have H1 : PrI (inot a) h / PrI a h = 1 :=
      mul_left_cancel₀ ht (H.trans (mul_one _).symm)
    rw [div_eq_one_iff_eq hu] at H1
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    norm_num

/-! ## §18 (folio 183) — 証人の信用度の二つの意味

a₁ = 「a is asserted by the witness」、h₁ = 証人の確かさについての資料、h₂ = a の真偽に
ついての他の資料。h₁h₂ は `iand h1 h2`。 -/

/-- ch16-119・ch16-120 (前提)、ch16-121 (folio 183): Let a/a₁h₁ = x₁ and a₁/ah₁ = x₂;
so that x₁ = (a/h₁ ÷ a₁/h₁) . x₂ (除法の但し書き a₁/h₁ ≠ 0)。 -/
theorem th_16_r121 (a a1 h1 : IProp) (x1 x2 : ℝ) (h119 : PrI a (iand a1 h1) = x1)
    (h120 : PrI a1 (iand a h1) = x2) (hA : PrI a1 h1 ≠ 0) :
    x1 = (PrI a h1 / PrI a1 h1) * x2 := by
  have e1 := def_X_left_i a a1 h1
  have e2 := def_X_right_i a a1 h1
  rw [h119] at e1
  rw [h120] at e2
  field_simp
  linarith

/-- ch16-122 (前提 h122) (folio 183): In general a/h₁ ≠ a₁/h₁。このとき (x₂ ≠ 0 なら)
x₁ ≠ x₂ — 「These two things are not equivalent」。 -/
theorem th_16_r122 (a a1 h1 : IProp) (x1 x2 : ℝ) (h119 : PrI a (iand a1 h1) = x1)
    (h120 : PrI a1 (iand a h1) = x2) (hA : PrI a1 h1 ≠ 0) (hx2 : x2 ≠ 0)
    (h122 : PrI a h1 ≠ PrI a1 h1) : x1 ≠ x2 := by
  intro heq
  have e := th_16_r121 a a1 h1 x1 x2 h119 h120 hA
  rw [heq] at e
  have : PrI a h1 / PrI a1 h1 = 1 := by
    have := mul_right_cancel₀ hx2 (e.symm.trans (one_mul x2).symm)
    exact this
  rw [div_eq_one_iff_eq hA] at this
  exact h122 this

/-- ch16-120・ch16-127 (前提)、ch16-125 (folio 183):
a/a₁h₁h₂ = (a₁/ah₁h₂ . a/h₁h₂) ÷ a₁/h₁h₂ = x₂p ÷ (a₁a/h₁h₂ + a₁ā/h₁h₂)
(連鎖の各段を連言で; p = a/h₁h₂、除法の但し書き a₁/h₁h₂ ≠ 0)。 -/
theorem th_16_r125 (a a1 h1 h2 : IProp) (x2 p : ℝ) (hne : PrI a1 (iand h1 h2) ≠ 0)
    (h127 : PrI a1 (iand a (iand h1 h2)) = PrI a1 (iand a h1))
    (h120 : PrI a1 (iand a h1) = x2) (hp : PrI a (iand h1 h2) = p) :
    PrI a (iand a1 (iand h1 h2)) =
        PrI a1 (iand a (iand h1 h2)) * PrI a (iand h1 h2) / PrI a1 (iand h1 h2) ∧
      PrI a1 (iand a (iand h1 h2)) * PrI a (iand h1 h2) / PrI a1 (iand h1 h2) =
        x2 * p / (PrI (iand a1 a) (iand h1 h2) + PrI (iand a1 (inot a)) (iand h1 h2)) := by
  constructor
  · rw [eq_div_iff hne, ← def_X_left_i a a1 (iand h1 h2), def_X_right_i a a1 (iand h1 h2)]
  · have d := def_IX_i a1 a (iand h1 h2)
    rw [h127, h120, hp, show PrI (iand a1 a) (iand h1 h2) +
      PrI (iand a1 (inot a)) (iand h1 h2) = PrI a1 (iand h1 h2) by linarith]

/-- ch16-124・ch16-128 (前提)、ch16-126 (folio 183): = x₂p ÷ (x₂p + a₁/āh₁h₂ . (1 − p))
= x₂p ÷ (x₂p + r(1 − p)); for a₁/ah₁h₂ = a₁/ah₁ and a₁/āh₁h₂ = a₁/āh₁ (連鎖を連言で、
先頭 a/a₁h₁h₂ との等式も)。 -/
theorem th_16_r126 (a a1 h1 h2 : IProp) (x2 p r : ℝ) (hc : Cons (iand h1 h2))
    (hne : PrI a1 (iand h1 h2) ≠ 0)
    (h127 : PrI a1 (iand a (iand h1 h2)) = PrI a1 (iand a h1))
    (h128 : PrI a1 (iand (inot a) (iand h1 h2)) = PrI a1 (iand (inot a) h1))
    (h120 : PrI a1 (iand a h1) = x2) (h124 : PrI a1 (iand (inot a) h1) = r)
    (hp : PrI a (iand h1 h2) = p) :
    x2 * p / (PrI (iand a1 a) (iand h1 h2) + PrI (iand a1 (inot a)) (iand h1 h2)) =
        x2 * p / (x2 * p + PrI a1 (iand (inot a) (iand h1 h2)) * (1 - p)) ∧
      x2 * p / (x2 * p + PrI a1 (iand (inot a) (iand h1 h2)) * (1 - p)) =
        x2 * p / (x2 * p + r * (1 - p)) ∧
      PrI a (iand a1 (iand h1 h2)) = x2 * p / (x2 * p + r * (1 - p)) := by
  have na : PrI (inot a) (iand h1 h2) = 1 - p := by
    have := th_13_1_i a (iand h1 h2) hc
    linarith
  have e1 : PrI (iand a1 a) (iand h1 h2) = x2 * p := by
    rw [def_X_left_i a1 a (iand h1 h2), h127, h120, hp]
  have e2 : PrI (iand a1 (inot a)) (iand h1 h2) =
      PrI a1 (iand (inot a) (iand h1 h2)) * (1 - p) := by
    rw [def_X_left_i a1 (inot a) (iand h1 h2), na]
  have s1 : x2 * p / (PrI (iand a1 a) (iand h1 h2) + PrI (iand a1 (inot a)) (iand h1 h2)) =
      x2 * p / (x2 * p + PrI a1 (iand (inot a) (iand h1 h2)) * (1 - p)) := by
    rw [e1, e2]
  have s2 : x2 * p / (x2 * p + PrI a1 (iand (inot a) (iand h1 h2)) * (1 - p)) =
      x2 * p / (x2 * p + r * (1 - p)) := by
    rw [h128, h124]
  obtain ⟨c1, c2⟩ := th_16_r125 a a1 h1 h2 x2 p hne h127 h120 hp
  exact ⟨s1, s2, by rw [c1, c2, s1, s2]⟩

/-! ## §19 (folio 184) — Johnson の信用度 -/

/-- ch16-129 (folio 184): A's credibility for x as a, where a is given by the equation
x/ah = x/h + a√(x/h . x̄/h) (0 < x/h < 1 のとき信用度 (α と書く) は一意に定まる)。 -/
theorem th_16_r129 (x a h : IProp) (hc : Cons h) (hlo : 0 < PrI x h) (hhi : PrI x h < 1) :
    ∃! α : ℝ, PrI x (iand a h) = PrI x h + α * Real.sqrt (PrI x h * PrI (inot x) h) := by
  have na := th_13_1_i x h hc
  have hs : 0 < Real.sqrt (PrI x h * PrI (inot x) h) :=
    Real.sqrt_pos.mpr (mul_pos hlo (by linarith))
  refine ⟨(PrI x (iand a h) - PrI x h) / Real.sqrt (PrI x h * PrI (inot x) h), ?_, ?_⟩
  · dsimp only
    rw [div_mul_cancel₀ _ hs.ne']
    ring
  · intro β hβ
    rw [eq_div_iff hs.ne']
    linarith

end KeynesI

/-! ## #print axioms (全定理) -/

#print axioms KeynesI.th_16_r003_premissless_fails
#print axioms KeynesI.th_16_r003
#print axioms KeynesI.th_16_r011
#print axioms KeynesI.th_16_r012
#print axioms KeynesI.th_16_r013
#print axioms KeynesI.th_16_r014
#print axioms KeynesI.th_16_r018
#print axioms KeynesI.th_16_r021
#print axioms KeynesI.th_16_r022
#print axioms KeynesI.th_16_r023
#print axioms KeynesI.th_16_r025
#print axioms KeynesI.th_16_r026
#print axioms KeynesI.th_16_r027
#print axioms KeynesI.th_16_r028
#print axioms KeynesI.th_16_r029
#print axioms KeynesI.th_16_r030
#print axioms KeynesI.th_16_r031
#print axioms KeynesI.th_16_r032
#print axioms KeynesI.th_16_r032_nearer
#print axioms KeynesI.th_16_r036
#print axioms KeynesI.th_16_r046
#print axioms KeynesI.th_16_r057
#print axioms KeynesI.th_16_r051
#print axioms KeynesI.th_16_r052
#print axioms KeynesI.th_16_r053
#print axioms KeynesI.th_16_r045
#print axioms KeynesI.th_16_r056_iff
#print axioms KeynesI.th_16_r056_le
#print axioms KeynesI.th_16_r056_fails
#print axioms KeynesI.th_16_r059
#print axioms KeynesI.th_16_r060
#print axioms KeynesI.th_16_r063
#print axioms KeynesI.th_16_r064
#print axioms KeynesI.th_16_r067
#print axioms KeynesI.th_16_r072
#print axioms KeynesI.th_16_r073
#print axioms KeynesI.th_16_r075
#print axioms KeynesI.th_16_r084
#print axioms KeynesI.th_16_r084_fails
#print axioms KeynesI.th_16_r093
#print axioms KeynesI.th_16_r094
#print axioms KeynesI.th_16_r098
#print axioms KeynesI.th_16_r100
#print axioms KeynesI.th_16_r101
#print axioms KeynesI.th_16_r105
#print axioms KeynesI.th_16_r106
#print axioms KeynesI.th_16_r110
#print axioms KeynesI.th_16_r111
#print axioms KeynesI.th_16_r111_printed_iff
#print axioms KeynesI.th_16_r111_model
#print axioms KeynesI.th_16_r113
#print axioms KeynesI.th_16_r114
#print axioms KeynesI.th_16_r115
#print axioms KeynesI.th_16_r116
#print axioms KeynesI.th_16_r117
#print axioms KeynesI.th_16_r121
#print axioms KeynesI.th_16_r122
#print axioms KeynesI.th_16_r125
#print axioms KeynesI.th_16_r126
#print axioms KeynesI.th_16_r129
