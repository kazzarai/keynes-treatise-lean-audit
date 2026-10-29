/- ============================================================
   PHASE 12a — 第3章の順序系列: ℝ 値では比較不能な対が表せないこと、
   および確率集合 Π を半順序の型にした形式化と有限モデル
   (第 I 部, Keynes (1921) Ch. III, folio 37–40; 第 II 部 Ax. (iv.), folio 136)

   出典アンカー (1921 年 Macmillan 初版の頁画像 folio_037–040.png, folio_136.png で照合):
   - folio 37 §17: "one probability C is equal to the sum of two other
     probabilities A and B, i.e. C = A + B. If in such a case A and B are
     equal, then we may write this C = 2A and say that C is double A.
     Similarly if D = C + A, we may write D = 3A, and so on. We can attach a
     meaning, therefore, to the equation P = n.A, where P and A are relations
     of probability, and n is a number. ... if P represents certainty, we
     should say ... that the magnitude of the probability A is 1/n."
   - folio 38 §18: "If we are given two distinct arguments, there is no
     general presumption that their two probabilities and certainty can be
     placed in an order."
   - folio 38 §19 (i.) "Every probability lies on a path between
     impossibility and certainty"; (iv.) "If ABC forms an ordered series,
     B lying between A and C, and BCD forms an ordered series, C lying
     between B and D, then ABCD forms an ordered series, B lying between
     A and D."
   - folio 39 §20: "As there are independent paths there will be some pairs
     of points representing relations of probability such that we cannot
     reach one by moving from the other along a path always in the same
     direction." 図の説明: "V is less than the numerical probability A, and
     is also less than W, X, and Y. X and Y are both greater than W, and
     greater than V, but are not comparable with one another, or with A.
     V and Z are both less than W, X, and Y, but are not comparable with one
     another; U is not quantitatively comparable with any of the
     probabilities V, W, X, Y, Z. ... the numerical path or strand, will be
     represented by OAI."
   - folio 39–40 §21: (i.) "If B is 'between' A and C, ABC form a series."
     (ii.) "If ... A is a probability, OAI form a series." (iii.) "If A lies
     between O and B, we may write this ÂB, so that ÔA and ÂI are true for
     all probabilities." (iv.) "If ÂB, the probability B is said to be
     greater than the probability A, and this can be expressed by B > A."
     (v.) "... this may be written aPh. It may also be written a/h = P."
     "If aPh and a′Ph′ ... this may be written a/h = a′/h′."
   - folio 136 Ax. (iv.): "If P, Q, R are relations of probability such that
     the products PQ, PR and the sums P + Q, P + R exist, then: ...
     (iv. b) PQ < P unless Q = 1 or P = 0; P + Q > P unless Q = 0.
     PQ = P if Q = 1 or P = 0; P + Q = P if Q = 0.
     (iv. c) If PQ ⋛ PR, then Q ⋛ R unless P = 0. If P + Q ⋛ P + R,
     then Q ⋛ R and conversely."

   引用文献:
   - 塩沢 (1983) = 塩沢由典「ケインズ『確率論』の論理構造」『別冊経済セミナー』
     (1983)。頁は phase8dp ヘッダと同じく要裁定。命題集合 Γ・確率集合 Π・
     写像集合 π の区別、埋め込み規則 I/II の出典 (新井 (2011) 修論 3-3-3 が引く)。
   - 高籔・新井 (2011a) = phase8dp ヘッダの書誌。§3.2–3.3 の「線形順序集合／
     半順序集合」「同一シリーズにない確率は比較不可能である」「Keynes「確率」は
     半順序束をなす」、§3.4 の「三項間の順序」(推移律は必ずしも成り立たない)。
   - Ryłow (2026): 反対称性についての指摘 (th_3_antisymm が答える)。
     Ryłow, J. (2026) "Keynes vs. Kolmogorov: Two Axiomatics of Probability",
     Univ. of Warsaw, Faculty of Economic Sciences, Working Papers 8/2026 (502).

   設計:
   段 1 (ℝ 値の形式化): phase6c・phase8dp と同じく命題集合 Γ を不透明型 IProp、
     確率関係を PrI : IProp → IProp → ℝ とする (本ファイルで同文を宣言し直す;
     既存ファイルは触らない)。ℝ は線形順序集合なので、どの二つの確率関係も
     比較でき (th_3_real_total, th_3_real_total_cross)、比較不能な対は存在しない
     (th_3_real_no_incomparable)。前提が異なる対 a/bh と a/h も比較できる
     (th_3_real_rule_I_pair): ℝ 値の PrI は各前提 h の確率集合 Π(h) を一つの
     ℝ に同時に埋め込んでおり、塩沢 (1983) が「一意的な「埋め込み」を決定
     しなければならない」とした問題 (規則 I は a/bh ↦ a/h) を、ℝ への埋め込みで
     先に決めている。この対応づけは定理ではなく読み (要裁定)。
   段 2 (半順序の形式化): 確率集合 Π を型 Deg とし、PartialOrder を公理で与える
     (instPartialOrderDeg)。確率関係は PrO : IProp → IProp → Deg (値域は ℝ で
     ない)。不可能性 O = dO、確実性 I = dI。「y が x と z の間にある」を
     Btw x y z := x ≤ y ∧ y ≤ z (端を含む) と読む。§21 (iii.) の「ÔA と ÂI は
     すべての確率で真」が端を含む読みを要する (A = O で ÔO)。
     数値的確率 (数値経路 OAI) は有理数の集合 numD (0, 1 を含み [0,1] の中) の
     num による像。num は numD 上で順序を保ち順序を映す (ax_3_num_order) ので
     像は全順序な鎖 (th_3_20_strand)。numD を ℚ ∩ [0,1] 全体とは置かない:
     有限モデルの鎖は {0, 1/2, 1} の像である (鎖を ℚ ∩ [0,1] 全体にとった
     無限モデルは本ファイルでは作っていない)。
     比較不能な対の存在 (§20) は確率関係の値の対として置く (ax_3_20_incomp)。
   段 3 (第 II 部 Ax. (iv.) の順序の部分): 加法・乗法は Π 上の部分関数
     padd, pmul : Deg → Deg → Option Deg とし、Ax. (iv.) の「積・和が存在する
     ならば」を前提 padd P Q = some S の形で書く。(iv. b)(iv. c) を Π の上で
     言い直して公理に置く (ax_ivb_*, ax_ivc_*)。⋛ は < = > の 3 成分に分け、
     (iv. c) 加法の "and conversely" は ↔ にした。(iv. a) (交換) は順序に関わら
     ないので公理に置かず、モデルの加法・乗法が満たすことだけを確かめる。

   有限モデル diagram (folio 39 の図): Π = 9 元 {O, A, I, U, V, W, X, Y, Z}。
     順序は O が最小、I が最大、ほかは V < A, V < W, V < X, V < Y, W < X, W < Y,
     Z < W, Z < X, Z < Y だけ (folio 39 の文の大小関係をそのまま置き、推移閉包を
     取ったもの)。数値経路は O, A = num (1/2), I。加法は O + y = y, x + O = x,
     A + A = I、乗法は O·y = O, x·O = O, I·y = y, x·I = x、ほかは未定義 (none)。
     命題集合は Π と同じ 9 元にとり a/h = a とする (PrO は ax_3_20_incomp と
     aPh の定義にしか現れない)。全公理を満たす (diagram_full; decide/norm_num)。
     比較不能な対: X と Y、X と A、Y と A、V と Z、U と V, W, X, Y, Z、
     U と A (= num (1/2)) (diagram_incomp_pairs)。
   線形モデル chain3 (必要性の判定): Π = 3 元 {O, A, I} の鎖。ax_3_20_incomp
     以外の全公理を満たし、比較不能な対を持たない (nec_incomp)。

   形式化の境界の記録:
   - §21 (iii.)(iv.): (iii.) の「ÔA と ÂI はすべての確率で真」と (iv.) の
     「ÂB ならば B > A」は、> を狭義に読むと、「間」の関係が何であっても
     A = O で O > O を出す (th_3_21_iii_iv_inconsistent)。端を含む Btw では
     印刷どおりの (iv.) は A = B = O で反証される (th_3_21_iv_printed_refuted)。
     修正形は A ≠ B を前提に加えた形 (th_3_21_iv_corr)。端を含まない読み SBtw では
     印刷どおりの (iv.) が成り立つ (th_3_21_iv_strict) が、そのとき (iii.) の
     ÔA は成り立たない。
   - §19 (iv.): 「間」を向きを問わない関係と読むとき、端を含まない読み
     (SymSBtw) では成り立ち (th_3_19_iv_sym_strict)、端を含む読み (SymBtw) では
     B = C で破れる (th_3_19_iv_sym_incl_fails, ℚ の反例)。高籔・新井 (2011a)
     §3.4 の「推移律は必ずしも成り立たない」との関係は要裁定。本ファイルの
     主読みは向きつきの Btw (th_3_19_iv)。
   - 段 3: diagram では A + V も A·A (= 1/4、鎖の外) も定義されない。
     (iv. b) の加法形と (iv. c) の加法の等号形を満たし A + A = I となる全域の
     加法は diagram の Π 上に存在しない (diagram_no_total_add)。一般に (iv. c) の
     下で A + A = I なら V ≠ A について A + V は I でない (th_3_ivc_add_partial)。
   - 各定理の被導出関係は末尾の #print axioms の出力で確認する。
   ============================================================ -/

import Mathlib

namespace KeynesOrderIII

/-! ## 命題集合 Γ (phase6c の KeynesI と同文の一部) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp

/-- 比較不能 (folio 39 "not comparable"): x ≤ y でも y ≤ x でもない。 -/
def Incomp {D : Type} [LE D] (x y : D) : Prop := ¬ x ≤ y ∧ ¬ y ≤ x

/-! ## 段 1: ℝ 値の確率関係では比較不能な対が存在しない -/

/-- 確率関係の値 (phase6c・phase8dp と同文): 値域は ℝ。 -/
axiom PrI : IProp → IProp → ℝ

/-- 同じ前提 h の下の二つの確率関係はつねに比較できる (全順序性)。 -/
theorem th_3_real_total (a b h : IProp) : PrI a h ≤ PrI b h ∨ PrI b h ≤ PrI a h :=
  le_total _ _

/-- 前提が異なっても比較できる。 -/
theorem th_3_real_total_cross (a h b k : IProp) :
    PrI a h ≤ PrI b k ∨ PrI b k ≤ PrI a h :=
  le_total _ _

/-- 塩沢 (1983) の埋め込み規則 I の対 a/bh と a/h: ℝ 値では比較がつねに決まる。 -/
theorem th_3_real_rule_I_pair (a b h : IProp) :
    PrI a (iand b h) ≤ PrI a h ∨ PrI a h ≤ PrI a (iand b h) :=
  le_total _ _

/-- 値域が線形順序集合であれば、確率関係のどの対も比較不能でない。 -/
theorem th_3_linear_no_incomparable {Γ D : Type} [LinearOrder D] (f : Γ → Γ → D) :
    ¬ ∃ a h b k, Incomp (f a h) (f b k) := by
  rintro ⟨a, h, b, k, h1, h2⟩
  rcases le_total (f a h) (f b k) with h3 | h3
  · exact h1 h3
  · exact h2 h3

/-- 第3章の比較不能な対 (folio 39 の X と Y など) は ℝ 値の PrI では表せない。 -/
theorem th_3_real_no_incomparable : ¬ ∃ a h b k : IProp, Incomp (PrI a h) (PrI b k) :=
  th_3_linear_no_incomparable PrI

/-! ## 段 2: 確率集合 Π を半順序の型にした形式化 -/

/-- 確率集合 Π (塩沢 1983): 確率の度の型。 -/
axiom Deg : Type
/-- Π の順序は半順序 (反射・推移・反対称)。全順序は仮定しない。 -/
axiom instPartialOrderDeg : PartialOrder Deg
attribute [instance] instPartialOrderDeg

/-- 不可能性 O。 -/
axiom dO : Deg
/-- 確実性 I。 -/
axiom dI : Deg
/-- 確率関係 a/h の値: 値域は Π (ℝ ではない)。 -/
axiom PrO : IProp → IProp → Deg
/-- 数値的確率の値の集合 (有理数)。 -/
axiom numD : Set ℚ
/-- 数値的確率の埋め込み (数値経路 OAI)。numD の外の値は意味を持たない。 -/
axiom num : ℚ → Deg
/-- Π 上の加法 (部分関数; Ax. (iv.) の「和が存在するならば」)。 -/
axiom padd : Deg → Deg → Option Deg
/-- Π 上の乗法 (部分関数; Ax. (iv.) の「積が存在するならば」)。 -/
axiom pmul : Deg → Deg → Option Deg

/-- 「y は x と z の間にある」(端を含む; 向きは x から z)。 -/
def Btw {D : Type} [LE D] (x y z : D) : Prop := x ≤ y ∧ y ≤ z

/-- 「y は x と z の間にある」(端を含まない)。 -/
def SBtw {D : Type} [LT D] (x y z : D) : Prop := x < y ∧ y < z

/-- ABCD が順序系列をなす。 -/
def Series4 {D : Type} [LE D] (a b c d : D) : Prop := a ≤ b ∧ b ≤ c ∧ c ≤ d

/-- 向きを問わない「間」(端を含む)。 -/
def SymBtw {D : Type} [LE D] (x y z : D) : Prop := Btw x y z ∨ Btw z y x

/-- 向きを問わない「間」(端を含まない)。 -/
def SymSBtw {D : Type} [LT D] (x y z : D) : Prop := SBtw x y z ∨ SBtw z y x

/-- §21 (iii.) ÔA: すべての確率 A について、O は O と A の間にある。 -/
axiom ax_3_21_iii_OA (A : Deg) : Btw dO dO A
/-- §21 (iii.) ÂI: すべての確率 A について、A は O と I の間にある。 -/
axiom ax_3_21_iii_AI (A : Deg) : Btw dO A dI

/-- 数値経路の端: num 0 = O。 -/
axiom ax_3_num_O : num 0 = dO
/-- 数値経路の端: num 1 = I。 -/
axiom ax_3_num_I : num 1 = dI
/-- 0 と 1 は数値的確率の値。 -/
axiom ax_3_numD_ends : (0 : ℚ) ∈ numD ∧ (1 : ℚ) ∈ numD
/-- 数値的確率の値は 0 と 1 の間。 -/
axiom ax_3_numD_range : ∀ p ∈ numD, 0 ≤ p ∧ p ≤ 1
/-- 数値的確率は数の大小どおりに並ぶ (§20 "numerically comparable")。 -/
axiom ax_3_num_order : ∀ p ∈ numD, ∀ q ∈ numD, (num p ≤ num q ↔ p ≤ q)

/-- §20: 比較不能な確率関係の対が存在する。 -/
axiom ax_3_20_incomp : ∃ a h b k : IProp, Incomp (PrO a h) (PrO b k)

/-- §17: 数値経路の上では加法は数の和 (和が鎖の中にあるとき)。 -/
axiom ax_3_17_add_num : ∀ p ∈ numD, ∀ q ∈ numD, p + q ∈ numD →
    padd (num p) (num q) = some (num (p + q))
/-- §17: 数値経路の上では乗法は数の積 (積が鎖の中にあるとき)。 -/
axiom ax_3_17_mul_num : ∀ p ∈ numD, ∀ q ∈ numD, p * q ∈ numD →
    pmul (num p) (num q) = some (num (p * q))

/-- (iv. b) PQ < P unless Q = 1 or P = 0 (積が存在するとき)。 -/
axiom ax_ivb_mul_lt (P Q S : Deg) : pmul P Q = some S → Q ≠ dI → P ≠ dO → S < P
/-- (iv. b) P + Q > P unless Q = 0 (和が存在するとき)。 -/
axiom ax_ivb_add_gt (P Q S : Deg) : padd P Q = some S → Q ≠ dO → S > P
/-- (iv. b) PQ = P if Q = 1 or P = 0。 -/
axiom ax_ivb_mul_eq (P Q S : Deg) : pmul P Q = some S → (Q = dI ∨ P = dO) → S = P
/-- (iv. b) P + Q = P if Q = 0。 -/
axiom ax_ivb_add_eq (P Q S : Deg) : padd P Q = some S → Q = dO → S = P
/-- (iv. c) If PQ ⋛ PR, then Q ⋛ R unless P = 0 (⋛ を < = > の 3 成分に)。 -/
axiom ax_ivc_mul (P Q R S T : Deg) : pmul P Q = some S → pmul P R = some T → P ≠ dO →
    (S < T → Q < R) ∧ (S = T → Q = R) ∧ (S > T → Q > R)
/-- (iv. c) If P + Q ⋛ P + R, then Q ⋛ R and conversely。 -/
axiom ax_ivc_add (P Q R S T : Deg) : padd P Q = some S → padd P R = some T →
    (S < T ↔ Q < R) ∧ (S = T ↔ Q = R) ∧ (S > T ↔ Q > R)

/-! ### 半順序の性質と端点 O, I -/

/-- 反対称性 (Ryłow 2026 の指摘への回答): x ≤ y かつ y ≤ x ならば x = y。 -/
theorem th_3_antisymm (x y : Deg) (h₁ : x ≤ y) (h₂ : y ≤ x) : x = y :=
  le_antisymm h₁ h₂

/-- 推移性。 -/
theorem th_3_trans (x y z : Deg) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  le_trans h₁ h₂

/-- O は最小元 (ÔA から)。 -/
theorem th_3_O_le (x : Deg) : dO ≤ x := (ax_3_21_iii_OA x).2

/-- I は最大元 (ÂI から)。 -/
theorem th_3_le_I (x : Deg) : x ≤ dI := (ax_3_21_iii_AI x).2

/-- O より下の確率は O だけ (反対称性と ÔA)。 -/
theorem th_3_le_O_iff (x : Deg) : x ≤ dO ↔ x = dO :=
  ⟨fun h => le_antisymm h (th_3_O_le x), fun h => h ▸ le_rfl⟩

/-- I より上の確率は I だけ (反対称性と ÂI)。 -/
theorem th_3_I_le_iff (x : Deg) : dI ≤ x ↔ x = dI :=
  ⟨fun h => le_antisymm (th_3_le_I x) h, fun h => h ▸ le_rfl⟩

/-- §19 (i.): どの確率も不可能性と確実性の間にある。 -/
theorem th_3_19_i (x : Deg) : Btw dO x dI := ax_3_21_iii_AI x

/-- 比較不能な対があるので O ≠ I (O < I)。 -/
theorem th_3_O_lt_I : dO < dI := by
  refine lt_of_le_of_ne (th_3_O_le dI) ?_
  intro hOI
  obtain ⟨a, h, b, k, h₁, -⟩ := ax_3_20_incomp
  apply h₁
  have e₁ : PrO a h = dO := (th_3_le_O_iff _).1 (hOI ▸ th_3_le_I _)
  rw [e₁]
  exact th_3_O_le _

/-- O < I は数値経路の公理からも出る (num 1 ≤ num 0 は 1 ≤ 0 と同値で偽)。 -/
theorem th_3_O_lt_I_num : dO < dI := by
  refine lt_of_le_of_ne (th_3_O_le dI) ?_
  intro hOI
  have h := (ax_3_num_order 1 ax_3_numD_ends.2 0 ax_3_numD_ends.1).1
  rw [ax_3_num_O, ax_3_num_I, hOI] at h
  exact absurd (h le_rfl) (by norm_num)

/-! ### §19 (iv.) と §21 (i.)(ii.) -/

/-- §21 (i.): B が A と C の間にあれば、ABC は系列をなす (A ≤ B ≤ C)。 -/
theorem th_3_21_i (A B C : Deg) (h : Btw A B C) : A ≤ B ∧ B ≤ C := h

/-- §19 (iv.): ABC が系列 (B は A と C の間)、BCD が系列 (C は B と D の間) ならば、
    ABCD は系列をなし、B は A と D の間にある。 -/
theorem th_3_19_iv (A B C D : Deg) (h₁ : Btw A B C) (h₂ : Btw B C D) :
    Series4 A B C D ∧ Btw A B D :=
  ⟨⟨h₁.1, h₁.2, h₂.2⟩, ⟨h₁.1, le_trans h₁.2 h₂.2⟩⟩

/-- §19 (iv.) を向きを問わない、端を含まない「間」で読んでも成り立つ。 -/
theorem th_3_19_iv_sym_strict {D : Type} [PartialOrder D] (A B C E : D)
    (h₁ : SymSBtw A B C) (h₂ : SymSBtw B C E) : SymSBtw A B E := by
  rcases h₁ with ⟨hab, hbc⟩ | ⟨hcb, hba⟩ <;> rcases h₂ with ⟨hbc', hce⟩ | ⟨hec, hcb'⟩
  · exact Or.inl ⟨hab, hbc.trans hce⟩
  · exact absurd hbc (lt_asymm hcb')
  · exact absurd hcb (lt_asymm hbc')
  · exact Or.inr ⟨hec.trans hcb', hba⟩

/-- 向きを問わない、端を含む「間」では §19 (iv.) は破れる (ℚ で A = 0, B = C = 1, D = 0)。 -/
theorem th_3_19_iv_sym_incl_fails :
    ¬ ∀ A B C E : ℚ, SymBtw A B C → SymBtw B C E → SymBtw A B E := by
  intro h
  have := h 0 1 1 0 (Or.inl ⟨by norm_num, le_rfl⟩) (Or.inr ⟨by norm_num, le_rfl⟩)
  rcases this with ⟨-, h'⟩ | ⟨-, h'⟩ <;> norm_num at h'

/-- §21 (ii.): A が確率ならば OAI は系列をなす。 -/
theorem th_3_21_ii (A : Deg) : Btw dO A dI := ax_3_21_iii_AI A

/-! ### §20 数値経路 OAI と比較不能な対 -/

/-- §20: 数値的確率はすべて一つの系列に属する (鎖)。 -/
theorem th_3_20_strand (p q : ℚ) (hp : p ∈ numD) (hq : q ∈ numD) :
    num p ≤ num q ∨ num q ≤ num p := by
  rcases le_total p q with h | h
  · exact Or.inl ((ax_3_num_order p hp q hq).2 h)
  · exact Or.inr ((ax_3_num_order q hq p hp).2 h)

/-- §20: 数値経路は O に始まり I に終わり、数値的確率 A はその間にある (OAI)。 -/
theorem th_3_20_OAI (p : ℚ) (hp : p ∈ numD) :
    num 0 = dO ∧ num 1 = dI ∧ Btw (num 0) (num p) (num 1) := by
  refine ⟨ax_3_num_O, ax_3_num_I, ?_, ?_⟩
  · exact (ax_3_num_order 0 ax_3_numD_ends.1 p hp).2 (ax_3_numD_range p hp).1
  · exact (ax_3_num_order p hp 1 ax_3_numD_ends.2).2 (ax_3_numD_range p hp).2

/-- §20: 比較不能な確率の度の対が存在する。 -/
theorem th_3_20_incomp : ∃ x y : Deg, Incomp x y := by
  obtain ⟨a, h, b, k, hi⟩ := ax_3_20_incomp
  exact ⟨_, _, hi⟩

/-- 段 1 との対照: PrO の順序を ℝ 値の関係で写すことはできない。 -/
theorem th_3_PrO_not_real :
    ¬ ∃ r : IProp → IProp → ℝ, ∀ a h b k, (PrO a h ≤ PrO b k ↔ r a h ≤ r b k) := by
  rintro ⟨r, hr⟩
  obtain ⟨a, h, b, k, h₁, h₂⟩ := ax_3_20_incomp
  rcases le_total (r a h) (r b k) with h₃ | h₃
  · exact h₁ ((hr a h b k).2 h₃)
  · exact h₂ ((hr b k a h).2 h₃)

/-- Π から ℝ への順序を映す写像は無い。 -/
theorem th_3_no_real_reflect : ¬ ∃ g : Deg → ℝ, ∀ x y, g x ≤ g y → x ≤ y := by
  rintro ⟨g, hg⟩
  obtain ⟨x, y, h₁, h₂⟩ := th_3_20_incomp
  rcases le_total (g x) (g y) with h₃ | h₃
  · exact h₁ (hg x y h₃)
  · exact h₂ (hg y x h₃)

/-! ### §21 (iii.)(iv.) ÂB と B > A -/

/-- §21 (iii.) ÔA (公理の再掲)。 -/
theorem th_3_21_iii_OA (A : Deg) : Btw dO dO A := ax_3_21_iii_OA A

/-- §21 (iii.) ÂI (公理の再掲)。 -/
theorem th_3_21_iii_AI (A : Deg) : Btw dO A dI := ax_3_21_iii_AI A

/-- 「間」の関係 Bt が何であっても、(iii.) の「すべての A で ÔA」と、狭義の > で
    読んだ (iv.) の「ÂB ならば B > A」は両立しない (A = O で O > O)。 -/
theorem th_3_21_iii_iv_inconsistent {D : Type} [Preorder D] (Bt : D → D → D → Prop) (O : D)
    (hOA : ∀ A, Bt O O A) (hiv : ∀ A B, Bt O A B → B > A) : False :=
  lt_irrefl O (hiv O O (hOA O))

/-- 端を含む Btw では印刷どおりの (iv.) は成り立たない (A = B = O)。 -/
theorem th_3_21_iv_printed_refuted : ¬ ∀ A B : Deg, Btw dO A B → B > A :=
  fun h => lt_irrefl dO (h dO dO ⟨le_rfl, le_rfl⟩)

/-- §21 (iv.) の修正形: ÂB かつ A ≠ B ならば B > A。 -/
theorem th_3_21_iv_corr (A B : Deg) (h : Btw dO A B) (hne : A ≠ B) : B > A :=
  lt_of_le_of_ne h.2 hne

/-- §21 (iv.) の非狭義形: ÂB ならば A ≤ B。 -/
theorem th_3_21_iv_le (A B : Deg) (h : Btw dO A B) : A ≤ B := h.2

/-- 端を含まない「間」で読めば印刷どおり: ÂB ならば B > A。 -/
theorem th_3_21_iv_strict (A B : Deg) (h : SBtw dO A B) : B > A := h.2

/-! ### §21 (v.) aPh と a/h = P -/

/-- aPh: 結論 a は前提 h に対して確率関係 P にある。 -/
def RelP (a : IProp) (P : Deg) (h : IProp) : Prop := PrO a h = P

/-- §21 (v.): aPh は a/h = P とも書ける (名付けの行; 定義の展開)。 -/
theorem th_3_21_v (a : IProp) (P : Deg) (h : IProp) : RelP a P h ↔ PrO a h = P :=
  Iff.rfl

/-- §21 (v.) 末: aPh かつ a′Ph′ ならば a/h = a′/h′。 -/
theorem th_3_21_v_eq (a a' h h' : IProp) (P : Deg) (h₁ : RelP a P h) (h₂ : RelP a' P h') :
    PrO a h = PrO a' h' :=
  h₁.trans h₂.symm

/-! ### §17 加法と n.A (Π 上の部分関数) -/

/-- n.A (n ≥ 1): A を n 回足した和 (途中の和が存在するとき)。n = 0 は未定義。 -/
noncomputable def nsm (A : Deg) : ℕ → Option Deg
  | 0 => none
  | 1 => some A
  | n + 2 => (nsm A (n + 1)).bind (fun x => padd x A)

theorem nsm_succ (A : Deg) (n : ℕ) (hn : 1 ≤ n) :
    nsm A (n + 1) = (nsm A n).bind (fun x => padd x A) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- §17: C = A + B で A と B が等しければ C = 2A。 -/
theorem th_3_17_double (A B C : Deg) (hC : padd A B = some C) (hAB : A = B) :
    nsm A 2 = some C := by
  subst hAB
  simp [nsm, hC]

/-- §17: C = A + A かつ D = C + A ならば D = 3A。 -/
theorem th_3_17_triple (A C D : Deg) (hC : padd A A = some C) (hD : padd C A = some D) :
    nsm A 3 = some D := by
  simp [nsm, hC, hD]

/-- §17 "and so on": P = n.A かつ D = P + A ならば D = (n+1).A。 -/
theorem th_3_17_succ (A P D : Deg) (n : ℕ) (hn : 1 ≤ n) (hP : nsm A n = some P)
    (hD : padd P A = some D) : nsm A (n + 1) = some D := by
  rw [nsm_succ A n hn, hP]
  simpa using hD

/-- §17: 数値経路が 1/n の倍数を含むとき、A の大きさが 1/n (A = num (1/n)) なら
    n.A は確実性 I (n.(num (1/n)) = I)。印刷の向き (P = n.A で P が確実性なら A の大きさは
    1/n) の逆向きである。 -/
theorem th_3_17_unit (n : ℕ) (hn : 1 ≤ n) (hD : ∀ k : ℕ, k ≤ n → (k : ℚ) / n ∈ numD) :
    nsm (num (1 / n)) n = some dI := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : (1 : ℚ) / n ∈ numD := by simpa using hD 1 hn
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ n → nsm (num (1 / n)) k = some (num ((k : ℚ) / n)) := by
    intro k hk1 hkn
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [nsm]
      · rw [nsm_succ _ k hk, ih hk (by omega)]
        have hsum := ax_3_17_add_num ((k : ℚ) / n) (hD k (by omega)) (1 / n) h1
          (by
            have := hD (k + 1) hkn
            rwa [Nat.cast_succ, add_div] at this)
        simp only [Option.bind_some]
        rw [hsum, Nat.cast_succ, add_div]
  rw [key n hn le_rfl, div_self hn', ax_3_num_I]

/-! ## 段 3: 第 II 部 Ax. (iv. b)(iv. c) の順序の部分 -/

/-- (iv. c) の加法の等号形の下で A + A = I ならば、V ≠ A について A + V は I でない。 -/
theorem th_3_ivc_add_partial (A V S : Deg) (hAA : padd A A = some dI)
    (hAV : padd A V = some S) (hne : V ≠ A) : S ≠ dI := by
  intro hS
  subst hS
  exact hne (((ax_ivc_add A V A dI dI hAV hAA).2.1).1 rfl)

/-- (iv. b) の加法形と (iv. c) から: 和が存在すれば和は加える数より大きいか等しい。 -/
theorem th_3_ivb_add_ge (P Q S : Deg) (h : padd P Q = some S) : P ≤ S := by
  by_cases hQ : Q = dO
  · exact (ax_ivb_add_eq P Q S h hQ).symm ▸ le_rfl
  · exact (ax_ivb_add_gt P Q S h hQ).le

/-! ## 公理の一覧 (構造体) と模型 -/

/-- 段 2・段 3 の形式化の解釈: 命題集合 Γ、確率集合 D と、その上の O, I, a/h,
    数値経路、加法・乗法。 -/
structure OrderSeries (Γ D : Type) where
  O : D
  I : D
  Pr : Γ → Γ → D
  numD : Set ℚ
  num : ℚ → D
  add : D → D → Option D
  mul : D → D → Option D

namespace OrderSeries

/-- ax_3_20_incomp を除く全公理 (宣言した公理と一対一)。 -/
structure Core {Γ D : Type} [PartialOrder D] (M : OrderSeries Γ D) : Prop where
  OA : ∀ A : D, Btw M.O M.O A
  AI : ∀ A : D, Btw M.O A M.I
  num_O : M.num 0 = M.O
  num_I : M.num 1 = M.I
  numD_ends : (0 : ℚ) ∈ M.numD ∧ (1 : ℚ) ∈ M.numD
  numD_range : ∀ p ∈ M.numD, 0 ≤ p ∧ p ≤ 1
  num_order : ∀ p ∈ M.numD, ∀ q ∈ M.numD, (M.num p ≤ M.num q ↔ p ≤ q)
  add_num : ∀ p ∈ M.numD, ∀ q ∈ M.numD, p + q ∈ M.numD →
    M.add (M.num p) (M.num q) = some (M.num (p + q))
  mul_num : ∀ p ∈ M.numD, ∀ q ∈ M.numD, p * q ∈ M.numD →
    M.mul (M.num p) (M.num q) = some (M.num (p * q))
  ivb_mul_lt : ∀ P Q S : D, M.mul P Q = some S → Q ≠ M.I → P ≠ M.O → S < P
  ivb_add_gt : ∀ P Q S : D, M.add P Q = some S → Q ≠ M.O → S > P
  ivb_mul_eq : ∀ P Q S : D, M.mul P Q = some S → (Q = M.I ∨ P = M.O) → S = P
  ivb_add_eq : ∀ P Q S : D, M.add P Q = some S → Q = M.O → S = P
  ivc_mul : ∀ P Q R S T : D, M.mul P Q = some S → M.mul P R = some T → P ≠ M.O →
    (S < T → Q < R) ∧ (S = T → Q = R) ∧ (S > T → Q > R)
  ivc_add : ∀ P Q R S T : D, M.add P Q = some S → M.add P R = some T →
    (S < T ↔ Q < R) ∧ (S = T ↔ Q = R) ∧ (S > T ↔ Q > R)

/-- ax_3_20_incomp: 比較不能な確率関係の対が存在する。 -/
def IncompArg {Γ D : Type} [PartialOrder D] (M : OrderSeries Γ D) : Prop :=
  ∃ a h b k : Γ, Incomp (M.Pr a h) (M.Pr b k)

/-- 全公理。 -/
def Full {Γ D : Type} [PartialOrder D] (M : OrderSeries Γ D) : Prop :=
  M.Core ∧ M.IncompArg

end OrderSeries

/-- 宣言した公理による解釈。 -/
noncomputable def axiomatic : OrderSeries IProp Deg :=
  ⟨dO, dI, PrO, numD, num, padd, pmul⟩

/-- 宣言した公理は Full の各項を与える (Full は公理の一覧として過不足ない)。 -/
theorem axiomatic_full : axiomatic.Full :=
  ⟨{ OA := ax_3_21_iii_OA
     AI := ax_3_21_iii_AI
     num_O := ax_3_num_O
     num_I := ax_3_num_I
     numD_ends := ax_3_numD_ends
     numD_range := ax_3_numD_range
     num_order := ax_3_num_order
     add_num := ax_3_17_add_num
     mul_num := ax_3_17_mul_num
     ivb_mul_lt := ax_ivb_mul_lt
     ivb_add_gt := ax_ivb_add_gt
     ivb_mul_eq := ax_ivb_mul_eq
     ivb_add_eq := ax_ivb_add_eq
     ivc_mul := ax_ivc_mul
     ivc_add := ax_ivc_add }, ax_3_20_incomp⟩

/-! ### 有限モデル diagram: folio 39 の図の 9 点 -/

/-- folio 39 の図の点。 -/
inductive D9 | O | A | I | U | V | W | X | Y | Z
  deriving DecidableEq, Fintype, Repr

namespace D9

/-- 図の順序: folio 39 の文の大小関係とその推移閉包。 -/
def le9 : D9 → D9 → Bool
  | O, _ => true
  | _, I => true
  | V, A => true
  | V, W => true
  | V, X => true
  | V, Y => true
  | W, X => true
  | W, Y => true
  | Z, W => true
  | Z, X => true
  | Z, Y => true
  | x, y => x == y

theorem le9_refl : ∀ a : D9, le9 a a = true := by decide

theorem le9_trans : ∀ a b c : D9, le9 a b = true → le9 b c = true → le9 a c = true := by
  decide

theorem le9_antisymm : ∀ a b : D9, le9 a b = true → le9 b a = true → a = b := by decide

instance : PartialOrder D9 where
  le x y := le9 x y = true
  lt x y := le9 x y = true ∧ ¬ le9 y x = true
  le_refl := le9_refl
  le_trans := le9_trans
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm := le9_antisymm

instance decLe : DecidableRel (α := D9) (· ≤ ·) :=
  fun x y => inferInstanceAs (Decidable (le9 x y = true))

instance decLt : DecidableRel (α := D9) (· < ·) :=
  fun x y => inferInstanceAs (Decidable (le9 x y = true ∧ ¬ le9 y x = true))

/-- 数値経路: 0 ↦ O, 1/2 ↦ A, 1 ↦ I (ほかの有理数は意味を持たない; O に送る)。 -/
def num9 (q : ℚ) : D9 := if q = 0 then O else if q = 1 / 2 then A else if q = 1 then I else O

/-- 加法: O + y = y, x + O = x, A + A = I (1/2 + 1/2 = 1)、ほかは未定義。 -/
def add9 : D9 → D9 → Option D9
  | O, y => some y
  | x, O => some x
  | A, A => some I
  | _, _ => none

/-- 乗法: O·y = O, x·O = O, I·y = y, x·I = x、ほかは未定義 (1/2·1/2 = 1/4 は鎖の外)。 -/
def mul9 : D9 → D9 → Option D9
  | O, _ => some O
  | _, O => some O
  | I, y => some y
  | x, I => some x
  | _, _ => none

end D9

open D9 in
/-- folio 39 の図の模型 (命題集合も 9 点、a/h = a)。 -/
def diagram : OrderSeries D9 D9 :=
  ⟨O, I, fun a _ => a, {0, 1 / 2, 1}, num9, add9, mul9⟩

theorem diagram_core : diagram.Core where
  OA x := ⟨le_rfl, by cases x <;> decide⟩
  AI x := ⟨by cases x <;> decide, by cases x <;> decide⟩
  num_O := by simp [diagram, D9.num9]
  num_I := by norm_num [diagram, D9.num9]
  numD_ends := by simp [diagram]
  numD_range := by
    intro p hp
    simp only [diagram, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  num_order := by
    intro p hp q hq
    simp only [diagram, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq ⊢
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      norm_num [D9.num9] <;> decide
  add_num := by
    intro p hp q hq hpq
    simp only [diagram, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq hpq ⊢
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
      | (norm_num [D9.num9]; rfl)
      | (norm_num at hpq)
  mul_num := by
    intro p hp q hq hpq
    simp only [diagram, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq hpq ⊢
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
      | (norm_num [D9.num9]; rfl)
      | (norm_num at hpq)
  ivb_mul_lt := by decide
  ivb_add_gt := by decide
  ivb_mul_eq := by decide
  ivb_add_eq := by decide
  ivc_mul := by decide +kernel
  ivc_add := by decide +kernel

/-- 比較不能な確率関係の対: a = X, b = Y (前提は任意)。 -/
theorem diagram_incompArg : diagram.IncompArg :=
  ⟨D9.X, D9.X, D9.Y, D9.X, by unfold Incomp; decide⟩

/-- diagram は全公理を満たす。 -/
theorem diagram_full : diagram.Full := ⟨diagram_core, diagram_incompArg⟩

open D9 in
/-- folio 39 の文の大小関係: V < A, V < W, X, Y; W < X, Y; Z < W, X, Y; A は数値経路の上。 -/
theorem diagram_folio39_lt :
    V < A ∧ V < W ∧ V < X ∧ V < Y ∧ W < X ∧ W < Y ∧ Z < W ∧ Z < X ∧ Z < Y ∧
    O < A ∧ A < I ∧ num9 (1 / 2) = A := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by norm_num [num9]⟩

open D9 in
/-- folio 39 の比較不能な対: X と Y、X と A、Y と A、V と Z、U と V, W, X, Y, Z、
    および U と A (= num (1/2))。 -/
theorem diagram_incomp_pairs :
    Incomp X Y ∧ Incomp X A ∧ Incomp Y A ∧ Incomp V Z ∧
    Incomp U V ∧ Incomp U W ∧ Incomp U X ∧ Incomp U Y ∧ Incomp U Z ∧
    Incomp U (num9 (1 / 2)) := by
  have hA : num9 (1 / 2) = A := by norm_num [num9]
  rw [hA]
  unfold Incomp
  decide

open D9 in
/-- 段 3 の形式化の境界: diagram では A + V も A·A も定義されない。 -/
theorem diagram_partial : add9 A V = none ∧ mul9 A A = none ∧ add9 A A = some I := by
  decide

open D9 in
/-- 段 3 の形式化の境界: diagram の Π 上に、A + A = I、(iv. b) の加法形、(iv. c) の
    加法の等号形を満たす全域の加法は無い (A + V は A より大きいので I、すると A + V =
    A + A から V = A)。 -/
theorem diagram_no_total_add :
    ¬ ∃ f : D9 → D9 → D9, f A A = I ∧ (∀ P Q, Q ≠ O → P < f P Q) ∧
      (∀ P Q R, f P Q = f P R → Q = R) := by
  rintro ⟨f, hAA, hgt, hcan⟩
  have hup : ∀ x : D9, A < x → x = I := by decide
  have hAV : f A V = I := hup _ (hgt A V (by decide))
  exact absurd (hcan A V A (hAV.trans hAA.symm)) (by decide)

open D9 in
/-- (iv. a) (順序に関わらないので公理に置かない): diagram の加法・乗法は交換的。 -/
theorem diagram_iva : (∀ P Q : D9, add9 P Q = add9 Q P) ∧ (∀ P Q : D9, mul9 P Q = mul9 Q P) := by
  decide

/-! ### 線形モデル chain3: ax_3_20_incomp の必要性 -/

/-- 3 点の鎖 O < A < I。 -/
inductive C3 | O | A | I
  deriving DecidableEq, Fintype, Repr

namespace C3

def rk : C3 → ℕ
  | O => 0
  | A => 1
  | I => 2

instance : PartialOrder C3 where
  le x y := rk x ≤ rk y
  lt x y := rk x ≤ rk y ∧ ¬ rk y ≤ rk x
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm := by decide

instance decLe : DecidableRel (α := C3) (· ≤ ·) :=
  fun x y => inferInstanceAs (Decidable (rk x ≤ rk y))

instance decLt : DecidableRel (α := C3) (· < ·) :=
  fun x y => inferInstanceAs (Decidable (rk x ≤ rk y ∧ ¬ rk y ≤ rk x))

def num3 (q : ℚ) : C3 := if q = 0 then O else if q = 1 / 2 then A else if q = 1 then I else O

def add3 : C3 → C3 → Option C3
  | O, y => some y
  | x, O => some x
  | A, A => some I
  | _, _ => none

def mul3 : C3 → C3 → Option C3
  | O, _ => some O
  | _, O => some O
  | I, y => some y
  | x, I => some x
  | _, _ => none

end C3

open C3 in
/-- 線形モデル (命題集合は 1 点)。 -/
def chain3 : OrderSeries Unit C3 :=
  ⟨O, I, fun _ _ => A, {0, 1 / 2, 1}, num3, add3, mul3⟩

theorem chain3_core : chain3.Core where
  OA x := ⟨le_rfl, by cases x <;> decide⟩
  AI x := ⟨by cases x <;> decide, by cases x <;> decide⟩
  num_O := by simp [chain3, C3.num3]
  num_I := by norm_num [chain3, C3.num3]
  numD_ends := by simp [chain3]
  numD_range := by
    intro p hp
    simp only [chain3, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  num_order := by
    intro p hp q hq
    simp only [chain3, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq ⊢
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      norm_num [C3.num3] <;> decide
  add_num := by
    intro p hp q hq hpq
    simp only [chain3, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq hpq ⊢
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
      | (norm_num [C3.num3]; rfl)
      | (norm_num at hpq)
  mul_num := by
    intro p hp q hq hpq
    simp only [chain3, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq hpq ⊢
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
      | (norm_num [C3.num3]; rfl)
      | (norm_num at hpq)
  ivb_mul_lt := by decide
  ivb_add_gt := by decide
  ivb_mul_eq := by decide
  ivb_add_eq := by decide
  ivc_mul := by decide +kernel
  ivc_add := by decide +kernel

/-- 必要性: ax_3_20_incomp 以外の全公理を満たし、比較不能な度の対を持たないモデルがある。
    したがって th_3_20_incomp・th_3_PrO_not_real・th_3_no_real_reflect は ax_3_20_incomp
    なしには導けない (O < I は chain3 でも成り立つ; 数値経路から出る th_3_O_lt_I_num)。 -/
theorem nec_incomp : chain3.Core ∧ ¬ ∃ x y : C3, Incomp x y := by
  refine ⟨chain3_core, ?_⟩
  unfold Incomp
  decide

end KeynesOrderIII

/-! ## 被導出関係 (#print axioms) -/

-- 段 1
#print axioms KeynesOrderIII.th_3_real_total
#print axioms KeynesOrderIII.th_3_real_total_cross
#print axioms KeynesOrderIII.th_3_real_rule_I_pair
#print axioms KeynesOrderIII.th_3_linear_no_incomparable
#print axioms KeynesOrderIII.th_3_real_no_incomparable
-- 段 2
#print axioms KeynesOrderIII.th_3_antisymm
#print axioms KeynesOrderIII.th_3_trans
#print axioms KeynesOrderIII.th_3_O_le
#print axioms KeynesOrderIII.th_3_le_I
#print axioms KeynesOrderIII.th_3_le_O_iff
#print axioms KeynesOrderIII.th_3_I_le_iff
#print axioms KeynesOrderIII.th_3_19_i
#print axioms KeynesOrderIII.th_3_O_lt_I
#print axioms KeynesOrderIII.th_3_21_i
#print axioms KeynesOrderIII.th_3_19_iv
#print axioms KeynesOrderIII.th_3_19_iv_sym_strict
#print axioms KeynesOrderIII.th_3_19_iv_sym_incl_fails
#print axioms KeynesOrderIII.th_3_21_ii
#print axioms KeynesOrderIII.th_3_20_strand
#print axioms KeynesOrderIII.th_3_20_OAI
#print axioms KeynesOrderIII.th_3_20_incomp
#print axioms KeynesOrderIII.th_3_PrO_not_real
#print axioms KeynesOrderIII.th_3_no_real_reflect
#print axioms KeynesOrderIII.th_3_21_iii_OA
#print axioms KeynesOrderIII.th_3_21_iii_AI
#print axioms KeynesOrderIII.th_3_21_iii_iv_inconsistent
#print axioms KeynesOrderIII.th_3_21_iv_printed_refuted
#print axioms KeynesOrderIII.th_3_21_iv_corr
#print axioms KeynesOrderIII.th_3_21_iv_le
#print axioms KeynesOrderIII.th_3_21_iv_strict
#print axioms KeynesOrderIII.th_3_21_v
#print axioms KeynesOrderIII.th_3_21_v_eq
#print axioms KeynesOrderIII.th_3_17_double
#print axioms KeynesOrderIII.th_3_17_triple
#print axioms KeynesOrderIII.th_3_17_succ
#print axioms KeynesOrderIII.th_3_17_unit
-- 段 3
#print axioms KeynesOrderIII.th_3_ivc_add_partial
#print axioms KeynesOrderIII.th_3_ivb_add_ge
-- 公理の一覧と模型
#print axioms KeynesOrderIII.axiomatic_full
#print axioms KeynesOrderIII.diagram_core
#print axioms KeynesOrderIII.diagram_incompArg
#print axioms KeynesOrderIII.diagram_full
#print axioms KeynesOrderIII.diagram_folio39_lt
#print axioms KeynesOrderIII.diagram_incomp_pairs
#print axioms KeynesOrderIII.diagram_partial
#print axioms KeynesOrderIII.diagram_no_total_add
#print axioms KeynesOrderIII.diagram_iva
#print axioms KeynesOrderIII.chain3_core
#print axioms KeynesOrderIII.nec_incomp
#print axioms KeynesOrderIII.th_3_O_lt_I_num
