/-
# Keynes (1921) *A Treatise on Probability* Part V — Lean 4 Phase 14a
# 第 XXIX 章 §6–§7 (folio 343–344): Keynes が自分の記法で書いた Bernoulli の定理の前提
#
# 第 V 部を載せる目的: Keynes の論理 (第 II 部の公理・定義) が統計的推論に接続しているかを確かめる。
# 「外部公理依存 (公理名)」: 第 II 部の公理群だけでは閉じず、名前付きの公理を足して閉じた行。#print axioms にその名が出る。
# 本ファイル (B36) は台帳 ch29-041〜054 (§6–§7 の Keynes 記法の 14 行) を扱う。
# 前半 001〜040 (二項分布・Stirling・正規近似) は B38、後半 055〜083 (Laplace の継起の規則) は B39 に回す。
#
# ## 基準
#   1921 年 Macmillan 初版の頁画像のみ (folio 337、342–344)。定理名は th_29_<行番号>。
#   台帳の行 ID (ch29-NNN) は各定理の docstring に書く。
#
# ## 原典 (folio 343、§6)
#   「Let _m x_n represent the statement that the event has occurred on m out of n occasions
#    and has not occurred on the others; and let _1x_1/h = p, where h represents our à priori
#    data … Bernoulli's Theorem then requires a series of conditions, of which the following is
#    typical: _{m+1}x_{n+1}/_m x_n . h = _1x_1/h, i.e. the probability of the event on the n+1th
#    occasion must be unaffected by our knowledge of its proportionate frequency on the first n
#    occasions, and must be exactly equal to its à priori probability before the first occasion.
#    … If y_r represents the statement that the event has occurred on each of r successive
#    occasions, y_r/h = y_r/y_{r−1}h . y_{r−1}/h and so on, so that y_r/h = Π_{s=1}^{s=r} y_s/y_{s−1}h.
#    Hence if we are to have y_r/h = p^r, we must have y_s/y_{s−1}h = p for all values of s from
#    1 to r. But in many particular examples y_s/y_{s−1}h increases with s, so that y_r/h > p^r.」
#   (folio 344、§7) 「Given, that is to say, a proposition a_1, some series a_1a_2 . . . can be found,
#    which satisfies the conditions: (i.) a_1/h = a_2/h . . . = a_r/h.
#    (ii.) a_r/a_s . . . ā_t . . . h = a_r/h.」
#
# ## キャリア
#   phase6c の内包キャリア (IProp, PrI, Cons; 公理 (i) の但し書き付き) を同名・同形で写す。
#   Def. XIII (独立)・Def. XIV (無関連) は phase10a と同形で写す。
#   `Prop → Prop → ℝ` 型の確率関係は置かない (CLAUDE.md 不変条件 3)。
#
# ## 記法の読み (定義のみ)
#   a r      : 「r 回目にその事象が起こる」(§7 の a_r; §6 の y_r・_m x_n の材料)。
#   y a r    : y_r。y 0 = itrue、y (r+1) = a_{r+1} ∧ y_r (iand で組む)。
#   x a m n  : _m x_n。最初の n 回のうち m 回起こり、他では起こらない。最後の回 a_n を肯定するか
#              否定するかで場合を分けた選言として組む。m = n のときは第 2 の選言肢
#              (「n 回のうち n+1 回」) が不可能なので省き、x a n n が y a n と同じ項になるように
#              置く (x_diag)。内包キャリアでは論証的に同値な命題が別の項になりうるので、
#              この選び方は定義の一部として明記する。
#   pB a h   : p = _1x_1/h (042 の名付け; th_29_042 は rfl で、台帳の判定には使わない)。
#   yfac     : y_s/y_{s−1}h (049)。
#   lits a L : a_s . . . ā_t . . . (054)。L の各成員 (s, true) は a_s、(t, false) は ā_t。
#
# ## 外部公理 (第 II 部の公理でないもの)
#   a29, h29                    : 第 29 章の事象の系列と à priori data の名付け (内容を主張しない)。
#   ax_data_cons29              : h は矛盾する連言でない (公理 (i) の但し書きを h に当てはめたもの)。
#   ax_bernoulli_independence   : 043 (§6 の典型的条件)、但し書き Cons (_m x_n ∧ h) 付き。
#   ax_equal_chance             : 052 (§7 の (i.))。
#   ax_independence_ii          : 053 (§7 の (ii.))、但し書き Cons (a_s…ā_t… ∧ h) 付き。
#   相対無矛盾性: 自明な代入 a_r := ⊤、h := ⊤ が第 II 部の公理だけから 3 条件と Cons ⊤ を満たす
#   (rel_cons_trivial)。よって第 II 部の公理群が無矛盾なら、外部公理を足しても無矛盾。
#   ただしこの代入では p = 1 であり、0 < p < 1 の場合の無矛盾性は示していない。
#
# ## 外部公理が第 II 部の公理から導けないこと (有限模型、KeynesXXIX_model)
#   phase12b の流儀で第 II 部の公理の文 13 本を構造 Sys に写し、重み付きの有限模型 (世界 Fin 3、
#   重み (1, 1, 1)) が Sys を満たすことを証明する (wSys・sys_M₁)。この模型の整合な h := ⊤ と
#   系列 a_1 := {0}、a_r := {0, 1} (r ≠ 1) について、043 の形 (nec_29_043_model)・052 の形
#   (nec_29_052_model)・053 の形 (nec_29_053_model)・047 の印刷形 y_2/h = p^2
#   (nec_29_047_model) がいずれも偽。よって 043・052・053・047 は第 II 部の公理群からは
#   導けない (系 not_derivable_043)。#print axioms は Lean の標準の公理だけ。
#
# ## 主結果 (047)
#   th_29_047_of43 / th_29_047_of: 前提 (043、または 052+053 の形) を仮定に取れば、
#     #print axioms は第 II 部の公理だけ (def_X_left_i・ax_iii_taut・cons_of_pos 等)。
#   th_29_047 / th_29_047_ii: 第 29 章の data 上の印刷形 y_r/h = p^r。#print axioms に
#     外部公理 (ax_bernoulli_independence または ax_equal_chance・ax_independence_ii、
#     ax_data_cons29、a29、h29) が出る。
#
# ## 第 III 部との接続
#   folio 337 (§1) は第 III 部 (帰納) に言及しない。§5 (folio 342) は「Our discussion of the
#   theorems of multiplication」と第 II 部 (第 14 章の乗法の定理) を指す。047 の帰納の一歩は
#   その乗法定理 (無関連下、th_14_36_i) である。第 III 部 phase9a の J_succ (F20.10) は 045 の
#   a 形 (th_29_045_a) と同じ Def. X 左形であり、th_20_12_src (y_n → 1) は 050 の
#   「y_s/y_{s−1}h increases with s」の場合にあたるが、phase9a は Cons の但し書きの無い公理群の
#   上にあり (import もできない) ので定理としては使わない。接続は散文のみ。
#
# ## 実行方法
#   lake env lean phases/keynes_part_v_phase14a_bernoulli_premises.lean
-/

import Mathlib

namespace KeynesXXIX

/-! ## 内包的キャリアと結合子 (phase6c と同一) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 `Cons h`: 「h は矛盾する連言でない」(folio 135、公理 (i))。 -/
axiom Cons : IProp → Prop

/-! ## Keynes 操作公理群 (内包版、phase6c と同一) -/

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- Def. VIII 双条件読み、但し書き付き (phase6c と同一)。本ファイルの定理は用いない。 -/
axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- Def. VIII 印刷どおり (→ のみ、phase6c と同一)。本ファイルの定理は用いない。 -/
axiom def_VIII_i_src (a b h : IProp) :
    PrI b (iand a h) = 1 → PrI a (iand b h) = 1 → PrI (iiff a b) h = 1

/-! ## 深い埋め込み: 構文・評価・トートロジー (phase6c と同一) -/

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

/-- 論証的トートロジー: すべての真理値割当で真。 -/
def Taut (f : Form) : Prop := ∀ v : ℕ → Bool, evalB v f = true

noncomputable def interp (env : ℕ → IProp) : Form → IProp
  | .var n    => env n
  | .tru      => itrue
  | .fls      => inot itrue
  | .conj f g => iand (interp env f) (interp env g)
  | .disj f g => ior (interp env f) (interp env g)
  | .neg f    => inot (interp env f)
  | .iffF f g => iiff (interp env f) (interp env g)

/-- Ax.(iii) 本体、但し書き付き (phase6c と同一)。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

/-! ## 整合性の公理 (phase6c と同一) -/

axiom cons_true : Cons itrue
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## 移植定理 (phase6c と同一の証明) -/

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

/-- 第13章の (12) (folio 141) の短い証明 (phase6c の th_12_i_short と同一)。 -/
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

/-- 認証代入 (th_12_i_short 経由; def_VIII_i を用いない)。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i_short _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-- **Th.(14.36) 内包版** 乗法定理 (無関連性下、phase6c と同一)。§5 (folio 342) の
「the theorems of multiplication」。 -/
theorem th_14_36_i (a b h : IProp) (hindep : PrI a (iand b h) = PrI a h) :
    PrI (iand a b) h = PrI a h * PrI b h := by
  have hx := def_X_left_i a b h
  rw [hindep] at hx
  exact hx

/-! ## Def. XIII・XIV (folio 138、phase10a と同形) -/

/-- **Def. XIII** (folio 138): 「If a₁/a₂h = a₁/h and a₂/a₁h = a₂/h, the
probabilities a₁/h and a₂/h are independent.」 -/
def Independent (a₁ a₂ h : IProp) : Prop :=
  PrI a₁ (iand a₂ h) = PrI a₁ h ∧ PrI a₂ (iand a₁ h) = PrI a₂ h

/-- **Def. XIV** (folio 138): 「If a₁/a₂h = a₁/h, a₂ is irrelevant … to a₁/h.」 -/
def Irrelevant (a₂ a₁ h : IProp) : Prop := PrI a₁ (iand a₂ h) = PrI a₁ h

/-- Def. XIV の対称形 (phase10a の th_12_XIV_symm と同一)。 -/
theorem th_12_XIV_symm (a₁ a₂ h : IProp) (hirr : PrI a₁ (iand a₂ h) = PrI a₁ h)
    (h1 : PrI a₁ h ≠ 0) :
    PrI a₂ (iand a₁ h) = PrI a₂ h := by
  have hl := def_X_left_i a₁ a₂ h
  have hr := def_X_right_i a₁ a₂ h
  rw [hirr] at hl
  have heq : PrI a₁ h * PrI a₂ (iand a₁ h) = PrI a₁ h * PrI a₂ h := by
    rw [mul_comm (PrI a₁ h) (PrI a₂ (iand a₁ h)), ← hr, hl, mul_comm]
  exact mul_left_cancel₀ h1 heq

/-! ## 補題 (第 II 部の公理から) -/

/-- 前提側の ⊤ は外せる: c/(⊤ ∧ h) = c/h (h 整合)。Def. X 左形
(c ∧ ⊤)/h = c/(⊤ ∧ h) · ⊤/h と、認証代入 (c ∧ ⊤)/h = c/h から。 -/
theorem pr_true_prem (c h : IProp) (hc : Cons h) : PrI c (iand itrue h) = PrI c h := by
  have hx := def_X_left_i c itrue h
  rw [itrue_certain h hc, mul_one] at hx
  have hs : PrI (iand c itrue) h = PrI c h :=
    subst_taut (Form.conj (Form.var 0) Form.tru) (Form.var 0) (fun _ => c) h hc
      (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  rw [← hx, hs]

/-- 前提に含まれる命題は確実: X/(X ∧ k) = 1 (k と X ∧ k が整合)。Def. X 左形
(X ∧ X)/k = X/(X ∧ k) · X/k と認証代入 (X ∧ X)/k = X/k、X/k ≠ 0 (Def. VI の印刷の向き)。
def_VIII_i を通らない。 -/
theorem pr_self_prem (X k : IProp) (hc : Cons k) (hcx : Cons (iand X k)) :
    PrI X (iand X k) = 1 := by
  have hx := def_X_left_i X X k
  have hs : PrI (iand X X) k = PrI X k :=
    subst_taut (Form.conj (Form.var 0) (Form.var 0)) (Form.var 0) (fun _ => X) k hc
      (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  have hne : PrI X k ≠ 0 := cons_of_pos_src X k hcx
  rw [hs] at hx
  have : PrI X k * PrI X (iand X k) = PrI X k * 1 := by rw [mul_one, mul_comm]; exact hx.symm
  exact mul_left_cancel₀ hne this

/-- 選言の一方が確実なら選言も確実: A/k = 1 ならば (A ∨ B)/k = 1 (k 整合)。
Def. IX で (A ∨ B)/k = ((A ∨ B) ∧ Ā)/k + ((A ∨ B) ∧ A)/k、後者は認証代入で A/k。 -/
theorem pr_ior_left_certain (A B k : IProp) (hc : Cons k) (hA : PrI A k = 1) :
    PrI (ior A B) k = 1 := by
  have s := def_IX_i (ior A B) A k
  have e : PrI (iand (ior A B) A) k = PrI A k :=
    subst_taut (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.var 0)) (Form.var 0)
      (fun n => match n with | 0 => A | _ => B) k hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have lo := ax_range_lo_i (iand (ior A B) (inot A)) k
  have hi := ax_range_hi_i (ior A B) k
  linarith

/-! ## 記法 (041・044・049・054、定義のみ) -/

/-- **y_r** (folio 343、§6): 「y_r represents the statement that the event has occurred on each
of r successive occasions」。y 0 = itrue (0 回の連続は何も主張しない)、
y (r+1) = a_{r+1} ∧ y_r。 -/
noncomputable def y (a : ℕ → IProp) : ℕ → IProp
  | 0 => itrue
  | r + 1 => iand (a (r + 1)) (y a r)

/-- **_m x_n** (folio 343、§6、台帳 ch29-041; 第 2 添字の n+1 は ch29-044):
「the event has occurred on m out of n occasions and has not occurred on the others」。
最初の n 回について、最後の回 a_n を肯定するか否定するかで分けた選言。m = n では
第 2 の選言肢 (n 回のうち n+1 回) が不可能なので省く (ファイル先頭の注)。 -/
noncomputable def x (a : ℕ → IProp) : ℕ → ℕ → IProp
  | 0, 0 => itrue
  | _ + 1, 0 => inot itrue
  | 0, n + 1 => iand (inot (a (n + 1))) (x a 0 n)
  | m + 1, n + 1 =>
      if m = n then iand (a (n + 1)) (x a m n)
      else ior (iand (a (n + 1)) (x a m n)) (iand (inot (a (n + 1))) (x a (m + 1) n))

/-- _r x_r と y_r は同じ項 (r 回のうち r 回 = r 回続けて)。 -/
theorem x_diag (a : ℕ → IProp) : ∀ r, x a r r = y a r
  | 0 => by simp [x, y]
  | r + 1 => by simp [x, y, x_diag a r]

/-- **p** (folio 343、§6、台帳 ch29-042): 「let _1x_1/h = p」の名付け。 -/
noncomputable def pB (a : ℕ → IProp) (h : IProp) : ℝ := PrI (x a 1 1) h

/-- **y_s/y_{s−1}h** (folio 343、§6、台帳 ch29-049): s 回目の成功の、前の s−1 回が
すべて成功したという知識の下での確率関係 (s ≥ 1 で用いる)。 -/
noncomputable def yfac (a : ℕ → IProp) (h : IProp) (s : ℕ) : ℝ :=
  PrI (y a s) (iand (y a (s - 1)) h)

/-- **a_s . . . ā_t . . .** (folio 344、§7、台帳 ch29-054 `a_1 a_2 . . .`): 系列の成員を
肯定 (true) または否定 (false、ā_t) して並置した連言。空の並置は itrue。 -/
noncomputable def lits (a : ℕ → IProp) : List (ℕ × Bool) → IProp
  | [] => itrue
  | (s, b) :: L => iand (if b then a s else inot (a s)) (lits a L)

/-- y_r を a_r a_{r−1} . . . a_1 の並置として書く成員の並び。 -/
def run : ℕ → List (ℕ × Bool)
  | 0 => []
  | r + 1 => (r + 1, true) :: run r

theorem lits_run (a : ℕ → IProp) : ∀ r, lits a (run r) = y a r
  | 0 => rfl
  | r + 1 => by simp [lits, run, y, lits_run a r]

theorem run_fst_le : ∀ r, ∀ k ∈ (run r).map Prod.fst, k ≤ r
  | 0 => by simp [run]
  | r + 1 => by
      intro k hk
      simp only [run, List.map_cons, List.mem_cons] at hk
      rcases hk with hk | hk
      · omega
      · have := run_fst_le r k hk; omega

/-! ## 前提の形 (043・052・053 と、依頼の y 形) -/

/-- **043 の形** (folio 343、§6): `_{m+1}x_{n+1} / _m x_n . h = _1x_1 / h` (m ≤ n)。
前提 _m x_n ∧ h が整合な場合に限る (公理 (i): 確率関係は整合な前提について存在する)。 -/
def Cond043 (a : ℕ → IProp) (h : IProp) : Prop :=
  ∀ m n, m ≤ n → Cons (iand (x a m n) h) →
    PrI (x a (m + 1) (n + 1)) (iand (x a m n) h) = PrI (x a 1 1) h

/-- **052 の形** (folio 344、§7 (i.)): `a_1/h = a_2/h . . . = a_r/h`。 -/
def EqualChance (a : ℕ → IProp) (h : IProp) : Prop :=
  ∀ r, 1 ≤ r → PrI (a r) h = PrI (a 1) h

/-- **053 の形** (folio 344、§7 (ii.)): `a_r / a_s . . . ā_t . . . h = a_r / h`。
a_r 自身を含まない成員の肯定・否定の並置 L について、前提 L ∧ h が整合な場合に限る。 -/
def IndepII (a : ℕ → IProp) (h : IProp) : Prop :=
  ∀ r (L : List (ℕ × Bool)), r ∉ L.map Prod.fst → Cons (iand (lits a L) h) →
    PrI (a r) (iand (lits a L) h) = PrI (a r) h

/-- 依頼の y 形の独立: 次の 1 回 a_{r+1} は前の r 回の連続成功 y_r に依らない
(前提 y_r ∧ h が整合な場合)。 -/
def BernoulliIndependent (a : ℕ → IProp) (h : IProp) : Prop :=
  ∀ r, Cons (iand (y a r) h) → PrI (a (r + 1)) (iand (y a r) h) = PrI (a (r + 1)) h

/-- 依頼の等確率: どの回も確率 p。 -/
def EqualChanceP (a : ℕ → IProp) (h : IProp) (p : ℝ) : Prop :=
  ∀ r, PrI (a (r + 1)) h = p

/-! ## 042 (名付け)・045・046 (第 II 部の公理だけで閉じる) -/

/-- **ch29-042** (folio 343): `_1x_1 / h = p` — p の名付けそのもの (pB の定義の展開、rfl)。
台帳の判定は「未 (定義のみ: pB の名付け)」で、この定理は判定に使わない。 -/
theorem th_29_042 (a : ℕ → IProp) (h : IProp) : PrI (x a 1 1) h = pB a h := rfl

/-- p = _1x_1/h = a_1/h (h 整合)。_1x_1 = a_1 ∧ ⊤ なので認証代入で。 -/
theorem pB_eq_a1 (a : ℕ → IProp) (h : IProp) (hc : Cons h) : pB a h = PrI (a 1) h := by
  have hx : x a 1 1 = iand (a 1) itrue := by simp [x]
  unfold pB
  rw [hx]
  exact subst_taut (Form.conj (Form.var 0) Form.tru) (Form.var 0) (fun _ => a 1) h hc
    (by intro v; cases h0 : v 0 <;> simp [evalB, h0])

/-- **ch29-045 の a 形**: y_{r+1}/h = a_{r+1}/y_r h · y_r/h。Def. X 左形そのもの
(Cons 不要)。phase9a の J_succ (F20.10) と同じ形。 -/
theorem th_29_045_a (a : ℕ → IProp) (h : IProp) (r : ℕ) :
    PrI (y a (r + 1)) h = PrI (a (r + 1)) (iand (y a r) h) * PrI (y a r) h :=
  def_X_left_i _ _ _

/-- **ch29-045** (folio 343): `y_r / h = y_r / y_{r−1} h . y_{r−1} / h` (r ≥ 1)。
Def. X 左形 (y_r ∧ y_{r−1})/h = y_r/y_{r−1}h · y_{r−1}/h と、認証代入
(y_r ∧ y_{r−1} ≡ y_r、y_r = a_r ∧ y_{r−1} なので恒真) から。前提 Cons h は認証代入の
但し書き (公理 (i))。 -/
theorem th_29_045 (a : ℕ → IProp) (h : IProp) (hc : Cons h) (r : ℕ) (hr : 1 ≤ r) :
    PrI (y a r) h = PrI (y a r) (iand (y a (r - 1)) h) * PrI (y a (r - 1)) h := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hx := def_X_left_i (y a (k + 1)) (y a k) h
  have hs : PrI (iand (y a (k + 1)) (y a k)) h = PrI (y a (k + 1)) h :=
    subst_taut (Form.conj (Form.conj (Form.var 0) (Form.var 1)) (Form.var 1))
      (Form.conj (Form.var 0) (Form.var 1))
      (fun n => match n with | 0 => a (k + 1) | _ => y a k) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  rw [← hs, hx]

/-- **ch29-046** (folio 343): `y_r / h = Π_{s=1}^{s=r} y_s / y_{s−1} h`。045 の反復と
y_0/h = ⊤/h = 1 (Ax. (iii)、h 整合)。 -/
theorem th_29_046 (a : ℕ → IProp) (h : IProp) (hc : Cons h) (r : ℕ) :
    PrI (y a r) h = ∏ s ∈ Finset.Icc 1 r, PrI (y a s) (iand (y a (s - 1)) h) := by
  induction r with
  | zero => simp [y, itrue_certain h hc]
  | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ← ih, th_29_045 a h hc (k + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      ring

/-! ## 047・048 (前提を仮定に取れば第 II 部の公理だけで閉じる) -/

/-- **ch29-047 の一般形 (043 から)**: 043 の形の前提の下で y_r/h = p^r。043 の対角
(m = n) だけを使う。y_r/h = 0 の場合は 045 の a 形で y_{r+1}/h = 0。それ以外は
cons_of_pos で y_r ∧ h が整合なので 043 が使える。 -/
theorem th_29_047_of43 (a : ℕ → IProp) (h : IProp) (hc : Cons h) (h43 : Cond043 a h) :
    ∀ r, PrI (y a r) h = pB a h ^ r := by
  intro r
  induction r with
  | zero => simp [y, itrue_certain h hc]
  | succ k ih =>
      by_cases hz : PrI (y a k) h = 0
      · have hp : pB a h ^ k = 0 := by rw [← ih, hz]
        rw [th_29_045_a, hz, mul_zero, pow_succ, hp, zero_mul]
      · have hck : Cons (iand (x a k k) h) := by
          rw [x_diag]; exact cons_of_pos _ _ hz hc
        have hf := h43 k k le_rfl hck
        rw [x_diag, x_diag] at hf
        rw [th_29_045 a h hc (k + 1) (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [hf, ih, pow_succ]
        unfold pB
        ring

/-- **ch29-047 の一般形 (依頼の y 形の独立 + 等確率から)**: 乗法定理 th_14_36_i の反復。
y_r/h = 0 の場合は 045 の a 形で 0。 -/
theorem th_29_047_of (a : ℕ → IProp) (h : IProp) (p : ℝ) (hc : Cons h)
    (hind : BernoulliIndependent a h) (heq : EqualChanceP a h p) :
    ∀ r, PrI (y a r) h = p ^ r := by
  intro r
  induction r with
  | zero => simp [y, itrue_certain h hc]
  | succ k ih =>
      by_cases hz : PrI (y a k) h = 0
      · have hp : p ^ k = 0 := by rw [← ih, hz]
        rw [th_29_045_a, hz, mul_zero, pow_succ, hp, zero_mul]
      · have hck : Cons (iand (y a k) h) := cons_of_pos _ _ hz hc
        have hm := th_14_36_i (a (k + 1)) (y a k) h (hind k hck)
        show PrI (iand (a (k + 1)) (y a k)) h = p ^ (k + 1)
        rw [hm, heq k, ih, pow_succ, mul_comm]

/-- **ch29-048 (「must have」の含意)** (folio 343): 「if we are to have y_r/h = p^r, we must
have y_s/y_{s−1}h = p for all values of s from 1 to r」。r 以下のすべての長さ s で
y_s/h = p^s が成り立ち p ≠ 0 ならば、1 ≤ s ≤ r のすべての s で y_s/y_{s−1}h = p。
045 で y_s/h = y_s/y_{s−1}h · y_{s−1}/h を p^{s−1} で割る。補った前提: p ≠ 0 と
「r 以下のすべての長さで」の読み。後者は印刷の文の代数的な同値変形ではなく読みの補いである。
単一の r の読みについては実数の算術上の反例 nec_29_048_single があるが、担体上の模型ではない。 -/
theorem th_29_048 (a : ℕ → IProp) (h : IProp) (p : ℝ) (hc : Cons h) (r : ℕ)
    (hall : ∀ s, s ≤ r → PrI (y a s) h = p ^ s) (hp : p ≠ 0) :
    ∀ s, 1 ≤ s → s ≤ r → yfac a h s = p := by
  intro s hs1 hsr
  have h45 := th_29_045 a h hc s hs1
  rw [hall s hsr, hall (s - 1) (by omega)] at h45
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h45
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp
  unfold yfac
  simp only [Nat.add_sub_cancel]
  rw [pow_succ] at h45
  exact (mul_right_cancel₀ hpk (by rw [← h45]; ring)).symm

/-- **048 の逆向き (Keynes の「Hence」)**: 1 ≤ s ≤ r のすべての s で y_s/y_{s−1}h = p
ならば y_r/h = p^r。046 の積がすべて p。 -/
theorem th_29_048_to_047 (a : ℕ → IProp) (h : IProp) (p : ℝ) (hc : Cons h) (r : ℕ)
    (hf : ∀ s, 1 ≤ s → s ≤ r → yfac a h s = p) :
    PrI (y a r) h = p ^ r := by
  have hc' : ∏ s ∈ Finset.Icc 1 r, PrI (y a s) (iand (y a (s - 1)) h)
      = ∏ _s ∈ Finset.Icc 1 r, p :=
    Finset.prod_congr rfl (fun s hs => hf s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2)
  rw [th_29_046 a h hc r, hc', Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]

/-- **048 の単一の r の読み (数値例)**: 積が p^r でも各因子が p とは限らない。
r = 2、p = 1/4、因子 1/2 と 1/8。実数の算術上の反例であり、担体上の模型 (この値をとる
IProp の系列) ではない。 -/
theorem nec_29_048_single :
    (1 / 2 : ℝ) * (1 / 8) = (1 / 4) ^ 2 ∧ (1 / 2 : ℝ) ≠ 1 / 4 := by
  norm_num

/-! ## 第 29 章の data 上の印刷形 (外部公理) -/

/-- 第 29 章の事象の系列 a_r (r 回目にその事象が起こる) の名付け。 -/
axiom a29 : ℕ → IProp
/-- 第 29 章の à priori data h の名付け。 -/
axiom h29 : IProp

/-- **外部公理**: h は矛盾する連言でない (公理 (i) の但し書きを第 29 章の data に当てはめたもの)。 -/
axiom ax_data_cons29 : Cons h29

/-- **外部公理 (ch29-043)** (folio 343、§6): Bernoulli の定理が要する典型的条件
`_{m+1}x_{n+1} / _m x_n . h = _1x_1 / h`。但し書き Cons (_m x_n ∧ h) 付き。 -/
axiom ax_bernoulli_independence : Cond043 a29 h29

/-- **外部公理 (ch29-052)** (folio 344、§7 (i.)): `a_1/h = a_2/h . . . = a_r/h`。 -/
axiom ax_equal_chance : EqualChance a29 h29

/-- **外部公理 (ch29-053)** (folio 344、§7 (ii.)): `a_r / a_s . . . ā_t . . . h = a_r / h`。
但し書き Cons (a_s…ā_t… ∧ h) 付き。 -/
axiom ax_independence_ii : IndepII a29 h29

/-- **ch29-043** (folio 343): `_{m+1}x_{n+1} / _m x_n . h = _1x_1 / h`。外部公理そのもの。 -/
theorem th_29_043 (m n : ℕ) (hmn : m ≤ n) (hc : Cons (iand (x a29 m n) h29)) :
    PrI (x a29 (m + 1) (n + 1)) (iand (x a29 m n) h29) = PrI (x a29 1 1) h29 :=
  ax_bernoulli_independence m n hmn hc

/-- **ch29-047** (folio 343): `y_r / h = p^r` — 第 29 章の data 上、§6 の経路
(043 → 045・046 → 047)。★ 主結果: #print axioms に外部公理 ax_bernoulli_independence・
ax_data_cons29 と名付け a29・h29 が出る。 -/
theorem th_29_047 (r : ℕ) : PrI (y a29 r) h29 = pB a29 h29 ^ r :=
  th_29_047_of43 a29 h29 ax_data_cons29 ax_bernoulli_independence r

/-- **ch29-048** (folio 343): `y_s / y_{s−1} h = p` — 第 29 章の data 上、043 の対角から。
s = 1 では前提 y_0 ∧ h が整合 (⊤/h = 1)、s ≥ 2 では p ≠ 0 のとき y_{s−1}/h = p^{s−1} ≠ 0。 -/
theorem th_29_048_data (hp : pB a29 h29 ≠ 0) (s : ℕ) (hs : 1 ≤ s) :
    yfac a29 h29 s = pB a29 h29 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hz : PrI (y a29 k) h29 ≠ 0 := by
    rw [th_29_047]; exact pow_ne_zero k hp
  have hck : Cons (iand (x a29 k k) h29) := by
    rw [x_diag]; exact cons_of_pos _ _ hz ax_data_cons29
  have hf := ax_bernoulli_independence k k le_rfl hck
  rw [x_diag, x_diag] at hf
  unfold yfac pB
  simp only [Nat.add_sub_cancel]
  exact hf

/-- **ch29-052** (folio 344、§7 (i.)): `a_1/h = a_2/h . . . = a_r/h`。外部公理そのもの。 -/
theorem th_29_052 (r : ℕ) (hr : 1 ≤ r) : PrI (a29 r) h29 = PrI (a29 1) h29 :=
  ax_equal_chance r hr

/-- **ch29-053** (folio 344、§7 (ii.)): `a_r / a_s . . . ā_t . . . h = a_r / h`。外部公理そのもの。 -/
theorem th_29_053 (r : ℕ) (L : List (ℕ × Bool)) (hr : r ∉ L.map Prod.fst)
    (hc : Cons (iand (lits a29 L) h29)) :
    PrI (a29 r) (iand (lits a29 L) h29) = PrI (a29 r) h29 :=
  ax_independence_ii r L hr hc

/-! ## 053 と Def. XIII の関係 (第 II 部の公理だけ) -/

/-- **053 は Def. XIV の形**: (ii.) の 1 式は「並置 L は a_r/h に無関連」(Def. XIV) と
同じ文 (定義の展開)。 -/
theorem th_29_053_is_XIV (a : ℕ → IProp) (h : IProp) (r : ℕ) (L : List (ℕ × Bool)) :
    PrI (a r) (iand (lits a L) h) = PrI (a r) h ↔ Irrelevant (lits a L) (a r) h :=
  Iff.rfl

/-- **053 から Def. XIII へ**: (ii.) の 1 式と a_r/h ≠ 0 から、a_r/h と L/h は独立
(Def. XIII の 2 式)。Def. XIII は定義なので、ある系列が (ii.) を満たすことは Def. XIII から
は出ない (053 は仮定として置く、ax_independence_ii)。 -/
theorem th_29_053_XIII (a : ℕ → IProp) (h : IProp) (r : ℕ) (L : List (ℕ × Bool))
    (h53 : PrI (a r) (iand (lits a L) h) = PrI (a r) h) (hne : PrI (a r) h ≠ 0) :
    Independent (a r) (lits a L) h :=
  ⟨h53, th_12_XIV_symm (a r) (lits a L) h h53 hne⟩

/-- **053 から依頼の y 形の独立へ**: y_r = a_r a_{r−1} . . . a_1 は a_{r+1} を含まない並置。 -/
theorem bernoulliIndependent_of_ii (a : ℕ → IProp) (h : IProp) (h53 : IndepII a h) :
    BernoulliIndependent a h := by
  intro r hc
  have hnot : r + 1 ∉ (run r).map Prod.fst := by
    intro hm; have := run_fst_le r (r + 1) hm; omega
  have := h53 (r + 1) (run r) hnot (by rw [lits_run]; exact hc)
  rwa [lits_run] at this

/-- **052 から依頼の等確率へ** (p = _1x_1/h、h 整合)。 -/
theorem equalChanceP_of_i (a : ℕ → IProp) (h : IProp) (hc : Cons h) (h52 : EqualChance a h) :
    EqualChanceP a h (pB a h) := by
  intro r
  rw [h52 (r + 1) (by omega), pB_eq_a1 a h hc]

/-- **ch29-047、§7 の経路** (folio 344 の (i.)(ii.) から): 第 29 章の data 上で
y_r/h = p^r。#print axioms に ax_equal_chance・ax_independence_ii・ax_data_cons29 が出る
(ax_bernoulli_independence は出ない)。 -/
theorem th_29_047_ii (r : ℕ) : PrI (y a29 r) h29 = pB a29 h29 ^ r :=
  th_29_047_of a29 h29 (pB a29 h29) ax_data_cons29
    (bernoulliIndependent_of_ii a29 h29 ax_independence_ii)
    (equalChanceP_of_i a29 h29 ax_data_cons29 ax_equal_chance) r

/-! ## 050 (Keynes の但し書き: 独立でない場合) -/

/-- s = 1 の因子は p: y_1/y_0 h = y_1/(⊤ ∧ h) = y_1/h = _1x_1/h (h 整合)。 -/
theorem yfac_one (a : ℕ → IProp) (h : IProp) (hc : Cons h) : yfac a h 1 = pB a h := by
  unfold yfac pB
  rw [x_diag]
  exact pr_true_prem (y a 1) h hc

/-- 増加列は初項以上: 1 ≤ s ≤ r で yfac 1 ≤ yfac s。 -/
theorem yfac_ge_first (f : ℕ → ℝ) (r : ℕ) (hinc : ∀ s, 1 ≤ s → s < r → f s < f (s + 1)) :
    ∀ s, 1 ≤ s → s ≤ r → f 1 ≤ f s := by
  intro s hs1 hsr
  induction s with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact le_rfl
      · exact le_of_lt (lt_of_le_of_lt (ih hk (by omega)) (hinc k hk (by omega)))

/-- **ch29-050** (folio 343): 「in many particular examples y_s/y_{s−1}h increases with s, so
that y_r/h > p^r」。y_s/y_{s−1}h が 1 ≤ s ≤ r で s とともに (狭義に) 増すとき、
y_r/h > p^r。補った前提: p > 0 (p = 0 なら両辺 0) と r ≥ 2 (r = 1 なら等号)。
F29.10 の分類は S (条件の省略) で、判定は ≈。
046 の積の各因子が p 以上で、s = 2 の因子は p より大きい。 -/
theorem th_29_050 (a : ℕ → IProp) (h : IProp) (hc : Cons h) (r : ℕ) (hr : 2 ≤ r)
    (hp : 0 < pB a h) (hinc : ∀ s, 1 ≤ s → s < r → yfac a h s < yfac a h (s + 1)) :
    PrI (y a r) h > pB a h ^ r := by
  have hge := yfac_ge_first (yfac a h) r hinc
  rw [yfac_one a h hc] at hge
  have h46 : PrI (y a r) h = ∏ s ∈ Finset.Icc 1 r, yfac a h s := th_29_046 a h hc r
  have hconst : pB a h ^ r = ∏ _s ∈ Finset.Icc 1 r, pB a h := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [h46, hconst, gt_iff_lt]
  apply Finset.prod_lt_prod
  · intro s _; exact hp
  · intro s hs; rw [Finset.mem_Icc] at hs; exact hge s hs.1 hs.2
  · refine ⟨2, Finset.mem_Icc.mpr ⟨by omega, hr⟩, ?_⟩
    have := hinc 1 le_rfl (by omega)
    rw [yfac_one a h hc] at this
    exact this

/-- **050 の向きは増加の前提から来る (双対)**: 因子が s とともに (狭義に) 減り、すべて正なら
y_r/h < p^r。独立でないことだけからは > は従わない (向きは因子の増減で決まる)。
この減少をとる IProp の系列 (模型) は作らない。 -/
theorem th_29_050_dual (a : ℕ → IProp) (h : IProp) (hc : Cons h) (r : ℕ) (hr : 2 ≤ r)
    (hpos : ∀ s, 1 ≤ s → s ≤ r → 0 < yfac a h s)
    (hdec : ∀ s, 1 ≤ s → s < r → yfac a h (s + 1) < yfac a h s) :
    PrI (y a r) h < pB a h ^ r := by
  have hle : ∀ s, 1 ≤ s → s ≤ r → yfac a h s ≤ yfac a h 1 := by
    have := yfac_ge_first (fun s => - yfac a h s) r (fun s h1 h2 => by
      have := hdec s h1 h2; simp only; linarith)
    intro s h1 h2; have := this s h1 h2; simp only at this; linarith
  rw [yfac_one a h hc] at hle
  have h46 : PrI (y a r) h = ∏ s ∈ Finset.Icc 1 r, yfac a h s := th_29_046 a h hc r
  have hconst : pB a h ^ r = ∏ _s ∈ Finset.Icc 1 r, pB a h := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [h46, hconst]
  apply Finset.prod_lt_prod
  · intro s hs; rw [Finset.mem_Icc] at hs; exact hpos s hs.1 hs.2
  · intro s hs; rw [Finset.mem_Icc] at hs; exact hle s hs.1 hs.2
  · refine ⟨2, Finset.mem_Icc.mpr ⟨by omega, hr⟩, ?_⟩
    have := hdec 1 le_rfl (by omega)
    rw [yfac_one a h hc] at this
    exact this

/-- **050 の場合は 043 の外にある**: 043 の下では y_2/y_1 h = p = y_1/y_0 h なので
(p ≠ 0 のとき)、因子が s = 1 から s = 2 へ増すことはない。 -/
theorem th_29_050_not_043 (a : ℕ → IProp) (h : IProp) (hc : Cons h) (h43 : Cond043 a h)
    (hp : pB a h ≠ 0) : ¬ (yfac a h 1 < yfac a h 2) := by
  have hz : PrI (y a 1) h ≠ 0 := by
    rw [th_29_047_of43 a h hc h43 1, pow_one]; exact hp
  have hck : Cons (iand (x a 1 1) h) := by
    rw [x_diag]; exact cons_of_pos _ _ hz hc
  have hf := h43 1 1 le_rfl hck
  rw [x_diag, x_diag] at hf
  have h2 : yfac a h 2 = pB a h := by unfold yfac pB; exact hf
  rw [h2, yfac_one a h hc]
  exact lt_irrefl _

/-! ## 051 (数値例) -/

set_option exponentiation.threshold 1024 in
/-- **ch29-051** (folio 343): `(½)^{1000}` — 「not usually so infinitesimally small as
(½)^1000」。(½)^1000 = 1/2^1000 は 10^{−302} と 10^{−301} の間。冪の評価の上限
(既定 256) をこの定理に限り 1024 に上げる。 -/
theorem th_29_051 :
    (1 / 2 : ℝ) ^ 1000 = 1 / 2 ^ 1000 ∧
    1 / (10 : ℝ) ^ 302 < (1 / 2 : ℝ) ^ 1000 ∧ (1 / 2 : ℝ) ^ 1000 < 1 / (10 : ℝ) ^ 301 := by
  rw [div_pow, one_pow]
  refine ⟨rfl, ?_, ?_⟩
  · exact one_div_lt_one_div_of_lt (by positivity) (by norm_num)
  · exact one_div_lt_one_div_of_lt (by positivity) (by norm_num)

/-! ## 外部公理の相対無矛盾性 -/

/-- **自明な代入**: a_r := ⊤、h := ⊤ は、第 II 部の公理だけから Cons ⊤ と 043・052・053 の
3 条件を満たす。a29・h29 は新しい定数なので、第 II 部の公理群の任意の模型で a29 := fun _ => ⊤、
h29 := ⊤ と読めば外部公理がすべて成り立つ。ただし p = 1 の模型であり、0 < p < 1 の場合の
無矛盾性はこの定理からは出ない。 -/
theorem rel_cons_trivial :
    Cons itrue ∧ Cond043 (fun _ => itrue) itrue ∧ EqualChance (fun _ => itrue) itrue ∧
      IndepII (fun _ => itrue) itrue := by
  refine ⟨cons_true, ?_, fun _ _ => rfl, ?_⟩
  · intro m n _ hck
    have hrhs : PrI (x (fun _ => itrue) 1 1) itrue = 1 := by
      have hx : x (fun _ => itrue) 1 1 = iand itrue itrue := by simp [x]
      rw [hx, true_conj itrue itrue cons_true, itrue_certain itrue cons_true]
    rw [hrhs]
    have hself := pr_self_prem (x (fun _ => itrue) m n) itrue cons_true hck
    have hA : PrI (iand itrue (x (fun _ => itrue) m n))
        (iand (x (fun _ => itrue) m n) itrue) = 1 := by
      rw [true_conj _ _ hck, hself]
    by_cases hmn : m = n
    · subst hmn
      have hx : x (fun _ => itrue) (m + 1) (m + 1) = iand itrue (x (fun _ => itrue) m m) := by
        simp [x]
      rw [hx]; exact hA
    · have hx : x (fun _ => itrue) (m + 1) (n + 1) =
          ior (iand itrue (x (fun _ => itrue) m n))
            (iand (inot itrue) (x (fun _ => itrue) (m + 1) n)) := by
        simp [x, hmn]
      rw [hx]; exact pr_ior_left_certain _ _ _ hck hA
  · intro r L _ hc
    show PrI itrue (iand (lits (fun _ => itrue) L) itrue) = PrI itrue itrue
    rw [itrue_certain _ hc, itrue_certain _ cons_true]

end KeynesXXIX

/-! ## 有限模型: 043・052・053 は第 II 部の公理群から導けない (phase12b の流儀)

axiom 宣言そのものは模型にできないので、phase12b と同じく第 II 部の公理の文 13 本を
構造 `Sys` に写し、重み付きの有限模型 (世界 Fin 3、命題 = 世界の集合、確率関係 =
条件付きの重みの比、Cons = 空でない) がそれを満たすことを証明する (`wSys`)。記法 x・y・lits
と前提の形 Cond043・EqualChance・IndepII を同じ文で場 `S` の上に写し、重み (1, 1, 1) の
模型 M₁ で、整合な h := ⊤ と系列 a_1 := {0}、a_r := {0, 1} (r ≠ 1) について 3 条件が
いずれも偽になることを示す。この系列では a_1 が a_2 を含むので y_2/y_1 h = 1 > 1/3 = y_1/h
であり、050 の「y_s/y_{s−1}h increases with s」の場合にあたる。 -/

namespace KeynesXXIX_model

open KeynesXXIX (Form evalB Taut)

/-- 結合子・確率関係・整合性述語の組 (phase12b と同一)。 -/
structure Ops where
  IProp : Type
  iand : IProp → IProp → IProp
  ior  : IProp → IProp → IProp
  inot : IProp → IProp
  iiff : IProp → IProp → IProp
  itrue : IProp
  PrI : IProp → IProp → ℝ
  Cons : IProp → Prop

/-- 構文の解釈 (KeynesXXIX.interp と同じ形)。 -/
def Ops.interp (S : Ops) (env : ℕ → S.IProp) : Form → S.IProp
  | .var n    => env n
  | .tru      => S.itrue
  | .fls      => S.inot S.itrue
  | .conj f g => S.iand (S.interp env f) (S.interp env g)
  | .disj f g => S.ior (S.interp env f) (S.interp env g)
  | .neg f    => S.inot (S.interp env f)
  | .iffF f g => S.iiff (S.interp env f) (S.interp env g)

/-- **第 II 部の公理群** (本ファイル KeynesXXIX の axiom 13 本の文をそのまま場に写したもの;
phase12b の Sys と同一)。 -/
structure Sys (S : Ops) : Prop where
  def_IX_i : ∀ p q h, S.PrI (S.iand p (S.inot q)) h + S.PrI (S.iand p q) h = S.PrI p h
  def_X_left_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI p (S.iand q h) * S.PrI q h
  def_X_right_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI q (S.iand p h) * S.PrI p h
  def_XI_i : ∀ (P Q R : ℝ), Q ≠ 0 → P * Q = R → P = R / Q
  ax_range_lo_i : ∀ p h, 0 ≤ S.PrI p h
  ax_range_hi_i : ∀ p h, S.PrI p h ≤ 1
  def_VIII_i : ∀ a b h, S.Cons (S.iand a h) → S.Cons (S.iand b h) →
    (S.PrI (S.iiff a b) h = 1 ↔ (S.PrI b (S.iand a h) = 1 ∧ S.PrI a (S.iand b h) = 1))
  def_VIII_i_src : ∀ a b h,
    S.PrI b (S.iand a h) = 1 → S.PrI a (S.iand b h) = 1 → S.PrI (S.iiff a b) h = 1
  ax_iii_taut : ∀ (f : Form) (env : ℕ → S.IProp) (h : S.IProp),
    S.Cons h → Taut f → S.PrI (S.interp env f) h = 1
  cons_true : S.Cons S.itrue
  cons_of_pos_src : ∀ a h, S.Cons (S.iand a h) → S.PrI a h ≠ 0
  cons_of_pos : ∀ a h, S.PrI a h ≠ 0 → S.Cons h → S.Cons (S.iand a h)
  cons_iff_taut : ∀ (f g : Form) (env : ℕ → S.IProp),
    Taut (Form.iffF f g) → (S.Cons (S.interp env f) ↔ S.Cons (S.interp env g))

/-! ### 記法と前提の形を場 S の上に写す (KeynesXXIX の x・Cond043・EqualChance・IndepII と同じ文) -/

/-- _m x_n (KeynesXXIX.x と同じ場合分け)。 -/
def Ops.x (S : Ops) (a : ℕ → S.IProp) : ℕ → ℕ → S.IProp
  | 0, 0 => S.itrue
  | _ + 1, 0 => S.inot S.itrue
  | 0, n + 1 => S.iand (S.inot (a (n + 1))) (Ops.x S a 0 n)
  | m + 1, n + 1 =>
      if m = n then S.iand (a (n + 1)) (Ops.x S a m n)
      else S.ior (S.iand (a (n + 1)) (Ops.x S a m n))
        (S.iand (S.inot (a (n + 1))) (Ops.x S a (m + 1) n))

/-- y_r (KeynesXXIX.y と同じ)。 -/
def Ops.y (S : Ops) (a : ℕ → S.IProp) : ℕ → S.IProp
  | 0 => S.itrue
  | r + 1 => S.iand (a (r + 1)) (Ops.y S a r)

/-- a_s . . . ā_t . . . (KeynesXXIX.lits と同じ)。 -/
def Ops.lits (S : Ops) (a : ℕ → S.IProp) : List (ℕ × Bool) → S.IProp
  | [] => S.itrue
  | (s, b) :: L => S.iand (if b then a s else S.inot (a s)) (Ops.lits S a L)

/-- 043 の形 (KeynesXXIX.Cond043 と同じ文)。 -/
def Ops.Cond043 (S : Ops) (a : ℕ → S.IProp) (h : S.IProp) : Prop :=
  ∀ m n, m ≤ n → S.Cons (S.iand (S.x a m n) h) →
    S.PrI (S.x a (m + 1) (n + 1)) (S.iand (S.x a m n) h) = S.PrI (S.x a 1 1) h

/-- 052 の形 (KeynesXXIX.EqualChance と同じ文)。 -/
def Ops.EqualChance (S : Ops) (a : ℕ → S.IProp) (h : S.IProp) : Prop :=
  ∀ r, 1 ≤ r → S.PrI (a r) h = S.PrI (a 1) h

/-- 053 の形 (KeynesXXIX.IndepII と同じ文)。 -/
def Ops.IndepII (S : Ops) (a : ℕ → S.IProp) (h : S.IProp) : Prop :=
  ∀ r (L : List (ℕ × Bool)), r ∉ L.map Prod.fst → S.Cons (S.iand (S.lits a L) h) →
    S.PrI (a r) (S.iand (S.lits a L) h) = S.PrI (a r) h

/-! ### 重み付き有限模型 (phase12b §2 と同一の証明) -/

/-- 世界集合。 -/
abbrev W := Fin 3
/-- 命題 = 世界の集合。 -/
abbrev M := Finset W

def mand (p q : M) : M := p ∩ q
def mor  (p q : M) : M := p ∪ q
def mnot (p : M) : M := pᶜ
def miff (p q : M) : M := (p ∩ q) ∪ (pᶜ ∩ qᶜ)
def mtrue : M := Finset.univ

/-- 命題 p に含まれる世界の重みの和。 -/
def mu (wt : W → ℝ) (p : M) : ℝ := ∑ w ∈ p, wt w

/-- 条件付きの重みの比。h = ∅ のときは 0 と約定 (phase6c_model・phase12b と同じ)。 -/
noncomputable def prw (wt : W → ℝ) (p h : M) : ℝ :=
  if h = ∅ then 0 else mu wt (p ∩ h) / mu wt h

/-- 整合性 = 充足可能性。 -/
def mcons (h : M) : Prop := h.Nonempty

section Weighted

variable {wt : W → ℝ} (hw : ∀ w, 0 < wt w)

include hw in
theorem mu_nonneg (p : M) : 0 ≤ mu wt p :=
  Finset.sum_nonneg (fun w _ => (hw w).le)

include hw in
theorem mu_pos {p : M} (hp : p.Nonempty) : 0 < mu wt p :=
  Finset.sum_pos (fun w _ => hw w) hp

theorem prw_of_empty (p : M) : prw wt p ∅ = 0 := by
  simp [prw]

theorem prw_of_ne {p h : M} (hh : h ≠ ∅) : prw wt p h = mu wt (p ∩ h) / mu wt h := by
  rw [prw, if_neg hh]

theorem ne_empty_of_cons {h : M} (hc : mcons h) : h ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp hc

theorem ne_empty_of_inter {a h : M} (hc : a ∩ h ≠ ∅) : h ≠ ∅ := by
  rintro rfl
  exact hc (Finset.inter_empty a)

include hw in
/-- 前提が整合なとき、確実 ⟺ 前提が結論を含む。 -/
theorem prw_eq_one_iff {p h : M} (hh : h ≠ ∅) : prw wt p h = 1 ↔ h ⊆ p := by
  have hpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [prw_of_ne hh, div_eq_one_iff_eq hpos.ne']
  constructor
  · intro H
    by_contra hns
    obtain ⟨w, hwh, hwp⟩ := Finset.not_subset.mp hns
    have e1 : p ∩ h = h.filter (· ∈ p) := by
      ext x; simp [and_comm]
    have hs := Finset.sum_filter_add_sum_filter_not h (· ∈ p) wt
    have hpos2 : 0 < mu wt (h.filter (· ∉ p)) :=
      mu_pos hw ⟨w, by simp [hwh, hwp]⟩
    rw [e1] at H
    unfold mu at H hpos2
    linarith
  · intro H
    rw [Finset.inter_eq_right.mpr H]

/-- 確実ならば h ≠ ∅ (約定 0 ≠ 1)。 -/
theorem ne_empty_of_prw_eq_one {p h : M} (H : prw wt p h = 1) : h ≠ ∅ := by
  rintro rfl
  rw [prw_of_empty] at H
  exact zero_ne_one H

/-- Def. VIII の集合論的中身: h ⊆ (a ≡ b) ⟺ (a ∩ h ⊆ b ∧ b ∩ h ⊆ a)。 -/
theorem subset_miff_iff (a b h : M) :
    h ⊆ miff a b ↔ (a ∩ h ⊆ b ∧ b ∩ h ⊆ a) := by
  simp only [miff, Finset.subset_iff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  constructor
  · intro H
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rcases H hw.2 with ⟨_, hb⟩ | ⟨hna, _⟩
      · exact hb
      · exact absurd hw.1 hna
    · rcases H hw.2 with ⟨ha, _⟩ | ⟨_, hnb⟩
      · exact ha
      · exact absurd hw.1 hnb
  · rintro ⟨H1, H2⟩ w hw
    by_cases ha : w ∈ a
    · exact Or.inl ⟨ha, H1 ⟨ha, hw⟩⟩
    · exact Or.inr ⟨ha, fun hb => ha (H2 ⟨hb, hw⟩)⟩

/-- **Def. IX** (folio 135)。 -/
theorem model_def_IX_i (p q h : M) :
    prw wt (mand p (mnot q)) h + prw wt (mand p q) h = prw wt p h := by
  by_cases hh : h = ∅
  · simp [prw, hh]
  · rw [prw_of_ne hh, prw_of_ne hh, prw_of_ne hh, ← add_div]
    congr 1
    have e1 : mand p q ∩ h = (p ∩ h).filter (· ∈ q) := by
      ext w; simp [mand]; tauto
    have e2 : mand p (mnot q) ∩ h = (p ∩ h).filter (· ∉ q) := by
      ext w; simp [mand, mnot]; tauto
    rw [e1, e2, add_comm]
    exact Finset.sum_filter_add_sum_filter_not _ _ _

include hw in
/-- **Def. X 左形** (folio 135)。 -/
theorem model_def_X_left_i (p q h : M) :
    prw wt (mand p q) h = prw wt p (mand q h) * prw wt q h := by
  by_cases hh : h = ∅
  · subst hh; simp [prw, mand]
  by_cases hqh : mand q h = ∅
  · have hz : mand p q ∩ h = ∅ := by
      have hsub : p ∩ (q ∩ h) ⊆ q ∩ h := Finset.inter_subset_right
      simp only [mand] at hqh ⊢
      rw [Finset.inter_assoc]
      exact Finset.subset_empty.mp (hsub.trans hqh.subset)
    rw [hqh, prw_of_empty, zero_mul, prw_of_ne hh, hz]
    simp [mu]
  · have hqpos : 0 < mu wt (q ∩ h) :=
      mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hqh)
    have hpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
    rw [prw_of_ne hh, prw_of_ne hqh, prw_of_ne hh]
    simp only [mand, Finset.inter_assoc]
    field_simp

include hw in
/-- **Def. X 右形** (folio 135)。 -/
theorem model_def_X_right_i (p q h : M) :
    prw wt (mand p q) h = prw wt q (mand p h) * prw wt p h := by
  have e : mand p q = mand q p := by simp [mand, Finset.inter_comm]
  rw [e]
  exact model_def_X_left_i hw q p h

/-- **Def. XI** (folio 136): 実数の算術。 -/
theorem model_def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q :=
  fun H => (eq_div_iff hQ).mpr H

include hw in
/-- **値域 (下)**。 -/
theorem model_ax_range_lo_i (p h : M) : 0 ≤ prw wt p h := by
  unfold prw
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (mu_nonneg hw _) (mu_nonneg hw _)

include hw in
/-- **値域 (上)**。 -/
theorem model_ax_range_hi_i (p h : M) : prw wt p h ≤ 1 := by
  by_cases hh : h = ∅
  · simp [prw, hh]
  · have hpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
    rw [prw_of_ne hh, div_le_one hpos]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun w _ _ => (hw w).le)

include hw in
/-- **Def. VIII 双条件読み、但し書き付き** (folio 134)。 -/
theorem model_def_VIII_i (a b h : M) (hca : mcons (mand a h)) (hcb : mcons (mand b h)) :
    prw wt (miff a b) h = 1 ↔ (prw wt b (mand a h) = 1 ∧ prw wt a (mand b h) = 1) := by
  have hca' : mand a h ≠ ∅ := ne_empty_of_cons hca
  have hcb' : mand b h ≠ ∅ := ne_empty_of_cons hcb
  have hh : h ≠ ∅ := ne_empty_of_inter hca'
  rw [prw_eq_one_iff hw hh, prw_eq_one_iff hw hca', prw_eq_one_iff hw hcb']
  exact subset_miff_iff a b h

include hw in
/-- **Def. VIII 印刷どおり** (folio 134、→ のみ)。 -/
theorem model_def_VIII_i_src (a b h : M) :
    prw wt b (mand a h) = 1 → prw wt a (mand b h) = 1 → prw wt (miff a b) h = 1 := by
  intro H1 H2
  have hca' := ne_empty_of_prw_eq_one H1
  have hcb' := ne_empty_of_prw_eq_one H2
  have hh : h ≠ ∅ := ne_empty_of_inter hca'
  rw [prw_eq_one_iff hw hca'] at H1
  rw [prw_eq_one_iff hw hcb'] at H2
  rw [prw_eq_one_iff hw hh]
  exact (subset_miff_iff a b h).mpr ⟨H1, H2⟩

end Weighted

/-- 重み wt の模型の結合子の組。 -/
noncomputable def wOps (wt : W → ℝ) : Ops where
  IProp := M
  iand := mand
  ior := mor
  inot := mnot
  iiff := miff
  itrue := mtrue
  PrI := prw wt
  Cons := mcons

/-- 構文の有限模型解釈 (wt によらない)。 -/
def finInterp (env : ℕ → M) : Form → M
  | .var n    => env n
  | .tru      => mtrue
  | .fls      => mnot mtrue
  | .conj f g => mand (finInterp env f) (finInterp env g)
  | .disj f g => mor (finInterp env f) (finInterp env g)
  | .neg f    => mnot (finInterp env f)
  | .iffF f g => miff (finInterp env f) (finInterp env g)

theorem wOps_interp (wt : W → ℝ) (env : ℕ → M) (f : Form) :
    (wOps wt).interp env f = finInterp env f := by
  induction f with
  | var n => rfl
  | tru => rfl
  | fls => rfl
  | conj f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl
  | disj f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl
  | neg f ihf => simp only [Ops.interp]; rw [ihf]; rfl
  | iffF f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl

/-- 解釈の帰属 ⟺ 世界での真理値評価。 -/
theorem mem_finInterp (env : ℕ → M) (f : Form) (w : W) :
    w ∈ finInterp env f ↔ evalB (fun n => decide (w ∈ env n)) f = true := by
  induction f with
  | var n => simp [finInterp, evalB]
  | tru => simp [finInterp, evalB, mtrue]
  | fls => simp [finInterp, evalB, mtrue, mnot]
  | conj f g ihf ihg => simp [finInterp, evalB, mand, ihf, ihg]
  | disj f g ihf ihg => simp [finInterp, evalB, mor, ihf, ihg]
  | neg f ihf => simp [finInterp, evalB, mnot, ihf]
  | iffF f g ihf ihg =>
    simp only [finInterp, evalB, miff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
      ihf, ihg]
    cases evalB (fun n => decide (w ∈ env n)) f <;> cases evalB (fun n => decide (w ∈ env n)) g <;>
      simp

section Weighted2

variable {wt : W → ℝ} (hw : ∀ w, 0 < wt w)

include hw in
/-- **Ax.(iii) 但し書き付き** (folio 135)。 -/
theorem model_ax_iii_taut (f : Form) (env : ℕ → M) (h : M) (hc : mcons h) (ht : Taut f) :
    prw wt (finInterp env f) h = 1 := by
  rw [prw_eq_one_iff hw (ne_empty_of_cons hc)]
  intro w _
  rw [mem_finInterp]
  exact ht _

/-- **cons_true**。 -/
theorem model_cons_true : mcons mtrue := Finset.univ_nonempty

include hw in
/-- **cons_of_pos_src** (Def. VI 印刷の向きの対偶、folio 134)。 -/
theorem model_cons_of_pos_src (a h : M) : mcons (mand a h) → prw wt a h ≠ 0 := by
  intro hca
  have hh : h ≠ ∅ := ne_empty_of_inter (ne_empty_of_cons hca)
  have hhpos : 0 < mu wt h := mu_pos hw (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [prw_of_ne hh]
  exact (div_pos (mu_pos hw hca) hhpos).ne'

/-- **cons_of_pos** (Def. VI の逆向き、(10) folio 140)。 -/
theorem model_cons_of_pos (a h : M) : prw wt a h ≠ 0 → mcons h → mcons (mand a h) := by
  intro hne hc
  by_contra hz
  apply hne
  rw [mcons, Finset.not_nonempty_iff_eq_empty] at hz
  rw [prw_of_ne (ne_empty_of_cons hc)]
  simp only [mand] at hz
  simp [hz, mu]

/-- **cons_iff_taut**。 -/
theorem model_cons_iff_taut (f g : Form) (env : ℕ → M) (ht : Taut (Form.iffF f g)) :
    mcons (finInterp env f) ↔ mcons (finInterp env g) := by
  have e : finInterp env f = finInterp env g := by
    ext w
    rw [mem_finInterp, mem_finInterp]
    have H := ht (fun n => decide (w ∈ env n))
    simp only [evalB, beq_iff_eq] at H
    rw [H]
  rw [e]

include hw in
/-- **正の重みの模型は第 II 部の公理群 13 本をすべて満たす** (phase12b の wSys と同一)。 -/
theorem wSys : Sys (wOps wt) where
  def_IX_i := model_def_IX_i
  def_X_left_i := model_def_X_left_i hw
  def_X_right_i := model_def_X_right_i hw
  def_XI_i := model_def_XI_i
  ax_range_lo_i := model_ax_range_lo_i hw
  ax_range_hi_i := model_ax_range_hi_i hw
  def_VIII_i := model_def_VIII_i hw
  def_VIII_i_src := model_def_VIII_i_src hw
  ax_iii_taut := fun f env h hc ht => by
    show prw wt ((wOps wt).interp env f) h = 1
    rw [wOps_interp]
    exact model_ax_iii_taut hw f env h hc ht
  cons_true := model_cons_true
  cons_of_pos_src := model_cons_of_pos_src hw
  cons_of_pos := model_cons_of_pos
  cons_iff_taut := fun f g env ht => by
    show mcons ((wOps wt).interp env f) ↔ mcons ((wOps wt).interp env g)
    rw [wOps_interp, wOps_interp]
    exact model_cons_iff_taut f g env ht

end Weighted2

/-! ### 模型 M₁ と反例の系列 -/

/-- 重み (1, 1, 1)。 -/
def wt₁ : W → ℝ := fun _ => 1

theorem wt₁_pos : ∀ w, 0 < wt₁ w := fun _ => by norm_num [wt₁]

/-- 模型 M₁ (重み (1, 1, 1) の wOps)。 -/
noncomputable abbrev M₁ : Ops := wOps wt₁

/-- M₁ は第 II 部の公理群 13 本を満たす。 -/
theorem sys_M₁ : Sys M₁ := wSys wt₁_pos

/-- 反例の系列: a_1 := {0}、a_r := {0, 1} (r ≠ 1)。a_1 は a_2 を含む。 -/
def aC : ℕ → M := fun r => if r = 1 then {0} else {0, 1}

/-- à priori data h := ⊤。 -/
def hC : M := mtrue

theorem cons_hC : M₁.Cons hC := Finset.univ_nonempty

theorem x11_C : @Eq M (M₁.x aC 1 1) {0} := by decide

theorem x22_C : @Eq M (M₁.x aC 2 2) {0} := by decide

/-- _1x_1/h = a_1/h = 1/3。 -/
theorem pB_C : M₁.PrI (M₁.x aC 1 1) hC = 1 / 3 := by
  rw [x11_C]
  show prw wt₁ {0} mtrue = 1 / 3
  rw [prw_of_ne (ne_empty_of_cons model_cons_true)]
  simp [mu, wt₁, mtrue]

/-- y_2/y_1 h = _2x_2/_1x_1 . h = 1。 -/
theorem fac2_C : M₁.PrI (M₁.x aC 2 2) (M₁.iand (M₁.x aC 1 1) hC) = 1 := by
  rw [x11_C, x22_C]
  show prw wt₁ {0} (mand {0} mtrue) = 1
  rw [prw_eq_one_iff wt₁_pos (by decide)]
  decide

/-- **043 は第 II 部の公理群から導けない**: 公理群 13 本を満たす模型 M₁ と整合な h について、
043 の形 (m = n = 1 の場合) が偽 (左辺 1、右辺 1/3)。 -/
theorem nec_29_043_model : Sys M₁ ∧ M₁.Cons hC ∧ ¬ M₁.Cond043 aC hC := by
  refine ⟨sys_M₁, cons_hC, fun H => ?_⟩
  have hc : M₁.Cons (M₁.iand (M₁.x aC 1 1) hC) := by
    rw [x11_C]; exact ⟨0, by decide⟩
  have := H 1 1 le_rfl hc
  rw [fac2_C, pB_C] at this
  norm_num at this

/-- **052 は第 II 部の公理群から導けない**: 同じ模型・同じ系列で a_2/h = 2/3 ≠ 1/3 = a_1/h。 -/
theorem nec_29_052_model : Sys M₁ ∧ M₁.Cons hC ∧ ¬ M₁.EqualChance aC hC := by
  refine ⟨sys_M₁, cons_hC, fun H => ?_⟩
  have := H 2 (by norm_num)
  have e2 : M₁.PrI (aC 2) hC = 2 / 3 := by
    show prw wt₁ (aC 2) mtrue = 2 / 3
    rw [prw_of_ne (ne_empty_of_cons model_cons_true)]
    norm_num [mu, wt₁, mtrue, aC]
  have e1 : M₁.PrI (aC 1) hC = 1 / 3 := by
    show prw wt₁ (aC 1) mtrue = 1 / 3
    rw [prw_of_ne (ne_empty_of_cons model_cons_true)]
    simp [mu, wt₁, mtrue, aC]
  rw [e2, e1] at this
  norm_num at this

/-- **053 は第 II 部の公理群から導けない**: 同じ模型・同じ系列で r = 2、並置 L = a_1 について
a_2/a_1 h = 1 ≠ 2/3 = a_2/h。 -/
theorem nec_29_053_model : Sys M₁ ∧ M₁.Cons hC ∧ ¬ M₁.IndepII aC hC := by
  refine ⟨sys_M₁, cons_hC, fun H => ?_⟩
  have hL : @Eq M (M₁.lits aC [(1, true)]) {0} := by decide
  have hc : M₁.Cons (M₁.iand (M₁.lits aC [(1, true)]) hC) := by
    rw [hL]; exact ⟨0, by decide⟩
  have := H 2 [(1, true)] (by simp) hc
  have e1 : M₁.PrI (aC 2) (M₁.iand (M₁.lits aC [(1, true)]) hC) = 1 := by
    rw [hL]
    show prw wt₁ (aC 2) (mand {0} mtrue) = 1
    rw [prw_eq_one_iff wt₁_pos (by decide)]
    decide
  have e2 : M₁.PrI (aC 2) hC = 2 / 3 := by
    show prw wt₁ (aC 2) mtrue = 2 / 3
    rw [prw_of_ne (ne_empty_of_cons model_cons_true)]
    norm_num [mu, wt₁, mtrue, aC]
  rw [e1, e2] at this
  norm_num at this

/-- **047 の印刷形 y_r/h = p^r は第 II 部の公理群から導けない**: 同じ模型・同じ系列で r = 2 に
ついて y_2/h = 1/3、p^2 = (1/3)^2 = 1/9。 -/
theorem nec_29_047_model :
    Sys M₁ ∧ M₁.Cons hC ∧ M₁.PrI (M₁.y aC 2) hC ≠ M₁.PrI (M₁.x aC 1 1) hC ^ 2 := by
  refine ⟨sys_M₁, cons_hC, ?_⟩
  have hy : @Eq M (M₁.y aC 2) {0} := by decide
  have e : M₁.PrI (M₁.y aC 2) hC = 1 / 3 := by
    rw [hy]
    show prw wt₁ {0} mtrue = 1 / 3
    rw [prw_of_ne (ne_empty_of_cons model_cons_true)]
    simp [mu, wt₁, mtrue]
  rw [e, pB_C]
  norm_num

/-- **系**: 第 II 部の公理群 13 本を満たすすべての場と、すべての整合な h とすべての系列 a で
043 が成り立つ、ということはない。 -/
theorem not_derivable_043 :
    ¬ ∀ S : Ops, Sys S → ∀ (a : ℕ → S.IProp) (h : S.IProp), S.Cons h → S.Cond043 a h :=
  fun H => nec_29_043_model.2.2 (H M₁ sys_M₁ aC hC cons_hC)

end KeynesXXIX_model

/-! ## 監査クエリ (Phase 14a) -/

-- 移植定理 (phase6c・phase10a)
#print axioms KeynesXXIX.itrue_certain
#print axioms KeynesXXIX.true_conj
#print axioms KeynesXXIX.th_13_1_i
#print axioms KeynesXXIX.taut_neg_zero
#print axioms KeynesXXIX.conj_neg_cert_zero
#print axioms KeynesXXIX.th_12_i_short
#print axioms KeynesXXIX.subst_taut
#print axioms KeynesXXIX.th_14_36_i
#print axioms KeynesXXIX.th_12_XIV_symm
-- 補題
#print axioms KeynesXXIX.pr_true_prem
#print axioms KeynesXXIX.pr_self_prem
#print axioms KeynesXXIX.pr_ior_left_certain
-- 記法 (041・044・049・054、定義のみ)
#print axioms KeynesXXIX.x
#print axioms KeynesXXIX.y
#print axioms KeynesXXIX.x_diag
#print axioms KeynesXXIX.yfac
#print axioms KeynesXXIX.lits
#print axioms KeynesXXIX.lits_run
#print axioms KeynesXXIX.run_fst_le
-- 042・045・046 (第 II 部の公理のみ)
#print axioms KeynesXXIX.th_29_042
#print axioms KeynesXXIX.pB_eq_a1
#print axioms KeynesXXIX.th_29_045_a
#print axioms KeynesXXIX.th_29_045
#print axioms KeynesXXIX.th_29_046
-- 047・048 の一般形 (前提は仮定; 第 II 部の公理のみ)
#print axioms KeynesXXIX.th_29_047_of43
#print axioms KeynesXXIX.th_29_047_of
#print axioms KeynesXXIX.th_29_048
#print axioms KeynesXXIX.th_29_048_to_047
#print axioms KeynesXXIX.nec_29_048_single
-- 第 29 章の data 上の印刷形 (外部公理依存)
#print axioms KeynesXXIX.th_29_043
#print axioms KeynesXXIX.th_29_047
#print axioms KeynesXXIX.th_29_048_data
#print axioms KeynesXXIX.th_29_052
#print axioms KeynesXXIX.th_29_053
#print axioms KeynesXXIX.th_29_047_ii
-- 053 と Def. XIII
#print axioms KeynesXXIX.th_29_053_is_XIV
#print axioms KeynesXXIX.th_29_053_XIII
#print axioms KeynesXXIX.bernoulliIndependent_of_ii
#print axioms KeynesXXIX.equalChanceP_of_i
-- 050
#print axioms KeynesXXIX.yfac_one
#print axioms KeynesXXIX.yfac_ge_first
#print axioms KeynesXXIX.th_29_050
#print axioms KeynesXXIX.th_29_050_dual
#print axioms KeynesXXIX.th_29_050_not_043
-- 051
#print axioms KeynesXXIX.th_29_051
-- 外部公理の相対無矛盾性
#print axioms KeynesXXIX.rel_cons_trivial
-- 有限模型: 043・052・053 は第 II 部の公理群から導けない
#print axioms KeynesXXIX_model.wSys
#print axioms KeynesXXIX_model.sys_M₁
#print axioms KeynesXXIX_model.x11_C
#print axioms KeynesXXIX_model.x22_C
#print axioms KeynesXXIX_model.pB_C
#print axioms KeynesXXIX_model.fac2_C
#print axioms KeynesXXIX_model.nec_29_043_model
#print axioms KeynesXXIX_model.nec_29_047_model
#print axioms KeynesXXIX_model.nec_29_052_model
#print axioms KeynesXXIX_model.nec_29_053_model
#print axioms KeynesXXIX_model.not_derivable_043
