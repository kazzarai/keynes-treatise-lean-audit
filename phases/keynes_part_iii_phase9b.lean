/-
# Keynes (1921) *A Treatise on Probability* Part III — Lean 4 Phase 9b
#
# 第 XIX 章「類推による議論の本性」(1921 年 Macmillan 初版 folio 222–232)
# §4 の不等式連鎖 (本章で唯一の "This proves") と、表示式として印刷された記法。
#
# ## 基準
#   1921 年初版の頁画像のみ。台帳 (第III部帰納/台帳_ch19_類推.md) の行番号 #n を
#   定理名 th_19_<n> に用いる (原著の第 XIX 章には式番号がない)。
#
# ## キャリア
#   第III部は内包キャリア (IProp, PrI; phase6c と同一の公理群) に載せる。
#   `Prop → Prop → ℝ` 型の確率関係は用いない (CLAUDE.md 不変条件 3)。
#   第 XIX 章の一般化 g(φ, f) は「φ(x) が真であるすべての x について f(x) が真」
#   (folio 222) なので、内包キャリアに全称量化子 iall を一本追加し、その上で
#   phase6c の Ax.(iii) (トートロジー的同値の確実性) を量化子の内側へ拡張する
#   (ax_iii_all) とともに、∀ が連言と可換であること (ax_all_iand) を置く。
#   どちらも純粋に論理的な原理であり、確率の値に関する新しい仮定ではない。
#
# ## 収録
#   A. 記法 (印刷された表示式を定義として写す)
#      folio 223     A_{a₁…aₙ}(φ)                    (台帳 #7, 脚注 #8)
#      folio 224     Ā_{a₁…aₙ}(φ′)                   (#9, 脚注 #10)
#      folio 222     g(φ, f)                          (#2)
#      folio 227     g(φ,f) / A(φφ₁f)                 (#26)
#      folio 228     g(φ,f) / A(φφ₁f) Ā(φ′)            (#29)
#      folio 229     g(φ,f) / A(φφ₁f) Ā(φ′) Π{A(ψ_k)}  (#32; folio 231 #42 と同形)
#      folio 229     A_{b}(_bφ _bφ₁ _bf) Ā_{b}(_bφ′) Π{A_{b}(_bψ_k)}   (#34)
#      folio 230     一般式 g(φ,f) / Π_{a,b…}{…} Π{…}  (#35; 誤植あり、下記)
#      folio 230     A_{a′}(_{a′}φ _{a′}f̄)            (#38)
#   B. §4 の連鎖 (folio 225)
#      #16  g(φ₁,f)/h = g(φ₁φ₂,f).g(φ₁φ̄₂,f)/h ≤ g(φ,f)/h       印刷どおり証明
#      #17  g(φ,f)/h = g(φ,f₁f₂)/h = g(φf₁,f₂)/h . g(φ,f₁)/h ≤ g(φ,f₁)/h
#           第 2 行は印刷どおりでは導出不能 (反例モデル)。第 1 因子の条件に
#           g(φ,f₁) を補った形 g(φf₁,f₂)/g(φ,f₁)h . g(φ,f₁)/h で証明。
#      #18  g(φ,f₁)/h ≥ g(φ,f)/h ≥ g(φ₁,f)/h                   証明
#   C. 形式化の境界の記録 (§5–§11): 定理にしない主張と、要る原理をコメントで列挙。
#
# ## 印刷上の注記
#   folio 230 の一般式は負の類推の項を `Ā_{a₁…aₙ}(_aφ¹)` (上付き 1) と印刷している。
#   folio 227–229 の対応する項はすべて `φ′` (プライム) なので `_aφ′` の誤植とみる。
#   本ファイルの定義は φ′ の読みで書き、印刷形はコメントに残す (下記 §9)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_iii_phase9b.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KeynesIII

/-! ## 内包的キャリアと結合子 (phase6c と同一) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-! ## Keynes 操作公理群 (内包版、phase6c と同一) -/

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- **Def.VIII (等値の定義)** 双条件読み (phase6c と同一)。 -/
axiom def_VIII_i (a b h : IProp) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

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

/-! ## 第III部のための拡張: 事例の領域と全称量化子 -/

/-- 事例 (instances) の領域。第 XIX 章の a₁ … aₙ, b₁ … b_m はこの型の要素。 -/
axiom Inst : Type

/-- 命題関数 (propositional function) φ(x)。 -/
abbrev PFun : Type := Inst → IProp

/-- 内包的全称量化子: iall P は「すべての x について P(x)」。 -/
axiom iall : (Inst → IProp) → IProp

/-- **Ax.(iii) の量化子内側への拡張**: 行列がトートロジー的に同値な二つの
全称命題は、任意の証拠の下で確実に同値。phase6c の ax_iii_taut と同じ原理を、
各事例 x ごとの代入 env x に対して述べたもの。 -/
axiom ax_iii_all (F G : Form) (env : Inst → ℕ → IProp) (h : IProp) :
    Taut (Form.iffF F G) →
    PrI (iiff (iall fun x => interp (env x) F) (iall fun x => interp (env x) G)) h = 1

/-- **∀ と連言の可換性**: ∀x (P x . Q x) と (∀x P x) . (∀x Q x) は確実に同値。 -/
axiom ax_all_iand (P Q : Inst → IProp) (h : IProp) :
    PrI (iiff (iall fun x => iand (P x) (Q x)) (iand (iall P) (iall Q))) h = 1

/-! ## 移植定理 (phase6c) -/

/-- **Th.(12) 内包版** 確実な双条件の下で確率は等しい。 -/
theorem th_12_i (a b h : IProp) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h := by
  obtain ⟨hba, hab⟩ := (def_VIII_i a b h).mp hcert
  have hl := def_X_left_i a b h
  have hr := def_X_right_i a b h
  rw [hab, one_mul] at hl
  rw [hba, one_mul] at hr
  linarith

/-- 量化子の内側での認証代入: 行列がトートロジー的に同値なら確率は等しい。 -/
theorem subst_all (F G : Form) (env : Inst → ℕ → IProp) (h : IProp)
    (ht : Taut (Form.iffF F G)) :
    PrI (iall fun x => interp (env x) F) h = PrI (iall fun x => interp (env x) G) h :=
  th_12_i _ _ h (ax_iii_all F G env h ht)

/-- ∀ の連言分配 (確率等式の形)。 -/
theorem pr_all_iand (P Q : Inst → IProp) (h : IProp) :
    PrI (iall fun x => iand (P x) (Q x)) h = PrI (iand (iall P) (iall Q)) h :=
  th_12_i _ _ h (ax_all_iand P Q h)

/-- 連言の確率は左の連言肢の確率を超えない: Def.X (右形) と範囲原理から。
「a が b を含意するならば a/h ≤ b/h」の、本章で要る形。 -/
theorem pr_conj_le_left_i (p q h : IProp) : PrI (iand p q) h ≤ PrI p h := by
  have hx := def_X_right_i p q h
  have h1 := ax_range_hi_i q (iand p h)
  have h0 := ax_range_lo_i p h
  rw [hx]
  nlinarith

/-- 連言の確率は右の連言肢の確率を超えない: Def.X (左形) と範囲原理から。 -/
theorem pr_conj_le_right_i (p q h : IProp) : PrI (iand p q) h ≤ PrI q h := by
  have hx := def_X_left_i p q h
  have h1 := ax_range_hi_i p (iand q h)
  have h0 := ax_range_lo_i q h
  rw [hx]
  nlinarith

/-! ## A. 記法 — 命題関数の結合 -/

/-- φψ : 命題関数の連言 (folio 225 の φ₁φ₂, f₁f₂, φf₁ など)。 -/
noncomputable def pand (φ ψ : PFun) : PFun := fun x => iand (φ x) (ψ x)

/-- φ̄ : 命題関数の否定 (folio 225 の φ̄₂、folio 230 の f̄)。 -/
noncomputable def pnot (φ : PFun) : PFun := fun x => inot (φ x)

infixr:35 " ∧ₚ " => pand
prefix:max "¬ₚ" => pnot

/-- **g(φ, f)** (folio 222, 台帳 #2): 「φ(x) が真であるすべての x の値について
f(x) が真」。本章の一般化 (generalisation)。 -/
noncomputable def g (φ f : PFun) : IProp := iall fun x => ior (inot (φ x)) (f x)

/-- **A_{a₁…aₙ}(φ)** (folio 223, 台帳 #7)。脚注 (#8) のとおり
`A_{a₁…aₙ}(φ) ≡ φ(a₁) . φ(a₂) … φ(aₙ)` と定める (事例の有限連言)。
空列は確実命題 itrue とする (原著は n ≥ 1 のみを扱う)。 -/
noncomputable def A : List Inst → PFun → IProp
  | [],        _ => itrue
  | [x],       φ => φ x
  | x :: rest, φ => iand (φ x) (A rest φ)

/-- 有限選言 Σ_{x=a_r}^{x=a_s} φ(x) (folio 224 脚注)。 -/
noncomputable def Sig : List Inst → PFun → IProp
  | [],        _ => inot itrue
  | [x],       φ => φ x
  | x :: rest, φ => ior (φ x) (Sig rest φ)

/-- **Ā_{a₁…aₙ}(φ′)** (folio 224, 台帳 #9)。脚注 (#10) のとおり
`Ā(φ′) ≡ Σ_{x=a_r}^{x=a_s} φ′(x) . Σ_{x=a_r′}^{x=a_s′} \overline{φ′(x)}`:
ある範囲 a_r…a_s のどれかで φ′ が真、かつ別の範囲 a_r′…a_s′ のどれかで φ′ が偽。
本文 (§2) の読み「少なくとも一つの事例で真、少なくとも一つで偽」は
両範囲を全事例列にとった特殊な場合。 -/
noncomputable def Abar (rs rs' : List Inst) (φ' : PFun) : IProp :=
  iand (Sig rs φ') (Sig rs' (¬ₚ φ'))

/-- 補助 (rfl)。脚注 (folio 223) の形が定義から直ちに出ること: 事例 3 個の場合。 -/
theorem A_three (a₁ a₂ a₃ : Inst) (φ : PFun) :
    A [a₁, a₂, a₃] φ = iand (φ a₁) (iand (φ a₂) (φ a₃)) := rfl

/-- 補助 (rfl)。脚注 (folio 224) の形: 範囲 a_r…a_s = [a₁, a₂], a_r′…a_s′ = [a₂, a₃] の場合。 -/
theorem Abar_example (a₁ a₂ a₃ : Inst) (φ' : PFun) :
    Abar [a₁, a₂] [a₂, a₃] φ'
      = iand (ior (φ' a₁) (φ' a₂)) (ior (inot (φ' a₂)) (inot (φ' a₃))) := rfl

/-! ## B. §4 の不等式連鎖 (folio 225) -/

/-- 変数 0 := φ₁, 1 := φ₂, 2 := f。 -/
noncomputable def env3 (φ₁ φ₂ f : PFun) (x : Inst) : ℕ → IProp :=
  fun n => match n with
    | 0 => φ₁ x
    | 1 => φ₂ x
    | _ => f x

/-- **folio 225 第 1 ブロック (台帳 #16) 印刷形**:
`g(φ₁, f)/h = g(φ₁φ₂, f) . g(φ₁φ̄₂, f)/h ≤ g(φ, f)/h`  (φ ≡ φ₁φ₂)。
等式: 行列 (φ₁ ⊃ f) と (φ₁φ₂ ⊃ f).(φ₁φ̄₂ ⊃ f) のトートロジー的同値を
量化子の内側で代入し (ax_iii_all)、∀ を連言に分配する (ax_all_iand)。
不等式: 連言 ≤ 連言肢 (Def.X + 範囲原理)。
前提について: 印刷は #13 g(φ₁,φ₂)/h ≠ 1、#14 g(f₁,f₂)/h ≠ 1、#15 φ ≡ φ₁φ₂ を
前提に置くが、本定理は #13, #14 を仮定に置かず落としている (前提なしで成立する
ので印刷より強い)。#15 は φ を φ₁ ∧ₚ φ₂ と書くことで定義的に展開した。 -/
theorem th_19_16_src (φ₁ φ₂ f : PFun) (h : IProp) :
    PrI (g φ₁ f) h = PrI (iand (g (φ₁ ∧ₚ φ₂) f) (g (φ₁ ∧ₚ ¬ₚ φ₂) f)) h ∧
    PrI (iand (g (φ₁ ∧ₚ φ₂) f) (g (φ₁ ∧ₚ ¬ₚ φ₂) f)) h ≤ PrI (g (φ₁ ∧ₚ φ₂) f) h := by
  -- 行列の同値: (¬φ₁ ∨ f) ↔ ((¬(φ₁∧φ₂) ∨ f) ∧ (¬(φ₁∧¬φ₂) ∨ f))
  have e1 : PrI (g φ₁ f) h
      = PrI (iall fun x => iand (ior (inot (iand (φ₁ x) (φ₂ x))) (f x))
                                 (ior (inot (iand (φ₁ x) (inot (φ₂ x)))) (f x))) h :=
    subst_all
      (Form.disj (Form.neg (Form.var 0)) (Form.var 2))
      (Form.conj (Form.disj (Form.neg (Form.conj (Form.var 0) (Form.var 1))) (Form.var 2))
                 (Form.disj (Form.neg (Form.conj (Form.var 0) (Form.neg (Form.var 1)))) (Form.var 2)))
      (env3 φ₁ φ₂ f) h
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  have e2 := pr_all_iand
      (fun x => ior (inot (iand (φ₁ x) (φ₂ x))) (f x))
      (fun x => ior (inot (iand (φ₁ x) (inot (φ₂ x)))) (f x)) h
  refine ⟨?_, ?_⟩
  · rw [e1]; exact e2
  · exact pr_conj_le_left_i _ _ h

/-- 変数 0 := φ, 1 := f₁, 2 := f₂。 -/
noncomputable def env3' (φ f₁ f₂ : PFun) (x : Inst) : ℕ → IProp :=
  fun n => match n with
    | 0 => φ x
    | 1 => f₁ x
    | _ => f₂ x

/-- 補題: g(φ, f₁f₂) ≡ g(φf₁, f₂) . g(φ, f₁) の確率等式 (§5 冒頭で Keynes が
「積として表せる」と述べる根拠)。 -/
theorem pr_g_concl_split (φ f₁ f₂ : PFun) (h : IProp) :
    PrI (g φ (f₁ ∧ₚ f₂)) h = PrI (iand (g (φ ∧ₚ f₁) f₂) (g φ f₁)) h := by
  have e1 : PrI (g φ (f₁ ∧ₚ f₂)) h
      = PrI (iall fun x => iand (ior (inot (iand (φ x) (f₁ x))) (f₂ x))
                                 (ior (inot (φ x)) (f₁ x))) h :=
    subst_all
      (Form.disj (Form.neg (Form.var 0)) (Form.conj (Form.var 1) (Form.var 2)))
      (Form.conj (Form.disj (Form.neg (Form.conj (Form.var 0) (Form.var 1))) (Form.var 2))
                 (Form.disj (Form.neg (Form.var 0)) (Form.var 1)))
      (env3' φ f₁ f₂) h
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  rw [e1]
  exact pr_all_iand
    (fun x => ior (inot (iand (φ x) (f₁ x))) (f₂ x))
    (fun x => ior (inot (φ x)) (f₁ x)) h

/-- **folio 225 第 2 ブロック (台帳 #17)、第 1 因子の条件を補った形**:
`g(φ, f)/h = g(φ, f₁f₂)/h = g(φf₁, f₂)/g(φ,f₁)h . g(φ, f₁)/h ≤ g(φ, f₁)/h`  (f ≡ f₁f₂)。
第 1 の等式は f ≡ f₁f₂ (定義)。第 2 の等式は上の補題と乗法定理 Def.X (左形)。
不等式は第 1 因子 ≤ 1 と第 2 因子 ≥ 0 (範囲原理)。 -/
theorem th_19_17 (φ f₁ f₂ : PFun) (h : IProp) :
    PrI (g φ (f₁ ∧ₚ f₂)) h
        = PrI (g (φ ∧ₚ f₁) f₂) (iand (g φ f₁) h) * PrI (g φ f₁) h ∧
    PrI (g (φ ∧ₚ f₁) f₂) (iand (g φ f₁) h) * PrI (g φ f₁) h ≤ PrI (g φ f₁) h := by
  have e := pr_g_concl_split φ f₁ f₂ h
  have hx := def_X_left_i (g (φ ∧ₚ f₁) f₂) (g φ f₁) h
  have h1 := ax_range_hi_i (g (φ ∧ₚ f₁) f₂) (iand (g φ f₁) h)
  have h0 := ax_range_lo_i (g φ f₁) h
  refine ⟨by rw [e, hx], ?_⟩
  nlinarith

/-- **folio 225 第 2 ブロック第 2 行、印刷どおりの形** `g(φ,f)/h = g(φf₁,f₂)/h . g(φ,f₁)/h`
が成り立つための必要十分条件: g(φ,f₁)/h = 0 であるか、または g(φf₁,f₂) が
h に相対して g(φ,f₁) から無関連 (独立) であること。すなわち印刷形は、省かれた
条件 g(φ,f₁) が第 1 因子に影響しない場合にしか成り立たない。 -/
theorem th_19_17_src_iff (φ f₁ f₂ : PFun) (h : IProp) :
    PrI (g φ (f₁ ∧ₚ f₂)) h = PrI (g (φ ∧ₚ f₁) f₂) h * PrI (g φ f₁) h ↔
    (PrI (g φ f₁) h = 0 ∨
     PrI (g (φ ∧ₚ f₁) f₂) (iand (g φ f₁) h) = PrI (g (φ ∧ₚ f₁) f₂) h) := by
  have e := (th_19_17 φ f₁ f₂ h).1
  rw [e]
  constructor
  · intro heq
    by_cases hz : PrI (g φ f₁) h = 0
    · exact Or.inl hz
    · right
      exact mul_right_cancel₀ hz heq
  · rintro (hz | hind)
    · rw [hz]; ring
    · rw [hind]

/-- **folio 225 結論行 (台帳 #18)**: `g(φ, f₁)/h ≥ g(φ, f)/h ≥ g(φ₁, f)/h`
(φ ≡ φ₁φ₂, f ≡ f₁f₂)。#16 と #17 の連結。"This proves the statement made above."
前提について: 印刷の前提 #13 g(φ₁,φ₂)/h ≠ 1、#14 g(f₁,f₂)/h ≠ 1 は仮定に置かず
落としている (前提なしで成立する)。#15 φ ≡ φ₁φ₂, f ≡ f₁f₂ は φ₁ ∧ₚ φ₂, f₁ ∧ₚ f₂ と
書くことで定義的に展開した。#13, #14 を加えても ≥ は狭義にならない
(StrictnessCountermodel)。 -/
theorem th_19_18_src (φ₁ φ₂ f₁ f₂ : PFun) (h : IProp) :
    PrI (g (φ₁ ∧ₚ φ₂) f₁) h ≥ PrI (g (φ₁ ∧ₚ φ₂) (f₁ ∧ₚ f₂)) h ∧
    PrI (g (φ₁ ∧ₚ φ₂) (f₁ ∧ₚ f₂)) h ≥ PrI (g φ₁ (f₁ ∧ₚ f₂)) h := by
  obtain ⟨e17, le17⟩ := th_19_17 (φ₁ ∧ₚ φ₂) f₁ f₂ h
  obtain ⟨e16, le16⟩ := th_19_16_src φ₁ φ₂ (f₁ ∧ₚ f₂) h
  constructor
  · rw [e17]; exact le17
  · rw [e16]; exact le16

/-! ## B (続) — 印刷形 #17 第 2 行の反例モデル

`g(φ,f)/h = g(φf₁,f₂)/h . g(φ,f₁)/h` (条件 g(φ,f₁) を落とした印刷形) は公理から
導けない。th_19_17_src_iff により、印刷形は「g(φ,f₁)/h = 0 または無関連」と
同値なので、どちらも成り立たない確率分布が一つあれば足りる。

モデル: 事例 3 個 a, b, c。φ ≡ φ₁φ₂, f ≡ f₁f₂ (印刷の前提 #15 を定義として置く)。
  a, b : φ₁, φ₂ とも確実に真 (h に含まれる)。f₁, f₂ は各事例で独立な等確率の二値。
  c    : φ₁ 確実に真・φ₂ 確実に偽 (ゆえに φ(c) 偽)。f₁(c), f₂(c) は確実に偽。
世界は (f₁(a), f₂(a), f₁(b), f₂(b)) の 16 組、各質量 1。
  g(φ, f₁)   = f₁(a) . f₁(b)                       質量 4
  g(φf₁, f₂) = (f₁(a) ⊃ f₂(a)) . (f₁(b) ⊃ f₂(b))   質量 3 × 3 = 9
  g(φ, f₁f₂) = f₁(a) f₂(a) f₁(b) f₂(b)              質量 1
  g(φf₁,f₂) . g(φ,f₁)                               質量 1 (= g(φ, f₁f₂))
事例 c では φ(c) が偽なので、g(φ, ·) の各項の c の因子 (¬φ(c) ∨ ·) は真であり、
上の質量は a, b だけで数えた値と一致する (instance_c_inert)。一方、印刷の前提
  #13  g(φ₁, φ₂)/h ≠ 1 : c で φ₁ 真・φ₂ 偽なので g(φ₁,φ₂) は全世界で偽、質量 0
  #14  g(f₁, f₂)/h ≠ 1 : (f₁ ⊃ f₂) は a, b で各 3/4、c で真、質量 9
はともに成立する (hypotheses_of_17_hold; 7i の hypotheses_of_35_hold と同じ型)。
質量は世界の列挙で機械的に数える (masses_by_enumeration)。条件付き確率は質量比
(Def.X の標準モデル)。7i の反例モデルと同じ流儀。 -/

namespace Erratum19_17Countermodel

/-- 世界: (f₁(a), f₂(a), f₁(b), f₂(b))。 -/
abbrev World := Bool × Bool × Bool × Bool

/-- 事例 a, b, c はそれぞれ 0, 1, 2。 -/
abbrev I := Fin 3

/-- 16 世界の列挙。 -/
def worlds : List World := do
  let p ← [false, true]
  let q ← [false, true]
  let r ← [false, true]
  let s ← [false, true]
  pure (p, q, r, s)

/-- 項を満たす世界の数 (各世界の質量 1)。 -/
def mass (p : World → Bool) : ℕ := (worlds.filter p).length

/-- φ₁: すべての事例で確実に真。 -/
def φ₁B : I → World → Bool := fun _ _ => true
/-- φ₂: a, b で確実に真、c で確実に偽。 -/
def φ₂B : I → World → Bool := fun i _ => decide (i.val < 2)
/-- f₁: a, b では世界の第 1, 第 3 成分、c では確実に偽。 -/
def f₁B : I → World → Bool := fun i w =>
  match i.val with
  | 0 => w.1
  | 1 => w.2.2.1
  | _ => false
/-- f₂: a, b では世界の第 2, 第 4 成分、c では確実に偽。 -/
def f₂B : I → World → Bool := fun i w =>
  match i.val with
  | 0 => w.2.1
  | 1 => w.2.2.2
  | _ => false

/-- 命題関数の連言 (Bool 版の pand)。 -/
def andB (φ ψ : I → World → Bool) : I → World → Bool := fun i w => φ i w && ψ i w

/-- g(φ, f) の Bool 版: 事例列 is のすべての x で (¬φ(x) ∨ f(x))。 -/
def gB (is : List I) (φ f : I → World → Bool) (w : World) : Bool :=
  is.all fun i => (!(φ i w)) || f i w

/-- φ ≡ φ₁φ₂ (前提 #15)。 -/
def φB : I → World → Bool := andB φ₁B φ₂B

def total : ℚ := 16
def mF1   : ℚ := 4     -- g(φ, f₁)
def mImp  : ℚ := 9     -- g(φf₁, f₂)
def mBoth : ℚ := 1     -- g(φ, f₁f₂) = g(φf₁,f₂) . g(φ,f₁)
def mIndφ : ℚ := 0     -- g(φ₁, φ₂)  (前提 #13 の項)
def mIndf : ℚ := 9     -- g(f₁, f₂)  (前提 #14 の項)

def P_g_f    : ℚ := mBoth / total    -- g(φ, f)/h          = 1/16
def P_g_f1   : ℚ := mF1 / total      -- g(φ, f₁)/h         = 1/4
def P_imp    : ℚ := mImp / total     -- g(φf₁, f₂)/h       = 9/16
def P_imp_c  : ℚ := mBoth / mF1      -- g(φf₁, f₂)/g(φ,f₁)h = 1/4
def P_ind_φ  : ℚ := mIndφ / total    -- g(φ₁, φ₂)/h        = 0
def P_ind_f  : ℚ := mIndf / total    -- g(f₁, f₂)/h        = 9/16

/-- 世界の数え上げ: f₁(a), f₂(a), f₁(b), f₂(b) の 16 組のうち、各項を満たす数。
含意 f₁ ⊃ f₂ は 4 組中 3 組で真。 -/
theorem masses_consistent :
    (2 : ℚ) ^ 4 = total ∧ (2 : ℚ) ^ 2 = mF1 ∧ (3 : ℚ) ^ 2 = mImp ∧ (1 : ℚ) = mBoth := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [total, mF1, mImp, mBoth]

/-- 質量を 3 事例 a, b, c の上で列挙して確認: g(φ,f₁), g(φf₁,f₂), g(φ,f₁f₂),
g(φf₁,f₂).g(φ,f₁), および前提の項 g(φ₁,φ₂), g(f₁,f₂)。 -/
theorem masses_by_enumeration :
    worlds.length = 16 ∧
    mass (gB [0, 1, 2] φB f₁B) = 4 ∧
    mass (gB [0, 1, 2] (andB φB f₁B) f₂B) = 9 ∧
    mass (gB [0, 1, 2] φB (andB f₁B f₂B)) = 1 ∧
    mass (fun w => gB [0, 1, 2] (andB φB f₁B) f₂B w && gB [0, 1, 2] φB f₁B w) = 1 ∧
    mass (gB [0, 1, 2] φ₁B φ₂B) = 0 ∧
    mass (gB [0, 1, 2] f₁B f₂B) = 9 := by
  decide

/-- 事例 c は g(φ, ·) に対して不活性: φ(c) が偽なので、3 事例で数えた質量は
a, b の 2 事例で数えた質量と一致する。 -/
theorem instance_c_inert :
    mass (gB [0, 1, 2] φB f₁B) = mass (gB [0, 1] φB f₁B) ∧
    mass (gB [0, 1, 2] (andB φB f₁B) f₂B) = mass (gB [0, 1] (andB φB f₁B) f₂B) ∧
    mass (gB [0, 1, 2] φB (andB f₁B f₂B)) = mass (gB [0, 1] φB (andB f₁B f₂B)) := by
  decide

/-- 列挙した質量と有理数の定義の一致。 -/
theorem masses_match_enumeration :
    (mass (gB [0, 1, 2] φB f₁B) : ℚ) = mF1 ∧
    (mass (gB [0, 1, 2] (andB φB f₁B) f₂B) : ℚ) = mImp ∧
    (mass (gB [0, 1, 2] φB (andB f₁B f₂B)) : ℚ) = mBoth ∧
    (mass (gB [0, 1, 2] φ₁B φ₂B) : ℚ) = mIndφ ∧
    (mass (gB [0, 1, 2] f₁B f₂B) : ℚ) = mIndf := by
  obtain ⟨_, h1, h2, h3, _, h5, h6⟩ := masses_by_enumeration
  rw [h1, h2, h3, h5, h6]
  norm_num [mF1, mImp, mBoth, mIndφ, mIndf]

/-- **印刷の前提 #13, #14 は成立**: g(φ₁,φ₂)/h = 0 ≠ 1、g(f₁,f₂)/h = 9/16 ≠ 1。
(#15 φ ≡ φ₁φ₂, f ≡ f₁f₂ は定義 φB, andB f₁B f₂B として置かれている。) -/
theorem hypotheses_of_17_hold : P_ind_φ ≠ 1 ∧ P_ind_f ≠ 1 := by
  constructor <;> norm_num [P_ind_φ, P_ind_f, mIndφ, mIndf, total]

/-- Def.X の該当インスタンス: g(φf₁,f₂)/g(φ,f₁)h · g(φ,f₁)/h = (g(φf₁,f₂).g(φ,f₁))/h。
条件を補った形 (th_19_17) はモデルで成立。 -/
theorem corrected_form_holds : P_g_f = P_imp_c * P_g_f1 := by
  norm_num [P_g_f, P_imp_c, P_g_f1, total, mF1, mBoth]

/-- **印刷形は破れる**: 1/16 ≠ 9/16 · 1/4 = 9/64。 -/
theorem printed_form_fails : ¬ (P_g_f = P_imp * P_g_f1) := by
  norm_num [P_g_f, P_imp, P_g_f1, total, mF1, mImp, mBoth]

/-- 不等式 ≤ g(φ,f₁)/h 自体はモデルで成立 (結論行 #18 には影響しない)。 -/
theorem inequality_holds : P_g_f ≤ P_g_f1 := by
  norm_num [P_g_f, P_g_f1, total, mF1, mBoth]

end Erratum19_17Countermodel

/-! ## B (続) — 独立性の前提 (#13–15) は狭義化を与えない

folio 224 末尾の主張 (#12) は「φ が増せば確率は**増し** (increases)、f が増せば
**減る** (diminish)」と狭義に読める語で述べられ、folio 225 の φ₁, φ₂ および
f₁, f₂ の独立性 (g(φ₁,φ₂)/h ≠ 1, g(f₁,f₂)/h ≠ 1) がその条件として置かれている。
しかし印刷の連鎖 (#18) は ≥ であり、独立性の前提を加えても狭義にはならない:

モデル: 事例 1 個。2 世界、各質量 1。
  w₁ : φ₁ 真, φ₂ 偽, f₁ 真, f₂ 真
  w₂ : φ₁ 偽, φ₂ 偽, f₁ 真, f₂ 偽
  g(φ₁,φ₂)/h = P(¬φ₁ ∨ φ₂) = {w₂} = 1/2 ≠ 1,  g(f₁,f₂)/h = P(¬f₁ ∨ f₂) = {w₁} = 1/2 ≠ 1,
  g(φ,f₁)/h = g(φ,f)/h = g(φ₁,f)/h = 1  (φ = φ₁φ₂ はどの世界でも偽; ¬φ₁ ∨ f₁f₂ は両世界で真)。
質量は Erratum19_17Countermodel と同じ型で、世界を列挙して decide で数える。 -/

namespace StrictnessCountermodel

/-- 世界: w₁ := true, w₂ := false。 -/
abbrev World := Bool
/-- 事例は 1 個 (0)。 -/
abbrev I := Fin 1

/-- 2 世界の列挙。 -/
def worlds : List World := [true, false]

/-- 項を満たす世界の数 (各世界の質量 1)。 -/
def mass (p : World → Bool) : ℕ := (worlds.filter p).length

/-- φ₁: w₁ で真, w₂ で偽。 -/
def φ₁B : I → World → Bool := fun _ w => w
/-- φ₂: 両世界で偽。 -/
def φ₂B : I → World → Bool := fun _ _ => false
/-- f₁: 両世界で真。 -/
def f₁B : I → World → Bool := fun _ _ => true
/-- f₂: w₁ で真, w₂ で偽。 -/
def f₂B : I → World → Bool := fun _ w => w

/-- 命題関数の連言 (Bool 版の pand)。 -/
def andB (φ ψ : I → World → Bool) : I → World → Bool := fun i w => φ i w && ψ i w

/-- g(φ, f) の Bool 版: 事例列 is のすべての x で (¬φ(x) ∨ f(x))。 -/
def gB (is : List I) (φ f : I → World → Bool) (w : World) : Bool :=
  is.all fun i => (!(φ i w)) || f i w

/-- φ ≡ φ₁φ₂, f ≡ f₁f₂ (前提 #15)。 -/
def φB : I → World → Bool := andB φ₁B φ₂B
def fB : I → World → Bool := andB f₁B f₂B

def total : ℚ := 2
def mIndφ : ℚ := 1     -- g(φ₁, φ₂)  (前提 #13 の項)
def mIndf : ℚ := 1     -- g(f₁, f₂)  (前提 #14 の項)
def mF1   : ℚ := 2     -- g(φ, f₁)
def mF    : ℚ := 2     -- g(φ, f)
def m1F   : ℚ := 2     -- g(φ₁, f)

def P_ind_phi : ℚ := mIndφ / total   -- g(φ₁, φ₂)/h = 1/2
def P_ind_f   : ℚ := mIndf / total   -- g(f₁, f₂)/h = 1/2
def P_g_f1    : ℚ := mF1 / total     -- g(φ, f₁)/h  = 1
def P_g_f     : ℚ := mF / total      -- g(φ, f)/h   = 1
def P_g1_f    : ℚ := m1F / total     -- g(φ₁, f)/h  = 1

/-- 質量を 1 事例・2 世界の上で列挙して確認: 前提の項 g(φ₁,φ₂), g(f₁,f₂) と
連鎖の三項 g(φ,f₁), g(φ,f), g(φ₁,f)。 -/
theorem masses_by_enumeration :
    worlds.length = 2 ∧
    mass (gB [0] φ₁B φ₂B) = 1 ∧
    mass (gB [0] f₁B f₂B) = 1 ∧
    mass (gB [0] φB f₁B) = 2 ∧
    mass (gB [0] φB fB) = 2 ∧
    mass (gB [0] φ₁B fB) = 2 := by
  decide

/-- 列挙した質量と有理数の定義の一致。 -/
theorem masses_match_enumeration :
    (mass (gB [0] φ₁B φ₂B) : ℚ) = mIndφ ∧
    (mass (gB [0] f₁B f₂B) : ℚ) = mIndf ∧
    (mass (gB [0] φB f₁B) : ℚ) = mF1 ∧
    (mass (gB [0] φB fB) : ℚ) = mF ∧
    (mass (gB [0] φ₁B fB) : ℚ) = m1F := by
  obtain ⟨_, h1, h2, h3, h4, h5⟩ := masses_by_enumeration
  rw [h1, h2, h3, h4, h5]
  norm_num [mIndφ, mIndf, mF1, mF, m1F]

/-- 独立性の前提 (#13, #14) は成立: 1/2 ≠ 1。 -/
theorem independence_premises_hold : P_ind_phi ≠ 1 ∧ P_ind_f ≠ 1 := by
  constructor <;> norm_num [P_ind_phi, P_ind_f, mIndφ, mIndf, total]

/-- 連鎖は等号で成立し、狭義不等式はどちらも破れる。 -/
theorem chain_is_equality :
    P_g_f1 = P_g_f ∧ P_g_f = P_g1_f ∧ ¬ (P_g_f1 > P_g_f) ∧ ¬ (P_g_f > P_g1_f) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [P_g_f1, P_g_f, P_g1_f, mF1, mF, m1F, total]

end StrictnessCountermodel

/-! ## B (続) — 量化子原理の必要性: ax_all_iand / ax_iii_all を破る読みでの th_19_16_src の破れ

th_19_16_src の等式 g(φ₁,f)/h = g(φ₁φ₂,f).g(φ₁φ̄₂,f)/h は第 II 部の公理だけでは
出ず、量化子原理 ax_iii_all (行列の同値の量化子内側への代入) と ax_all_iand
(∀ の連言分配) を要する。証明からどちらを落としても赤になることは確認した上で、
ここではそれぞれを破る iall の読み替えの下で等式が破れることを定理として残す。
どちらも 1 世界の Bool 評価 (確率は 0/1、PrI p h := [h ⊃ p]) で、iand, ior, inot, iiff
は標準の真理値計算である。この評価が Def.IX, Def.X, 範囲原理, Def.VIII を満たすのは
h が整合な場合に限る: 不整合な h では [h ⊃ p] = 1 がすべての p で成り立ち、Def.IX
(PrI (p¬q) h + PrI (pq) h = PrI p h) が 1 + 1 = 1 で破れる。したがって以下は
**公理群全体のモデルではなく**、量化子原理の一方を破る読みの下で th_19_16_src の
等式の両辺の値が食い違うことを示す**数値例**である。必要性そのものは、証明から
各公理を落として赤になることで確認した (上記)。
変数は本文の env3 と同じ 0 := φ₁, 1 := φ₂, 2 := f。

(i) 存在読み (ax_all_iand が破れる): iall P を「ある事例で P」と読む。行列の同値は
    事例ごとの代入で保たれるので ax_iii_all は成立する (exists_respects_taut)。
    事例 a, b で φ₁ 真; φ₂ は a で真・b で偽; f は両方で偽。
    g(φ₁,f) = ∃x(¬φ₁ ∨ f) は偽、g(φ₁φ₂,f) = ∃x(¬(φ₁φ₂) ∨ f) は b で真、
    g(φ₁φ̄₂,f) = ∃x(¬(φ₁φ̄₂) ∨ f) は a で真。等式は 0 = 1 となり破れる。
(ii) 捩れ読み (ax_iii_all が破れる): iall P を「すべての事例で twist(P)」と読む。
    twist は ¬(u . v) を ¬u . ¬v に書き換える構文変換 (誤ったド・モルガン則) で、
    連言と可換なので ax_all_iand は成立する (twist_conj)。iall が行列の
    トートロジー的同値を保たないので ax_iii_all は破れる (iii_all_fails_twist)。
    事例 1 個で φ₁ 偽・φ₂ 真・f 偽とすると、g(φ₁,f) = ¬φ₁ ∨ f は真、
    右辺は (¬φ₁ . ¬φ₂ ∨ f) . (¬φ₁ . ¬¬φ₂ ∨ f) で偽。等式は 1 = 0 となり破れる。
    真理関数的な iall の読みはすべて ax_iii_all を満たすので、これを破るには
    内包キャリアの上でのみ可能な、構文に反応する読みが要る。 -/

namespace QuantifierNecessity

/-- th_19_16_src の行列: 左辺 F16 = (¬φ₁ ∨ f)、右辺 G16a . G16b
= (¬(φ₁φ₂) ∨ f) . (¬(φ₁φ̄₂) ∨ f)。 -/
def F16 : Form := .disj (.neg (.var 0)) (.var 2)
def G16a : Form := .disj (.neg (.conj (.var 0) (.var 1))) (.var 2)
def G16b : Form := .disj (.neg (.conj (.var 0) (.neg (.var 1)))) (.var 2)

/-- 行列の同値 (th_19_16_src の証明内で用いたものと同じ)。 -/
theorem taut_16 : Taut (Form.iffF F16 (Form.conj G16a G16b)) := by
  intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
    simp [F16, G16a, G16b, evalB, h0, h1, h2]

/-- (i) 事例 a の割当: φ₁ 真, φ₂ 真, f 偽。 -/
def va : ℕ → Bool := fun n => match n with | 0 => true | 1 => true | _ => false
/-- (i) 事例 b の割当: φ₁ 真, φ₂ 偽, f 偽。 -/
def vb : ℕ → Bool := fun n => match n with | 0 => true | 1 => false | _ => false

/-- iall の存在読み (事例 a, b): ある事例で真。 -/
def ex (F : Form) : Bool := evalB va F || evalB vb F

/-- 存在読みでも ax_iii_all は成立: 行列がトートロジー的に同値なら値は等しい。 -/
theorem exists_respects_taut (F G : Form) (ht : Taut (Form.iffF F G)) : ex F = ex G := by
  have ha := ht va
  have hb := ht vb
  simp only [evalB, beq_iff_eq] at ha hb
  simp [ex, ha, hb]

/-- 存在読みで ax_all_iand は破れる: ∃x(P . Q) と (∃x P) . (∃x Q) の値が異なる。 -/
theorem all_iand_fails_exists : ex (.conj G16a G16b) ≠ (ex G16a && ex G16b) := by
  decide

/-- **存在読みで th_19_16_src の等式は破れる**: 左辺 g(φ₁,f)/h = 0、
右辺 g(φ₁φ₂,f).g(φ₁φ̄₂,f)/h = 1。 -/
theorem th_19_16_eq_fails_exists : ex F16 = false ∧ (ex G16a && ex G16b) = true := by
  decide

/-- (ii) 捩れ: ¬(u . v) を ¬u . ¬v に書き換える (それ以外は構造を保つ)。 -/
def twist : Form → Form
  | .neg (.conj u v) => .conj (.neg (twist u)) (.neg (twist v))
  | .neg u           => .neg (twist u)
  | .conj u v        => .conj (twist u) (twist v)
  | .disj u v        => .disj (twist u) (twist v)
  | .iffF u v        => .iffF (twist u) (twist v)
  | .var n           => .var n
  | .tru             => .tru
  | .fls             => .fls

/-- 捩れ読みでも ax_all_iand は成立: twist は連言と可換。 -/
theorem twist_conj (u v : Form) : twist (.conj u v) = .conj (twist u) (twist v) := by
  simp [twist]

/-- (ii) 事例 1 個の割当: φ₁ 偽, φ₂ 真, f 偽。 -/
def v1 : ℕ → Bool := fun n => match n with | 0 => false | 1 => true | _ => false

/-- iall の捩れ読み (1 事例): twist した行列の値。 -/
def tw (F : Form) : Bool := evalB v1 (twist F)

/-- 捩れ読みで ax_iii_all は破れる: 行列は同値 (taut_16) だが ∀ の値が異なる。 -/
theorem iii_all_fails_twist : tw F16 ≠ tw (.conj G16a G16b) := by
  decide

/-- **捩れ読みで th_19_16_src の等式は破れる**: 左辺 g(φ₁,f)/h = 1、
右辺 g(φ₁φ₂,f).g(φ₁φ̄₂,f)/h = 0。 -/
theorem th_19_16_eq_fails_twist : tw F16 = true ∧ (tw G16a && tw G16b) = false := by
  decide

end QuantifierNecessity

/-! ## A (続) — §6–§11 の記法 (folio 227–231)

以下はすべて**定義** (印刷された表示式を確率の記法として写したもの) であり、
その値について原著が述べる比較 (φ₁ が小さいほど良い、等) は定理にしない (下記 C)。 -/

/-- Π{ A_{a_r…a_s}(ψ_k) } (folio 229): 部分類推の総乗。各項は (事例の部分列, ψ_k)。 -/
noncomputable def PiA : List (List Inst × PFun) → IProp
  | []             => itrue
  | [(l, ψ)]       => A l ψ
  | (l, ψ) :: rest => iand (A l ψ) (PiA rest)

/-- **folio 227 (台帳 #26)** `g(φ, f) / A_{a₁…aₙ}(φφ₁f)`: 第二の型 (知識は完全だが
正の類推 φ₁ が一般化に覆われない) の類推論証の確率。 -/
noncomputable def p_sec6 (l : List Inst) (φ φ₁ f : PFun) : ℝ :=
  PrI (g φ f) (A l (φ ∧ₚ φ₁ ∧ₚ f))

/-- **folio 228 (台帳 #29)** `g(φ, f) / A_{a₁…aₙ}(φφ₁f) Ā_{a₁…aₙ}(φ′)`: 第三の型
(知識が不完全)。既知の負の類推 φ′ を明示する。
添字について: 印刷では Ā の添字は A と同じ事例列 a₁…aₙ であり、脚注 (folio 224)
の範囲 a_r…a_s, a_r′…a_s′ はその部分列。本定義は rs, rs' を l と独立な引数にとる
ので印刷より一般であり、印刷形は rs, rs' ⊆ l の特殊な場合。 -/
noncomputable def p_sec7 (l rs rs' : List Inst) (φ φ₁ f φ' : PFun) : ℝ :=
  PrI (g φ f) (iand (A l (φ ∧ₚ φ₁ ∧ₚ f)) (Abar rs rs' φ'))

/-- **folio 229 (台帳 #32) = folio 231 (台帳 #42)**
`g(φ, f) / A_{a₁…aₙ}(φφ₁f) Ā_{a₁…aₙ}(φ′) Π{ A_{a_r…a_s}(ψ_k) }`:
部分類推を加えた式。§11 で以後の「第三段階の一般性」の作業式とされる。
添字について: 印刷では Ā の添字は a₁…aₙ (A と同じ事例列)、Π の各項の添字
a_r…a_s はその部分列。本定義は rs, rs' と subs の各事例列を l と独立な引数に
とるので印刷より一般であり、印刷形はそれらが l の部分列である特殊な場合。 -/
noncomputable def p_sec8 (l rs rs' : List Inst) (subs : List (List Inst × PFun))
    (φ φ₁ f φ' : PFun) : ℝ :=
  PrI (g φ f) (iand (A l (φ ∧ₚ φ₁ ∧ₚ f)) (iand (Abar rs rs' φ') (PiA subs)))

/-- **folio 229 (台帳 #34)** `A_{b₁…b_m}(_bφ _bφ₁ _bf) Ā_{b₁…b_m}(_bφ′) Π{ A_{b_r…b_s}(_bψ_k) }`:
部分的事例 b₁…b_m が示す類推 (証拠側の命題)。_bφ, _bf は φ, f の部分。
「部分」の関係 (_bφ は φ の一部) は原著では非形式的に置かれており、ここでは
別個の命題関数として引数にとる。 -/
noncomputable def ev_partial (lb rb rb' : List Inst) (subsb : List (List Inst × PFun))
    (bφ bφ₁ bf bφ' : PFun) : IProp :=
  iand (A lb (bφ ∧ₚ bφ₁ ∧ₚ bf)) (iand (Abar rb rb' bφ') (PiA subsb))

/-- 一つの事例集合 (a₁…aₙ, b₁…b_m, …) とその正・負の類推。folio 230 の Π_{a,b…} の一項。 -/
structure InstSet where
  l   : List Inst
  rs  : List Inst
  rs' : List Inst
  φa  : PFun     -- _aφ  (φ の全体または部分)
  φ₁a : PFun     -- _aφ₁
  fa  : PFun     -- _af  (f の全体または部分)
  φ'a : PFun     -- _aφ′ (印刷は _aφ¹、下記)

/-- Π_{a,b…}{ A_{a₁…aₙ}(_aφ _aφ₁ _af) Ā_{a₁…aₙ}(_aφ′) } (folio 230)。 -/
noncomputable def PiSets : List InstSet → IProp
  | []        => itrue
  | [s]       => iand (A s.l (s.φa ∧ₚ s.φ₁a ∧ₚ s.fa)) (Abar s.rs s.rs' s.φ'a)
  | s :: rest => iand (iand (A s.l (s.φa ∧ₚ s.φ₁a ∧ₚ s.fa)) (Abar s.rs s.rs' s.φ'a))
                      (PiSets rest)

/-- **folio 230 (台帳 #35) 一般式**
`g(φ, f) / Π_{a,b…}{ A_{a₁…aₙ}(_aφ _aφ₁ _af) Ā_{a₁…aₙ}(_aφ¹) } Π{ A_{a_r b_s…}(ψ_k) }`。

**印刷上の注記 (folio 230)**: 負の類推の項は印刷では `Ā_{a₁…aₙ}(_aφ¹)` と上付き
「1」で組まれている。folio 227, 228, 229, 231 の同じ項はすべて `φ′` (プライム)
であり、§7 の本文も「φ′ は異なると知られる特性」と述べるので、`_aφ′` の誤植と
みる。本定義は φ′ の読み (InstSet.φ'a) で書く。印刷形を機械反駁する対象ではない
(記号の取り違えであり、命題の真偽に関わらない)。 -/
noncomputable def p_sec9 (sets : List InstSet) (subs : List (List Inst × PFun))
    (φ f : PFun) : ℝ :=
  PrI (g φ f) (iand (PiSets sets) (PiA subs))

/-- **folio 230 (台帳 #38)** `A_{a₁′…a′_{n′}}(_{a′}φ _{a′}f̄)`: 負の証拠。_{a′}φ (φ の一部) が
集合全体に真で、_{a′}f (f の一部) が集合全体に偽である類推。 -/
noncomputable def ev_negative (l' : List Inst) (φa' fa' : PFun) : IProp :=
  A l' (φa' ∧ₚ ¬ₚ fa')

/-- 補助 (rfl)。部分類推のない場合 (subs = [])、§8 の式の証拠は PiA [] = itrue により
`A(φφ₁f) . (Ā(φ′) . itrue)` に展開される。これは §7 の式 p_sec7 の証拠
`A(φφ₁f) . Ā(φ′)` に確実命題 itrue を連言した形であり、両者の確率の一致
(itrue の連言肢の除去) は本ファイルの公理からは証明しない (定理にしない)。 -/
theorem p_sec8_nil (l rs rs' : List Inst) (φ φ₁ f φ' : PFun) :
    p_sec8 l rs rs' [] φ φ₁ f φ'
      = PrI (g φ f) (iand (A l (φ ∧ₚ φ₁ ∧ₚ f)) (iand (Abar rs rs' φ') itrue)) := rfl

/-- 補助 (rfl)。事例集合 1 個・部分類推なしの場合、§9 の一般式の証拠は
PiSets [s] と PiA [] = itrue の連言に展開される。p_sec8_nil と同じく、itrue の
連言肢の除去は証明しない。 -/
theorem p_sec9_single (s : InstSet) (φ f : PFun) :
    p_sec9 [s] [] φ f
      = PrI (g φ f) (iand (iand (A s.l (s.φa ∧ₚ s.φ₁a ∧ₚ s.fa)) (Abar s.rs s.rs' s.φ'a))
                          itrue) := rfl

/-! ## C. 形式化の境界の記録 (§5–§11)

以下の主張は第 II 部の公理 (Def.IX, Def.X, 範囲原理, Ax.(iii)) と本ファイルの
量化子原理 (ax_iii_all, ax_all_iand) からの導出が未構成である (導けないことの
反例モデルも未構成)。それぞれ、どの原理を追加すれば定理になり得るかを記す。
定理にはしない (他の機会に譲る)。
量化子原理そのものの必要性 (th_19_16_src に対する) は、証明から落とすと赤になる
ことで確認した。公理群全体 (第 II 部の公理 + 量化子原理の一方) を満たしつつ
th_19_16_src の等式を破る反例モデルは未構成であり、QuantifierNecessity に置いた
のは Bool 評価での数値例 (読み替えの下で両辺の値が食い違う) のみである。

  (§5, #21–25)  完全類推 (perfect analogy) と「無関係 (irrelevant) な区別」。
      要る原理: 「a についての言明」という関係 (脚注 ψ(a) = h . θ(a))、および
      同一者不可識別の原理。確率公理の外。

  (§6, #27–28)  「φ₁ が小さいほど g(φ,f)/A(φφ₁f) は大きい」、「φ₁ を大きく減らす
      1 事例は φ₁ にあまり影響しない多数の事例より確率を高める」。
      要る原理: 証拠 A(φφ₁f) の φ₁ 部分の包括性 (命題関数の包含順序) を確率の
      順序に写す単調性原理。Def.X からは、φ₁ ⊃ φ₁′ のとき
      g(φ,f)/A(φφ₁f) と g(φ,f)/A(φφ₁′f) の大小は決まらない (条件が変わる)。
      Keynes 自身、正当化は第 XX–XXII 章に委ねる (§12, #47)。

  (§7, #30)  事例の数 n が多いほど総負の類推が既知負の類推を超える機会が大きい。
      要る原理: 純粋帰納の原理 (第 XX 章)。本章では述べるのみ。

  (§8, #31)  部分類推 ψ_k の存在は「明らかに (evidently)」弱点。
      要る原理: §6 と同じ単調性原理 (ψ_k を φ₁ の一部とみなす読み)。

  (§10, #37 後半, #39–40)  φ の一部が真で f が偽の事例は「ある程度」弱める;
      φ, f がともに偽の事例は有利に関連する。
      要る原理: 「有利 (favourable)」の判断を与える関連性原理 (第 XVI 章の
      favourable evidence の定義では、A(_{a′}φ _{a′}f̄) が g(φ,f) に対して
      unfavourable であることは φ, f の内容を固定しない限り決まらない)。
      #40 は原著自身が「問題はやや困惑的」として未決。
      #37 前半 (φ 真・f 偽の事例があれば一般化は覆される) は iall の導入則
      ∀x P(x) ⊃ P(a) を加えれば定理になる (本ファイルには未収録)。

  (§11, #44–46)  論証を強める三手段 (φ₁ を減らす・φ′ を増やす・ψ_k を減らす) が
      「かなり明白 (fairly obvious)」に確率を高める。
      要る原理: 「φ₁ が φ とともに f の必要条件である可能性」を確率の減少に
      結ぶ原理 — §6 と同じ単調性原理の言い換え。

  (§4, #19)  二つの一般化の à priori 確率を大小比較できるのは条件と結論の包含が
      交差する場合に限る。これは「比較できない場合がある」という第 I 部第 III 章
      の主張の適用であり、本公理系 (PrI : … → ℝ) は全順序を前提にするので
      「比較不能」を述べる語彙がない。th_19_18_src が示すのは「包含があれば
      比較できる」の側のみ。
-/

end KeynesIII

/-! ## 監査クエリ (Phase 9b) -/

#check @KeynesIII.th_19_16_src
#check @KeynesIII.th_19_17
#check @KeynesIII.th_19_17_src_iff
#check @KeynesIII.th_19_18_src
#check @KeynesIII.Erratum19_17Countermodel.printed_form_fails
#check @KeynesIII.Erratum19_17Countermodel.hypotheses_of_17_hold
#check @KeynesIII.StrictnessCountermodel.chain_is_equality
#check @KeynesIII.QuantifierNecessity.th_19_16_eq_fails_exists
#check @KeynesIII.QuantifierNecessity.th_19_16_eq_fails_twist

#print axioms KeynesIII.th_12_i
#print axioms KeynesIII.pr_conj_le_left_i
#print axioms KeynesIII.A_three
#print axioms KeynesIII.Abar_example
#print axioms KeynesIII.th_19_16_src
#print axioms KeynesIII.pr_g_concl_split
#print axioms KeynesIII.th_19_17
#print axioms KeynesIII.th_19_17_src_iff
#print axioms KeynesIII.th_19_18_src
#print axioms KeynesIII.Erratum19_17Countermodel.masses_consistent
#print axioms KeynesIII.Erratum19_17Countermodel.corrected_form_holds
#print axioms KeynesIII.Erratum19_17Countermodel.printed_form_fails
#print axioms KeynesIII.Erratum19_17Countermodel.inequality_holds
#print axioms KeynesIII.Erratum19_17Countermodel.masses_by_enumeration
#print axioms KeynesIII.Erratum19_17Countermodel.instance_c_inert
#print axioms KeynesIII.Erratum19_17Countermodel.masses_match_enumeration
#print axioms KeynesIII.Erratum19_17Countermodel.hypotheses_of_17_hold
#print axioms KeynesIII.StrictnessCountermodel.masses_by_enumeration
#print axioms KeynesIII.StrictnessCountermodel.masses_match_enumeration
#print axioms KeynesIII.StrictnessCountermodel.independence_premises_hold
#print axioms KeynesIII.StrictnessCountermodel.chain_is_equality
#print axioms KeynesIII.QuantifierNecessity.taut_16
#print axioms KeynesIII.QuantifierNecessity.exists_respects_taut
#print axioms KeynesIII.QuantifierNecessity.all_iand_fails_exists
#print axioms KeynesIII.QuantifierNecessity.th_19_16_eq_fails_exists
#print axioms KeynesIII.QuantifierNecessity.twist_conj
#print axioms KeynesIII.QuantifierNecessity.iii_all_fails_twist
#print axioms KeynesIII.QuantifierNecessity.th_19_16_eq_fails_twist
#print axioms KeynesIII.p_sec8_nil
#print axioms KeynesIII.p_sec9_single
