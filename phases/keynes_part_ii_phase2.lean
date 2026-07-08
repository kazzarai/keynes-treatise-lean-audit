/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 2
#
# 新井一成・Claude共著、2026年4月
# Phase 1 (pilot, 7 ノード)  → Phase 2 (Ch.12 完成版, +18 ノード = 合計約 25 ノード)
#
# ## 本ファイルで追加したもの
#   Definitions:  Def.II, III, IV, V, VI, VII, VIII, XIV (8 個)
#   Axioms:       Ax.(i) コメント化, Ax.(ii), Ax.(iii_true) 補助形,
#                 Ax.(iv-a,b,c), Ax.(v), Ax.(vi)           (8 個)
#   Theorems:     Th.(13.1), (13.2), (13.3), (13.19), (13.20)  (5 個)
#
# Pilot から継承:  Pr, Def.IX, Def.X (L/R), Def.XI, Def.XII, Def.XIII,
#                 ax_iii_op, Th.(24), Th.(24.1)
#
# ## 検証方法
#   1. https://live.lean-lang.org/ にアクセス
#   2. エディタの中身を削除してこのファイルを貼る
#   3. Mathlib ロード完了後、赤い波線が無ければ kernel accepted
#   4. ファイル末尾の `#print axioms` ブロックで全定理のカーネル依存を確認
#
# ## 期待される kernel 依存の変化
#   Phase 1 pilot: {propext, Classical.choice, Quot.sound, Pr, ax_iii_op, def_IX}
#   Phase 2 では Def.XII が def_IX + 算術だけでは完結しない Th.(13.1) 等で
#   明示的に必要になる可能性がある (Mode B∩C 仮説の再検証機会)。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace Keynes

/-! ## プリミティブ -/

/-- **Primitive probability function** (Keynes の一次関係).
値域は ℝ。`Mathlib.MeasureTheory.Probability` を import しないことで
「σ-加法族上の測度」ではなく「命題間の一次関係」という Keynes の立場を
型レベルで明示する。 -/
axiom Pr : Prop → Prop → ℝ

/-! ## Ch.12 §4 Preliminary Definitions -/

/- **Def.I** (確率記号). `α/h = P` を Lean では `Pr α h = P` と書く。
これは Keynes の表記定義に過ぎず、独立した公理は不要。 -/

/-- **Def.II** (確実性). -/
def Certain (α h : Prop) : Prop := Pr α h = 1

/-- **Def.III** (不可能性). -/
def Impossible (α h : Prop) : Prop := Pr α h = 0

/-- **Def.IV** (非確実性). -/
def NonCertain (α h : Prop) : Prop := Pr α h < 1

/-- **Def.V** (非不可能性). -/
def NonImpossible (α h : Prop) : Prop := 0 < Pr α h

/-- **Def.VI** (不整合性). Keynes の原文は「`α/h=0` ならば `αh` は不整合」という
*定義的語彙導入*。ここでは `Pr α h = 0` を満たすことを述語 `Inconsistent α h`
と同一視する。 -/
def Inconsistent (α h : Prop) : Prop := Pr α h = 0

/-- **Def.VII** (群). Keynes:「`α/h=1` であるような命題 α のクラスを
h によって定まる群と呼ぶ」。述語化。 -/
def InGroup (α h : Prop) : Prop := Pr α h = 1

/-- **Def.VIII** (等値). `(α=β)/h=1` は Keynes 原文で
「`β/αh=1 かつ α/βh=1`」と定義される。 -/
def KEq (α β h : Prop) : Prop := Pr β (α ∧ h) = 1 ∧ Pr α (β ∧ h) = 1

/-! ## Ch.12 §5 Preliminary Axioms -/

/- **Ax.(i)** (存在・一意性). 「整合的 h に対し確率関係は一意に存在する」。
Lean では `Pr : Prop → Prop → ℝ` が *関数* であることから自動的に保証される。
したがって独立した `axiom` 宣言を追加する必要はない。 -/

/-- **Ax.(ii)** (等値公理). `(α=β)/h=1` のとき任意の命題 c について
`c/(αh) = c/(βh)`。 -/
axiom ax_ii (α β h c : Prop) :
    KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)

/-- **Ax.(iii)**_op (Tautology 公理 / 作用形). Pilot で導入。
命題論理的に同値な命題は同じ確率を持つ。 -/
axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h

/-- **Ax.(iii)**_true (Tautology 公理 / 確実形).
「tautology の確率は 1」の直接形。Keynes 原文 Ax.(iii) の主眼。 -/
axiom ax_iii_true (h : Prop) : Pr True h = 1

/-- **Ax.(iv-a)** (交換律). Keynes は `PQ=QP`, `P+Q=Q+P` を明記する。
ℝ の可換性から自動だが、Keynes の体系では独立した公理として位置づけられるため
テキスト忠実性のために宣言。Lean の proof はすべて ℝ 側の可換性で完了する。 -/
axiom ax_iva_mul (P Q : ℝ) : P * Q = Q * P
axiom ax_iva_add (P Q : ℝ) : P + Q = Q + P

/-- **Ax.(iv-b)** (順序公理).
Keynes: `Q≠0 → P+Q > P` (確率値の正性を前提とする)。
Lean 側では Q > 0 版として定式化。 -/
axiom ax_ivb (P Q : ℝ) : 0 < Q → P < P + Q

/-- **Ax.(iv-c)** (消去律).
`P+Q = P+R → Q = R`. ℝ の加法消去律と一致。 -/
axiom ax_ivc (P Q R : ℝ) : P + Q = P + R → Q = R

/-- **Ax.(v)** (混合演算結合律).
Keynes: `[±P±Q] + [±R±S] = [±P±R] ∓ [±Q∓S]`。ℝ の結合・交換律から導出可能。
代表形だけを axiom 化。 -/
axiom ax_v (P Q R S : ℝ) : (P + Q) + (R + S) = (P + R) + (Q + S)

/-- **Ax.(vi)** (分配律). `P(R+S) = PR + PS`. -/
axiom ax_vi (P R S : ℝ) : P * (R + S) = P * R + P * S

/-! ## Ch.12 §6 Operation Definitions (pilot から継承) -/

/-- **Def.IX** (加法). `αb̄/h + αb/h = α/h`. -/
axiom def_IX (p q h : Prop) :
    Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h

/-- **Def.X** (乗法 / 左形). `αb/h = α/(bh) · b/h`. -/
axiom def_X_left (p q h : Prop) :
    Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h

/-- **Def.X** (乗法 / 右形). `αb/h = b/(αh) · α/h`. -/
axiom def_X_right (p q h : Prop) :
    Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h

/-- **Def.XI** (除法). `PQ=R → P=R/Q` (`Q≠0`). -/
axiom def_XI (P Q R : ℝ) (hQ : Q ≠ 0) :
    P * Q = R → P = R / Q

/-- **Def.XII** (減法). `P+Q=R → P=R-Q`. Pilot で Mode B∩C と判定された定義。 -/
axiom def_XII (P Q R : ℝ) :
    P + Q = R → P = R - Q

/-! ## Ch.12 §8 Independence / Irrelevance -/

/-- **Def.XIII** (独立性). -/
def Independent (p q h : Prop) : Prop :=
    Pr p (q ∧ h) = Pr p h ∧ Pr q (p ∧ h) = Pr q h

/-- **Def.XIV** (無関連性). 「`α₂` は `α₁/h` に無関連」 ⇔ `Pr α₁ (α₂∧h) = Pr α₁ h`. -/
def Irrelevant (α₂ α₁ h : Prop) : Prop := Pr α₁ (α₂ ∧ h) = Pr α₁ h

/-! ## Ch.14 Theorem (24) & (24.1) (pilot から継承)
    *順序上の注意*: th_13_20 が th_24 を呼ぶため、論理順序ではこちらを先に置く。
    Keynes の章番号は pedagogical であって logical ではない。 -/

/-- **Theorem (24)** — 加法定理. `(α∨β)/h = α/h + β/h - (α∧β)/h`. -/
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

/-- **Theorem (24.1)** — 相互排反の場合. -/
theorem th_24_1 (α β h : Prop) (hexcl : Pr (α ∧ β) h = 0) :
    Pr (α ∨ β) h = Pr α h + Pr β h := by
  rw [th_24]
  linarith

/-! ## Ch.13 基礎定理 (5 本) -/

/-- **Th.(13.1)** 矛盾命題の確率の和 = 1.
    `α/h + ᾱ/h = 1`.
    Prolog DB: cites(th13_1, def_ix), cites(th13_1, def_x), cites(th13_1, ax_iii).

## Proof architecture
| Step | Mechanism   | Cites             |
|------|-------------|-------------------|
|  1   | def_IX      | explicit          |
|  2   | ax_iii_op   | explicit (tauto 経由) |
|  3   | ax_iii_true | explicit          |
|  4   | linarith    | IMPLICIT Def.XII  | -/
theorem th_13_1 (α h : Prop) :
    Pr α h + Pr (¬α) h = 1 := by
  have step1 : Pr (True ∧ ¬α) h + Pr (True ∧ α) h = Pr True h :=
    def_IX True α h
  have eq1 : (True ∧ ¬α) ↔ ¬α := by tauto
  have eq2 : (True ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h eq1, ax_iii_op _ _ h eq2] at step1
  rw [ax_iii_true h] at step1
  linarith

/-- **Th.(13.2)** 非確実 → 1 未満.  `Def.IV` の直接適用だけで自明。 -/
theorem th_13_2 (α h : Prop) :
    NonCertain α h → Pr α h < 1 := by
  intro h_nc
  exact h_nc

/-- **Th.(13.3)** 非不可能 → 0 超.  `Def.V` の直接適用。 -/
theorem th_13_3 (α h : Prop) :
    NonImpossible α h → 0 < Pr α h := by
  intro h_ni
  exact h_ni

/-- **Th.(13.19)** 矛盾原理. `αᾱ/h = 0`.

## Proof architecture
| Step | Mechanism              | Cites               |
|------|------------------------|---------------------|
|  1   | def_IX (α,α,h)         | explicit            |
|  2   | ax_iii_op: (α∧α)↔α     | explicit            |
|  3   | linarith               | IMPLICIT Def.XII    |

Prolog DB は (19) → (18),(1),(15) と経由した導出を記録しているが、
Lean では def_IX を `p := α, q := α` に特殊化するだけで 1 行で済む。
これは Keynes が他の定理経由で遠回りに証明した結果を、Lean が直接導出
できる事例: *数学的 shortcut が kernel レベルで検出される* Mode A" の候補。 -/
theorem th_13_19 (α h : Prop) :
    Pr (α ∧ ¬α) h = 0 := by
  have step1 : Pr (α ∧ ¬α) h + Pr (α ∧ α) h = Pr α h :=
    def_IX α α h
  have eq : (α ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h eq] at step1
  linarith

/-- **Th.(13.20)** 排中原理. `(α∨¬α)/h = 1`.

## Proof architecture
| Step | Mechanism              | Cites               |
|------|------------------------|---------------------|
|  1   | th_24 α (¬α) h         | chain: Def.IX, Ax.(iii) |
|  2   | th_13_19 α h           | chain: Def.IX, Ax.(iii) |
|  3   | th_13_1 α h            | chain: Def.IX, Ax.(iii) |
|  4   | linarith               | IMPLICIT Def.XII    |

Prolog DB は (20) → ax_iii,(19),(12),(1) と記録している。Lean proof は
(24) + (19) + (1) で閉じ、(12) を経由しない。これは引用 DAG の最小性
(minimum cut-set) を kernel が自動発見する典型例。 -/
theorem th_13_20 (α h : Prop) :
    Pr (α ∨ ¬α) h = 1 := by
  have h24  : Pr (α ∨ ¬α) h = Pr α h + Pr (¬α) h - Pr (α ∧ ¬α) h :=
    th_24 α (¬α) h
  have h19  : Pr (α ∧ ¬α) h = 0 := th_13_19 α h
  have h131 : Pr α h + Pr (¬α) h = 1 := th_13_1 α h
  linarith

end Keynes

/-! ## 監査クエリ -/

-- 署名検査: 定理の型が Prolog DB の主張と一致するか
#check @Keynes.th_13_1
#check @Keynes.th_13_2
#check @Keynes.th_13_3
#check @Keynes.th_13_19
#check @Keynes.th_13_20
#check @Keynes.th_24
#check @Keynes.th_24_1

-- 各定理の kernel 依存を列挙。Mode C (undeclared prerequisite) の検出に用いる。
-- pilot からの変化点:
--   th_13_1  → ax_iii_true が初登場
--   th_13_19 → def_IX のみで閉じる (shortcut 発見)
--   th_13_20 → th_24 を経由するので def_IX + ax_iii_op チェーン全体が surface
#print axioms Keynes.th_13_1
#print axioms Keynes.th_13_2
#print axioms Keynes.th_13_3
#print axioms Keynes.th_13_19
#print axioms Keynes.th_13_20
#print axioms Keynes.th_24
#print axioms Keynes.th_24_1
