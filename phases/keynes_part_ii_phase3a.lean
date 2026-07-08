/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 3a
#
# 新井一成・Claude共著、2026年4月
# Phase 2 (Ch.12 完成, 25 ノード) → Phase 3a (Ch.14 乗法・Bayes, +3 定理)
#
# ## 本ファイルで追加したもの
#   Theorems:
#     Th.(14.24.2)  : αb/h + ᾱb/h = b/h  ――― def_IX の純粋な応用
#     Th.(14.36)    : 独立 → αβ/h = α/h · β/h  ――― def_X と Def.XIII 初登場
#     Th.(14.38_b)  : α/(bh) = αb/h / b/h  ――― def_XI 初登場 (Bayes 基本形)
#
# 継承: Phase 2 の全 25 ノード (再掲)
#
# ## 目的
# Phase 2 では def_X, def_XI, def_XIII が #print axioms に一度も surface しなかった。
# 本ファイルでは乗法と独立性を明示的に使う 3 定理を追加し、これら 3 axiom が
# 初めてカーネル依存リストに現れることを確認する。
#
# ## 期待される新規 surface
#   th_14_24_2 : def_IX のみ (新規なし)
#   th_14_36   : def_X_left + Keynes.Independent 展開
#                Independent は def なので Lean の axiom リストには出ないが、
#                展開後の def_X_left は必ず surface する。
#   th_14_38_b : def_X_left + def_XI  ――― Def.XI が初登場
#
# ## 検証方法
#   1. https://live.lean-lang.org/ にアクセス
#   2. エディタの中身を削除してこのファイルを貼る
#   3. Mathlib ロード完了後、赤い波線が無ければ kernel accepted
#   4. ファイル末尾の `#print axioms` ブロックで新規 surface を確認
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FieldSimp

namespace Keynes

/-! ## プリミティブ (Phase 1-2 から継承) -/

axiom Pr : Prop → Prop → ℝ

/-! ## Ch.12 §4 Preliminary Definitions -/

def Certain       (α h : Prop) : Prop := Pr α h = 1
def Impossible    (α h : Prop) : Prop := Pr α h = 0
def NonCertain    (α h : Prop) : Prop := Pr α h < 1
def NonImpossible (α h : Prop) : Prop := 0 < Pr α h
def Inconsistent  (α h : Prop) : Prop := Pr α h = 0
def InGroup       (α h : Prop) : Prop := Pr α h = 1
def KEq (α β h : Prop) : Prop := Pr β (α ∧ h) = 1 ∧ Pr α (β ∧ h) = 1

/-! ## Ch.12 §5-§6 Axioms -/

axiom ax_ii (α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)
axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1
axiom ax_iva_mul (P Q : ℝ) : P * Q = Q * P
axiom ax_iva_add (P Q : ℝ) : P + Q = Q + P
axiom ax_ivb (P Q : ℝ) : 0 < Q → P < P + Q
axiom ax_ivc (P Q R : ℝ) : P + Q = P + R → Q = R
axiom ax_v (P Q R S : ℝ) : (P + Q) + (R + S) = (P + R) + (Q + S)
axiom ax_vi (P R S : ℝ) : P * (R + S) = P * R + P * S

/-! ## Ch.12 §6 Operation Definitions -/

axiom def_IX (p q h : Prop) :
    Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h

axiom def_X_left (p q h : Prop) :
    Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h

axiom def_X_right (p q h : Prop) :
    Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h

axiom def_XI (P Q R : ℝ) (hQ : Q ≠ 0) :
    P * Q = R → P = R / Q

axiom def_XII (P Q R : ℝ) :
    P + Q = R → P = R - Q

/-! ## Ch.12 §8 Independence / Irrelevance -/

/-- **Def.XIII** (独立性). `α₁/α₂h = α₁/h ∧ α₂/α₁h = α₂/h`. -/
def Independent (p q h : Prop) : Prop :=
    Pr p (q ∧ h) = Pr p h ∧ Pr q (p ∧ h) = Pr q h

def Irrelevant (α₂ α₁ h : Prop) : Prop := Pr α₁ (α₂ ∧ h) = Pr α₁ h

/-! ## Ch.13-14 既証定理 (Phase 2 から継承) -/

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

theorem th_24_1 (α β h : Prop) (hexcl : Pr (α ∧ β) h = 0) :
    Pr (α ∨ β) h = Pr α h + Pr β h := by
  rw [th_24]
  linarith

theorem th_13_1 (α h : Prop) :
    Pr α h + Pr (¬α) h = 1 := by
  have step1 : Pr (True ∧ ¬α) h + Pr (True ∧ α) h = Pr True h :=
    def_IX True α h
  have eq1 : (True ∧ ¬α) ↔ ¬α := by tauto
  have eq2 : (True ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h eq1, ax_iii_op _ _ h eq2] at step1
  rw [ax_iii_true h] at step1
  linarith

theorem th_13_19 (α h : Prop) :
    Pr (α ∧ ¬α) h = 0 := by
  have step1 : Pr (α ∧ ¬α) h + Pr (α ∧ α) h = Pr α h :=
    def_IX α α h
  have eq : (α ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h eq] at step1
  linarith

theorem th_13_20 (α h : Prop) :
    Pr (α ∨ ¬α) h = 1 := by
  have h24  : Pr (α ∨ ¬α) h = Pr α h + Pr (¬α) h - Pr (α ∧ ¬α) h :=
    th_24 α (¬α) h
  have h19  : Pr (α ∧ ¬α) h = 0 := th_13_19 α h
  have h131 : Pr α h + Pr (¬α) h = 1 := th_13_1 α h
  linarith

/-! ## Phase 3a: 新規定理 -/

/-- **Th.(14.24.2)**.  `αb/h + ᾱb/h = b/h`.
Keynes Prolog DB: cites(th14_24_2, def_ix, 'Def.IXの特殊化').

## Proof architecture
| Step | Mechanism                        | Cites             |
|------|----------------------------------|-------------------|
|  1   | def_IX b α h (roles swapped)     | explicit          |
|  2   | ax_iii_op: (b∧¬α) ↔ (¬α∧b) 他   | explicit          |
|  3   | linarith                         | IMPLICIT Def.XII  |

Def.IX は `Pr(p∧¬q) h + Pr(p∧q) h = Pr p h` の形。
`p := b, q := α` と特殊化するだけで、交換律のトートロジーで記号を揃える。 -/
theorem th_14_24_2 (α b h : Prop) :
    Pr (α ∧ b) h + Pr (¬α ∧ b) h = Pr b h := by
  have step1 : Pr (b ∧ ¬α) h + Pr (b ∧ α) h = Pr b h :=
    def_IX b α h
  have eq1 : (b ∧ ¬α) ↔ (¬α ∧ b) := by tauto
  have eq2 : (b ∧ α) ↔ (α ∧ b) := by tauto
  rw [ax_iii_op _ _ h eq1, ax_iii_op _ _ h eq2] at step1
  linarith

/-- **Th.(14.36)** 乗法定理 (独立な場合). `α, β 独立 → αβ/h = α/h · β/h`.
Keynes Prolog DB: cites(th14_36, def_x), cites(th14_36, def_xiii).

## Proof architecture
| Step | Mechanism                 | Cites             |
|------|---------------------------|-------------------|
|  1   | def_X_left α β h          | explicit (Def.X)  |
|  2   | Independent.1 を展開      | explicit (Def.XIII)|
|  3   | rw                        | (算術)             |

## 検証対象
- `def_X_left` が kernel に初登場するか
- `Independent` は def なので Lean 内では展開されるが、`def_X_left` は surface する
  はず。これが Phase 3a の主要な確認事項。 -/
theorem th_14_36 (α β h : Prop) (hindep : Independent α β h) :
    Pr (α ∧ β) h = Pr α h * Pr β h := by
  have step1 : Pr (α ∧ β) h = Pr α (β ∧ h) * Pr β h :=
    def_X_left α β h
  rw [step1, hindep.1]

/-- **Th.(14.38)_b** Bayes 基本形.  `α/(bh) = (αb/h) / (b/h)` (when `b/h ≠ 0`).

Keynes の Th.(14.38) は完全な逆確率比の形だが、本ファイルでは Bayes の中核を成す
「条件付き確率は同時確率を周辺確率で割った値」という形を先に証明する。

Keynes Prolog DB: cites(th14_38, def_x), cites(th14_38, def_xi).

## Proof architecture
| Step | Mechanism           | Cites             |
|------|---------------------|-------------------|
|  1   | def_X_left α b h    | explicit (Def.X)  |
|  2   | 式を入れ替えて      |                    |
|  3   | def_XI 適用         | explicit (Def.XI) |

## 検証対象
- `def_XI` が kernel に初登場
- `def_X_left` も surface -/
theorem th_14_38_b (α b h : Prop) (hb : Pr b h ≠ 0) :
    Pr α (b ∧ h) = Pr (α ∧ b) h / Pr b h := by
  have step1 : Pr (α ∧ b) h = Pr α (b ∧ h) * Pr b h :=
    def_X_left α b h
  -- def_XI は `P * Q = R → P = R / Q` の形。step1 を左右入れ替えて適用。
  exact def_XI (Pr α (b ∧ h)) (Pr b h) (Pr (α ∧ b) h) hb step1.symm

end Keynes

/-! ## 監査クエリ (Phase 3a 新規) -/

-- 署名検査
#check @Keynes.th_14_24_2
#check @Keynes.th_14_36
#check @Keynes.th_14_38_b

-- kernel 依存.
-- 注目点:
--   th_14_24_2 → def_IX のみ (Phase 2 定理と同じ)
--   th_14_36   → def_X_left が初登場; Independent は def なのでリストには出ない
--   th_14_38_b → def_X_left + def_XI が surface
#print axioms Keynes.th_14_24_2
#print axioms Keynes.th_14_36
#print axioms Keynes.th_14_38_b

-- Phase 2 既証の再確認 (回帰テスト)
#print axioms Keynes.th_13_1
#print axioms Keynes.th_13_19
#print axioms Keynes.th_13_20
#print axioms Keynes.th_24
