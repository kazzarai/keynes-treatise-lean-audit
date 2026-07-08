/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7a
#
# 新井一成・Claude共著、2026年7月8日
# 分類訂正: 「残り 14 本」台帳の精査により、(13.16.1) と (13.16.3) は
# DB gloss 損傷組ではなく**現有公理で可証明**と判明したため、ここで検証する。
# (16 族を一括で損傷扱いした Phase 6b 時点の分類が粗かった — 監査の監査。)
#
# ## 本ファイルで追加したもの (数値ノード 2)
#   th_13_16_1 : h₁/h₂h = 1 → (h₂⊃h₁)/h = 1
#   th_13_16_3 : (h₂⊃h₁)/h = 1 ∧ h₂ 非不可能 → h₁/h₂h = 1
#
# 両者を合わせると「条件付き確実性 ⟺ 条件文の確実性」(h₂ 整合の下) の
# 往復になる。Keynes の条件付き確率と実質含意の間の橋であり、
# Ramsey テスト前史としても読める箇所。
#
# ## 検証したい仮説
#   H20: 両定理の kernel 集合は {ax_iii_op, ax_iii_true, def_IX, def_X_left}
#        + floor に収まる (範囲原理は不要)。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase7a.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (継承) -/

axiom Pr : Prop → Prop → ℝ

axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1

axiom def_IX (p q h : Prop) :
    Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h
axiom def_X_left (p q h : Prop) :
    Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h

/-! ## 再掲 (証明付き) -/

theorem th_13_1 (α h : Prop) : Pr α h + Pr (¬α) h = 1 := by
  have step := def_IX True α h
  have e1 : (True ∧ ¬α) ↔ ¬α := by tauto
  have e2 : (True ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, ax_iii_true] at step
  linarith

/-! ## Phase 7a 新規 (2 本) -/

/-- **Th.(13.16.1)** 条件付き確実性から条件文の確実性へ.
h₁/h₂h = 1 ならば (h₂⊃h₁)/h = 1。h₂ の整合性すら不要
(h₂ が不可能なら含意は空虚に確実になる)。

Keynes Prolog DB: cites(th13_16, th13_1), cites(th13_16, th13_15) 系列。

## Proof architecture
| Step | Mechanism                                  | Cites            |
|------|--------------------------------------------|------------------|
|  1   | 補完律 at (h₂∧h): ¬h₁ の条件付き不可能性  | (13.1)           |
|  2   | def_X_left で ¬h₁∧h₂/h = 0                 | Def.X            |
|  3   | ¬(h₂→h₁) ↔ ¬h₁∧h₂ (古典)                   | Ax.(iii)         |
|  4   | 補完律 at h                                 | (13.1)           | -/
theorem th_13_16_1 (h₁ h₂ h : Prop) (hcert : Pr h₁ (h₂ ∧ h) = 1) :
    Pr (h₂ → h₁) h = 1 := by
  have hneg : Pr (¬h₁) (h₂ ∧ h) = 0 := by
    have := th_13_1 h₁ (h₂ ∧ h)
    linarith
  have hconj : Pr (¬h₁ ∧ h₂) h = 0 := by
    have hx := def_X_left (¬h₁) h₂ h
    rw [hneg, zero_mul] at hx
    exact hx
  have hcompl := th_13_1 (h₂ → h₁) h
  have e : (¬(h₂ → h₁)) ↔ (¬h₁ ∧ h₂) := by tauto
  rw [ax_iii_op _ _ h e] at hcompl
  linarith

/-- **Th.(13.16.3)** 条件文の確実性から条件付き確実性へ.
(h₂⊃h₁)/h = 1 かつ h₂ が非不可能ならば h₁/h₂h = 1。
(16.1) の逆向き。整合性条件はここで初めて要る (除算の分岐消去)。

## 検証対象 (H20)
- {ax_iii_op, ax_iii_true, def_IX, def_X_left} + floor で閉じるか。
- (16.1) との対で「⊃ の確実性 ⟺ 条件付き確実性」の往復が機械化される。 -/
theorem th_13_16_3 (h₁ h₂ h : Prop) (hcert : Pr (h₂ → h₁) h = 1)
    (hcons : Pr h₂ h ≠ 0) : Pr h₁ (h₂ ∧ h) = 1 := by
  have hneg : Pr (¬(h₂ → h₁)) h = 0 := by
    have := th_13_1 (h₂ → h₁) h
    linarith
  have e : (¬(h₂ → h₁)) ↔ (¬h₁ ∧ h₂) := by tauto
  rw [ax_iii_op _ _ h e] at hneg
  have hx := def_X_left (¬h₁) h₂ h
  rw [hneg] at hx
  rcases mul_eq_zero.mp hx.symm with h0 | h0
  · have := th_13_1 h₁ (h₂ ∧ h)
    linarith
  · exact absurd h0 hcons

end Keynes

/-! ## 監査クエリ (Phase 7a 新規) -/

#check @Keynes.th_13_16_1
#check @Keynes.th_13_16_3

-- Kernel 依存. 注目点:
--   両定理: ★ H20 判定点 — {ax_iii_op, ax_iii_true, def_IX, def_X_left} + floor
#print axioms Keynes.th_13_16_1
#print axioms Keynes.th_13_16_3

-- 回帰テスト
#print axioms Keynes.th_13_1
