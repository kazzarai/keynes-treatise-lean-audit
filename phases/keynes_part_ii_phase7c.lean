/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7c
#
# 新井一成・Claude共著、2026年7月8日
# **原著照合バッチ第 2 号**: Ch.13 の損傷 5 ノードの復元と形式化。
# 照合ソース: 佐藤隆三訳 pp.160-162 (欄外 154-156 / PDF 190-192、画像精読)。
#
# ## 照合の主発見: DB 損傷の正体は「バーの脱落」
#   DB gloss で数学的に偽・自己矛盾に見えた (16)(16.2)(15.1) は、転記時に
#   否定バー (h̄₂, h̄₁) が失われていたことが原因。原文は:
#     (16)   もし h₁/h₂=1 ならば (h₁ + h̄₂)/h = 1        [∨¬ 形]
#     (16.1) = (16) の ⊃ 書き換え (原文が明言)            [7a で検証済み]
#     (16.2) もし (h₁+h̄₂)/h=1 かつ h₂h 整合 → h₁/h₂h=1   [∨¬ 形]
#     (16.3) = (16.2) の ⊃ 書き換え (原文が明言)          [7a で検証済み]
#   つまり Phase 7a の 2 本は ⊃ 形、本ファイルの (16)(16.2) は ∨¬ 形で、
#   原文の 4 本組がここで完全に揃う。
#
# ## 本ファイルで追加したもの (DB ノード 5)
#   th_13_12_1 : 等値原理の前提強化形 (a≡b)/h=1 ∧ x 非不可能 → a/hx = b/hx
#   th_13_15_1 : (15) の逆 h₁h₂/h=0 ∧ h₂h 整合 → h₁/h₂h=0
#   th_13_16   : h₁/h₂h=1 → (h₁ ∨ ¬h₂)/h = 1
#   th_13_16_2 : (h₁ ∨ ¬h₂)/h=1 ∧ h₂h 整合 → h₁/h₂h=1
#   th_13_17   : (h₁ ⊃ (a≡b))/h=1 ∧ h₁h 整合 → a/h₁h = b/h₁h
#   → 台帳カバレッジ 93 → 98/100 (残り: (14.34) 英語原典待ち、(14.42.2) Perm)
#
# ## 検証したい仮説
#   H24: (12.1) は Ax.(ii) 不要で閉じる。原文の証明は Ax.(ii) を明示的に
#        使う (「(ii) により x/ah = x/bh」) が、kernel 経路は
#        (9) 確実性伝播 + (12) 等値定理 の合成で足りる
#        → **Mode S 第 10 例候補** (ax_ii バイパス)。
#   H25: (17) は (16.3) と (12) の純粋な合成 (原文の導出通り) で、
#        依存集合は両者の和集合に一致する。
#   H26: (16) は整合性条件なしで成立する (原文も条件を付していない —
#        h₂ が不可能でも含意は空虚に確実)。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase7c.lean
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

axiom ax_range_lo (α h : Prop) : 0 ≤ Pr α h

/-! ## 再掲 (証明付き: 13.1, 連言上界, 13.8, 13.9, 13.12, 13.16.3) -/

theorem th_13_1 (α h : Prop) : Pr α h + Pr (¬α) h = 1 := by
  have step := def_IX True α h
  have e1 : (True ∧ ¬α) ↔ ¬α := by tauto
  have e2 : (True ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, ax_iii_true] at step
  linarith

theorem pr_conj_le_right (α y h : Prop) : Pr (α ∧ y) h ≤ Pr y h := by
  have h9 := def_IX y α h
  have hlo := ax_range_lo (y ∧ ¬α) h
  have e : (y ∧ α) ↔ (α ∧ y) := by tauto
  rw [ax_iii_op _ _ h e] at h9
  linarith

theorem th_13_8_conj (α b h : Prop) (h0 : Pr α h = 0) : Pr (α ∧ b) h = 0 := by
  have h9 := def_IX α b h
  have hlo1 := ax_range_lo (α ∧ ¬b) h
  have hlo2 := ax_range_lo (α ∧ b) h
  linarith

theorem th_13_8 (α b k : Prop) (h0 : Pr α k = 0) (hb : Pr b k ≠ 0) :
    Pr α (b ∧ k) = 0 := by
  have hconj : Pr (α ∧ b) k = 0 := th_13_8_conj α b k h0
  have hx := def_X_left α b k
  rw [hconj] at hx
  rcases mul_eq_zero.mp hx.symm with h1 | h2
  · exact h1
  · exact absurd h2 hb

theorem th_13_9 (α b k : Prop) (hcert : Pr α k = 1) (hb : Pr b k ≠ 0) :
    Pr α (b ∧ k) = 1 := by
  have hcompl := th_13_1 α k
  have hneg : Pr (¬α) k = 0 := by linarith
  have hneg2 : Pr (¬α) (b ∧ k) = 0 := th_13_8 (¬α) b k hneg hb
  have hcompl2 := th_13_1 α (b ∧ k)
  linarith

theorem th_13_12 (α b h : Prop) (hcert : Pr (α ↔ b) h = 1) :
    Pr α h = Pr b h := by
  have hcompl := th_13_1 (α ↔ b) h
  have hneg : Pr (¬(α ↔ b)) h = 0 := by linarith
  have hq1 := def_IX α (α ↔ b) h
  have hq2 := def_IX b (α ↔ b) h
  have hz1 : Pr (α ∧ ¬(α ↔ b)) h = 0 := by
    have hub := pr_conj_le_right α (¬(α ↔ b)) h
    have hlo := ax_range_lo (α ∧ ¬(α ↔ b)) h
    linarith
  have hz2 : Pr (b ∧ ¬(α ↔ b)) h = 0 := by
    have hub := pr_conj_le_right b (¬(α ↔ b)) h
    have hlo := ax_range_lo (b ∧ ¬(α ↔ b)) h
    linarith
  have e : (α ∧ (α ↔ b)) ↔ (b ∧ (α ↔ b)) := by tauto
  have he := ax_iii_op _ _ h e
  linarith

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

/-! ## Phase 7c 新規 (照合済み 5 本) -/

/-- **Th.(13.15.1)** (15) の逆 (佐藤訳 p.161).
「もし h₁h₂/h=0 であり、かつ h₂h が不整合でないならば、h₁/h₂h = 0。
これは (15) の逆であり、X と (6) から導かれる。」
DB gloss は前提が壊れていた (h₂/h=0 と誤転記)。 -/
theorem th_13_15_1 (h₁ h₂ h : Prop)
    (h0 : Pr (h₁ ∧ h₂) h = 0) (hcons : Pr h₂ h ≠ 0) :
    Pr h₁ (h₂ ∧ h) = 0 := by
  have hx := def_X_left h₁ h₂ h
  rw [h0] at hx
  rcases mul_eq_zero.mp hx.symm with hz | hz
  · exact hz
  · exact absurd hz hcons

/-- **Th.(13.12.1)** 等値原理の前提強化形 (佐藤訳 p.160).
「もし (a≡b)/h=1 であり、かつ hx が不整合でないならば、a/hx = b/hx。」
原文注: 「これは等値の原理である。この原理および公理 (ii) により、…
b に a を代入することができ、その逆もできる。」

## 検証対象 (H24)
原文の証明は Ax.(ii) を明示使用 (「(ii) により x/ah = x/bh」) するが、
本証明は (9) 確実性伝播 + (12) 等値定理の合成で閉じる。Ax.(ii) が
バイパスされれば **Mode S 第 10 例**。 -/
theorem th_13_12_1 (a b x h : Prop)
    (hcert : Pr (a ↔ b) h = 1) (hx : Pr x h ≠ 0) :
    Pr a (x ∧ h) = Pr b (x ∧ h) := by
  have hstrong : Pr (a ↔ b) (x ∧ h) = 1 := th_13_9 (a ↔ b) x h hcert hx
  exact th_13_12 a b (x ∧ h) hstrong

/-- **Th.(13.16)** 条件付き確実性から選言確実性へ (佐藤訳 p.162).
「もし h₁/h₂=1 ならば、(h₁ + h̄₂)/h = 1。」
**DB gloss は h̄₂ のバーを落としており、そのままでは偽だった。**
原文に整合性条件はない (h₂ が不可能でも空虚に成立 — H26)。 -/
theorem th_13_16 (h₁ h₂ h : Prop) (hcert : Pr h₁ (h₂ ∧ h) = 1) :
    Pr (h₁ ∨ ¬h₂) h = 1 := by
  have hneg : Pr (¬h₁) (h₂ ∧ h) = 0 := by
    have := th_13_1 h₁ (h₂ ∧ h)
    linarith
  have hconj : Pr ((¬h₁) ∧ h₂) h = 0 := by
    have hx := def_X_left (¬h₁) h₂ h
    rw [hneg, zero_mul] at hx
    exact hx
  have hcompl := th_13_1 (h₁ ∨ ¬h₂) h
  have e : (¬(h₁ ∨ ¬h₂)) ↔ ((¬h₁) ∧ h₂) := by tauto
  rw [ax_iii_op _ _ h e] at hcompl
  linarith

/-- **Th.(13.16.2)** 選言確実性から条件付き確実性へ (佐藤訳 p.162).
「もし (h₁+h̄₂)/h=1 であり、かつ h₂h が不整合でないならば、h₁/h₂h=1。
これは (14) の逆である。」原文の導出 ((16) 型分解 → (15.1) → (1.4)) を移植。 -/
theorem th_13_16_2 (h₁ h₂ h : Prop)
    (hcert : Pr (h₁ ∨ ¬h₂) h = 1) (hcons : Pr h₂ h ≠ 0) :
    Pr h₁ (h₂ ∧ h) = 1 := by
  have hcompl := th_13_1 (h₁ ∨ ¬h₂) h
  have e : (¬(h₁ ∨ ¬h₂)) ↔ ((¬h₁) ∧ h₂) := by tauto
  rw [ax_iii_op _ _ h e] at hcompl
  have hconj : Pr ((¬h₁) ∧ h₂) h = 0 := by linarith
  have hneg : Pr (¬h₁) (h₂ ∧ h) = 0 := th_13_15_1 (¬h₁) h₂ h hconj hcons
  have := th_13_1 h₁ (h₂ ∧ h)
  linarith

/-- **Th.(13.17)** 条件付き等値 (佐藤訳 p.162).
「もし (h₁⊃: a≡b)/h=1 であり、かつ h₁h が不整合でないならば、
a/h₁h = b/h₁h。これは (16.3) と (12) から導かれる。」
原文の導出をそのまま合成 (H25)。 -/
theorem th_13_17 (a b h₁ h : Prop)
    (hcert : Pr (h₁ → (a ↔ b)) h = 1) (hcons : Pr h₁ h ≠ 0) :
    Pr a (h₁ ∧ h) = Pr b (h₁ ∧ h) := by
  have h163 : Pr (a ↔ b) (h₁ ∧ h) = 1 := th_13_16_3 (a ↔ b) h₁ h hcert hcons
  exact th_13_12 a b (h₁ ∧ h) h163

end Keynes

/-! ## 監査クエリ (Phase 7c 新規) -/

#check @Keynes.th_13_12_1
#check @Keynes.th_13_15_1
#check @Keynes.th_13_16
#check @Keynes.th_13_16_2
#check @Keynes.th_13_17

-- Kernel 依存. 注目点:
--   th_13_12_1 : ★ H24 判定点 — Ax.(ii) 不在で閉じるか (Mode S 第 10 例候補)
--   th_13_16   : ★ H26 — 整合性条件なし・範囲原理なしで閉じるか
--   th_13_17   : ★ H25 — (16.3) と (12) の依存集合の和に一致するか
#print axioms Keynes.th_13_12_1
#print axioms Keynes.th_13_15_1
#print axioms Keynes.th_13_16
#print axioms Keynes.th_13_16_2
#print axioms Keynes.th_13_17

-- 回帰テスト
#print axioms Keynes.th_13_9
#print axioms Keynes.th_13_12
#print axioms Keynes.th_13_16_3
