/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 6b
#
# 新井一成・Claude共著、2026年7月7日
# Phase 6a (積形式) → Phase 6b (Ch.13/14 系列定理の一斉掃討, +34 数値ノード)
#
# ## 本ファイルで追加したもの
#   Ch.13 (18 本): (4)(5)(6)(7)(8)(9)(10)(11)(12)(13)(13.1)(13.2)(14)(15)
#                  (18)(21)(22)(23)
#   Ch.14 (16 本): (24.3)(24.4)(24.5)(24.6)(24.7)(26)(26.1)(27)(27.1)
#                  (28)(28.1)(29)(31)(32)(37)(41.2)
#   これで数値定理は 86/100。
#
# ## 意図的省略 (理由つき、§7.14 更新予定)
#   Ch.13: (12.1)(15.1)(16)(16.1)(16.2)(16.3)(17) — DB グロスの OCR 損傷が
#     大きく原文照合なしには定式化できない、または Ax.(ii) の KEq 機構を
#     本格導入してから (Phase 7)。
#   Ch.14: (30) — グロスがトートロジーに崩れており原文照合待ち。
#          (33)(34)(35) — 関連性の推移・合成。Keynes の原主張自体が
#     Carnap 以降の反例で係争中。素朴な定式化は kernel が**反証**する
#     見込みが高く、反証監査として独立の価値があるため Phase 7 の
#     専用課題とする (今夜の掃討には不適)。
#          (39)(40) — DB に式形なし、原文照合待ち。
#          (42.2) — 任意置換の不変性。List.Perm 帰納が要る (Phase 7)。
#
# ## 読みの規約 (本ファイルで採用した操作的読み替え)
#   - 「整合 (consistent)」は「非不可能」(Pr ≠ 0) と読む (Def.V/VI 経由)。
#   - 「α/b」型 (裸の証拠) は ambient h を保持して「α/(b∧h)」と読む。
#   - (13.12) の「(α=b)」は双条件命題 (α ↔ b) をオブジェクトとして読む。
#   - (26) の h/h = 1 (自己確実性) は仮定として明示 (Keynes は (13) を引く)。
#   - (37) の「条件付き等確率」は評価非依存の定数尤度として強め読み (明記)。
#
# ## 検証したい仮説
#   H12: (13.12) 等値定理は {def_IX, ax_iii_op, ax_iii_true, ax_range_lo}
#        + floor で閉じ、DB 引用 (def_x, def_viii, ax_ivb) を全バイパス
#        → **Mode S 第 7 例候補**。Ax.(ii) も不要。
#   H13: ax_iii_ev (証拠スロット形) の load-bearing 集合は
#        {(13.21), (14.26), (14.26.1), (14.29)} — 証拠側監査の本格化。
#   H14: (13.13) 自己条件付け α/α∧h = 1 が def_X_left + ax_iii_op から
#        **定理として**出る (Keynes は 6 ノードを引くが kernel は 2 公理)。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase6b.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (Phase 6a と同一) -/

axiom Pr : Prop → Prop → ℝ

axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1
axiom ax_iii_ev (p h k : Prop) : (h ↔ k) → Pr p h = Pr p k

axiom def_IX (p q h : Prop) :
    Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h
axiom def_X_left (p q h : Prop) :
    Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h
axiom def_X_right (p q h : Prop) :
    Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h
axiom def_XI (P Q R : ℝ) (hQ : Q ≠ 0) :
    P * Q = R → P = R / Q

axiom ax_range_lo (α h : Prop) : 0 ≤ Pr α h
axiom ax_range_hi (α h : Prop) : Pr α h ≤ 1

/-! ## 再掲 (証明付き) -/

theorem th_13_1 (α h : Prop) : Pr α h + Pr (¬α) h = 1 := by
  have step := def_IX True α h
  have e1 : (True ∧ ¬α) ↔ ¬α := by tauto
  have e2 : (True ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, ax_iii_true] at step
  linarith

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

theorem pr_false (h : Prop) : Pr False h = 0 := by
  have step := def_IX False False h
  have e1 : (False ∧ ¬False) ↔ False := by tauto
  have e2 : (False ∧ False) ↔ False := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at step
  linarith

theorem pr_conj_le_left (α y h : Prop) : Pr (α ∧ y) h ≤ Pr α h := by
  have h9 := def_IX α y h
  have hlo := ax_range_lo (α ∧ ¬y) h
  linarith

theorem pr_conj_le_right (α y h : Prop) : Pr (α ∧ y) h ≤ Pr y h := by
  have h9 := def_IX y α h
  have hlo := ax_range_lo (y ∧ ¬α) h
  have e : (y ∧ α) ↔ (α ∧ y) := by tauto
  rw [ax_iii_op _ _ h e] at h9
  linarith

/-! ## Ch.13 系列 (18 本) -/

/-- **Th.(13.4)** 結合確率の上界: αb/h ≤ b/h。
DB cites: def_x, ax_ivb — kernel 経路は def_IX + 範囲原理 (Mode S 系データ点)。 -/
theorem th_13_4 (α b h : Prop) : Pr (α ∧ b) h ≤ Pr b h :=
  pr_conj_le_right α b h

/-- **Th.(13.5)** P+Q=0 → P=0 ∧ Q=0 (範囲原理下)。 -/
theorem th_13_5 (α β h k : Prop) (hsum : Pr α h + Pr β k = 0) :
    Pr α h = 0 ∧ Pr β k = 0 := by
  have l1 := ax_range_lo α h
  have l2 := ax_range_lo β k
  constructor <;> linarith

/-- **Th.(13.6)** PQ=0 → P=0 ∨ Q=0 (substrate の体論)。 -/
theorem th_13_6 (α β h k : Prop) (hmul : Pr α h * Pr β k = 0) :
    Pr α h = 0 ∨ Pr β k = 0 :=
  mul_eq_zero.mp hmul

/-- **Th.(13.7)** PQ=1 → P=1 ∧ Q=1 (範囲原理下)。 -/
theorem th_13_7 (α β h k : Prop) (hmul : Pr α h * Pr β k = 1) :
    Pr α h = 1 ∧ Pr β k = 1 := by
  have hx0 := ax_range_lo α h
  have hx1 := ax_range_hi α h
  have hy0 := ax_range_lo β k
  have hy1 := ax_range_hi β k
  have k1 : Pr α h * Pr β k ≤ Pr β k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hy0]
  have k2 : Pr α h * Pr β k ≤ Pr α h := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hy1)]
  constructor <;> linarith

/-- (13.8) 前半: 不可能命題の連言も不可能。 -/
theorem th_13_8_conj (α b h : Prop) (h0 : Pr α h = 0) : Pr (α ∧ b) h = 0 := by
  have hub := pr_conj_le_left α b h
  have hlo := ax_range_lo (α ∧ b) h
  linarith

/-- **Th.(13.8)** 不可能命題の前提追加不変性: α/h=0 ∧ b 非不可能 → α/bh=0。 -/
theorem th_13_8 (α b k : Prop) (h0 : Pr α k = 0) (hb : Pr b k ≠ 0) :
    Pr α (b ∧ k) = 0 := by
  have hconj : Pr (α ∧ b) k = 0 := th_13_8_conj α b k h0
  have hx := def_X_left α b k
  rw [hconj] at hx
  rcases mul_eq_zero.mp hx.symm with h1 | h2
  · exact h1
  · exact absurd h2 hb

/-- **Th.(13.9)** 確実命題の前提追加不変性: α/h=1 ∧ b 非不可能 → α/bh=1。 -/
theorem th_13_9 (α b k : Prop) (hcert : Pr α k = 1) (hb : Pr b k ≠ 0) :
    Pr α (b ∧ k) = 1 := by
  have hcompl := th_13_1 α k
  have hneg : Pr (¬α) k = 0 := by linarith
  have hneg2 : Pr (¬α) (b ∧ k) = 0 := th_13_8 (¬α) b k hneg hb
  have hcompl2 := th_13_1 α (b ∧ k)
  linarith

/-- **Th.(13.10)** α/h=1 → αb/h = b/h。 -/
theorem th_13_10 (α b h : Prop) (hcert : Pr α h = 1) :
    Pr (α ∧ b) h = Pr b h := by
  have hcompl := th_13_1 α h
  have hneg : Pr (¬α) h = 0 := by linarith
  have h9 := def_IX b α h
  have hz : Pr (b ∧ ¬α) h = 0 := by
    have hub := pr_conj_le_right b (¬α) h
    have hlo := ax_range_lo (b ∧ ¬α) h
    linarith
  have e : (α ∧ b) ↔ (b ∧ α) := by tauto
  rw [ax_iii_op _ _ h e]
  linarith

/-- **Th.(13.11)** αb/h=1 → α/bh=1 (ambient h 読み)。 -/
theorem th_13_11 (α b h : Prop) (h1 : Pr (α ∧ b) h = 1) :
    Pr α (b ∧ h) = 1 := by
  have hx := def_X_left α b h
  rw [h1] at hx
  exact (th_13_7 α b (b ∧ h) h hx.symm).1

/-- **Th.(13.12)** 等値定理: (α↔b)/h = 1 → α/h = b/h.
双条件命題を確率のオブジェクトとして扱い、確実な双条件の下での
確率等値を導く。

DB cites: def_x, def_viii, ax_ivb。

## 検証対象 (H12)
- kernel 経路は象限分解のみ: {def_IX, ax_iii_op, ax_iii_true, ax_range_lo}。
  Ax.(ii)・Def.VIII・Def.X をすべてバイパス → **Mode S 第 7 例候補**。 -/
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

/-- **Th.(13.13)** 同語反復: α 非不可能 → α/(α∧h) = 1.
Keynes は (iii)(12)(X)(ii)(VI)(i) の 6 ノードを引くが、kernel 経路は
def_X_left の自己適用 + ax_iii_op の 2 公理で閉じる見込み (H14)。 -/
theorem th_13_13 (α h : Prop) (hα : Pr α h ≠ 0) : Pr α (α ∧ h) = 1 := by
  have hx := def_X_left α α h
  have e : (α ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h e] at hx
  have h0 : (Pr α (α ∧ h) - 1) * Pr α h = 0 := by
    first
      | nlinarith [hx]
      | linear_combination -hx
  rcases mul_eq_zero.mp h0 with h1 | h2
  · linarith
  · exact absurd h2 hα

/-- **Th.(13.13.1)** α 非不可能 → ᾱ/(α∧h) = 0。 -/
theorem th_13_13_1 (α h : Prop) (hα : Pr α h ≠ 0) : Pr (¬α) (α ∧ h) = 0 := by
  have h13 := th_13_13 α h hα
  have hc := th_13_1 α (α ∧ h)
  linarith

/-- **Th.(13.13.2)** ᾱ 非不可能 → α/(ᾱ∧h) = 0。 -/
theorem th_13_13_2 (α h : Prop) (hα : Pr (¬α) h ≠ 0) : Pr α (¬α ∧ h) = 0 := by
  have h13 := th_13_13 (¬α) h hα
  have hc := th_13_1 α (¬α ∧ h)
  linarith

/-- **Th.(13.14)** 不可能性の対称性: α/bh=0 ∧ α 非不可能 → b/αh=0。 -/
theorem th_13_14 (α b h : Prop) (h0 : Pr α (b ∧ h) = 0) (hα : Pr α h ≠ 0) :
    Pr b (α ∧ h) = 0 := by
  have hl := def_X_left α b h
  have hr := def_X_right α b h
  rw [h0, zero_mul] at hl
  rw [hl] at hr
  rcases mul_eq_zero.mp hr.symm with h1 | h2
  · exact h1
  · exact absurd h2 hα

/-- **Th.(13.15)** h₁/h₂h=0 → h₁h₂/h=0。 -/
theorem th_13_15 (h₁ h₂ h : Prop) (h0 : Pr h₁ (h₂ ∧ h) = 0) :
    Pr (h₁ ∧ h₂) h = 0 := by
  have hx := def_X_left h₁ h₂ h
  rw [h0, zero_mul] at hx
  exact hx

/-- **Th.(13.18)** 同語反復の普遍性: α/α=1 または ᾱ/ᾱ=1 (ambient h)。
α と ¬α が同時に不可能にはなれない (補完律) ことから、古典分割で閉じる。 -/
theorem th_13_18 (α h : Prop) :
    Pr α (α ∧ h) = 1 ∨ Pr (¬α) (¬α ∧ h) = 1 := by
  by_cases hα : Pr α h = 0
  · right
    have hc := th_13_1 α h
    have h1 : Pr (¬α) h = 1 := by linarith
    have hne : Pr (¬α) h ≠ 0 := by rw [h1]; norm_num
    exact th_13_13 (¬α) h hne
  · left
    exact th_13_13 α h hα

/-- **Th.(13.21)** α/h₁h=1 ∧ α/h₂h=0 → h₁h₂/h=0.
両前提の連言は不可能。証明は二重の古典分割 + 証拠スロット同値 (ax_iii_ev)。 -/
theorem th_13_21 (α h₁ h₂ h : Prop)
    (hc1 : Pr α (h₁ ∧ h) = 1) (hc2 : Pr α (h₂ ∧ h) = 0) :
    Pr (h₁ ∧ h₂) h = 0 := by
  by_cases hd : Pr h₂ (h₁ ∧ h) = 0
  · have hr := def_X_right h₁ h₂ h
    rw [hd, zero_mul] at hr
    exact hr
  · by_cases he : Pr h₁ (h₂ ∧ h) = 0
    · have hl := def_X_left h₁ h₂ h
      rw [he, zero_mul] at hl
      exact hl
    · exfalso
      have hA := th_13_9 α h₂ (h₁ ∧ h) hc1 hd
      have hB := th_13_8 α h₁ (h₂ ∧ h) hc2 he
      have hev := ax_iii_ev α (h₂ ∧ (h₁ ∧ h)) (h₁ ∧ (h₂ ∧ h)) (by tauto)
      rw [hA, hB] at hev
      norm_num at hev

/-- **Th.(13.22)** α/h₁h=0 ∧ h₁/h=1 → α/h=0。 -/
theorem th_13_22 (α h₁ h : Prop) (h0 : Pr α (h₁ ∧ h) = 0) (hc : Pr h₁ h = 1) :
    Pr α h = 0 := by
  have hconj : Pr (α ∧ h₁) h = 0 := by
    have hx := def_X_left α h₁ h
    rw [h0, zero_mul] at hx
    exact hx
  have hcompl := th_13_1 h₁ h
  have hneg : Pr (¬h₁) h = 0 := by linarith
  have hz : Pr (α ∧ ¬h₁) h = 0 := by
    have hub := pr_conj_le_right α (¬h₁) h
    have hlo := ax_range_lo (α ∧ ¬h₁) h
    linarith
  have h9 := def_IX α h₁ h
  linarith

/-- **Th.(13.23)** b/αh=0 ∧ b/ᾱh=0 → b/h=0。 -/
theorem th_13_23 (b α h : Prop)
    (h1 : Pr b (α ∧ h) = 0) (h2 : Pr b (¬α ∧ h) = 0) : Pr b h = 0 := by
  have h9 := def_IX b α h
  have hA : Pr (b ∧ α) h = 0 := by
    have hx := def_X_left b α h
    rw [h1, zero_mul] at hx
    exact hx
  have hB : Pr (b ∧ ¬α) h = 0 := by
    have hx := def_X_left b (¬α) h
    rw [h2, zero_mul] at hx
    exact hx
  linarith

/-! ## List 機構 (Phase 5/6a から再掲) -/

def bigOr : List Prop → Prop
  | [] => False
  | p :: rest => p ∨ bigOr rest

def bigAnd : List Prop → Prop
  | [] => True
  | p :: rest => p ∧ bigAnd rest

noncomputable def sumPr : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr p h + sumPr rest h

noncomputable def overlapSum : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr (p ∧ bigOr rest) h + overlapSum rest h

noncomputable def chainProd : List Prop → Prop → ℝ
  | [], _ => 1
  | p :: rest, h => Pr p (bigAnd rest ∧ h) * chainProd rest h

noncomputable def prodPr : List Prop → Prop → ℝ
  | [], _ => 1
  | p :: rest, h => Pr p h * prodPr rest h

/-- **n 項影響係数** {α₁…αₙ} (Arai 拡張、Infl/Infl3 の一般形)。 -/
noncomputable def InflN (l : List Prop) (h : Prop) : ℝ :=
    Pr (bigAnd l) h / prodPr l h

theorem incl_excl (h : Prop) (l : List Prop) :
    Pr (bigOr l) h = sumPr l h - overlapSum l h := by
  induction l with
  | nil =>
      simp only [bigOr, sumPr, overlapSum]
      rw [pr_false]
      norm_num
  | cons p rest ih =>
      simp only [bigOr, sumPr, overlapSum]
      have h24 := th_24 p (bigOr rest) h
      linarith

theorem sumPr_zero_of_all_zero (h : Prop) : ∀ (l : List Prop),
    (∀ q ∈ l, Pr q h = 0) → sumPr l h = 0 := by
  intro l
  induction l with
  | nil => intro _; simp only [sumPr]
  | cons q rest ih =>
      intro hall
      simp only [sumPr]
      rw [hall q (by simp), ih (fun r hr => hall r (by simp [hr]))]
      norm_num

theorem pr_conj_bigOr_le (h p : Prop) : ∀ (l : List Prop),
    Pr (p ∧ bigOr l) h ≤ sumPr (l.map (fun q => p ∧ q)) h := by
  intro l
  induction l with
  | nil =>
      simp only [bigOr, List.map_nil, sumPr]
      have e : (p ∧ False) ↔ False := by tauto
      -- rw が @[refl] で 0 ≤ 0 を自動クローズする版としない版の両対応
      first
        | (rw [ax_iii_op _ _ h e, pr_false]; norm_num)
        | rw [ax_iii_op _ _ h e, pr_false]
  | cons q rest ih =>
      simp only [bigOr, List.map_cons, sumPr]
      have e : (p ∧ (q ∨ bigOr rest)) ↔ ((p ∧ q) ∨ (p ∧ bigOr rest)) := by tauto
      rw [ax_iii_op _ _ h e]
      have h24 := th_24 (p ∧ q) (p ∧ bigOr rest) h
      have hlo := ax_range_lo ((p ∧ q) ∧ (p ∧ bigOr rest)) h
      linarith

theorem overlapSum_zero_of_excl (h : Prop) : ∀ (l : List Prop),
    l.Pairwise (fun a b => Pr (a ∧ b) h = 0) → overlapSum l h = 0 := by
  intro l
  induction l with
  | nil => intro _; simp only [overlapSum]
  | cons p rest ih =>
      intro hexcl
      rw [List.pairwise_cons] at hexcl
      obtain ⟨hhead, htail⟩ := hexcl
      simp only [overlapSum]
      have hub := pr_conj_bigOr_le h p rest
      have hzero : sumPr (rest.map (fun q => p ∧ q)) h = 0 := by
        apply sumPr_zero_of_all_zero
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        exact hhead b hb
      have hlo := ax_range_lo (p ∧ bigOr rest) h
      rw [ih htail]
      linarith

/-- 連鎖律 (Phase 5 の (58) 核心の再掲、(37)(41.2) で使用)。 -/
theorem chain_rule (h : Prop) (l : List Prop) :
    Pr (bigAnd l) h = chainProd l h := by
  induction l with
  | nil =>
      simp only [bigAnd, chainProd]
      exact ax_iii_true h
  | cons p rest ih =>
      simp only [bigAnd, chainProd]
      rw [def_X_left p (bigAnd rest) h, ih]

/-! ## Ch.14 系列 (16 本) -/

/-- **Th.(14.24.3)** (α+b)/h = α/h + ᾱb/h。 -/
theorem th_14_24_3 (α b h : Prop) :
    Pr (α ∨ b) h = Pr α h + Pr (¬α ∧ b) h := by
  have h24 := th_24 α (¬α ∧ b) h
  have e1 : (α ∨ (¬α ∧ b)) ↔ (α ∨ b) := by tauto
  have e2 : (α ∧ (¬α ∧ b)) ↔ False := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, pr_false] at h24
  linarith

/-- **Th.(14.24.4)** 3 項への拡張 (順序型)。 -/
theorem th_14_24_4 (α β γ h : Prop) :
    Pr (α ∨ β ∨ γ) h = Pr α h + Pr β h + Pr γ h
      - Pr (β ∧ γ) h - Pr (α ∧ (β ∨ γ)) h := by
  have h1 := th_24 α (β ∨ γ) h
  have h2 := th_24 β γ h
  linarith

/-- **Th.(14.24.5)** n 項への一般化 = 順序型包除恒等式 (Phase 5 補題の昇格)。 -/
theorem th_14_24_5 (h : Prop) (l : List Prop) :
    Pr (bigOr l) h = sumPr l h - overlapSum l h :=
  incl_excl h l

/-- **Th.(14.24.6)** 相互排反ならば加法: (p₁+…+pₙ)/h = Σ pₖ/h。 -/
theorem th_14_24_6 (h : Prop) (l : List Prop)
    (hexcl : l.Pairwise (fun a b => Pr (a ∧ b) h = 0)) :
    Pr (bigOr l) h = sumPr l h := by
  have hie := incl_excl h l
  have hz := overlapSum_zero_of_excl h l hexcl
  linarith

/-- **Th.(14.24.7)** 相互排反かつ完全なら Σ pₖ/h = 1。 -/
theorem th_14_24_7 (h : Prop) (l : List Prop)
    (hexcl : l.Pairwise (fun a b => Pr (a ∧ b) h = 0))
    (hexh : Pr (bigOr l) h = 1) :
    sumPr l h = 1 := by
  have h6 := th_14_24_6 h l hexcl
  linarith

/-- **Th.(14.26)** 前提の群への吸収: αh/h = α/h (h/h=1 の下で).
証拠スロット同値 (ax_iii_ev) の load-bearing 例 (H13)。 -/
theorem th_14_26 (α h : Prop) (hself : Pr h h = 1) :
    Pr (α ∧ h) h = Pr α h := by
  have hx := def_X_left α h h
  rw [hself, mul_one] at hx
  have hev := ax_iii_ev α (h ∧ h) h (by tauto)
  rw [hev] at hx
  exact hx

/-- **Th.(14.26.1)** (h⊃α)/h = α/h (h/h=1 の下で)。 -/
theorem th_14_26_1 (α h : Prop) (hself : Pr h h = 1) :
    Pr (h → α) h = Pr α h := by
  have hx := def_X_left (h → α) h h
  rw [hself, mul_one] at hx
  have hev := ax_iii_ev (h → α) (h ∧ h) h (by tauto)
  rw [hev] at hx
  have hop := ax_iii_op ((h → α) ∧ h) (α ∧ h) h (by tauto)
  have h26 := th_14_26 α h hself
  linarith

/-- **Th.(14.27)** (α+b)/h=0 → α/h=0。 -/
theorem th_14_27 (α b h : Prop) (h0 : Pr (α ∨ b) h = 0) : Pr α h = 0 := by
  have h24 := th_24 α b h
  have hcb := pr_conj_le_right α b h
  have hloa := ax_range_lo α h
  linarith

/-- **Th.(14.27.1)** α/h=0 ∧ b/h=0 → (α+b)/h=0。 -/
theorem th_14_27_1 (α b h : Prop) (h0a : Pr α h = 0) (h0b : Pr b h = 0) :
    Pr (α ∨ b) h = 0 := by
  have h24 := th_24 α b h
  have hub := pr_conj_le_left α b h
  have hlo := ax_range_lo (α ∧ b) h
  linarith

/-- **Th.(14.28)** α/h=1 → (α+b)/h=1。 -/
theorem th_14_28 (α b h : Prop) (h1 : Pr α h = 1) : Pr (α ∨ b) h = 1 := by
  have h24 := th_24 α b h
  have hub := pr_conj_le_right α b h
  have hhi := ax_range_hi (α ∨ b) h
  linarith

/-- **Th.(14.28.1)** α/h=0 → (ᾱ+b)/h=1。 -/
theorem th_14_28_1 (α b h : Prop) (h0 : Pr α h = 0) : Pr (¬α ∨ b) h = 1 := by
  have hc := th_13_1 α h
  have h24 := th_24 (¬α) b h
  have hub := pr_conj_le_right (¬α) b h
  have hhi := ax_range_hi (¬α ∨ b) h
  linarith

/-- **Th.(14.29)** α/(h₁+h₂)h=1 → α/h₁h=1 ∧ α/h₂h=1 (各前提が非不可能な限り).
(13.9) の確実性伝播 + ax_iii_ev による証拠正規化。 -/
theorem th_14_29 (α h₁ h₂ h : Prop)
    (hcert : Pr α ((h₁ ∨ h₂) ∧ h) = 1)
    (hcons₁ : Pr h₁ ((h₁ ∨ h₂) ∧ h) ≠ 0)
    (hcons₂ : Pr h₂ ((h₁ ∨ h₂) ∧ h) ≠ 0) :
    Pr α (h₁ ∧ h) = 1 ∧ Pr α (h₂ ∧ h) = 1 := by
  constructor
  · have h9 := th_13_9 α h₁ ((h₁ ∨ h₂) ∧ h) hcert hcons₁
    have hev := ax_iii_ev α (h₁ ∧ ((h₁ ∨ h₂) ∧ h)) (h₁ ∧ h) (by tauto)
    rw [hev] at h9
    exact h9
  · have h9 := th_13_9 α h₂ ((h₁ ∨ h₂) ∧ h) hcert hcons₂
    have hev := ax_iii_ev α (h₂ ∧ ((h₁ ∨ h₂) ∧ h)) (h₂ ∧ h) (by tauto)
    rw [hev] at h9
    exact h9

/-- **Th.(14.31)** 独立性の対称性: α₂/α₁h=α₂/h ∧ α₂ 非不可能 → α₁/α₂h=α₁/h。 -/
theorem th_14_31 (α₁ α₂ h : Prop)
    (hirrel : Pr α₂ (α₁ ∧ h) = Pr α₂ h) (h2 : Pr α₂ h ≠ 0) :
    Pr α₁ (α₂ ∧ h) = Pr α₁ h := by
  have hl := def_X_left α₁ α₂ h
  have hr := def_X_right α₁ α₂ h
  rw [hirrel] at hr
  have h0 : (Pr α₁ (α₂ ∧ h) - Pr α₁ h) * Pr α₂ h = 0 := by
    first
      | nlinarith [hl, hr]
      | linear_combination hl - hr
  rcases mul_eq_zero.mp h0 with hz | hz
  · linarith
  · exact absurd hz h2

/-- **Th.(14.32)** 好都合な関連の対称性: α/h₁h > α/h → h₁/αh > h₁/h.
確証の対称性 (現代確証理論の基本形)。 -/
theorem th_14_32 (α h₁ h : Prop)
    (hα : 0 < Pr α h) (hh₁ : 0 < Pr h₁ h)
    (hfav : Pr α h < Pr α (h₁ ∧ h)) :
    Pr h₁ h < Pr h₁ (α ∧ h) := by
  have hl := def_X_left α h₁ h
  have hr := def_X_right α h₁ h
  have key := mul_lt_mul_of_pos_right hfav hh₁
  have hgt2 : Pr h₁ h * Pr α h < Pr h₁ (α ∧ h) * Pr α h := by
    nlinarith [key, hl, hr]
  nlinarith [hgt2, hα]

/-- **Th.(14.37)** 連鎖等確率: 各段の条件付き確率が定数 v なら連鎖積 = vⁿ.
「条件付き等確率」は評価非依存の定数尤度として強め読み (規約参照)。 -/
theorem th_14_37 (h : Prop) (v : ℝ) : ∀ (l : List Prop),
    (∀ p ∈ l, ∀ (e : Prop), Pr p e = v) → chainProd l h = v ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp only [chainProd, List.length_nil, pow_zero]
  | cons p rest ih =>
      intro hall
      simp only [chainProd, List.length_cons]
      rw [hall p (by simp) (bigAnd rest ∧ h),
          ih (fun q hq e => hall q (by simp [hq]) e)]
      ring

/-- **Th.(14.37)_full** 命題形: p₁…pₙ/h = vⁿ (連鎖律との合成)。 -/
theorem th_14_37_full (h : Prop) (v : ℝ) (l : List Prop)
    (hall : ∀ p ∈ l, ∀ (e : Prop), Pr p e = v) :
    Pr (bigAnd l) h = v ^ l.length := by
  rw [chain_rule h l]
  exact th_14_37 h v l hall

/-- **Th.(14.41.2)** n 項累積公式: α₁…αₙ/h = {α₁…αₙ}·Πₖ αₖ/h.
二項 (41)・三項 (41.1) の任意項一般化。影響係数は定義的、等式は substrate。 -/
theorem th_14_41_2 (l : List Prop) (h : Prop) (hne : prodPr l h ≠ 0) :
    Pr (bigAnd l) h = InflN l h * prodPr l h := by
  unfold InflN
  field_simp

end Keynes

/-! ## 監査クエリ (Phase 6b 新規) -/

#check @Keynes.th_13_4
#check @Keynes.th_13_12
#check @Keynes.th_13_13
#check @Keynes.th_13_18
#check @Keynes.th_13_21
#check @Keynes.th_14_24_6
#check @Keynes.th_14_26
#check @Keynes.th_14_29
#check @Keynes.th_14_31
#check @Keynes.th_14_32
#check @Keynes.th_14_37_full
#check @Keynes.th_14_41_2

-- Kernel 依存. 注目点:
--   th_13_12 : ★ H12 判定点 (Mode S 第 7 例候補: DB は def_x/def_viii/ax_ivb)
--   th_13_13 : ★ H14 判定点 (6 ノード引用 vs kernel 2 公理)
--   th_13_18 : Classical.choice の明示的消費 (古典分割)
--   th_13_21 / th_14_26 / th_14_26_1 / th_14_29 : ★ H13 判定点 (ax_iii_ev 群)
--   th_14_37_full : 連鎖律経由の帰納 (C_rec、公理增加なしと予測)
#print axioms Keynes.th_13_4
#print axioms Keynes.th_13_5
#print axioms Keynes.th_13_6
#print axioms Keynes.th_13_7
#print axioms Keynes.th_13_8
#print axioms Keynes.th_13_9
#print axioms Keynes.th_13_10
#print axioms Keynes.th_13_11
#print axioms Keynes.th_13_12
#print axioms Keynes.th_13_13
#print axioms Keynes.th_13_13_1
#print axioms Keynes.th_13_13_2
#print axioms Keynes.th_13_14
#print axioms Keynes.th_13_15
#print axioms Keynes.th_13_18
#print axioms Keynes.th_13_21
#print axioms Keynes.th_13_22
#print axioms Keynes.th_13_23
#print axioms Keynes.th_14_24_3
#print axioms Keynes.th_14_24_4
#print axioms Keynes.th_14_24_5
#print axioms Keynes.th_14_24_6
#print axioms Keynes.th_14_24_7
#print axioms Keynes.th_14_26
#print axioms Keynes.th_14_26_1
#print axioms Keynes.th_14_27
#print axioms Keynes.th_14_27_1
#print axioms Keynes.th_14_28
#print axioms Keynes.th_14_28_1
#print axioms Keynes.th_14_29
#print axioms Keynes.th_14_31
#print axioms Keynes.th_14_32
#print axioms Keynes.th_14_37
#print axioms Keynes.th_14_37_full
#print axioms Keynes.th_14_41_2

-- 回帰テスト
#print axioms Keynes.chain_rule
#print axioms Keynes.incl_excl
