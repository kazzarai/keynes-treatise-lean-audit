/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 6a
#
# 新井一成・Claude共著、2026年7月7日
# Phase 5 (アンカー15/15) → Phase 6a (積形式・相互独立性・全確率公式, +9 数値ノード)
#
# ## 本ファイルで追加したもの
#   新公理 (操作形):
#     ax_iii_ev : Ax.(iii) の**証拠スロット側**操作形 (h ↔ k → p/h = p/k)。
#         従来の ax_iii_op は命題スロット側のみだった。(46.1) 型の特殊化は
#         証拠側の同値代入を要求するため、ここで初めて分離・顕在化する。
#         命題側と証拠側の区別自体が新しい監査データ点 (Finding 候補)。
#         整合性: 縮退モデル (Pr T _=1, Pr F _=0) は証拠に依存しないので充足 ✓
#   新定義 (Arai 拡張):
#     prodComplement : Π(1−eₖ)     (Laplace/Boole の独立余事象積)
#     pairProdSum    : Σ_{j<k} eⱼeₖ (2次補正項)
#     weightSum      : Σₖ qₖeₖ      (Bayes 正規化分母)
#     NegChainIndep  : 連鎖型負独立性 (各原因の否定が後続否定連言に無関連)
#   Theorems (数値ノード 9):
#     th_14_25   : 全確率公式 (相互排反完全系)  ★Ch.14 の中堅、46.2 の前提
#     th_14_46_1 : (46) の特殊化 (証拠反復の collapse) — ax_iii_ev 初使用
#     th_14_46_2 : n 仮説 Bayes 正規化 (排反完全系での事後確率)
#     th_14_47_1 : (47) 凝縮形 (事後 × 正規化子 = 重み)
#     th_14_49_1 : 証拠累積の一般化 (尤度 > 混合平均 → 確証)
#     th_17_57_1 : n 原因独立下の下界 π ≥ Σeₖpₖ − Σ_{j<k}eⱼeₖ ((56.5) の n 項化)
#     th_17_57_3 : 独立性下の両側範囲
#     th_17_57_4 : 諸原因十分+独立 → π = 1 − Π(1−eₖ)
#     th_17_57_5 : 小事前確率近似の両側誤差限界 (≈ の厳密化)
#   これで Ch.17 は 17/17 (完全制覇)、Ch.14 は 17→22/47。
#
# ## 相互独立性の設計判断 (Phase 6 の主要判断、§7 に記載予定)
#   Keynes の「原因知識の独立」は 3 つの強さで現れる:
#     (a) 対独立 (pairwise): List.Pairwise で表現 — (57.1)(57.3)(57.5) 用
#     (b) 連鎖型負独立 (NegChainIndep): (57.4) の Π(1−eₖ) 用
#     (c) 対排反 (pairwise exclusive): (25)(46.2) の分割用
#   完全相互独立 (全部分集合) はどの定理にも不要だった — それ自体が発見:
#   Keynes の Ch.17 独立性は常に「隣接する結合の分解」までしか使わない。
#
# ## 検証したい仮説
#   H9 : ax_iii_ev は (46.1) で初めて surface し、命題側 ax_iii_op と独立に
#        カウントされる (証拠スロット監査の開始点)。
#   H10: (25) 全確率公式の kernel 集合は {ax_iii_op, def_IX, def_X_left,
#        ax_iii_true, 範囲原理} + floor 以内 (Def.X 右形不要) と予測。
#   H11: (57.4) は {ax_iii_op, ax_iii_true, def_IX?, def_X_left, def_X_right}
#        + floor。NegChainIndep 経由で範囲原理は不要と予測。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase6a.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (Phase 5 から継承 + 証拠側操作形) -/

axiom Pr : Prop → Prop → ℝ

axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1

/-- **Ax.(iii) 証拠スロット側操作形** (Phase 6a 新規)。
Keynes の Ax.(iii) 族は「α/h=1 → αh=h」(証拠群の同一視) を含み、Def.VII の
「群」概念は証拠が論理的同値で閉じることを前提する。従来の ax_iii_op は
命題スロットのみを扱っており、(46.1) 型の証拠反復 collapse はこの証拠側
形式なしには書けない。命題側との分離自体が監査上の新データ点。
縮退への影響: 縮退モデルは証拠非依存なので整合性は保たれる (系は無矛盾のまま)。 -/
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

/-! ## 再掲 (Phase 2/4/5 から、証明付き) -/

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

theorem th_14_38_full (α β h : Prop) (hβ : Pr β h ≠ 0) :
    Pr α (β ∧ h) = Pr β (α ∧ h) * Pr α h / Pr β h := by
  have h_left  : Pr (α ∧ β) h = Pr α (β ∧ h) * Pr β h := def_X_left α β h
  have h_right : Pr (α ∧ β) h = Pr β (α ∧ h) * Pr α h := def_X_right α β h
  have heq : Pr α (β ∧ h) * Pr β h = Pr β (α ∧ h) * Pr α h := by
    rw [← h_left, h_right]
  exact def_XI (Pr α (β ∧ h)) (Pr β h) (Pr β (α ∧ h) * Pr α h) hβ heq

def bigOr : List Prop → Prop
  | [] => False
  | p :: rest => p ∨ bigOr rest

noncomputable def sumPr : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr p h + sumPr rest h

noncomputable def overlapSum : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr (p ∧ bigOr rest) h + overlapSum rest h

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

theorem bigOr_map_and (E : Prop) (l : List Prop) :
    bigOr (l.map (fun p => p ∧ E)) ↔ (bigOr l ∧ E) := by
  induction l with
  | nil =>
      simp only [List.map_nil, bigOr]
      tauto
  | cons p rest ih =>
      simp only [List.map_cons, bigOr]
      rw [ih]
      tauto

theorem th_17_57 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) (E ∧ h) = 1) :
    Pr E h = sumPr (causes.map (fun p => p ∧ E)) h
             - overlapSum (causes.map (fun p => p ∧ E)) h := by
  have key : Pr ((bigOr causes) ∧ E) h = Pr (bigOr causes) (E ∧ h) * Pr E h :=
    def_X_left (bigOr causes) E h
  rw [hexh, one_mul] at key
  have hre : Pr (bigOr (causes.map (fun p => p ∧ E))) h
      = Pr ((bigOr causes) ∧ E) h :=
    ax_iii_op _ _ h (bigOr_map_and E causes)
  have hie := incl_excl h (causes.map (fun p => p ∧ E))
  rw [hre, key] at hie
  exact hie

/-! ## 新定義 (Arai 拡張) -/

/-- Π(1−eₖ): 独立余事象積。Laplace/Boole の「どの原因も働かない」確率。 -/
noncomputable def prodComplement : List Prop → Prop → ℝ
  | [], _ => 1
  | p :: rest, h => (1 - Pr p h) * prodComplement rest h

/-- Σ_{j<k} eⱼeₖ: 2 次補正項 (Bonferroni 第 2 項)。 -/
noncomputable def pairProdSum : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr p h * sumPr rest h + pairProdSum rest h

/-- Σₖ qₖeₖ: 尤度重み付き事前和 (n 仮説 Bayes の正規化分母)。 -/
noncomputable def weightSum : List Prop → Prop → Prop → ℝ
  | [], _, _ => 0
  | a :: rest, E, h => Pr E (a ∧ h) * Pr a h + weightSum rest E h

/-- 連鎖型負独立性: 各原因の否定が、後続原因の否定連言に無関連。
完全相互独立より弱く、Π(1−eₖ) の導出にはこれで十分 (設計判断)。 -/
def NegChainIndep : List Prop → Prop → Prop
  | [], _ => True
  | p :: rest, h => (Pr (¬p) ((¬ bigOr rest) ∧ h) = Pr (¬p) h) ∧ NegChainIndep rest h

/-! ## 補助補題 (Arai) -/

/-- 全要素ゼロなら和はゼロ。 -/
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

/-- 頭要素との対独立の下で Σ P(a∧qⱼ) = Pa · Σ Pqⱼ。 -/
theorem sumPr_map_and_head (h a : Prop) : ∀ (l : List Prop),
    (∀ b ∈ l, Pr (a ∧ b) h = Pr a h * Pr b h) →
    sumPr (l.map (fun q => a ∧ q)) h = Pr a h * sumPr l h := by
  intro l
  induction l with
  | nil => intro _; simp only [List.map_nil, sumPr]; ring
  | cons b rest ih =>
      intro hall
      simp only [List.map_cons, sumPr]
      rw [hall b (by simp), ih (fun c hc => hall c (by simp [hc]))]
      ring

/-- 連言対選言の union bound: P(p ∧ (q₁∨…∨qₙ)) ≤ Σ P(p∧qⱼ)。 -/
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

/-- 重なり項の単調性: ((a∧E) ∧ bigOr[map ∧E]) ≤ (a ∧ bigOr)。 -/
theorem overlap_term_mono (E h a : Prop) (rest : List Prop) :
    Pr ((a ∧ E) ∧ bigOr (rest.map (fun b => b ∧ E))) h
      ≤ Pr (a ∧ bigOr rest) h := by
  have e1 : ((a ∧ E) ∧ bigOr (rest.map (fun b => b ∧ E)))
      ↔ ((a ∧ bigOr rest) ∧ E) := by
    rw [bigOr_map_and]
    tauto
  rw [ax_iii_op _ _ h e1]
  exact pr_conj_le_left (a ∧ bigOr rest) E h

theorem overlapSum_nonneg (h : Prop) : ∀ (l : List Prop), 0 ≤ overlapSum l h := by
  intro l
  induction l with
  | nil => norm_num [overlapSum]
  | cons p rest ih =>
      simp only [overlapSum]
      have := ax_range_lo (p ∧ bigOr rest) h
      linarith

/-- Σ P(αₖ∧E)/h = weightSum (def_X_right の一斉適用)。 -/
theorem sumPr_map_and_eq_weightSum (E h : Prop) : ∀ (l : List Prop),
    sumPr (l.map (fun a => a ∧ E)) h = weightSum l E h := by
  intro l
  induction l with
  | nil => simp only [List.map_nil, sumPr, weightSum]
  | cons a rest ih =>
      simp only [List.map_cons, sumPr, weightSum]
      rw [def_X_right a E h, ih]

/-- 対排反の下で mapped overlapSum は消える。 -/
theorem overlapSum_map_and_zero_of_excl (E h : Prop) : ∀ (l : List Prop),
    l.Pairwise (fun a b => Pr (a ∧ b) h = 0) →
    overlapSum (l.map (fun a => a ∧ E)) h = 0 := by
  intro l
  induction l with
  | nil => intro _; simp only [List.map_nil, overlapSum]
  | cons a rest ih =>
      intro hexcl
      rw [List.pairwise_cons] at hexcl
      obtain ⟨hhead, htail⟩ := hexcl
      simp only [List.map_cons, overlapSum]
      have hmono := overlap_term_mono E h a rest
      have hub := pr_conj_bigOr_le h a rest
      have hzero : sumPr (rest.map (fun q => a ∧ q)) h = 0 := by
        apply sumPr_zero_of_all_zero
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        exact hhead b hb
      have hlo := ax_range_lo ((a ∧ E) ∧ bigOr (rest.map (fun b => b ∧ E))) h
      have htailz := ih htail
      rw [htailz]
      linarith

/-- 対独立の下で mapped overlapSum ≤ Σ_{j<k} eⱼeₖ。 -/
theorem overlapSum_map_le_pairProdSum (E h : Prop) : ∀ (l : List Prop),
    l.Pairwise (fun a b => Pr (a ∧ b) h = Pr a h * Pr b h) →
    overlapSum (l.map (fun a => a ∧ E)) h ≤ pairProdSum l h := by
  intro l
  induction l with
  | nil =>
      intro _
      simp only [List.map_nil, overlapSum, pairProdSum]
      norm_num
  | cons a rest ih =>
      intro hind
      rw [List.pairwise_cons] at hind
      obtain ⟨hhead, htail⟩ := hind
      simp only [List.map_cons, overlapSum, pairProdSum]
      have hmono := overlap_term_mono E h a rest
      have hub := pr_conj_bigOr_le h a rest
      have hsum := sumPr_map_and_head h a rest hhead
      have htaille := ih htail
      linarith

/-- 連鎖型負独立の下で P(¬(α₁∨…∨αₙ)) = Π(1−eₖ)。(57.4) の核心。 -/
theorem prodComplement_eq (h : Prop) : ∀ (l : List Prop), NegChainIndep l h →
    Pr (¬ bigOr l) h = prodComplement l h := by
  intro l
  induction l with
  | nil =>
      intro _
      simp only [bigOr, prodComplement]
      have e : (¬ False) ↔ True := by tauto
      rw [ax_iii_op _ _ h e, ax_iii_true]
  | cons p rest ih =>
      intro hind
      simp only [NegChainIndep] at hind
      obtain ⟨hhead, htail⟩ := hind
      simp only [bigOr, prodComplement]
      have e : (¬ (p ∨ bigOr rest)) ↔ (¬p ∧ ¬ bigOr rest) := by tauto
      rw [ax_iii_op _ _ h e, def_X_left (¬p) (¬ bigOr rest) h, hhead, ih htail]
      have hc := th_13_1 p h
      have hval : Pr (¬p) h = 1 - Pr p h := by linarith
      rw [hval]

/-! ## 数値ノード (9 本) -/

/-- **Th.(14.25)** 全確率公式 (相互排反完全系).
排反 (対ごとに αᵢαⱼ/h = 0) かつ完全 ((α₁+…+αₙ)/h = 1) な仮説系に対し、
E/h = Σₖ E/αₖh · αₖ/h。

Keynes Prolog DB: cites(th14_25, th13_9), cites(th14_25, th14_24_6),
cites(th14_25, def_x), cites(th14_25, th13_8).

## 検証対象 (H10)
- kernel 集合は {ax_iii_op, ax_iii_true, def_IX, def_X_left, def_X_right, 範囲原理}
  以内と予測 (右形は weightSum への分解 def_X_right 経由で入る)。
- DB 引用の th13_9 / th13_8 (確実性・不可能性の前提伝播) は kernel 経路では
  排反消滅補題に吸収される見込み → Mode S 系データ点。 -/
theorem th_14_25 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) h = 1)
    (hexcl : causes.Pairwise (fun a b => Pr (a ∧ b) h = 0)) :
    Pr E h = weightSum causes E h := by
  have hX1 : Pr (¬ bigOr causes) h = 0 := by
    have := th_13_1 (bigOr causes) h
    linarith
  have hng : Pr (E ∧ ¬ bigOr causes) h = 0 := by
    have hub := pr_conj_le_right E (¬ bigOr causes) h
    have hlo := ax_range_lo (E ∧ ¬ bigOr causes) h
    linarith
  have h9 := def_IX E (bigOr causes) h
  have e1 : (bigOr (causes.map (fun a => a ∧ E))) ↔ (E ∧ bigOr causes) := by
    rw [bigOr_map_and]
    tauto
  have hre : Pr (bigOr (causes.map (fun a => a ∧ E))) h
      = Pr (E ∧ bigOr causes) h := ax_iii_op _ _ h e1
  have hie := incl_excl h (causes.map (fun a => a ∧ E))
  rw [hre, sumPr_map_and_eq_weightSum E h causes,
      overlapSum_map_and_zero_of_excl E h causes hexcl] at hie
  linarith

/-- **Th.(14.25.1)** 全確率公式の整理形 (非加重形).
E/h = Σₖ (αₖ∧E)/h。(25) の weightSum 形の手前にある素朴和形。

Keynes Prolog DB: cites(th14_25_1, th14_25). -/
theorem th_14_25_1 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) h = 1)
    (hexcl : causes.Pairwise (fun a b => Pr (a ∧ b) h = 0)) :
    Pr E h = sumPr (causes.map (fun a => a ∧ E)) h := by
  rw [sumPr_map_and_eq_weightSum E h causes]
  exact th_14_25 causes E h hexh hexcl

/-- **Th.(14.46.1)** (46) の特殊化: 証拠反復の collapse.
β∧β を証拠とする Bayes は β を証拠とする Bayes に等しい。

Keynes Prolog DB: cites(th14_46_1, th14_46).

## 検証対象 (H9)
- **ax_iii_ev (証拠スロット形) の初 surface**。命題スロット形 ax_iii_op は
  この定理では不要。Ax.(iii) の二面性が kernel レベルで分離される。
- DB 引用の th14_46 は kernel 経路では th_14_38_full 直行でバイパス
  ((46) 自体が (38) の代入例のため自明な短絡)。 -/
theorem th_14_46_1 (α β h : Prop) (hβ : Pr β h ≠ 0) :
    Pr α ((β ∧ β) ∧ h) = Pr β (α ∧ h) * Pr α h / Pr β h := by
  have e : ((β ∧ β) ∧ h) ↔ (β ∧ h) := by tauto
  rw [ax_iii_ev α _ _ e]
  exact th_14_38_full α β h hβ

/-- **Th.(14.46.2)** n 仮説 Bayes 正規化 (相互排反完全系).
排反完全な仮説系 {αₖ} に対し、αₖ/Eh = qₖeₖ / Σⱼ qⱼeⱼ。
(48) の 2 仮説形を任意の分割に一般化する。分母は全確率公式 (25)。

Keynes Prolog DB: cites(th14_46_2, th14_24_7), cites(th14_46_2, th14_46). -/
theorem th_14_46_2 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) h = 1)
    (hexcl : causes.Pairwise (fun a b => Pr (a ∧ b) h = 0))
    (hE : Pr E h ≠ 0) (α : Prop) (_hmem : α ∈ causes) :
    Pr α (E ∧ h) = Pr E (α ∧ h) * Pr α h / weightSum causes E h := by
  have h25 := th_14_25 causes E h hexh hexcl
  have h38 := th_14_38_full α E h hE
  rw [h38, h25]

/-- **Th.(14.47.1)** (47) の凝縮形: 事後確率 × 正規化子 = 尤度重み.
除算仮定を避けた cross-multiplied 形。

Keynes Prolog DB: cites(th14_47_1, th14_47). -/
theorem th_14_47_1 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) h = 1)
    (hexcl : causes.Pairwise (fun a b => Pr (a ∧ b) h = 0))
    (hE : Pr E h ≠ 0) (α : Prop) (hmem : α ∈ causes)
    (hW : weightSum causes E h ≠ 0) :
    Pr α (E ∧ h) * weightSum causes E h = Pr E (α ∧ h) * Pr α h := by
  rw [th_14_46_2 causes E h hexh hexcl hE α hmem]
  field_simp

/-- **Th.(14.49.1)** 証拠累積の一般化 (相互排反完全系).
仮説 αₖ の尤度が混合平均 (= 正規化子 W) を超えるとき、E の獲得は αₖ を
確証する: αₖ/Eh > αₖ/h。「尤度 > 平均 ⟺ 確証」の片方向。

Keynes Prolog DB: cites(th14_49_1, th14_46_2). -/
theorem th_14_49_1 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) h = 1)
    (hexcl : causes.Pairwise (fun a b => Pr (a ∧ b) h = 0))
    (hE : Pr E h ≠ 0) (α : Prop) (hmem : α ∈ causes)
    (hα : 0 < Pr α h) (hW : 0 < weightSum causes E h)
    (hlik : weightSum causes E h < Pr E (α ∧ h)) :
    Pr α h < Pr α (E ∧ h) := by
  have hnum : 0 < Pr E (α ∧ h) * Pr α h - Pr α h * weightSum causes E h := by
    nlinarith [mul_pos hα (sub_pos.mpr hlik)]
  have hfrac : 0 < (Pr E (α ∧ h) * Pr α h - Pr α h * weightSum causes E h)
      / weightSum causes E h := div_pos hnum hW
  have hWne : weightSum causes E h ≠ 0 := ne_of_gt hW
  have heq : Pr E (α ∧ h) * Pr α h / weightSum causes E h - Pr α h
      = (Pr E (α ∧ h) * Pr α h - Pr α h * weightSum causes E h)
        / weightSum causes E h := by
    first
      | (field_simp; ring)
      | field_simp
  rw [← heq] at hfrac
  rw [th_14_46_2 causes E h hexh hexcl hE α hmem]
  linarith

/-- **Th.(17.57.1)** n 原因・対独立下の下界: π ≥ Σₖ eₖpₖ − Σ_{j<k} eⱼeₖ.
(56.5) の n 項一般化 (Bonferroni 第 2 次)。DB 原文の式は OCR 損傷のため、
「独立性下で重なり補正が対積和で抑えられる」という数学的核心を採録。

Keynes Prolog DB: cites(th17_57_1, th17_57). -/
theorem th_17_57_1 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) (E ∧ h) = 1)
    (hind : causes.Pairwise (fun a b => Pr (a ∧ b) h = Pr a h * Pr b h)) :
    sumPr (causes.map (fun a => a ∧ E)) h - pairProdSum causes h ≤ Pr E h := by
  have h57 := th_17_57 causes E h hexh
  have hle := overlapSum_map_le_pairProdSum E h causes hind
  linarith

/-- **Th.(17.57.3)** 独立性下の両側範囲.
下界は (57.1)、上界は任意の原因メンバーによる 1−eₖ(1−pₖ) (この上界は
独立性も網羅性も不要 — それ自体が監査データ点)。

Keynes Prolog DB: cites(th17_57_3, th17_57_1). -/
theorem th_17_57_3 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) (E ∧ h) = 1)
    (hind : causes.Pairwise (fun a b => Pr (a ∧ b) h = Pr a h * Pr b h))
    (α : Prop) (_hmem : α ∈ causes) :
    (sumPr (causes.map (fun a => a ∧ E)) h - pairProdSum causes h ≤ Pr E h) ∧
    (Pr E h ≤ 1 - Pr α h + Pr E (α ∧ h) * Pr α h) := by
  constructor
  · exact th_17_57_1 causes E h hexh hind
  · have hq := def_IX α E h
    have d1 : Pr (α ∧ E) h = Pr E (α ∧ h) * Pr α h := def_X_right α E h
    have disj := th_24 E (α ∧ ¬E) h
    have ef : (E ∧ (α ∧ ¬E)) ↔ False := by tauto
    rw [ax_iii_op _ _ h ef, pr_false] at disj
    have hub := ax_range_hi (E ∨ (α ∧ ¬E)) h
    linarith

/-- **Th.(17.57.4)** 諸原因十分かつ独立: π = 1 − Π(1−eₖ).
各原因が働けば E は確実 (十分性: E/(α₁∨…∨αₙ)h = 1)、原因は E を通じて
のみ (網羅性)、原因の否定は連鎖型負独立。このとき π は
「どの原因も働かない確率」の補数に一致する。

Keynes Prolog DB: cites(th17_57_4, th17_57_1).

## 検証対象 (H11)
- NegChainIndep 経由の Π(1−eₖ) 導出で、完全相互独立が不要なこと。 -/
theorem th_17_57_4 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) (E ∧ h) = 1)
    (hsuff : Pr E ((bigOr causes) ∧ h) = 1)
    (hind : NegChainIndep causes h) :
    Pr E h = 1 - prodComplement causes h := by
  have key1 : Pr ((bigOr causes) ∧ E) h = Pr (bigOr causes) (E ∧ h) * Pr E h :=
    def_X_left (bigOr causes) E h
  rw [hexh, one_mul] at key1
  have key2 : Pr ((bigOr causes) ∧ E) h
      = Pr E ((bigOr causes) ∧ h) * Pr (bigOr causes) h :=
    def_X_right (bigOr causes) E h
  rw [hsuff, one_mul] at key2
  have hcompl := th_13_1 (bigOr causes) h
  have hprod := prodComplement_eq h causes hind
  linarith

/-- **Th.(17.57.5)** 小事前確率近似の厳密化: 両側誤差限界.
Σₖ eₖpₖ − Σ_{j<k} eⱼeₖ ≤ π ≤ Σₖ eₖpₖ。事前確率が小さいとき補正項は
2 次の小ささなので π ≈ Σeₖpₖ — Keynes の「≈」を区間で置き換える。

Keynes Prolog DB: cites(th17_57_5, th17_57). -/
theorem th_17_57_5 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) (E ∧ h) = 1)
    (hind : causes.Pairwise (fun a b => Pr (a ∧ b) h = Pr a h * Pr b h)) :
    (sumPr (causes.map (fun a => a ∧ E)) h - pairProdSum causes h ≤ Pr E h) ∧
    (Pr E h ≤ sumPr (causes.map (fun a => a ∧ E)) h) := by
  have h57 := th_17_57 causes E h hexh
  have hle := overlapSum_map_le_pairProdSum E h causes hind
  have hnn := overlapSum_nonneg h (causes.map (fun a => a ∧ E))
  constructor <;> linarith

end Keynes

/-! ## 監査クエリ (Phase 6a 新規) -/

#check @Keynes.th_14_25
#check @Keynes.th_14_25_1
#check @Keynes.th_14_46_1
#check @Keynes.th_14_46_2
#check @Keynes.th_14_47_1
#check @Keynes.th_14_49_1
#check @Keynes.th_17_57_1
#check @Keynes.th_17_57_3
#check @Keynes.th_17_57_4
#check @Keynes.th_17_57_5

-- Kernel 依存. 注目点:
--   th_14_25    : ★ H10 判定点 (全確率公式の公理集合)
--   th_14_46_1  : ★ H9 判定点 (ax_iii_ev の初 surface、ax_iii_op 不在か)
--   th_14_46_2  : (25) + 38_full の合成集合
--   th_14_49_1  : 46_2 + 算術のみ (新規 surface なしと予測)
--   th_17_57_4  : ★ H11 判定点 (範囲原理不要と予測)
#print axioms Keynes.th_14_25
#print axioms Keynes.th_14_25_1
#print axioms Keynes.th_14_46_1
#print axioms Keynes.th_14_46_2
#print axioms Keynes.th_14_47_1
#print axioms Keynes.th_14_49_1
#print axioms Keynes.th_17_57_1
#print axioms Keynes.th_17_57_3
#print axioms Keynes.th_17_57_4
#print axioms Keynes.th_17_57_5

-- 回帰テスト
#print axioms Keynes.th_17_57
#print axioms Keynes.prodComplement_eq
#print axioms Keynes.overlapSum_map_le_pairProdSum
#print axioms Keynes.overlapSum_map_and_zero_of_excl
