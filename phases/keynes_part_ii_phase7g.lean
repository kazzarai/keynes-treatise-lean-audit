/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7g
#
# 新井一成・Claude共著、2026年7月14日
# **7f照合キューの原文正確形 (その1): Ch.14前半・Ch.15**
# ⚠ DRAFT v1 — サンドボックスでは未コンパイル。正準ラン v6 前にローカル確認。
#
# ## 照合ソース (7f インデックス準拠)
#   佐藤訳 印字166-167頁 (欄外160-161): (24.4)(24.5)(24.6)(24.7)(25)(25.1)
#     (26)(26.1)(27)(27.1)(28)(28.1)
#   佐藤訳 印字172頁: (40.1)
#   佐藤訳 印字182頁 (欄外175): (50) 一般 m,n 形 (公理(vii)+定義XIX)
#   佐藤訳 印字186-187頁 (欄外180): (55) 6等式ワーク例 (結論: cの上限
#     min{b+1−e, a+1−d, a+b} / 下限 max{a,b} — 「ブールの例を少し修正」)
#
# ## 本ファイルの新規項目 (7gキュー #1,2,3,6,7,10)
#   th_14_24_4_src   : 3項包除原理 (原文の7項展開形)
#   th_14_24_5_src   : n項包除原理 (ieSum 再帰 = 原文の交代和)
#   th_14_24_6_src   : 排反下の加法性 (「Xを繰り返し適用」の再帰形)
#   th_14_24_7_src   : 排反+網羅 → Σ p_r/h = 1
#   th_14_25_src     : 全確率 a/h = Σ p_r a/h
#   th_14_25_1_src   : 事後正規化 p_r/ah = X_r/ΣX_r (除算なし形)
#   th_14_26_src     : a/h = (a+h̄)/h (overbar 回復形)
#   th_14_26_1_src   : a/h = (h⊃a)/h
#   th_14_28_src     : a/h=1 → (a+b̄)/h=1 / th_14_28_1_src : a/h=0 → (ā+b)/h=1
#   th_14_40_1_src   : p=1/2 の事後特例 (除算なし形)
#   Intensional.th_15_50_src : 1/m + 1/n = (m+n)/mn (公理(vii)修復形+XIX機構)
#   th_15_55_worked  : (55) の6等式ワーク例 — 単一 linarith 型の showcase
#
# ## 検証したい仮説
#   H32: n項包除 (24.5) の再帰は List 帰納のみで閉じ、公理コストは
#        {def_IX, ax_iii_op, ax_iii_true} + floor (C_rec 不可視)。
#   H33: (55) は floor + 0 Keynes 公理 (純線形算術)。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (継承 — phase2/3a/4 と同形) -/

axiom Pr : Prop → Prop → ℝ
axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1
axiom def_IX (p q h : Prop) : Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h
axiom def_X_left  (p q h : Prop) : Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h
axiom def_X_right (p q h : Prop) : Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h
axiom ax_range_lo (p h : Prop) : 0 ≤ Pr p h
axiom ax_range_hi (p h : Prop) : Pr p h ≤ 1

/-! ## 基本補題 (再掲・ファイル内自足) -/

theorem th_13_1 (a h : Prop) : Pr a h + Pr (¬a) h = 1 := by
  have step := def_IX True a h
  have e1 : (True ∧ ¬a) ↔ (¬a) := by tauto
  have e2 : (True ∧ a) ↔ a := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, ax_iii_true] at step
  linarith

theorem pr_false (h : Prop) : Pr False h = 0 := by
  have := th_13_1 True h
  have e : (¬True) ↔ False := by tauto
  rw [ax_iii_op _ _ h e] at this
  have := ax_iii_true h
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

/-- 連言の単調性 (右因子)。Pr (p∧q) h ≤ Pr q h。 -/
theorem pr_conj_le_right (p q h : Prop) : Pr (p ∧ q) h ≤ Pr q h := by
  have hx := def_X_right p q h
  -- Pr (p∧q) h = Pr q (p∧h) * Pr p h ... 逆向き。左因子版を使う:
  -- Pr (p∧q) h = Pr p (q∧h) * Pr q h ≤ 1 * Pr q h
  have hl := def_X_left p q h
  have h1 := ax_range_hi p (q ∧ h)
  have h0 := ax_range_lo q h
  nlinarith [ax_range_lo p (q ∧ h)]

/-- 選言の単調性。Pr p h ≤ Pr (p∨q) h。 -/
theorem pr_or_ge (p q h : Prop) : Pr p h ≤ Pr (p ∨ q) h := by
  have h24 := th_24 p q h
  have hc := pr_conj_le_right p q h
  linarith

/-! ## リスト機構 (再掲) -/

def bigOr : List Prop → Prop
  | [] => False
  | p :: rest => p ∨ bigOr rest

def bigAnd : List Prop → Prop
  | [] => True
  | p :: rest => p ∧ bigAnd rest

noncomputable def sumPr : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr p h + sumPr rest h

/-- 分配補題: p ∧ ⋁l ↔ ⋁(l.map (p ∧ ·))。 -/
theorem and_bigOr_distrib (p : Prop) : ∀ (l : List Prop),
    (p ∧ bigOr l) ↔ bigOr (l.map (fun q => p ∧ q)) := by
  intro l
  induction l with
  | nil => simp [bigOr]
  | cons q rest ih =>
      simp only [bigOr, List.map]
      constructor
      · rintro ⟨hp, hq | hrest⟩
        · exact Or.inl ⟨hp, hq⟩
        · exact Or.inr (ih.mp ⟨hp, hrest⟩)
      · rintro (⟨hp, hq⟩ | hrest)
        · exact ⟨hp, Or.inl hq⟩
        · obtain ⟨hp, hr⟩ := ih.mpr hrest
          exact ⟨hp, Or.inr hr⟩

/-- 分配補題 (右結合版): ⋁l ∧ a ↔ ⋁(l.map (· ∧ a))。 -/
theorem bigOr_and_distrib (a : Prop) : ∀ (l : List Prop),
    (bigOr l ∧ a) ↔ bigOr (l.map (fun q => q ∧ a)) := by
  intro l
  induction l with
  | nil => simp [bigOr]
  | cons q rest ih =>
      simp only [bigOr, List.map]
      rw [← ih]
      tauto

/-! ## (24.5) n項包除原理 — ieSum 再帰 -/

/-- **包除和** (Arai 拡張定義)。
ieSum (p::rest) h = Pr p h + ieSum rest h − ieSum (rest.map (p∧·)) h。
展開すると原文 (24.5) の交代和 Σp_r/h − Σp_sp_t/h + … + (−1)^{n−1}p₁…p_n/h。 -/
noncomputable def ieSum : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr p h + ieSum rest h - ieSum (rest.map (fun q => p ∧ q)) h
termination_by l _ => l.length
decreasing_by
  all_goals
    (simp only [List.length_map, List.length_cons, List.length_attach]; omega)

/-- 補助: 長さ制限つき帰納で (24.5) を閉じる。 -/
theorem th_24_5_aux (h : Prop) :
    ∀ (n : ℕ) (l : List Prop), l.length ≤ n → Pr (bigOr l) h = ieSum l h := by
  intro n
  induction n with
  | zero =>
      intro l hl
      have hl0 : l.length = 0 := Nat.le_zero.mp hl
      have : l = [] := List.eq_nil_of_length_eq_zero hl0
      subst this
      simp [bigOr, ieSum, pr_false]
  | succ k ih =>
      intro l hl
      cases l with
      | nil => simp [bigOr, ieSum, pr_false]
      | cons p rest =>
          have hlen : rest.length ≤ k := by
            simpa using Nat.succ_le_succ_iff.mp hl
          have hlen2 : (rest.map (fun q => p ∧ q)).length ≤ k := by
            simpa [List.length_map] using hlen
          have h24 := th_24 p (bigOr rest) h
          have hdist : Pr (p ∧ bigOr rest) h
              = Pr (bigOr (rest.map (fun q => p ∧ q))) h :=
            ax_iii_op _ _ h (and_bigOr_distrib p rest)
          have ih1 := ih rest hlen
          have ih2 := ih (rest.map (fun q => p ∧ q)) hlen2
          simp only [bigOr, ieSum]
          rw [h24, hdist, ih1, ih2]

/-- **Th.(14.24.5)** n項包除原理 (原文の一般交代和)。
「(p₁+…+p_n)/h = Σp_r/h − Σp_sp_t/h + … + (−1)^{n−1}p₁p₂…p_n/h」 -/
theorem th_14_24_5_src (h : Prop) (l : List Prop) :
    Pr (bigOr l) h = ieSum l h :=
  th_24_5_aux h l.length l le_rfl

/-- **Th.(14.24.4)** 3項包除の原文7項展開:
(a+b+c)/h = a/h + b/h + c/h − ab/h − bc/h − ca/h + abc/h。 -/
theorem th_14_24_4_src (a b c h : Prop) :
    Pr (a ∨ (b ∨ c)) h
      = Pr a h + Pr b h + Pr c h
        - Pr (a ∧ b) h - Pr (b ∧ c) h - Pr (a ∧ c) h + Pr (a ∧ (b ∧ c)) h := by
  -- (24) の3段適用 (原文の (24.4) 導出そのもの)
  have h1 := th_24 a (b ∨ c) h
  have h2 := th_24 b c h
  have hd : Pr (a ∧ (b ∨ c)) h = Pr ((a ∧ b) ∨ (a ∧ c)) h :=
    ax_iii_op _ _ h (by tauto)
  have h3 := th_24 (a ∧ b) (a ∧ c) h
  have he : Pr ((a ∧ b) ∧ (a ∧ c)) h = Pr (a ∧ (b ∧ c)) h :=
    ax_iii_op _ _ h (by tauto)
  linarith

/-! ## (24.6)(24.7) 排反下の加法性 — 「X を繰り返し適用」の再帰形 -/

/-- 連鎖排反 (原文の証明手順そのもの: 先頭と残り全体の交わりが逐次 0)。 -/
def chainExclusive : List Prop → Prop → Prop
  | [], _ => True
  | p :: rest, h => (Pr (p ∧ bigOr rest) h = 0) ∧ chainExclusive rest h

/-- **Th.(14.24.6)** 排反なら加法的: (p₁+…+p_n)/h = Σ p_r/h。 -/
theorem th_14_24_6_src (h : Prop) :
    ∀ (l : List Prop), chainExclusive l h → Pr (bigOr l) h = sumPr l h := by
  intro l
  induction l with
  | nil => intro _; simp [bigOr, sumPr, pr_false]
  | cons p rest ih =>
      rintro ⟨hnull, hrest⟩
      have h24 := th_24 p (bigOr rest) h
      simp only [bigOr, sumPr]
      rw [h24, hnull, ih hrest]
      ring

/-- **Th.(14.24.7)** 排反+網羅 → Σ p_r/h = 1。 -/
theorem th_14_24_7_src (h : Prop) (l : List Prop)
    (hex : chainExclusive l h) (hexh : Pr (bigOr l) h = 1) :
    sumPr l h = 1 := by
  rw [← th_14_24_6_src h l hex]
  exact hexh

/-! ## (25)(25.1) 全確率と事後正規化 -/

/-- **Th.(14.25)** 全確率: 排反+網羅 (a∧h 相対) なら a/h = Σ p_r a/h。
前提 hpart は原文の「(p₁+…+p_n)/ah = 1」に相当 (phase5 の hexh 流儀)。 -/
theorem th_14_25_src (a h : Prop) (l : List Prop)
    (hpart : Pr (bigOr l) (a ∧ h) = 1)
    (hex : chainExclusive (l.map (fun p => p ∧ a)) h) :
    Pr a h = sumPr (l.map (fun p => p ∧ a)) h := by
  have key : Pr (bigOr l ∧ a) h = Pr (bigOr l) (a ∧ h) * Pr a h :=
    def_X_left (bigOr l) a h
  rw [hpart, one_mul] at key
  have hdist : Pr (bigOr l ∧ a) h
      = Pr (bigOr (l.map (fun p => p ∧ a))) h :=
    ax_iii_op _ _ h (bigOr_and_distrib a l)
  rw [hdist] at key
  rw [← key]
  exact th_14_24_6_src h _ hex

/-- **Th.(14.25.1)** 事後正規化 (除算なし形):
p_r a/h = X_r とおけば p_r/ah · ΣX_r = X_r。原文の X_r/ΣX_r 表示の
分母払い形。6a の th_14_46_2 と同内容であることの再ラベル確定 (7f ✎#2)。 -/
theorem th_14_25_1_src (a h p : Prop) (l : List Prop)
    (hpart : Pr (bigOr l) (a ∧ h) = 1)
    (hex : chainExclusive (l.map (fun q => q ∧ a)) h) :
    Pr p (a ∧ h) * sumPr (l.map (fun q => q ∧ a)) h = Pr (p ∧ a) h := by
  have h25 := th_14_25_src a h l hpart hex
  have hx := def_X_left p a h
  rw [← h25]
  linarith [hx]

/-! ## (26)(26.1)(28)(28.1) overbar 回復形 -/

/-- **Th.(14.26)** a/h = (a+h̄)/h。前提 hns : h̄/h = 0 は (13.1) 系
(整合性下で成立) を入力化したもの。 -/
theorem th_14_26_src (a h : Prop) (hns : Pr (¬h) h = 0) :
    Pr a h = Pr (a ∨ ¬h) h := by
  have h24 := th_24 a (¬h) h
  have hle := pr_conj_le_right a (¬h) h
  have hlo := ax_range_lo (a ∧ ¬h) h
  have hz : Pr (a ∧ ¬h) h = 0 := le_antisymm (by linarith [hns]) hlo
  rw [h24, hns, hz]
  ring

/-- **Th.(14.26.1)** a/h = (h⊃a)/h。 -/
theorem th_14_26_1_src (a h : Prop) (hns : Pr (¬h) h = 0) :
    Pr a h = Pr (h → a) h := by
  have h26 := th_14_26_src a h hns
  have e : (a ∨ ¬h) ↔ (h → a) := by tauto
  rw [h26, ax_iii_op _ _ h e]

/-- **Th.(14.28)** a/h = 1 → (a+b̄)/h = 1
「確実な命題はすべての命題によって含意される」。 -/
theorem th_14_28_src (a b h : Prop) (h1 : Pr a h = 1) :
    Pr (a ∨ ¬b) h = 1 := by
  have hge := pr_or_ge a (¬b) h
  have hhi := ax_range_hi (a ∨ ¬b) h
  linarith

/-- **Th.(14.28.1)** a/h = 0 → (ā+b)/h = 1
「確実に偽なる命題はすべての命題を含意する」。 -/
theorem th_14_28_1_src (a b h : Prop) (h0 : Pr a h = 0) :
    Pr (¬a ∨ b) h = 1 := by
  have hc := th_13_1 a h
  have h1 : Pr (¬a) h = 1 := by linarith
  have hge := pr_or_ge (¬a) b h
  have hhi := ax_range_hi (¬a ∨ b) h
  linarith

/-! ## (40.1) p = 1/2 の事後特例 -/

/-- **Th.(14.40.1)** p = a/h₁ = 1/2 のとき
a/h₁h₂ · (h₂/ah₁ + h₂/āh₁) = h₂/ah₁ (除算なし形)。
原文: a/h₁h₂ = h₂/ah₁ / (h₂/ah₁ + h₂/āh₁)、かつ比 h₂/ah₁ : h₂/āh₁ と
ともに増加する。 -/
theorem th_14_40_1_src (a h₁ h₂ : Prop) (hp : Pr a h₁ = 1/2) :
    Pr a (h₂ ∧ h₁) * (Pr h₂ (a ∧ h₁) + Pr h₂ (¬a ∧ h₁)) = Pr h₂ (a ∧ h₁) := by
  -- 事前分割: h₂/h₁ = ah₂/h₁ + āh₂/h₁
  have hsplit := def_IX h₂ a h₁
  have e1 : (h₂ ∧ ¬a) ↔ (¬a ∧ h₂) := by tauto
  have e2 : (h₂ ∧ a) ↔ (a ∧ h₂) := by tauto
  rw [ax_iii_op _ _ h₁ e1, ax_iii_op _ _ h₁ e2] at hsplit
  -- 各項を def_X で分解
  have hA : Pr (a ∧ h₂) h₁ = Pr h₂ (a ∧ h₁) * Pr a h₁ := def_X_right a h₂ h₁
  have hB : Pr (¬a ∧ h₂) h₁ = Pr h₂ (¬a ∧ h₁) * Pr (¬a) h₁ := def_X_right (¬a) h₂ h₁
  -- 事後の連鎖: a/h₂h₁ · h₂/h₁ = ah₂/h₁
  have hC : Pr (h₂ ∧ a) h₁ = Pr a (h₂ ∧ h₁) * Pr h₂ h₁ := def_X_right h₂ a h₁
  have e3 : (h₂ ∧ a) ↔ (a ∧ h₂) := by tauto
  rw [ax_iii_op _ _ h₁ e3] at hC
  -- 補元事前: ā/h₁ = 1/2
  have hcomp := th_13_1 a h₁
  have hq : Pr (¬a) h₁ = 1/2 := by linarith
  rw [hp] at hA
  rw [hq] at hB
  -- 尤度を結合確率に引き戻し、h₂/h₁ を消去して積レベルで閉じる
  have hX : Pr h₂ (a ∧ h₁) = 2 * Pr (a ∧ h₂) h₁ := by linarith
  have hY : Pr h₂ (¬a ∧ h₁) = 2 * Pr (¬a ∧ h₂) h₁ := by linarith
  have hs' : Pr (a ∧ h₂) h₁ + Pr (¬a ∧ h₂) h₁ = Pr h₂ h₁ := by linarith
  have key : Pr a (h₂ ∧ h₁) * (Pr (a ∧ h₂) h₁ + Pr (¬a ∧ h₂) h₁)
      = Pr (a ∧ h₂) h₁ := by
    rw [hs']
    linarith
  rw [hX, hY]
  ring_nf
  ring_nf at key
  linarith [key]

/-! ## (50) 一般 m,n 形 — 内包キャリア上 (公理(vii)修復形) -/

namespace Intensional

axiom IProp : Type
axiom PrI : IProp → IProp → ℝ

/-- **公理(vii)** (修復形; 旧称 Ax.(前)/ax_mae)。 -/
axiom ax_vii (p n : ℕ) (hpn : p ≤ n) (hn : n ≠ 0) :
    ∃ (a e : IProp), PrI a e = (p : ℝ) / (n : ℝ)

/-- 定義XIX機構 (反復加算) — substrate 吸収の再掲。 -/
noncomputable def addTimes : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, P => P + addTimes n P

theorem addTimes_eq (P : ℝ) : ∀ n : ℕ, addTimes n P = (n : ℝ) * P := by
  intro n
  induction n with
  | zero => simp [addTimes]
  | succ k ih => simp only [addTimes, ih]; push_cast; ring

/-- **Th.(15.50) 一般形** (原文: a/f = 1/m, b/h = 1/n → a/f + b/h = (m+n)/mn)。
存在は公理(vii) (P = 1/mn)、値算術は substrate。前提 hle : m+n ≤ mn は
和が確率値であるための原文の暗黙条件。 -/
theorem th_15_50_src (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hle : m + n ≤ m * n) :
    ∃ (a e : IProp), PrI a e = 1 / (m : ℝ) + 1 / (n : ℝ) := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  obtain ⟨a, e, hval⟩ := ax_vii (m + n) (m * n) hle hmn
  refine ⟨a, e, ?_⟩
  rw [hval]
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  push_cast
  field_simp
  ring

/-- (XIX) 機構の使用例 (原文証明の n·P = 1/m の段):
P = 1/(mn) の n 回反復加算は 1/m。 -/
theorem th_15_50_xix_step (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    addTimes n (1 / ((m : ℝ) * (n : ℝ))) = 1 / (m : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [addTimes_eq]
  field_simp

end Intensional

/-! ## (55) 6等式ワーク例 — Boole 消去法の showcase -/

/-- **Th.(15.55) ワーク例** (原文 印字186-187頁の6等式系)。
λ+ν=a, λ+σ=b, λ+ν+σ=c, λ+μ+ν+ρ=d, λ+μ+σ+τ=e, λ+μ+ν+ρ+σ+τ+υ=1、
全変数 ≥ 0 から、c の限界:
  下限 max{a, b} ≤ c ≤ 上限 min{a+b, a+1−d, b+1−e}。
全体が線形算術 — H33: floor + 0 Keynes 公理。 -/
theorem th_15_55_worked
    (lam mu nu rho sig tau ups a b c d e : ℝ)
    (h1 : lam + nu = a) (h2 : lam + sig = b) (h3 : lam + nu + sig = c)
    (h4 : lam + mu + nu + rho = d) (h5 : lam + mu + sig + tau = e)
    (h6 : lam + mu + nu + rho + sig + tau + ups = 1)
    (hlam : 0 ≤ lam) (_hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hrho : 0 ≤ rho)
    (hsig : 0 ≤ sig) (htau : 0 ≤ tau) (hups : 0 ≤ ups) :
    (a ≤ c ∧ b ≤ c) ∧ (c ≤ a + b ∧ c ≤ a + 1 - d ∧ c ≤ b + 1 - e) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> linarith

end Keynes

/-! ## 監査クエリ (Phase 7g) -/

#check @Keynes.th_14_24_4_src
#check @Keynes.th_14_24_5_src
#check @Keynes.th_14_24_6_src
#check @Keynes.th_14_24_7_src
#check @Keynes.th_14_25_src
#check @Keynes.th_14_25_1_src
#check @Keynes.th_14_26_src
#check @Keynes.th_14_26_1_src
#check @Keynes.th_14_28_src
#check @Keynes.th_14_28_1_src
#check @Keynes.th_14_40_1_src
#check @Keynes.Intensional.th_15_50_src
#check @Keynes.th_15_55_worked

#print axioms Keynes.th_14_24_4_src
#print axioms Keynes.th_14_24_5_src
#print axioms Keynes.th_14_24_6_src
#print axioms Keynes.th_14_24_7_src
#print axioms Keynes.th_14_25_src
#print axioms Keynes.th_14_25_1_src
#print axioms Keynes.th_14_26_src
#print axioms Keynes.th_14_26_1_src
#print axioms Keynes.th_14_28_src
#print axioms Keynes.th_14_28_1_src
#print axioms Keynes.th_14_40_1_src
#print axioms Keynes.Intensional.th_15_50_src
#print axioms Keynes.Intensional.th_15_50_xix_step
#print axioms Keynes.th_15_55_worked
