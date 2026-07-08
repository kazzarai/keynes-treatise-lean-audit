/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 3d
#
# 新井一成・Claude共著、2026年5月4日
# Phase 3c (n-ary 影響係数 + フル Bayes, 39 ノード) → Phase 3d (累積 Bayes, +3 定理)
#
# ## 本ファイルで追加したもの
#   Theorems:
#     Th.(14.46)_seq     : 複数証拠 Bayes        ――― β = β₁∧β₂ 代入
#     Th.(14.47)_odds    : 事後オッズ比          ――― th_14_38_full 二回適用
#     Th.(14.48)_binary  : 2-仮説 Bayes 正規化形 ――― (47) + 全確率公式
#
# Phase 3d 意図的省略:
#   Th.(14.49) 証拠累積 ――― qualitative 命題 (条件付き独立性 + monotonicity)
#                          for Phase 5 に送る (induction 系の Mode C と一緒に)
#
# 継承: Phase 3c の全 39 ノード (簡略再掲、proof は省略してすぐ使う)
#
# ## 期待される新規 surface
#   th_14_46_seq      : th_14_38_full と同じ依存集合 (def_X_left, def_X_right, def_XI)
#   th_14_47_odds     : th_14_38_full 経由で Def.X 族 + def_XI
#   th_14_48_binary   : 上記 + def_IX + ax_iii_op (¬α 命題操作)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Keynes

/-! ## プリミティブ・公理・定義 (Phase 3c から継承、簡潔再掲) -/

axiom Pr : Prop → Prop → ℝ

axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1

axiom def_IX (p q h : Prop) :
    Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h
axiom def_X_left (p q h : Prop) :
    Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h
axiom def_X_right (p q h : Prop) :
    Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h
axiom def_XI (P Q R : ℝ) (hQ : Q ≠ 0) :
    P * Q = R → P = R / Q

/-! ## Phase 3c までの主要定理 (回帰用、proof copy) -/

theorem th_14_38_full (α β h : Prop) (hβ : Pr β h ≠ 0) :
    Pr α (β ∧ h) = Pr β (α ∧ h) * Pr α h / Pr β h := by
  have h_left  : Pr (α ∧ β) h = Pr α (β ∧ h) * Pr β h := def_X_left α β h
  have h_right : Pr (α ∧ β) h = Pr β (α ∧ h) * Pr α h := def_X_right α β h
  have heq : Pr α (β ∧ h) * Pr β h = Pr β (α ∧ h) * Pr α h := by
    rw [← h_left, h_right]
  exact def_XI (Pr α (β ∧ h)) (Pr β h) (Pr β (α ∧ h) * Pr α h) hβ heq

/-! ## Phase 3d 新規 -/

/-- **Th.(14.46)_seq** 複数証拠 Bayes.
$\Pr(\alpha, \beta_1\wedge\beta_2\wedge h) = \dfrac{\Pr(\beta_1\wedge\beta_2, \alpha\wedge h)\cdot\Pr(\alpha,h)}{\Pr(\beta_1\wedge\beta_2, h)}$.

Keynes Prolog DB: cites(th14_46, th14_38), cites(th14_46, th14_41_2).

これは th_14_38_full を $\beta := \beta_1\wedge\beta_2$ に特殊化しただけの形。
連続証拠の Bayes 更新の最小単位。

## Proof architecture
| Step | Mechanism                  | Cites             |
|------|----------------------------|-------------------|
|  1   | th_14_38_full α (β₁∧β₂) h  | explicit          |

## 検証対象
- th_14_38_full と同じ依存集合 (def_X_left, def_X_right, def_XI) が surface
- Th.(14.41.2) の引用は不要 (Phase 3c の発見 7 = Mode B∩C* により、Infl 経由の
  累積展開は Lean では substrate に吸収される)
- DB の引用 (th14_41_2) が Mode S finding として記録される -/
theorem th_14_46_seq (α β₁ β₂ h : Prop)
    (hβ : Pr (β₁ ∧ β₂) h ≠ 0) :
    Pr α ((β₁ ∧ β₂) ∧ h) =
    Pr (β₁ ∧ β₂) (α ∧ h) * Pr α h / Pr (β₁ ∧ β₂) h :=
  th_14_38_full α (β₁ ∧ β₂) h hβ

/-- **Th.(14.47)_odds** 事後オッズ比 = 事前オッズ × 尤度比.
$\dfrac{\Pr(\alpha_1, \beta\wedge h)}{\Pr(\alpha_2, \beta\wedge h)}
 = \dfrac{\Pr(\alpha_1, h)\cdot\Pr(\beta, \alpha_1\wedge h)}{\Pr(\alpha_2, h)\cdot\Pr(\beta, \alpha_2\wedge h)}$.

Keynes Prolog DB: cites(th14_47, th14_46), cites(th14_47, th14_38).

Bayes の決定理論的定式化の基本形。事後確率の比 = 事前確率の比 × 尤度の比。
仮説選好の更新ルール。

## Proof architecture
| Step | Mechanism                              | Cites             |
|------|----------------------------------------|-------------------|
|  1   | th_14_38_full α₁ β h                   | explicit          |
|  2   | th_14_38_full α₂ β h                   | explicit          |
|  3   | 比を取る                                |                   |
|  4   | 算術整理                                |                   |

## 検証対象
- th_14_38_full の依存 (def_X_left, def_X_right, def_XI) を継承
- 新規 surface は無し (algebraic 操作のみ)
- 4-axiom floor からの上昇は def_X_left, def_X_right, def_XI の 3 つのみ -/
theorem th_14_47_odds (α₁ α₂ β h : Prop)
    (hβ : Pr β h ≠ 0)
    (hα₂_post : Pr α₂ (β ∧ h) ≠ 0)
    (hα₂_prior : Pr α₂ h ≠ 0)
    (hβ_α₂ : Pr β (α₂ ∧ h) ≠ 0) :
    Pr α₁ (β ∧ h) / Pr α₂ (β ∧ h)
    = (Pr α₁ h * Pr β (α₁ ∧ h)) / (Pr α₂ h * Pr β (α₂ ∧ h)) := by
  have h₁ : Pr α₁ (β ∧ h) = Pr β (α₁ ∧ h) * Pr α₁ h / Pr β h :=
    th_14_38_full α₁ β h hβ
  have h₂ : Pr α₂ (β ∧ h) = Pr β (α₂ ∧ h) * Pr α₂ h / Pr β h :=
    th_14_38_full α₂ β h hβ
  rw [h₁, h₂]
  have hβ_α₂_α₂_ne : Pr β (α₂ ∧ h) * Pr α₂ h ≠ 0 := mul_ne_zero hβ_α₂ hα₂_prior
  -- field_simp が単独で閉じる版と ring が要る版の両対応 (2026-07-07 修正)
  first
    | (field_simp; ring)
    | field_simp

/-- **Th.(14.48)_binary** 2-仮説 Bayes 正規化形.
仮説 α₁ と α₂ = ¬α₁ が排反かつ完全な場合、
$\Pr(\alpha_1, \beta\wedge h) = \dfrac{p_1 q_1}{p_1 q_1 + p_2 q_2}$,
where $p_1 = \Pr(\alpha_1, h)$, $p_2 = \Pr(\neg\alpha_1, h)$,
$q_1 = \Pr(\beta, \alpha_1\wedge h)$, $q_2 = \Pr(\beta, \neg\alpha_1\wedge h)$.

Keynes Prolog DB: cites(th14_48, th14_46_2).

## Proof architecture
| Step | Mechanism                                       | Cites             |
|------|------------------------------------------------|-------------------|
|  1   | th_14_38_full α₁ β h                           | explicit          |
|  2   | def_IX β α₁ h: Pr β h = Pr(β∧¬α₁)h + Pr(β∧α₁)h | explicit          |
|  3   | def_X_left x2 で Pr(β∧αᵢ)h = qᵢpᵢ              | explicit          |
|  4   | ax_iii_op で命題形を整える (¬α₁∧β ↔ β∧¬α₁)     | explicit          |
|  5   | field_simp + ring                               | (Mathlib)         |

## 検証対象
- def_IX, ax_iii_op, def_X_left, def_X_right, def_XI が全て surface
- Phase 3d 中で **最も多くの Keynes 公理に依存する**定理になる見込み
  (th_14_38_full 経由 + 全確率公式の def_IX + 命題形整え) -/
theorem th_14_48_binary (α β h : Prop)
    (hp1 : Pr α h ≠ 0) (hp2 : Pr (¬α) h ≠ 0)
    (hβ : Pr β h ≠ 0) :
    Pr α (β ∧ h) =
    (Pr α h * Pr β (α ∧ h)) /
    (Pr α h * Pr β (α ∧ h) + Pr (¬α) h * Pr β (¬α ∧ h)) := by
  -- Step 1: 全確率公式  Pr β h = Pr(β∧¬α)h + Pr(β∧α)h
  have h_total_step : Pr (β ∧ ¬α) h + Pr (β ∧ α) h = Pr β h :=
    def_IX β α h
  -- Step 2: def_X で各項を分解
  have h_left_alpha : Pr (β ∧ α) h = Pr β (α ∧ h) * Pr α h :=
    def_X_left β α h
  have h_left_neg : Pr (β ∧ ¬α) h = Pr β (¬α ∧ h) * Pr (¬α) h :=
    def_X_left β (¬α) h
  -- Step 3: th_14_38_full 適用
  have h_bayes : Pr α (β ∧ h) = Pr β (α ∧ h) * Pr α h / Pr β h :=
    th_14_38_full α β h hβ
  -- Step 4: Pr β h を全確率公式で置換
  have h_total : Pr β h =
      Pr β (α ∧ h) * Pr α h + Pr β (¬α ∧ h) * Pr (¬α) h := by
    rw [← h_total_step, h_left_alpha, h_left_neg]
    ring
  rw [h_bayes, h_total]
  -- Goal: Pr β (α ∧ h) * Pr α h / (qα·pα + q¬α·p¬α)
  --     = (Pr α h * Pr β (α ∧ h)) / (Pr α h * Pr β (α ∧ h) + Pr (¬α) h * Pr β (¬α ∧ h))
  -- 形が違うだけ (mul の順序). ring で揃える前に分母非ゼロを確認.
  have hdenom :
      Pr β (α ∧ h) * Pr α h + Pr β (¬α ∧ h) * Pr (¬α) h =
      Pr α h * Pr β (α ∧ h) + Pr (¬α) h * Pr β (¬α ∧ h) := by ring
  rw [hdenom]
  -- 残り: Pr β (α ∧ h) * Pr α h = Pr α h * Pr β (α ∧ h) (commutativity)
  ring

end Keynes

/-! ## 監査クエリ (Phase 3d 新規) -/

#check @Keynes.th_14_46_seq
#check @Keynes.th_14_47_odds
#check @Keynes.th_14_48_binary

-- Kernel 依存. 注目点:
--   th_14_46_seq      : th_14_38_full をそのまま (def_X_left, def_X_right, def_XI)
--   th_14_47_odds     : 同上 + (algebraic only)
--   th_14_48_binary   : 上記 + def_IX, ax_iii_op (Phase 3d で最も依存数が多い)
#print axioms Keynes.th_14_46_seq
#print axioms Keynes.th_14_47_odds
#print axioms Keynes.th_14_48_binary

-- 回帰テスト
#print axioms Keynes.th_14_38_full
