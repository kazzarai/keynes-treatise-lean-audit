/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 3c
#
# 新井一成・Claude共著、2026年4月
# Phase 3b (Johnson 影響係数 binary, 33 ノード) → Phase 3c (n-ary 拡張 + フル Bayes, +6 定理)
#
# ## 本ファイルで追加したもの
#   Definitions (新):
#     Infl3  : 3-ary 影響係数 {αβγ} := Pr(α∧β∧γ,h) / (Pr α h · Pr β h · Pr γ h)
#   Theorems:
#     Th.(14.45)_b : {(α∧α)β} = {αβ}        ――― 反復規則 (binary 形)
#     Th.(14.41)_c : αβγ/h = {αβγ}·α/h·β/h·γ/h  ――― 3-ary 累積公式
#     Th.(14.42)_c : {αβγ} = {αγβ}          ――― 3-arg 順序対称性
#     Th.(14.43)   : 分離因数規則            ――― def_X_left の (α, β∧γ) 適用
#     Th.(14.38)_full : Pr α (β∧h) = Pr β (α∧h) · Pr α h / Pr β h  ――― フル Bayes
#
# 継承: Phase 3b の全 33 ノード (再掲)
#
# ## 鍵となる設計判断
# Keynes の {ααβ}={αβ} (Th.14.45) は multiset エンコーディングを必要としない。
# Lean では `Infl (α ∧ α) β h = Infl α β h` という二項形で書け、`(α∧α) ↔ α` を
# `ax_iii_op` で書き換えるだけで閉じる。Keynes の `{}` 表記の暗黙的 dedup は
# 命題論理レベルで起こっており、Lean では `ax_iii_op` がその役割を果たす。
#
# ## 期待される新規 surface
#   th_14_45_b   : ax_iii_op のみ (Phase 3b の th_14_42 と同様)
#   th_14_41_c   : (基底のみ) 4-axiom floor 達成見込み
#   th_14_42_c   : ax_iii_op (3-arg permutation で出る)
#   th_14_43     : def_X_left のみ
#   th_14_38_full: def_X_left + def_X_right + def_XI 全集合
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Keynes

/-! ## プリミティブ・公理・定義 (Phase 3b から継承) -/

axiom Pr : Prop → Prop → ℝ

def Certain       (α h : Prop) : Prop := Pr α h = 1
def Impossible    (α h : Prop) : Prop := Pr α h = 0
def NonCertain    (α h : Prop) : Prop := Pr α h < 1
def NonImpossible (α h : Prop) : Prop := 0 < Pr α h
def Inconsistent  (α h : Prop) : Prop := Pr α h = 0
def InGroup       (α h : Prop) : Prop := Pr α h = 1
def KEq (α β h : Prop) : Prop := Pr β (α ∧ h) = 1 ∧ Pr α (β ∧ h) = 1

axiom ax_ii (α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)
axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1
axiom ax_iva_mul (P Q : ℝ) : P * Q = Q * P
axiom ax_iva_add (P Q : ℝ) : P + Q = Q + P
axiom ax_ivb (P Q : ℝ) : 0 < Q → P < P + Q
axiom ax_ivc (P Q R : ℝ) : P + Q = P + R → Q = R
axiom ax_v (P Q R S : ℝ) : (P + Q) + (R + S) = (P + R) + (Q + S)
axiom ax_vi (P R S : ℝ) : P * (R + S) = P * R + P * S

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

def Independent (p q h : Prop) : Prop :=
    Pr p (q ∧ h) = Pr p h ∧ Pr q (p ∧ h) = Pr q h
def Irrelevant (α₂ α₁ h : Prop) : Prop := Pr α₁ (α₂ ∧ h) = Pr α₁ h

/-! ## Phase 3b 既証 (回帰用) -/

noncomputable def Infl (α β h : Prop) : ℝ := Pr (α ∧ β) h / (Pr α h * Pr β h)

theorem th_14_36 (α β h : Prop) (hindep : Independent α β h) :
    Pr (α ∧ β) h = Pr α h * Pr β h := by
  have step1 : Pr (α ∧ β) h = Pr α (β ∧ h) * Pr β h :=
    def_X_left α β h
  rw [step1, hindep.1]

theorem th_14_42 (α β h : Prop) : Infl α β h = Infl β α h := by
  unfold Infl
  have eq : (α ∧ β) ↔ (β ∧ α) := by tauto
  rw [ax_iii_op _ _ h eq, mul_comm (Pr α h) (Pr β h)]

/-! ## Phase 3c 新規 -/

/-- **Th.(14.45)_b** 反復規則 (binary 形).
$\{(\alpha\wedge\alpha)\beta\} = \{\alpha\beta\}$.

Keynes 原文では `{ααβ}={αβ}` と書かれるが、これは multiset 表記ではなく、
**propositional dedup の暗黙適用**を意味する。Keynes は `{}` 内の命題が
論理的に同値であれば結果は変わらない、という暗黙のルールを使っている。

Lean ではこれを直接表現できる: 二項影響係数 `Infl` に `(α ∧ α)` を渡すと、
`ax_iii_op` 経由で `α` を渡したのと同じ値になる。

Keynes Prolog DB: cites(th14_45, ax_ii), cites(th14_45, th13_12).

## Proof architecture
| Step | Mechanism                | Cites                  |
|------|--------------------------|------------------------|
|  1   | (α∧α)∧β ↔ α∧β            | ax_iii_op + tauto      |
|  2   | α∧α ↔ α                  | ax_iii_op + tauto      |

## 検証対象
- ax_iii_op が surface
- Ax.(ii) や Th.(13.12) は **不要** (Lean では命題同値の伝搬が自動)
  → これは Mode S finding 候補: DB は Ax.(ii)+Th.(13.12) を引用するが、
     kernel は ax_iii_op だけで閉じる。 -/
theorem th_14_45_b (α β h : Prop) :
    Infl (α ∧ α) β h = Infl α β h := by
  unfold Infl
  have eq1 : (α ∧ α) ↔ α := by tauto
  have eq2 : ((α ∧ α) ∧ β) ↔ (α ∧ β) := by tauto
  rw [ax_iii_op _ _ h eq1, ax_iii_op _ _ h eq2]

/-- **3-ary 影響係数** {αβγ}.
$\{\alpha\beta\gamma\} := \dfrac{\Pr(\alpha\wedge\beta\wedge\gamma, h)}
{\Pr(\alpha,h)\cdot\Pr(\beta,h)\cdot\Pr(\gamma,h)}$. -/
noncomputable def Infl3 (α β γ h : Prop) : ℝ :=
    Pr (α ∧ β ∧ γ) h / (Pr α h * Pr β h * Pr γ h)

/-- **Th.(14.41)_c** 3-arg 累積公式.
$\alpha\beta\gamma/h = \{\alpha\beta\gamma\}\cdot\alpha/h\cdot\beta/h\cdot\gamma/h$.

Keynes Prolog DB: cites(th14_41_1, th14_41) — 41 の 3 項拡張として.

## Proof architecture
| Step | Mechanism            | Cites             |
|------|----------------------|-------------------|
|  1   | Infl3 の定義展開     | (Lean def)        |
|  2   | field_simp           | (Mathlib)         |

## 検証対象
- Phase 3b の th_14_41_b と同じく 4-axiom floor 達成見込み (Mode B∩C* 拡張) -/
theorem th_14_41_c (α β γ h : Prop)
    (hα : Pr α h ≠ 0) (hβ : Pr β h ≠ 0) (hγ : Pr γ h ≠ 0) :
    Pr (α ∧ β ∧ γ) h = Infl3 α β γ h * Pr α h * Pr β h * Pr γ h := by
  unfold Infl3
  have hp : Pr α h * Pr β h * Pr γ h ≠ 0 :=
    mul_ne_zero (mul_ne_zero hα hβ) hγ
  field_simp

/-- **Th.(14.42)_c** 3-arg 順序対称性. {αβγ} = {αγβ}.

Keynes Prolog DB: cites(th14_42_1, th14_42).

## Proof architecture
| Step | Mechanism                | Cites             |
|------|--------------------------|-------------------|
|  1   | Infl3 の定義展開         | (Lean def)        |
|  2   | (α∧β∧γ) ↔ (α∧γ∧β)        | ax_iii_op + tauto |
|  3   | ring                     | (built-in)        |

検証対象: ax_iii_op が再び Mode A' として surface (binary 版と同じ機構). -/
theorem th_14_42_c (α β γ h : Prop) :
    Infl3 α β γ h = Infl3 α γ β h := by
  unfold Infl3
  have eq : (α ∧ β ∧ γ) ↔ (α ∧ γ ∧ β) := by tauto
  rw [ax_iii_op _ _ h eq]
  ring

/-- **Th.(14.43)** 分離因数規則.
α が h 下で (β∧γ) と独立(無関連)なら、
$\Pr(\alpha\wedge(\beta\wedge\gamma),h) = \Pr(\alpha,h) \cdot \Pr(\beta\wedge\gamma,h)$.

Keynes 原文: 「乗数として分離因数は被乗数における連合を分離する」.
これは Th.(14.36) (binary 独立性 → 乗法分解) を、第二引数を複合命題 (β∧γ) に
した形に過ぎない。Lean では def_X_left を直接適用するだけ。

Keynes Prolog DB: cites(th14_43, def_x), cites(th14_43, th14_41_2).

## Proof architecture
| Step | Mechanism            | Cites             |
|------|----------------------|-------------------|
|  1   | def_X_left α (β∧γ) h | explicit          |
|  2   | hirrel で書換        | (hypothesis)      |

検証対象: def_X_left のみ surface (Th.14.36 と同じ最小性). -/
theorem th_14_43 (α β γ h : Prop)
    (hirrel : Pr α ((β ∧ γ) ∧ h) = Pr α h) :
    Pr (α ∧ (β ∧ γ)) h = Pr α h * Pr (β ∧ γ) h := by
  rw [def_X_left α (β ∧ γ) h, hirrel]

/-- **Th.(14.38)_full** 完全 Bayes 比率形.
任意の α, β について Pr β h ≠ 0 なら、
$\Pr(\alpha, \beta\wedge h) = \dfrac{\Pr(\beta, \alpha\wedge h)\cdot\Pr(\alpha,h)}{\Pr(\beta,h)}$.

これは Keynes Th.(14.38) の中核を成す式. Phase 3a の th_14_38_b
(α/(bh) = αb/h / b/h) は条件付き確率の定義的形式だったが、本定理は
Def.X の左形と右形の整合性から **逆方向** の確率を引き出す Bayes 反転.

Keynes Prolog DB: cites(th14_38, def_x), cites(th14_38, def_xi).

## Proof architecture
| Step | Mechanism                          | Cites             |
|------|------------------------------------|-------------------|
|  1   | def_X_left α β h                   | explicit (Def.X)  |
|  2   | def_X_right α β h                  | explicit (Def.X)  |
|  3   | 両式から Pr α (β∧h) · Pr β h = Pr β (α∧h) · Pr α h | (算術) |
|  4   | def_XI で除算                      | explicit (Def.XI) |

## 検証対象
- def_X_left + def_X_right が両方 surface
- def_XI も surface (Phase 3a の th_14_38_b と同じく明示適用)
- Phase 3a Finding 6 の延長で、Def.XI が再び明示的に必要となる Bayes 系
  定理として記録される。 -/
theorem th_14_38_full (α β h : Prop) (hβ : Pr β h ≠ 0) :
    Pr α (β ∧ h) = Pr β (α ∧ h) * Pr α h / Pr β h := by
  have h_left  : Pr (α ∧ β) h = Pr α (β ∧ h) * Pr β h := def_X_left α β h
  have h_right : Pr (α ∧ β) h = Pr β (α ∧ h) * Pr α h := def_X_right α β h
  have heq : Pr α (β ∧ h) * Pr β h = Pr β (α ∧ h) * Pr α h := by
    rw [← h_left, h_right]
  exact def_XI (Pr α (β ∧ h)) (Pr β h) (Pr β (α ∧ h) * Pr α h) hβ heq

end Keynes

/-! ## 監査クエリ (Phase 3c 新規) -/

#check @Keynes.Infl3
#check @Keynes.th_14_45_b
#check @Keynes.th_14_41_c
#check @Keynes.th_14_42_c
#check @Keynes.th_14_43
#check @Keynes.th_14_38_full

-- Kernel 依存. 注目点:
--   th_14_45_b   : ax_iii_op のみ (Mode S 候補: DB は ax_ii, th13_12 を引用)
--   th_14_41_c   : 4-axiom floor 達成見込み (Mode B∩C* 拡張)
--   th_14_42_c   : ax_iii_op が surface (Mode A' 反復)
--   th_14_43     : def_X_left のみ
--   th_14_38_full: def_X_left + def_X_right + def_XI が全て surface
#print axioms Keynes.th_14_45_b
#print axioms Keynes.th_14_41_c
#print axioms Keynes.th_14_42_c
#print axioms Keynes.th_14_43
#print axioms Keynes.th_14_38_full

-- 回帰テスト
#print axioms Keynes.th_14_36
#print axioms Keynes.th_14_42
