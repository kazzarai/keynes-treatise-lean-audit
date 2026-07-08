/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 5
#
# 新井一成・Claude共著、2026年7月6日
# Phase 4 (Ch.15 数値測定) → Phase 5 (Ch.17 逆確率 + Ch.14 積み残し (14.49))
#
# ## 本ファイルで追加したもの
#   Ch.14 積み残し (Phase 3d が意図的に送った最後のアンカー):
#     th_14_49       : 証拠累積定理 (正の関連 → 相互強化)
#     th_14_49_infl  : 影響係数形 ({β₁β₂} > 1 → 相互強化)
#   Ch.17 (Boole 挑戦問題・逆確率・Laplace 継承則):
#     th_17_56_raw   : (56) 原型  π = α₁E/h + α₂E/h − α₁α₂E/h
#     th_17_56       : (56)      π = e₁p₁ + e₂p₂ − z·π  [Boole 挑戦問題]
#     th_17_56_1     : (56.1)    π の 5 限界 (max ≤ π ≤ 3 種の min 成分)
#     th_17_56_2     : (56.2)    e₁,e₂ 消去限界  π ≤ p₁ + p₂
#     th_17_56_3     : (56.3)    e₂ 消去限界    e₁p₁ ≤ π ≤ 1−e₁+e₁p₁
#     th_17_56_4     : (56.4)    p₂ 消去限界    π ≤ e₁p₁ + e₂
#     th_17_56_5     : (56.5)    原因知識独立   π ≥ e₁p₁ + e₂p₂ − e₁e₂
#     th_17_57       : (57)      n 原因一般化 (List 帰納法・順序型包除)
#     th_17_57_2     : (57.2)    各 eₖpₖ ≤ π (n 原因下界)
#     th_17_57_6     : (57.6)    事後確率 = Bayes 反転 [Boole 問題 IX]
#     th_17_58       : (58)      Laplace 継承則 = n 項連鎖律 (Def.X の反復)
#     th_17_58_1     : (58.1)    不変原因 (各段確実) → 連鎖積 = 1
#     th_17_58_2     : (58.2)    連鎖積の単調非増加 (範囲原理下)
#     th_17_58_3     : (58.3)    不変原因の事後確率の収束レート下界
#
# ## Phase 5 意図的省略 (Phase 6 送り、理由明記)
#   Th.(14.49.1), (17.57.1), (17.57.3), (17.57.4), (17.57.5):
#     いずれも n 原因の相互独立性下の Π(1−eᵢ) 積公式。List 上の相互独立性
#     predicate (n 項 mutual independence) という新しい基盤機構を要する。
#     アンカー内容 (Boole 限界 + Bayes 反転 + 収束) は本 Phase で網羅済み。
#
# ## 検証したい仮説 (実行結果が最終判定)
#   H5: 「monotone convergence が新規 Mode C として surface する」(引き継ぎ書) は
#       H1 (帰納法) と同型の反証を受ける。収束の Keynes 的内容は有限 n の
#       レート不等式 (th_17_58_3, 純代数) に載っており、極限移行は substrate。
#       #print axioms th_17_58_3 は floor + 0 個の Keynes 公理と予測。
#   H6: th_17_56 (Boole 挑戦問題) は def_IX + ax_iii_op + def_X_left +
#       def_X_right の 4 公理を同時に要求する (Bayes 反転 th_14_38_full の
#       3 公理同時 surface [Finding 11] を上回る、監査中最大の同時要求)。
#   H7: th_17_58 (Laplace) の kernel 経路は {ax_iii_true, def_X_left} のみ。
#       DB は cites(th17_58, th14_38) を記録するが、連鎖律に Bayes 反転は
#       不要 → **Mode S 第 4 例候補** (実行結果で判定)。
#   H8: 順序型包除 (th_17_57) と連鎖律 (th_17_58) の帰納法は、H1 と同じく
#       #print axioms に痕跡を残さない。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase5.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (Phase 4 から継承) -/

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

axiom ax_range_lo (α h : Prop) : 0 ≤ Pr α h
axiom ax_range_hi (α h : Prop) : Pr α h ≤ 1

/-! ## 再掲 (Pilot / Phase 3c / Phase 4 から、証明付き) -/

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

theorem th_14_38_full (α β h : Prop) (hβ : Pr β h ≠ 0) :
    Pr α (β ∧ h) = Pr β (α ∧ h) * Pr α h / Pr β h := by
  have h_left  : Pr (α ∧ β) h = Pr α (β ∧ h) * Pr β h := def_X_left α β h
  have h_right : Pr (α ∧ β) h = Pr β (α ∧ h) * Pr α h := def_X_right α β h
  have heq : Pr α (β ∧ h) * Pr β h = Pr β (α ∧ h) * Pr α h := by
    rw [← h_left, h_right]
  exact def_XI (Pr α (β ∧ h)) (Pr β h) (Pr β (α ∧ h) * Pr α h) hβ heq

/-- 連言の左上界 (Arai 補題): αy/h ≤ α/h。Phase 4 の (51) 上界成分の再掲。 -/
theorem pr_conj_le_left (α y h : Prop) : Pr (α ∧ y) h ≤ Pr α h := by
  have h9 := def_IX α y h
  have hlo := ax_range_lo (α ∧ ¬y) h
  linarith

/-- 連言の右上界 (Arai 補題): αy/h ≤ y/h。 -/
theorem pr_conj_le_right (α y h : Prop) : Pr (α ∧ y) h ≤ Pr y h := by
  have h9 := def_IX y α h
  have hlo := ax_range_lo (y ∧ ¬α) h
  have e : (y ∧ α) ↔ (α ∧ y) := by tauto
  rw [ax_iii_op _ _ h e] at h9
  linarith

/-! ## Ch.14 積み残し: Th.(14.49) 証拠累積定理 -/

/-- **二項影響係数** (Phase 3b 再掲、Arai 拡張定義)。 -/
noncomputable def Infl (α β h : Prop) : ℝ := Pr (α ∧ β) h / (Pr α h * Pr β h)

/-- **Th.(14.49)** 証拠累積定理 (核心形).
β₁ と β₂ が h 下で正に関連する (合接確率が積を超える) とき、β₁ の獲得は
β₂ の確率を強化する: β₂/β₁h > β₂/h。

Keynes Prolog DB: cites(th14_49, th14_24_2), cites(th14_49, th14_41_2).
Keynes の散文「α, b, c, … が命題 n を支持するとき、各データは相互の
確率を強化する」の二項核心。

## Proof architecture
| Step | Mechanism                        | Cites             |
|------|----------------------------------|-------------------|
|  1   | ax_iii_op (∧ 交換) + def_X_left  | Ax.(iii) + Def.X  |
|  2   | 正値 Pr β₁ h での積の消去        | (算術)            |

## 検証対象
- DB 引用の th14_24_2 / th14_41_2 は kernel 経路では不要
  (影響係数の代数は substrate に吸収済み [Finding 7/10] のため、
   残るのは Def.X による Pr への接続のみ) → Mode S 系データ点 -/
theorem th_14_49 (β₁ β₂ h : Prop) (h1 : 0 < Pr β₁ h)
    (hassoc : Pr β₁ h * Pr β₂ h < Pr (β₁ ∧ β₂) h) :
    Pr β₂ h < Pr β₂ (β₁ ∧ h) := by
  have hx : Pr (β₁ ∧ β₂) h = Pr β₂ (β₁ ∧ h) * Pr β₁ h := by
    have e : (β₁ ∧ β₂) ↔ (β₂ ∧ β₁) := by tauto
    rw [ax_iii_op _ _ h e]
    exact def_X_left β₂ β₁ h
  rw [hx] at hassoc
  -- hassoc : Pr β₁ h * Pr β₂ h < Pr β₂ (β₁ ∧ h) * Pr β₁ h。
  -- 正値 Pr β₁ h の消去は nlinarith (名前付き消去補題の版差を回避)。
  nlinarith [hassoc, h1]

/-- **Th.(14.49)_infl** 影響係数形: {β₁β₂} > 1 → 相互強化。 -/
theorem th_14_49_infl (β₁ β₂ h : Prop) (h1 : 0 < Pr β₁ h) (h2 : 0 < Pr β₂ h)
    (hinfl : 1 < Infl β₁ β₂ h) : Pr β₂ h < Pr β₂ (β₁ ∧ h) := by
  have hprod : 0 < Pr β₁ h * Pr β₂ h := mul_pos h1 h2
  unfold Infl at hinfl
  have hassoc : Pr β₁ h * Pr β₂ h < Pr (β₁ ∧ β₂) h :=
    (one_lt_div hprod).mp hinfl
  exact th_14_49 β₁ β₂ h h1 hassoc

/-! ## Ch.17 §2: Boole 挑戦問題 (56) 系列 -/

/-- **Th.(17.56)_raw** Boole 挑戦問題の原型.
E が原因 α₁, α₂ を通じてのみ生起する (網羅性: (α₁∨α₂)/Eh = 1) とき、
π = α₁E/h + α₂E/h − α₁α₂E/h。

## Proof architecture
| Step | Mechanism                                  | Cites            |
|------|--------------------------------------------|------------------|
|  1   | def_X_left で (α₁∨α₂)∧E を分解 + 網羅性    | Def.X            |
|  2   | th_24 で E∧ 分配後の選言を展開             | (24) 加法定理    |
|  3   | ax_iii_op で分配律を処理                   | Ax.(iii)         |
|  4   | linarith                                   | (算術)           | -/
theorem th_17_56_raw (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1) :
    Pr E h = Pr (α₁ ∧ E) h + Pr (α₂ ∧ E) h - Pr ((α₁ ∧ α₂) ∧ E) h := by
  have key : Pr ((α₁ ∨ α₂) ∧ E) h = Pr (α₁ ∨ α₂) (E ∧ h) * Pr E h :=
    def_X_left (α₁ ∨ α₂) E h
  rw [hexh, one_mul] at key
  have expand := th_24 (α₁ ∧ E) (α₂ ∧ E) h
  have e1 : ((α₁ ∧ E) ∨ (α₂ ∧ E)) ↔ ((α₁ ∨ α₂) ∧ E) := by tauto
  have e2 : ((α₁ ∧ E) ∧ (α₂ ∧ E)) ↔ ((α₁ ∧ α₂) ∧ E) := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at expand
  linarith

/-- **Th.(17.56)** Boole 挑戦問題 (Keynes 再定式形).
e₁ = α₁/h, e₂ = α₂/h, p₁ = E/α₁h, p₂ = E/α₂h, z = α₁α₂/Eh とおくと
π = e₁p₁ + e₂p₂ − z·π。

Keynes Prolog DB: cites(th17_56, th14_24), cites(th17_56, def_x).

## 検証対象 (H6 の判定点)
- def_IX + ax_iii_op + def_X_left + def_X_right の 4 公理同時 surface。
  Bayes 反転 (Finding 11 の 3 公理) を上回る、監査中最大の同時要求と予測。 -/
theorem th_17_56 (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1) :
    Pr E h = Pr E (α₁ ∧ h) * Pr α₁ h + Pr E (α₂ ∧ h) * Pr α₂ h
             - Pr (α₁ ∧ α₂) (E ∧ h) * Pr E h := by
  have raw := th_17_56_raw α₁ α₂ E h hexh
  have d1 : Pr (α₁ ∧ E) h = Pr E (α₁ ∧ h) * Pr α₁ h := def_X_right α₁ E h
  have d2 : Pr (α₂ ∧ E) h = Pr E (α₂ ∧ h) * Pr α₂ h := def_X_right α₂ E h
  have d3 : Pr ((α₁ ∧ α₂) ∧ E) h = Pr (α₁ ∧ α₂) (E ∧ h) * Pr E h :=
    def_X_left (α₁ ∧ α₂) E h
  linarith

/-- **Th.(17.56.1)** π の 5 限界.
max(e₁p₁, e₂p₂) ≤ π ≤ min(e₁p₁+e₂p₂, 1−e₁(1−p₁), 1−e₂(1−p₂))
を 5 本の不等式の連言として与える。Boole 問題の「解は区間」という
Keynes の主張 (SIPTA 系 imprecise probability の先駆) の機械検証。

Keynes Prolog DB: cites(th17_56_1, th14_24_2), cites(th17_56_1, th13_4). -/
theorem th_17_56_1 (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1) :
    (Pr E (α₁ ∧ h) * Pr α₁ h ≤ Pr E h) ∧
    (Pr E (α₂ ∧ h) * Pr α₂ h ≤ Pr E h) ∧
    (Pr E h ≤ Pr E (α₁ ∧ h) * Pr α₁ h + Pr E (α₂ ∧ h) * Pr α₂ h) ∧
    (Pr E h ≤ 1 - Pr α₁ h + Pr E (α₁ ∧ h) * Pr α₁ h) ∧
    (Pr E h ≤ 1 - Pr α₂ h + Pr E (α₂ ∧ h) * Pr α₂ h) := by
  have raw := th_17_56_raw α₁ α₂ E h hexh
  have d1 : Pr (α₁ ∧ E) h = Pr E (α₁ ∧ h) * Pr α₁ h := def_X_right α₁ E h
  have d2 : Pr (α₂ ∧ E) h = Pr E (α₂ ∧ h) * Pr α₂ h := def_X_right α₂ E h
  -- 重なり項の単調性 (両方向)
  have mono2 : Pr ((α₁ ∧ α₂) ∧ E) h ≤ Pr (α₂ ∧ E) h := by
    have e : ((α₁ ∧ α₂) ∧ E) ↔ (α₁ ∧ (α₂ ∧ E)) := by tauto
    rw [ax_iii_op _ _ h e]
    exact pr_conj_le_right α₁ (α₂ ∧ E) h
  have mono1 : Pr ((α₁ ∧ α₂) ∧ E) h ≤ Pr (α₁ ∧ E) h := by
    have e : ((α₁ ∧ α₂) ∧ E) ↔ (α₂ ∧ (α₁ ∧ E)) := by tauto
    rw [ax_iii_op _ _ h e]
    exact pr_conj_le_right α₂ (α₁ ∧ E) h
  have hC0 := ax_range_lo ((α₁ ∧ α₂) ∧ E) h
  -- (iv)(v) 用: π + αᵢ(¬E)/h ≤ 1 (排反選言の範囲原理)
  have hq1 := def_IX α₁ E h        -- P(α₁∧¬E) + P(α₁∧E) = P α₁
  have hq2 := def_IX α₂ E h
  have disj1 := th_24 E (α₁ ∧ ¬E) h
  have ef1 : (E ∧ (α₁ ∧ ¬E)) ↔ False := by tauto
  rw [ax_iii_op _ _ h ef1, pr_false] at disj1
  have hub1 := ax_range_hi (E ∨ (α₁ ∧ ¬E)) h
  have disj2 := th_24 E (α₂ ∧ ¬E) h
  have ef2 : (E ∧ (α₂ ∧ ¬E)) ↔ False := by tauto
  rw [ax_iii_op _ _ h ef2, pr_false] at disj2
  have hub2 := ax_range_hi (E ∨ (α₂ ∧ ¬E)) h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-- **Th.(17.56.2)** e₁, e₂ 消去限界: π ≤ p₁ + p₂。
(56.1) の第 3 成分に範囲原理 (eᵢ ≤ 1, pᵢ ≥ 0) を代入して消去。 -/
theorem th_17_56_2 (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1) :
    Pr E h ≤ Pr E (α₁ ∧ h) + Pr E (α₂ ∧ h) := by
  have hup := (th_17_56_1 α₁ α₂ E h hexh).2.2.1
  have k1 : Pr E (α₁ ∧ h) * Pr α₁ h ≤ Pr E (α₁ ∧ h) := by
    have := mul_le_mul_of_nonneg_left (ax_range_hi α₁ h) (ax_range_lo E (α₁ ∧ h))
    simpa using this
  have k2 : Pr E (α₂ ∧ h) * Pr α₂ h ≤ Pr E (α₂ ∧ h) := by
    have := mul_le_mul_of_nonneg_left (ax_range_hi α₂ h) (ax_range_lo E (α₂ ∧ h))
    simpa using this
  linarith

/-- **Th.(17.56.3)** e₂ 消去限界: e₁p₁ ≤ π ≤ 1 − e₁ + e₁p₁。
(56.1) の第 1・第 4 成分の連言 (Keynes の「e₂ を消去」に対応)。 -/
theorem th_17_56_3 (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1) :
    (Pr E (α₁ ∧ h) * Pr α₁ h ≤ Pr E h) ∧
    (Pr E h ≤ 1 - Pr α₁ h + Pr E (α₁ ∧ h) * Pr α₁ h) :=
  ⟨(th_17_56_1 α₁ α₂ E h hexh).1, (th_17_56_1 α₁ α₂ E h hexh).2.2.2.1⟩

/-- **Th.(17.56.4)** p₂ 消去限界: π ≤ e₁p₁ + e₂。
重なり項 ≥ 0 と α₂E/h ≤ e₂ (連言上界) から。 -/
theorem th_17_56_4 (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1) :
    Pr E h ≤ Pr E (α₁ ∧ h) * Pr α₁ h + Pr α₂ h := by
  have raw := th_17_56_raw α₁ α₂ E h hexh
  have d1 : Pr (α₁ ∧ E) h = Pr E (α₁ ∧ h) * Pr α₁ h := def_X_right α₁ E h
  have hB : Pr (α₂ ∧ E) h ≤ Pr α₂ h := pr_conj_le_left α₂ E h
  have hC0 := ax_range_lo ((α₁ ∧ α₂) ∧ E) h
  linarith

/-- **Th.(17.56.5)** 原因知識独立の場合: π ≥ e₁p₁ + e₂p₂ − e₁e₂。
独立性 (α₁/α₂h = α₁/h) の下で重なり項が e₁e₂ で抑えられる。

Keynes Prolog DB: cites(th17_56_5, th17_56), cites(th17_56_5, def_x). -/
theorem th_17_56_5 (α₁ α₂ E h : Prop)
    (hexh : Pr (α₁ ∨ α₂) (E ∧ h) = 1)
    (hindep : Pr α₁ (α₂ ∧ h) = Pr α₁ h) :
    Pr E (α₁ ∧ h) * Pr α₁ h + Pr E (α₂ ∧ h) * Pr α₂ h
      - Pr α₁ h * Pr α₂ h ≤ Pr E h := by
  have raw := th_17_56_raw α₁ α₂ E h hexh
  have d1 : Pr (α₁ ∧ E) h = Pr E (α₁ ∧ h) * Pr α₁ h := def_X_right α₁ E h
  have d2 : Pr (α₂ ∧ E) h = Pr E (α₂ ∧ h) * Pr α₂ h := def_X_right α₂ E h
  have monoC : Pr ((α₁ ∧ α₂) ∧ E) h ≤ Pr (α₁ ∧ α₂) h :=
    pr_conj_le_left (α₁ ∧ α₂) E h
  have hmul : Pr (α₁ ∧ α₂) h = Pr α₁ (α₂ ∧ h) * Pr α₂ h := def_X_left α₁ α₂ h
  rw [hindep] at hmul
  linarith

/-! ## Ch.17 §2: n 原因一般化 (57) 系列 — List 帰納法 -/

/-- **n 項連言** (Phase 4 再掲、Arai 拡張定義)。 -/
def bigAnd : List Prop → Prop
  | [] => True
  | p :: rest => p ∧ bigAnd rest

/-- **n 項選言** (Arai 拡張定義)。Keynes の α₁ + α₂ + … + αₙ。 -/
def bigOr : List Prop → Prop
  | [] => False
  | p :: rest => p ∨ bigOr rest

/-- **確率の n 項和** (Phase 4 再掲、Arai 拡張定義)。 -/
noncomputable def sumPr : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr p h + sumPr rest h

/-- **順序型重なり和** (Arai 拡張定義)。
overlapSum [p₁,…,pₙ] h = Σₖ pₖ ∧ (pₖ₊₁ ∨ … ∨ pₙ) /h。
Keynes (57) の補正項 Σ α₁…α_{k−1}αₖ/h の順序型対応物。 -/
noncomputable def overlapSum : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr (p ∧ bigOr rest) h + overlapSum rest h

/-- **順序型包除恒等式** (Arai 補題): (α₁+…+αₙ)/h = Σ αₖ/h − overlapSum。
(24) 加法定理の n 項展開。List 帰納法 (H8 の判定点の一つ)。 -/
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

/-- 分配補題 (Arai 補題): (Σ 選言) ∧ E の List 版分配律。 -/
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

/-- 選言の単調性 (Arai 補題): p ∈ l → p/h ≤ (bigOr l)/h。 -/
theorem pr_le_bigOr (h p : Prop) : ∀ (l : List Prop), p ∈ l →
    Pr p h ≤ Pr (bigOr l) h := by
  intro l
  induction l with
  | nil => intro hmem; cases hmem
  | cons q rest ih =>
      intro hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · subst heq
        simp only [bigOr]
        have h24 := th_24 p (bigOr rest) h
        have hub := pr_conj_le_right p (bigOr rest) h
        linarith
      · simp only [bigOr]
        have h24 := th_24 q (bigOr rest) h
        have hub := pr_conj_le_left q (bigOr rest) h
        have hih := ih hmem'
        linarith

/-- **Th.(17.57)** n 原因への一般化 (Boole 問題 VI).
E が原因リスト causes を通じてのみ生起するとき、
π = Σₖ (αₖ∧E)/h − overlapSum。各項は def_X_right により eₖpₖ に分解される
(th_17_57_2 参照)。

Keynes Prolog DB: cites(th17_57, th17_56), cites(th17_57, th14_24),
cites(th17_57, def_x).

## 検証対象
- List 帰納法 ×2 (incl_excl + bigOr_map_and) を経由した後も、
  #print axioms が {def_IX, ax_iii_op, ax_iii_true?, def_X_left} + floor に
  とどまるか (H8)。 -/
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

/-- **Th.(17.57.2)** n 原因下界: 各原因項 eₖpₖ ≤ π。
(56.1) の max 下界の n 項一般化 (List 帰属で表現)。 -/
theorem th_17_57_2 (causes : List Prop) (E h : Prop)
    (hexh : Pr (bigOr causes) (E ∧ h) = 1)
    (α : Prop) (hmem : α ∈ causes) :
    Pr E (α ∧ h) * Pr α h ≤ Pr E h := by
  have key : Pr ((bigOr causes) ∧ E) h = Pr (bigOr causes) (E ∧ h) * Pr E h :=
    def_X_left (bigOr causes) E h
  rw [hexh, one_mul] at key
  have hmem' : (α ∧ E) ∈ causes.map (fun p => p ∧ E) :=
    List.mem_map.mpr ⟨α, hmem, rfl⟩
  have hle := pr_le_bigOr h (α ∧ E) (causes.map (fun p => p ∧ E)) hmem'
  have hre : Pr (bigOr (causes.map (fun p => p ∧ E))) h
      = Pr ((bigOr causes) ∧ E) h :=
    ax_iii_op _ _ h (bigOr_map_and E causes)
  have hval : Pr (α ∧ E) h = Pr E (α ∧ h) * Pr α h := def_X_right α E h
  rw [hre, key] at hle
  rw [hval] at hle
  exact hle

/-- **Th.(17.57.6)** 事後確率 (Boole 問題 IX): αᵣ/Eh = eᵣpᵣ / (E/h)。
Bayes 反転 th_14_38_full の直接の系。

Keynes Prolog DB: cites(th17_57_6, th17_57), cites(th17_57_6, def_x). -/
theorem th_17_57_6 (αr E h : Prop) (hE : Pr E h ≠ 0) :
    Pr αr (E ∧ h) = Pr E (αr ∧ h) * Pr αr h / Pr E h :=
  th_14_38_full αr E h hE

/-! ## Ch.17 §2: Laplace 継承則 (58) 系列 -/

/-- **n 項連鎖積** (Arai 拡張定義).
chainProd [p₁,…,pₙ] h = p₁/(p₂…pₙ∧h) · p₂/(p₃…pₙ∧h) · … · pₙ/h。
Keynes の y_{n} = p₁p₂…pₙ (各 pₖ は先行成功を条件とする成功確率) の厳密化。 -/
noncomputable def chainProd : List Prop → Prop → ℝ
  | [], _ => 1
  | p :: rest, h => Pr p (bigAnd rest ∧ h) * chainProd rest h

/-- **Th.(17.58)** Laplace 継承則の核心 = n 項連鎖律.
(p₁∧…∧pₙ)/h = chainProd。Def.X の n 回反復であり、Keynes が Laplace 継承則の
導出に用いる「連鎖」そのもの。

Keynes Prolog DB: cites(th17_58, th14_38), cites(th17_58, def_x).

## 検証対象 (H7 の判定点)
- kernel 経路は {ax_iii_true, def_X_left} + floor のみと予測。
  DB の cites(th17_58, th14_38) (Bayes 反転) は連鎖律には不要
  → **Mode S 第 4 例候補**。 -/
theorem th_17_58 (h : Prop) (l : List Prop) :
    Pr (bigAnd l) h = chainProd l h := by
  induction l with
  | nil =>
      simp only [bigAnd, chainProd]
      exact ax_iii_true h
  | cons p rest ih =>
      simp only [bigAnd, chainProd]
      rw [def_X_left p (bigAnd rest) h, ih]

/-- **Th.(17.58.1)** 不変原因: 各段の成功が確実 (各 pₖ = 1) なら連鎖積 = 1。
「不変原因のみなら 1 回の観測で確実性」の Keynes 主張の連鎖積側。 -/
theorem th_17_58_1 (h : Prop) : ∀ (l : List Prop),
    (∀ p ∈ l, ∀ (e : Prop), Pr p e = 1) → chainProd l h = 1 := by
  intro l
  induction l with
  | nil => intro _; norm_num [chainProd]
  | cons p rest ih =>
      intro hcert
      simp only [chainProd]
      rw [hcert p (by simp) (bigAnd rest ∧ h),
          ih (fun q hq e => hcert q (List.mem_cons_of_mem p hq) e)]
      norm_num

/-- 連鎖積の非負性 (Arai 補題、範囲原理下)。 -/
theorem chainProd_nonneg (h : Prop) (l : List Prop) : 0 ≤ chainProd l h := by
  induction l with
  | nil => norm_num [chainProd]
  | cons p rest ih =>
      simp only [chainProd]
      exact mul_nonneg (ax_range_lo p (bigAnd rest ∧ h)) ih

/-- **Th.(17.58.2)** 連鎖積の単調非増加: 観測を 1 段追加すると y は増えない。
y_{n+1} ≤ y_n (範囲原理下)。Keynes の「y_{n+1} − y_n の符号と減衰」主張の
機械検証可能部分。 -/
theorem th_17_58_2 (h : Prop) (p : Prop) (l : List Prop) :
    chainProd (p :: l) h ≤ chainProd l h := by
  have hx := ax_range_hi p (bigAnd l ∧ h)
  have hc := chainProd_nonneg h l
  have key : 0 ≤ chainProd l h * (1 - Pr p (bigAnd l ∧ h)) :=
    mul_nonneg hc (by linarith)
  simp only [chainProd]
  nlinarith [key]

/-- **Th.(17.58.3)** 不変原因の事後確率の収束レート下界.
事前確率 a の不変原因 (毎回成功) と、n 回連続成功の確率が rⁿ に減衰する
対立原因の 2 仮説 Bayes (Th.(14.48)) において、n 回成功後の不変原因の
事後確率は t_n = a/(a + (1−a)rⁿ) であり、
  (a − (1−a)rⁿ)/a ≤ t_n
が成り立つ。0 ≤ r < 1 なら右辺 → 1 (n → ∞)、すなわち t_n → 1。

## 検証対象 (H5 の判定点)
- 本定理は有限 n の**純代数**であり、#print axioms は floor + 0 個の
  Keynes 公理と予測。極限移行 (rⁿ → 0) は substrate (Archimedes 性) の
  営みであって、公理監査には現れない — monotone convergence が「新規
  Mode C として surface する」という引き継ぎ書の予測は、H1 (帰納法) と
  同型の反証を受けると予測する。収束の Keynes 的内容はこのレート
  不等式に尽きている。 -/
theorem th_17_58_3 (a r : ℝ) (n : ℕ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hr0 : 0 ≤ r) :
    (a - (1 - a) * r ^ n) / a ≤ a / (a + (1 - a) * r ^ n) := by
  have hterm : 0 ≤ (1 - a) * r ^ n :=
    mul_nonneg (by linarith) (pow_nonneg hr0 n)
  have hD : 0 < a + (1 - a) * r ^ n := by linarith
  have hane : a ≠ 0 := ne_of_gt ha
  have hDne : a + (1 - a) * r ^ n ≠ 0 := ne_of_gt hD
  -- 分子の非負性: a² − (a−t)(a+t) = t² ≥ 0 (t := (1−a)rⁿ)
  have hnum : 0 ≤ a * a - (a - (1 - a) * r ^ n) * (a + (1 - a) * r ^ n) := by
    nlinarith [sq_nonneg ((1 - a) * r ^ n)]
  have hden : 0 < (a + (1 - a) * r ^ n) * a := mul_pos hD ha
  have hfrac : 0 ≤ (a * a - (a - (1 - a) * r ^ n) * (a + (1 - a) * r ^ n))
      / ((a + (1 - a) * r ^ n) * a) := div_nonneg hnum (le_of_lt hden)
  -- 差の通分恒等式 (div_le_div_iff の版差を回避する手組み経路)
  have heq : a / (a + (1 - a) * r ^ n) - (a - (1 - a) * r ^ n) / a
      = (a * a - (a - (1 - a) * r ^ n) * (a + (1 - a) * r ^ n))
        / ((a + (1 - a) * r ^ n) * a) := by
    first
      | (field_simp; ring)
      | field_simp
  rw [← heq] at hfrac
  linarith

end Keynes

/-! ## 監査クエリ (Phase 5 新規) -/

#check @Keynes.th_14_49
#check @Keynes.th_14_49_infl
#check @Keynes.th_17_56_raw
#check @Keynes.th_17_56
#check @Keynes.th_17_56_1
#check @Keynes.th_17_56_2
#check @Keynes.th_17_56_3
#check @Keynes.th_17_56_4
#check @Keynes.th_17_56_5
#check @Keynes.th_17_57
#check @Keynes.th_17_57_2
#check @Keynes.th_17_57_6
#check @Keynes.th_17_58
#check @Keynes.th_17_58_1
#check @Keynes.th_17_58_2
#check @Keynes.th_17_58_3

-- Kernel 依存. 注目点:
--   th_14_49       : def_X_left + ax_iii_op のみ (DB の th14_24_2/th14_41_2 は不要?)
--   th_17_56       : ★ H6 判定点: 4 公理同時 surface (def_IX, ax_iii_op,
--                    def_X_left, def_X_right) か
--   th_17_56_1     : 上記 + 範囲原理 2 本 + ax_iii_true? (pr_false 経由では
--                    ax_iii_true は不要のはず — def_IX + ax_iii_op で閉じる)
--   th_17_57       : ★ H8 判定点: List 帰納法 ×2 経由後の公理集合
--   th_17_58       : ★ H7 判定点: {ax_iii_true, def_X_left} + floor のみか
--                    (DB 引用の th14_38 が不要なら Mode S 第 4 例)
--   th_17_58_3     : ★ H5 判定点: floor + Keynes 公理 0 と予測
#print axioms Keynes.th_14_49
#print axioms Keynes.th_14_49_infl
#print axioms Keynes.th_17_56_raw
#print axioms Keynes.th_17_56
#print axioms Keynes.th_17_56_1
#print axioms Keynes.th_17_56_2
#print axioms Keynes.th_17_56_3
#print axioms Keynes.th_17_56_4
#print axioms Keynes.th_17_56_5
#print axioms Keynes.th_17_57
#print axioms Keynes.th_17_57_2
#print axioms Keynes.th_17_57_6
#print axioms Keynes.th_17_58
#print axioms Keynes.th_17_58_1
#print axioms Keynes.th_17_58_2
#print axioms Keynes.th_17_58_3

-- 回帰テスト (再掲定理)
#print axioms Keynes.th_24
#print axioms Keynes.pr_false
#print axioms Keynes.th_14_38_full
#print axioms Keynes.incl_excl
#print axioms Keynes.pr_le_bigOr
#print axioms Keynes.chainProd_nonneg
