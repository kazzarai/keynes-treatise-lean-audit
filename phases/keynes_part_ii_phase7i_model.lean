/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7i model
#
# 新井一成・Claude共著、2026年10月20日
# **外延版公理群 (Pr : Prop → Prop → ℝ) の但し書き点検 — 二値モデルによる無矛盾性と一意性**
#
# ## 問い (依頼 B10)
#   第12章 §5 公理 (i) (folio 135) は「h が矛盾する連言でない (h is not an
#   inconsistent conjunction) とき、a と h の間に確率関係が一つだけ存在する」と
#   但し書きを付ける。外延版の各 phase (2, 3a–3d, 4, 5, 6a, 6b, 7a–7i, 8d) は
#   `ax_iii_true (h : Prop) : Pr True h = 1` をこの但し書きなしに、任意の h
#   (矛盾する h = False を含む) について置く。内包版 phase6c では同種の但し書き
#   落ちから False が導けた (B09 で修復中)。外延版でも矛盾が出るか、出ないか。
#
# ## 答え (本ファイルの定理)
#   出ない。候補モデル
#     PrM p h := if h then (if p then 1 else 0) else (if p then 1 else 0)
#   (h の真偽によらず p の真理値で評価する二値モデル) が
#     (1) phase7i の 7 公理文 (ax_iii_op, ax_iii_true, def_IX, def_X_left,
#         def_X_right, ax_range_lo, ax_range_hi)                → §1
#     (2) phase2 の Pr を除く公理文 14 本 = 7i と共通の 5 本 (ax_iii_op,
#         ax_iii_true, def_IX, def_X_left, def_X_right) + 9 本 (ax_ii,
#         ax_iva_mul, ax_iva_add, ax_ivb, ax_ivc, ax_v, ax_vi, def_XI, def_XII)。
#         ax_range_lo/hi は phase2 に無い                       → §2
#     (3) phase6a/6b の ax_iii_ev、phase8d の V 公理 3 本 (V := 0)  → §3
#   をすべて満たす (`ext7i_consistent`, `ext2_consistent`)。満たさない公理は無い。
#   (1)–(3) の和集合 (Pr の公理 17 本 + V の公理 3 本) を一本にまとめたものが
#   `ext_all_consistent` (§5)。
#   さらに ax_iii_true + def_IX の 2 本から、任意の Pr は PrM に一致する
#   (`ext_forced`, 一意性)。ax_iii_op は公理として要らない: 任意の
#   Pr : Prop → Prop → ℝ について (p ↔ q) → Pr p h = Pr q h は propext の系である
#   (`op_of_propext`)。2 本のどちらも落とせない (`ext_forced_needs_true`:
#   Pr ≡ 0 は op と def_IX を満たすが PrM と異なる; `ext_forced_needs_IX`:
#   Pr ≡ 1 は op と ax_iii_true を満たすが PrM と異なる)。
#   この一意性は ax_iii_true と def_IX を共に含む phase (2, 3a–3d, 4, 5, 6a, 6b,
#   7a–7c, 7g, 7h, 7i) に限って成り立つ。phase7d (def_X_left/right + ax_range_lo
#   のみ)・phase7e (ax_iii_op のみ)・pilot (def_IX はあるが ax_iii_true が無い)
#   は該当せず、phase7d には前提で値が変わるモデル PrD p h := if h ∧ p then 1
#   else 0 がある (`ext7d_premiss_matters`)。7f という phase は存在しない。
#   phase4 の `th_15_degeneracy` (Pr α h ∈ {0,1}) は一意性の値域側の言い換えであり、
#   phase4 `Naive.collapse` (Ax.(前) 素朴形 ∃ α h, Pr α h = p/n を加えると False)
#   はこの一意モデルが中間値を一切持たないことの帰結である。
#
# ## 境界記録 (定理にしない)
#   このモデルは Keynes の意図と二点で異なる。第一に、Keynes は公理 (i) で
#   「矛盾した前提 h に対しては確率関係が存在しない」と言う (folio 135:
#   "Thus any conclusion a bears to any consistent premiss h one and only one
#   relation of probability") が、PrM は h = False に対しても値を返し、
#   PrM True False = 1、PrM p False = PrM p True である (`PrM_inconsistent_premiss`)。
#   外延版では Pr が全域関数なので、但し書きを落としても矛盾は生じず、
#   「存在しないはずの関係」に値が付くだけである。第二に、より重い違いとして、
#   ax_iii_true と def_IX を共に含む phase では外延版のモデルは PrM に限られる
#   (`ext_forced`) ため、前提 h は確率の値に一切寄与しない
#   (`ext_premiss_irrelevant`: Pr p h = Pr p k)。Keynes の
#   確率関係は前提に相対的 (a/h と a/hh₁ は一般に異なる、第6章・第14章) で
#   あり、中間の値 (第15章の p/n) を取る。外延版が矛盾しないのは、その内容が
#   「結論の真理値」に退化しているからであって、Keynes の体系が保たれている
#   からではない。これは CLAUDE.md 不変条件 3 (第I部・第III部を IProp 上に
#   置く理由) の、確率関係そのものについての確認である。したがって
#   「但し書き落ち」の点検結果は: 外延版 — 無矛盾だが退化 (本ファイル);
#   内包版 — 但し書きが必要 (B09)。
#
# ## 実行方法 (Mac ローカル)
#   lake env lean phases/keynes_part_ii_phase7i_model.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KeynesExtModel

open Classical

/-! ## §0 候補モデル -/

/-- 依頼 B10 の候補モデル。h の真偽で分岐するが両枝は同じ (p の真理値)。 -/
noncomputable def PrM (p h : Prop) : ℝ :=
  if h then (if p then 1 else 0) else (if p then 1 else 0)

/-- 両枝が同じなので h は消える。 -/
theorem PrM_eq (p h : Prop) : PrM p h = if p then 1 else 0 := by
  simp [PrM]

/-! ## §1 phase7i の 7 公理文 (公理 Pr 自体は PrM が担う) -/

/-- ax_iii_op: `(p ↔ q) → Pr p h = Pr q h`. -/
theorem m_ax_iii_op (p q h : Prop) : (p ↔ q) → PrM p h = PrM q h := by
  intro e
  simp only [PrM_eq, e]

/-- ax_iii_true: `Pr True h = 1` (但し書きなし、h = False を含む)。 -/
theorem m_ax_iii_true (h : Prop) : PrM True h = 1 := by
  simp [PrM_eq]

/-- def_IX: `Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h`. -/
theorem m_def_IX (p q h : Prop) :
    PrM (p ∧ ¬q) h + PrM (p ∧ q) h = PrM p h := by
  simp only [PrM_eq]
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- def_X_left: `Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h`. -/
theorem m_def_X_left (p q h : Prop) :
    PrM (p ∧ q) h = PrM p (q ∧ h) * PrM q h := by
  simp only [PrM_eq]
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- def_X_right: `Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h`. -/
theorem m_def_X_right (p q h : Prop) :
    PrM (p ∧ q) h = PrM q (p ∧ h) * PrM p h := by
  simp only [PrM_eq]
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- ax_range_lo: `0 ≤ Pr α h`. -/
theorem m_ax_range_lo (α h : Prop) : 0 ≤ PrM α h := by
  simp only [PrM_eq]
  split_ifs <;> norm_num

/-- ax_range_hi: `Pr α h ≤ 1`. -/
theorem m_ax_range_hi (α h : Prop) : PrM α h ≤ 1 := by
  simp only [PrM_eq]
  split_ifs <;> norm_num

/-- **受け入れ条件 1・3 (第1回)**: phase7i の公理文 7 本を同時に満たす
`Pr : Prop → Prop → ℝ` が存在する (証人 PrM)。 -/
theorem ext7i_consistent :
    ∃ Pr : Prop → Prop → ℝ,
      (∀ p q h : Prop, (p ↔ q) → Pr p h = Pr q h) ∧
      (∀ h : Prop, Pr True h = 1) ∧
      (∀ p q h : Prop, Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h) ∧
      (∀ p q h : Prop, Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h) ∧
      (∀ p q h : Prop, Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h) ∧
      (∀ α h : Prop, 0 ≤ Pr α h) ∧
      (∀ α h : Prop, Pr α h ≤ 1) :=
  ⟨PrM, m_ax_iii_op, m_ax_iii_true, m_def_IX, m_def_X_left, m_def_X_right,
    m_ax_range_lo, m_ax_range_hi⟩

/-! ## §2 phase2 の Pr を除く公理文 14 本 (7i と共通の 5 本 + 9 本)

phase2 の公理は `Pr` を除いて 14 本: 7i と共通の 5 本 (ax_iii_op, ax_iii_true,
def_IX, def_X_left, def_X_right) と、phase2 だけの 9 本 (ax_ii, ax_iva_mul,
ax_iva_add, ax_ivb, ax_ivc, ax_v, ax_vi, def_XI, def_XII)。ax_range_lo/hi は
phase2 に無い。 -/

/-- Def.VIII (等値) を PrM で読んだもの。phase2 の `KEq` と同じ文。 -/
def KEqM (α β h : Prop) : Prop := PrM β (α ∧ h) = 1 ∧ PrM α (β ∧ h) = 1

/-- ax_ii: `KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)`. 前提は使わずに閉じる
(PrM は前提を見ないため)。 -/
theorem m_ax_ii (α β h c : Prop) :
    KEqM α β h → PrM c (α ∧ h) = PrM c (β ∧ h) := by
  intro _
  simp only [PrM_eq]

/-- ax_iva_mul: `P * Q = Q * P`. -/
theorem m_ax_iva_mul (P Q : ℝ) : P * Q = Q * P := mul_comm P Q

/-- ax_iva_add: `P + Q = Q + P`. -/
theorem m_ax_iva_add (P Q : ℝ) : P + Q = Q + P := add_comm P Q

/-- ax_ivb: `0 < Q → P < P + Q`. -/
theorem m_ax_ivb (P Q : ℝ) : 0 < Q → P < P + Q := fun hQ => lt_add_of_pos_right P hQ

/-- ax_ivc: `P + Q = P + R → Q = R`. -/
theorem m_ax_ivc (P Q R : ℝ) : P + Q = P + R → Q = R := fun e => add_left_cancel e

/-- ax_v: `(P + Q) + (R + S) = (P + R) + (Q + S)`. -/
theorem m_ax_v (P Q R S : ℝ) : (P + Q) + (R + S) = (P + R) + (Q + S) := by ring

/-- ax_vi: `P * (R + S) = P * R + P * S`. -/
theorem m_ax_vi (P R S : ℝ) : P * (R + S) = P * R + P * S := mul_add P R S

/-- def_XI: `Q ≠ 0 → P * Q = R → P = R / Q`. -/
theorem m_def_XI (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q :=
  fun e => eq_div_of_mul_eq hQ e

/-- def_XII: `P + Q = R → P = R - Q`. -/
theorem m_def_XII (P Q R : ℝ) : P + Q = R → P = R - Q := fun e => eq_sub_of_add_eq e

/-- **受け入れ条件 2・3 (第1回)**: phase2 の Pr を除く公理文 14 本 (ax_ii は
Def.VIII を展開した形) を同時に満たす `Pr` が存在する (証人 PrM)。満たさない
公理は無い。 -/
theorem ext2_consistent :
    ∃ Pr : Prop → Prop → ℝ,
      (∀ α β h c : Prop,
        (Pr β (α ∧ h) = 1 ∧ Pr α (β ∧ h) = 1) → Pr c (α ∧ h) = Pr c (β ∧ h)) ∧
      (∀ p q h : Prop, (p ↔ q) → Pr p h = Pr q h) ∧
      (∀ h : Prop, Pr True h = 1) ∧
      (∀ P Q : ℝ, P * Q = Q * P) ∧
      (∀ P Q : ℝ, P + Q = Q + P) ∧
      (∀ P Q : ℝ, 0 < Q → P < P + Q) ∧
      (∀ P Q R : ℝ, P + Q = P + R → Q = R) ∧
      (∀ P Q R S : ℝ, (P + Q) + (R + S) = (P + R) + (Q + S)) ∧
      (∀ P R S : ℝ, P * (R + S) = P * R + P * S) ∧
      (∀ p q h : Prop, Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h) ∧
      (∀ p q h : Prop, Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h) ∧
      (∀ p q h : Prop, Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h) ∧
      (∀ P Q R : ℝ, Q ≠ 0 → P * Q = R → P = R / Q) ∧
      (∀ P Q R : ℝ, P + Q = R → P = R - Q) :=
  ⟨PrM, m_ax_ii, m_ax_iii_op, m_ax_iii_true, m_ax_iva_mul, m_ax_iva_add, m_ax_ivb,
    m_ax_ivc, m_ax_v, m_ax_vi, m_def_IX, m_def_X_left, m_def_X_right, m_def_XI,
    m_def_XII⟩

/-! ## §3 他の外延版 phase にある追加公理 (6a/6b の ax_iii_ev、8d の V 公理) -/

/-- ax_iii_ev (phase6a/6b): `(h ↔ k) → Pr p h = Pr p k`. -/
theorem m_ax_iii_ev (p h k : Prop) : (h ↔ k) → PrM p h = PrM p k := by
  intro _
  simp only [PrM_eq]

/-- phase8d の重み V をゼロ定数で読む。 -/
noncomputable def VM (_a _h : Prop) : ℝ := 0

/-- ax_vi_mono (phase8d): `V a h ≤ V a (h₁ ∧ h)`. -/
theorem m_ax_vi_mono (a h h₁ : Prop) : VM a h ≤ VM a (h₁ ∧ h) := le_refl _

/-- ax_vi_compl (phase8d): `V a h = V (¬a) h`. -/
theorem m_ax_vi_compl (a h : Prop) : VM a h = VM (¬a) h := rfl

/-- ax_vi_equiv (phase8d): `Pr a (b ∧ h) = 1 → Pr b (a ∧ h) = 1 → V a h = V b h`. -/
theorem m_ax_vi_equiv (a b h : Prop) :
    PrM a (b ∧ h) = 1 → PrM b (a ∧ h) = 1 → VM a h = VM b h := fun _ _ => rfl

/-! ## §4 一意性: ax_iii_true と def_IX を共に含む phase では、モデルは PrM に限る

適用範囲: phase 2, 3a–3d, 4, 5, 6a, 6b, 7a–7c, 7g, 7h, 7i (ax_iii_true と def_IX を
共に置く phase)。phase7d (def_X_left/right + ax_range_lo のみ)、phase7e
(ax_iii_op のみ)、pilot (def_IX はあるが ax_iii_true が無い)、phase8d (Pr の
公理は無く V の公理のみ) は該当しない。7f という phase は存在しない。 -/

/-- **受け入れ条件 1 (第2回)**: ax_iii_op は公理として要らない。任意の
`Pr : Prop → Prop → ℝ` について `(p ↔ q) → Pr p h = Pr q h` は propext の系
(`p ↔ q` から `p = q` が出るので、`Pr p h` と `Pr q h` は同じ項)。 -/
theorem op_of_propext (Pr : Prop → Prop → ℝ) (p q h : Prop) (e : p ↔ q) :
    Pr p h = Pr q h := by
  rw [propext e]

/-- ax_iii_true + def_IX の 2 本だけで、任意のモデル Pr は PrM に一致する
(ax_iii_op は `op_of_propext` で賄う)。証明は phase4 `pr_false` +
`th_15_degeneracy` と同じ経路 (def_IX を (False, False) に特殊化して
Pr False h = 0、あとは p の場合分け)。 -/
theorem ext_forced (Pr : Prop → Prop → ℝ)
    (h_true : ∀ h : Prop, Pr True h = 1)
    (h_IX : ∀ p q h : Prop, Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h) :
    ∀ p h : Prop, Pr p h = PrM p h := by
  intro p h
  have hF : Pr False h = 0 := by
    have step := h_IX False False h
    rw [op_of_propext Pr (False ∧ ¬False) False h (by tauto),
        op_of_propext Pr (False ∧ False) False h (by tauto)] at step
    linarith
  rw [PrM_eq]
  by_cases hp : p
  · rw [if_pos hp, op_of_propext Pr p True h (by tauto), h_true]
  · rw [if_neg hp, op_of_propext Pr p False h (by tauto), hF]

/-- 系: ax_iii_true と def_IX を共に含む phase では、どのモデルでも前提は値に
寄与しない (Pr p h = Pr p k)。 -/
theorem ext_premiss_irrelevant (Pr : Prop → Prop → ℝ)
    (h_true : ∀ h : Prop, Pr True h = 1)
    (h_IX : ∀ p q h : Prop, Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h)
    (p h k : Prop) : Pr p h = Pr p k := by
  rw [ext_forced Pr h_true h_IX p h, ext_forced Pr h_true h_IX p k, PrM_eq, PrM_eq]

/-- 境界記録の定量形: 公理 (i) が除外する h = False でも PrM は値を持ち、
しかも h = True のときと同じ値である。 -/
theorem PrM_inconsistent_premiss (p : Prop) :
    PrM p False = PrM p True ∧ PrM True False = 1 := by
  constructor
  · simp only [PrM_eq]
  · simp [PrM_eq]

/-! ### §4.1 必要性の反例 (受け入れ条件 2、第2回)

`ext_forced` の前提 2 本はどちらも落とせない。落とした側の反例を定理として残す。 -/

/-- 零定数モデル。ax_iii_true を落としたときの反例。 -/
noncomputable def Pr0 (_p _h : Prop) : ℝ := 0

/-- 壱定数モデル。def_IX を落としたときの反例。 -/
noncomputable def Pr1 (_p _h : Prop) : ℝ := 1

/-- ax_iii_true を落とすと一意性は失われる: Pr ≡ 0 は ax_iii_op と def_IX を
満たすが PrM と異なる (Pr0 True True = 0 ≠ 1 = PrM True True)。 -/
theorem ext_forced_needs_true :
    (∀ p q h : Prop, (p ↔ q) → Pr0 p h = Pr0 q h) ∧
    (∀ p q h : Prop, Pr0 (p ∧ ¬q) h + Pr0 (p ∧ q) h = Pr0 p h) ∧
    ∃ p h : Prop, Pr0 p h ≠ PrM p h :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ => by simp [Pr0],
    ⟨True, True, by simp [Pr0, PrM_eq]⟩⟩

/-- def_IX を落とすと一意性は失われる: Pr ≡ 1 は ax_iii_op と ax_iii_true を
満たすが PrM と異なる (Pr1 False True = 1 ≠ 0 = PrM False True)。 -/
theorem ext_forced_needs_IX :
    (∀ p q h : Prop, (p ↔ q) → Pr1 p h = Pr1 q h) ∧
    (∀ h : Prop, Pr1 True h = 1) ∧
    ∃ p h : Prop, Pr1 p h ≠ PrM p h :=
  ⟨fun _ _ _ _ => rfl, fun _ => rfl, ⟨False, True, by simp [Pr1, PrM_eq]⟩⟩

/-- `ext_forced` から h_true を外した文は偽である (反例 Pr0)。 -/
theorem ext_forced_fails_without_true :
    ¬ ∀ Pr : Prop → Prop → ℝ,
      (∀ p q h : Prop, Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h) →
      ∀ p h : Prop, Pr p h = PrM p h := by
  intro H
  have := H Pr0 ext_forced_needs_true.2.1 True True
  simp [Pr0, PrM_eq] at this

/-- `ext_forced` から h_IX を外した文は偽である (反例 Pr1)。 -/
theorem ext_forced_fails_without_IX :
    ¬ ∀ Pr : Prop → Prop → ℝ,
      (∀ h : Prop, Pr True h = 1) →
      ∀ p h : Prop, Pr p h = PrM p h := by
  intro H
  have := H Pr1 ext_forced_needs_IX.2.1 False True
  simp [Pr1, PrM_eq] at this

/-! ### §4.2 適用範囲外の phase: phase7d には前提で値が変わるモデルがある
(受け入れ条件 3、第2回) -/

/-- phase7d 用のモデル: 前提 h と結論 p がともに真のときだけ 1。 -/
noncomputable def PrD (p h : Prop) : ℝ := if h ∧ p then 1 else 0

/-- def_X_left を PrD が満たす。 -/
theorem d_def_X_left (p q h : Prop) :
    PrD (p ∧ q) h = PrD p (q ∧ h) * PrD q h := by
  simp only [PrD]
  by_cases hp : p <;> by_cases hq : q <;> by_cases hh : h <;> simp [hp, hq, hh]

/-- def_X_right を PrD が満たす。 -/
theorem d_def_X_right (p q h : Prop) :
    PrD (p ∧ q) h = PrD q (p ∧ h) * PrD p h := by
  simp only [PrD]
  by_cases hp : p <;> by_cases hq : q <;> by_cases hh : h <;> simp [hp, hq, hh]

/-- ax_range_lo を PrD が満たす。 -/
theorem d_ax_range_lo (α h : Prop) : 0 ≤ PrD α h := by
  simp only [PrD]
  split_ifs <;> norm_num

/-- PrD は ax_iii_true を満たさない (PrD True False = 0)。phase7d が ax_iii_true
を置かないからこそ、このモデルが許される。 -/
theorem PrD_not_ax_iii_true : PrD True False ≠ 1 := by
  simp [PrD]

/-- **受け入れ条件 3 (第2回)**: phase7d の公理 3 本 (def_X_left, def_X_right,
ax_range_lo) を満たし、かつ前提で値が変わる Pr が存在する (証人 PrD:
PrD True True = 1 ≠ 0 = PrD True False)。したがって `ext_forced` と
`ext_premiss_irrelevant` は phase7d には及ばない。 -/
theorem ext7d_premiss_matters :
    ∃ Pr : Prop → Prop → ℝ,
      (∀ p q h : Prop, Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h) ∧
      (∀ p q h : Prop, Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h) ∧
      (∀ α h : Prop, 0 ≤ Pr α h) ∧
      ∃ p h k : Prop, Pr p h ≠ Pr p k :=
  ⟨PrD, d_def_X_left, d_def_X_right, d_ax_range_lo,
    ⟨True, True, False, by simp [PrD]⟩⟩

/-! ## §5 束ね: 外延版の公理の和集合 (受け入れ条件 5、第2回)

§1–§3 に現れた Pr の公理文の和集合 (phase2 の 14 本 + ax_range_lo/hi +
ax_iii_ev = 17 本) と phase8d の V の公理 3 本を、一組の証人 (PrM, VM) で
同時に満たす。 -/

theorem ext_all_consistent :
    ∃ (Pr V : Prop → Prop → ℝ),
      -- phase2 の 14 本 (ax_ii は Def.VIII を展開した形)
      (∀ α β h c : Prop,
        (Pr β (α ∧ h) = 1 ∧ Pr α (β ∧ h) = 1) → Pr c (α ∧ h) = Pr c (β ∧ h)) ∧
      (∀ p q h : Prop, (p ↔ q) → Pr p h = Pr q h) ∧
      (∀ h : Prop, Pr True h = 1) ∧
      (∀ P Q : ℝ, P * Q = Q * P) ∧
      (∀ P Q : ℝ, P + Q = Q + P) ∧
      (∀ P Q : ℝ, 0 < Q → P < P + Q) ∧
      (∀ P Q R : ℝ, P + Q = P + R → Q = R) ∧
      (∀ P Q R S : ℝ, (P + Q) + (R + S) = (P + R) + (Q + S)) ∧
      (∀ P R S : ℝ, P * (R + S) = P * R + P * S) ∧
      (∀ p q h : Prop, Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h) ∧
      (∀ p q h : Prop, Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h) ∧
      (∀ p q h : Prop, Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h) ∧
      (∀ P Q R : ℝ, Q ≠ 0 → P * Q = R → P = R / Q) ∧
      (∀ P Q R : ℝ, P + Q = R → P = R - Q) ∧
      -- 7i/4/5/6a/6b/7g の ax_range_lo/hi
      (∀ α h : Prop, 0 ≤ Pr α h) ∧
      (∀ α h : Prop, Pr α h ≤ 1) ∧
      -- 6a/6b の ax_iii_ev
      (∀ p h k : Prop, (h ↔ k) → Pr p h = Pr p k) ∧
      -- 8d の V 公理 3 本
      (∀ a h h₁ : Prop, V a h ≤ V a (h₁ ∧ h)) ∧
      (∀ a h : Prop, V a h = V (¬a) h) ∧
      (∀ a b h : Prop, Pr a (b ∧ h) = 1 → Pr b (a ∧ h) = 1 → V a h = V b h) :=
  ⟨PrM, VM, m_ax_ii, m_ax_iii_op, m_ax_iii_true, m_ax_iva_mul, m_ax_iva_add,
    m_ax_ivb, m_ax_ivc, m_ax_v, m_ax_vi, m_def_IX, m_def_X_left, m_def_X_right,
    m_def_XI, m_def_XII, m_ax_range_lo, m_ax_range_hi, m_ax_iii_ev,
    m_ax_vi_mono, m_ax_vi_compl, m_ax_vi_equiv⟩

end KeynesExtModel

/-! ## 依存公理の全数監査 -/

#print axioms KeynesExtModel.m_ax_iii_op
#print axioms KeynesExtModel.m_ax_iii_true
#print axioms KeynesExtModel.m_def_IX
#print axioms KeynesExtModel.m_def_X_left
#print axioms KeynesExtModel.m_def_X_right
#print axioms KeynesExtModel.m_ax_range_lo
#print axioms KeynesExtModel.m_ax_range_hi
#print axioms KeynesExtModel.ext7i_consistent
#print axioms KeynesExtModel.m_ax_ii
#print axioms KeynesExtModel.m_ax_iva_mul
#print axioms KeynesExtModel.m_ax_iva_add
#print axioms KeynesExtModel.m_ax_ivb
#print axioms KeynesExtModel.m_ax_ivc
#print axioms KeynesExtModel.m_ax_v
#print axioms KeynesExtModel.m_ax_vi
#print axioms KeynesExtModel.m_def_XI
#print axioms KeynesExtModel.m_def_XII
#print axioms KeynesExtModel.ext2_consistent
#print axioms KeynesExtModel.m_ax_iii_ev
#print axioms KeynesExtModel.m_ax_vi_mono
#print axioms KeynesExtModel.m_ax_vi_compl
#print axioms KeynesExtModel.m_ax_vi_equiv
#print axioms KeynesExtModel.op_of_propext
#print axioms KeynesExtModel.ext_forced
#print axioms KeynesExtModel.ext_premiss_irrelevant
#print axioms KeynesExtModel.PrM_inconsistent_premiss
#print axioms KeynesExtModel.ext_forced_needs_true
#print axioms KeynesExtModel.ext_forced_needs_IX
#print axioms KeynesExtModel.ext_forced_fails_without_true
#print axioms KeynesExtModel.ext_forced_fails_without_IX
#print axioms KeynesExtModel.d_def_X_left
#print axioms KeynesExtModel.d_def_X_right
#print axioms KeynesExtModel.d_ax_range_lo
#print axioms KeynesExtModel.PrD_not_ax_iii_true
#print axioms KeynesExtModel.ext7d_premiss_matters
#print axioms KeynesExtModel.ext_all_consistent
