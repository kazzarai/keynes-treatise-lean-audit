/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7e
#
# 新井一成・Claude共著、2026年7月9日
# **(14.42.2) 影響係数の一般置換則 — List.Perm 機構による最後の 1 本**
#
# ## 照合ソース
#   佐藤訳 p.173 (欄外 167): 「(42.2) そこで一般に項の順序をつねに交換する
#   ことができる交換規則を得る。たとえば {aᵏbcᵏdefᵏg}={bcᵏaᵏgᵏdef}, …」
#   英語原典 (Gutenberg TeX) 同旨。任意の置換の下での n 項影響係数の不変性。
#
# ## 本ファイルで追加したもの (DB ノード 1 — 台帳最後の 1 本)
#   bigAnd_perm    : 置換の下での n 項連言の同値 (List.Perm 帰納)
#   prodPr_perm    : 置換の下での確率積の不変性
#   th_14_42_2_pr  : Pr (bigAnd l) h の置換不変性
#   th_14_42_2     : InflN の置換不変性 (本体)
#
# ## 検証したい仮説
#   H31: 依存集合は {Pr, ax_iii_op} + floor のみ。List.Perm の再帰子
#        (Perm.rec) は #print axioms に現れない — C_rec の最終確認例。
#        「任意の置換」という無限族の主張が、公理コストゼロの機構
#        (帰納) だけで閉じる。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase7e.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (継承) -/

axiom Pr : Prop → Prop → ℝ

axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h

/-! ## 定義 (再掲) -/

def bigAnd : List Prop → Prop
  | [] => True
  | p :: rest => p ∧ bigAnd rest

noncomputable def prodPr : List Prop → Prop → ℝ
  | [], _ => 1
  | p :: rest, h => Pr p h * prodPr rest h

noncomputable def InflN (l : List Prop) (h : Prop) : ℝ :=
    Pr (bigAnd l) h / prodPr l h

/-! ## Perm 補題 (Arai) -/

/-- 置換の下での n 項連言の命題同値。List.Perm の 4 構成子で帰納。 -/
theorem bigAnd_perm {l l' : List Prop} (hp : l.Perm l') :
    bigAnd l ↔ bigAnd l' := by
  induction hp with
  | nil => exact Iff.rfl
  | cons x _ ih =>
      simp only [bigAnd]
      tauto
  | swap x y l =>
      simp only [bigAnd]
      tauto
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- 置換の下での確率積の不変性。 -/
theorem prodPr_perm (h : Prop) {l l' : List Prop} (hp : l.Perm l') :
    prodPr l h = prodPr l' h := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
      simp only [prodPr]
      rw [ih]
  | swap x y l =>
      simp only [prodPr]
      ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Phase 7e 新規 (台帳最後の 1 本) -/

/-- 連言確率の置換不変性 (ax_iii_op 経由)。 -/
theorem th_14_42_2_pr (h : Prop) {l l' : List Prop} (hp : l.Perm l') :
    Pr (bigAnd l) h = Pr (bigAnd l') h :=
  ax_iii_op _ _ h (bigAnd_perm hp)

/-- **Th.(14.42.2)** 影響係数の一般交換規則.
{α₁…αₙ} は項の任意の置換の下で不変。(42)(42.1) の binary/3-ary 対称性の
完全一般化。「任意の置換」は List.Perm の帰納で処理され、公理コストは
命題側の ax_iii_op のみ (H31)。 -/
theorem th_14_42_2 (h : Prop) {l l' : List Prop} (hp : l.Perm l') :
    InflN l h = InflN l' h := by
  unfold InflN
  rw [th_14_42_2_pr h hp, prodPr_perm h hp]

end Keynes

/-! ## 監査クエリ (Phase 7e) -/

#check @Keynes.bigAnd_perm
#check @Keynes.prodPr_perm
#check @Keynes.th_14_42_2_pr
#check @Keynes.th_14_42_2

-- Kernel 依存. 注目点:
--   th_14_42_2 : ★ H31 判定点 — {Pr, ax_iii_op} + floor のみか
--                (Perm.rec は現れないはず — C_rec 最終確認)
#print axioms Keynes.bigAnd_perm
#print axioms Keynes.prodPr_perm
#print axioms Keynes.th_14_42_2_pr
#print axioms Keynes.th_14_42_2
