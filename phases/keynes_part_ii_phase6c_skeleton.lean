/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 6c SKELETON
#
# 新井一成・Claude共著、2026年7月7日
# 内包移行: pedantic Ax.(iii) + Th.(12) over IProp
#
# ## 本ファイルの位置づけ
# これは**スケルトン**である。公理層 + 煙試験 2 本のみ収録し、本体実装は
# `PHASE6C_DESIGN.md` の設計に従って Phase 6c 本番で行う。
# 目的は「この公理層がコンパイルし、融合形なしで代入が回る」ことの確認。
#
# ## 核心のアイデア
# Phase 4 の縮退定理 (Finding 15) の原因は、融合形 ax_iii_op が
# 「実質的同値」(仮説依存の ↔ 証明) を受理することだった。
# 本スケルトンでは:
#   (1) 確率の項を不透明型 IProp にする (em が存在しない)
#   (2) 同値代入は KTaut (Keynes が Ax.(iii) で列挙したトートロジー図式の
#       閉じた生成子) で認証されたものに限る
#   (3) Th.(12) を経由して代入を回す
# これにより実質的同値の混入経路が型レベルで遮断される。
#
# ## 検証したい仮説 (Phase 6c 本番)
#   H15: 縮退定理の内包版 `∀ p h, PrI p h = 0 ∨ PrI p h = 1` は導出不能。
#        (証明: 構文的独立性の直接証明ではなく、値 1/2 を取る Popper 関数
#         モデルの構成による反例証明書 — PHASE6C_DESIGN.md §4)
#   H16: Ax.(前) の内包版は無矛盾に追加できる (Phase 4 Intensional の再現)。
#   H17: th_12_i は def_IX_i + ktaut_subst から**定理として**証明できる
#        (Phase 6b の th_13_12 の証明構造の内包版)。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase6c_skeleton.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KeynesI

/-! ## 内包的キャリアと結合子 (不透明型 — em なし) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

/-- 内包的確率関係 (プリミティブ)。 -/
axiom PrI : IProp → IProp → ℝ

/-! ## Keynes 操作公理群の内包版 -/

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-! ## Pedantic Ax.(iii): 列挙されたトートロジー図式 -/

/-- Keynes 論証的トートロジー述語。生成子は**閉じた図式のみ**
(真理条件への言及を持つ生成子を追加してはならない — 追加すれば
実質的同値が再侵入し縮退が復活する。PHASE6C_DESIGN.md §3 の規律)。 -/
axiom KTaut : IProp → Prop

axiom ktaut_true : KTaut itrue
axiom ktaut_and_comm  (p q : IProp)   : KTaut (iiff (iand p q) (iand q p))
axiom ktaut_and_idem  (p : IProp)     : KTaut (iiff (iand p p) p)
axiom ktaut_and_assoc (p q r : IProp) :
    KTaut (iiff (iand (iand p q) r) (iand p (iand q r)))
axiom ktaut_dneg (p : IProp) : KTaut (iiff (inot (inot p)) p)
axiom ktaut_and_true (p : IProp) : KTaut (iiff (iand itrue p) p)
-- Phase 6c 本番: De Morgan・分配・(α∨β)∧¬β ↔ α∧¬β 等、
-- Ch.12 §5 の Keynes 列挙を全収録する (th_24_i の再証明に必要)。

/-- **Ax.(iii) pedantic 形**: 認証されたトートロジーは確実。 -/
axiom ax_iii_pedantic (t h : IProp) : KTaut t → PrI t h = 1

/-- 代入補助生成子: 認証同値の下での文脈代入
(Keynes の (12) 証明が暗黙に使う「同値な部分の入替」の最小形)。
Phase 6c 本番では、これを個別図式に分解できるか (あるいは deep embedding
に置換すべきか) を判断する — PHASE6C_DESIGN.md §3.2。 -/
axiom ktaut_subst (a b p : IProp) :
    KTaut (iiff a b) → KTaut (iiff (iand p a) (iand p b))

/-- **Th.(12) 内包版** — 現状は公理として仮置き。
Phase 6c 本番タスク: def_IX_i + ktaut_subst + ax_iii_pedantic から
**定理に降格**する (Phase 6b th_13_12 の証明構造を内包側に移植)。
降格に成功したら、その kernel 依存リストが「pedantic 経路の実コスト」の
初測定になる。 -/
axiom th_12_i (a b h : IProp) : PrI (iiff a b) h = 1 → PrI a h = PrI b h

/-! ## 煙試験: 融合形なしで代入が回ることの確認 -/

/-- 煙試験 1: 交換律の代入 (14.42 系の内包版のプロトタイプ)。 -/
theorem smoke_comm (p q h : IProp) : PrI (iand p q) h = PrI (iand q p) h :=
  th_12_i _ _ h (ax_iii_pedantic _ h (ktaut_and_comm p q))

/-- 煙試験 2: 反復律の代入 (14.45 系の内包版のプロトタイプ)。 -/
theorem smoke_idem (p h : IProp) : PrI (iand p p) h = PrI p h :=
  th_12_i _ _ h (ax_iii_pedantic _ h (ktaut_and_idem p))

/-- 煙試験 3: 補完律の内包版 — def_IX_i + ktaut 経由 (th_13_1 の移植試験)。 -/
theorem smoke_compl (p h : IProp) :
    PrI (iand itrue (inot p)) h + PrI (iand itrue p) h = PrI itrue h :=
  def_IX_i itrue p h

-- ## 縮退の否定 (Phase 6c 本番の主目標 — ここでは述べるだけ)
--
-- 次は証明**できない**はずである (H15):
--
--   theorem degeneracy_i (p h : IProp) : PrI p h = 0 ∨ PrI p h = 1 := ...
--
-- 外延版の証明は `by_cases hp : p` (= Classical.em) を使ったが、
-- IProp は Prop ではないため case split の対象にならない。
-- 導出不能性の主張は Popper 関数モデルの構成 (値 1/2 の実現) による
-- 反例証明書として与える — PHASE6C_DESIGN.md §4 参照。

end KeynesI

/-! ## 監査クエリ -/

#check @KeynesI.smoke_comm
#check @KeynesI.smoke_idem
#check @KeynesI.smoke_compl

#print axioms KeynesI.smoke_comm
#print axioms KeynesI.smoke_idem
#print axioms KeynesI.smoke_compl
