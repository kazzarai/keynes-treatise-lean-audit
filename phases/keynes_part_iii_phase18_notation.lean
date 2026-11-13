/-
# Keynes (1921) *A Treatise on Probability* Part III — Lean 4 Phase 18 (notation)
#
# 第 XIX 章・第 XX 章の記法の約束 (1921 年 Macmillan 初版 folio 225, 235)
# 台帳 docs/全数台帳/ch19.md・ch20.md の式行のうち、印刷が主張ではなく
# 記法の約束 (≡ による名付け) として置いている行と、その約束による書換えの行。
#
# ## 基準
#   1921 年初版の頁画像のみ。
#
# ## キャリア
#   第III部は内包キャリア (IProp, PrI) に載せる (CLAUDE.md 不変条件 3)。
#   本ファイルは自己完結で、phase9b の結合子・全称量化子・g(φ, f) を再掲する
#   (phase9b と同一の宣言)。確率の値に関する公理は使わない。
#
# ## 収録
#   folio 225 §4  `g(φ, f)/h = g(φ, f₁f₂)/h`  (台帳 ch19-023)
#       約定 f ≡ f₁f₂ (ch19-017・020) による書換え。約定を前提 hf に運ぶ定理
#       th_19_023_rewrite。約定の右辺 f₁f₂ は phase9b と同じ pand。
#
# ## 定義にしない行 (台帳では 未 のまま)
#   ch20-015 `φ(x) ≡ ' x can be inferred from h '`: 被定義項が引用符つきの語句で、
#       「x は h から推論できる」を IProp の値として与える結合子が本キャリアにない
#       (x/h = 1 は ℝ の等式であって IProp ではない)。
#   ch20-016 `f(x) ≡ x`: x は命題の上を動く。本キャリアの全称量化子 iall は
#       事例 (Inst) の上を動くので、命題の上の全称量化子を新たに置かないと、
#       この f を使う一般化 g(φ, f) を定義に書けない (印刷に無い道具は足さない)。
#   ch20-017 `g(φ, f) ≡ h`: 脚注の結論 (then …) であって約定ではない。導くには
#       ch20-015 の推論関係を命題として持つことが要る。
#   ch19-033 `ψ(a) = h . θ(a)`: 「a についての言明」の条件付き定義の前提で、
#       但し書き「h は a を含まない命題」を IProp の上で述べる語彙がない。
#
# ## 実行方法
#   lake env lean phases/keynes_part_iii_phase18_notation.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KeynesIII

/-! ## 内包的キャリアと結合子 (phase9b と同一) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp

axiom PrI : IProp → IProp → ℝ

/-- 事例 (instances) の領域 (phase9b と同一)。 -/
axiom Inst : Type

/-- 命題関数 φ(x) (phase9b と同一)。 -/
abbrev PFun : Type := Inst → IProp

/-- 内包的全称量化子 (phase9b と同一)。 -/
axiom iall : (Inst → IProp) → IProp

/-- φψ : 命題関数の連言 (phase9b と同一)。 -/
noncomputable def pand (φ ψ : PFun) : PFun := fun x => iand (φ x) (ψ x)

infixr:35 " ∧ₚ " => pand

/-- **g(φ, f)** (folio 222、phase9b と同一)。 -/
noncomputable def g (φ f : PFun) : IProp := iall fun x => ior (inot (φ x)) (f x)

/-! ## folio 225 §4 — 約定 f ≡ f₁f₂ による書換え (台帳 ch19-023) -/

/-- **folio 225 第 2 ブロック第 1 行 (台帳 ch19-023)** `g(φ, f)/h = g(φ, f₁f₂)/h`。
約定 `f ≡ f₁f₂` (ch19-017・020) を前提 hf に運び、書換えの等号を述べる。
等号は約定の代入だけで出る (確率の公理は使わない)。 -/
theorem th_19_023_rewrite (φ f f₁ f₂ : PFun) (h : IProp) (hf : f = (f₁ ∧ₚ f₂)) :
    PrI (g φ f) h = PrI (g φ (f₁ ∧ₚ f₂)) h := by
  subst hf; rfl

end KeynesIII

/-! ## 監査クエリ (Phase 18 notation) -/

#check @KeynesIII.th_19_023_rewrite

#print axioms KeynesIII.th_19_023_rewrite
