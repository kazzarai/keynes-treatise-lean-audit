/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7d
#
# 新井一成・Claude共著、2026年7月9日
# **(14.34) の決着: 原典正誤の反証監査 + 修復形の検証**
#
# ## 照合ソース
#   - 英語原典: Project Gutenberg #32625 TeX (原著/Keynes(1921)_英語.tex,
#     l.7869-7877)。1921 年初版の忠実転記。
#   - 日本語版: 佐藤訳 p.169-170 (全集版 1973 底本)。**両者の (34) は一字一句同一**
#     — すなわち問題は翻訳・スキャンではなく原典自体にある。
#
# ## 診断 (3 点、いずれも本ファイルで機械証明する)
#   D1. 印刷されたブリッジ式
#         (a/hh₁x)/(a/hx) · (a/hh₁)/(a/hh₁x)
#           = (x/hh₁a)/(x/ha) · (h₁/ha)/(h₁/hax)
#       の**右辺は Keynes 自身の Def.X により恒等的に 1** (証拠 ha 上で
#       x, h₁ に X の左右両形を適用)。→ th_34_printed_rhs_trivial
#   D2. 左辺は telescope して (a/hh₁)/(a/hx) であり、一般に 1 ではない。
#       重み (2,1,1,2) の 4 世界モデル (a={w₀,w₁}, x={w₀,w₂}, h₁={w₀,w₃}) で
#       左辺 = 3/4 ≠ 1 = 右辺。しかも同モデルは (34) の前提を全て満たしつつ
#       結論を破る (P(a|h₁) = P(a))。全証拠結合は整合的 (質量正)。
#       → namespace Erratum34Countermodel (ℚ 演算、norm_num 検証)
#   D3. 正しいブリッジは
#         (a/hh₁)/(a/hx) = (h₁/ah)/(h₁/h) · (x/h)/(x/ah)
#       であり、これは**逆原理 (38) を仮説 {h₁, x}・データ a で並べ替えたもの**
#       (新井の指摘 2026-07-09: 「式 34 は逆確率の定理では」— 的中)。
#       印刷式は右辺 2 因子の証拠添字が h ↔ ha で取り違えられている。
#       修復形の定理: 「x が a/h に好都合で、かつ a が h₁/h に対して x/h に
#       対するのに劣らず好都合ならば、h₁ は a/h に好都合」→ th_14_34
#
# ## 付記 (33) について
#   英語原典の (33) プローズは "not MORE favourable"、直後の証明は「第 3・4 項の
#   積は 1 **以上**」= "not LESS" を要求し、プローズと証明が逆向き。数学的に
#   正しいのは証明側で、Phase 7b の th_14_33 は証明側に忠実 (= 正しい形) で
#   検証済み。プローズの不等号向きの誤りとして正誤表に記録する。
#
# ## 検証したい仮説
#   H28: th_34_printed_rhs_trivial は {def_X_left, def_X_right} + floor で閉じる
#        (Keynes の X だけで彼のブリッジ右辺が崩壊することの証明書)。
#   H29: 修復形 th_14_34 は {def_X_left, def_X_right, ax_range_lo} + floor。
#   H30: 反例モデル (ℚ) は公理ゼロ (純計算 = norm_num) で全チェックが通る。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase7d.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (継承) -/

axiom Pr : Prop → Prop → ℝ

axiom def_X_left (p q h : Prop) :
    Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h
axiom def_X_right (p q h : Prop) :
    Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h

axiom ax_range_lo (α h : Prop) : 0 ≤ Pr α h

/-! ## D1: 印刷ブリッジ右辺の崩壊 (Keynes 自身の X による) -/

/-- **印刷された (34) ブリッジ右辺は恒等的に 1** (分母因子が正のとき).
証拠 K := a∧h 上で命題 x, h₁ に Def.X の左右両形を適用すると
  x/(h₁∧K) · h₁/K = h₁/(x∧K) · x/K
が Keynes 系の定理となり、印刷右辺 (x/hh₁a)/(x/ha) · (h₁/ha)/(h₁/hax) は
ちょうどこの左辺/右辺の比、すなわち 1 である。 -/
theorem th_34_printed_rhs_trivial (a x h₁ h : Prop)
    (hv₂ : 0 < Pr x (a ∧ h)) (hu₂ : 0 < Pr h₁ (x ∧ (a ∧ h))) :
    (Pr x (h₁ ∧ (a ∧ h)) * Pr h₁ (a ∧ h)) /
      (Pr x (a ∧ h) * Pr h₁ (x ∧ (a ∧ h))) = 1 := by
  have hl := def_X_left x h₁ (a ∧ h)
  have hr := def_X_right x h₁ (a ∧ h)
  have hX : Pr x (h₁ ∧ (a ∧ h)) * Pr h₁ (a ∧ h)
      = Pr x (a ∧ h) * Pr h₁ (x ∧ (a ∧ h)) := by
    calc Pr x (h₁ ∧ (a ∧ h)) * Pr h₁ (a ∧ h)
        = Pr (x ∧ h₁) (a ∧ h) := hl.symm
      _ = Pr h₁ (x ∧ (a ∧ h)) * Pr x (a ∧ h) := hr
      _ = Pr x (a ∧ h) * Pr h₁ (x ∧ (a ∧ h)) := by ring
  rw [hX]
  exact div_self (ne_of_gt (mul_pos hv₂ hu₂))

/-! ## D3: 修復形 — (38) 逆原理の並べ替えとしての (34) -/

/-- **Th.(14.34) 修復形** (正誤表つき検証).
「もし x が a/h に対して好都合であり、かつ a が h₁/h に対して、x/h に
対するのに劣らず好都合であるならば、そのとき h₁ は a/h に対して好都合である。」

比較条件は交差乗算形: x/ah · h₁/h ≤ h₁/ah · x/h
(= 影響係数 (h₁/ah)/(h₁/h) ≥ (x/ah)/(x/h)、分母正の下)。

正しいブリッジ (a/hh₁)/(a/hx) = (h₁/ah)/(h₁/h) · (x/h)/(x/ah) は
逆原理 (38) の並べ替えであり、証明は X の左右両形の 2 連鎖
(C·P₀ = P₁·A、B·Q₀ = Q₁·A) から除算なしで閉じる。 -/
theorem th_14_34 (a x h₁ h : Prop)
    (hfav : Pr a h < Pr a (x ∧ h))
    (hP0 : 0 < Pr h₁ h) (hQ0 : 0 < Pr x h)
    (hcmp : Pr x (a ∧ h) * Pr h₁ h ≤ Pr h₁ (a ∧ h) * Pr x h) :
    Pr a h < Pr a (h₁ ∧ h) := by
  have hx1 := def_X_left a h₁ h
  have hx2 := def_X_right a h₁ h
  have hy1 := def_X_left a x h
  have hy2 := def_X_right a x h
  have hA := ax_range_lo a h
  have eB : Pr a (x ∧ h) * Pr x h = Pr x (a ∧ h) * Pr a h := by
    linarith [hy1, hy2]
  have eC : Pr a (h₁ ∧ h) * Pr h₁ h = Pr h₁ (a ∧ h) * Pr a h := by
    linarith [hx1, hx2]
  have step : Pr a (x ∧ h) * Pr x h * Pr h₁ h
      ≤ Pr a (h₁ ∧ h) * Pr h₁ h * Pr x h := by
    calc Pr a (x ∧ h) * Pr x h * Pr h₁ h
        = (Pr a (x ∧ h) * Pr x h) * Pr h₁ h := by ring
      _ = (Pr x (a ∧ h) * Pr a h) * Pr h₁ h := by rw [eB]
      _ = (Pr x (a ∧ h) * Pr h₁ h) * Pr a h := by ring
      _ ≤ (Pr h₁ (a ∧ h) * Pr x h) * Pr a h :=
          mul_le_mul_of_nonneg_right hcmp hA
      _ = (Pr h₁ (a ∧ h) * Pr a h) * Pr x h := by ring
      _ = (Pr a (h₁ ∧ h) * Pr h₁ h) * Pr x h := by rw [eC]
      _ = Pr a (h₁ ∧ h) * Pr h₁ h * Pr x h := by ring
  have hpos : 0 < Pr h₁ h * Pr x h := mul_pos hP0 hQ0
  have key : Pr a (x ∧ h) ≤ Pr a (h₁ ∧ h) := by nlinarith [step, hpos]
  linarith

end Keynes

/-! ## D2: 印刷形の数値反例モデル (公理フリー、ℚ の norm_num 計算のみ) -/

namespace Erratum34Countermodel

/-
4 世界 {w₀, w₁, w₂, w₃}、重み (2, 1, 1, 2)、総質量 6。
  a  = {w₀, w₁} (質量 3)
  x  = {w₀, w₂} (質量 3)
  h₁ = {w₀, w₃} (質量 4)
全ての交わりは {w₀} (質量 2) — すなわち全証拠結合が整合的 (質量正)。
条件付き確率は標準の質量比。以下、各値を質量比として定義し、
モデルの由来を分母・分子に可視化する。
-/

def total : ℚ := 6
def mA : ℚ := 3        -- mass a
def mX : ℚ := 3        -- mass x
def mH : ℚ := 4        -- mass h₁
def mAX : ℚ := 2       -- mass a∧x
def mAH : ℚ := 2       -- mass a∧h₁
def mXH : ℚ := 2       -- mass x∧h₁
def mAXH : ℚ := 2      -- mass a∧x∧h₁

def A : ℚ := mA / total       -- a/h        = 1/2
def B : ℚ := mAX / mX         -- a/hx       = 2/3
def C : ℚ := mAH / mH         -- a/hh₁      = 1/2
def v₂ : ℚ := mAX / mA        -- x/ha       = 2/3
def v₁ : ℚ := mAH / mA        -- h₁/ha      = 2/3
def u₁ : ℚ := mAXH / mAH      -- x/hh₁a     = 1
def u₂ : ℚ := mAXH / mAX      -- h₁/hax     = 1
def D : ℚ := mAXH / mXH       -- a/hh₁x     = 1

/-- 全証拠結合の整合性 (質量正)。Keynes Ax.(i) の存在条件を満たす。 -/
theorem masses_positive :
    0 < total ∧ 0 < mA ∧ 0 < mX ∧ 0 < mH ∧ 0 < mAX ∧ 0 < mAH ∧
    0 < mXH ∧ 0 < mAXH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [total, mA, mX, mH, mAX, mAH, mXH, mAXH]

/-- モデルは Def.X の関連インスタンスを満たす (標準条件付き確率であることの検査)。
例: a/hh₁ · h₁/h = h₁/ah · a/h (× total 正規化で質量恒等式に帰着)。 -/
theorem model_satisfies_X_instances :
    C * (mH / total) = v₁ * A ∧ B * (mX / total) = v₂ * A ∧
    u₁ * v₁ = u₂ * v₂ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [A, B, C, v₁, v₂, u₁, u₂, total, mA, mX, mH, mAX, mAH, mXH, mAXH]

/-- (34) の前提は全て成立する: x は a/h に好都合 (2/3 > 1/2)、
h₁ は x/ha に好都合 (1 > 2/3)、比較条件も (等号で) 成立。 -/
theorem hypotheses_of_34_hold :
    A < B ∧ v₂ < u₁ ∧ u₁ * v₁ ≥ u₂ * v₂ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [A, B, v₁, v₂, u₁, u₂, total, mA, mX, mH, mAX, mAH, mXH, mAXH]

/-- **結論は破れる**: h₁ は a/h に好都合でない (P(a|h₁) = 1/2 = P(a))。 -/
theorem conclusion_of_34_fails : ¬ (A < C) := by
  norm_num [A, C, total, mA, mH, mAH]

/-- **印刷ブリッジ式は偽**: 左辺 (telescope 後) = 3/4、右辺 = 1。 -/
theorem printed_bridge_false :
    (D / B) * (C / D) = 3/4 ∧ (u₁ / v₂) * (v₁ / u₂) = 1 ∧
    (D / B) * (C / D) ≠ (u₁ / v₂) * (v₁ / u₂) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [A, B, C, D, v₁, v₂, u₁, u₂, total, mA, mX, mH, mAX, mAH, mXH, mAXH]

end Erratum34Countermodel

/-! ## 監査クエリ (Phase 7d) -/

#check @Keynes.th_34_printed_rhs_trivial
#check @Keynes.th_14_34
#check @Erratum34Countermodel.printed_bridge_false

-- Kernel 依存. 注目点:
--   th_34_printed_rhs_trivial : ★ H28 — {def_X_left, def_X_right} + floor
--   th_14_34 (修復形)          : ★ H29 — {def_X 両形, ax_range_lo} + floor
--   反例モデル群               : ★ H30 — Keynes 公理ゼロ (純 ℚ 計算)
#print axioms Keynes.th_34_printed_rhs_trivial
#print axioms Keynes.th_14_34
#print axioms Erratum34Countermodel.masses_positive
#print axioms Erratum34Countermodel.model_satisfies_X_instances
#print axioms Erratum34Countermodel.hypotheses_of_34_hold
#print axioms Erratum34Countermodel.conclusion_of_34_fails
#print axioms Erratum34Countermodel.printed_bridge_false
