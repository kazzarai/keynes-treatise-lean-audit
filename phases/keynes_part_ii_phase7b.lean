/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7b
#
# 新井一成・Claude共著、2026年7月8日
# **原著照合バッチ第 1 号**: 本ファイルの全定理は、佐藤隆三訳『確率論』
# (ケインズ全集第 8 巻、東洋経済新報社) の該当ページを画像で照合した上で
# 形式化されている。DB (keynes_axioms_v2.pl) 単独を典拠とした従来方式からの
# 方法論的転換点 (2026-07-08 反省会による)。
#
# ## 照合ソース (佐藤訳ページ / 底本欄外ページ)
#   (30)         : 佐藤訳 p.168 / 欄外 162  — 無関連の補元不変性 (証明印刷あり)
#   (33)(33.1)   : 佐藤訳 p.169 / 欄外 162-163 — 比較的関連の伝達 (telescoping 証明印刷あり)
#   (35)         : 佐藤訳 p.170 / 欄外 163  — 同上の変形
#   (39)(40)     : 佐藤訳 p.172 / 欄外 165-166 — 諸前提の結合定理 (式明記)
#
# ## 本ファイルで追加したもの (DB ノード 5 + DB 外枝番 1)
#   th_14_30   : 無関連なら矛盾命題も無関連
#   th_14_33   : 比較的関連の伝達 (側条件つき — 無条件推移性ではない!)
#   th_14_33_1 : (33) の a fortiori 形 ★DB 未収録 (原著にのみ存在する枝番)
#   th_14_35   : (33) の変形 (h₁x 経由の比較)
#   th_14_39   : 前提結合 a/h₁h₂h = u/(u+v)
#   th_14_40   : 前提結合の 2 仮説 Bayes 形 (1−q 表記も原著通り)
#
# ## 照合が明らかにしたこと (§7 追記予定の要点)
#   1. **(33)-(35) は無条件の関連推移性ではない**。DB の見出し「関連の推移性」は
#      誤解を招く要約で、原著は比較影響の側条件を明示し、証明は影響係数比の
#      telescoping である。ケインズは Carnap 以降に教科書事項となる
#      推移性の罠を 1921 年時点で側条件により回避していた。
#   2. **DB は原著の枝番を数え漏らしている**: (29.1)-(29.3), (33.1), (38.2),
#      (40.1) は原著に存在するが DB に無い。「100 定理」は DB 台帳基準であり
#      原著基準ではない (README / 論文の記述を要修正)。
#   3. (34) は翻訳スキャンの上付きバー (ā) が判読不能で、素直な読みでは
#      Def.X の左右対称性により恒等式へ潰れる解釈が混入する。**英語原典で
#      式を確定するまで形式化しない** (Phase 7d)。
#
# ## 検証したい仮説
#   H21: (33)(33.1)(35) は floor + Pr のみで閉じる (比較的関連の伝達は
#        純粋な順序体代数であり、確率的内容は仮説の解釈に全て宿る)。
#   H22: (30) は {ax_iii_op, ax_iii_true, def_IX, def_X_left} + floor。
#   H23: (40) は 6 公理 (2 仮説 Bayes 系の再現) — (46.2) の 7 公理に次ぐ規模。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase7b.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (継承) -/

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

/-! ## 再掲 (証明付き) -/

theorem th_13_1 (α h : Prop) : Pr α h + Pr (¬α) h = 1 := by
  have step := def_IX True α h
  have e1 : (True ∧ ¬α) ↔ ¬α := by tauto
  have e2 : (True ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, ax_iii_true] at step
  linarith

theorem th_14_38_full (α β h : Prop) (hβ : Pr β h ≠ 0) :
    Pr α (β ∧ h) = Pr β (α ∧ h) * Pr α h / Pr β h := by
  have h_left  : Pr (α ∧ β) h = Pr α (β ∧ h) * Pr β h := def_X_left α β h
  have h_right : Pr (α ∧ β) h = Pr β (α ∧ h) * Pr α h := def_X_right α β h
  have heq : Pr α (β ∧ h) * Pr β h = Pr β (α ∧ h) * Pr α h := by
    rw [← h_left, h_right]
  exact def_XI (Pr α (β ∧ h)) (Pr β h) (Pr β (α ∧ h) * Pr α h) hβ heq

/-! ## Phase 7b 新規 (照合済み 6 本) -/

/-- **Th.(14.30)** 無関連の補元不変性 (佐藤訳 p.168).
「もし a/h₁h₂ = a/h₁ ならば、そのとき、もし h₁h̄₂ が不整合でないならば、
a/h₁h̄₂ = a/h₁」— したがって「もし命題が推論に対して無関連ならば、
その命題の矛盾命題も無関連である」。
証明は原著印刷のもの ((24.2) 分解 → 補完律 → 消去) を移植。
ambient 規約: h₁ を証拠 k として保持。 -/
theorem th_14_30 (a h₂ k : Prop)
    (hirrel : Pr a (h₂ ∧ k) = Pr a k) (hcons : Pr (¬h₂) k ≠ 0) :
    Pr a ((¬h₂) ∧ k) = Pr a k := by
  have hIX := def_IX a h₂ k
  have hXl1 := def_X_left a h₂ k
  rw [hirrel] at hXl1
  have hXl2 := def_X_left a (¬h₂) k
  have hcompl := th_13_1 h₂ k
  have h0 : (Pr a ((¬h₂) ∧ k) - Pr a k) * Pr (¬h₂) k = 0 := by
    first
      | nlinarith [hIX, hXl1, hXl2, hcompl]
      | linear_combination -hXl2 + hIX - hXl1 - Pr a k * hcompl
  rcases mul_eq_zero.mp h0 with hz | hz
  · linarith
  · exact absurd hz hcons

/-- **Th.(14.33)** 比較的関連の伝達 (佐藤訳 p.169).
「もし x が a/h に対して好都合であり、かつ h₁ が a/hx に対して、
x が a/hh₁ に対するのに劣らず好都合ならば、そのとき h₁ は a/h に対して
好都合である。」

原著の証明: a/hh₁ = a/h · (a/hx)/(a/h) · (a/hh₁x)/(a/hx) · (a/hh₁)/(a/hh₁x)
の telescoping。第 2 項 > 1 (好都合仮定)、第 3×4 項 ≥ 1 (側条件)。

**これは無条件の推移性ではない** — 側条件 (hcmp) が本質。本形式化では
側条件を分母正値と両立する交差乗算形で表す:
  (a/hh₁x)/(a/hx) ≥ (a/hh₁x)/(a/hh₁)  ⟺  D·B ≤ D·C (D > 0 の下)。 -/
theorem th_14_33 (a x h₁ h : Prop)
    (hfav : Pr a h < Pr a (x ∧ h))
    (hD : 0 < Pr a (h₁ ∧ (x ∧ h)))
    (hcmp : Pr a (h₁ ∧ (x ∧ h)) * Pr a (x ∧ h)
              ≤ Pr a (h₁ ∧ (x ∧ h)) * Pr a (h₁ ∧ h)) :
    Pr a h < Pr a (h₁ ∧ h) := by
  have hBC : Pr a (x ∧ h) ≤ Pr a (h₁ ∧ h) := by nlinarith [hcmp, hD]
  linarith

/-- **Th.(14.33.1)** (33) の a fortiori 形 (佐藤訳 p.169) ★DB 未収録枝番.
「いっそう強力な理由で、もし x が a/h に対して好都合であり、かつ a/hh₁ に
対して好都合でないならば、かつまたもし h₁ が a/hx に対して不都合で
ないならば、そのとき h₁ は a/h に対して好都合である。」 -/
theorem th_14_33_1 (a x h₁ h : Prop)
    (hfav : Pr a h < Pr a (x ∧ h))
    (hf3 : Pr a (x ∧ h) ≤ Pr a (h₁ ∧ (x ∧ h)))
    (hg : Pr a (h₁ ∧ (x ∧ h)) ≤ Pr a (h₁ ∧ h)) :
    Pr a h < Pr a (h₁ ∧ h) := by
  linarith

/-- **Th.(14.35)** 比較的関連の伝達・変形 (佐藤訳 p.170).
「もし x は a/h に対して好都合であるが、h₁x ほどには a/h に対して好都合で
はなく、かつ a/hh₁ に対してよりも優るとも劣らず a/h に対して好都合で
あるならば、そのとき h₁ は a/h に対して好都合である。」

原著の brace 恒等式:
a/hh₁ = a/h · {(a/h)/(a/hx) · (a/hh₁x)/(a/h)} · {(a/hx)/(a/h) · (a/hh₁)/(a/hh₁x)}
第 1 brace > 1 (hBD)、第 2 brace ≥ 1 (hcmp、交差乗算形 B·C ≥ D·A)。
好都合性の比較は非不可能性 (0 < a/h) を前提する (原著の比率記法が要求)。 -/
theorem th_14_35 (a x h₁ h : Prop)
    (hA : 0 < Pr a h)
    (hfav : Pr a h < Pr a (x ∧ h))
    (hBD : Pr a (x ∧ h) < Pr a (h₁ ∧ (x ∧ h)))
    (hcmp : Pr a (h₁ ∧ (x ∧ h)) * Pr a h ≤ Pr a (x ∧ h) * Pr a (h₁ ∧ h)) :
    Pr a h < Pr a (h₁ ∧ h) := by
  have hB : 0 < Pr a (x ∧ h) := lt_trans hA hfav
  have hstep : 0 < Pr a h * (Pr a (h₁ ∧ (x ∧ h)) - Pr a (x ∧ h)) :=
    mul_pos hA (sub_pos.mpr hBD)
  have key : Pr a (x ∧ h) * Pr a h < Pr a (x ∧ h) * Pr a (h₁ ∧ h) := by
    nlinarith [hcmp, hstep]
  nlinarith [key, hB]

/-- **Th.(14.39)** 諸前提の結合 (佐藤訳 p.172).
「X および (24.2) により a/h₁h₂h = (ah₁h₂/h)/(h₁h₂/h)
 = (ah₁h₂/h)/(ah₁h₂/h + āh₁h₂/h) = u/(u+v)」
u は結論と両前提の同時事前確率、v はその矛盾命題版。式は原著明記。 -/
theorem th_14_39 (a h₁ h₂ h : Prop) (hK : Pr (h₁ ∧ h₂) h ≠ 0) :
    Pr a ((h₁ ∧ h₂) ∧ h) =
      Pr (a ∧ (h₁ ∧ h₂)) h /
        (Pr (a ∧ (h₁ ∧ h₂)) h + Pr ((¬a) ∧ (h₁ ∧ h₂)) h) := by
  have hIX := def_IX (h₁ ∧ h₂) a h
  have e1 : ((h₁ ∧ h₂) ∧ ¬a) ↔ ((¬a) ∧ (h₁ ∧ h₂)) := by tauto
  have e2 : ((h₁ ∧ h₂) ∧ a) ↔ (a ∧ (h₁ ∧ h₂)) := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at hIX
  have hXl := def_X_left a (h₁ ∧ h₂) h
  have hdiv := def_XI (Pr a ((h₁ ∧ h₂) ∧ h)) (Pr (h₁ ∧ h₂) h)
      (Pr (a ∧ (h₁ ∧ h₂)) h) hK hXl.symm
  rw [hdiv, ← hIX]
  ring

/-- **Th.(14.40)** 前提結合の 2 仮説 Bayes 形 (佐藤訳 p.172).
「a/h₁h₂ = (h₁/ah₂ · q)/(h₁/ah₂ · q + h₁/āh₂ · (1−q)), ここに q = a/h₂」
(1−q) 表記も原著通り (補完律で ¬a の事前を消去した形)。
h₂ を ambient 証拠として読む。 -/
theorem th_14_40 (a h₁ h₂ : Prop) (hh₁ : Pr h₁ h₂ ≠ 0) :
    Pr a (h₁ ∧ h₂) =
      Pr h₁ (a ∧ h₂) * Pr a h₂ /
        (Pr h₁ (a ∧ h₂) * Pr a h₂ + Pr h₁ ((¬a) ∧ h₂) * (1 - Pr a h₂)) := by
  have hcompl := th_13_1 a h₂
  have hq : Pr (¬a) h₂ = 1 - Pr a h₂ := by linarith
  have h_total_step := def_IX h₁ a h₂
  have h_left_a := def_X_left h₁ a h₂
  have h_left_na := def_X_left h₁ (¬a) h₂
  have h_bayes := th_14_38_full a h₁ h₂ hh₁
  have h_total : Pr h₁ h₂ =
      Pr h₁ (a ∧ h₂) * Pr a h₂ + Pr h₁ ((¬a) ∧ h₂) * (1 - Pr a h₂) := by
    rw [← h_total_step, h_left_a, h_left_na, hq]
    ring
  rw [h_bayes, h_total]

end Keynes

/-! ## 監査クエリ (Phase 7b 新規) -/

#check @Keynes.th_14_30
#check @Keynes.th_14_33
#check @Keynes.th_14_33_1
#check @Keynes.th_14_35
#check @Keynes.th_14_39
#check @Keynes.th_14_40

-- Kernel 依存. 注目点:
--   th_14_33 / th_14_33_1 / th_14_35 : ★ H21 判定点 — floor + Pr のみか
--     (比較的関連の伝達 = 純順序体代数、確率的内容は仮説の解釈に宿る)
--   th_14_30 : ★ H22 判定点
--   th_14_40 : ★ H23 判定点 — 6 公理級 (2 仮説 Bayes 系)
#print axioms Keynes.th_14_30
#print axioms Keynes.th_14_33
#print axioms Keynes.th_14_33_1
#print axioms Keynes.th_14_35
#print axioms Keynes.th_14_39
#print axioms Keynes.th_14_40

-- 回帰テスト
#print axioms Keynes.th_13_1
#print axioms Keynes.th_14_38_full
