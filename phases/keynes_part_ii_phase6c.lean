/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 6c 本番
#
# 新井一成・Claude共著、2026年7月8日
# 内包移行・案B: deep embedding による pedantic Ax.(iii) + Th.(12) 降格
#
# ## 本ファイルで実装したもの (PHASE6C_DESIGN.md 案B)
#   1. 構文型 Form (命題論理の深い埋め込み) + Boolean 評価 evalB + Taut 述語。
#      「論証的 (demonstrated) 同値」= 全真理値割当で真、という計算的意味を付与。
#      スケルトンの KTaut 生成子公理群は**全廃** — トートロジー性は公理でなく
#      計算になった (公理数の大幅削減が案Bの狙い)。
#   2. ax_iii_taut: 認証トートロジーの解釈は確実 — pedantic Ax.(iii) の本体。
#      True の確実性 (旧 ax_iii_true) もこの 1 本に吸収される (itrue_certain)。
#   3. def_VIII_i: Keynes Def.VIII (等値の定義) の双条件読み。
#   4. **Th.(12) の定理降格** (th_12_i): Keynes 自身の導出経路
#      (VIII で交差確実性に開き、Def.X の左右両形で積として閉じる) を移植。
#      スケルトンで公理だった th_12_i がここで証明される (H17)。
#   5. 移植定理: 補完律 (13.1)、加法定理 (24)、乗法定理 (36)、Bayes (38)_full。
#      各 #print axioms が「pedantic 経路の実コスト」の測定値になる。
#
# ## 検証したい仮説
#   H17: th_12_i の kernel 集合 = {def_VIII_i, def_X_left_i, def_X_right_i}
#        + floor。DB の cites(th13_12, ax_ivb) は substrate に吸収される。
#   H18: Form/evalB/Taut の埋め込み機構は #print axioms に一切痕跡を残さない
#        (トートロジー検査は純 substrate = C_rec。Finding 17 の再確認)。
#   H19: **pedantry のコスト測定**: 外延版 th_24 の Keynes 集合は
#        {def_IX, ax_iii_op} だったが、内包版 th_24_i は代入を VIII+X 経由で
#        回すため {def_IX_i, ax_iii_taut, def_VIII_i, def_X_left_i,
#        def_X_right_i} に増える見込み。融合形 ax_iii_op が VIII+X の合成を
#        1 公理に隠していたことの定量化。
#   H15 (別ファイル課題): 縮退定理の内包版が導出不能であること。
#        外延版の証明は `by_cases hα : α` (= Classical.em) を要したが、
#        a : IProp は Prop ではないため case split の対象にならず、
#        実質的同値の混入経路が型レベルで存在しない。導出不能性の
#        正の証明 (Popper 関数モデルによる値 1/2 の反例証明書) は
#        PHASE6C_DESIGN.md §4 に従い Phase 6c-model として別途実装する。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase6c.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace KeynesI

/-! ## 内包的キャリアと結合子 (スケルトンと同一) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-! ## Keynes 操作公理群 (内包版) -/

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- **Def.VIII (等値の定義)** 双条件読み: (a=b)/h = 1 であることと、
交差条件付き確実性 (b/ah = 1 かつ a/bh = 1) は同じことである。
Keynes は右辺で左辺を**定義**する (DB: '等値: b/αh=1 かつ α/bh=1 ならば
(α=b)/h=1')。 -/
axiom def_VIII_i (a b h : IProp) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-! ## 深い埋め込み: 構文・評価・トートロジー -/

/-- 命題論理の構文 (Arai 拡張)。Keynes の「論証的同値」の対象言語。 -/
inductive Form : Type where
  | var  : ℕ → Form
  | tru  : Form
  | fls  : Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | neg  : Form → Form
  | iffF : Form → Form → Form

/-- Boolean 評価 (真理値計算)。 -/
def evalB (v : ℕ → Bool) : Form → Bool
  | .var n    => v n
  | .tru      => true
  | .fls      => false
  | .conj f g => evalB v f && evalB v g
  | .disj f g => evalB v f || evalB v g
  | .neg f    => !(evalB v f)
  | .iffF f g => evalB v f == evalB v g

/-- **論証的トートロジー**: すべての真理値割当で真。
「demonstrated equivalence」の計算的意味論。仮説依存の実質的同値は
定義上ここに入り込めない (割当の全称量化が遮断する)。 -/
def Taut (f : Form) : Prop := ∀ v : ℕ → Bool, evalB v f = true

/-- 構文の内包的解釈 (環境 env : 変数 → IProp)。 -/
noncomputable def interp (env : ℕ → IProp) : Form → IProp
  | .var n    => env n
  | .tru      => itrue
  | .fls      => inot itrue
  | .conj f g => iand (interp env f) (interp env g)
  | .disj f g => ior (interp env f) (interp env g)
  | .neg f    => inot (interp env f)
  | .iffF f g => iiff (interp env f) (interp env g)

/-- **Ax.(iii) pedantic 本体**: 論証的トートロジーの任意の解釈は、
任意の証拠の下で確実。スケルトンの KTaut 生成子群 + ax_iii_pedantic +
ax_iii_true をこの 1 本が置き換える。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Taut f → PrI (interp env f) h = 1

/-! ## Th.(12) の定理降格 (H17) -/

/-- **Th.(12) 内包版 — 定理として証明**.
確実な双条件の下で確率は等しい。証明は Keynes 自身の経路:
Def.VIII で交差確実性 (b/ah = 1, a/bh = 1) に開き、同一対象
P(a∧b)/h を Def.X の左形と右形で二通りに積分解すると、確実性因子が
1 になって P(a)/h = P(b)/h が落ちる。**命題の交換すら不要** (左右両形が
同じ iand a b を分解するため)。

DB cites(th13_12): def_x ✓ (両形), def_viii ✓, ax_ivb → substrate へ吸収。 -/
theorem th_12_i (a b h : IProp) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h := by
  obtain ⟨hba, hab⟩ := (def_VIII_i a b h).mp hcert
  have hl := def_X_left_i a b h
  have hr := def_X_right_i a b h
  rw [hab, one_mul] at hl
  rw [hba, one_mul] at hr
  linarith

/-- 認証代入 (pedantic 代入原理): 構文的トートロジー ↔ の解釈同士は
確率が等しい。融合形 ax_iii_op のあった場所に、ax_iii_taut + th_12_i の
合成が立つ。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i _ _ h (ax_iii_taut (Form.iffF f g) env h ht)

/-- True の確実性: 旧 ax_iii_true は ax_iii_taut の系に降格。 -/
theorem itrue_certain (h : IProp) : PrI itrue h = 1 :=
  ax_iii_taut Form.tru (fun _ => itrue) h (fun _ => rfl)

/-! ## 移植定理 (pedantic コストの測定、H18/H19) -/

/-- **Th.(13.1) 内包版** 補完律。 -/
theorem th_13_1_i (a h : IProp) : PrI a h + PrI (inot a) h = 1 := by
  have step := def_IX_i itrue a h
  have e1 : PrI (iand itrue (inot a)) h = PrI (inot a) h :=
    subst_taut (Form.conj Form.tru (Form.neg (Form.var 0))) (Form.neg (Form.var 0))
      (fun _ => a) h (by intro v; cases h0 : v 0 <;> simp [Taut, evalB, h0])
  have e2 : PrI (iand itrue a) h = PrI a h :=
    subst_taut (Form.conj Form.tru (Form.var 0)) (Form.var 0)
      (fun _ => a) h (by intro v; cases h0 : v 0 <;> simp [Taut, evalB, h0])
  have e3 := itrue_certain h
  linarith [step, e1, e2, e3]

/-- **Th.(24) 内包版** 加法定理。外延版の 2 回の ax_iii_op 書換えが、
2 枚の Taut 証明書 (2 変数・4 割当の真理値計算) に置き換わる。 -/
theorem th_24_i (a b h : IProp) :
    PrI (ior a b) h = PrI a h + PrI b h - PrI (iand a b) h := by
  have step1 := def_IX_i (ior a b) b h
  have e1 : PrI (iand (ior a b) (inot b)) h = PrI (iand a (inot b)) h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.neg (Form.var 1)))
      (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
      (fun n => match n with | 0 => a | _ => b) h
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [Taut, evalB, h0, h1])
  have e2 : PrI (iand (ior a b) b) h = PrI b h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.var 1))
      (Form.var 1)
      (fun n => match n with | 0 => a | _ => b) h
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [Taut, evalB, h0, h1])
  have step3 := def_IX_i a b h
  linarith [step1, e1, e2, step3]

/-- **Th.(14.36) 内包版** 乗法定理 (無関連性下)。代入不要、Def.X のみ。 -/
theorem th_14_36_i (a b h : IProp) (hindep : PrI a (iand b h) = PrI a h) :
    PrI (iand a b) h = PrI a h * PrI b h := by
  have hx := def_X_left_i a b h
  rw [hindep] at hx
  exact hx

/-- **Th.(14.38)_full 内包版** Bayes 反転。代入不要、Def.X 両形 + Def.XI。 -/
theorem th_14_38_full_i (a b h : IProp) (hb : PrI b h ≠ 0) :
    PrI a (iand b h) = PrI b (iand a h) * PrI a h / PrI b h := by
  have hl := def_X_left_i a b h
  have hr := def_X_right_i a b h
  have heq : PrI a (iand b h) * PrI b h = PrI b (iand a h) * PrI a h := by
    rw [← hl, hr]
  exact def_XI_i _ _ _ hb heq

/-! ## 縮退の遮断 (H15 の状況、prose)

外延版の縮退定理 th_15_degeneracy は `by_cases hα : α` — すなわち
Classical.em による真理値場合分け — を本質的に使った。ここでは a : IProp は
命題ではなく不透明型の項であり、`by_cases ha : a` は**型エラー**になる
(case split の対象が Prop でない)。実質的同値を製造する経路が型レベルで
存在しないため、縮退定理の内包版は本公理系では述べても証明手段がない。
導出不能性の正の証明 (健全性経由) は、値 1/2 を実現する Popper 関数
モデルの構成による — PHASE6C_DESIGN.md §4、Phase 6c-model として実装予定。 -/

end KeynesI

/-! ## 監査クエリ (Phase 6c 本番) -/

#check @KeynesI.th_12_i
#check @KeynesI.subst_taut
#check @KeynesI.itrue_certain
#check @KeynesI.th_13_1_i
#check @KeynesI.th_24_i
#check @KeynesI.th_14_36_i
#check @KeynesI.th_14_38_full_i

-- Kernel 依存. 注目点:
--   th_12_i          : ★ H17 判定点 — {def_VIII_i, def_X_left_i, def_X_right_i}
--                      + floor か (ax_iii_taut 不要のはず)
--   th_13_1_i        : ax_iii_taut が初めて load-bearing になる場所
--   th_24_i          : ★ H19 判定点 — pedantic コスト (外延版 {def_IX, ax_iii_op}
--                      との差分が「融合形が隠していたもの」の定量)
--   th_14_36_i/38_i  : 代入フリー definitional 群 (外延版と同コストのはず)
--   全理             : ★ H18 — Form/evalB/Taut は axiom として現れないはず
#print axioms KeynesI.th_12_i
#print axioms KeynesI.subst_taut
#print axioms KeynesI.itrue_certain
#print axioms KeynesI.th_13_1_i
#print axioms KeynesI.th_24_i
#print axioms KeynesI.th_14_36_i
#print axioms KeynesI.th_14_38_full_i
