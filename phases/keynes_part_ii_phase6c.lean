/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 6c 本番
#
# 新井一成・Claude共著、2026年7月8日 (初版)、2026年10月20日 (B09 修復)
# 内包移行・案B: deep embedding による pedantic Ax.(iii) + Th.(12) 降格
#
# ## 2026-10-20 修復 (B09、案 A): 第12章 公理 (i) の但し書きを公理群に戻す
#
#   初版の公理群は False を導いた (記録: phase6c_inconsistency.lean、
#   th_6c_old_inconsistent)。原因は Keynes 第12章 §5 公理 (i) の但し書きが
#   形式化で落ちていたこと。原典 (唯一の基準、1921 Macmillan 初版) の該当箇所:
#
#   folio 135 (第12章 §5 公理 (i)):
#   「(i.) Provided that a and h are propositions or conjunctions of propositions
#    or disjunctions of propositions, and that h is not an inconsistent
#    conjunction, there exists one and only one relation of probability P between
#    a as conclusion and h as premiss. Thus any conclusion a bears to any
#    consistent premiss h one and only one relation of probability.」
#   folio 134 (第12章 §4 Def. VI):
#   「VI. If a/h = 0, the conjunction ah is inconsistent. Def.」
#   folio 134 (第12章 §4 Def. VIII、原文の向きは → のみ):
#   「VIII. If b/ah = 1 and a/bh = 1, (a≡b)/h = 1. Def.
#    This may be regarded as the definition of Equivalence. Thus we see that
#    equivalence is relative to a premiss h. a is equivalent to b, given h,
#    if b follows from ah, and a from bh.」
#   folio 135 (第12章 §5 公理 (iii)):
#   「(iii.) (\overline{a+b} ≡ \bar{a}\bar{b})/h = 1, (aa ≡ a)/h = 1,
#    (\bar{\bar{a}} ≡ a)/h = 1, (ab + \bar{a}b ≡ b)/h = 1.
#    If a/h = 1, ah ≡ h.」
#   folio 141 (第13章): (13) a/a = 1, unless a is inconsistent.
#    (13.1) \bar{a}/a = 0, unless a is inconsistent.
#    (14) If a/b = 0 and a is not inconsistent, b/a = 0.
#    (12.1) If (a≡b)/h = 1 and hx is not inconsistent, a/hx = b/hx.
#   folio 140 (第13章): (8) If a/h = 0, ab/h = 0 and a/bh = 0 if bh is not
#    inconsistent. (9) If a/h = 1, a/bh = 1 if bh is not inconsistent.
#
#   修復の内容:
#   1. 整合性述語 `Cons : IProp → Prop` (「h は矛盾する連言でない」) を置く。
#   2. ax_iii_taut に `Cons h →` を付ける (公理 (i): 確率関係 a/h は h が整合な
#      ときに存在する。恒真式の確実性もその範囲でのみ主張される)。
#   3. def_VIII_i に `Cons (a ∧ h) → Cons (b ∧ h) →` を付ける (b/ah, a/bh が
#      存在する範囲)。向きは双条件のまま (Keynes 自身が (12) の証明で VIII を
#      逆向きに使う、folio 141)。**原典の印刷は → のみ**なので、案 B として
#      印刷どおりの片向き版 def_VIII_i_src を並置する。
#   4. Cons の公理は cons_true (⊤ は整合)、cons_of_pos_src (ah 整合ならば
#      a/h ≠ 0 — Def. VI 印刷の向きの対偶そのもの、用法は第13章 (8)(14))、
#      cons_of_pos (a/h ≠ 0 かつ h 整合ならば ah 整合 — Def. VI を定義として
#      双方向に読んだときの対偶、印刷の向きの逆。用法は (10) folio 140
#      「a/bh = 1 by (9) unless b/h = 0」)、cons_iff_taut (論証的同値な命題は
#      整合性を共有 — 公理 (ii)(iii) による置換)。本ファイルの定理が用いるのは
#      cons_of_pos のみ。
#   5. 既存の定理は但し書きどおり `Cons h` を前提に足して全部通す。初版では
#      (12) → 代入原理 → (1) の順に導いたが、但し書き付きでは代入原理が (1) を
#      要するため、Keynes の順 (1) → (12) に戻した。(1) の証明は Keynes 自身の
#      経路 (folio 139: b/h = 1 とおく) を b := ⊤ で行い、Keynes が公理 (ii)
#      (bh ≡ h) で済ませた一歩を Def. X 左形 + cons_of_pos で置き換える。
#   6. 無矛盾性: phase6c_model.lean の有限モデルが修復後の全公理を満たす。
#      旧経路 (任意の a, h で a/(a∧h) = 1) はそのモデルで偽 (同ファイル)。
#
# ## 本ファイルで実装したもの (PHASE6C_DESIGN.md 案B、初版からの引き継ぎ)
#   1. 構文型 Form (命題論理の深い埋め込み) + Boolean 評価 evalB + Taut 述語。
#      「論証的 (demonstrated) 同値」= 全真理値割当で真、という計算的意味を付与。
#   2. ax_iii_taut: 認証トートロジーの解釈は (整合な証拠の下で) 確実。
#   3. def_VIII_i: Keynes Def.VIII (等値の定義) の双条件読み (但し書き付き)。
#   4. **Th.(12) の定理降格** (th_12_i): Keynes の経路 (VIII で交差確実性に
#      開き、Def.X の左右両形で積として閉じる) に、a/h = 0 または b/h = 0 の
#      場合 (交差確実性が存在しない場合) の処理を足したもの。
#   5. 移植定理: 補完律 (1) (第13章の式 (1)、folio 139; 印刷の (13.1) folio 141
#      とは別)、加法定理 (24)、乗法定理 (36)、Bayes (38)_full。
#
# ## 検証したい仮説 (初版) と修復後の状況
#   H17: th_12_i の #print axioms の出力は初版 {def_VIII_i, def_X_left_i,
#        def_X_right_i} から、修復後は {def_IX_i, def_X_left_i, def_X_right_i,
#        def_VIII_i, ax_iii_taut, cons_of_pos} に増える (a/h = 0 の場合の処理と、
#        矛盾の確率 0 を (1) 経由で出すため)。ただしこの集合は**上界**である:
#        def_VIII_i は Keynes の経路 (folio 141「by VIII.」) をなぞるために
#        用いたもので、除ける。th_12_i_short は def_IX_i a b h・def_IX_i b a h・
#        def_X_left_i a b h・def_X_right_i b a h の 4 式と linarith で同じ結論を
#        出し、その出力に def_VIII_i は現れない。「def_VIII_i を落とすと th_12_i
#        が赤」という必要性の主張は取り下げる。
#   H18: Form/evalB/Taut の埋め込み機構は #print axioms に痕跡を残さない。
#   H19: pedantry のコスト測定 (th_24_i の #print axioms の出力)。subst_taut・
#        th_24_i の集合も H17 と同じ理由で上界であり、必要性は主張しない。
#   H15: 縮退定理の内包版が導出不能であること — 有限モデル (phase6c_model) で
#        中間値 1/2 が実現されることを示した (model_intermediate_value)。
#
# ## 実行方法
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

/-- **整合性述語** `Cons h`: 「h は矛盾する連言でない (h is not an inconsistent
conjunction)」(folio 135、公理 (i))。確率関係 a/h は Cons h のときに存在する。
PrI は全域関数なので、Cons h でない h に対する PrI の値は公理群が値を拘束しない
範囲にある。 -/
axiom Cons : IProp → Prop

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

/-- **Def.VIII (等値の定義)** 双条件読み、但し書き付き (案 A)。
原文 (folio 134): 「VIII. If b/ah = 1 and a/bh = 1, (a≡b)/h = 1. Def.」
印刷は → のみだが、Keynes は定義として双方向に使う ((12) の証明、folio 141:
「b/ah = 1, a/bh = 1 by VIII.」)。関係 b/ah, a/bh は公理 (i) により
ah, bh が整合な場合にのみ存在するので、その範囲で双条件を主張する。
但し書きを落とした双条件は False を導く (phase6c_inconsistency.lean)。 -/
axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- **Def.VIII 印刷どおり** (案 B、→ のみ): 「If b/ah = 1 and a/bh = 1, (a≡b)/h = 1.」
(folio 134)。但し書きは印刷に無いのでそのまま置く。有限モデルはこの形も満たす
(phase6c_model.lean, model_def_VIII_i_src)。本ファイルの定理はこれを用いない。 -/
axiom def_VIII_i_src (a b h : IProp) :
    PrI b (iand a h) = 1 → PrI a (iand b h) = 1 → PrI (iiff a b) h = 1

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

/-- **Ax.(iii) pedantic 本体、但し書き付き**: 論証的トートロジーの任意の解釈は、
**整合な**証拠の下で確実。公理 (i) (folio 135) により a/h は h が矛盾する連言で
ないときに存在するので、公理 (iii) (folio 135) の主張もその範囲に限られる。
但し書きなしの形は False を導く (phase6c_inconsistency.lean)。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

/-! ## 整合性の公理 (4 本。うち 6c の定理に使うのは cons_of_pos のみ、残り 3 本は下流 phase 用) -/

/-- **⊤ は整合**。第12章 §1 (folio 133): 「we need only assume that our data
always include those logical rules, of which the steps of our proofs are
instances」、§5 (folio 135): 「there is included in every premiss with which we
are concerned the formal implications which allow us to assert the following
axioms」。形式的真理だけからなる前提 ⊤ は矛盾する連言ではない。 -/
axiom cons_true : Cons itrue

/-- **ah 整合ならば a/h ≠ 0**: Def. VI 印刷の向きの対偶そのもの。
原文 (folio 134): 「VI. If a/h = 0, the conjunction ah is inconsistent. Def.」
印刷の向きの用法は第13章 (8) (folio 140: 「∴ unless b/h = 0, a/bh = 0 … whence
the result by VI.」) と (14) (folio 141: 「a/f ≠ 0, since a is not inconsistent」)。
本ファイルの定理はこれを用いない (下流 phase のための公理)。有限モデルは
この文を満たす (phase6c_model.lean, model_cons_of_pos_src)。 -/
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0

/-- **a/h ≠ 0 かつ h 整合ならば ah 整合**。Def. VI (folio 134、上掲) を定義として
双方向に読んだときの対偶であり、印刷の向き (cons_of_pos_src) の**逆向き**。
Keynes がこの向きを使うのは (10) (folio 140): 「Since a/h = 1, a/bh = 1 by (9)
unless b/h = 0」— (9) の但し書き「if bh is not inconsistent」を「unless b/h = 0」
で済ませており、b/h ≠ 0 から bh の整合を得ている。 -/
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)

/-- **論証的同値な命題は整合性を共有する**。公理 (ii) (folio 135、等値の公理:
(a≡b)/h = 1 ならば x/ah = x/bh) と公理 (iii) の恒真式を合わせると、論証的に
同値な前提は交換できる (第13章 (13.2)、folio 141: 「by writing \bar{a} for a」)。
整合性 (公理 (i) の但し書き) もこの交換で保たれる。本ファイルの定理は
これを用いない (下流 phase のための公理)。 -/
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## True の確実性と補完律 (Keynes の順: (1) を先に) -/

/-- True の確実性: 旧 ax_iii_true は ax_iii_taut の系に降格。但し書き `Cons h`
は公理 (i) の姿。 -/
theorem itrue_certain (h : IProp) (hc : Cons h) : PrI itrue h = 1 :=
  ax_iii_taut Form.tru (fun _ => itrue) h hc (fun _ => rfl)

/-- **⊤ との連言は確率を変えない**: (⊤ ∧ a)/h = a/h。Keynes の (1) の証明
(folio 139) は b/h = 1 から bh ≡ h (公理 (iii) 末尾) と公理 (ii) で前提を
bh から h に戻す。ここでは b := ⊤ とし、Def. X 左形 (⊤∧a)/h = ⊤/(ah) · a/h で
a/h ≠ 0 なら ah 整合 (cons_of_pos) ゆえ ⊤/(ah) = 1、a/h = 0 なら両辺 0。 -/
theorem true_conj (a h : IProp) (hc : Cons h) : PrI (iand itrue a) h = PrI a h := by
  have hr := def_X_left_i itrue a h
  by_cases ha : PrI a h = 0
  · rw [ha, mul_zero] at hr
    rw [hr, ha]
  · have hca : Cons (iand a h) := cons_of_pos a h ha hc
    rw [itrue_certain (iand a h) hca, one_mul] at hr
    exact hr

/-- **Th.(1) 内包版** 補完律 a/h + \bar{a}/h = 1 (第13章の式 (1)、folio 139)。
定理名の `13_1` は「第 13 章の (1)」の意であり、印刷の (13.1) (folio 141:
「\bar{a}/a = 0, unless a is inconsistent」) ではない。
印刷に但し書きは無いが、証明中の b/h = 1 は公理 (i) により h が整合な場合の
主張なので `Cons h` を前提に置く (docs/COLLATION_INDEX_1921.md、T 前提の補充)。 -/
theorem th_13_1_i (a h : IProp) (hc : Cons h) : PrI a h + PrI (inot a) h = 1 := by
  have step := def_IX_i itrue a h
  rw [true_conj (inot a) h hc, true_conj a h hc, itrue_certain h hc] at step
  linarith

/-- **矛盾の確率は 0**: ¬f が恒真ならば f/h = 0 (h 整合)。第13章の (1) と
Ax.(iii) から。 -/
theorem taut_neg_zero (f : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.neg f)) : PrI (interp env f) h = 0 := by
  have h1 : PrI (inot (interp env f)) h = 1 := ax_iii_taut (Form.neg f) env h hc ht
  have h2 := th_13_1_i (interp env f) h hc
  linarith

/-- **確実な命題の否定との連言は確率 0**: E/h = 1 ならば (x ∧ ¬E)/h = 0。
(1) で \bar{E}/h = 0、Def. X 左形で (x ∧ \bar{E})/h = x/(\bar{E}h) · \bar{E}/h。 -/
theorem conj_neg_cert_zero (x E h : IProp) (hc : Cons h) (hE : PrI E h = 1) :
    PrI (iand x (inot E)) h = 0 := by
  have h1 := th_13_1_i E h hc
  have hnE : PrI (inot E) h = 0 := by linarith
  rw [def_X_left_i x (inot E) h, hnE, mul_zero]

/-! ## Th.(12) の定理降格 (H17) -/

/-- **Th.(12) 内包版 — 定理として証明** (folio 141: 「If (a≡b)/h = 1, a/h = b/h」)。
但し書き `Cons h` は公理 (i) の姿 ((a≡b)/h が存在する範囲)。印刷に但し書きは
無い (docs/COLLATION_INDEX_1921.md、T 前提の補充)。

証明は Keynes 自身の経路 (Def.VIII で交差確実性 b/ah = 1, a/bh = 1 に開き、
同一対象 (ab)/h を Def.X の左形と右形で二通りに積分解する) を、交差確実性が
存在する場合 (a/h ≠ 0 かつ b/h ≠ 0、cons_of_pos で ah, bh が整合) に用い、
a/h = 0 または b/h = 0 の場合は (1) と Def.IX・Def.X で直接 b/h = 0 (または
a/h = 0) を示す: b/h = (b ∧ \bar{a})/h + (b ∧ a)/h、前者は矛盾
(b ∧ \bar{a}) ∧ (a≡b) の確率 0 と \overline{(a≡b)}/h = 0 から 0、後者は
b/(ah) · a/h = 0。

def_VIII_i は Keynes の経路 (folio 141「by VIII.」) をなぞるために使っているもの
で、除ける: 下の th_12_i_short は (b ∧ \bar{a})/h = 0、(a ∧ \bar{b})/h = 0 を
得たあと Def.IX・Def.X の 4 式だけで閉じる。 -/
theorem th_12_i (a b h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h := by
  -- (b ∧ ¬a)/h = 0: (b ∧ ¬a) ∧ (a≡b) は矛盾
  have hba : PrI (iand b (inot a)) h = 0 := by
    have s := def_IX_i (iand b (inot a)) (iiff a b) h
    have z1 := conj_neg_cert_zero (iand b (inot a)) (iiff a b) h hc hcert
    have z2 : PrI (iand (iand b (inot a)) (iiff a b)) h = 0 :=
      taut_neg_zero
        (Form.conj (Form.conj (Form.var 1) (Form.neg (Form.var 0)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h hc
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  -- (a ∧ ¬b)/h = 0: 対称
  have hab : PrI (iand a (inot b)) h = 0 := by
    have s := def_IX_i (iand a (inot b)) (iiff a b) h
    have z1 := conj_neg_cert_zero (iand a (inot b)) (iiff a b) h hc hcert
    have z2 : PrI (iand (iand a (inot b)) (iiff a b)) h = 0 :=
      taut_neg_zero
        (Form.conj (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h hc
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  by_cases ha : PrI a h = 0
  · -- a/h = 0 ⟹ b/h = 0
    have s := def_IX_i b a h
    have x := def_X_left_i b a h
    rw [ha, mul_zero] at x
    linarith
  by_cases hb : PrI b h = 0
  · -- b/h = 0 ⟹ a/h = 0
    have s := def_IX_i a b h
    have x := def_X_left_i a b h
    rw [hb, mul_zero] at x
    linarith
  -- 交差確実性が存在する場合: Keynes の経路
  have hca : Cons (iand a h) := cons_of_pos a h ha hc
  have hcb : Cons (iand b h) := cons_of_pos b h hb hc
  obtain ⟨hba', hab'⟩ := (def_VIII_i a b h hca hcb).mp hcert
  have hl := def_X_left_i a b h
  have hr := def_X_right_i a b h
  rw [hab', one_mul] at hl
  rw [hba', one_mul] at hr
  linarith

/-- **Th.(12) 内包版、短い証明 (def_VIII_i を用いない)**。
(b ∧ \bar{a})/h = 0 と (a ∧ \bar{b})/h = 0 (th_12_i と同じ: (1) と Ax.(iii)) を
得たあとは、def_IX_i a b h・def_IX_i b a h・def_X_left_i a b h・
def_X_right_i b a h の 4 式で ab/h = ba/h = a/(bh) · b/h となり、linarith で
a/h = b/h。交差確実性 (Def. VIII) も a/h = 0 の場合分けも要らない。
#print axioms の出力に def_VIII_i は現れない (cons_of_pos は (1) の証明
true_conj を通じて現れる)。 -/
theorem th_12_i_short (a b h : IProp) (hc : Cons h) (hcert : PrI (iiff a b) h = 1) :
    PrI a h = PrI b h := by
  have hba : PrI (iand b (inot a)) h = 0 := by
    have s := def_IX_i (iand b (inot a)) (iiff a b) h
    have z1 := conj_neg_cert_zero (iand b (inot a)) (iiff a b) h hc hcert
    have z2 : PrI (iand (iand b (inot a)) (iiff a b)) h = 0 :=
      taut_neg_zero
        (Form.conj (Form.conj (Form.var 1) (Form.neg (Form.var 0)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h hc
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  have hab : PrI (iand a (inot b)) h = 0 := by
    have s := def_IX_i (iand a (inot b)) (iiff a b) h
    have z1 := conj_neg_cert_zero (iand a (inot b)) (iiff a b) h hc hcert
    have z2 : PrI (iand (iand a (inot b)) (iiff a b)) h = 0 :=
      taut_neg_zero
        (Form.conj (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
          (Form.iffF (Form.var 0) (Form.var 1)))
        (fun n => match n with | 0 => a | _ => b) h hc
        (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
    linarith
  have e1 := def_IX_i a b h
  have e2 := def_IX_i b a h
  have e3 := def_X_left_i a b h
  have e4 := def_X_right_i b a h
  linarith

/-- 認証代入 (pedantic 代入原理): 構文的トートロジー ↔ の解釈同士は
(整合な証拠の下で) 確率が等しい。融合形 ax_iii_op のあった場所に、
ax_iii_taut + th_12_i の合成が立つ。但し書き `Cons h` は公理 (i) の姿。
#print axioms の出力は th_12_i のそれを含む上界であり、def_VIII_i は
th_12_i_short に差し替えれば消える。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-! ## 移植定理 (pedantic コストの測定、H18/H19) -/

/-- **Th.(24) 内包版** 加法定理 (folio 144)。外延版の 2 回の ax_iii_op 書換えが、
2 枚の Taut 証明 (2 変数・4 割当の真理値計算) に置き換わる。
但し書き `Cons h` は代入原理 (公理 (i)) の姿。印刷に但し書きは無い
(docs/COLLATION_INDEX_1921.md、T 前提の補充)。#print axioms の出力 (H19) は
subst_taut 経由の上界であり、def_VIII_i の必要性は主張しない。 -/
theorem th_24_i (a b h : IProp) (hc : Cons h) :
    PrI (ior a b) h = PrI a h + PrI b h - PrI (iand a b) h := by
  have step1 := def_IX_i (ior a b) b h
  have e1 : PrI (iand (ior a b) (inot b)) h = PrI (iand a (inot b)) h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.neg (Form.var 1)))
      (Form.conj (Form.var 0) (Form.neg (Form.var 1)))
      (fun n => match n with | 0 => a | _ => b) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have e2 : PrI (iand (ior a b) b) h = PrI b h :=
    subst_taut
      (Form.conj (Form.disj (Form.var 0) (Form.var 1)) (Form.var 1))
      (Form.var 1)
      (fun n => match n with | 0 => a | _ => b) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have step3 := def_IX_i a b h
  linarith [step1, e1, e2, step3]

/-- **Th.(14.36) 内包版** 乗法定理 (無関連性下)。代入不要、Def.X のみ。
但し書き不要 (Cons を使わない)。 -/
theorem th_14_36_i (a b h : IProp) (hindep : PrI a (iand b h) = PrI a h) :
    PrI (iand a b) h = PrI a h * PrI b h := by
  have hx := def_X_left_i a b h
  rw [hindep] at hx
  exact hx

/-- **Th.(14.38)_full 内包版** Bayes 反転。代入不要、Def.X 両形 + Def.XI。
但し書き不要 (Cons を使わない)。 -/
theorem th_14_38_full_i (a b h : IProp) (hb : PrI b h ≠ 0) :
    PrI a (iand b h) = PrI b (iand a h) * PrI a h / PrI b h := by
  have hl := def_X_left_i a b h
  have hr := def_X_right_i a b h
  have heq : PrI a (iand b h) * PrI b h = PrI b (iand a h) * PrI a h := by
    rw [← hl, hr]
  exact def_XI_i _ _ _ hb heq

/-! ## 旧経路の遮断 (prose)

修復前は pr_self_evidence (任意の a, h で a/(a ∧ h) = 1) が ax_iii_taut と
def_VIII_i の逆向きから導けた。修復後、同じ経路は `Cons (iand a h)` を要する:
`Cons h → Cons (iand a h) → PrI a (iand a h) = 1` は依然として導ける
(下の th_13_13_conj_i、第13章 (13) 「a/a = 1, unless a is inconsistent」の
前提 a ∧ h 版)。但し書きなしの形が導けないことは、修復後の全公理を満たし
pr_self_evidence を満たさない有限モデル (phase6c_model.lean,
model_not_self_evidence, not_self_evidence) による。 -/

/-- **Th.(13) の前提 a ∧ h 版**: a/(a ∧ h) = 1、但し a ∧ h が整合なとき
(folio 141: 「(13) a/a = 1, unless a is inconsistent」)。Keynes の (13) は前提 a
そのものだが、本公理系には前提側の置換 (公理 (ii)) が無いので a ∧ h の形で
述べる (docs/COLLATION_INDEX_1921.md、T 前提の補充)。 -/
theorem th_13_13_conj_i (a h : IProp) (hc : Cons h) (hca : Cons (iand a h)) :
    PrI a (iand a h) = 1 := by
  have hcert : PrI (iiff a a) h = 1 :=
    ax_iii_taut (Form.iffF (Form.var 0) (Form.var 0)) (fun _ => a) h hc
      (by intro v; simp [evalB])
  exact ((def_VIII_i a a h hca hca).mp hcert).1

/-! ## 縮退の遮断 (H15 の状況、prose)

外延版の縮退定理 th_15_degeneracy は `by_cases hα : α` — すなわち
Classical.em による真理値場合分け — を本質的に使った。ここでは a : IProp は
命題ではなく不透明型の項であり、`by_cases ha : a` は**型エラー**になる
(case split の対象が Prop でない)。実質的同値を製造する経路が型レベルで
存在しないため、縮退定理の内包版は本公理系では述べても証明手段がない。
導出不能性の正の証明 (健全性経由) は、値 1/2 を実現する有限モデルの構成による
(phase6c_model.lean, model_intermediate_value)。 -/

end KeynesI

/-! ## 監査クエリ (Phase 6c 本番) -/

#check @KeynesI.th_12_i
#check @KeynesI.th_12_i_short
#check @KeynesI.subst_taut
#check @KeynesI.itrue_certain
#check @KeynesI.th_13_1_i
#check @KeynesI.th_24_i
#check @KeynesI.th_14_36_i
#check @KeynesI.th_14_38_full_i
#check @KeynesI.th_13_13_conj_i

-- Kernel 依存. 注目点:
--   itrue_certain    : ax_iii_taut のみ (Cons h は前提)
--   true_conj        : ax_iii_taut + cons_of_pos + def_X_left_i
--   th_13_1_i        : (1) が ax_iii_taut の最初の使用点に戻った (Keynes の順)
--   th_12_i          : ★ H17 判定点 — 初版 {def_VIII_i, def_X_left_i, def_X_right_i}
--                      に def_IX_i, ax_iii_taut, cons_of_pos が加わる (上界)
--   th_12_i_short    : 同じ結論で def_VIII_i を含まない (def_VIII_i は除ける)
--   th_24_i          : ★ H19 判定点 — pedantic コスト (上界)
--   th_14_36_i/38_i  : 代入フリー definitional 群 (Cons 不要、初版と同コスト)
--   全理             : ★ H18 — Form/evalB/Taut は axiom として現れないはず
--   cons_true, cons_of_pos_src, cons_iff_taut, def_VIII_i_src は本ファイルの
--   どの定理にも現れない
#print axioms KeynesI.itrue_certain
#print axioms KeynesI.true_conj
#print axioms KeynesI.th_13_1_i
#print axioms KeynesI.taut_neg_zero
#print axioms KeynesI.conj_neg_cert_zero
#print axioms KeynesI.th_12_i
#print axioms KeynesI.th_12_i_short
#print axioms KeynesI.subst_taut
#print axioms KeynesI.th_24_i
#print axioms KeynesI.th_14_36_i
#print axioms KeynesI.th_14_38_full_i
#print axioms KeynesI.th_13_13_conj_i
