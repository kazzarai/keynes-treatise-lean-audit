/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 16a
#
# **第17章 §2 (folio 187–189): ブールの挑戦問題 (56)–(56.5) と乗法 (Def. X) の暗黙使用**
#
# ## 対象
#   (56) の設定 a₁/h = c₁, a₂/h = c₂, e/a₁h = p₁, e/a₂h = p₂ (求めるのは e/h = u) を
#   KeynesI 担体 (IProp, PrI, Cons) の上に置き、(56)–(56.5) の証明行を Keynes の順に
#   再証明する。phase10d の 56 系 (l004, l014, l017, l018, l021, l023, l025, l035, l036) は
#   名前に `_i` を付けて再掲し、(56.1)–(56.5) の言明を本担体で述べ直す (phase5 の
#   th_17_56_1–5 は `Prop → Prop → ℝ` の担体)。Boole の原著の式は扱わない。
#
# ## 問い
#   phase5 ヘッダ H6 は (56) が def_IX・ax_iii_op・def_X_left・def_X_right の 4 公理を同時に
#   要すると記録した。一方 Keynes は §2 (56)–(56.5) で X. を一度も引かない。本文の引用語
#   (照合語) とカーネルの被導出関係を行ごとに並べ、乗法がどの行で引用なしに使われているかを
#   確定する。
#
# ## 方法
#   各行に二つの定理を置く。
#   (1) 本定理 `th_17_56_lNNN_i`: 記号の約束と前提 (e/ā₁ā₂h = 0, Cons h) だけから行を導く。
#   (2) 引用版 `th_17_56_lNNN_cited`: Keynes が引く定理 ((24), (24.2), (4)) の当該の場合と、
#       「∴」「so that」「from the same equations」で受ける先行行を仮定に取り、その行の
#       段だけを証明する。引用版の #print axioms に def_X_left_i / def_X_right_i が残れば、
#       その段で乗法を引用なしに使っている。残らなければ、乗法は先行行か引用定理から来る。
#   乗法の必要性は、def_X 以外の公理 11 本をすべて満たし (56.1) が偽になる有限模型
#   (§ 模型、4 世界、条件ごとに重みが変わる) で示す。
#
# ## 2 列表 (folio 187–189; 照合語は 1921 年版の頁画像から転記)
#   印: ★ = 本文は乗法 (X.) を引かず、その行の段がカーネルで def_X を要する (引用版に def_X が残る)。
#       ☆ = 段そのものは算術だけ (引用版に def_X が無い) で、def_X は先行の ★ 行から受け継ぐ。
#       △ = def_X は引用された定理 (24) か、本文が引かない (1)・代入原理 (12) を経て入る。
#           Keynes 自身の (12) の証明は「by X.」(folio 141, ch13-076)、(4) は「by X. and (iv. b)」
#           (folio 140, ch13-023)、(24) の証明 (folio 144, ch14-004) は ā/bh . b/h を「by (iii.)
#           and IX.」と書く。
#       — = def_X を要しない。
#   公理の略記: L = def_X_left_i, R = def_X_right_i, XI = def_XI_i, IX = def_IX_i,
#     T = ax_iii_taut, P = cons_of_pos, lo/hi = ax_range_lo_i/hi_i。担体の定数 (IProp, PrI, iand,
#     ior, inot, iiff, itrue, Cons) と Lean 標準 (propext, Classical.choice, Quot.sound) は省く。
#     各行の #print axioms の全文はファイル末尾の出力。
#
#   | 行 (folio) | 印刷 | Keynes 本文の照合語 | 本定理の公理 | 引用版の公理 | 印 |
#   |---|---|---|---|---|---|
#   | ch17-004 (187) | u = c₁p₁ + c₂p₂ (排反の場合) | 「the solution is」(引用なし) | IX T P L R | L | ★ (ea_r/h = c_r p_r と ea₁a₂/h = 0) |
#   | ch17-013 (188) | e/ā₁ā₂h = 0 | 「Since the event cannot occur in the absence of both the causes」 | (前提) | — | — |
#   | ch17-014/015 (188) | ā₁ā₂/eh = 0, unless e/h = 0 | 「It follows from this that … unless」(引用なし) | L R | (本定理が段そのもの) | ★ (逆確率: 左右両向き) |
#   | ch17-016 (188) | (a₁ + a₂)/eh = 1 | 「i.e.」(引用なし) | IX T P L R | なし (公理 0) | △ ((1) と代入原理 (12) を経る) |
#   | ch17-017 (188) | a₁/eh + a₂/eh = 1 + a₁a₂/eh | 「whence … by (24).」 | IX T P L R | なし | △ ((24) を経る) |
#   | ch17-018 (188) | a₁/eh = c₁p₁/u, a₂/eh = c₂p₂/u | 「Now」(引用なし) | L R XI | (本定理が段そのもの) | ★ (第 14 章 (38) の Bayes 反転と同じ公理の組) |
#   | ch17-019 (188) | ∴ u = (c₁p₁ + c₂p₂)/(1 + z) | 「∴」 | IX T P L R XI lo | lo | ☆ (018 から) |
#   | ch17-021 (188) | y = a₁a₂/eh . e/h = uz | 「If we write ea₁a₂/h = y,」(引用なし) | R | (本定理が段そのもの) | ★ |
#   | ch17-022 (188) | u = (c₁p₁ + c₂p₂) − y | 「so that」 | IX T P L R | なし | ☆ (019・021 から) |
#   | ch17-023 (188) | y ⩾ 0 | 「since」 | lo | — | — |
#   | ch17-024 (188) | u ⩽ c₁p₁ + c₂p₂ | 「then, since y ⩾ 0,」 | IX T P L R lo | なし | ☆ (022 から) |
#   | ch17-025 (188) | e/h = eā₁/h + ea₁/h ⩽ ā₁/h + ea₁/h ⩽ 1 − c₁ + c₁p₁ | 「by (24.2) and (4).」 | IX T P L lo hi | L | ★ (ea₁/h = c₁p₁ は (24.2)・(4) の外) |
#   | ch17-026 (188) | e/h ⩽ 1 − c₂ + c₂p₂ | 「Similarly」 | IX T P L lo hi | (025 と同じ) | ★ |
#   | ch17-027/028 (188) | e/h ⩾ c₁p₁ and ⩾ c₂p₂ | 「From the same equations it appears that」 | IX L lo | L lo | ★ |
#   | ch17-029 (189) | ∴ u lies between the greatest of {…} and the least of {…} | 「∴」 | IX T P L R lo hi | なし | ☆ (024–028 から) |
#   | ch17-030 (189) | (56.2) u < p₁ + p₂ (修正形 ⩽) | 「Suppose that … c₁ and c₂ are to be eliminated. The only limit we then have is」 | IX T P L R lo hi | lo hi | ☆ (024 から) |
#   | ch17-031 (189) | (56.3) c₁p₁ ⩽ u ⩽ 1 − c₁ + c₁p₁ | 「We then have limits」 | IX T P L lo hi | なし | ☆ (025・027 から) |
#   | ch17-032/033 (189) | (56.4) c₁p₁ ⩽ u ⩽ c₁p₁ + c₂ ⩽ c₁p₁ + 1 − c₁ | 「We then have」 | IX T P L R lo hi | lo hi | ☆ (024・025・027 から) |
#   | ch17-034 (189) | (56.5) a₁/a₂h = a₁/h | 「If …, i.e. if our knowledge of each of the causes is independent」 | (前提) | — | — |
#   | ch17-035 (189) | y = ea₁a₂/h = e/a₁a₂h . a₁/a₂h . a₂/h = e/a₁a₂h . c₁c₂ | 「For」(引用なし) | L | (本定理が段そのもの) | ★ (左向き 2 回) |
#   | ch17-036 (189) | ∴ u = c₁p₁ + c₂p₂ − c₁c₂ . e/a₁a₂h | 「∴」 | IX T P L R | なし | ☆ (022・035 から) |
#   | ch17-037 (189) | ∴ u > c₁p₁ + c₂p₂ − c₁c₂ (修正形 ⩾) | 「∴」 | IX T P L R lo hi | lo hi | ☆ (036 から) |
#
#   結論: §2 の (56)–(56.5) で本文が引く定理は (24) (ch17-017) と (24.2)・(4) (ch17-025) だけで、
#   「by X.」「by IX.」の語はない。カーネルで乗法の段そのものが要るのは ★ の 7 行
#   (004, 014, 018, 021, 025/026, 027/028, 035) で、いずれも本文に引用語がない
#   (014・018・021・035 は「It follows」「Now」「If we write」「For」、027 は「From the same
#   equations」、025 は引用 (24.2)・(4) の外で ea₁/h を c₁p₁ と書き替える)。☆ の 9 行は ★ から
#   乗法を受け継ぎ、△ の 2 行は引用定理か代入原理を経る。仮説「Keynes は挑戦問題の説明で
#   乗法定理を暗黙の導出関数として使っている」は、★ の 7 行について確定する。
#
# ## 逆確率と乗法 (両向き)
#   ch17-018 の比 a₁/eh = c₁p₁/u は第 14 章 (38) の Bayes 反転 th_14_38_full_i の a := a₁,
#   b := e の場合そのもので、th_17_56_l018_i は th_14_38_full_i から一段で出す。両者の
#   #print axioms は同じ組 {def_X_left_i, def_X_right_i, def_XI_i} (と担体の定数) を返す。
#   a₁e/h を a₁/eh . e/h (左向き) と e/a₁h . a₁/h (右向き) の二通りに書いて等置するので、比を
#   作るには両向きが要る。ch17-014 (ā₁ā₂/eh = 0) も同じ反転 (ā₁ā₂/eh . e/h = e/ā₁ā₂h . ā₁ā₂/h)
#   で、def_X_left_i と def_X_right_i の両方に依る。右向きだけの行 (021) と左向きだけの行
#   (025, 027, 035) もある。片向きだけを満たす模型は置いていない: 連言が可換な集合模型では
#   左向きの全称と右向きの全称は互いに導かれる。
#
# ## 乗法の必要性
#   (a) 模型 (§ 模型): 4 世界 W = Fin 4 の部分集合を命題とし、x/h を「条件 h ごとの重み」の比
#       で与える。h = ⊤ では一様、h ≠ ⊤ では世界 w に重み w + 1。条件ごとに重みが変わるので
#       def_X は成り立たない。def_X_left_i・def_X_right_i を除く本ファイルの公理 11 本は
#       すべて成り立つ (noX_sys)。この模型で e := {0, 2}, a₁ := {0, 1}, a₂ := {2, 3}, h := ⊤
#       とすると Cons h かつ e/ā₁ā₂h = 0 だが、u = 1/2 > c₁p₁ + c₂p₂ = 1/6 + 3/14 = 8/21
#       で (56.1) は偽 (model_56_1_fails)。ch17-018 の比も偽 (a₁/eh = 1/4 ≠ c₁p₁/u = 1/3、
#       model_18_fails)。よって (56.1) と (56) の比は def_X 抜きの公理からは導けない。
#   (b) RED の記録 (写しを lake env lean で検査、写しは残していない):
#       `axiom def_X_right_i` を除いた写し: th_12_i_short・th_14_38_full_i・th_17_56_l014_i・
#       th_17_56_l021_i の 4 か所で「Unknown identifier `def_X_right_i`」。#print axioms に
#       sorryAx が出るのは 19 本: th_12_i_short, subst_taut, th_24_i, th_14_38_full_i,
#       th_17_56_raw_i, l004_i, l014_i, l016_i, l017_i, l018_i, l019_i, l021_i, l022_i, l024_i,
#       th_17_56_1_i, 2_i, 4_i, l036_i, 5_i (左形だけの 025/026/027/(56.3)/035 と引用版は残る)。
#       `axiom def_X_left_i` を除いた写し: true_conj・conj_neg_cert_zero・th_12_i_short・
#       th_14_38_full_i・th_17_56_raw_i・l004_i・l004_cited・l014_i・l022_i・l025_i・
#       l025_cited・l027_i・l027_cited・l035_i の 14 か所で「Unknown identifier `def_X_left_i`」。
#       sorryAx が出るのは 30 本 (itrue_certain・l023_i・右形だけの l021_i、def_X を含まない
#       引用版 016/017/019/022/024/(56.1)/(56.2)/(56.3)/(56.4)/036/(56.5)、模型の定理以外のすべて)。
#       (b) は「この証明が落ちる」ことの記録で、導けないことの証明は (a)。
#
# ## 印刷形が成り立たない行
#   ch17-030 (56.2) と ch17-037 (56.5) の狭義の不等号 (COLLATION の S)。本ファイルは修正形
#   (⩽, ⩾) を述べる。反例は phase15a_ch05_ch08 の th_17_56_2_strict_cm・th_17_56_5_strict_cm。
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase16a_boole_challenge.lean
-/

import Mathlib

open Finset

namespace KeynesI

/-! ## 内包的キャリアと公理 (phase6c・phase10d と同形) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 `Cons h`: 「h は矛盾する連言でない」(folio 135、公理 (i))。 -/
axiom Cons : IProp → Prop

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- Def. VIII (folio 134) 双条件読み、但し書き付き (phase6c と同形)。 -/
axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- Def. VIII 印刷どおり (→ のみ; phase6c と同形)。 -/
axiom def_VIII_i_src (a b h : IProp) :
    PrI b (iand a h) = 1 → PrI a (iand b h) = 1 → PrI (iiff a b) h = 1

/-- 命題論理の構文 (phase6c と同形)。 -/
inductive Form : Type where
  | var  : ℕ → Form
  | tru  : Form
  | fls  : Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | neg  : Form → Form
  | iffF : Form → Form → Form

def evalB (v : ℕ → Bool) : Form → Bool
  | .var n    => v n
  | .tru      => true
  | .fls      => false
  | .conj f g => evalB v f && evalB v g
  | .disj f g => evalB v f || evalB v g
  | .neg f    => !(evalB v f)
  | .iffF f g => evalB v f == evalB v g

def Taut (f : Form) : Prop := ∀ v : ℕ → Bool, evalB v f = true

noncomputable def interp (env : ℕ → IProp) : Form → IProp
  | .var n    => env n
  | .tru      => itrue
  | .fls      => inot itrue
  | .conj f g => iand (interp env f) (interp env g)
  | .disj f g => ior (interp env f) (interp env g)
  | .neg f    => inot (interp env f)
  | .iffF f g => iiff (interp env f) (interp env g)

/-- Ax.(iii) 但し書き付き (phase6c と同形)。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

axiom cons_true : Cons itrue
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0
/-- a/h ≠ 0 かつ h 整合ならば ah 整合 (phase6c と同形; Def. VI の逆向き、(10) folio 140)。 -/
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## phase6c・phase10d の定理の写し (補完律 (1)、Th.(12)、代入原理、(24)、Bayes 反転) -/

theorem itrue_certain (h : IProp) (hc : Cons h) : PrI itrue h = 1 :=
  ax_iii_taut Form.tru (fun _ => itrue) h hc (fun _ => rfl)

theorem true_conj (a h : IProp) (hc : Cons h) : PrI (iand itrue a) h = PrI a h := by
  have hr := def_X_left_i itrue a h
  by_cases ha : PrI a h = 0
  · rw [ha, mul_zero] at hr
    rw [hr, ha]
  · have hca : Cons (iand a h) := cons_of_pos a h ha hc
    rw [itrue_certain (iand a h) hca, one_mul] at hr
    exact hr

/-- 第13章の式 (1) (folio 139): a/h + ā/h = 1。 -/
theorem th_13_1_i (a h : IProp) (hc : Cons h) : PrI a h + PrI (inot a) h = 1 := by
  have step := def_IX_i itrue a h
  rw [true_conj (inot a) h hc, true_conj a h hc, itrue_certain h hc] at step
  linarith

theorem taut_neg_zero (f : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.neg f)) : PrI (interp env f) h = 0 := by
  have h1 : PrI (inot (interp env f)) h = 1 := ax_iii_taut (Form.neg f) env h hc ht
  have h2 := th_13_1_i (interp env f) h hc
  linarith

theorem conj_neg_cert_zero (x E h : IProp) (hc : Cons h) (hE : PrI E h = 1) :
    PrI (iand x (inot E)) h = 0 := by
  have h1 := th_13_1_i E h hc
  have hnE : PrI (inot E) h = 0 := by linarith
  rw [def_X_left_i x (inot E) h, hnE, mul_zero]

/-- Th.(12) (folio 141) の短い証明 (phase6c th_12_i_short の写し; def_VIII_i を用いない)。 -/
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

/-- 代入原理 (phase6c subst_taut の写し; th_12_i_short 経由)。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i_short _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-- Th.(24) (folio 144) 加法定理 (phase6c th_24_i の写し)。 -/
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

/-- **Th.(14.38)_full 内包版** Bayes 反転 (phase6c th_14_38_full_i の写し)。
Def. X 両形 + Def. XI。 -/
theorem th_14_38_full_i (a b h : IProp) (hb : PrI b h ≠ 0) :
    PrI a (iand b h) = PrI b (iand a h) * PrI a h / PrI b h := by
  have hl := def_X_left_i a b h
  have hr := def_X_right_i a b h
  have heq : PrI a (iand b h) * PrI b h = PrI b (iand a h) * PrI a h := by
    rw [← hl, hr]
  exact def_XI_i _ _ _ hb heq

/-- (56) の生の分解 (phase10d th_17_56_raw_i の写し): e/ā₁ā₂h = 0 ならば
e/h = ea₁/h + ea₂/h − ea₁a₂/h。乗法を使わない ((24) と代入原理だけ)。 -/
theorem th_17_56_raw_i (a₁ a₂ e h : IProp) (hc : Cons h)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    PrI e h = PrI (iand e a₁) h + PrI (iand e a₂) h - PrI (iand e (iand a₁ a₂)) h := by
  have s1 := def_IX_i e (ior a₁ a₂) h
  have e1 : PrI (iand e (inot (ior a₁ a₂))) h = PrI (iand e (iand (inot a₁) (inot a₂))) h :=
    subst_taut (Form.conj (.var 0) (Form.neg (Form.disj (.var 1) (.var 2))))
      (Form.conj (.var 0) (Form.conj (Form.neg (.var 1)) (Form.neg (.var 2))))
      (fun n => match n with | 0 => e | 1 => a₁ | _ => a₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  have z1 : PrI (iand e (iand (inot a₁) (inot a₂))) h = 0 := by
    rw [def_X_left_i, hexh, zero_mul]
  have e2 : PrI (iand e (ior a₁ a₂)) h = PrI (ior (iand e a₁) (iand e a₂)) h :=
    subst_taut (Form.conj (.var 0) (Form.disj (.var 1) (.var 2)))
      (Form.disj (Form.conj (.var 0) (.var 1)) (Form.conj (.var 0) (.var 2)))
      (fun n => match n with | 0 => e | 1 => a₁ | _ => a₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  have t24 := th_24_i (iand e a₁) (iand e a₂) h hc
  have e3 : PrI (iand (iand e a₁) (iand e a₂)) h = PrI (iand e (iand a₁ a₂)) h :=
    subst_taut (Form.conj (Form.conj (.var 0) (.var 1)) (Form.conj (.var 0) (.var 2)))
      (Form.conj (.var 0) (Form.conj (.var 1) (.var 2)))
      (fun n => match n with | 0 => e | 1 => a₁ | _ => a₂) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;>
            simp [evalB, h0, h1, h2])
  linarith

/-! ## (56) (folio 187–188): 二つの原因の問題

記号の約束 (ch17-006–012, 020): a₁/h = c₁, a₂/h = c₂, e/a₁h = p₁, e/a₂h = p₂, e/h = u,
a₁a₂/eh = z, ea₁a₂/h = y。いずれも定理の前提 (hc₁ … hy) に置く。網羅の前提は
Keynes の e/ā₁ā₂h = 0 (ch17-013) をそのまま hexh とする。 -/

/-- **ch17-004 (folio 187)** 原因が排反 (a₁a₂/h = 0) のとき u = c₁p₁ + c₂p₂
(phase10d th_17_56_l004 の再掲)。本文「the solution is」(引用なし)。 -/
theorem th_17_56_l004_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0)
    (hexcl : PrI (iand a₁ a₂) h = 0) :
    u = c₁ * p₁ + c₂ * p₂ := by
  have raw := th_17_56_raw_i a₁ a₂ e h hc hexh
  have x1 := def_X_left_i e a₁ h
  have x2 := def_X_left_i e a₂ h
  have x3 := def_X_left_i e (iand a₁ a₂) h
  rw [hexcl, mul_zero] at x3
  rw [hp₁, hc₁] at x1
  rw [hp₂, hc₂] at x2
  rw [← hu]
  linarith

/-- **ch17-004 引用版**: 生の分解 e/h = ea₁/h + ea₂/h − ea₁a₂/h ((24) と代入原理の帰結) と
排反 a₁a₂/h = 0 を仮定に取る。残る段 ea_r/h = c_r p_r と ea₁a₂/h = e/a₁a₂h . a₁a₂/h = 0 に
Def. X 左形が残る。 -/
theorem th_17_56_l004_cited (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (raw : PrI e h = PrI (iand e a₁) h + PrI (iand e a₂) h - PrI (iand e (iand a₁ a₂)) h)
    (hexcl : PrI (iand a₁ a₂) h = 0) :
    u = c₁ * p₁ + c₂ * p₂ := by
  have x1 := def_X_left_i e a₁ h
  have x2 := def_X_left_i e a₂ h
  have x3 := def_X_left_i e (iand a₁ a₂) h
  rw [hexcl, mul_zero] at x3
  rw [hp₁, hc₁] at x1
  rw [hp₂, hc₂] at x2
  rw [← hu]
  linarith

/-- **ch17-013, 014, 015 (folio 188)** e/ā₁ā₂h = 0 ならば ā₁ā₂/eh = 0、ただし e/h = 0 の
場合を除く (phase10d th_17_56_l014 の再掲)。本文「It follows from this that … unless」。
段そのものが逆確率 ā₁ā₂/eh . e/h = e/ā₁ā₂h . ā₁ā₂/h で、Def. X の左右両形を使う。 -/
theorem th_17_56_l014_i (a₁ a₂ e h : IProp)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    PrI (iand (inot a₁) (inot a₂)) (iand e h) = 0 ∨ PrI e h = 0 := by
  have l := def_X_left_i (iand (inot a₁) (inot a₂)) e h
  have r := def_X_right_i (iand (inot a₁) (inot a₂)) e h
  rw [hexh, zero_mul] at r
  rw [r] at l
  exact mul_eq_zero.mp l.symm

/-- **ch17-016 (folio 188)** (a₁ + a₂)/eh = 1 (e/h ≠ 0 のとき)。本文「i.e.」。
ā₁ā₂/eh = 0 (ch17-014) から、補完律 (1) と a₁ + a₂ ≡ ‾(ā₁ā₂) の代入 (公理 (iii.) と (12)) で。
Cons (eh) は cons_of_pos で e/h ≠ 0 と Cons h から出す。 -/
theorem th_17_56_l016_i (a₁ a₂ e h : IProp) (hc : Cons h) (hu0 : PrI e h ≠ 0)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    PrI (ior a₁ a₂) (iand e h) = 1 := by
  have hceh : Cons (iand e h) := cons_of_pos e h hu0 hc
  have h014 : PrI (iand (inot a₁) (inot a₂)) (iand e h) = 0 :=
    (th_17_56_l014_i a₁ a₂ e h hexh).resolve_right hu0
  have hdm : PrI (ior a₁ a₂) (iand e h)
      = PrI (inot (iand (inot a₁) (inot a₂))) (iand e h) :=
    subst_taut (Form.disj (.var 0) (.var 1))
      (Form.neg (Form.conj (Form.neg (.var 0)) (Form.neg (.var 1))))
      (fun n => match n with | 0 => a₁ | _ => a₂) (iand e h) hceh
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> simp [evalB, h0, h1])
  have h1 := th_13_1_i (iand (inot a₁) (inot a₂)) (iand e h) hceh
  linarith

/-- **ch17-016 引用版**: ch17-014 の結論、(1) の当該の場合、代入 a₁ + a₂ ≡ ‾(ā₁ā₂) を仮定に
取ると、段は算術だけ (公理を要しない)。 -/
theorem th_17_56_l016_cited (a₁ a₂ e h : IProp)
    (h014 : PrI (iand (inot a₁) (inot a₂)) (iand e h) = 0)
    (h1 : PrI (iand (inot a₁) (inot a₂)) (iand e h)
        + PrI (inot (iand (inot a₁) (inot a₂))) (iand e h) = 1)
    (hdm : PrI (ior a₁ a₂) (iand e h) = PrI (inot (iand (inot a₁) (inot a₂))) (iand e h)) :
    PrI (ior a₁ a₂) (iand e h) = 1 := by
  linarith

/-- **ch17-017 (folio 188)** a₁/eh + a₂/eh = 1 + a₁a₂/eh、「whence … by (24).」
(phase10d th_17_56_l017 の再掲)。 -/
theorem th_17_56_l017_i (a₁ a₂ e h : IProp) (hc : Cons (iand e h))
    (h016 : PrI (ior a₁ a₂) (iand e h) = 1) :
    PrI a₁ (iand e h) + PrI a₂ (iand e h) = 1 + PrI (iand a₁ a₂) (iand e h) := by
  have := th_24_i a₁ a₂ (iand e h) hc
  linarith

/-- **ch17-017 引用版**: (24) の当該の場合 (前提 eh) を仮定に取ると、段は算術だけ。 -/
theorem th_17_56_l017_cited (a₁ a₂ e h : IProp)
    (h24 : PrI (ior a₁ a₂) (iand e h)
        = PrI a₁ (iand e h) + PrI a₂ (iand e h) - PrI (iand a₁ a₂) (iand e h))
    (h016 : PrI (ior a₁ a₂) (iand e h) = 1) :
    PrI a₁ (iand e h) + PrI a₂ (iand e h) = 1 + PrI (iand a₁ a₂) (iand e h) := by
  linarith

/-- **ch17-018 (folio 188)** a₁/eh = c₁p₁/u, a₂/eh = c₂p₂/u、本文「Now」(引用なし)。
第 14 章 (38) の Bayes 反転 th_14_38_full_i (a := aᵣ, b := e) から一段で出す。 -/
theorem th_17_56_l018_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hu0 : u ≠ 0) :
    PrI a₁ (iand e h) = c₁ * p₁ / u ∧ PrI a₂ (iand e h) = c₂ * p₂ / u := by
  have hu0' : PrI e h ≠ 0 := by rw [hu]; exact hu0
  have b1 := th_14_38_full_i a₁ e h hu0'
  have b2 := th_14_38_full_i a₂ e h hu0'
  rw [hp₁, hc₁, hu] at b1
  rw [hp₂, hc₂, hu] at b2
  exact ⟨by rw [b1, mul_comm p₁], by rw [b2, mul_comm p₂]⟩

/-- **ch17-019 引用版**: ch17-017 と ch17-018 を仮定に取ると、u = (c₁p₁ + c₂p₂)/(1 + z) は
算術と z ⩾ 0 (範囲公理) だけで出る。 -/
theorem th_17_56_l019_cited (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u z : ℝ)
    (hz : PrI (iand a₁ a₂) (iand e h) = z) (hu0 : u ≠ 0)
    (h017 : PrI a₁ (iand e h) + PrI a₂ (iand e h) = 1 + PrI (iand a₁ a₂) (iand e h))
    (h018 : PrI a₁ (iand e h) = c₁ * p₁ / u ∧ PrI a₂ (iand e h) = c₂ * p₂ / u) :
    u = (c₁ * p₁ + c₂ * p₂) / (1 + z) := by
  have hz0 : 0 ≤ z := hz ▸ ax_range_lo_i _ _
  have hz1 : (1 + z) ≠ 0 := by positivity
  have e1 : PrI a₁ (iand e h) * u = c₁ * p₁ := by rw [h018.1, div_mul_cancel₀ _ hu0]
  have e2 : PrI a₂ (iand e h) * u = c₂ * p₂ := by rw [h018.2, div_mul_cancel₀ _ hu0]
  rw [eq_div_iff hz1, ← hz]
  linear_combination e1 + e2 - u * h017

/-- **ch17-019 (folio 188)** ∴ u = (c₁p₁ + c₂p₂)/(1 + z) (印刷の分数形; u ≠ 0)。 -/
theorem th_17_56_l019_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u z : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hz : PrI (iand a₁ a₂) (iand e h) = z)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) (hu0 : u ≠ 0) :
    u = (c₁ * p₁ + c₂ * p₂) / (1 + z) := by
  have hu0' : PrI e h ≠ 0 := by rw [hu]; exact hu0
  have hceh := cons_of_pos e h hu0' hc
  have h016 := th_17_56_l016_i a₁ a₂ e h hc hu0' hexh
  have h017 := th_17_56_l017_i a₁ a₂ e h hceh h016
  have h018 := th_17_56_l018_i a₁ a₂ e h c₁ c₂ p₁ p₂ u hc₁ hc₂ hp₁ hp₂ hu hu0
  exact th_17_56_l019_cited a₁ a₂ e h c₁ c₂ p₁ p₂ u z hz hu0 h017 h018

/-- **ch17-020, 021 (folio 188)** ea₁a₂/h = y の下で y = a₁a₂/eh . e/h = uz
(phase10d th_17_56_l021 の再掲)。本文「If we write ea₁a₂/h = y,」(引用なし)。Def. X 右形。 -/
theorem th_17_56_l021_i (a₁ a₂ e h : IProp) (u z y : ℝ) (hu : PrI e h = u)
    (hz : PrI (iand a₁ a₂) (iand e h) = z) (hy : PrI (iand e (iand a₁ a₂)) h = y) :
    y = PrI (iand a₁ a₂) (iand e h) * PrI e h
      ∧ PrI (iand a₁ a₂) (iand e h) * PrI e h = u * z := by
  have r := def_X_right_i e (iand a₁ a₂) h
  refine ⟨by rw [← hy, r], by rw [hz, hu, mul_comm]⟩

/-- **ch17-022 引用版**: ch17-019 と ch17-021 を仮定に取ると、u = (c₁p₁ + c₂p₂) − y は
算術だけ。 -/
theorem th_17_56_l022_cited (c₁ c₂ p₁ p₂ u z y : ℝ) (hz1 : 1 + z ≠ 0)
    (h019 : u = (c₁ * p₁ + c₂ * p₂) / (1 + z)) (h021 : y = u * z) :
    u = (c₁ * p₁ + c₂ * p₂) - y := by
  rw [eq_div_iff hz1] at h019
  rw [h021]
  linear_combination h019

/-- **ch17-022 (folio 188)** u = (c₁p₁ + c₂p₂) − y、本文「so that」。u ≠ 0 を要しない形で、
生の分解と Def. X 左形 (ea₁/h = c₁p₁) から。 -/
theorem th_17_56_l022_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u y : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hy : PrI (iand e (iand a₁ a₂)) h = y)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    u = (c₁ * p₁ + c₂ * p₂) - y := by
  have raw := th_17_56_raw_i a₁ a₂ e h hc hexh
  have x1 := def_X_left_i e a₁ h
  have x2 := def_X_left_i e a₂ h
  rw [hp₁, hc₁] at x1
  rw [hp₂, hc₂] at x2
  rw [← hu, ← hy]
  linarith

/-- **ch17-023 (folio 188)** y ⩾ 0 (範囲公理; phase10d th_17_56_l023 の再掲)。 -/
theorem th_17_56_l023_i (a₁ a₂ e h : IProp) (y : ℝ) (hy : PrI (iand e (iand a₁ a₂)) h = y) :
    y ≥ 0 := by
  rw [← hy]; exact ax_range_lo_i _ _

/-! ## (56.1) (folio 188–189): y と z によらない限界 -/

/-- **ch17-024 引用版**: ch17-022 と ch17-023 から u ⩽ c₁p₁ + c₂p₂ (算術だけ)。 -/
theorem th_17_56_l024_cited (c₁ c₂ p₁ p₂ u y : ℝ)
    (h022 : u = (c₁ * p₁ + c₂ * p₂) - y) (h023 : y ≥ 0) :
    u ≤ c₁ * p₁ + c₂ * p₂ := by
  linarith

/-- **ch17-024 (folio 188)** u ⩽ c₁p₁ + c₂p₂、本文「then, since y ⩾ 0,」。 -/
theorem th_17_56_l024_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    u ≤ c₁ * p₁ + c₂ * p₂ :=
  th_17_56_l024_cited c₁ c₂ p₁ p₂ u _
    (th_17_56_l022_i a₁ a₂ e h c₁ c₂ p₁ p₂ u _ hc hc₁ hc₂ hp₁ hp₂ hu rfl hexh)
    (th_17_56_l023_i a₁ a₂ e h _ rfl)

/-- **ch17-025 (folio 188)** e/h = eā₁/h + ea₁/h ⩽ ā₁/h + ea₁/h ⩽ 1 − c₁ + c₁p₁、
「by (24.2) and (4).」(phase10d th_17_56_l025 の再掲)。 -/
theorem th_17_56_l025_i (a₁ e h : IProp) (c₁ p₁ : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hp₁ : PrI e (iand a₁ h) = p₁) :
    PrI e h = PrI (iand e (inot a₁)) h + PrI (iand e a₁) h
      ∧ PrI (iand e (inot a₁)) h + PrI (iand e a₁) h ≤ PrI (inot a₁) h + PrI (iand e a₁) h
      ∧ PrI (inot a₁) h + PrI (iand e a₁) h ≤ 1 - c₁ + c₁ * p₁ := by
  have s := def_IX_i e a₁ h
  have x1 := def_X_left_i e (inot a₁) h
  have hle := ax_range_hi_i e (iand (inot a₁) h)
  have hlo := ax_range_lo_i (inot a₁) h
  have x2 := def_X_left_i e a₁ h
  have c := th_13_1_i a₁ h hc
  rw [hp₁, hc₁] at x2
  refine ⟨by linarith, ?_, ?_⟩
  · have : PrI e (iand (inot a₁) h) * PrI (inot a₁) h ≤ PrI (inot a₁) h :=
      mul_le_of_le_one_left hlo hle
    linarith
  · rw [hc₁] at c
    linarith

/-- **ch17-025 引用版**: 引用された (24.2) (ab/h + āb/h = b/h を e/h = eā₁/h + ea₁/h の形で) と
(4) (ab/h ⩽ b/h を eā₁/h ⩽ ā₁/h の形で)、および補完律 (1) を仮定に取る。残る段
ea₁/h = e/a₁h . a₁/h = c₁p₁ は引用の外で、Def. X 左形を要する。 -/
theorem th_17_56_l025_cited (a₁ e h : IProp) (c₁ p₁ : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hp₁ : PrI e (iand a₁ h) = p₁)
    (h242 : PrI (iand e (inot a₁)) h + PrI (iand e a₁) h = PrI e h)
    (h4 : PrI (iand e (inot a₁)) h ≤ PrI (inot a₁) h)
    (h1 : PrI a₁ h + PrI (inot a₁) h = 1) :
    PrI e h = PrI (iand e (inot a₁)) h + PrI (iand e a₁) h
      ∧ PrI (iand e (inot a₁)) h + PrI (iand e a₁) h ≤ PrI (inot a₁) h + PrI (iand e a₁) h
      ∧ PrI (inot a₁) h + PrI (iand e a₁) h ≤ 1 - c₁ + c₁ * p₁ := by
  have x2 := def_X_left_i e a₁ h
  rw [hp₁, hc₁] at x2
  rw [hc₁] at h1
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **ch17-026 (folio 188)** e/h ⩽ 1 − c₂ + c₂p₂、本文「Similarly」(ch17-025 の a₂ 版)。 -/
theorem th_17_56_l026_i (a₂ e h : IProp) (c₂ p₂ : ℝ) (hc : Cons h)
    (hc₂ : PrI a₂ h = c₂) (hp₂ : PrI e (iand a₂ h) = p₂) :
    PrI e h ≤ 1 - c₂ + c₂ * p₂ := by
  obtain ⟨k1, k2, k3⟩ := th_17_56_l025_i a₂ e h c₂ p₂ hc hc₂ hp₂
  linarith

/-- **ch17-027, 028 (folio 188)** e/h ⩾ c₁p₁ and ⩾ c₂p₂、
本文「From the same equations it appears that」。 -/
theorem th_17_56_l027_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) :
    PrI e h ≥ c₁ * p₁ ∧ PrI e h ≥ c₂ * p₂ := by
  have s1 := def_IX_i e a₁ h
  have s2 := def_IX_i e a₂ h
  have l1 := ax_range_lo_i (iand e (inot a₁)) h
  have l2 := ax_range_lo_i (iand e (inot a₂)) h
  have x1 := def_X_left_i e a₁ h
  have x2 := def_X_left_i e a₂ h
  rw [hp₁, hc₁] at x1
  rw [hp₂, hc₂] at x2
  constructor <;> linarith

/-- **ch17-027, 028 引用版**: 「the same equations」(ch17-025 の (24.2) の形、a₁ と a₂ の
二本) を仮定に取る。ea_r/h を c_r p_r と書く段に Def. X 左形が残る。 -/
theorem th_17_56_l027_cited (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂)
    (h242₁ : PrI (iand e (inot a₁)) h + PrI (iand e a₁) h = PrI e h)
    (h242₂ : PrI (iand e (inot a₂)) h + PrI (iand e a₂) h = PrI e h) :
    PrI e h ≥ c₁ * p₁ ∧ PrI e h ≥ c₂ * p₂ := by
  have l1 := ax_range_lo_i (iand e (inot a₁)) h
  have l2 := ax_range_lo_i (iand e (inot a₂)) h
  have x1 := def_X_left_i e a₁ h
  have x2 := def_X_left_i e a₂ h
  rw [hp₁, hc₁] at x1
  rw [hp₂, hc₂] at x2
  constructor <;> linarith

/-- **ch17-029 引用版**: ch17-024–028 の 5 本を仮定に取ると、「u lies between the greatest of
{c₁p₁, c₂p₂} and the least of {c₁p₁ + c₂p₂, 1 − c₁(1 − p₁), 1 − c₂(1 − p₂)}」は算術だけ。 -/
theorem th_17_56_1_cited (c₁ c₂ p₁ p₂ u : ℝ)
    (h024 : u ≤ c₁ * p₁ + c₂ * p₂) (h025 : u ≤ 1 - c₁ + c₁ * p₁)
    (h026 : u ≤ 1 - c₂ + c₂ * p₂) (h027 : u ≥ c₁ * p₁) (h028 : u ≥ c₂ * p₂) :
    max (c₁ * p₁) (c₂ * p₂) ≤ u
      ∧ u ≤ min (c₁ * p₁ + c₂ * p₂) (min (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂))) := by
  refine ⟨max_le h027 h028, le_min h024 (le_min ?_ ?_)⟩
  · linarith
  · linarith

/-- **ch17-029 (folio 189) (56.1)** ∴ u は {c₁p₁, c₂p₂} の大きい方と
{c₁p₁ + c₂p₂, 1 − c₁(1 − p₁), 1 − c₂(1 − p₂)} の最小のあいだにある。 -/
theorem th_17_56_1_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    max (c₁ * p₁) (c₂ * p₂) ≤ u
      ∧ u ≤ min (c₁ * p₁ + c₂ * p₂) (min (1 - c₁ * (1 - p₁)) (1 - c₂ * (1 - p₂))) := by
  have h024 := th_17_56_l024_i a₁ a₂ e h c₁ c₂ p₁ p₂ u hc hc₁ hc₂ hp₁ hp₂ hu hexh
  obtain ⟨k1, k2, k3⟩ := th_17_56_l025_i a₁ e h c₁ p₁ hc hc₁ hp₁
  have h026 := th_17_56_l026_i a₂ e h c₂ p₂ hc hc₂ hp₂
  have h027 := th_17_56_l027_i a₁ a₂ e h c₁ c₂ p₁ p₂ hc₁ hc₂ hp₁ hp₂
  rw [hu] at k1 h026 h027
  exact th_17_56_1_cited c₁ c₂ p₁ p₂ u h024 (by linarith) h026 h027.1 h027.2

/-! ## (56.2)–(56.4) (folio 189): 一部の記号を消去した限界 -/

/-- **ch17-030 引用版**: ch17-024 と範囲 (c_r ⩽ 1, p_r ⩾ 0) から u ⩽ p₁ + p₂。 -/
theorem th_17_56_2_cited (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂)
    (h024 : u ≤ c₁ * p₁ + c₂ * p₂) :
    u ≤ p₁ + p₂ := by
  have k1 : c₁ * p₁ ≤ p₁ :=
    mul_le_of_le_one_left (hp₁ ▸ ax_range_lo_i _ _) (hc₁ ▸ ax_range_hi_i _ _)
  have k2 : c₂ * p₂ ≤ p₂ :=
    mul_le_of_le_one_left (hp₂ ▸ ax_range_lo_i _ _) (hc₂ ▸ ax_range_hi_i _ _)
  linarith

/-- **ch17-030 (folio 189) (56.2)** c₁, c₂ を消去した限界 u ⩽ p₁ + p₂ (修正形; 印刷は狭義の
「u < p₁ + p₂」で、等号は起こりうる — COLLATION の S、反例は phase15a_ch05_ch08)。 -/
theorem th_17_56_2_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    u ≤ p₁ + p₂ :=
  th_17_56_2_cited a₁ a₂ e h c₁ c₂ p₁ p₂ u hc₁ hc₂ hp₁ hp₂
    (th_17_56_l024_i a₁ a₂ e h c₁ c₂ p₁ p₂ u hc hc₁ hc₂ hp₁ hp₂ hu hexh)

/-- **ch17-031 引用版**: (56.1) の第 1・第 4 成分 (ch17-027, 025) の対 (算術だけ)。 -/
theorem th_17_56_3_cited (c₁ p₁ u : ℝ)
    (h027 : u ≥ c₁ * p₁) (h025 : u ≤ 1 - c₁ + c₁ * p₁) :
    c₁ * p₁ ≤ u ∧ u ≤ 1 - c₁ + c₁ * p₁ :=
  ⟨h027, h025⟩

/-- **ch17-031 (folio 189) (56.3)** c₂ を消去した限界 c₁p₁ ⩽ u ⩽ 1 − c₁ + c₁p₁。 -/
theorem th_17_56_3_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u) :
    c₁ * p₁ ≤ u ∧ u ≤ 1 - c₁ + c₁ * p₁ := by
  obtain ⟨k1, k2, k3⟩ := th_17_56_l025_i a₁ e h c₁ p₁ hc hc₁ hp₁
  have h027 := (th_17_56_l027_i a₁ a₂ e h c₁ c₂ p₁ p₂ hc₁ hc₂ hp₁ hp₂).1
  rw [hu] at k1 h027
  exact th_17_56_3_cited c₁ p₁ u h027 (by linarith)

/-- **ch17-032, 033 引用版**: ch17-024, 025, 027 と範囲 (c₂ ⩾ 0, p₂ ⩽ 1) から
c₁p₁ ⩽ u ⩽ c₁p₁ + c₂ と u ⩽ c₁p₁ + 1 − c₁。 -/
theorem th_17_56_4_cited (a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ)
    (hc₂ : PrI a₂ h = c₂) (hp₂ : PrI e (iand a₂ h) = p₂)
    (h024 : u ≤ c₁ * p₁ + c₂ * p₂) (h025 : u ≤ 1 - c₁ + c₁ * p₁) (h027 : u ≥ c₁ * p₁) :
    c₁ * p₁ ≤ u ∧ u ≤ c₁ * p₁ + c₂ ∧ u ≤ c₁ * p₁ + 1 - c₁ := by
  have k : c₂ * p₂ ≤ c₂ :=
    mul_le_of_le_one_right (hc₂ ▸ ax_range_lo_i _ _) (hp₂ ▸ ax_range_hi_i _ _)
  refine ⟨h027, by linarith, by linarith⟩

/-- **ch17-032, 033 (folio 189) (56.4)** p₂ を消去した限界
c₁p₁ ⩽ u ⩽ c₁p₁ + c₂、⩽ c₁p₁ + 1 − c₁ (連鎖の 2 行目は u の上界として読む; 7i と同じ)。 -/
theorem th_17_56_4_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0) :
    c₁ * p₁ ≤ u ∧ u ≤ c₁ * p₁ + c₂ ∧ u ≤ c₁ * p₁ + 1 - c₁ := by
  have h024 := th_17_56_l024_i a₁ a₂ e h c₁ c₂ p₁ p₂ u hc hc₁ hc₂ hp₁ hp₂ hu hexh
  have h3 := th_17_56_3_i a₁ a₂ e h c₁ c₂ p₁ p₂ u hc hc₁ hc₂ hp₁ hp₂ hu
  exact th_17_56_4_cited a₂ e h c₁ c₂ p₁ p₂ u hc₂ hp₂ h024 h3.2 h3.1

/-! ## (56.5) (folio 189): 原因についての知識が独立な場合 -/

/-- **ch17-035 (folio 189)** a₁/a₂h = a₁/h の下で
y = ea₁a₂/h = e/a₁a₂h . a₁/a₂h . a₂/h = e/a₁a₂h . c₁c₂、本文「For」(引用なし)
(phase10d th_17_56_l035 の再掲)。Def. X 左形を 2 回。 -/
theorem th_17_56_l035_i (a₁ a₂ e h : IProp) (c₁ c₂ y : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hind : PrI a₁ (iand a₂ h) = PrI a₁ h) (hy : PrI (iand e (iand a₁ a₂)) h = y) :
    y = PrI (iand e (iand a₁ a₂)) h
      ∧ PrI (iand e (iand a₁ a₂)) h
          = PrI e (iand (iand a₁ a₂) h) * PrI a₁ (iand a₂ h) * PrI a₂ h
      ∧ PrI e (iand (iand a₁ a₂) h) * PrI a₁ (iand a₂ h) * PrI a₂ h
          = PrI e (iand (iand a₁ a₂) h) * (c₁ * c₂) := by
  have x1 := def_X_left_i e (iand a₁ a₂) h
  have x2 := def_X_left_i a₁ a₂ h
  refine ⟨hy.symm, by rw [x1, x2]; ring, by rw [hind, hc₁, hc₂]; ring⟩

/-- **ch17-036 引用版**: ch17-022 と ch17-035 を仮定に取ると、算術だけ。 -/
theorem th_17_56_l036_cited (c₁ c₂ p₁ p₂ u y E : ℝ)
    (h022 : u = (c₁ * p₁ + c₂ * p₂) - y) (h035 : y = E * (c₁ * c₂)) :
    u = c₁ * p₁ + c₂ * p₂ - c₁ * c₂ * E := by
  linear_combination h022 - h035

/-- **ch17-036 (folio 189)** ∴ u = c₁p₁ + c₂p₂ − c₁c₂ . e/a₁a₂h。 -/
theorem th_17_56_l036_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0)
    (hind : PrI a₁ (iand a₂ h) = PrI a₁ h) :
    u = c₁ * p₁ + c₂ * p₂ - c₁ * c₂ * PrI e (iand (iand a₁ a₂) h) := by
  have h022 := th_17_56_l022_i a₁ a₂ e h c₁ c₂ p₁ p₂ u _ hc hc₁ hc₂ hp₁ hp₂ hu rfl hexh
  obtain ⟨y1, y2, y3⟩ := th_17_56_l035_i a₁ a₂ e h c₁ c₂ _ hc₁ hc₂ hind rfl
  exact th_17_56_l036_cited c₁ c₂ p₁ p₂ u _ _ h022 (y2.trans y3)

/-- **ch17-037 引用版**: ch17-036 と範囲 (e/a₁a₂h ⩽ 1, c_r ⩾ 0) から
u ⩾ c₁p₁ + c₂p₂ − c₁c₂。 -/
theorem th_17_56_5_cited (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (h036 : u = c₁ * p₁ + c₂ * p₂ - c₁ * c₂ * PrI e (iand (iand a₁ a₂) h)) :
    u ≥ c₁ * p₁ + c₂ * p₂ - c₁ * c₂ := by
  have k : c₁ * c₂ * PrI e (iand (iand a₁ a₂) h) ≤ c₁ * c₂ :=
    mul_le_of_le_one_right
      (mul_nonneg (hc₁ ▸ ax_range_lo_i _ _) (hc₂ ▸ ax_range_lo_i _ _)) (ax_range_hi_i _ _)
  linarith

/-- **ch17-034, 037 (folio 189) (56.5)** a₁/a₂h = a₁/h ならば u ⩾ c₁p₁ + c₂p₂ − c₁c₂
(修正形; 印刷は狭義の「u > c₁p₁ + c₂p₂ − c₁c₂」で、等号は起こりうる — COLLATION の S、
反例は phase15a_ch05_ch08)。 -/
theorem th_17_56_5_i (a₁ a₂ e h : IProp) (c₁ c₂ p₁ p₂ u : ℝ) (hc : Cons h)
    (hc₁ : PrI a₁ h = c₁) (hc₂ : PrI a₂ h = c₂)
    (hp₁ : PrI e (iand a₁ h) = p₁) (hp₂ : PrI e (iand a₂ h) = p₂) (hu : PrI e h = u)
    (hexh : PrI e (iand (iand (inot a₁) (inot a₂)) h) = 0)
    (hind : PrI a₁ (iand a₂ h) = PrI a₁ h) :
    u ≥ c₁ * p₁ + c₂ * p₂ - c₁ * c₂ :=
  th_17_56_5_cited a₁ a₂ e h c₁ c₂ p₁ p₂ u hc₁ hc₂
    (th_17_56_l036_i a₁ a₂ e h c₁ c₂ p₁ p₂ u hc hc₁ hc₂ hp₁ hp₂ hu hexh hind)

/-! ## 模型: def_X 以外の公理をすべて満たし、(56.1) と ch17-018 が偽になる -/

namespace NoX

/-- 結合子・確率関係・整合性述語の組 (phase13a の Ops と同形)。 -/
structure Ops where
  P : Type
  and_ : P → P → P
  or_  : P → P → P
  not_ : P → P
  iff_ : P → P → P
  tru  : P
  pr   : P → P → ℝ
  cons : P → Prop

def Ops.interp (S : Ops) (env : ℕ → S.P) : Form → S.P
  | .var n    => env n
  | .tru      => S.tru
  | .fls      => S.not_ S.tru
  | .conj f g => S.and_ (S.interp env f) (S.interp env g)
  | .disj f g => S.or_ (S.interp env f) (S.interp env g)
  | .neg f    => S.not_ (S.interp env f)
  | .iffF f g => S.iff_ (S.interp env f) (S.interp env g)

/-- 本ファイルの公理のうち def_X_left_i・def_X_right_i を除く 11 本を場に写したもの。 -/
structure SysNoX (S : Ops) : Prop where
  def_IX : ∀ p q h, S.pr (S.and_ p (S.not_ q)) h + S.pr (S.and_ p q) h = S.pr p h
  def_XI : ∀ (P Q R : ℝ), Q ≠ 0 → P * Q = R → P = R / Q
  range_lo : ∀ p h, 0 ≤ S.pr p h
  range_hi : ∀ p h, S.pr p h ≤ 1
  def_VIII : ∀ a b h, S.cons (S.and_ a h) → S.cons (S.and_ b h) →
    (S.pr (S.iff_ a b) h = 1 ↔ (S.pr b (S.and_ a h) = 1 ∧ S.pr a (S.and_ b h) = 1))
  def_VIII_src : ∀ a b h,
    S.pr b (S.and_ a h) = 1 → S.pr a (S.and_ b h) = 1 → S.pr (S.iff_ a b) h = 1
  iii_taut : ∀ (f : Form) (env : ℕ → S.P) (h : S.P),
    S.cons h → Taut f → S.pr (S.interp env f) h = 1
  cons_tru : S.cons S.tru
  pos_src : ∀ a h, S.cons (S.and_ a h) → S.pr a h ≠ 0
  pos : ∀ a h, S.pr a h ≠ 0 → S.cons h → S.cons (S.and_ a h)
  iff_taut : ∀ (f g : Form) (env : ℕ → S.P),
    Taut (Form.iffF f g) → (S.cons (S.interp env f) ↔ S.cons (S.interp env g))

/-- (56.1) の言明 (th_17_56_1_i と同じ形、c, p, u を pr で書いたもの) を場 S の上で。 -/
def Stmt56_1 (S : Ops) : Prop :=
  ∀ a₁ a₂ e h : S.P, S.cons h →
    S.pr e (S.and_ (S.and_ (S.not_ a₁) (S.not_ a₂)) h) = 0 →
    max (S.pr a₁ h * S.pr e (S.and_ a₁ h)) (S.pr a₂ h * S.pr e (S.and_ a₂ h)) ≤ S.pr e h
      ∧ S.pr e h ≤ min (S.pr a₁ h * S.pr e (S.and_ a₁ h) + S.pr a₂ h * S.pr e (S.and_ a₂ h))
          (min (1 - S.pr a₁ h * (1 - S.pr e (S.and_ a₁ h)))
               (1 - S.pr a₂ h * (1 - S.pr e (S.and_ a₂ h))))

/-- ch17-018 の比の言明 (th_17_56_l018_i の第 1 成分) を場 S の上で。 -/
def Stmt56_18 (S : Ops) : Prop :=
  ∀ a₁ e h : S.P, S.pr e h ≠ 0 →
    S.pr a₁ (S.and_ e h) = S.pr a₁ h * S.pr e (S.and_ a₁ h) / S.pr e h

abbrev W := Fin 4
abbrev M := Finset W

def mand (p q : M) : M := p ∩ q
def mor  (p q : M) : M := p ∪ q
def mnot (p : M) : M := pᶜ
def miff (p q : M) : M := (p ∩ q) ∪ (pᶜ ∩ qᶜ)
def mtrue : M := Finset.univ

def mu (wt : W → ℝ) (p : M) : ℝ := ∑ w ∈ p, wt w

/-- 条件 h ごとの重み wt h の比。h = ∅ のときは 0 と約定 (phase13a と同じ)。重みが h に
よって変わるので、Def. X は一般に成り立たない。 -/
noncomputable def prw (wt : M → W → ℝ) (p h : M) : ℝ :=
  if h = ∅ then 0 else mu (wt h) (p ∩ h) / mu (wt h) h

def mCons (h : M) : Prop := h.Nonempty

theorem mu_nonneg {wt : W → ℝ} (hw : ∀ w, 0 < wt w) (p : M) : 0 ≤ mu wt p :=
  Finset.sum_nonneg (fun w _ => (hw w).le)

theorem mu_pos {wt : W → ℝ} (hw : ∀ w, 0 < wt w) {p : M} (hp : p.Nonempty) : 0 < mu wt p :=
  Finset.sum_pos (fun w _ => hw w) hp

section Weighted

variable {wt : M → W → ℝ} (hw : ∀ h w, 0 < wt h w)

theorem prw_of_empty (p : M) : prw wt p ∅ = 0 := by
  simp [prw]

theorem prw_of_ne {p h : M} (hh : h ≠ ∅) : prw wt p h = mu (wt h) (p ∩ h) / mu (wt h) h := by
  rw [prw, if_neg hh]

theorem ne_empty_of_cons {h : M} (hc : mCons h) : h ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp hc

theorem ne_empty_of_inter {a h : M} (hc : a ∩ h ≠ ∅) : h ≠ ∅ := by
  rintro rfl
  exact hc (Finset.inter_empty a)

include hw in
theorem prw_eq_one_iff {p h : M} (hh : h ≠ ∅) : prw wt p h = 1 ↔ h ⊆ p := by
  have hpos : 0 < mu (wt h) h := mu_pos (hw h) (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [prw_of_ne hh, div_eq_one_iff_eq hpos.ne']
  constructor
  · intro H
    by_contra hns
    obtain ⟨w, hwh, hwp⟩ := Finset.not_subset.mp hns
    have e1 : p ∩ h = h.filter (· ∈ p) := by
      ext x; simp [and_comm]
    have hs := Finset.sum_filter_add_sum_filter_not h (· ∈ p) (wt h)
    have hpos2 : 0 < mu (wt h) (h.filter (· ∉ p)) :=
      mu_pos (hw h) ⟨w, by simp [hwh, hwp]⟩
    rw [e1] at H
    unfold mu at H hpos2
    linarith
  · intro H
    rw [Finset.inter_eq_right.mpr H]

theorem ne_empty_of_prw_eq_one {p h : M} (H : prw wt p h = 1) : h ≠ ∅ := by
  rintro rfl
  rw [prw_of_empty] at H
  exact zero_ne_one H

theorem subset_miff_iff (a b h : M) :
    h ⊆ miff a b ↔ (a ∩ h ⊆ b ∧ b ∩ h ⊆ a) := by
  simp only [miff, Finset.subset_iff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
  constructor
  · intro H
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rcases H hw.2 with ⟨_, hb⟩ | ⟨hna, _⟩
      · exact hb
      · exact absurd hw.1 hna
    · rcases H hw.2 with ⟨ha, _⟩ | ⟨_, hnb⟩
      · exact ha
      · exact absurd hw.1 hnb
  · rintro ⟨H1, H2⟩ w hw
    by_cases ha : w ∈ a
    · exact Or.inl ⟨ha, H1 ⟨ha, hw⟩⟩
    · exact Or.inr ⟨ha, fun hb => ha (H2 ⟨hb, hw⟩)⟩

theorem model_def_IX (p q h : M) :
    prw wt (mand p (mnot q)) h + prw wt (mand p q) h = prw wt p h := by
  by_cases hh : h = ∅
  · simp [prw, hh]
  · rw [prw_of_ne hh, prw_of_ne hh, prw_of_ne hh, ← add_div]
    congr 1
    have e1 : mand p q ∩ h = (p ∩ h).filter (· ∈ q) := by
      ext w; simp [mand]; tauto
    have e2 : mand p (mnot q) ∩ h = (p ∩ h).filter (· ∉ q) := by
      ext w; simp [mand, mnot]; tauto
    rw [e1, e2, add_comm]
    exact Finset.sum_filter_add_sum_filter_not _ _ _

theorem model_def_XI (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q :=
  fun H => (eq_div_iff hQ).mpr H

include hw in
theorem model_range_lo (p h : M) : 0 ≤ prw wt p h := by
  unfold prw
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (mu_nonneg (hw h) _) (mu_nonneg (hw h) _)

include hw in
theorem model_range_hi (p h : M) : prw wt p h ≤ 1 := by
  by_cases hh : h = ∅
  · simp [prw, hh]
  · have hpos : 0 < mu (wt h) h := mu_pos (hw h) (Finset.nonempty_iff_ne_empty.mpr hh)
    rw [prw_of_ne hh, div_le_one hpos]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun w _ _ => (hw h w).le)

include hw in
theorem model_def_VIII (a b h : M) (hca : mCons (mand a h)) (hcb : mCons (mand b h)) :
    prw wt (miff a b) h = 1 ↔ (prw wt b (mand a h) = 1 ∧ prw wt a (mand b h) = 1) := by
  have hca' : mand a h ≠ ∅ := ne_empty_of_cons hca
  have hcb' : mand b h ≠ ∅ := ne_empty_of_cons hcb
  have hh : h ≠ ∅ := ne_empty_of_inter hca'
  rw [prw_eq_one_iff hw hh, prw_eq_one_iff hw hca', prw_eq_one_iff hw hcb']
  exact subset_miff_iff a b h

include hw in
theorem model_def_VIII_src (a b h : M) :
    prw wt b (mand a h) = 1 → prw wt a (mand b h) = 1 → prw wt (miff a b) h = 1 := by
  intro H1 H2
  have hca' := ne_empty_of_prw_eq_one H1
  have hcb' := ne_empty_of_prw_eq_one H2
  have hh : h ≠ ∅ := ne_empty_of_inter hca'
  rw [prw_eq_one_iff hw hca'] at H1
  rw [prw_eq_one_iff hw hcb'] at H2
  rw [prw_eq_one_iff hw hh]
  exact (subset_miff_iff a b h).mpr ⟨H1, H2⟩

end Weighted

noncomputable def wOps (wt : M → W → ℝ) : Ops where
  P := M
  and_ := mand
  or_ := mor
  not_ := mnot
  iff_ := miff
  tru := mtrue
  pr := prw wt
  cons := mCons

def finInterp (env : ℕ → M) : Form → M
  | .var n    => env n
  | .tru      => mtrue
  | .fls      => mnot mtrue
  | .conj f g => mand (finInterp env f) (finInterp env g)
  | .disj f g => mor (finInterp env f) (finInterp env g)
  | .neg f    => mnot (finInterp env f)
  | .iffF f g => miff (finInterp env f) (finInterp env g)

theorem wOps_interp (wt : M → W → ℝ) (env : ℕ → M) (f : Form) :
    (wOps wt).interp env f = finInterp env f := by
  induction f with
  | var n => rfl
  | tru => rfl
  | fls => rfl
  | conj f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl
  | disj f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl
  | neg f ihf => simp only [Ops.interp]; rw [ihf]; rfl
  | iffF f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl

theorem mem_finInterp (env : ℕ → M) (f : Form) (w : W) :
    w ∈ finInterp env f ↔ evalB (fun n => decide (w ∈ env n)) f = true := by
  induction f with
  | var n => simp [finInterp, evalB]
  | tru => simp [finInterp, evalB, mtrue]
  | fls => simp [finInterp, evalB, mtrue, mnot]
  | conj f g ihf ihg => simp [finInterp, evalB, mand, ihf, ihg]
  | disj f g ihf ihg => simp [finInterp, evalB, mor, ihf, ihg]
  | neg f ihf => simp [finInterp, evalB, mnot, ihf]
  | iffF f g ihf ihg =>
    simp only [finInterp, evalB, miff, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
      ihf, ihg]
    cases evalB (fun n => decide (w ∈ env n)) f <;> cases evalB (fun n => decide (w ∈ env n)) g <;>
      simp

section Weighted2

variable {wt : M → W → ℝ} (hw : ∀ h w, 0 < wt h w)

include hw in
theorem model_iii_taut (f : Form) (env : ℕ → M) (h : M) (hc : mCons h) (ht : Taut f) :
    prw wt (finInterp env f) h = 1 := by
  rw [prw_eq_one_iff hw (ne_empty_of_cons hc)]
  intro w _
  rw [mem_finInterp]
  exact ht _

theorem model_cons_tru : mCons mtrue := Finset.univ_nonempty

include hw in
theorem model_pos_src (a h : M) : mCons (mand a h) → prw wt a h ≠ 0 := by
  intro hca
  have hh : h ≠ ∅ := ne_empty_of_inter (ne_empty_of_cons hca)
  have hhpos : 0 < mu (wt h) h := mu_pos (hw h) (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [prw_of_ne hh]
  exact (div_pos (mu_pos (hw h) hca) hhpos).ne'

theorem model_pos (a h : M) : prw wt a h ≠ 0 → mCons h → mCons (mand a h) := by
  intro hne hc
  by_contra hz
  apply hne
  rw [mCons, Finset.not_nonempty_iff_eq_empty] at hz
  rw [prw_of_ne (ne_empty_of_cons hc)]
  simp only [mand] at hz
  simp [hz, mu]

theorem model_iff_taut (f g : Form) (env : ℕ → M) (ht : Taut (Form.iffF f g)) :
    mCons (finInterp env f) ↔ mCons (finInterp env g) := by
  have e : finInterp env f = finInterp env g := by
    ext w
    rw [mem_finInterp, mem_finInterp]
    have H := ht (fun n => decide (w ∈ env n))
    simp only [evalB, beq_iff_eq] at H
    rw [H]
  rw [e]

include hw in
/-- 正の重み (条件ごとに変わってよい) の模型は、def_X を除く 11 本の公理をすべて満たす。 -/
theorem wSysNoX : SysNoX (wOps wt) where
  def_IX := model_def_IX
  def_XI := model_def_XI
  range_lo := model_range_lo hw
  range_hi := model_range_hi hw
  def_VIII := model_def_VIII hw
  def_VIII_src := model_def_VIII_src hw
  iii_taut := fun f env h hc ht => by
    show prw wt ((wOps wt).interp env f) h = 1
    rw [wOps_interp]
    exact model_iii_taut hw f env h hc ht
  cons_tru := model_cons_tru
  pos_src := model_pos_src hw
  pos := model_pos
  iff_taut := fun f g env ht => by
    show mCons ((wOps wt).interp env f) ↔ mCons ((wOps wt).interp env g)
    rw [wOps_interp, wOps_interp]
    exact model_iff_taut f g env ht

end Weighted2

/-! ### 条件ごとに重みが変わる模型: h = ⊤ で一様、h ≠ ⊤ で世界 w に重み w + 1 -/

noncomputable def wt₄ (h : M) (w : W) : ℝ := if h = mtrue then 1 else (w.val : ℝ) + 1

theorem wt₄_pos : ∀ h w, 0 < wt₄ h w := by
  intro h w
  unfold wt₄
  split_ifs
  · norm_num
  · positivity

/-- 4 世界の模型。 -/
noncomputable abbrev M₄ : Ops := wOps wt₄

theorem noX_sys : SysNoX M₄ := wSysNoX wt₄_pos

/-- 原因 a₁ := {0, 1}, a₂ := {2, 3}, 事象 e := {0, 2}, 与件 h := ⊤。 -/
def a₁ₘ : M := {0, 1}
def a₂ₘ : M := {2, 3}
def eₘ : M := {0, 2}

theorem m_u : prw wt₄ eₘ mtrue = 1 / 2 := by
  rw [prw_of_ne (by decide)]
  have e1 : eₘ ∩ mtrue = {0, 2} := by decide
  rw [e1]
  simp [mu, wt₄, mtrue]
  norm_num

theorem m_c₁ : prw wt₄ a₁ₘ mtrue = 1 / 2 := by
  rw [prw_of_ne (by decide)]
  have e1 : a₁ₘ ∩ mtrue = {0, 1} := by decide
  rw [e1]
  simp [mu, wt₄, mtrue]
  norm_num

theorem m_c₂ : prw wt₄ a₂ₘ mtrue = 1 / 2 := by
  rw [prw_of_ne (by decide)]
  have e1 : a₂ₘ ∩ mtrue = {2, 3} := by decide
  rw [e1]
  simp [mu, wt₄, mtrue]
  norm_num

theorem m_p₁ : prw wt₄ eₘ (mand a₁ₘ mtrue) = 1 / 3 := by
  have e0 : mand a₁ₘ mtrue = {0, 1} := by decide
  have e1 : eₘ ∩ ({0, 1} : M) = {0} := by decide
  have hne : ({0, 1} : M) ≠ mtrue := by decide
  rw [e0, prw_of_ne (by decide), e1]
  simp [mu, wt₄, hne]
  norm_num

theorem m_p₂ : prw wt₄ eₘ (mand a₂ₘ mtrue) = 3 / 7 := by
  have e0 : mand a₂ₘ mtrue = {2, 3} := by decide
  have e1 : eₘ ∩ ({2, 3} : M) = {2} := by decide
  have hne : ({2, 3} : M) ≠ mtrue := by decide
  rw [e0, prw_of_ne (by decide), e1]
  simp [mu, wt₄, hne]
  norm_num

theorem m_exh : prw wt₄ eₘ (mand (mand (mnot a₁ₘ) (mnot a₂ₘ)) mtrue) = 0 := by
  have e0 : mand (mand (mnot a₁ₘ) (mnot a₂ₘ)) mtrue = ∅ := by decide
  rw [e0, prw_of_empty]

/-- **(56.1) は def_X 抜きでは導けない**: def_X を除く 11 本の公理を満たす模型 M₄ で、
Cons h と e/ā₁ā₂h = 0 が成り立つのに u = 1/2 > c₁p₁ + c₂p₂ = 8/21。 -/
theorem model_56_1_fails : SysNoX M₄ ∧ ¬ Stmt56_1 M₄ := by
  refine ⟨noX_sys, fun H => ?_⟩
  have k := (H a₁ₘ a₂ₘ eₘ mtrue model_cons_tru m_exh).2
  have k' := le_trans k (min_le_left _ _)
  change prw wt₄ eₘ mtrue ≤ prw wt₄ a₁ₘ mtrue * prw wt₄ eₘ (mand a₁ₘ mtrue)
      + prw wt₄ a₂ₘ mtrue * prw wt₄ eₘ (mand a₂ₘ mtrue) at k'
  rw [m_u, m_c₁, m_c₂, m_p₁, m_p₂] at k'
  norm_num at k'

/-- **ch17-018 の比は def_X 抜きでは導けない**: 同じ模型で a₁/eh = 1/4 だが
c₁p₁/u = (1/2 . 1/3)/(1/2) = 1/3。 -/
theorem model_18_fails : SysNoX M₄ ∧ ¬ Stmt56_18 M₄ := by
  refine ⟨noX_sys, fun H => ?_⟩
  have k := H a₁ₘ eₘ mtrue (by rw [show (M₄.pr eₘ mtrue) = prw wt₄ eₘ mtrue from rfl, m_u]; norm_num)
  change prw wt₄ a₁ₘ (mand eₘ mtrue)
      = prw wt₄ a₁ₘ mtrue * prw wt₄ eₘ (mand a₁ₘ mtrue) / prw wt₄ eₘ mtrue at k
  have e0 : mand eₘ mtrue = {0, 2} := by decide
  have e1 : a₁ₘ ∩ ({0, 2} : M) = {0} := by decide
  have hne : ({0, 2} : M) ≠ mtrue := by decide
  rw [m_u, m_c₁, m_p₁, e0, prw_of_ne (by decide), e1] at k
  simp [mu, wt₄, hne] at k
  norm_num at k

/-- 同じ模型で Def. X 左形そのものが偽: a₁e/⊤ = 1/4 だが a₁/e⊤ . e/⊤ = 1/4 . 1/2 = 1/8。 -/
theorem model_def_X_left_fails :
    ¬ ∀ p q h : M₄.P, M₄.pr (M₄.and_ p q) h = M₄.pr p (M₄.and_ q h) * M₄.pr q h := by
  intro H
  have k := H a₁ₘ eₘ mtrue
  change prw wt₄ (mand a₁ₘ eₘ) mtrue = prw wt₄ a₁ₘ (mand eₘ mtrue) * prw wt₄ eₘ mtrue at k
  have e0 : mand eₘ mtrue = {0, 2} := by decide
  have e1 : a₁ₘ ∩ ({0, 2} : M) = {0} := by decide
  have e2 : mand a₁ₘ eₘ ∩ mtrue = {0} := by decide
  have hne : ({0, 2} : M) ≠ Finset.univ := by decide
  rw [m_u, e0, prw_of_ne (by decide : ({0, 2} : M) ≠ ∅), e1, prw_of_ne (by decide), e2] at k
  simp [mu, wt₄, mtrue, hne] at k
  norm_num at k

end NoX

end KeynesI

/-! # 監査クエリ -/

-- 写し (phase6c・phase10d)
#print axioms KeynesI.itrue_certain
#print axioms KeynesI.true_conj
#print axioms KeynesI.th_13_1_i
#print axioms KeynesI.taut_neg_zero
#print axioms KeynesI.conj_neg_cert_zero
#print axioms KeynesI.th_12_i_short
#print axioms KeynesI.subst_taut
#print axioms KeynesI.th_24_i
#print axioms KeynesI.th_14_38_full_i
#print axioms KeynesI.th_17_56_raw_i
-- (56)
#print axioms KeynesI.th_17_56_l004_i
#print axioms KeynesI.th_17_56_l004_cited
#print axioms KeynesI.th_17_56_l014_i
#print axioms KeynesI.th_17_56_l016_i
#print axioms KeynesI.th_17_56_l016_cited
#print axioms KeynesI.th_17_56_l017_i
#print axioms KeynesI.th_17_56_l017_cited
#print axioms KeynesI.th_17_56_l018_i
#print axioms KeynesI.th_17_56_l019_i
#print axioms KeynesI.th_17_56_l019_cited
#print axioms KeynesI.th_17_56_l021_i
#print axioms KeynesI.th_17_56_l022_i
#print axioms KeynesI.th_17_56_l022_cited
#print axioms KeynesI.th_17_56_l023_i
-- (56.1)
#print axioms KeynesI.th_17_56_l024_i
#print axioms KeynesI.th_17_56_l024_cited
#print axioms KeynesI.th_17_56_l025_i
#print axioms KeynesI.th_17_56_l025_cited
#print axioms KeynesI.th_17_56_l026_i
#print axioms KeynesI.th_17_56_l027_i
#print axioms KeynesI.th_17_56_l027_cited
#print axioms KeynesI.th_17_56_1_i
#print axioms KeynesI.th_17_56_1_cited
-- (56.2)–(56.4)
#print axioms KeynesI.th_17_56_2_i
#print axioms KeynesI.th_17_56_2_cited
#print axioms KeynesI.th_17_56_3_i
#print axioms KeynesI.th_17_56_3_cited
#print axioms KeynesI.th_17_56_4_i
#print axioms KeynesI.th_17_56_4_cited
-- (56.5)
#print axioms KeynesI.th_17_56_l035_i
#print axioms KeynesI.th_17_56_l036_i
#print axioms KeynesI.th_17_56_l036_cited
#print axioms KeynesI.th_17_56_5_i
#print axioms KeynesI.th_17_56_5_cited
-- 模型 (Lean 標準の公理のみのはず)
#print axioms KeynesI.NoX.noX_sys
#print axioms KeynesI.NoX.model_56_1_fails
#print axioms KeynesI.NoX.model_18_fails
#print axioms KeynesI.NoX.model_def_X_left_fails
