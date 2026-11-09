/-
# Keynes (1921) *A Treatise on Probability* Part V — Lean 4 Phase 16b
# 第 XXIX 章 §8–§11 (folio 345–351): Poisson の定理、戻さない取り出し (Czuber・Pearson)、Poisson の壺、
#   継起の仮定の人工例 (台帳 ch29-055〜083)
#
# 「外部公理依存 (公理名)」: 第 II 部の公理群だけでは閉じず、名前付きの公理を足して閉じた行。#print axioms にその名が出る。
# 分担: phase14b (B38) は 001〜040、phase14a (B36) は 041〜054、本ファイル (B48) は 055〜083。
#
# ## 基準
#   1921 年 Macmillan 初版の頁画像のみ (folio 344–351)。定理名は th_29_<行番号>。台帳の行 ID は各定理の docstring に書く。
#
# ## 原典
#   (folio 344、§8) 「A formula, which dispenses with the explicit assumption of equal à priori probabilities at every
#    trial, was proposed by Poisson, and is usually known by his name. It does not dispense,」(folio 345) 「however, with
#    the other inexplicit assumption. … Poisson's Theorem may be enunciated as follows: Let s trials be made, and at the
#    λth trial (λ = 1, 2 . . . s) let the probabilities for the occurrence and non-occurrence of the event be p_λ, q_λ
#    respectively. Then, if Σp_λ/s = p, the probability that the number of occurrences m of the event in the s trials
#    will lie between the limits sp ± l is given by
#      P = 2/(k√(πs)) ∫_0^l e^{−x²/k²s} dx + e^{−l²/k²s}/(k√(πs)),   where k = √(2Σp_λq_λ/s).
#    By substituting x/(k√s) = t and l/(k√s) = γ, this may be written in a form corresponding to that of Bernoulli's
#    Theorem, namely: The probability that the number of occurrences of the event will lie between sp ± γk√s is given by
#      P = 2/√π ∫_0^γ e^{−t²} dt + e^{−γ²}/(k√(πs)).」
#   (folio 347、§10) 「If σ is the number of balls and s the number of drawings, he reaches the interesting conclusion
#    (assuming that σ, s and σ − s are all large) that the probability of the number of black balls lying within given
#    limits is the same as it would be if the balls were replaced after each drawing and the number of drawings were
#    (σ − s)/σ · s instead of s. … narrow compared with the total number of black balls pσ. … even where s > pσ.」
#   (folio 348) 「the probability that a given proportion m/(m + n) of these μ balls will be black is independent of the
#    number and the colour of the l balls originally drawn out. For, he argues, if l + μ balls are drawn out, …」
#   (folio 349、§11) 「Thus the à priori probability p (= r/s) of an event is based on the observation of its occurrence
#    r times out of s occasions … the probability of the event's occurring n times running is p^n or (r/s)^n. But, if
#    the event occurs at the first trial, the probability at the second」(folio 350) 「becomes (r + 1)/(s + 1), and so on.
#    Hence the probability P, properly calculated, of n successive occurrences is r/s · (r+1)/(s+1) · (r+2)/(s+2) · · ·
#    (r+n−1)/(s+n−1). Hence P = (r+n−1)!(s−1)!/((s+n−1)!(r−1)!) = [Stirling] … provided that r and s are large;
#    = (r/s)^n (1 + (n−1)/r)^{r+n−½}/(1 + (n−1)/s)^{s+n−½} = p^n Q^n, where Q = … . Thus, in this case, the assumption of
#    Bernoulli's Theorem is approximately correct, only if Q is nearly unity. … sp (= r) … approximately p^n, unless n
#    is also small. … n occurrences and m failures on m + n occasions」(folio 351) 「… and m small compared with s − r.
#    … If an event has occurred x times in the first y trials, its probability at the y + 1th is (r + x)/(s + y)」
#
# ## キャリア
#   phase6c の内包キャリア (IProp, PrI, Cons; 公理 (i) の但し書き付き) を phase14a と同名・同形で写す。
#   y・x (y_r・_m x_n) も phase14a と同一。`Prop → Prop → ℝ` 型の確率関係は置かない (CLAUDE.md 不変条件 3)。
#
# ## 記法の読み (定)
#   trials s     : λ = 1, 2 . . . s (055)。pmean p s : p = Σp_λ/s (056)。kP p s : k = √(2Σp_λq_λ/s) (059)。
#   pp a h       : p_λ := a_λ/h (各回の確率の名付け)。pbin p n m : 各回の確率 p_λ で互いに無関連な試行の
#                  n 回中 m 回の確率 (Poisson 二項分布)。probWithinP・probWithinI : 限界 sp ± l の確率 (057;
#                  前者は分布の和、後者はキャリア上の _m x_s の確率の和)。poissonP : 058 の P (印刷の式)。
#   hyp σ K s k  : 戻さない取り出しの超幾何分布 (§10)。pairs・black : Poisson の壺の 5 個の玉の模型 (§10)。
#   pR r s       : p = r/s (070)。bernP p n : p^n (071)。SuccRule : 人工例の仮定 (073・083)。
#   st076・Q078  : 076 の右辺と 078 の Q (印刷の式)。fr075 : 075 の右辺。gSt : Stirling の形 √(2π)x^{x+½}e^{−x}。
#
# ## 外部公理 (第 II 部の公理でないもの)
#   aP, hP, aS, hS            : §8・§11 の事象の系列と data の名付け (内容を主張しない)。
#   ax_data_consP, ax_data_consS : data は矛盾する連言でない (公理 (i) の但し書き)。
#   ax_poisson_independence   : PoissonIndep aP hP。Poisson の定理の「other inexplicit assumption」(folio 345): λ+1 回目の
#                               生起の確率は最初の λ 回の生起の回数を知っても変わらない。057・058・063 が依る。
#   ax_poisson_approx         : Poisson 二項分布の積分形の正規近似 (Lindeberg–Feller の中心極限定理の場合)。各 p_λ が
#                               δ ≤ p_λ ≤ 1 − δ (δ > 0) なら |m − sp| < γk√s の確率 → Θ(γ)。Mathlib にない。058・063 が依る。
#                               実解析の真な定理の言明 (B38 の ax_normal_approx は p_λ = p の場合)。
#   ax_succession_rule        : 人工例の仮定 SuccRule (0 < r < s): k 回続けて起こった後の k+1 回目の確率は (r+k)/(s+k)。
#                               070 (data 上の値)・073・074・075 (data 上の形) が依る。Pólya の壺 (黒 r・白 s − r、
#                               取り出した玉に同じ色の玉 1 個を添えて戻す) がこの仮定を満たす標準的な模型で、
#                               最初に起こらない回の分布を重みにした模型 MS で検査した (succRule_MS)。
#   相対無矛盾性: ax_poisson_independence は自明な代入 a_λ := ⊤、h := ⊤ で第 II 部の公理だけから満たされる
#   (rel_cons_poisson_trivial; p_λ = 1 の代入)。ax_succession_rule は p = r/s < 1 を要するので自明な代入では
#   満たされない。そこで第 II 部の公理の文 13 本を構造 Sys に写し (phase14a・phase12b の流儀)、可算の世界
#   (ℕ × ℕ) × ℕ の重み付き模型 MS (重みは Pólya の壺で最初に起こらない回の分布) が Sys を満たし (sys_MS)、
#   その上で ax_data_consP・ax_poisson_independence・ax_data_consS・ax_succession_rule の形がすべての (r, s)
#   について同時に成り立つ読みがあることを示した (model_external)。#print axioms は Lean の標準の公理だけ。
#   ax_poisson_approx はキャリアを含まない実解析の文 (真な定理の言明) で、この模型の対象外。
#
# ## 外部公理が第 II 部の公理から導けないこと (模型、KeynesXXIXc_model)
#   同じ模型 MS と整合な h := h_{1,2} について: Pólya の壺の系列 a_k := tM 1 2 k (継起の仮定を満たす系列) では
#   PoissonIndep が偽 (a_2/_1x_1 h = 2/3 ≠ 1/3 = a_2/h、nec_poisson_model)。すべての k で同じ命題 a_k := tM 1 2 1
#   では y_1/h = 1/2 = r/s (r = 1、s = 2) だが a_2/y_1 h = 1 ≠ 2/3 = (r + 1)/(s + 1) で SuccRule が偽
#   (nec_succession_model)。系 not_derivable_poisson・not_derivable_succession。phase14a の 3 世界の模型は
#   有限で、y_k ∧ h がすべての k で整合な継起の仮定を満たせないので、模型は可算にした。
#
# ## 第 29 章の外部公理一覧 (phase14a・phase14b・本ファイル; 名前・意味・依存する行)
#   ax_stirling_approx (phase14b)        : 局所 de Moivre–Laplace 定理 (p ∈ (0, 1)、|h| ≤ C√m で一様に比 → 1)。
#                                          012 (外)。
#   ax_normal_approx (phase14b)          : 積分形 de Moivre–Laplace 定理 (|n − mp| < √(2mpq)γ の確率 → Θ(γ))。
#                                          022・027・029 (外)。
#   a29・h29・ax_data_cons29 (phase14a)  : §6–§7 の系列と data の名付け、data の整合性。043・047・052・053 (外) が依る。
#   ax_bernoulli_independence (phase14a) : 043 (§6 の典型的条件)。043・047 (外)、048 の data 上の形 th_29_048_data (≈)。
#   ax_equal_chance (phase14a)           : 052 (§7 の (i.))。052 (外)、047 の §7 経路 th_29_047_ii。
#   ax_independence_ii (phase14a)        : 053 (§7 の (ii.))。053 (外)、047 の §7 経路 th_29_047_ii。
#   aP・hP・ax_data_consP (本ファイル)   : §8 の系列と data の名付け、data の整合性。057・058・063 が依る。
#   ax_poisson_independence (本ファイル) : Poisson の定理の「other inexplicit assumption」。058・063 (外)、
#                                          057 の th_29_057 (行は 定)。
#   ax_poisson_approx (本ファイル)       : Poisson 二項分布の積分形の正規近似。058・063 (外)。
#   aS・hS・ax_data_consS (本ファイル)   : §11 の人工例の系列と data の名付け、data の整合性。073・074・075 が依る。
#   ax_succession_rule (本ファイル)      : §11 の人工例の仮定 (r + k)/(s + k)。073・074・075 (外; 075 は
#                                          th_29_075_data)、070 の th_29_070_data (行は 定)。
#
# ## 外部公理に依らない部分
#   th_poisson_dist (前提 PoissonIndep を仮定に取れば第 II 部の公理だけで _m x_n/h = Poisson 二項分布)、
#   th_29_059 (分散 Σp_λq_λ = k²s/2)、th_29_poisson_cheb (Chebyshev 型の Poisson の定理)、060・063_eq (変数変換)、
#   th_29_074_of (前提 SuccRule を仮定に取れば第 II 部の公理だけで y_n/h = Π(r+i)/(s+i))、075 (積 = 階乗の比)、
#   075_beta・073_beta・laplace_uniform (Beta 積分; 事前の密度 θ^a(1 − θ)^b で r = a + 1、s = a + b + 2)、
#   076 (Mathlib の Stirling.factorial_isEquivalent_stirling から)、077・078 (rpow の代数)、080 (P と p^n の比較)。
#
# ## 依頼文との違い (報告事項)
#   依頼は §11 を「Laplace の継起の規則 (m+1)/(m+2)」と書き、無差別原理の事前分布を ax_uniform_prior と名付けるよう
#   求めたが、印刷の §11 (folio 349–351) は Laplace の規則ではなく、r/s から (r+1)/(s+1) へ上がる人工例を置き、
#   脚注 1 (folio 351) で「This paragraph is concerned with a different point from that dealt with in Professor Pearson's
#   article … Laplace's "Rule of Succession"」と断っている。(r+x)/(s+y) は一様な事前の密度ではなく θ^{r−1}(1 − θ)^{s−r−1}
#   に当たる (th_29_073_beta)。よって公理は印刷の仮定どおり ax_succession_rule とし、ax_uniform_prior は置かない。
#   一様な事前の密度の場合 (r = 1、s = 2) が Laplace の規則になることは th_29_laplace_uniform に定理として残した。
#
# ## 実行方法
#   lake env lean phases/keynes_part_v_phase16b_poisson_succession.lean
-/
import Mathlib

namespace KeynesXXIXc

open Real Finset Filter Topology Asymptotics

/-! ## 内包的キャリアと結合子 (phase6c・phase14a と同一) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 `Cons h`: 「h は矛盾する連言でない」(folio 135、公理 (i))。 -/
axiom Cons : IProp → Prop

/-! ## Keynes 操作公理群 (内包版、phase6c・phase14a と同一) -/

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom def_XI_i (P Q R : ℝ) (hQ : Q ≠ 0) : P * Q = R → P = R / Q
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-- Def. VIII 双条件読み、但し書き付き (phase6c と同一)。本ファイルの定理は用いない。 -/
axiom def_VIII_i (a b h : IProp) (hca : Cons (iand a h)) (hcb : Cons (iand b h)) :
    PrI (iiff a b) h = 1 ↔ (PrI b (iand a h) = 1 ∧ PrI a (iand b h) = 1)

/-- Def. VIII 印刷どおり (→ のみ、phase6c と同一)。本ファイルの定理は用いない。 -/
axiom def_VIII_i_src (a b h : IProp) :
    PrI b (iand a h) = 1 → PrI a (iand b h) = 1 → PrI (iiff a b) h = 1

/-! ## 深い埋め込み: 構文・評価・トートロジー (phase6c と同一) -/

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

/-- 論証的トートロジー: すべての真理値割当で真。 -/
def Taut (f : Form) : Prop := ∀ v : ℕ → Bool, evalB v f = true

noncomputable def interp (env : ℕ → IProp) : Form → IProp
  | .var n    => env n
  | .tru      => itrue
  | .fls      => inot itrue
  | .conj f g => iand (interp env f) (interp env g)
  | .disj f g => ior (interp env f) (interp env g)
  | .neg f    => inot (interp env f)
  | .iffF f g => iiff (interp env f) (interp env g)

/-- Ax.(iii) 本体、但し書き付き (phase6c と同一)。 -/
axiom ax_iii_taut (f : Form) (env : ℕ → IProp) (h : IProp) :
    Cons h → Taut f → PrI (interp env f) h = 1

/-! ## 整合性の公理 (phase6c と同一) -/

axiom cons_true : Cons itrue
axiom cons_of_pos_src (a h : IProp) : Cons (iand a h) → PrI a h ≠ 0
axiom cons_of_pos (a h : IProp) : PrI a h ≠ 0 → Cons h → Cons (iand a h)
axiom cons_iff_taut (f g : Form) (env : ℕ → IProp) :
    Taut (Form.iffF f g) → (Cons (interp env f) ↔ Cons (interp env g))

/-! ## 移植定理 (phase6c・phase14a と同一の証明) -/

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

/-- 第13章の (12) (folio 141) の短い証明 (phase6c の th_12_i_short と同一)。 -/
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

/-- 認証代入 (th_12_i_short 経由; def_VIII_i を用いない)。 -/
theorem subst_taut (f g : Form) (env : ℕ → IProp) (h : IProp) (hc : Cons h)
    (ht : Taut (Form.iffF f g)) :
    PrI (interp env f) h = PrI (interp env g) h :=
  th_12_i_short _ _ h hc (ax_iii_taut (Form.iffF f g) env h hc ht)

/-! ## 系列の記法 (phase14a と同一) -/

/-- y_r (phase14a と同一): r 回続けて起こる。y 0 = itrue、y (r+1) = a_{r+1} ∧ y_r。 -/
noncomputable def y (a : ℕ → IProp) : ℕ → IProp
  | 0 => itrue
  | r + 1 => iand (a (r + 1)) (y a r)

/-- _m x_n (phase14a と同一): 最初の n 回のうち m 回起こり、他では起こらない。 -/
noncomputable def x (a : ℕ → IProp) : ℕ → ℕ → IProp
  | 0, 0 => itrue
  | _ + 1, 0 => inot itrue
  | 0, n + 1 => iand (inot (a (n + 1))) (x a 0 n)
  | m + 1, n + 1 =>
      if m = n then iand (a (n + 1)) (x a m n)
      else ior (iand (a (n + 1)) (x a m n)) (iand (inot (a (n + 1))) (x a (m + 1) n))

/-! ## 第 II 部の公理から: 排反な選言の加法と、無関連な場合の乗法 -/

/-- ⊥/h = 0 (h 整合)。 -/
theorem pr_false (h : IProp) (hc : Cons h) : PrI (inot itrue) h = 0 :=
  taut_neg_zero Form.fls (fun _ => itrue) h hc (fun _ => rfl)

/-- A が X ∧ h について無関連なら (A ∧ X)/h = A/h · X/h。X/h = 0 の場合は両辺 0。 -/
theorem pr_mul_of_irr (A X h : IProp) (hc : Cons h)
    (hA : Cons (iand X h) → PrI A (iand X h) = PrI A h) :
    PrI (iand A X) h = PrI A h * PrI X h := by
  rw [def_X_left_i]
  by_cases h0 : PrI X h = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [hA (cons_of_pos X h h0 hc)]

/-- 同じ前提で (Ā ∧ X)/h = (1 − A/h) · X/h。 -/
theorem pr_mul_not_of_irr (A X h : IProp) (hc : Cons h)
    (hA : Cons (iand X h) → PrI A (iand X h) = PrI A h) :
    PrI (iand (inot A) X) h = (1 - PrI A h) * PrI X h := by
  rw [def_X_left_i]
  by_cases h0 : PrI X h = 0
  · rw [h0, mul_zero, mul_zero]
  · have hcx := cons_of_pos X h h0 hc
    have e := th_13_1_i A (iand X h) hcx
    rw [hA hcx] at e
    rw [show PrI (inot A) (iand X h) = 1 - PrI A h by linarith]

/-- 排反な選言: ((A ∧ X) ∨ (Ā ∧ Y))/h = (A ∧ X)/h + (Ā ∧ Y)/h (h 整合)。Def. IX と認証代入 2 回。 -/
theorem pr_or_excl (A X Y h : IProp) (hc : Cons h) :
    PrI (ior (iand A X) (iand (inot A) Y)) h = PrI (iand A X) h + PrI (iand (inot A) Y) h := by
  have s := def_IX_i (ior (iand A X) (iand (inot A) Y)) (iand A X) h
  have e1 : PrI (iand (ior (iand A X) (iand (inot A) Y)) (iand A X)) h = PrI (iand A X) h :=
    subst_taut
      (Form.conj (Form.disj (Form.conj (Form.var 0) (Form.var 1))
        (Form.conj (Form.neg (Form.var 0)) (Form.var 2))) (Form.conj (Form.var 0) (Form.var 1)))
      (Form.conj (Form.var 0) (Form.var 1))
      (fun n => match n with | 0 => A | 1 => X | _ => Y) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> simp [evalB, h0, h1, h2])
  have e2 : PrI (iand (ior (iand A X) (iand (inot A) Y)) (inot (iand A X))) h
      = PrI (iand (inot A) Y) h :=
    subst_taut
      (Form.conj (Form.disj (Form.conj (Form.var 0) (Form.var 1))
        (Form.conj (Form.neg (Form.var 0)) (Form.var 2)))
        (Form.neg (Form.conj (Form.var 0) (Form.var 1))))
      (Form.conj (Form.neg (Form.var 0)) (Form.var 2))
      (fun n => match n with | 0 => A | 1 => X | _ => Y) h hc
      (by intro v; cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> simp [evalB, h0, h1, h2])
  linarith

/-! ## §8 (folio 345): Poisson の定理 — 記法 (定) -/

/-- q := 1 − p (q_λ = 1 − p_λ)。 -/
noncomputable def q (p : ℝ) : ℝ := 1 - p

/-- ch29-055: 試行の番号 λ = 1, 2 . . . s。 -/
def trials (s : ℕ) : Finset ℕ := Finset.Icc 1 s

/-- ch29-056: p := Σp_λ / s (Poisson の p、各回の p_λ の平均)。 -/
noncomputable def pmean (p : ℕ → ℝ) (s : ℕ) : ℝ := (∑ j ∈ trials s, p j) / s

/-- ch29-059: k := √(2Σp_λ q_λ / s)。 -/
noncomputable def kP (p : ℕ → ℝ) (s : ℕ) : ℝ := √(2 * (∑ j ∈ trials s, p j * q (p j)) / s)

/-- 各回の確率が p_λ で互いに無関連なとき、s 回のうち m 回起こる確率 (Poisson 二項分布)。
λ 回目の確率は p λ (λ = 1, …, s)。 -/
noncomputable def pbin (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => if m = 0 then 1 else 0
  | n + 1, 0 => q (p (n + 1)) * pbin p n 0
  | n + 1, m + 1 => p (n + 1) * pbin p n m + q (p (n + 1)) * pbin p n (m + 1)

/-- ch29-057: 生起の回数 m が限界 sp ± l の間にある確率 (Poisson 二項分布の和)。 -/
noncomputable def probWithinP (p : ℕ → ℝ) (s : ℕ) (l : ℝ) : ℝ :=
  ∑ m ∈ (range (s + 1)).filter (fun m : ℕ => |(m : ℝ) - s * pmean p s| < l), pbin p s m

/-- Θ(t) = 2/√π ∫_0^t e^{−u²} du (phase14b と同一)。 -/
noncomputable def Θ (t : ℝ) : ℝ := 2 / √π * ∫ u in (0 : ℝ)..t, exp (-(u ^ 2))

/-- ch29-058 の P (印刷の式): 2/(k√(πs)) ∫_0^l e^{−x²/k²s} dx + e^{−l²/k²s}/(k√(πs))。 -/
noncomputable def poissonP (p : ℕ → ℝ) (s : ℕ) (l : ℝ) : ℝ :=
  2 / (kP p s * √(π * s)) * (∫ t in (0 : ℝ)..l, exp (-(t ^ 2) / (kP p s ^ 2 * s)))
    + exp (-(l ^ 2) / (kP p s ^ 2 * s)) / (kP p s * √(π * s))

/-! ## §8: 独立の前提 (キャリア上) と分布 -/

/-- Poisson の定理の「inexplicit assumption」(folio 344–345): λ+1 回目の生起の確率は、最初の n 回の
生起の回数 (_m x_n) を知っても変わらない (前提 _m x_n ∧ h が整合な場合)。等しい見込みは要求しない。 -/
def PoissonIndep (a : ℕ → IProp) (h : IProp) : Prop :=
  ∀ m n, Cons (iand (x a m n) h) → PrI (a (n + 1)) (iand (x a m n) h) = PrI (a (n + 1)) h

/-- 各回の確率 p_λ := a_λ/h (ch29-055・056 の「let the probabilities … be p_λ, q_λ」)。 -/
noncomputable def pp (a : ℕ → IProp) (h : IProp) : ℕ → ℝ := fun j => PrI (a j) h

theorem pbin_zero_of_lt (p : ℕ → ℝ) : ∀ n m, n < m → pbin p n m = 0 := by
  intro n
  induction n with
  | zero => intro m hm; simp [pbin, Nat.pos_iff_ne_zero.mp hm]
  | succ n ih =>
      intro m hm
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [pbin]
      rw [ih m (by omega), ih (m + 1) (by omega)]
      ring

/-- 独立の前提の下で _m x_n / h は Poisson 二項分布の値 (第 II 部の公理と前提 PoissonIndep のみ)。 -/
theorem th_poisson_dist (a : ℕ → IProp) (h : IProp) (hc : Cons h) (hind : PoissonIndep a h) :
    ∀ n m, PrI (x a m n) h = pbin (pp a h) n m := by
  intro n
  induction n with
  | zero =>
      intro m
      cases m with
      | zero => simp only [x, pbin]; exact itrue_certain h hc
      | succ m => simp only [x, pbin]; rw [if_neg (by omega)]; exact pr_false h hc
  | succ n ih =>
      intro m
      cases m with
      | zero =>
          simp only [x, pbin]
          rw [pr_mul_not_of_irr _ _ h hc (hind 0 n), ih 0]
          rfl
      | succ m =>
          by_cases hmn : m = n
          · subst hmn
            simp only [x, pbin, if_true]
            rw [pr_mul_of_irr _ _ h hc (hind m m), ih m, pbin_zero_of_lt _ m (m + 1) (by omega)]
            simp [pp]
          · simp only [x, if_neg hmn, pbin]
            rw [pr_or_excl _ _ _ h hc, pr_mul_of_irr _ _ h hc (hind m n),
              pr_mul_not_of_irr _ _ h hc (hind (m + 1) n), ih m, ih (m + 1)]
            simp only [pp, q]


/-! ## §8: 第 29 章の data (外部公理) -/

/-- §8 の事象の系列 a_λ (λ 回目に起こる) の名付け (内容を主張しない)。 -/
axiom aP : ℕ → IProp
/-- §8 の à priori data の名付け (内容を主張しない)。 -/
axiom hP : IProp
/-- h は矛盾する連言でない (公理 (i) の但し書きを h に当てはめたもの)。 -/
axiom ax_data_consP : Cons hP
/-- Poisson の定理の暗黙の前提 (folio 344–345 「It does not dispense, however, with the other inexplicit
assumption」): 各回の生起は、それまでの生起の回数を知っても変わらない。 -/
axiom ax_poisson_independence : PoissonIndep aP hP

/-- 限界 sp ± l の確率をキャリアの上で: 排反な選言肢 _m x_s の確率の和 (|m − sp| < l)。 -/
noncomputable def probWithinI (a : ℕ → IProp) (h : IProp) (s : ℕ) (l : ℝ) : ℝ :=
  ∑ m ∈ (range (s + 1)).filter (fun m : ℕ => |(m : ℝ) - s * pmean (pp a h) s| < l), PrI (x a m s) h

/-- ch29-057 (外部公理依存): data の上で、限界 sp ± l の確率は Poisson 二項分布の和。 -/
theorem th_29_057 (s : ℕ) (l : ℝ) : probWithinI aP hP s l = probWithinP (pp aP hP) s l := by
  unfold probWithinI probWithinP
  exact Finset.sum_congr rfl (fun m _ => th_poisson_dist aP hP ax_data_consP ax_poisson_independence s m)

/-! ## §8: 変数変換 (060・061・063、外部公理に依らない) -/

theorem cont_poisson_exp (v : ℝ) : Continuous (fun t : ℝ => exp (-(t ^ 2) / v)) := by fun_prop

/-- ch29-060 (定: 置換 x/(k√s) = t): 2/(k√(πs)) ∫_0^l e^{−x²/k²s} dx = 2/√π ∫_0^{l/(k√s)} e^{−t²} dt。 -/
theorem th_29_060 (k s l : ℝ) (hk : 0 < k) (hs : 0 < s) :
    2 / (k * √(π * s)) * (∫ t in (0 : ℝ)..l, exp (-(t ^ 2) / (k ^ 2 * s)))
      = 2 / √π * ∫ t in (0 : ℝ)..(l / (k * √s)), exp (-(t ^ 2)) := by
  have hss : 0 < √s := Real.sqrt_pos.mpr hs
  have hc : 0 < k * √s := mul_pos hk hss
  have hc2 : (k * √s) ^ 2 = k ^ 2 * s := by rw [mul_pow, Real.sq_sqrt hs.le]
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  have key := intervalIntegral.integral_comp_mul_left (fun t => exp (-(t ^ 2) / (k ^ 2 * s)))
    (a := 0) (b := l / (k * √s)) hc.ne'
  simp only [mul_zero, smul_eq_mul] at key
  rw [show k * √s * (l / (k * √s)) = l by field_simp] at key
  have e : (∫ t in (0 : ℝ)..(l / (k * √s)), exp (-((k * √s * t) ^ 2) / (k ^ 2 * s)))
      = ∫ t in (0 : ℝ)..(l / (k * √s)), exp (-(t ^ 2)) := by
    congr 1; ext t; congr 1; rw [mul_pow, hc2]; field_simp
  rw [e] at key
  rw [key, show √(π * s) = √π * √s from Real.sqrt_mul pi_pos.le s]
  field_simp

/-- ch29-063 の恒等式 (外部公理に依らない): l/(k√s) = γ (061 の名付け) なら 058 の P は
2/√π ∫_0^γ e^{−t²} dt + e^{−γ²}/(k√(πs))。 -/
theorem th_29_063_eq (p : ℕ → ℝ) (s : ℕ) (l γ : ℝ) (hk : 0 < kP p s) (hs : 0 < (s : ℝ))
    (hγ : l / (kP p s * √s) = γ) :
    poissonP p s l = 2 / √π * (∫ t in (0 : ℝ)..γ, exp (-(t ^ 2))) + exp (-(γ ^ 2)) / (kP p s * √(π * s)) := by
  unfold poissonP
  rw [th_29_060 _ _ l hk hs, hγ]
  congr 2
  have hss : 0 < √s := Real.sqrt_pos.mpr hs
  have hl : l = γ * (kP p s * √s) := by rw [← hγ]; field_simp
  rw [hl, mul_pow, mul_pow, Real.sq_sqrt hs.le]
  field_simp

/-- ch29-062: l/(k√s) = γ なら限界 sp ± l は sp ± γk√s。 -/
theorem th_29_062 (sp l γ k sq m : ℝ) (hc : 0 < k * sq) (hγ : l / (k * sq) = γ) :
    (sp - l < m ∧ m < sp + l) ↔ (sp - γ * k * sq < m ∧ m < sp + γ * k * sq) := by
  have hl : l = γ * k * sq := by rw [← hγ, mul_assoc, div_mul_cancel₀ l hc.ne']
  rw [hl]

/-! ## §8: Poisson 二項分布の総和・平均・分散 (059 の k の意味; 外部公理に依らない) -/

/-- 1 回足したときの和の漸化式。 -/
theorem pbin_sum_succ (p : ℕ → ℝ) (n : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ range (n + 2), f m * pbin p (n + 1) m =
      p (n + 1) * ∑ m ∈ range (n + 1), f (m + 1) * pbin p n m +
      q (p (n + 1)) * ∑ m ∈ range (n + 1), f m * pbin p n m := by
  have key : ∑ m ∈ range (n + 2), f m * pbin p n m = ∑ m ∈ range (n + 1), f m * pbin p n m := by
    rw [Finset.sum_range_succ, pbin_zero_of_lt p n (n + 1) (by omega), mul_zero, add_zero]
  rw [← key, Finset.sum_range_succ' (fun m => f m * pbin p (n + 1) m),
    Finset.sum_range_succ' (fun m => f m * pbin p n m)]
  simp only [pbin]
  have e : ∀ m, f (m + 1) * (p (n + 1) * pbin p n m + q (p (n + 1)) * pbin p n (m + 1))
      = p (n + 1) * (f (m + 1) * pbin p n m) + q (p (n + 1)) * (f (m + 1) * pbin p n (m + 1)) := by
    intro m; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Σ_{λ ≤ n} p_λ (= np、生起の回数の平均)。 -/
noncomputable def psum (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ trials n, p j

/-- Σ_{λ ≤ n} p_λ q_λ (= k²n/2、生起の回数の分散)。 -/
noncomputable def pqsum (p : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ trials n, p j * q (p j)

theorem psum_succ (p : ℕ → ℝ) (n : ℕ) : psum p (n + 1) = psum p n + p (n + 1) := by
  unfold psum trials; rw [Finset.sum_Icc_succ_top (by omega)]

theorem pqsum_succ (p : ℕ → ℝ) (n : ℕ) : pqsum p (n + 1) = pqsum p n + p (n + 1) * q (p (n + 1)) := by
  unfold pqsum trials; rw [Finset.sum_Icc_succ_top (by omega)]

theorem pbin_moments (p : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ range (n + 1), pbin p n m = 1 ∧
    ∑ m ∈ range (n + 1), (m : ℝ) * pbin p n m = psum p n ∧
    ∑ m ∈ range (n + 1), (m : ℝ) ^ 2 * pbin p n m = pqsum p n + psum p n ^ 2 := by
  induction n with
  | zero => simp [pbin, psum, pqsum, trials]
  | succ n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have s0 := pbin_sum_succ p n (fun _ => 1)
      have s1 := pbin_sum_succ p n (fun m => (m : ℝ))
      have s2 := pbin_sum_succ p n (fun m => (m : ℝ) ^ 2)
      simp only [one_mul] at s0
      have e1 : ∑ m ∈ range (n + 1), ((m + 1 : ℕ) : ℝ) * pbin p n m
          = ∑ m ∈ range (n + 1), (m : ℝ) * pbin p n m + ∑ m ∈ range (n + 1), pbin p n m := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun m _ => by push_cast; ring)
      have e2 : ∑ m ∈ range (n + 1), ((m + 1 : ℕ) : ℝ) ^ 2 * pbin p n m
          = ∑ m ∈ range (n + 1), (m : ℝ) ^ 2 * pbin p n m
            + 2 * ∑ m ∈ range (n + 1), (m : ℝ) * pbin p n m + ∑ m ∈ range (n + 1), pbin p n m := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun m _ => by push_cast; ring)
      rw [e1] at s1
      rw [e2] at s2
      rw [h0] at s0 s1 s2
      rw [h1] at s1 s2
      rw [h2] at s2
      refine ⟨?_, ?_, ?_⟩
      · rw [s0]; unfold q; ring
      · rw [s1, psum_succ]; unfold q; ring
      · rw [s2, psum_succ, pqsum_succ]; unfold q; ring

/-- ch29-059 の k の意味 (外部公理に依らない): 生起の回数の分散 Σ (m − Σp_λ)² P(m) は Σp_λ q_λ で、
s > 0 なら k² s / 2 に等しい (k = √(2Σp_λq_λ/s))。 -/
theorem th_29_059 (p : ℕ → ℝ) (s : ℕ) (hs : 0 < s) (hpq : 0 ≤ pqsum p s) :
    ∑ m ∈ range (s + 1), ((m : ℝ) - psum p s) ^ 2 * pbin p s m = pqsum p s ∧
    pqsum p s = kP p s ^ 2 * s / 2 := by
  obtain ⟨h0, h1, h2⟩ := pbin_moments p s
  constructor
  · have e : ∑ m ∈ range (s + 1), ((m : ℝ) - psum p s) ^ 2 * pbin p s m
        = ∑ m ∈ range (s + 1), (m : ℝ) ^ 2 * pbin p s m
          - 2 * psum p s * ∑ m ∈ range (s + 1), (m : ℝ) * pbin p s m
          + psum p s ^ 2 * ∑ m ∈ range (s + 1), pbin p s m := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [e, h0, h1, h2]; ring
  · have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    unfold kP
    rw [Real.sq_sqrt (by unfold pqsum at hpq; positivity)]
    unfold pqsum; field_simp

theorem pbin_nonneg (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) : ∀ n m, 0 ≤ pbin p n m := by
  intro n
  induction n with
  | zero => intro m; unfold pbin; split_ifs <;> norm_num
  | succ n ih =>
      intro m
      have hq : 0 ≤ q (p (n + 1)) := by unfold q; linarith [(hp (n + 1)).2]
      cases m with
      | zero => simp only [pbin]; exact mul_nonneg hq (ih 0)
      | succ m =>
          simp only [pbin]
          exact add_nonneg (mul_nonneg (hp (n + 1)).1 (ih m)) (mul_nonneg hq (ih (m + 1)))

theorem s_pmean (p : ℕ → ℝ) (s : ℕ) : (s : ℝ) * pmean p s = psum p s := by
  unfold pmean psum
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h; simp [trials]
  · have : (0 : ℝ) < s := by exact_mod_cast h
    field_simp

/-- Poisson の定理の Chebyshev 型の形 (外部公理に依らない): 各 p_λ ∈ [0, 1]、l > 0 なら
限界 sp ± l の間にある確率は 1 − Σp_λq_λ / l² 以上。解析的近似 (058) を使わない弱い形。 -/
theorem th_29_poisson_cheb (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (s : ℕ) (l : ℝ) (hl : 0 < l) :
    1 - pqsum p s / l ^ 2 ≤ probWithinP p s l := by
  obtain ⟨h0, h1, h2⟩ := pbin_moments p s
  have hnn := pbin_nonneg p hp s
  unfold probWithinP
  set F := fun m : ℕ => |(m : ℝ) - s * pmean p s| < l with hF
  have hsplit := Finset.sum_filter_add_sum_filter_not (range (s + 1)) F (fun m => pbin p s m)
  rw [h0] at hsplit
  have hvar : ∑ m ∈ range (s + 1), ((m : ℝ) - psum p s) ^ 2 * pbin p s m = pqsum p s := by
    have e : ∑ m ∈ range (s + 1), ((m : ℝ) - psum p s) ^ 2 * pbin p s m
        = ∑ m ∈ range (s + 1), (m : ℝ) ^ 2 * pbin p s m
          - 2 * psum p s * ∑ m ∈ range (s + 1), (m : ℝ) * pbin p s m
          + psum p s ^ 2 * ∑ m ∈ range (s + 1), pbin p s m := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [e, h0, h1, h2]; ring
  have hout : ∑ m ∈ (range (s + 1)).filter (fun m => ¬ F m), pbin p s m ≤ pqsum p s / l ^ 2 := by
    have hl2 : 0 < l ^ 2 := by positivity
    rw [le_div_iff₀ hl2, Finset.sum_mul, ← hvar]
    calc ∑ m ∈ (range (s + 1)).filter (fun m => ¬ F m), pbin p s m * l ^ 2
        ≤ ∑ m ∈ (range (s + 1)).filter (fun m => ¬ F m), ((m : ℝ) - psum p s) ^ 2 * pbin p s m := by
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_filter] at hm
          have hF' : l ≤ |(m : ℝ) - psum p s| := by
            have := hm.2; simp only [hF, not_lt, s_pmean] at this; exact this
          have : l ^ 2 ≤ ((m : ℝ) - psum p s) ^ 2 := by
            rw [← sq_abs ((m : ℝ) - psum p s)]; exact pow_le_pow_left₀ hl.le hF' 2
          nlinarith [hnn m]
      _ ≤ ∑ m ∈ range (s + 1), ((m : ℝ) - psum p s) ^ 2 * pbin p s m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro m _ _; exact mul_nonneg (sq_nonneg _) (hnn m)
  linarith

/-! ## §8: 解析的近似 (外部公理) と 058・063 -/

/-- Poisson の定理の解析的近似 (外部公理; Lindeberg–Feller の中心極限定理の Poisson 二項分布の場合):
各 p_λ が δ ≤ p_λ ≤ 1 − δ (δ > 0) を満たし γ > 0 なら、|m − sp| < γk√s の確率は s → ∞ で Θ(γ) に近づく。
Mathlib にない (B38 の ax_normal_approx はその p_λ = p の場合)。 -/
axiom ax_poisson_approx (p : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hb : ∀ j, δ ≤ p j ∧ p j ≤ 1 - δ)
    (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun s : ℕ => probWithinP p s (γ * kP p s * √s)) atTop (𝓝 (Θ γ))

theorem pqsum_ge (p : ℕ → ℝ) (δ : ℝ) (hb : ∀ j, δ ≤ p j ∧ p j ≤ 1 - δ) (s : ℕ) :
    s * (δ * (1 - δ)) ≤ pqsum p s := by
  unfold pqsum
  have h := Finset.card_nsmul_le_sum (trials s) (fun j => p j * q (p j)) (δ * (1 - δ)) (by
    intro j _
    obtain ⟨h1, h2⟩ := hb j
    unfold q; nlinarith)
  simp only [trials, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at h
  exact h

/-- k√s = √(2Σp_λq_λ) (s > 0)。 -/
theorem kP_mul_sqrt (p : ℕ → ℝ) (s : ℕ) (hs : 0 < s) : kP p s * √s = √(2 * pqsum p s) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  unfold kP
  rw [← Real.sqrt_mul' _ hs'.le]
  congr 1
  unfold pqsum; field_simp

/-- 058・063 の補正項 e^{−γ²}/(k√(πs)) は s → ∞ で 0 (δ ≤ p_λ ≤ 1 − δ、δ > 0)。 -/
theorem poisson_corr_vanish (p : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hb : ∀ j, δ ≤ p j ∧ p j ≤ 1 - δ)
    (γ : ℝ) :
    Tendsto (fun s : ℕ => exp (-(γ ^ 2)) / (kP p s * √(π * s))) atTop (𝓝 0) := by
  have hδ1 : δ < 1 := by have := hb 0; linarith
  have hc : 0 < δ * (1 - δ) := by nlinarith
  apply tendsto_const_nhds.div_atTop
  have hlow : Tendsto (fun s : ℕ => √(2 * (s * (δ * (1 - δ)))) * √π) atTop atTop := by
    apply Tendsto.atTop_mul_const (Real.sqrt_pos.mpr pi_pos)
    apply tendsto_sqrt_atTop.comp
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hc
    exact this.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [eventually_ge_atTop 1] with s hs
  rw [show √(π * s) = √π * √s from Real.sqrt_mul pi_pos.le s,
    show kP p s * (√π * √(s : ℝ)) = (kP p s * √s) * √π by ring, kP_mul_sqrt p s hs]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  linarith [pqsum_ge p δ hb s]

theorem kP_pos (p : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hb : ∀ j, δ ≤ p j ∧ p j ≤ 1 - δ) (s : ℕ) (hs : 1 ≤ s) :
    0 < kP p s := by
  have hδ1 : δ < 1 := by have := hb 0; linarith
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hge := pqsum_ge p δ hb s
  have hc : 0 < δ * (1 - δ) := by nlinarith
  have : 0 < pqsum p s := lt_of_lt_of_le (mul_pos hs' hc) hge
  unfold kP
  apply Real.sqrt_pos.mpr
  unfold pqsum at this
  positivity

/-- ch29-063 (外部公理依存): data の上で、限界 sp ± γk√s の確率と
2/√π ∫_0^γ e^{−t²} dt + e^{−γ²}/(k√(πs)) の差は s → ∞ で 0。各回の確率 p_λ = a_λ/h が
δ ≤ p_λ ≤ 1 − δ (δ > 0) を満たす場合 (解析的近似の条件; 印刷にはない)。 -/
theorem th_29_063 (δ : ℝ) (hδ : 0 < δ) (hb : ∀ j, δ ≤ PrI (aP j) hP ∧ PrI (aP j) hP ≤ 1 - δ)
    (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun s : ℕ => probWithinI aP hP s (γ * kP (pp aP hP) s * √s) -
      (2 / √π * (∫ t in (0 : ℝ)..γ, exp (-(t ^ 2))) + exp (-(γ ^ 2)) / (kP (pp aP hP) s * √(π * s))))
      atTop (𝓝 0) := by
  have hb' : ∀ j, δ ≤ pp aP hP j ∧ pp aP hP j ≤ 1 - δ := hb
  have h := ((ax_poisson_approx (pp aP hP) δ hδ hb' γ hγ).sub_const (Θ γ)).sub
    (poisson_corr_vanish (pp aP hP) δ hδ hb' γ)
  rw [sub_self, sub_zero] at h
  refine h.congr (fun s => ?_)
  rw [th_29_057]; unfold Θ; ring

/-- ch29-058 (外部公理依存): data の上で、限界 sp ± l の確率と 058 の P の差は s → ∞ で 0
(l = γk√s、γ > 0 固定; 各回の確率は δ ≤ p_λ ≤ 1 − δ)。 -/
theorem th_29_058 (δ : ℝ) (hδ : 0 < δ) (hb : ∀ j, δ ≤ PrI (aP j) hP ∧ PrI (aP j) hP ≤ 1 - δ)
    (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun s : ℕ => probWithinI aP hP s (γ * kP (pp aP hP) s * √s) -
      poissonP (pp aP hP) s (γ * kP (pp aP hP) s * √s)) atTop (𝓝 0) := by
  have hb' : ∀ j, δ ≤ pp aP hP j ∧ pp aP hP j ≤ 1 - δ := hb
  refine (th_29_063 δ hδ hb γ hγ).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hk := kP_pos (pp aP hP) δ hδ hb' s hs
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hss : 0 < √(s : ℝ) := Real.sqrt_pos.mpr hs'
  rw [th_29_063_eq (pp aP hP) s _ γ hk hs' (by field_simp)]


/-! ## §10 (folio 347–348): 戻さない取り出し (Czuber・Pearson) と Poisson の逆説 -/

/-- σ 個 (うち黒 K 個) の壺から s 個を戻さずに取り出して黒が k 個の確率 (超幾何分布)。 -/
noncomputable def hyp (σ K s k : ℕ) : ℝ :=
  (K.choose k : ℝ) * ((σ - K).choose (s - k) : ℝ) / (σ.choose s : ℝ)

/-- ch29-065 (数値評価): σ = 10、黒 K = 4 (p = 2/5)、s = 5 回の取り出しで、黒の数の平均は sp = 2、
平均からの偏りの二乗の平均は 2/3 = s(σ − s)/(σ − 1) · pq。戻す場合に取り出しの回数を
(σ − s)/σ · s とした値 ((σ − s)/σ · s) pq は 3/5 で、比は σ/(σ − 1) = 10/9 (σ が大きいと 1 に近づく)。 -/
theorem th_29_065 :
    ∑ k ∈ range 6, hyp 10 4 5 k = 1 ∧
    ∑ k ∈ range 6, (k : ℝ) * hyp 10 4 5 k = 5 * (2 / 5) ∧
    ∑ k ∈ range 6, ((k : ℝ) - 2) ^ 2 * hyp 10 4 5 k = 5 * (10 - 5) / (10 - 1) * ((2 / 5) * (3 / 5)) ∧
    5 * (10 - 5) / (10 - 1) * ((2 / 5) * (3 / 5)) = (2 / 3 : ℝ) ∧
    ((10 - 5) / 10 * 5) * ((2 / 5) * (3 / 5)) = (3 / 5 : ℝ) := by
  have c : (Nat.choose 10 5 = 252) ∧ (Nat.choose 6 5 = 6) ∧ (Nat.choose 6 4 = 15) ∧
      (Nat.choose 6 3 = 20) ∧ (Nat.choose 6 2 = 15) ∧ (Nat.choose 6 1 = 6) ∧ (Nat.choose 6 0 = 1) ∧
      (Nat.choose 4 0 = 1) ∧ (Nat.choose 4 1 = 4) ∧ (Nat.choose 4 2 = 6) ∧ (Nat.choose 4 3 = 4) ∧
      (Nat.choose 4 4 = 1) ∧ (Nat.choose 4 5 = 0) := by decide
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := c
  simp only [hyp, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]

/-- ch29-065: s(σ − s)/(σ − 1) と (σ − s)/σ · s の比は σ/(σ − 1) (σ > 1)。 -/
theorem th_29_065_ratio (σ s : ℝ) (hσ : 1 < σ) (hs : 0 < s) (hσs : s < σ) :
    (s * (σ - s) / (σ - 1)) / ((σ - s) / σ * s) = σ / (σ - 1) := by
  have h1 : σ - 1 ≠ 0 := by linarith
  have h2 : σ - s ≠ 0 := by linarith
  have h3 : σ ≠ 0 := by linarith
  field_simp

/-- ch29-067 (定: Pearson の場合 s > pσ を前提 hs に写す): 取り出す数 s が黒の総数 K = pσ を超えると、
s 個すべてが黒になる確率は 0 (割合の全範囲を扱うとき、黒の割合は 1 に届かない)。 -/
theorem th_29_067 (σ K s : ℕ) (hs : K < s) : hyp σ K s s = 0 := by
  unfold hyp
  rw [Nat.choose_eq_zero_of_lt hs]
  simp

/-- Poisson の壺 (folio 348): 5 個の玉 (0, 1, 2 が黒、3, 4 が白) から 2 個を順に戻さず取り出す。
順序のついた 20 通りが同じ確からしさ。 -/
def pairs : Finset (Fin 5 × Fin 5) := Finset.univ.filter (fun ij => ij.1 ≠ ij.2)

def black (i : Fin 5) : Prop := i.val < 3

instance : DecidablePred black := fun i => inferInstanceAs (Decidable (i.val < 3))

theorem pairs_cards :
    pairs.card = 20 ∧ (pairs.filter (fun ij => black ij.2)).card = 12 ∧
    (pairs.filter (fun ij => black ij.1)).card = 12 ∧
    (pairs.filter (fun ij => black ij.1 ∧ black ij.2)).card = 6 ∧
    (pairs.filter (fun ij => ¬ black ij.1)).card = 8 ∧
    (pairs.filter (fun ij => ¬ black ij.1 ∧ black ij.2)).card = 6 := by decide

/-- ch29-068 (数値評価; l = μ = 1 の Poisson の壺): 最初の 1 個の色が知られていなければ、次の 1 個が黒の
確率 12/20 = 3/5 は最初の 1 個を取り出す前の確率 3/5 と同じ (Poisson の結論)。最初の 1 個が黒と
知られていれば 6/12 = 1/2、白と知られていれば 6/8 = 3/4 で、知識は確率を変える (Keynes の但し書き)。 -/
theorem th_29_068 :
    ((pairs.filter (fun ij => black ij.2)).card : ℝ) / pairs.card = 3 / 5 ∧
    ((pairs.filter (fun ij => black ij.1)).card : ℝ) / pairs.card = 3 / 5 ∧
    ((pairs.filter (fun ij => black ij.1 ∧ black ij.2)).card : ℝ) /
      (pairs.filter (fun ij => black ij.1)).card = 1 / 2 ∧
    ((pairs.filter (fun ij => ¬ black ij.1 ∧ black ij.2)).card : ℝ) /
      (pairs.filter (fun ij => ¬ black ij.1)).card = 3 / 4 := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := pairs_cards
  rw [c1, c2, c3, c4, c5, c6]
  norm_num

/-! ## §11 (folio 349–351): 継起の仮定の人工例 — 記法 (定) -/

/-- ch29-070: p := r/s (r 回の生起を s 回の機会で観察した à priori の確率)。 -/
noncomputable def pR (r s : ℕ) : ℝ := (r : ℝ) / s

/-- ch29-071: Bernoulli の定理を直接当てた n 回続けての確率 p^n の名付け。 -/
noncomputable def bernP (p : ℝ) (n : ℕ) : ℝ := p ^ n

/-- ch29-072: p^n = (r/s)^n。 -/
theorem th_29_072 (r s n : ℕ) : bernP (pR r s) n = ((r : ℝ) / s) ^ n := rfl

/-- ch29-079: sp (= r) (s > 0)。 -/
theorem th_29_079 (r s : ℕ) (hs : 0 < s) : (s : ℝ) * pR r s = r := by
  have : (0 : ℝ) < s := by exact_mod_cast hs
  unfold pR; field_simp

/-- 人工例の仮定 (folio 349–350、ch29-073・083): 最初の k 回すべてに起こったと知れば、k+1 回目の確率は
(r + k)/(s + k) (前提 y_k ∧ h が整合な場合)。k = 1 が「the probability at the second becomes (r+1)/(s+1)」。 -/
def SuccRule (a : ℕ → IProp) (h : IProp) (r s : ℕ) : Prop :=
  ∀ k, Cons (iand (y a k) h) → PrI (a (k + 1)) (iand (y a k) h) = ((r : ℝ) + k) / ((s : ℝ) + k)

/-- ch29-074 の一般形 (第 II 部の公理と前提 SuccRule のみ): y_n/h = Π_{i<n} (r + i)/(s + i)。
Def. X 左形 y_{i+1}/h = a_{i+1}/y_i h · y_i/h の反復 (phase14a の th_29_045_a・th_29_046 と同じ形)。 -/
theorem th_29_074_of (a : ℕ → IProp) (h : IProp) (r s : ℕ) (hc : Cons h) (hR : SuccRule a h r s) :
    ∀ n, PrI (y a n) h = ∏ i ∈ range n, ((r : ℝ) + i) / ((s : ℝ) + i) := by
  intro n
  induction n with
  | zero => simp only [y, Finset.prod_range_zero]; exact itrue_certain h hc
  | succ n ih =>
      show PrI (iand (a (n + 1)) (y a n)) h = _
      rw [def_X_left_i, Finset.prod_range_succ]
      by_cases h0 : PrI (y a n) h = 0
      · rw [h0, mul_zero, ← ih, h0, zero_mul]
      · rw [hR n (cons_of_pos _ h h0 hc), ih, mul_comm]

/-! ## §11: 第 29 章の data (外部公理) -/

/-- §11 の人工例の系列: à priori の経験 (s 回中 r 回) ごとの事象の系列 a_k (k 回目に起こる) の名付け。 -/
axiom aS : ℕ → ℕ → ℕ → IProp
/-- §11 の人工例の data の名付け。 -/
axiom hS : ℕ → ℕ → IProp
/-- data は矛盾する連言でない。 -/
axiom ax_data_consS (r s : ℕ) : Cons (hS r s)
/-- 人工例の仮定 (folio 349–350): 起こるたびに次の回の確率が (r + k)/(s + k) に上がる (0 < r < s)。
Pólya の壺 (黒 r・白 s − r、取り出した玉を同じ色の玉 1 個を添えて戻す) がこの仮定の標準的な模型 (KeynesXXIXc_model.succRule_MS で検査)。 -/
axiom ax_succession_rule (r s : ℕ) (hr : 0 < r) (hrs : r < s) : SuccRule (aS r s) (hS r s) r s

/-- ch29-074 (外部公理依存): data の上で、n 回続けて起こる確率は r/s · (r+1)/(s+1) · · · (r+n−1)/(s+n−1)。 -/
theorem th_29_074 (r s : ℕ) (hr : 0 < r) (hrs : r < s) (n : ℕ) :
    PrI (y (aS r s) n) (hS r s) = ∏ i ∈ range n, ((r : ℝ) + i) / ((s : ℝ) + i) :=
  th_29_074_of _ _ r s (ax_data_consS r s) (ax_succession_rule r s hr hrs) n

/-- ch29-070 (data の上の値、外部公理依存): 1 回目の確率は p = r/s。 -/
theorem th_29_070_data (r s : ℕ) (hr : 0 < r) (hrs : r < s) :
    PrI (aS r s 1) (hS r s) = pR r s := by
  have h1 := th_29_074 r s hr hrs 1
  simp only [Finset.prod_range_one, Nat.cast_zero, add_zero] at h1
  have hx : y (aS r s) 1 = iand (aS r s 1) itrue := rfl
  rw [hx] at h1
  have e : PrI (iand (aS r s 1) itrue) (hS r s) = PrI (aS r s 1) (hS r s) :=
    subst_taut (Form.conj (Form.var 0) Form.tru) (Form.var 0) (fun _ => aS r s 1) _ (ax_data_consS r s)
      (by intro v; cases h0 : v 0 <;> simp [evalB, h0])
  rw [← e, h1]; rfl

/-- ch29-073 (外部公理依存): 1 回目に起これば 2 回目の確率は (r + 1)/(s + 1)。前提 y_1 ∧ h の整合は
y_1/h = r/s ≠ 0 から出る (cons_of_pos)。 -/
theorem th_29_073 (r s : ℕ) (hr : 0 < r) (hrs : r < s) :
    PrI (aS r s 2) (iand (y (aS r s) 1) (hS r s)) = ((r : ℝ) + 1) / ((s : ℝ) + 1) := by
  have h1 := th_29_074 r s hr hrs 1
  simp only [Finset.prod_range_one, Nat.cast_zero, add_zero] at h1
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast (lt_trans hr hrs)
  have hne : PrI (y (aS r s) 1) (hS r s) ≠ 0 := by rw [h1]; positivity
  have := ax_succession_rule r s hr hrs 1 (cons_of_pos _ _ hne (ax_data_consS r s))
  rw [this]; push_cast; ring

/-! ## §11: 075 (積 = 階乗の比) と Beta 積分 -/

/-- ch29-075: r/s · (r+1)/(s+1) · · · (r+n−1)/(s+n−1) = (r+n−1)! (s−1)! / ((s+n−1)! (r−1)!) (r, s ≥ 1)。 -/
theorem th_29_075 (r s n : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ∏ i ∈ range n, ((r : ℝ) + i) / ((s : ℝ) + i)
      = ((r + n - 1).factorial * (s - 1).factorial : ℝ) / ((s + n - 1).factorial * (r - 1).factorial) := by
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction n with
  | zero =>
      simp only [Finset.prod_range_zero, add_zero, Nat.add_sub_cancel]
      have h1 : (r.factorial : ℝ) ≠ 0 := by positivity
      have h2 : (s.factorial : ℝ) ≠ 0 := by positivity
      field_simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      rw [show r + 1 + (n + 1) - 1 = (r + n) + 1 by omega, show s + 1 + (n + 1) - 1 = (s + n) + 1 by omega,
        show r + 1 + n - 1 = r + n by omega, show s + 1 + n - 1 = s + n by omega]
      rw [Nat.factorial_succ (r + n), Nat.factorial_succ (s + n)]
      have h1 : ((r + n).factorial : ℝ) ≠ 0 := by positivity
      have h2 : ((s + n).factorial : ℝ) ≠ 0 := by positivity
      have h3 : (r.factorial : ℝ) ≠ 0 := by positivity
      have h4 : ((s : ℝ) + 1 + n) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- ch29-075 (data の上、外部公理依存): n 回続けて起こる確率 P は (r+n−1)! (s−1)! / ((s+n−1)! (r−1)!)。 -/
theorem th_29_075_data (r s : ℕ) (hr : 0 < r) (hrs : r < s) (n : ℕ) :
    PrI (y (aS r s) n) (hS r s)
      = ((r + n - 1).factorial * (s - 1).factorial : ℝ) / ((s + n - 1).factorial * (r - 1).factorial) := by
  rw [th_29_074 r s hr hrs n, th_29_075 r s n hr (by omega)]

/-- Beta 積分 (phase15b と同一; Mathlib の Complex.betaIntegral_eq_Gamma_mul_div から)。 -/
theorem beta_nat (m n : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n
      = Real.Gamma (m + 1) * Real.Gamma (n + 1) / Real.Gamma (m + n + 2) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div ((m : ℂ) + 1) ((n : ℂ) + 1)
    (by simp; positivity) (by simp; positivity)
  unfold Complex.betaIntegral at h
  simp only [add_sub_cancel_right, Complex.cpow_natCast] at h
  have hL : (∫ x in (0 : ℝ)..1, (x : ℂ) ^ m * (1 - (x : ℂ)) ^ n)
      = ((∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  have h1 : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have h3 : ((m : ℂ) + 1 + ((n : ℂ) + 1)) = (((m : ℝ) + n + 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hL, h3, h1, h2, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  exact_mod_cast h

/-- Beta 積分を階乗で: ∫_0^1 x^m (1 − x)^b dx = m! b! / (m + b + 1)!。 -/
theorem beta_fact (m b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ b = (m.factorial * b.factorial : ℝ) / (m + b + 1).factorial := by
  rw [beta_nat, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    show (m : ℝ) + b + 2 = ((m + b + 1 : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]

/-- 1 段の比: ∫ x^{m+1}(1 − x)^b = (m + 1)/(m + b + 2) · ∫ x^m (1 − x)^b。 -/
theorem beta_step (m b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ b
      = ((m : ℝ) + 1) / ((m : ℝ) + b + 2) * ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ b := by
  rw [beta_fact, beta_fact, show m + 1 + b + 1 = (m + b + 1) + 1 by ring,
    Nat.factorial_succ (m + b + 1), Nat.factorial_succ m]
  have h1 : ((m + b + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((m : ℝ) + b + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- ch29-075 と Beta 積分 (外部公理に依らない): 未知の確率 θ の事前の密度を θ^a (1 − θ)^b に比例させると
(r = a + 1、s = a + b + 2)、n 回続けての確率 ∫θ^n · (事前の密度) は r/s · (r+1)/(s+1) · · · (r+n−1)/(s+n−1)。 -/
theorem th_29_075_beta (a b n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ (a + n) * (1 - x) ^ b) / (∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b)
      = ∏ i ∈ range n, ((a + 1 : ℕ) + (i : ℝ)) / ((a + b + 2 : ℕ) + (i : ℝ)) := by
  have hpos : 0 < ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b := by rw [beta_fact]; positivity
  induction n with
  | zero => simp only [add_zero, Finset.prod_range_zero]; exact div_self hpos.ne'
  | succ n ih =>
      rw [Finset.prod_range_succ, ← ih, show a + (n + 1) = (a + n) + 1 by ring, beta_step]
      push_cast
      field_simp
      ring

/-- 継起の仮定と Beta 積分 (外部公理に依らない): 事前の密度 θ^a (1 − θ)^b (r = a + 1、s = a + b + 2) の下で、
x 回起こり c 回起こらなかった後の次の回の確率は (r + x)/(s + x + c) (ch29-073 は x = 1、c = 0)。 -/
theorem th_29_073_beta (a b x c : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ (a + x + 1) * (1 - t) ^ (b + c)) / (∫ t in (0 : ℝ)..1, t ^ (a + x) * (1 - t) ^ (b + c))
      = ((a + 1 : ℕ) + (x : ℝ)) / ((a + b + 2 : ℕ) + (x : ℝ) + c) := by
  have hpos : 0 < ∫ t in (0 : ℝ)..1, t ^ (a + x) * (1 - t) ^ (b + c) := by rw [beta_fact]; positivity
  rw [beta_step, mul_div_assoc, div_self hpos.ne', mul_one]
  push_cast
  ring

/-- 一様な事前の密度 (a = b = 0、無差別の原理) では th_29_073_beta は Laplace の継起の規則
(x + 1)/(x + c + 2) になる (r = 1、s = 2; 第 30 章 phase15b の th_30_026 と同じ値)。 -/
theorem th_29_laplace_uniform (x c : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ (x + 1) * (1 - t) ^ c) / (∫ t in (0 : ℝ)..1, t ^ x * (1 - t) ^ c)
      = ((x : ℝ) + 1) / ((x : ℝ) + c + 2) := by
  have h := th_29_073_beta 0 0 x c
  simp only [zero_add] at h
  rw [h]; push_cast; ring

/-! ## §11: 077・078 (Stirling の形の代数) -/

/-- ch29-076 の右辺 (印刷の式):
(r+n−1)^{r+n−½} e^{−(r+n−1)} s^{s−½} e^{−(s−1)} / ((s+n−1)^{s+n−½} e^{−(s+n−1)} r^{r−½} e^{−(r−1)})。 -/
noncomputable def st076 (r s n : ℝ) : ℝ :=
  (r + n - 1) ^ (r + n - 1 / 2) * exp (-(r + n - 1)) * (s ^ (s - 1 / 2) * exp (-(s - 1))) /
    ((s + n - 1) ^ (s + n - 1 / 2) * exp (-(s + n - 1)) * (r ^ (r - 1 / 2) * exp (-(r - 1))))

/-- ch29-077: 076 の右辺 = (r/s)^n · (1 + (n−1)/r)^{r+n−½} / (1 + (n−1)/s)^{s+n−½} (r, s > 0、n ≥ 1)。 -/
theorem th_29_077 (r s : ℝ) (n : ℕ) (hr : 0 < r) (hs : 0 < s) (hn : 1 ≤ n) :
    st076 r s n = (r / s) ^ n * (1 + (n - 1) / r) ^ (r + n - 1 / 2) / (1 + (n - 1) / s) ^ (s + n - 1 / 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : 0 ≤ 1 + ((n : ℝ) - 1) / r := by have : 0 ≤ ((n : ℝ) - 1) / r := div_nonneg (by linarith) hr.le; linarith
  have hB : 0 ≤ 1 + ((n : ℝ) - 1) / s := by have : 0 ≤ ((n : ℝ) - 1) / s := div_nonneg (by linarith) hs.le; linarith
  have eA : r + n - 1 = r * (1 + (n - 1) / r) := by field_simp; ring
  have eB : s + n - 1 = s * (1 + (n - 1) / s) := by field_simp; ring
  unfold st076
  rw [eA, eB, Real.mul_rpow hr.le hA, Real.mul_rpow hs.le hB]
  rw [← eA, ← eB]
  have pr : r ^ (r + n - 1 / 2) = r ^ (n : ℝ) * r ^ (r - 1 / 2) := by
    rw [← Real.rpow_add hr]; ring_nf
  have ps : s ^ (s + n - 1 / 2) = s ^ (n : ℝ) * s ^ (s - 1 / 2) := by
    rw [← Real.rpow_add hs]; ring_nf
  rw [pr, ps, Real.rpow_natCast, Real.rpow_natCast]
  have ex : exp (-(r + n - 1)) * exp (-(s - 1)) = exp (-(s + n - 1)) * exp (-(r - 1)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h1 : 0 < r ^ (r - 1 / 2) := Real.rpow_pos_of_pos hr _
  have h2 : 0 < s ^ (s - 1 / 2) := Real.rpow_pos_of_pos hs _
  have h3 : 0 < (1 + ((n : ℝ) - 1) / s) ^ (s + n - 1 / 2) := by
    apply Real.rpow_pos_of_pos; have : 0 ≤ ((n : ℝ) - 1) / s := div_nonneg (by linarith) hs.le; linarith
  have ex' : exp (-(r + n - 1)) = exp (-(s + n - 1)) * exp (-(r - 1)) / exp (-(s - 1)) := by
    rw [eq_div_iff (exp_pos _).ne']; exact ex
  rw [ex']
  generalize (1 + ((n : ℝ) - 1) / r) ^ (r + (n : ℝ) - 1 / 2) = A
  generalize (1 + ((n : ℝ) - 1) / s) ^ (s + (n : ℝ) - 1 / 2) = B at h3
  generalize r ^ (r - 1 / 2) = R at h1
  generalize s ^ (s - 1 / 2) = S at h2
  have e2 := exp_pos (-(s - 1))
  have e3 := exp_pos (-(s + n - 1))
  have e4 := exp_pos (-(r - 1))
  generalize exp (-(s - 1)) = E2 at e2
  generalize exp (-(s + n - 1)) = E3 at e3
  generalize exp (-(r - 1)) = E4 at e4
  rw [div_pow]
  field_simp

/-- ch29-078 の Q。 -/
noncomputable def Q078 (r s : ℝ) (n : ℕ) : ℝ :=
  (1 + (n - 1) / r) ^ ((r - 1 / 2) / n + 1) / (1 + (n - 1) / s) ^ ((s - 1 / 2) / n + 1)

/-- ch29-078: (r/s)^n (1 + (n−1)/r)^{r+n−½} / (1 + (n−1)/s)^{s+n−½} = p^n Q^n、
Q = (1 + (n−1)/r)^{(r−½)/n + 1} / (1 + (n−1)/s)^{(s−½)/n + 1}、p = r/s (r, s > 0、n ≥ 1)。 -/
theorem th_29_078 (r s : ℝ) (n : ℕ) (hr : 0 < r) (hs : 0 < s) (hn : 1 ≤ n) :
    (r / s) ^ n * (1 + (n - 1) / r) ^ (r + n - 1 / 2) / (1 + (n - 1) / s) ^ (s + n - 1 / 2)
      = (r / s) ^ n * Q078 r s n ^ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hA : 0 ≤ 1 + ((n : ℝ) - 1) / r := by have : 0 ≤ ((n : ℝ) - 1) / r := div_nonneg (by linarith) hr.le; linarith
  have hB : 0 ≤ 1 + ((n : ℝ) - 1) / s := by have : 0 ≤ ((n : ℝ) - 1) / s := div_nonneg (by linarith) hs.le; linarith
  have e1 : ((r - 1 / 2) / n + 1) * n = r + n - 1 / 2 := by field_simp; ring
  have e2 : ((s - 1 / 2) / n + 1) * n = s + n - 1 / 2 := by field_simp; ring
  unfold Q078
  rw [div_pow ((1 + ((n : ℝ) - 1) / r) ^ ((r - 1 / 2) / n + 1)) ((1 + ((n : ℝ) - 1) / s) ^ ((s - 1 / 2) / n + 1)) n,
    ← Real.rpow_natCast ((1 + ((n : ℝ) - 1) / r) ^ ((r - 1 / 2) / n + 1)) n,
    ← Real.rpow_natCast ((1 + ((n : ℝ) - 1) / s) ^ ((s - 1 / 2) / n + 1)) n,
    ← Real.rpow_mul hA, ← Real.rpow_mul hB, e1, e2, mul_div_assoc]

/-! ## §11: 076 (Stirling、Mathlib の Stirling.factorial_isEquivalent_stirling から) -/

/-- Stirling の形 g(x) = √(2π) x^{x+½} e^{−x}。 -/
noncomputable def gSt (x : ℝ) : ℝ := √(2 * π) * x ^ (x + 1 / 2) * exp (-x)

/-- n! ∼ √(2π) n^{n+½} e^{−n} (Mathlib の Stirling の書き換え)。 -/
theorem stirling_g : (fun m : ℕ => (m.factorial : ℝ)) ~[atTop] (fun m : ℕ => gSt m) := by
  refine Stirling.factorial_isEquivalent_stirling.congr_right ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold gSt
  rw [div_pow, Real.exp_one_pow, Real.rpow_add hm', ← Real.sqrt_eq_rpow, Real.rpow_natCast,
    show (2 : ℝ) * m * π = 2 * π * m by ring, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π),
    Real.exp_neg]
  field_simp

/-- 076 の右辺を g で書く: st076 = g(r+n−1) · (g(s)/s) / (g(s+n−1) · (g(r)/r)) (r, s ≥ 1)。 -/
theorem st076_g (r s : ℝ) (n : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    st076 r s n = gSt (r + n - 1) * (gSt s / s) / (gSt (s + n - 1) * (gSt r / r)) := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : 0 < r + n - 1 := by linarith
  have hN2 : 0 < s + n - 1 := by linarith
  unfold st076 gSt
  have er : r ^ (r - 1 / 2) = r ^ (r + 1 / 2) / r := by
    rw [show r - 1 / 2 = (r + 1 / 2) - 1 by ring, Real.rpow_sub_one hr0.ne']
  have es : s ^ (s - 1 / 2) = s ^ (s + 1 / 2) / s := by
    rw [show s - 1 / 2 = (s + 1 / 2) - 1 by ring, Real.rpow_sub_one hs0.ne']
  have e1 : r + n - 1 / 2 = (r + n - 1) + 1 / 2 := by ring
  have e2 : s + n - 1 / 2 = (s + n - 1) + 1 / 2 := by ring
  have xr : exp (-(r - 1)) = exp (-r) * exp 1 := by rw [← Real.exp_add]; ring_nf
  have xs : exp (-(s - 1)) = exp (-s) * exp 1 := by rw [← Real.exp_add]; ring_nf
  rw [er, es, e1, e2, xr, xs]
  have h1 : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < (s + n - 1) ^ (s + n - 1 + 1 / 2) := Real.rpow_pos_of_pos hN2 _
  have h3 : 0 < r ^ (r + 1 / 2) := Real.rpow_pos_of_pos hr0 _
  have h4 : 0 < exp 1 := exp_pos 1
  field_simp

/-- 076 の左辺 (075 の階乗の比)。 -/
noncomputable def fr075 (r s n : ℕ) : ℝ :=
  ((r + n - 1).factorial * (s - 1).factorial : ℝ) / ((s + n - 1).factorial * (r - 1).factorial)

/-- ch29-076 (≈: 印刷の = を r, s → ∞ での漸近同値 ∼ と読む): n を固定し r, s → ∞ なら
(r+n−1)! (s−1)! / ((s+n−1)! (r−1)!) ∼ 076 の右辺。Mathlib の Stirling の公式だけから。 -/
theorem th_29_076 (n : ℕ) (hn : 1 ≤ n) (r s : ℕ → ℕ) (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop) :
    (fun k => fr075 (r k) (s k) n) ~[atTop] (fun k => st076 (r k) (s k) n) := by
  have tN1 : Tendsto (fun k => r k + n - 1) atTop atTop :=
    tendsto_atTop_mono (fun k => (by omega : r k ≤ r k + n - 1)) hr
  have tN2 : Tendsto (fun k => s k + n - 1) atTop atTop :=
    tendsto_atTop_mono (fun k => (by omega : s k ≤ s k + n - 1)) hs
  have A := stirling_g.comp_tendsto tN1
  have B := stirling_g.comp_tendsto hs
  have C := stirling_g.comp_tendsto tN2
  have D := stirling_g.comp_tendsto hr
  have Bs := B.div (IsEquivalent.refl (u := fun k => ((s k : ℕ) : ℝ)))
  have Dr := D.div (IsEquivalent.refl (u := fun k => ((r k : ℕ) : ℝ)))
  have E := (A.mul Bs).div (C.mul Dr)
  refine (E.congr_left ?_).congr_right ?_
  · filter_upwards [hr.eventually_ge_atTop 1, hs.eventually_ge_atTop 1] with k hrk hsk
    simp only [Function.comp, Pi.mul_apply, Pi.div_apply]
    unfold fr075
    obtain ⟨r', hr'⟩ : ∃ t, r k = t + 1 := ⟨r k - 1, by omega⟩
    obtain ⟨s', hs'⟩ : ∃ t, s k = t + 1 := ⟨s k - 1, by omega⟩
    rw [hr', hs', Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.factorial_succ r', Nat.factorial_succ s']
    have h1 : (r'.factorial : ℝ) ≠ 0 := by positivity
    have h2 : (s'.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · filter_upwards [hr.eventually_ge_atTop 1, hs.eventually_ge_atTop 1] with k hrk hsk
    simp only [Function.comp, Pi.mul_apply, Pi.div_apply]
    have hr1 : (1 : ℝ) ≤ r k := by exact_mod_cast hrk
    have hs1 : (1 : ℝ) ≤ s k := by exact_mod_cast hsk
    rw [st076_g _ _ n hr1 hs1 hn]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring_nf

/-! ## §11: 080 (Keynes の批判: P は p^n と違う) -/

/-- ch29-080 (Keynes の批判の式): 0 < r < s、n ≥ 2 なら、正しく計算した P = Π (r+i)/(s+i) は
Bernoulli の値 p^n = (r/s)^n より真に大きい (i ≥ 1 の因子が r/s より大きい)。 -/
theorem th_29_080_gt (r s : ℝ) (hr : 0 < r) (hrs : r < s) (n : ℕ) (hn : 2 ≤ n) :
    (r / s) ^ n < ∏ i ∈ range n, (r + i) / (s + i) := by
  have hs : 0 < s := lt_trans hr hrs
  rw [show (r / s) ^ n = ∏ _i ∈ range n, r / s by rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_lt_prod
  · intro i _; positivity
  · intro i _
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    rw [div_le_div_iff₀ hs (by positivity)]; nlinarith
  · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [div_lt_div_iff₀ hs (by positivity)]; push_cast; nlinarith

/-- ch29-080 (数値評価): r = 1、s = 2 (p = ½)、n = 10 で P = 1/11、p^n = 1/1024。 -/
theorem th_29_080_num :
    ∏ i ∈ range 10, ((1 : ℝ) + i) / (2 + i) = 1 / 11 ∧ ((1 : ℝ) / 2) ^ 10 = 1 / 1024 := by
  constructor
  · simp only [Finset.prod_range_succ, Finset.prod_range_zero]; norm_num
  · norm_num

/-- ch29-080: n を固定し r, s → ∞ なら P / p^n → 1 (「P is approximately p^n」は n が r, s に比べて
小さいとき)。 -/
theorem th_29_080_lim (n : ℕ) (r s : ℕ → ℕ) (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop) :
    Tendsto (fun k => (∏ i ∈ range n, ((r k : ℝ) + i) / ((s k : ℝ) + i)) / (((r k : ℝ) / (s k)) ^ n))
      atTop (𝓝 1) := by
  have hr' : Tendsto (fun k => (r k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hr
  have hs' : Tendsto (fun k => (s k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
  have hf : Tendsto (fun k => ∏ i ∈ range n, (1 + (i : ℝ) / r k) / (1 + (i : ℝ) / s k)) atTop
      (𝓝 (∏ i ∈ range n, ((1 + 0) / (1 + 0) : ℝ))) := by
    apply tendsto_finset_prod
    intro i _
    exact (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hr')).div
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hs')) (by norm_num)
  simp only [add_zero, div_one, Finset.prod_const_one] at hf
  refine hf.congr' ?_
  filter_upwards [hr.eventually_ge_atTop 1, hs.eventually_ge_atTop 1] with k hrk hsk
  have h1 : (0 : ℝ) < r k := by exact_mod_cast hrk
  have h2 : (0 : ℝ) < s k := by exact_mod_cast hsk
  rw [show ((r k : ℝ) / s k) ^ n = ∏ _i ∈ range n, ((r k : ℝ) / s k) by
    rw [Finset.prod_const, Finset.card_range], ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  field_simp

/-- ch29-082: 過去の失敗の数 s − r。y 回中 x 回起こった後の失敗の確率は 1 − (r+x)/(s+y) = ((s−r) + (y−x))/(s+y)。 -/
theorem th_29_082 (r s x y : ℝ) (h : s + y ≠ 0) :
    1 - (r + x) / (s + y) = ((s - r) + (y - x)) / (s + y) := by
  field_simp; ring

/-! ## 外部公理の相対無矛盾性 (キャリアの上の自明な代入) -/

/-- **自明な代入** (phase14a の rel_cons_trivial に当たる): a_λ := ⊤、h := ⊤ は第 II 部の公理だけから
Cons ⊤ と PoissonIndep を満たす。aP・hP は新しい定数なので、第 II 部の公理群の任意の模型で
aP := fun _ => ⊤、hP := ⊤ と読めば ax_data_consP・ax_poisson_independence が成り立つ。ただし p_λ = 1 の
代入であり、058・063 の条件 δ ≤ p_λ ≤ 1 − δ の場合の無矛盾性はこの定理からは出ない。
ax_succession_rule は p = r/s < 1 を要するので自明な代入では満たされない (KeynesXXIXc_model.model_external)。 -/
theorem rel_cons_poisson_trivial : Cons itrue ∧ PoissonIndep (fun _ => itrue) itrue :=
  ⟨cons_true, fun _ _ hc => by rw [itrue_certain _ hc, itrue_certain _ cons_true]⟩

end KeynesXXIXc

/-! ## 模型: 外部公理が第 II 部の公理から導けないこと、および外部公理の無矛盾性

axiom 宣言そのものは模型にできないので、phase14a (phase12b の流儀) と同じく第 II 部の公理の文 13 本を
構造 `Sys` に写す。模型は可算の世界 W = (ℕ × ℕ) × ℕ の上の重み付きの模型 (命題 = 世界の集合、確率関係 =
条件付きの重みの比 (∑' による)、Cons = 空でない)。phase14a の 3 世界の模型は有限なので、y_k ∧ h が
すべての k で整合で y_k/h → 0 となる継起の仮定を満たせない (Pólya の壺では y_k ∧ ā_{k+1} がすべての k で
正の確率をもつ)。そこで世界を可算にした。

世界 ((r, s), j) は「data (r, s) の系列で、最初の j 回が起こり j + 1 回目が起こらない」。重みは
(½)^r (½)^s · (π_j − π_{j+1})、π_k = Π_{i<k} (r + i)/(s + i) (0 < r < s; 他の (r, s) は (1, 2) の重みを借りる)。
これは Pólya の壺 (黒 r・白 s − r、取り出した玉に同じ色の玉 1 個を添えて戻す) で最初の白が出る回の分布である。
h_{r,s} := {((r, s), j)}、a_k := {((r, s), j) | k ≤ j} と読むと y_k ∧ h の重みは (½)^r (½)^s π_k で、
a_{k+1}/y_k h = π_{k+1}/π_k = (r + k)/(s + k)。 -/

namespace KeynesXXIXc_model

open KeynesXXIXc (Form evalB Taut)
open Filter Topology

/-- 結合子・確率関係・整合性述語の組 (phase14a・phase12b と同一)。 -/
structure Ops where
  IProp : Type
  iand : IProp → IProp → IProp
  ior  : IProp → IProp → IProp
  inot : IProp → IProp
  iiff : IProp → IProp → IProp
  itrue : IProp
  PrI : IProp → IProp → ℝ
  Cons : IProp → Prop

/-- 構文の解釈 (KeynesXXIXc.interp と同じ形)。 -/
def Ops.interp (S : Ops) (env : ℕ → S.IProp) : Form → S.IProp
  | .var n    => env n
  | .tru      => S.itrue
  | .fls      => S.inot S.itrue
  | .conj f g => S.iand (S.interp env f) (S.interp env g)
  | .disj f g => S.ior (S.interp env f) (S.interp env g)
  | .neg f    => S.inot (S.interp env f)
  | .iffF f g => S.iiff (S.interp env f) (S.interp env g)

/-- **第 II 部の公理群** (本ファイル KeynesXXIXc の axiom 13 本の文をそのまま場に写したもの;
phase14a の Sys と同一)。 -/
structure Sys (S : Ops) : Prop where
  def_IX_i : ∀ p q h, S.PrI (S.iand p (S.inot q)) h + S.PrI (S.iand p q) h = S.PrI p h
  def_X_left_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI p (S.iand q h) * S.PrI q h
  def_X_right_i : ∀ p q h, S.PrI (S.iand p q) h = S.PrI q (S.iand p h) * S.PrI p h
  def_XI_i : ∀ (P Q R : ℝ), Q ≠ 0 → P * Q = R → P = R / Q
  ax_range_lo_i : ∀ p h, 0 ≤ S.PrI p h
  ax_range_hi_i : ∀ p h, S.PrI p h ≤ 1
  def_VIII_i : ∀ a b h, S.Cons (S.iand a h) → S.Cons (S.iand b h) →
    (S.PrI (S.iiff a b) h = 1 ↔ (S.PrI b (S.iand a h) = 1 ∧ S.PrI a (S.iand b h) = 1))
  def_VIII_i_src : ∀ a b h,
    S.PrI b (S.iand a h) = 1 → S.PrI a (S.iand b h) = 1 → S.PrI (S.iiff a b) h = 1
  ax_iii_taut : ∀ (f : Form) (env : ℕ → S.IProp) (h : S.IProp),
    S.Cons h → Taut f → S.PrI (S.interp env f) h = 1
  cons_true : S.Cons S.itrue
  cons_of_pos_src : ∀ a h, S.Cons (S.iand a h) → S.PrI a h ≠ 0
  cons_of_pos : ∀ a h, S.PrI a h ≠ 0 → S.Cons h → S.Cons (S.iand a h)
  cons_iff_taut : ∀ (f g : Form) (env : ℕ → S.IProp),
    Taut (Form.iffF f g) → (S.Cons (S.interp env f) ↔ S.Cons (S.interp env g))

/-! ### 記法と前提の形を場 S の上に写す (KeynesXXIXc の x・y・PoissonIndep・SuccRule と同じ文) -/

/-- _m x_n (KeynesXXIXc.x と同じ場合分け)。 -/
def Ops.x (S : Ops) (a : ℕ → S.IProp) : ℕ → ℕ → S.IProp
  | 0, 0 => S.itrue
  | _ + 1, 0 => S.inot S.itrue
  | 0, n + 1 => S.iand (S.inot (a (n + 1))) (Ops.x S a 0 n)
  | m + 1, n + 1 =>
      if m = n then S.iand (a (n + 1)) (Ops.x S a m n)
      else S.ior (S.iand (a (n + 1)) (Ops.x S a m n))
        (S.iand (S.inot (a (n + 1))) (Ops.x S a (m + 1) n))

/-- y_r (KeynesXXIXc.y と同じ)。 -/
def Ops.y (S : Ops) (a : ℕ → S.IProp) : ℕ → S.IProp
  | 0 => S.itrue
  | r + 1 => S.iand (a (r + 1)) (Ops.y S a r)

/-- ax_poisson_independence の形 (KeynesXXIXc.PoissonIndep と同じ文)。 -/
def Ops.PoissonIndep (S : Ops) (a : ℕ → S.IProp) (h : S.IProp) : Prop :=
  ∀ m n, S.Cons (S.iand (S.x a m n) h) → S.PrI (a (n + 1)) (S.iand (S.x a m n) h) = S.PrI (a (n + 1)) h

/-- ax_succession_rule の形 (KeynesXXIXc.SuccRule と同じ文)。 -/
def Ops.SuccRule (S : Ops) (a : ℕ → S.IProp) (h : S.IProp) (r s : ℕ) : Prop :=
  ∀ k, S.Cons (S.iand (S.y a k) h) → S.PrI (a (k + 1)) (S.iand (S.y a k) h) = ((r : ℝ) + k) / ((s : ℝ) + k)

/-! ### 可算の世界の重み付き模型 (重みは正で総和が有限) -/

section Count

variable {V : Type}

/-- 命題 p に含まれる世界の重みの和 (∑')。 -/
noncomputable def cmu (wt : V → ℝ) (p : Set V) : ℝ := ∑' v, p.indicator wt v

/-- 条件付きの重みの比。h の重みが 0 (h = ∅) のときは実数の除法の約定で 0 (phase14a の約定 0 と同じ値)。 -/
noncomputable def cprw (wt : V → ℝ) (p h : Set V) : ℝ := cmu wt (p ∩ h) / cmu wt h

/-- 構文の解釈 (集合の演算)。 -/
def cInterp (env : ℕ → Set V) : Form → Set V
  | .var n    => env n
  | .tru      => Set.univ
  | .fls      => (Set.univ)ᶜ
  | .conj f g => cInterp env f ∩ cInterp env g
  | .disj f g => cInterp env f ∪ cInterp env g
  | .neg f    => (cInterp env f)ᶜ
  | .iffF f g => (cInterp env f ∩ cInterp env g) ∪ ((cInterp env f)ᶜ ∩ (cInterp env g)ᶜ)

/-- 世界 v での真理値割当 (v ∈ env n の真偽)。 -/
noncomputable def valOf (env : ℕ → Set V) (v : V) : ℕ → Bool :=
  fun n => @decide (v ∈ env n) (Classical.propDecidable _)

/-- 解釈の帰属 ⟺ 世界での真理値評価。 -/
theorem mem_cInterp (env : ℕ → Set V) (f : Form) (v : V) :
    v ∈ cInterp env f ↔ evalB (valOf env v) f = true := by
  induction f with
  | var n => simp [cInterp, evalB, valOf]
  | tru => simp [cInterp, evalB]
  | fls => simp [cInterp, evalB]
  | conj f g ihf ihg => simp [cInterp, evalB, ihf, ihg]
  | disj f g ihf ihg => simp [cInterp, evalB, ihf, ihg]
  | neg f ihf => simp [cInterp, evalB, ihf]
  | iffF f g ihf ihg =>
    simp only [cInterp, evalB, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, ihf, ihg]
    cases evalB (valOf env v) f <;> cases evalB (valOf env v) g <;> simp

/-- Def. VIII の集合論的中身: h ⊆ (a ≡ b) ⟺ (a ∩ h ⊆ b ∧ b ∩ h ⊆ a)。 -/
theorem csubset_miff_iff (a b h : Set V) :
    h ⊆ (a ∩ b) ∪ (aᶜ ∩ bᶜ) ↔ (a ∩ h ⊆ b ∧ b ∩ h ⊆ a) := by
  constructor
  · intro H
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rcases H hv.2 with ⟨_, hb⟩ | ⟨hna, _⟩
      · exact hb
      · exact absurd hv.1 hna
    · rcases H hv.2 with ⟨ha, _⟩ | ⟨_, hnb⟩
      · exact ha
      · exact absurd hv.1 hnb
  · rintro ⟨H1, H2⟩ v hv
    by_cases ha : v ∈ a
    · exact Or.inl ⟨ha, H1 ⟨ha, hv⟩⟩
    · exact Or.inr ⟨ha, fun hb => ha (H2 ⟨hb, hv⟩)⟩

theorem cmu_empty (wt : V → ℝ) : cmu wt ∅ = 0 := by simp [cmu]

variable {wt : V → ℝ} (hw : ∀ v, 0 < wt v) (hs : Summable wt)

include hw in
theorem cmu_nonneg (p : Set V) : 0 ≤ cmu wt p :=
  tsum_nonneg (Set.indicator_nonneg (fun v _ => (hw v).le))

include hs in
/-- 重みの加法: h = (p ∩ h) ∪ (p̄ ∩ h)。 -/
theorem cmu_split (p h : Set V) : cmu wt h = cmu wt (p ∩ h) + cmu wt (pᶜ ∩ h) := by
  unfold cmu
  rw [← Summable.tsum_add (hs.indicator _) (hs.indicator _)]
  congr 1; ext v
  by_cases hp : v ∈ p <;> by_cases hh : v ∈ h <;> simp [Set.indicator, hp, hh]

include hw hs in
theorem cmu_pos {p : Set V} (hp : p.Nonempty) : 0 < cmu wt p := by
  obtain ⟨v, hv⟩ := hp
  exact (hs.indicator p).tsum_pos (Set.indicator_nonneg (fun v _ => (hw v).le)) v
    (by rw [Set.indicator_of_mem hv]; exact hw v)

include hw hs in
theorem cmu_eq_zero_iff (p : Set V) : cmu wt p = 0 ↔ p = ∅ := by
  constructor
  · intro H
    by_contra hne
    have := cmu_pos hw hs (Set.nonempty_iff_ne_empty.mpr hne)
    linarith
  · rintro rfl; exact cmu_empty wt

include hw hs in
theorem cmu_mono {p q : Set V} (hpq : p ⊆ q) : cmu wt p ≤ cmu wt q :=
  (hs.indicator p).tsum_le_tsum
    (fun v => Set.indicator_le_indicator_of_subset hpq (fun v => (hw v).le) v) (hs.indicator q)

include hw hs in
/-- 前提が整合なとき、確実 ⟺ 前提が結論を含む。 -/
theorem cprw_eq_one_iff {p h : Set V} (hh : h.Nonempty) : cprw wt p h = 1 ↔ h ⊆ p := by
  have hpos := cmu_pos hw hs hh
  rw [cprw, div_eq_one_iff_eq hpos.ne']
  have hsp := cmu_split hs p h
  constructor
  · intro H v hv
    by_contra hvp
    have h0 : cmu wt (pᶜ ∩ h) = 0 := by linarith
    rw [cmu_eq_zero_iff hw hs] at h0
    have hm : v ∈ pᶜ ∩ h := ⟨hvp, hv⟩
    rw [h0] at hm
    exact hm
  · intro H
    rw [Set.inter_eq_right.mpr H]

/-- 確実ならば h は空でない (約定 0 ≠ 1)。 -/
theorem nonempty_of_cprw_eq_one {p h : Set V} (H : cprw wt p h = 1) : h.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  simp [cprw, cmu_empty] at H

include hs in
/-- **Def. IX** (folio 135)。 -/
theorem cmodel_def_IX_i (p q h : Set V) :
    cprw wt (p ∩ qᶜ) h + cprw wt (p ∩ q) h = cprw wt p h := by
  unfold cprw
  rw [← add_div]
  congr 1
  have e1 : p ∩ qᶜ ∩ h = qᶜ ∩ (p ∩ h) := by ext; simp only [Set.mem_inter_iff, Set.mem_compl_iff]; tauto
  have e2 : p ∩ q ∩ h = q ∩ (p ∩ h) := by ext; simp only [Set.mem_inter_iff]; tauto
  rw [e1, e2, cmu_split hs q (p ∩ h)]
  ring

include hw hs in
/-- **Def. X 左形** (folio 135)。 -/
theorem cmodel_def_X_left_i (p q h : Set V) :
    cprw wt (p ∩ q) h = cprw wt p (q ∩ h) * cprw wt q h := by
  unfold cprw
  by_cases hz : q ∩ h = ∅
  · have hz' : p ∩ q ∩ h = ∅ := by rw [Set.inter_assoc, hz, Set.inter_empty]
    rw [hz', hz, Set.inter_empty, cmu_empty]
    simp
  · have hqh : 0 < cmu wt (q ∩ h) := cmu_pos hw hs (Set.nonempty_iff_ne_empty.mpr hz)
    have hh : 0 < cmu wt h := lt_of_lt_of_le hqh (cmu_mono hw hs Set.inter_subset_right)
    rw [Set.inter_assoc]
    field_simp

include hw hs in
/-- **Def. X 右形** (folio 135)。 -/
theorem cmodel_def_X_right_i (p q h : Set V) :
    cprw wt (p ∩ q) h = cprw wt q (p ∩ h) * cprw wt p h := by
  rw [Set.inter_comm p q]
  exact cmodel_def_X_left_i hw hs q p h

include hw in
/-- **値域 (下)**。 -/
theorem cmodel_ax_range_lo_i (p h : Set V) : 0 ≤ cprw wt p h :=
  div_nonneg (cmu_nonneg hw _) (cmu_nonneg hw _)

include hw hs in
/-- **値域 (上)**。 -/
theorem cmodel_ax_range_hi_i (p h : Set V) : cprw wt p h ≤ 1 := by
  rcases Set.eq_empty_or_nonempty h with hh | hh
  · subst hh; simp [cprw, cmu_empty]
  · rw [cprw, div_le_one (cmu_pos hw hs hh)]
    exact cmu_mono hw hs Set.inter_subset_right

include hw hs in
/-- **Def. VIII 双条件読み、但し書き付き** (folio 134)。 -/
theorem cmodel_def_VIII_i (a b h : Set V) (hca : (a ∩ h).Nonempty) (hcb : (b ∩ h).Nonempty) :
    cprw wt ((a ∩ b) ∪ (aᶜ ∩ bᶜ)) h = 1 ↔ (cprw wt b (a ∩ h) = 1 ∧ cprw wt a (b ∩ h) = 1) := by
  have hh : h.Nonempty := hca.mono Set.inter_subset_right
  rw [cprw_eq_one_iff hw hs hh, cprw_eq_one_iff hw hs hca, cprw_eq_one_iff hw hs hcb]
  exact csubset_miff_iff a b h

include hw hs in
/-- **Def. VIII 印刷どおり** (folio 134、→ のみ)。 -/
theorem cmodel_def_VIII_i_src (a b h : Set V) :
    cprw wt b (a ∩ h) = 1 → cprw wt a (b ∩ h) = 1 → cprw wt ((a ∩ b) ∪ (aᶜ ∩ bᶜ)) h = 1 := by
  intro H1 H2
  have hca := nonempty_of_cprw_eq_one H1
  have hcb := nonempty_of_cprw_eq_one H2
  have hh : h.Nonempty := hca.mono Set.inter_subset_right
  rw [cprw_eq_one_iff hw hs hca] at H1
  rw [cprw_eq_one_iff hw hs hcb] at H2
  rw [cprw_eq_one_iff hw hs hh]
  exact (csubset_miff_iff a b h).mpr ⟨H1, H2⟩

include hw hs in
/-- **cons_of_pos_src** (Def. VI 印刷の向きの対偶、folio 134)。 -/
theorem cmodel_cons_of_pos_src (a h : Set V) : (a ∩ h).Nonempty → cprw wt a h ≠ 0 := by
  intro hca
  have hh : h.Nonempty := hca.mono Set.inter_subset_right
  exact (div_pos (cmu_pos hw hs hca) (cmu_pos hw hs hh)).ne'

/-- **cons_of_pos** (Def. VI の逆向き、(10) folio 140)。 -/
theorem cmodel_cons_of_pos (a h : Set V) : cprw wt a h ≠ 0 → h.Nonempty → (a ∩ h).Nonempty := by
  intro hne _
  by_contra hz
  rw [Set.not_nonempty_iff_eq_empty] at hz
  apply hne
  rw [cprw, hz, cmu_empty, zero_div]

/-- 重み wt の可算模型の結合子の組。 -/
noncomputable abbrev cOps (wt : V → ℝ) : Ops where
  IProp := Set V
  iand := fun p q => p ∩ q
  ior := fun p q => p ∪ q
  inot := fun p => pᶜ
  iiff := fun p q => (p ∩ q) ∪ (pᶜ ∩ qᶜ)
  itrue := Set.univ
  PrI := cprw wt
  Cons := Set.Nonempty

theorem cOps_interp (wt : V → ℝ) (env : ℕ → Set V) (f : Form) :
    (cOps wt).interp env f = cInterp env f := by
  induction f with
  | var n => rfl
  | tru => rfl
  | fls => rfl
  | conj f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl
  | disj f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl
  | neg f ihf => simp only [Ops.interp]; rw [ihf]; rfl
  | iffF f g ihf ihg => simp only [Ops.interp]; rw [ihf, ihg]; rfl

include hw hs in
/-- **正の重み・有限の総和の可算模型は第 II 部の公理群 13 本をすべて満たす**。 -/
theorem cSys [Nonempty V] : Sys (cOps wt) where
  def_IX_i := cmodel_def_IX_i hs
  def_X_left_i := cmodel_def_X_left_i hw hs
  def_X_right_i := cmodel_def_X_right_i hw hs
  def_XI_i := fun _ _ _ hQ H => (eq_div_iff hQ).mpr H
  ax_range_lo_i := cmodel_ax_range_lo_i hw
  ax_range_hi_i := cmodel_ax_range_hi_i hw hs
  def_VIII_i := cmodel_def_VIII_i hw hs
  def_VIII_i_src := cmodel_def_VIII_i_src hw hs
  ax_iii_taut := fun f env h hc ht => by
    show cprw wt ((cOps wt).interp env f) h = 1
    rw [cOps_interp, cprw_eq_one_iff hw hs hc]
    intro v _
    rw [mem_cInterp]
    exact ht _
  cons_true := Set.univ_nonempty
  cons_of_pos_src := cmodel_cons_of_pos_src hw hs
  cons_of_pos := cmodel_cons_of_pos
  cons_iff_taut := fun f g env ht => by
    show ((cOps wt).interp env f).Nonempty ↔ ((cOps wt).interp env g).Nonempty
    rw [cOps_interp, cOps_interp]
    have e : cInterp env f = cInterp env g := by
      ext v
      rw [mem_cInterp, mem_cInterp]
      have H := ht (valOf env v)
      simp only [evalB, beq_iff_eq] at H
      rw [H]
    rw [e]

end Count

/-! ### Pólya の壺の重み: 最初に起こらない回の分布 -/

/-- π_k = Π_{i<k} (r + i)/(s + i) (k 回続けて起こる確率、074 の右辺)。 -/
noncomputable def piR (r s k : ℕ) : ℝ := ∏ i ∈ Finset.range k, ((r : ℝ) + i) / ((s : ℝ) + i)

theorem piR_succ (r s k : ℕ) : piR r s (k + 1) = piR r s k * (((r : ℝ) + k) / ((s : ℝ) + k)) :=
  Finset.prod_range_succ _ _

theorem piR_pos (r s : ℕ) (hr : 0 < r) (hrs : r < s) : ∀ k, 0 < piR r s k := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast (lt_trans hr hrs)
  intro k
  induction k with
  | zero => simp [piR]
  | succ k ih =>
      rw [piR_succ]
      positivity

/-- r < s なら π_k ≤ r/(r + k)。 -/
theorem piR_le (r s : ℕ) (hr : 0 < r) (hrs : r < s) : ∀ k, piR r s k ≤ (r : ℝ) / ((r : ℝ) + k) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrs' : (r : ℝ) + 1 ≤ s := by exact_mod_cast hrs
  intro k
  induction k with
  | zero => simp [piR, hr'.ne']
  | succ k ih =>
      rw [piR_succ]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      calc piR r s k * (((r : ℝ) + k) / ((s : ℝ) + k))
          ≤ (r : ℝ) / ((r : ℝ) + k) * (((r : ℝ) + k) / ((s : ℝ) + k)) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = (r : ℝ) / ((s : ℝ) + k) := by field_simp
        _ ≤ (r : ℝ) / ((r : ℝ) + ((k + 1 : ℕ) : ℝ)) := by
            apply div_le_div_of_nonneg_left hr'.le (by positivity)
            push_cast; linarith

/-- r < s なら π_k → 0 (すべての回に起こる確率は 0)。 -/
theorem piR_tendsto (r s : ℕ) (hr : 0 < r) (hrs : r < s) : Tendsto (piR r s) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (r : ℝ) / ((r : ℝ) + k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun k => (piR_pos r s hr hrs k).le) (piR_le r s hr hrs)

/-- 最初に起こらないのが j + 1 回目である確率 π_j − π_{j+1}。 -/
noncomputable def pw (r s j : ℕ) : ℝ := piR r s j - piR r s (j + 1)

theorem pw_pos (r s : ℕ) (hr : 0 < r) (hrs : r < s) (j : ℕ) : 0 < pw r s j := by
  have hp := piR_pos r s hr hrs j
  have hrs' : (r : ℝ) < s := by exact_mod_cast hrs
  have hs' : (0 : ℝ) < s := by exact_mod_cast (lt_trans hr hrs)
  have hq : ((r : ℝ) + j) / ((s : ℝ) + j) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have := mul_lt_mul_of_pos_left hq hp
  rw [pw, piR_succ]
  linarith

theorem pw_tail_sum (r s k : ℕ) : ∀ n,
    ∑ j ∈ Finset.range (k + n), (if k ≤ j then pw r s j else 0) = piR r s k - piR r s (k + n) := by
  intro n
  induction n with
  | zero =>
      rw [Finset.sum_eq_zero (fun j hj => if_neg (by simp at hj; omega))]
      simp
  | succ n ih =>
      rw [show k + (n + 1) = (k + n) + 1 from rfl, Finset.sum_range_succ, ih, if_pos (by omega)]
      unfold pw; ring

/-- 尾の和: Σ_{j ≥ k} (π_j − π_{j+1}) = π_k (r < s)。 -/
theorem pw_tail_hasSum (r s : ℕ) (hr : 0 < r) (hrs : r < s) (k : ℕ) :
    HasSum (fun j => if k ≤ j then pw r s j else 0) (piR r s k) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by
    split_ifs
    · exact (pw_pos r s hr hrs j).le
    · exact le_refl 0)]
  have h := (tendsto_const_nhds (x := piR r s k)).sub (piR_tendsto r s hr hrs)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  exact (pw_tail_sum r s k m).symm

/-! ### 模型 MS: 世界 (ℕ × ℕ) × ℕ、data (r, s) ごとに Pólya の壺の系列 -/

/-- 世界: ((r, s), j)。 -/
abbrev WS := (ℕ × ℕ) × ℕ

/-- data (r, s) の重み (0 < r < s 以外は (1, 2) の重みを借りる)。 -/
noncomputable def pwF (r s j : ℕ) : ℝ := if 0 < r ∧ r < s then pw r s j else pw 1 2 j

theorem pwF_pos (r s j : ℕ) : 0 < pwF r s j := by
  unfold pwF; split_ifs with h
  · exact pw_pos r s h.1 h.2 j
  · exact pw_pos 1 2 (by norm_num) (by norm_num) j

theorem pwF_hasSum (r s : ℕ) : HasSum (pwF r s) 1 := by
  have e : ∀ r s : ℕ, 0 < r → r < s → HasSum (pw r s) 1 := fun r s hr hrs => by
    have h := pw_tail_hasSum r s hr hrs 0
    simp only [Nat.zero_le, if_true] at h
    simpa [piR] using h
  unfold pwF; split_ifs with h
  · exact e r s h.1 h.2
  · exact e 1 2 (by norm_num) (by norm_num)

/-- 世界の重み (½)^r (½)^s · pwF r s j。 -/
noncomputable def wtS (w : WS) : ℝ := (1 / 2 : ℝ) ^ w.1.1 * (1 / 2 : ℝ) ^ w.1.2 * pwF w.1.1 w.1.2 w.2

theorem wtS_pos (w : WS) : 0 < wtS w := by
  unfold wtS; have := pwF_pos w.1.1 w.1.2 w.2; positivity

theorem wtS_summable : Summable wtS := by
  have hnn : 0 ≤ wtS := fun w => (wtS_pos w).le
  refine (summable_prod_of_nonneg hnn).mpr ⟨fun x => ?_, ?_⟩
  · exact ((pwF_hasSum x.1 x.2).mul_left ((1 / 2 : ℝ) ^ x.1 * (1 / 2 : ℝ) ^ x.2)).summable
  · have e : (fun x : ℕ × ℕ => ∑' y, wtS (x, y)) = fun x => (1 / 2 : ℝ) ^ x.1 * (1 / 2 : ℝ) ^ x.2 := by
      funext x
      have := (pwF_hasSum x.1 x.2).mul_left ((1 / 2 : ℝ) ^ x.1 * (1 / 2 : ℝ) ^ x.2)
      rw [mul_one] at this
      exact this.tsum_eq
    rw [e]
    exact summable_geometric_two.mul_of_nonneg summable_geometric_two
      (fun n => by positivity) (fun n => by positivity)

/-- 模型 MS (重み wtS の可算模型)。 -/
noncomputable abbrev MS : Ops := cOps wtS

/-- MS は第 II 部の公理群 13 本を満たす。 -/
theorem sys_MS : Sys MS := cSys wtS_pos wtS_summable

/-- data h_{r,s} := {((r, s), j)}。 -/
def hM (r s : ℕ) : Set WS := {w | w.1 = (r, s)}

/-- a_k := {((r, s), j) | k ≤ j} (最初の j 回が起こる世界で、k 回目に起こる)。 -/
def tM (r s k : ℕ) : Set WS := {w | w.1 = (r, s) ∧ k ≤ w.2}

/-- y_k ∧ h_{r,s} = {((r, s), j) | k ≤ j}。 -/
theorem y_tM (r s : ℕ) : ∀ k, MS.y (tM r s) k ∩ hM r s = tM r s k := by
  intro k
  induction k with
  | zero =>
      show Set.univ ∩ hM r s = tM r s 0
      ext w; simp [hM, tM]
  | succ k ih =>
      show (tM r s (k + 1) ∩ MS.y (tM r s) k) ∩ hM r s = tM r s (k + 1)
      rw [Set.inter_assoc, ih]
      ext w
      simp only [tM, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, _⟩; exact h1
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1, by omega⟩

theorem tM_inter (r s k : ℕ) : tM r s (k + 1) ∩ tM r s k = tM r s (k + 1) := by
  ext w
  simp only [tM, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, _⟩; exact h1
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1, by omega⟩

theorem tM_zero (r s : ℕ) : tM r s 0 = hM r s := by
  ext w; simp [hM, tM]

/-- tM r s k の重みは (½)^r (½)^s π_k (0 < r < s)。 -/
theorem cmu_tM (r s : ℕ) (hr : 0 < r) (hrs : r < s) (k : ℕ) :
    cmu wtS (tM r s k) = (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ s * piR r s k := by
  unfold cmu
  have hinj : Function.Injective (fun j : ℕ => (((r, s), j) : WS)) := fun a b h => by
    simpa using h
  have hsupp : Function.support ((tM r s k).indicator wtS) ⊆ Set.range (fun j : ℕ => (((r, s), j) : WS)) := by
    intro w hw
    have hm : w ∈ tM r s k := Set.mem_of_indicator_ne_zero hw
    exact ⟨w.2, Prod.ext hm.1.symm rfl⟩
  rw [← hinj.tsum_eq hsupp]
  have e : (fun j : ℕ => (tM r s k).indicator wtS ((r, s), j))
      = fun j => (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ s * (if k ≤ j then pw r s j else 0) := by
    funext j
    by_cases hkj : k ≤ j
    · rw [Set.indicator_of_mem (show (((r, s), j) : WS) ∈ tM r s k from ⟨rfl, hkj⟩), if_pos hkj]
      simp [wtS, pwF, hr, hrs]
    · rw [Set.indicator_of_notMem (show (((r, s), j) : WS) ∉ tM r s k from fun h => hkj h.2), if_neg hkj,
        mul_zero]
  rw [e]
  exact ((pw_tail_hasSum r s hr hrs k).mul_left _).tsum_eq

/-- **継起の仮定は模型 MS で成り立つ**: 0 < r < s なら h_{r,s}・a_k := tM r s k は SuccRule を満たす。 -/
theorem succRule_MS (r s : ℕ) (hr : 0 < r) (hrs : r < s) : MS.SuccRule (tM r s) (hM r s) r s := by
  intro k _
  show cprw wtS (tM r s (k + 1)) (MS.y (tM r s) k ∩ hM r s) = _
  rw [y_tM, cprw, tM_inter, cmu_tM r s hr hrs, cmu_tM r s hr hrs, piR_succ]
  have hp := piR_pos r s hr hrs k
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ s := by positivity
  field_simp

theorem cons_hM (r s : ℕ) : MS.Cons (hM r s) := ⟨((r, s), 0), rfl⟩

/-- **外部公理の無矛盾性 (模型)**: 第 II 部の公理群 13 本を満たす模型 MS に、ax_data_consP・
ax_poisson_independence (aP := ⊤、hP := ⊤) と ax_data_consS・ax_succession_rule (aS r s := tM r s、
hS r s := hM r s) をすべて同時に満たす読みがある。ax_poisson_approx はキャリアを含まない実解析の文で、
この定理の対象外。 -/
theorem model_external :
    Sys MS ∧
    (MS.Cons Set.univ ∧ MS.PoissonIndep (fun _ => Set.univ) Set.univ) ∧
    (∀ r s, MS.Cons (hM r s)) ∧
    (∀ r s, 0 < r → r < s → MS.SuccRule (tM r s) (hM r s) r s) := by
  refine ⟨sys_MS, ⟨Set.univ_nonempty, fun m n hc => ?_⟩, cons_hM, succRule_MS⟩
  have h1 : cprw wtS Set.univ (MS.x (fun _ => Set.univ) m n ∩ Set.univ) = 1 :=
    (cprw_eq_one_iff wtS_pos wtS_summable hc).mpr (Set.subset_univ _)
  have h2 : cprw wtS Set.univ Set.univ = 1 :=
    (cprw_eq_one_iff wtS_pos wtS_summable Set.univ_nonempty).mpr (Set.subset_univ _)
  show cprw wtS Set.univ (MS.x (fun _ => Set.univ) m n ∩ Set.univ) = cprw wtS Set.univ Set.univ
  rw [h1, h2]

/-! ### 反例: 外部公理は第 II 部の公理群から導けない -/

theorem piR_12 : piR 1 2 1 = 1 / 2 ∧ piR 1 2 2 = 1 / 3 := by
  refine ⟨?_, ?_⟩ <;> norm_num [piR, Finset.prod_range_succ]

/-- **ax_poisson_independence は第 II 部の公理群から導けない**: 公理群 13 本を満たす模型 MS と整合な
h := h_{1,2} について、Pólya の壺の系列 a_k := tM 1 2 k (継起の仮定を満たす系列) では m = n = 1 で
a_2/_1x_1 h = 2/3 ≠ 1/3 = a_2/h。 -/
theorem nec_poisson_model : Sys MS ∧ MS.Cons (hM 1 2) ∧ ¬ MS.PoissonIndep (tM 1 2) (hM 1 2) := by
  refine ⟨sys_MS, cons_hM 1 2, fun H => ?_⟩
  have hx : MS.x (tM 1 2) 1 1 ∩ hM 1 2 = tM 1 2 1 := by
    have : MS.x (tM 1 2) 1 1 = MS.y (tM 1 2) 1 := rfl
    rw [this, y_tM]
  have hc : MS.Cons (MS.iand (MS.x (tM 1 2) 1 1) (hM 1 2)) := by
    show (MS.x (tM 1 2) 1 1 ∩ hM 1 2).Nonempty
    rw [hx]; exact ⟨((1, 2), 1), rfl, le_rfl⟩
  have H1 := H 1 1 hc
  change cprw wtS (tM 1 2 2) (MS.x (tM 1 2) 1 1 ∩ hM 1 2) = cprw wtS (tM 1 2 2) (hM 1 2) at H1
  rw [hx, cprw, cprw, tM_inter, ← tM_zero, show tM 1 2 2 ∩ tM 1 2 0 = tM 1 2 2 by
      ext w; simp only [tM, Set.mem_inter_iff, Set.mem_setOf_eq]; constructor
      · rintro ⟨h1, _⟩; exact h1
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1, by omega⟩,
    cmu_tM 1 2 (by norm_num) (by norm_num), cmu_tM 1 2 (by norm_num) (by norm_num),
    cmu_tM 1 2 (by norm_num) (by norm_num), piR_12.1, piR_12.2,
    show piR 1 2 0 = 1 by simp [piR]] at H1
  norm_num at H1

/-- **ax_succession_rule は第 II 部の公理群から導けない**: 同じ模型 MS と整合な h := h_{1,2} について、
a_k := tM 1 2 1 (すべての k で同じ命題: 1 回目に起これば以後も確実に起こる) では y_1/h = 1/2 = r/s
(r = 1、s = 2) だが a_2/y_1 h = 1 ≠ 2/3 = (r + 1)/(s + 1)。 -/
theorem nec_succession_model :
    Sys MS ∧ MS.Cons (hM 1 2) ∧ MS.PrI (MS.y (fun _ => tM 1 2 1) 1) (hM 1 2) = (1 : ℝ) / 2 ∧
      ¬ MS.SuccRule (fun _ => tM 1 2 1) (hM 1 2) 1 2 := by
  have hy : MS.y (fun _ => tM 1 2 1) 1 ∩ hM 1 2 = tM 1 2 1 := by
    show (tM 1 2 1 ∩ Set.univ) ∩ hM 1 2 = tM 1 2 1
    rw [Set.inter_univ, Set.inter_eq_left]
    exact fun w hw => hw.1
  refine ⟨sys_MS, cons_hM 1 2, ?_, fun H => ?_⟩
  · show cprw wtS (MS.y (fun _ => tM 1 2 1) 1) (hM 1 2) = 1 / 2
    rw [cprw, hy, ← tM_zero, cmu_tM 1 2 (by norm_num) (by norm_num),
      cmu_tM 1 2 (by norm_num) (by norm_num), piR_12.1, show piR 1 2 0 = 1 by simp [piR]]
    norm_num
  · have hc : MS.Cons (MS.iand (MS.y (fun _ => tM 1 2 1) 1) (hM 1 2)) := by
      show (MS.y (fun _ => tM 1 2 1) 1 ∩ hM 1 2).Nonempty
      rw [hy]; exact ⟨((1, 2), 1), rfl, le_rfl⟩
    have H1 := H 1 hc
    change cprw wtS (tM 1 2 1) (MS.y (fun _ => tM 1 2 1) 1 ∩ hM 1 2) = _ at H1
    rw [hy, cprw, Set.inter_self, div_self (cmu_pos wtS_pos wtS_summable (p := tM 1 2 1) ⟨((1, 2), 1), rfl, le_rfl⟩).ne']
      at H1
    norm_num at H1

/-- **系**: 第 II 部の公理群 13 本を満たすすべての場、すべての整合な h とすべての系列 a で
PoissonIndep が成り立つ、ということはない。 -/
theorem not_derivable_poisson :
    ¬ ∀ S : Ops, Sys S → ∀ (a : ℕ → S.IProp) (h : S.IProp), S.Cons h → S.PoissonIndep a h :=
  fun H => nec_poisson_model.2.2 (H MS sys_MS (tM 1 2) (hM 1 2) (cons_hM 1 2))

/-- **系**: 同じく、0 < r < s と整合な h のもとで SuccRule が成り立つ、ということはない。 -/
theorem not_derivable_succession :
    ¬ ∀ S : Ops, Sys S → ∀ (a : ℕ → S.IProp) (h : S.IProp) (r s : ℕ), 0 < r → r < s →
      S.Cons h → S.SuccRule a h r s :=
  fun H => nec_succession_model.2.2.2
    (H MS sys_MS (fun _ => tM 1 2 1) (hM 1 2) 1 2 (by norm_num) (by norm_num) (cons_hM 1 2))

end KeynesXXIXc_model

/-! ## #print axioms -/
#print axioms KeynesXXIXc.itrue_certain
#print axioms KeynesXXIXc.true_conj
#print axioms KeynesXXIXc.th_13_1_i
#print axioms KeynesXXIXc.taut_neg_zero
#print axioms KeynesXXIXc.conj_neg_cert_zero
#print axioms KeynesXXIXc.th_12_i_short
#print axioms KeynesXXIXc.subst_taut
#print axioms KeynesXXIXc.y
#print axioms KeynesXXIXc.x
#print axioms KeynesXXIXc.pr_false
#print axioms KeynesXXIXc.pr_mul_of_irr
#print axioms KeynesXXIXc.pr_mul_not_of_irr
#print axioms KeynesXXIXc.pr_or_excl
#print axioms KeynesXXIXc.q
#print axioms KeynesXXIXc.trials
#print axioms KeynesXXIXc.pmean
#print axioms KeynesXXIXc.kP
#print axioms KeynesXXIXc.pbin
#print axioms KeynesXXIXc.probWithinP
#print axioms KeynesXXIXc.Θ
#print axioms KeynesXXIXc.poissonP
#print axioms KeynesXXIXc.PoissonIndep
#print axioms KeynesXXIXc.pp
#print axioms KeynesXXIXc.pbin_zero_of_lt
#print axioms KeynesXXIXc.th_poisson_dist
#print axioms KeynesXXIXc.probWithinI
#print axioms KeynesXXIXc.th_29_057
#print axioms KeynesXXIXc.cont_poisson_exp
#print axioms KeynesXXIXc.th_29_060
#print axioms KeynesXXIXc.th_29_063_eq
#print axioms KeynesXXIXc.th_29_062
#print axioms KeynesXXIXc.pbin_sum_succ
#print axioms KeynesXXIXc.psum
#print axioms KeynesXXIXc.pqsum
#print axioms KeynesXXIXc.psum_succ
#print axioms KeynesXXIXc.pqsum_succ
#print axioms KeynesXXIXc.pbin_moments
#print axioms KeynesXXIXc.th_29_059
#print axioms KeynesXXIXc.pbin_nonneg
#print axioms KeynesXXIXc.s_pmean
#print axioms KeynesXXIXc.th_29_poisson_cheb
#print axioms KeynesXXIXc.pqsum_ge
#print axioms KeynesXXIXc.kP_mul_sqrt
#print axioms KeynesXXIXc.poisson_corr_vanish
#print axioms KeynesXXIXc.kP_pos
#print axioms KeynesXXIXc.th_29_063
#print axioms KeynesXXIXc.th_29_058
#print axioms KeynesXXIXc.hyp
#print axioms KeynesXXIXc.th_29_065
#print axioms KeynesXXIXc.th_29_065_ratio
#print axioms KeynesXXIXc.th_29_067
#print axioms KeynesXXIXc.pairs
#print axioms KeynesXXIXc.black
#print axioms KeynesXXIXc.pairs_cards
#print axioms KeynesXXIXc.th_29_068
#print axioms KeynesXXIXc.pR
#print axioms KeynesXXIXc.bernP
#print axioms KeynesXXIXc.th_29_072
#print axioms KeynesXXIXc.th_29_079
#print axioms KeynesXXIXc.SuccRule
#print axioms KeynesXXIXc.th_29_074_of
#print axioms KeynesXXIXc.th_29_074
#print axioms KeynesXXIXc.th_29_070_data
#print axioms KeynesXXIXc.th_29_073
#print axioms KeynesXXIXc.th_29_075
#print axioms KeynesXXIXc.th_29_075_data
#print axioms KeynesXXIXc.beta_nat
#print axioms KeynesXXIXc.beta_fact
#print axioms KeynesXXIXc.beta_step
#print axioms KeynesXXIXc.th_29_075_beta
#print axioms KeynesXXIXc.th_29_073_beta
#print axioms KeynesXXIXc.th_29_laplace_uniform
#print axioms KeynesXXIXc.st076
#print axioms KeynesXXIXc.th_29_077
#print axioms KeynesXXIXc.Q078
#print axioms KeynesXXIXc.th_29_078
#print axioms KeynesXXIXc.gSt
#print axioms KeynesXXIXc.stirling_g
#print axioms KeynesXXIXc.st076_g
#print axioms KeynesXXIXc.fr075
#print axioms KeynesXXIXc.th_29_076
#print axioms KeynesXXIXc.th_29_080_gt
#print axioms KeynesXXIXc.th_29_080_num
#print axioms KeynesXXIXc.th_29_080_lim
#print axioms KeynesXXIXc.th_29_082
-- 外部公理の相対無矛盾性 (キャリアの上の自明な代入)
#print axioms KeynesXXIXc.rel_cons_poisson_trivial
-- 模型: 第 II 部の公理群 13 本を満たす可算模型、外部公理の無矛盾性と導けないこと
#print axioms KeynesXXIXc_model.Ops
#print axioms KeynesXXIXc_model.Ops.interp
#print axioms KeynesXXIXc_model.Sys
#print axioms KeynesXXIXc_model.Ops.x
#print axioms KeynesXXIXc_model.Ops.y
#print axioms KeynesXXIXc_model.Ops.PoissonIndep
#print axioms KeynesXXIXc_model.Ops.SuccRule
#print axioms KeynesXXIXc_model.cmu
#print axioms KeynesXXIXc_model.cprw
#print axioms KeynesXXIXc_model.cInterp
#print axioms KeynesXXIXc_model.valOf
#print axioms KeynesXXIXc_model.mem_cInterp
#print axioms KeynesXXIXc_model.csubset_miff_iff
#print axioms KeynesXXIXc_model.cmu_empty
#print axioms KeynesXXIXc_model.cmu_nonneg
#print axioms KeynesXXIXc_model.cmu_split
#print axioms KeynesXXIXc_model.cmu_pos
#print axioms KeynesXXIXc_model.cmu_eq_zero_iff
#print axioms KeynesXXIXc_model.cmu_mono
#print axioms KeynesXXIXc_model.cprw_eq_one_iff
#print axioms KeynesXXIXc_model.nonempty_of_cprw_eq_one
#print axioms KeynesXXIXc_model.cmodel_def_IX_i
#print axioms KeynesXXIXc_model.cmodel_def_X_left_i
#print axioms KeynesXXIXc_model.cmodel_def_X_right_i
#print axioms KeynesXXIXc_model.cmodel_ax_range_lo_i
#print axioms KeynesXXIXc_model.cmodel_ax_range_hi_i
#print axioms KeynesXXIXc_model.cmodel_def_VIII_i
#print axioms KeynesXXIXc_model.cmodel_def_VIII_i_src
#print axioms KeynesXXIXc_model.cmodel_cons_of_pos_src
#print axioms KeynesXXIXc_model.cmodel_cons_of_pos
#print axioms KeynesXXIXc_model.cOps
#print axioms KeynesXXIXc_model.cOps_interp
#print axioms KeynesXXIXc_model.cSys
#print axioms KeynesXXIXc_model.piR
#print axioms KeynesXXIXc_model.piR_succ
#print axioms KeynesXXIXc_model.piR_pos
#print axioms KeynesXXIXc_model.piR_le
#print axioms KeynesXXIXc_model.piR_tendsto
#print axioms KeynesXXIXc_model.pw
#print axioms KeynesXXIXc_model.pw_pos
#print axioms KeynesXXIXc_model.pw_tail_sum
#print axioms KeynesXXIXc_model.pw_tail_hasSum
#print axioms KeynesXXIXc_model.pwF
#print axioms KeynesXXIXc_model.pwF_pos
#print axioms KeynesXXIXc_model.pwF_hasSum
#print axioms KeynesXXIXc_model.wtS
#print axioms KeynesXXIXc_model.wtS_pos
#print axioms KeynesXXIXc_model.wtS_summable
#print axioms KeynesXXIXc_model.sys_MS
#print axioms KeynesXXIXc_model.hM
#print axioms KeynesXXIXc_model.tM
#print axioms KeynesXXIXc_model.y_tM
#print axioms KeynesXXIXc_model.tM_inter
#print axioms KeynesXXIXc_model.tM_zero
#print axioms KeynesXXIXc_model.cmu_tM
#print axioms KeynesXXIXc_model.succRule_MS
#print axioms KeynesXXIXc_model.cons_hM
#print axioms KeynesXXIXc_model.model_external
#print axioms KeynesXXIXc_model.piR_12
#print axioms KeynesXXIXc_model.nec_poisson_model
#print axioms KeynesXXIXc_model.nec_succession_model
#print axioms KeynesXXIXc_model.not_derivable_poisson
#print axioms KeynesXXIXc_model.not_derivable_succession
