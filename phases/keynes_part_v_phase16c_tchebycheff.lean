/-
# Keynes (1921) *A Treatise on Probability* Part V — Lean 4 Phase 16c
# 第 XXIX 章 §11 末–§16 (folio 351–360): φ(p, q) の漸化式、Czuber の出生数の例、Tchebycheff の定理、
#   Bernoulli・Poisson の定理の Tchebycheff 形、Tchebycheff (1846) の補足の結果、Simmons の表 (台帳 ch29-084〜190)
#
# 分担: phase14b (B38) は 001〜040、phase14a (B36) は 041〜054、phase16b (B48) は 055〜083、本ファイル (B49) は 084〜190。
#
# ## Keynes の確率関係が現れない節
#   §12–§16 の式 (台帳 089〜190) は Keynes の確率関係 (a/h) を含まない。Tchebycheff の定理 (§13) は値と確率の重み付き和の
#   代数であり、Bernoulli・Poisson の定理の Tchebycheff 形 (§14) はその当てはめ、§12・§16 は数値の例である。そこで
#   第 II 部のキャリアではなく、有限和 (Finset) と実数の上で述べる (B38 の phase14b と同じ扱い)。量 x, y, z . . . の値の組
#   κ = (x_κ, y_λ, z_μ, . . .) の確率は独立の積 p_κ q_λ r_μ . . . (印刷の「provided that the values of x, y, z . . . are
#   independent」) を定義として置く (jp)。キャリア (IProp, PrI, Cons) を用いるのは §11 の 086 だけである。
#
# ## 基準
#   1921 年 Macmillan 初版の頁画像のみ (folio 351–360)。定理名は th_29_<行番号>、反例は nec_29_<行番号>、
#   修正形は th_29_<行番号>_fix。台帳の行 ID は各定理の docstring に書く。
#
# ## 原典
#   (folio 351、§11) 「If an event has occurred x times in the first y trials, its probability at the y + 1th is
#    (r + x)/(s + y); determine the à priori probability of the event's occurring p times in q trials. If the à priori
#    probability in question is represented by φ(p, q), we have
#      φ(p, q) = (r+p−1)/(s+q−1) φ(p−1, q−1) + (s+q−1−r−p)/(s+q−1) φ(p, q−1).
#    I know of no solution of this, even approximate.」
#   (folio 351–352、§12) 「In the period 1866–1877 there were registered in Austria m = 4,311,076 male births,
#    n = 4,052,193 female births, s = 8,363,269; for the succeeding period, 1877–1899, we are given only
#    m′ = 6,533,961 male births; … the most probable value n_0′ = nm′/m = 6,141,587, and that there is a probability
#    P = ·9999779 that n′ will lie between the limits 6,118,361 and 6,164,813. … (P = ·9999779 = 1 − 1/45250)」
#   (folio 353–355、§13) 「Let x, y, z . . . represent certain magnitudes, of which x can take the values x_1x_2 . . . x_k
#    with probabilities p_1p_2 . . . p_k … so that Σp = 1, Σq = 1, Σr = 1, etc. Write Σp_κx_κ = a, … and
#    Σp_κx_κ² = a_1, … The probability that the sum x + y + z + . . . will have for its value x_κ + y_λ + z_μ + . . . is
#    p_κq_λr_μ . . . (provided that the values of x, y, z . . . are independent). … whence
#      Σ(x_κ + y_λ + z_μ + . . . − a − b − c . . .)²p_κq_λr_μ . . . / (a²(a_1 + b_1 + c_1 + . . . − a² − b² − c² − . . .)) = 1/a²,
#    where … a is some arbitrary number greater than unity. If we omit those terms … for which (…)²/(a²(…)) < 1,
#    and write unity for this expression in the remaining terms, both these processes diminish the magnitude of the
#    left-hand side. Hence Σp_κq_λr_μ . . . < 1/a², where the summation covers those sets of values only for which
#    (…)²/(a²(…)) ≥ 1. If P is the probability that (…)²/(a²(…)) is equal to or less than unity, it follows that
#    1 − P < 1/a², i.e. P > 1 − 1/a².」
#    「Let n be the number of the magnitudes x, y, z . . ., and write a = √n/t; then the probability that the arithmetic
#    mean (x_κ + y_λ + z_μ + . . .)/n lies between the limits … is greater than 1 − t²/n. … if an amount A is won when an
#    event of probability p[p = 1 − q] occurs and an amount B lost when it fails, then in s trials the probability that
#    the total winnings (or losses) will lie between the limits s(pA − qB) ± a(A + B)√(spq) is greater than 1 − 1/a².」
#   (folio 356、§14) 「… s magnitudes x_1x_2 . . . x_s corresponding, such that x = 1 when the event under consideration
#    occurs, and x = 0 when it fails. If the probability of the event's occurrence is p, we have a = p, b = p, etc., and
#    a_1 = p, b_1 = p, etc. Hence the probability P that the number of the event's occurrences will lie between the
#    limits sp ± a√(sp − sp²), i.e. between the limits sp ± a√(spq) where q = 1 − p, is > 1 − 1/a². … where this formula
#    gives P > 1 − 1/a², Bernoulli's Theorem with greater precision gives P = Θ(a/√2). … For we put a = p_1, b = p_2,
#    etc., and a_1 = p_1, b_1 = p_2, etc.,」
#   (folio 357) 「I. … the probability that E will occur at least m times is less than … provided that m > s + 1;
#    II. … the probability that E will not occur more than n times is less than … provided that n < s − 1.
#    III. … provided m > s + 1, n < s − 1.」
#   (folio 359–360、§16) 「If 1/(a + 1) is the probability of the event at each trial and n(a + 1) the number of trials,
#    … the difference between the two probabilities being a maximum when n = 1, constantly diminishing as n increases
#    … [p = 1/(a + 1), m = n(a + 1)] … in 100 sets of 4 trials each, where p = 1/4, the actual frequency is likely to
#    exceed the most probable 26 times and to fall short of it 31 times; and in 100 sets of 10 trials each, where
#    p = 1/10, to exceed 26 times and to fall short 34 times.」
#
# ## 記法の読み (定)
#   GenSucc a h r s : §11 の一般の問題の前提 (x 回起こった後の y + 1 回目の確率は (r + x)/(s + y); 084)。
#   aG・hG          : §11 の一般の問題の系列と data の名付け (外部公理、下記)。
#   φ a h p q       : φ(p, q) = _p x_q / h (085)。phiP : 漸化式の解 (Pólya の壺の分布、上昇階乗 rf)。
#   mB・nB・mB′     : m = 4,311,076、n = 4,052,193、m′ = 6,533,961 (089・090・092)。
#   Mag             : 量 (値 X と確率 P; 096〜101)。前提 Σp = 1 (102) は各定理の仮定 hN、p ≥ 0 は hP。
#   mean・mean2     : a = Σp_κx_κ (103)、a_1 = Σp_κx_κ² (104)。jp・Ssum : p_κq_λr_μ . . .、x_κ + y_λ + z_μ + . . . (107・108)。
#   Atot・Vt        : a + b + c + . . .、a_1 + b_1 + c_1 + . . . − a² − b² − c² − . . .
#   ratio・Pt       : 比 (…)²/(a²(…)) (120・122・123) と P (比 ≤ 1 の確率、123)。aT : a = √n/t (130)。
#   q・gainMag      : q = 1 − p (134・146)、勝ち A・負け B の量 (134)。indMag・bern・poi : x = 1/0 の量 (138・139)、
#                     Bernoulli (各回 p) と Poisson (λ 回目 p_λ) の族。
#   provI・provII   : 但し書き m > s + 1、n < s − 1 (164・166・169・170)。provI は nec_29_163、provII は
#                     th_29_165_cmp の前提に写す。tchI・tchII : I.・II. の印刷形 (163・165)。
#   pS・mS・deltaS  : p = 1/(a + 1) (186)、m = n(a + 1) (187)、Simmons の差 Δ。
#
# ## 外部公理 (第 II 部の公理でないもの)
#   ax_normal_approx : 積分形の de Moivre–Laplace 定理 (phase14b の同名の公理の再掲)。094・149 が依る。
#                      実解析の真な定理の言明で Mathlib に無い。Θ の数値 (094・095 の ·9999779 = Θ(3)、表の Θ(a/√2) の列) は
#                      erf の数表の値で、Lean では検算していない。
#   aG・hG・ax_data_consG : §11 の一般の問題の系列と data の名付け、data の整合性 (phase16b の aS・hS・ax_data_consS と
#                      同じ置き方)。
#   ax_gen_succ      : §11 の一般の問題の前提 GenSucc を data の上で名付けた公理 (0 < r < s)。086 (外) が依る
#                      (th_29_086_data)。GenSucc を定理の仮定に取った形 th_29_086 は補助で、第 II 部の公理だけで閉じる。
#                      第 II 部の公理群からは導けない: GenSucc の x = y の場合は phase16b の SuccRule の形 (gensucc_succ) で、
#                      phase16b の nec_succession_model が第 II 部の公理の文 13 本を満たす可算模型でその形を偽にする
#                      (phase は互いに import しないので参照のみ)。相対無矛盾性: 自明な代入 (r = s、a_λ := ⊤、h := ⊤) で
#                      GenSucc は第 II 部の公理だけから満たされる (rel_cons_gensucc_trivial)。0 < r < s の場合の模型
#                      (phase16b の MS の拡張) は作っていない (未検査)。
#
# ## 第 29 章の外部公理一覧 (phase14a・phase14b・phase16b・本ファイル; 名前・意味・依存する行)
#   ax_stirling_approx (phase14b)        : 局所 de Moivre–Laplace 定理。012 (外)。
#   ax_normal_approx (phase14b; 本ファイルに再掲) : 積分形 de Moivre–Laplace 定理。022・027・029 (外、phase14b)、
#                                          094・149 (外、本ファイル)。
#   a29・h29・ax_data_cons29 (phase14a)  : §6–§7 の系列と data の名付け、data の整合性。043・047・052・053 (外) が依る。
#   ax_bernoulli_independence (phase14a) : 043 (§6 の典型的条件)。043・047 (外)、048 の data 上の形。
#   ax_equal_chance (phase14a)           : 052 (§7 の (i.))。052 (外)。
#   ax_independence_ii (phase14a)        : 053 (§7 の (ii.))。053 (外)。
#   aP・hP・ax_data_consP (phase16b)     : §8 の系列と data の名付け、data の整合性。057・058・063 が依る。
#   ax_poisson_independence (phase16b)   : Poisson の定理の「other inexplicit assumption」。058・063 (外)。
#   ax_poisson_approx (phase16b)         : Poisson 二項分布の積分形の正規近似。058・063 (外)。
#   aS・hS・ax_data_consS (phase16b)     : §11 の人工例の系列と data の名付け、data の整合性。073・074・075 が依る。
#   ax_succession_rule (phase16b)        : §11 の人工例の仮定 (r + k)/(s + k)。073・074・075 (外)。
#   aG・hG・ax_data_consG (本ファイル)   : §11 の一般の問題の系列と data の名付け、data の整合性。086 (外) が依る。
#   ax_gen_succ (本ファイル)             : §11 の一般の問題の前提 (r + x)/(s + y)。086 (外)。
#   本ファイルで新しく置いた外部公理は aG・hG・ax_data_consG・ax_gen_succ の 4 本 (ほかは ax_normal_approx の再掲)。
#
# ## 所見候補
#   093 (✎): n_0′ = nm′/m = 6,141,587 だが、印刷の m、n、m′ では nm′/m = 6,141,592·27 . . . (nec_29_093・th_29_093_fix)。
#            限界 6,118,361・6,164,813 は 6,141,587 ± 23,226 で、印刷の中心値に揃っている (th_29_094_limits)。
#   121 (✎): Σp_κq_λr_μ . . . < 1/a² (比 ≥ 1 の組) は狭義では一般に偽: 値 −2, 0, 2、確率 1/8, 3/4, 1/8、a = 2 で等号
#            (nec_29_121)。成り立つのは ≤ (th_29_121_fix)。ただし 124・125 (比 > 1 の確率に当たる 1 − P) は狭義で真
#            (th_29_124・th_29_125)。
#   163 (F29.5 の一部): I. の印刷形 (s/μ)^m では但し書き m > s + 1 の下でも偽 (nec_29_163: μ = 10、p = 1/5、m = 5)。
#            III. の対応する因子 (s/m)^m が意図と読める (I. が T)。
#   165 (F29.5 の一部): II. の根号 √(μ(μ − n)/μ) は、I. (III. の形) を余事象に写した形の √(n(μ − n)/μ) より大きい
#            (th_29_165_cmp、但し書き provII の下)。印刷の II. は写した形より弱い上界で、反例にはならない。III. の第 2 行の
#            指数 n − μ (II. では μ − n) は扱っていない。
#   161 (✎、F29.1): 「is greater than t − 1/a²」の t を §13 の a = √n/t (130) で読むと偽 (nec_29_161: s = 16、a = 2 で
#            t = 2、t − 1/a² = 7/4 > 1)。t を 1 と読んだ形は th_29_158。t のこの読みは作業役の読みである。
#   160 (F29.2): 印刷の sp ± √2 ak√s は a√(Σp_λq_λ) = ak√s/√2 の 2 倍 (th_29_160_fix・nec_29_160)。
#   178: Simmons の「n = 1 で最大、n とともに減少」は a = 2, 3, 9、n = 1, 2, 3 の 9 点の検算のみ (th_29_178)。一般の証明は
#            ない (台帳は 未)。a = 1 (p = 1/2) では対称性から Δ = 0 で「減少」は狭義には成り立たない (Lean では示していない)。
#   187 の表 (F29.9): p = 1/100、m = 100 の Δ は ·101794 . . . で印刷の ·101813 と 10⁻⁵ 以上違う (nec_29_187_table)。
#            他の 9 行は印刷の桁で合う (th_29_187_table・th_29_187_table_1000; 印刷は切り捨て、最後の桁で数単位の違いあり)。
#   152 の表 (F29.8): ·9445 は 1 − 1/18 = ·94444 . . . の 4 桁の丸めでない (nec_29_152)。
#   086: 「I know of no solution of this, even approximate」— 漸化式は閉じた解をもつ (Pólya の壺の分布
#            C(q, p) r^{(p)} (s − r)^{(q−p)}/s^{(q)}、th_29_086_sol・th_29_086_closed)。印刷の誤りではない (補足)。
#   119: 分数の分母 a_1 + b_1 + . . . − a² − b² − . . . が 0 でないことを暗に仮定している (nec_29_119)。
#   §13 の a は x の平均と、限界の倍率 (a > 1) の二役に印刷されている (folio 354–355)。本ファイルでは倍率を a、平均を mean と書く。
#   189・190: 26・31・26・34 は 100 倍した確率 26·17・31·64・26·39・34·87 の切り捨て (丸めなら 31 は 32、34 は 35)。
#
# ## 依頼文との違い (報告事項)
#   154〜157 (a = p_1 等): 第 10 回は ✓ としたが、修正 1 回目の裁定で 定 (印刷は「For we put」; 079 の前例)。
#   th_29_154〜157 (x = 1/0 の量の平均として導く形) は補助に残す。
#   086 (漸化式): 第 10 回は前提 GenSucc を定理の仮定に取って ✓ としたが、修正 1 回目の裁定で 074・075 と揃えて 外部公理依存:
#   GenSucc を data (aG・hG) の上の外部公理 ax_gen_succ として名付け、th_29_086_data がそれに依る。仮定を前提に取った形
#   th_29_086 は補助。
#   189・190 (p = 1/4、p = 1/10): 修正 1 回目の裁定で 定 (例の前提)。th_29_189・th_29_190 は p を前提 hp に写した検算。
#   178: 修正 1 回目の裁定で ≈ (数値評価) をやめ 未 (数値 9 点の検算のみ、一般の証明なし)。
#   用語: p_κ の訳は「確率」(印刷は probabilities)。
#
# ## 実行方法
#   lake env lean phases/keynes_part_v_phase16c_tchebycheff.lean
-/
import Mathlib

namespace KeynesXXIXd

open Real Finset Filter Topology

/-! ## 内包的キャリアと結合子 (phase6c・phase14a・phase16b と同一; §11 の 086 だけが用いる) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom iiff : IProp → IProp → IProp
axiom itrue : IProp

axiom PrI : IProp → IProp → ℝ

/-- 整合性述語 `Cons h`: 「h は矛盾する連言でない」(folio 135、公理 (i))。 -/
axiom Cons : IProp → Prop

/-! ## Keynes 操作公理群 (内包版、phase6c・phase16b と同一) -/

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

/-! ## 移植定理 (phase6c・phase16b と同一の証明) -/

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

/-- _m x_n (phase14a・phase16b と同一): 最初の n 回のうち m 回起こり、他では起こらない。 -/
noncomputable def x (a : ℕ → IProp) : ℕ → ℕ → IProp
  | 0, 0 => itrue
  | _ + 1, 0 => inot itrue
  | 0, n + 1 => iand (inot (a (n + 1))) (x a 0 n)
  | m + 1, n + 1 =>
      if m = n then iand (a (n + 1)) (x a m n)
      else ior (iand (a (n + 1)) (x a m n)) (iand (inot (a (n + 1))) (x a (m + 1) n))

/-- ⊥/h = 0 (h 整合)。 -/
theorem pr_false (h : IProp) (hc : Cons h) : PrI (inot itrue) h = 0 :=
  taut_neg_zero Form.fls (fun _ => itrue) h hc (fun _ => rfl)

/-- 排反な選言: ((A ∧ X) ∨ (Ā ∧ Y))/h = (A ∧ X)/h + (Ā ∧ Y)/h (h 整合; phase16b と同一)。 -/
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

/-- 条件付きの乗法: X ∧ h が整合なら A/X h = c、のとき (A ∧ X)/h = c · X/h (X/h = 0 なら両辺 0)。 -/
theorem cond_mul (A X h : IProp) (hc : Cons h) (c : ℝ)
    (hA : Cons (iand X h) → PrI A (iand X h) = c) :
    PrI (iand A X) h = c * PrI X h := by
  rw [def_X_left_i]
  by_cases h0 : PrI X h = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [hA (cons_of_pos X h h0 hc)]

/-- 同じ前提で (Ā ∧ X)/h = (1 − c) · X/h。 -/
theorem cond_mul_not (A X h : IProp) (hc : Cons h) (c : ℝ)
    (hA : Cons (iand X h) → PrI A (iand X h) = c) :
    PrI (iand (inot A) X) h = (1 - c) * PrI X h := by
  rw [def_X_left_i]
  by_cases h0 : PrI X h = 0
  · rw [h0, mul_zero, mul_zero]
  · have hcx := cons_of_pos X h h0 hc
    have e := th_13_1_i A (iand X h) hcx
    rw [hA hcx] at e
    rw [show PrI (inot A) (iand X h) = 1 - c by linarith]

/-- n 回のうち n 回より多く起こることはない: m > n なら _m x_n / h = 0。 -/
theorem x_zero (a : ℕ → IProp) (h : IProp) (hc : Cons h) :
    ∀ n m, n < m → PrI (x a m n) h = 0 := by
  intro n
  induction n with
  | zero =>
      intro m hm
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [x]; exact pr_false h hc
  | succ n ih =>
      intro m hm
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [x, if_neg (show m ≠ n by omega)]
      rw [pr_or_excl _ _ _ h hc, def_X_left_i, def_X_left_i (inot _), ih m (by omega),
        ih (m + 1) (by omega)]
      ring

/-! ## §11 (folio 351): 一般の問題と φ(p, q) の漸化式 (086) -/

/-- §11 の一般の問題の前提 (folio 351): 「If an event has occurred x times in the first y trials, its probability at
the y + 1th is (r + x)/(s + y)」(前提 _x x_y ∧ h が整合な場合)。 -/
def GenSucc (a : ℕ → IProp) (h : IProp) (r s : ℝ) : Prop :=
  ∀ k y, Cons (iand (x a k y) h) → PrI (a (y + 1)) (iand (x a k y) h) = (r + k) / (s + y)

/-- ch29-085 (定): φ(p, q) = q 回の試行で事象が p 回起こる à priori の確率 (_p x_q / h)。 -/
noncomputable def φ (a : ℕ → IProp) (h : IProp) (p q : ℕ) : ℝ := PrI (x a p q) h

/-- ch29-086 の補助 (仮定を前提に取った形): 前提 GenSucc の下で
φ(p, q) = (r+p−1)/(s+q−1) · φ(p−1, q−1) + (s+q−1−r−p)/(s+q−1) · φ(p, q−1) (p, q ≥ 1、s > 0)。
第 II 部の公理 (Def. IX・X、Ax. (iii)、整合性) と前提 GenSucc だけによる。台帳の判定は data の上の th_29_086_data。 -/
theorem th_29_086 (a : ℕ → IProp) (h : IProp) (hc : Cons h) (r s : ℝ) (hs : 0 < s)
    (hR : GenSucc a h r s) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    φ a h p q = (r + p - 1) / (s + q - 1) * φ a h (p - 1) (q - 1)
      + (s + q - 1 - r - p) / (s + q - 1) * φ a h p (q - 1) := by
  obtain ⟨p, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hsq : 0 < s + q := by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith
  have e1 : s + (q + 1) - 1 = s + q := by ring
  have e2 : r + (p + 1) - 1 = r + p := by ring
  rw [e1, e2]
  have hA1 := hR p q
  have hA2 : Cons (iand (x a (p + 1) q) h) →
      PrI (a (q + 1)) (iand (x a (p + 1) q) h) = (r + (p + 1)) / (s + q) := by
    intro hcx; rw [hR (p + 1) q hcx]; push_cast; ring
  unfold φ
  by_cases hpq : p = q
  · subst hpq
    simp only [x, if_true]
    rw [cond_mul _ _ h hc _ hA1, x_zero a h hc p (p + 1) (by omega)]
    ring
  · simp only [x, if_neg hpq]
    rw [pr_or_excl _ _ _ h hc, cond_mul _ _ h hc _ hA1, cond_mul_not _ _ h hc _ hA2]
    have : 1 - (r + (p + 1)) / (s + q) = (s + q - r - (p + 1)) / (s + q) := by
      field_simp; ring
    rw [this]

/-- 上昇階乗 x(x+1)···(x+n−1)。 -/
noncomputable def rf (y : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => rf y n * (y + n)

theorem rf_pos (y : ℝ) (hy : 0 < y) : ∀ n, 0 < rf y n := by
  intro n
  induction n with
  | zero => simp [rf]
  | succ n ih => simp only [rf]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; positivity

/-- 086 の漸化式の解 (Pólya の壺の分布): φ(p, q) = C(q, p) r^{(p)} (s − r)^{(q−p)} / s^{(q)} (上昇階乗)。 -/
noncomputable def phiP (r s : ℝ) (p q : ℕ) : ℝ :=
  if p ≤ q then (q.choose p : ℝ) * rf r p * rf (s - r) (q - p) / rf s q else 0

/-- 086 の漸化式は解をもつ (「I know of no solution of this, even approximate」への補足): phiP は漸化式を満たす。 -/
theorem th_29_086_sol (r s : ℝ) (hs : 0 < s) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    phiP r s p q = (r + p - 1) / (s + q - 1) * phiP r s (p - 1) (q - 1)
      + (s + q - 1 - r - p) / (s + q - 1) * phiP r s p (q - 1) := by
  obtain ⟨p, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hsq : 0 < s + q := by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith
  have e1 : s + (q + 1) - 1 = s + q := by ring
  have e2 : r + (p + 1) - 1 = r + p := by ring
  rw [e1, e2]
  have hrf := rf_pos s hs q
  rcases lt_trichotomy p q with hlt | heq | hgt
  · obtain ⟨k, rfl⟩ : ∃ k, q = p + k + 1 := ⟨q - p - 1, by omega⟩
    unfold phiP
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    rw [show p + k + 1 + 1 - (p + 1) = k + 1 by omega, show p + k + 1 - p = k + 1 by omega,
      show p + k + 1 - (p + 1) = k by omega]
    rw [Nat.choose_succ_succ]
    simp only [rf, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  · subst heq
    unfold phiP
    rw [if_pos le_rfl, if_pos le_rfl, if_neg (by omega)]
    simp only [Nat.sub_self, Nat.choose_self, rf]
    push_cast
    field_simp
    ring
  · unfold phiP
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

/-- 前提 GenSucc の下で φ(p, q) は phiP に等しい (q についての帰納法; 第 II 部の公理と前提 GenSucc だけ)。 -/
theorem th_29_086_closed (a : ℕ → IProp) (h : IProp) (hc : Cons h) (r s : ℝ) (hs : 0 < s)
    (hR : GenSucc a h r s) : ∀ q p, φ a h p q = phiP r s p q := by
  intro q
  induction q with
  | zero =>
      intro p
      cases p with
      | zero => simp [φ, x, phiP, rf, itrue_certain h hc]
      | succ p => simp [φ, x, phiP, pr_false h hc]
  | succ q ih =>
      intro p
      cases p with
      | zero =>
          have hsq : 0 < s + q := by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith
          have hA : Cons (iand (x a 0 q) h) → PrI (a (q + 1)) (iand (x a 0 q) h) = r / (s + q) := by
            intro hcx; rw [hR 0 q hcx]; simp
          have e : φ a h 0 (q + 1) = (1 - r / (s + q)) * φ a h 0 q := by
            unfold φ; simp only [x]; exact cond_mul_not _ _ h hc _ hA
          rw [e, ih 0]
          unfold phiP
          rw [if_pos (by omega), if_pos (by omega)]
          simp only [Nat.choose_zero_right, Nat.sub_zero, rf, Nat.cast_one]
          have hrf := rf_pos s hs q
          field_simp
          ring
      | succ p =>
          have e := th_29_086 a h hc r s hs hR (p + 1) (q + 1) (by omega) (by omega)
          have e' := th_29_086_sol r s hs (p + 1) (q + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel] at e e'
          rw [e, e', ih p, ih (p + 1)]

/-- 自明な代入 a_λ := ⊤、h := ⊤ では、_k x_y / h は k = y でなければ 0。 -/
theorem x_true_zero : ∀ n m, m ≠ n → PrI (x (fun _ => itrue) m n) itrue = 0 := by
  intro n
  induction n with
  | zero =>
      intro m hm
      obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [x]; exact pr_false itrue cons_true
  | succ n ih =>
      intro m hm
      have hz : ∀ X : IProp, PrI (iand (inot itrue) X) itrue = 0 := by
        intro X
        rw [cond_mul _ _ itrue cons_true 0 (fun hcx => pr_false _ hcx), zero_mul]
      cases m with
      | zero => simp only [x]; exact hz _
      | succ m =>
          by_cases hmn : m < n
          · simp only [x, if_neg (show m ≠ n by omega)]
            rw [pr_or_excl _ _ _ itrue cons_true, true_conj _ _ cons_true, ih m (by omega), hz]
            ring
          · exact x_zero _ itrue cons_true (n + 1) (m + 1) (by omega)

/-- 前提 GenSucc は自明な代入 a_λ := ⊤、h := ⊤、r = s (> 0) で第 II 部の公理だけから満たされる (確率 1 の場合;
phase16b の rel_cons_poisson_trivial と同じ水準の確かめ)。 -/
theorem rel_cons_gensucc_trivial (s : ℝ) (hs : 0 < s) :
    Cons itrue ∧ GenSucc (fun _ => itrue) itrue s s := by
  refine ⟨cons_true, fun k y hcx => ?_⟩
  have hky : k = y := by
    by_contra hne
    exact cons_of_pos_src _ _ hcx (x_true_zero y k hne)
  subst hky
  rw [itrue_certain _ hcx]
  have : (0 : ℝ) < s + k := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  field_simp

/-- y_k: 最初の k 回すべてに起こる (phase14a・phase16b と同一)。 -/
noncomputable def y (a : ℕ → IProp) : ℕ → IProp
  | 0 => itrue
  | r + 1 => iand (a (r + 1)) (y a r)

/-- _k x_k = y_k (k 回のうち k 回起こる)。 -/
theorem x_diag (a : ℕ → IProp) : ∀ k, x a k k = y a k
  | 0 => rfl
  | k + 1 => by rw [x, if_pos rfl, x_diag a k, y]

/-- GenSucc の x = y の場合は phase16b の SuccRule の形: 最初の k 回すべてに起これば k + 1 回目の確率は (r + k)/(s + k)。
phase16b の nec_succession_model は、第 II 部の公理の文 13 本を満たす可算模型 MS で、整合な h と r = 1、s = 2 について
この形を偽にする。よって GenSucc (ax_gen_succ) は第 II 部の公理群からは導けない (phase は互いに import しないので参照のみ)。 -/
theorem gensucc_succ (a : ℕ → IProp) (h : IProp) (r s : ℝ) (hR : GenSucc a h r s) (k : ℕ)
    (hc : Cons (iand (y a k) h)) : PrI (a (k + 1)) (iand (y a k) h) = (r + k) / (s + k) := by
  rw [← x_diag a k] at hc ⊢
  exact hR k k hc

/-! ## §11: 一般の問題の data (外部公理; phase16b の aS・hS・ax_succession_rule と同じ置き方) -/

/-- §11 の一般の問題の系列: à priori の経験 (r, s) ごとの事象の系列 a_k (k 回目に起こる) の名付け。 -/
axiom aG : ℕ → ℕ → ℕ → IProp
/-- §11 の一般の問題の data の名付け。 -/
axiom hG : ℕ → ℕ → IProp
/-- data は矛盾する連言でない。 -/
axiom ax_data_consG (r s : ℕ) : Cons (hG r s)
/-- 一般の問題の前提 (folio 351): 最初の y 回で x 回起こったと知れば、y + 1 回目の確率は (r + x)/(s + y) (0 < r < s)。 -/
axiom ax_gen_succ (r s : ℕ) (hr : 0 < r) (hrs : r < s) : GenSucc (aG r s) (hG r s) r s

/-- ch29-086 (外部公理依存): data の上で
φ(p, q) = (r+p−1)/(s+q−1) · φ(p−1, q−1) + (s+q−1−r−p)/(s+q−1) · φ(p, q−1) (p, q ≥ 1、0 < r < s)。
第 II 部の公理と外部公理 ax_gen_succ (・ax_data_consG) による。 -/
theorem th_29_086_data (r s : ℕ) (hr : 0 < r) (hrs : r < s) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    φ (aG r s) (hG r s) p q
      = ((r : ℝ) + p - 1) / ((s : ℝ) + q - 1) * φ (aG r s) (hG r s) (p - 1) (q - 1)
        + ((s : ℝ) + q - 1 - r - p) / ((s : ℝ) + q - 1) * φ (aG r s) (hG r s) p (q - 1) :=
  th_29_086 _ _ (ax_data_consG r s) r s (Nat.cast_pos.mpr (by omega)) (ax_gen_succ r s hr hrs) p q hp hq

/-- 086 の解を data の上で: φ(p, q) = C(q, p) r^{(p)} (s − r)^{(q−p)}/s^{(q)} (外部公理 ax_gen_succ による)。 -/
theorem th_29_086_closed_data (r s : ℕ) (hr : 0 < r) (hrs : r < s) (p q : ℕ) :
    φ (aG r s) (hG r s) p q = phiP r s p q :=
  th_29_086_closed _ _ (ax_data_consG r s) r s (Nat.cast_pos.mpr (by omega)) (ax_gen_succ r s hr hrs) q p

/-! ## §13 (folio 353): 量・確率・平均 (定) -/

/-- 量 (magnitude) x: 値 x_κ と確率 p_κ (κ は有限個)。 -/
structure Mag (ι : Type) [Fintype ι] where
  X : ι → ℝ
  P : ι → ℝ

variable {ι : Type} [Fintype ι]

/-- ch29-103: a := Σp_κ x_κ (x の平均)。 -/
def mean (M : Mag ι) : ℝ := ∑ j, M.P j * M.X j

/-- ch29-104: a_1 := Σp_κ x_κ² (x² の平均)。 -/
def mean2 (M : Mag ι) : ℝ := ∑ j, M.P j * M.X j ^ 2

/-! ## 111・112: Σ(x_κ − a)² p_κ = a_1 − a² -/

/-- ch29-111 (✓): Σ(x_κ² − 2a x_κ + a²) p_κ = Σp_κx_κ² − 2aΣp_κx_κ + a²Σp_κ。 -/
theorem th_29_111 (M : Mag ι) (a : ℝ) :
    ∑ j, (M.X j ^ 2 - 2 * a * M.X j + a ^ 2) * M.P j
      = ∑ j, M.P j * M.X j ^ 2 - 2 * a * ∑ j, M.P j * M.X j + a ^ 2 * ∑ j, M.P j := by
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl (fun j _ => by ring)

/-- ch29-112 (✓): (Σp = 1、a = Σpx のとき) = a_1 − 2a² + a² = a_1 − a²。 -/
theorem th_29_112 (M : Mag ι) (hN : ∑ j, M.P j = 1) :
    ∑ j, M.P j * M.X j ^ 2 - 2 * mean M * ∑ j, M.P j * M.X j + mean M ^ 2 * ∑ j, M.P j
        = mean2 M - 2 * mean M ^ 2 + mean M ^ 2 ∧
      mean2 M - 2 * mean M ^ 2 + mean M ^ 2 = mean2 M - mean M ^ 2 := by
  refine ⟨?_, by ring⟩
  rw [hN]; unfold mean mean2; ring

/-- 111・112 をつないだ形: Σ(x_κ − a)² p_κ = a_1 − a²。 -/
theorem var_one (M : Mag ι) (hN : ∑ j, M.P j = 1) :
    ∑ j, M.P j * (M.X j - mean M) ^ 2 = mean2 M - mean M ^ 2 := by
  have e := th_29_111 M (mean M)
  rw [(th_29_112 M hN).1, (th_29_112 M hN).2] at e
  rw [← e]
  exact sum_congr rfl (fun j _ => by ring)

/-! ## 114–116: Σ2(x_κ − a)(y_λ − b) p_κ = 0 -/

/-- ch29-114 (✓): Σ2(x_κ − a)(y_λ − b) p_κ = Σ2(x_κ y_λ − b x_κ − a y_λ + ab) p_κ。 -/
theorem th_29_114 (M : Mag ι) (a b y : ℝ) :
    ∑ j, 2 * (M.X j - a) * (y - b) * M.P j
      = ∑ j, 2 * (M.X j * y - b * M.X j - a * y + a * b) * M.P j :=
  sum_congr rfl (fun j _ => by ring)

/-- ch29-115 (✓): = 2(y_λ Σp_κx_κ − bΣp_κx_κ − a y_λ Σp_κ + abΣp_κ)。 -/
theorem th_29_115 (M : Mag ι) (a b y : ℝ) :
    ∑ j, 2 * (M.X j * y - b * M.X j - a * y + a * b) * M.P j
      = 2 * (y * ∑ j, M.P j * M.X j - b * ∑ j, M.P j * M.X j - a * y * ∑ j, M.P j
          + a * b * ∑ j, M.P j) := by
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl (fun j _ => by ring)

/-- ch29-116 (✓): (Σp = 1、a = Σpx のとき) = 2(a y_λ − ab − a y_λ + ab) = 0。 -/
theorem th_29_116 (M : Mag ι) (hN : ∑ j, M.P j = 1) (b y : ℝ) :
    2 * (y * ∑ j, M.P j * M.X j - b * ∑ j, M.P j * M.X j - mean M * y * ∑ j, M.P j
          + mean M * b * ∑ j, M.P j)
        = 2 * (mean M * y - mean M * b - mean M * y + mean M * b) ∧
      2 * (mean M * y - mean M * b - mean M * y + mean M * b) = 0 := by
  refine ⟨?_, by ring⟩
  rw [hN]; unfold mean; ring

/-- 一次の中心化: Σ(x_κ − a) p_κ = 0。 -/
theorem dev_zero (M : Mag ι) (hN : ∑ j, M.P j = 1) : ∑ j, M.P j * (M.X j - mean M) = 0 := by
  have : ∑ j, M.P j * (M.X j - mean M) = ∑ j, M.P j * M.X j - mean M * ∑ j, M.P j := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl (fun j _ => by ring)
  rw [this, hN]; unfold mean; ring

/-! ## 量の族と同時の確率 (107・108) -/

section Family

variable {n : ℕ} {ι : Fin n → Type} [∀ i, Fintype (ι i)]

/-- ch29-108: p_κ q_λ r_μ . . . (値の組 κ の確率; 量は互いに独立)。 -/
def jp (M : ∀ i, Mag (ι i)) (κ : ∀ i, ι i) : ℝ := ∏ i, (M i).P (κ i)

/-- ch29-107: x_κ + y_λ + z_μ + . . . -/
def Ssum (M : ∀ i, Mag (ι i)) (κ : ∀ i, ι i) : ℝ := ∑ i, (M i).X (κ i)

/-- a + b + c + . . . -/
def Atot (M : ∀ i, Mag (ι i)) : ℝ := ∑ i, mean (M i)

/-- a_1 + b_1 + c_1 + . . . − a² − b² − c² − . . . -/
def Vt (M : ∀ i, Mag (ι i)) : ℝ := ∑ i, mean2 (M i) - ∑ i, mean (M i) ^ 2

/-- 周辺化 (一つの量): Σ_κ p_κ q_λ r_μ . . . G(x_κ) = Σ p_κ G(x_κ)。 -/
theorem marg1 (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1) (i : Fin n)
    (G : ∀ l, ι l → ℝ) :
    ∑ κ, jp M κ * G i (κ i) = ∑ t, (M i).P t * G i t := by
  have e1 : ∀ κ : (∀ l, ι l), jp M κ * G i (κ i)
      = ∏ l, ((M l).P (κ l) * (if l = i then G l (κ l) else 1)) := by
    intro κ
    rw [prod_mul_distrib, prod_ite_eq' univ i (fun l => G l (κ l))]
    simp [jp]
  simp_rw [e1]
  rw [← Fintype.prod_sum (fun l t => (M l).P t * (if l = i then G l t else 1))]
  have e2 : ∀ l, ∑ t, (M l).P t * (if l = i then G l t else 1)
      = if l = i then ∑ t, (M l).P t * G l t else 1 := by
    intro l
    split_ifs with h
    · rfl
    · simp [hN l]
  simp_rw [e2]
  rw [prod_ite_eq' univ i (fun l => ∑ t, (M l).P t * G l t)]
  simp

/-- 周辺化 (二つの量、i ≠ j): Σ p_κ q_λ r_μ . . . G(x_κ) H(y_λ) = (Σp_κG(x_κ))(Σq_λH(y_λ))。 -/
theorem marg2 (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1) (i j : Fin n) (hij : i ≠ j)
    (G H : ∀ l, ι l → ℝ) :
    ∑ κ, jp M κ * G i (κ i) * H j (κ j)
      = (∑ t, (M i).P t * G i t) * (∑ t, (M j).P t * H j t) := by
  have e1 : ∀ κ : (∀ l, ι l), jp M κ * G i (κ i) * H j (κ j)
      = ∏ l, ((M l).P (κ l) * (if l = i then G l (κ l) else 1)
          * (if l = j then H l (κ l) else 1)) := by
    intro κ
    rw [prod_mul_distrib, prod_mul_distrib, prod_ite_eq' univ i (fun l => G l (κ l)),
      prod_ite_eq' univ j (fun l => H l (κ l))]
    simp [jp]
  simp_rw [e1]
  rw [← Fintype.prod_sum (fun l t => (M l).P t * (if l = i then G l t else 1)
      * (if l = j then H l t else 1))]
  have e2 : ∀ l, ∑ t, (M l).P t * (if l = i then G l t else 1) * (if l = j then H l t else 1)
      = (if l = i then ∑ t, (M l).P t * G l t else 1)
        * (if l = j then ∑ t, (M l).P t * H l t else 1) := by
    intro l
    by_cases hi : l = i
    · subst hi
      simp [hij]
    · by_cases hj : l = j
      · subst hj
        simp [hi]
      · simp [hi, hj, hN l]
  simp_rw [e2]
  rw [prod_mul_distrib, prod_ite_eq' univ i (fun l => ∑ t, (M l).P t * G l t),
    prod_ite_eq' univ j (fun l => ∑ t, (M l).P t * H l t)]
  simp

/-- ch29-113 (✓): Σq_λ r_μ . . . = 1 (すべての λ, μ . . . にわたる和)。 -/
theorem th_29_113 (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1) :
    ∑ κ, jp M κ = 1 := by
  unfold jp
  rw [← Fintype.prod_sum (fun l t => (M l).P t)]
  simp [hN]

/-- ch29-117・118 (✓): Σ(x_κ + y_λ + z_μ + . . . − a − b − c − . . .)² p_κ q_λ r_μ . . .
= a_1 + b_1 + c_1 + . . . − a² − b² − c² − . . . -/
theorem th_29_117 (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1) :
    ∑ κ, (Ssum M κ - Atot M) ^ 2 * jp M κ
      = ∑ i, mean2 (M i) - ∑ i, mean (M i) ^ 2 := by
  set D : ∀ l, ι l → ℝ := fun l t => (M l).X t - mean (M l) with hD
  have hS : ∀ κ : (∀ l, ι l), Ssum M κ - Atot M = ∑ i, D i (κ i) := by
    intro κ; unfold Ssum Atot; rw [← sum_sub_distrib]
  have e1 : ∀ κ : (∀ l, ι l), (Ssum M κ - Atot M) ^ 2 * jp M κ
      = ∑ i, ∑ j, jp M κ * D i (κ i) * D j (κ j) := by
    intro κ
    rw [hS, sq, sum_mul_sum, sum_mul]
    exact sum_congr rfl (fun i _ => by rw [sum_mul]; exact sum_congr rfl (fun j _ => by ring))
  simp_rw [e1]
  rw [sum_comm]
  have e2 : ∀ i, ∑ κ, ∑ j, jp M κ * D i (κ i) * D j (κ j) = mean2 (M i) - mean (M i) ^ 2 := by
    intro i
    rw [sum_comm, sum_eq_single i]
    · have := marg1 M hN i (fun l t => D l t * D l t)
      simp only at this
      rw [← var_one (M i) (hN i)]
      simp_rw [mul_assoc]
      rw [this]
      exact sum_congr rfl (fun t _ => by rw [hD]; ring)
    · intro j _ hji
      rw [marg2 M hN i j (Ne.symm hji) D D]
      have h0 := dev_zero (M i) (hN i)
      simp only [hD]
      rw [h0, zero_mul]
    · simp
  simp_rw [e2]
  rw [sum_sub_distrib]

/-- ch29-119 (✓): Σ(x_κ + . . . − a − . . .)² p_κ q_λ r_μ . . . / (a²(a_1 + . . . − a² − . . .)) = 1/a²
(分母が 0 でないこと、すなわち a_1 + b_1 + . . . − a² − b² − . . . ≠ 0 は分数が意味をもつ条件)。 -/
theorem th_29_119 (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1) (a : ℝ) (ha : 1 < a)
    (hV : Vt M ≠ 0) :
    ∑ κ, (Ssum M κ - Atot M) ^ 2 * jp M κ / (a ^ 2 * Vt M) = 1 / a ^ 2 := by
  rw [← sum_div, th_29_117 M hN]
  have ha0 : a ≠ 0 := by positivity
  change Vt M / (a ^ 2 * Vt M) = 1 / a ^ 2
  field_simp

/-- 119 の分母の条件は外せない: a_1 + b_1 + . . . − a² − b² − . . . = 0 なら左辺は (実数の除法で) 0 で、1/a² でない。 -/
theorem nec_29_119 (M : ∀ i, Mag (ι i)) (a : ℝ) (ha : 1 < a) (hV : Vt M = 0) :
    ∑ κ, (Ssum M κ - Atot M) ^ 2 * jp M κ / (a ^ 2 * Vt M) ≠ 1 / a ^ 2 := by
  rw [hV]; simp only [mul_zero, div_zero, sum_const_zero]
  have : 0 < a := by linarith
  positivity

/-- ch29-123: 比 (x_κ + . . . − a − . . .)² / (a²(a_1 + . . . − a² − . . .))。 -/
noncomputable def ratio (M : ∀ i, Mag (ι i)) (a : ℝ) (κ : ∀ i, ι i) : ℝ :=
  (Ssum M κ - Atot M) ^ 2 / (a ^ 2 * Vt M)

/-- ch29-123: P = 比が 1 以下 (「equal to or less than unity」) である確率。 -/
noncomputable def Pt (M : ∀ i, Mag (ι i)) (a : ℝ) : ℝ :=
  ∑ κ ∈ univ.filter (fun κ => ratio M a κ ≤ 1), jp M κ

/-- 119 の左辺の項は 比 × p_κ q_λ r_μ . . . -/
theorem term_eq (M : ∀ i, Mag (ι i)) (a : ℝ) (κ : ∀ i, ι i) :
    (Ssum M κ - Atot M) ^ 2 * jp M κ / (a ^ 2 * Vt M) = ratio M a κ * jp M κ := by
  unfold ratio; ring

theorem jp_nonneg (M : ∀ i, Mag (ι i)) (hP : ∀ i j, 0 ≤ (M i).P j) (κ : ∀ i, ι i) :
    0 ≤ jp M κ := prod_nonneg (fun i _ => hP i (κ i))

/-- 値の組のどの集まりについても、確率の和は 1 を超えない。 -/
theorem jp_sum_le_one (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1)
    (hP : ∀ i j, 0 ≤ (M i).P j) (S : Finset (∀ i, ι i)) : ∑ κ ∈ S, jp M κ ≤ 1 := by
  rw [← th_29_113 M hN]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun κ _ _ => jp_nonneg M hP κ)

theorem ratio_nonneg (M : ∀ i, Mag (ι i)) (a : ℝ) (hV : 0 < Vt M) (κ : ∀ i, ι i) :
    0 ≤ ratio M a κ := by
  unfold ratio; positivity

/-- ch29-120 (定 の行の主張): 比 < 1 の項 (120) を省き、残る項で比を 1 に置き換える。どちらの操作も
左辺を増やさない (「both these processes diminish the magnitude of the left-hand side」)。 -/
theorem th_29_120 (M : ∀ i, Mag (ι i)) (hP : ∀ i j, 0 ≤ (M i).P j) (a : ℝ) (hV : 0 < Vt M) :
    ∑ κ ∈ univ.filter (fun κ => 1 ≤ ratio M a κ), jp M κ
        ≤ ∑ κ ∈ univ.filter (fun κ => 1 ≤ ratio M a κ), ratio M a κ * jp M κ ∧
      ∑ κ ∈ univ.filter (fun κ => 1 ≤ ratio M a κ), ratio M a κ * jp M κ
        ≤ ∑ κ, (Ssum M κ - Atot M) ^ 2 * jp M κ / (a ^ 2 * Vt M) := by
  constructor
  · refine sum_le_sum (fun κ hκ => ?_)
    have h1 := (mem_filter.mp hκ).2
    nlinarith [jp_nonneg M hP κ]
  · simp_rw [term_eq]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun κ _ _ => mul_nonneg (ratio_nonneg M a hV κ) (jp_nonneg M hP κ))

/-- ch29-121 の修正形 (✎): Σp_κ q_λ r_μ . . . ≤ 1/a² (比 ≥ 1 の組にわたる和)。 -/
theorem th_29_121_fix (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1)
    (hP : ∀ i j, 0 ≤ (M i).P j) (a : ℝ) (ha : 1 < a) (hV : 0 < Vt M) :
    ∑ κ ∈ univ.filter (fun κ => 1 ≤ ratio M a κ), jp M κ ≤ 1 / a ^ 2 := by
  have h := th_29_120 M hP a hV
  rw [th_29_119 M hN a ha hV.ne'] at h
  linarith [h.1, h.2]

/-- ch29-124 (✓): 1 − P < 1/a² (P は比が 1 以下である確率; 狭義の不等号も印刷どおり成り立つ)。 -/
theorem th_29_124 (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1)
    (hP : ∀ i j, 0 ≤ (M i).P j) (a : ℝ) (ha : 1 < a) (hV : 0 < Vt M) :
    1 - Pt M a < 1 / a ^ 2 := by
  have hsplit := sum_filter_add_sum_filter_not univ (fun κ => ratio M a κ ≤ 1) (jp M)
  rw [th_29_113 M hN] at hsplit
  have h1 : 1 - Pt M a = ∑ κ ∈ univ.filter (fun κ => ¬ ratio M a κ ≤ 1), jp M κ := by
    unfold Pt; linarith
  rw [h1]
  have hall : ∑ κ, ratio M a κ * jp M κ = 1 / a ^ 2 := by
    rw [← th_29_119 M hN a ha hV.ne']; simp_rw [term_eq]
  have hsub : ∑ κ ∈ univ.filter (fun κ => ¬ ratio M a κ ≤ 1), ratio M a κ * jp M κ
      ≤ ∑ κ, ratio M a κ * jp M κ :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun κ _ _ => mul_nonneg (ratio_nonneg M a hV κ) (jp_nonneg M hP κ))
  by_cases hz : ∀ κ ∈ univ.filter (fun κ => ¬ ratio M a κ ≤ 1), jp M κ = 0
  · rw [sum_eq_zero hz]; positivity
  · obtain ⟨κ0, hκ0, hne⟩ : ∃ κ0 ∈ univ.filter (fun κ => ¬ ratio M a κ ≤ 1), jp M κ0 ≠ 0 := by
      by_contra hc
      exact hz (fun κ hκ => by by_contra h; exact hc ⟨κ, hκ, h⟩)
    have hlt : ∑ κ ∈ univ.filter (fun κ => ¬ ratio M a κ ≤ 1), jp M κ
        < ∑ κ ∈ univ.filter (fun κ => ¬ ratio M a κ ≤ 1), ratio M a κ * jp M κ := by
      refine sum_lt_sum (fun κ hκ => ?_) ⟨κ0, hκ0, ?_⟩
      · have h1 := (mem_filter.mp hκ).2
        nlinarith [jp_nonneg M hP κ]
      · have h1 := (mem_filter.mp hκ0).2
        have hpos : 0 < jp M κ0 := lt_of_le_of_ne (jp_nonneg M hP κ0) (Ne.symm hne)
        nlinarith
    linarith

/-- ch29-125 (✓): P > 1 − 1/a²。 -/
theorem th_29_125 (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1)
    (hP : ∀ i j, 0 ≤ (M i).P j) (a : ℝ) (ha : 1 < a) (hV : 0 < Vt M) :
    Pt M a > 1 - 1 / a ^ 2 := by
  have := th_29_124 M hN hP a ha hV
  linarith

/-- 比 ≤ 1 は和が限界 a + b + c + . . . ± a√(a_1 + . . . − a² − . . .) の間にあることと同じ。 -/
theorem ratio_le_one_iff (M : ∀ i, Mag (ι i)) (a : ℝ) (ha : 0 < a) (hV : 0 < Vt M)
    (κ : ∀ i, ι i) :
    ratio M a κ ≤ 1 ↔ |Ssum M κ - Atot M| ≤ a * √(Vt M) := by
  unfold ratio
  rw [div_le_one (by positivity), ← sq_abs, ← Real.sqrt_le_sqrt_iff (by positivity),
    Real.sqrt_sq (abs_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]

/-- ch29-126〜129 (Tchebycheff の定理): 和 x_κ + y_λ + z_μ + . . . が限界
a + b + c + . . . ± a√(a_1 + b_1 + c_1 + . . . − a² − b² − c² − . . .) の間にある確率は 1 − 1/a² より大きい
(a > 1)。 -/
theorem th_29_tcheb (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1)
    (hP : ∀ i j, 0 ≤ (M i).P j) (a : ℝ) (ha : 1 < a) (hV : 0 < Vt M) :
    ∑ κ ∈ univ.filter (fun κ => |Ssum M κ - Atot M| ≤ a * √(Vt M)), jp M κ > 1 - 1 / a ^ 2 := by
  have h := th_29_125 M hN hP a ha hV
  unfold Pt at h
  rwa [filter_congr (fun κ _ => ratio_le_one_iff M a (by linarith) hV κ)] at h

/-- ch29-130 (定): a := √n/t。 -/
noncomputable def aT (n : ℕ) (t : ℝ) : ℝ := √(n : ℝ) / t

/-- 130 の代入の帰結: t > 0、t² < n なら a = √n/t > 1 で、1 − 1/a² = 1 − t²/n。 -/
theorem th_29_130 (n : ℕ) (t : ℝ) (ht : 0 < t) (htn : t ^ 2 < n) :
    1 < aT n t ∧ 1 - 1 / aT n t ^ 2 = 1 - t ^ 2 / n := by
  have hn : (0 : ℝ) < n := by nlinarith
  refine ⟨(one_lt_div ht).mpr ((Real.lt_sqrt ht.le).mpr htn), ?_⟩
  unfold aT
  rw [div_pow, Real.sq_sqrt hn.le]; field_simp

/-- ch29-130〜133 (第二の形): a = √n/t と書くと、算術平均 (x_κ + y_λ + z_μ + . . .)/n が限界
(a + b + c + . . .)/n ± (1/t)√((a_1 + b_1 + c_1 + . . .)/n − (a² + b² + c² + . . .)/n) の間にある確率は
1 − t²/n より大きい (n は量の個数、t > 0、t² < n すなわち a > 1)。 -/
theorem th_29_133 (M : ∀ i, Mag (ι i)) (hN : ∀ i, ∑ j, (M i).P j = 1)
    (hP : ∀ i j, 0 ≤ (M i).P j) (t : ℝ) (ht : 0 < t) (htn : t ^ 2 < n) (hV : 0 < Vt M) :
    ∑ κ ∈ univ.filter (fun κ => |Ssum M κ / n - Atot M / n|
        ≤ 1 / t * √((∑ i, mean2 (M i)) / n - (∑ i, mean (M i) ^ 2) / n)), jp M κ
      > 1 - t ^ 2 / n := by
  have hn : (0 : ℝ) < n := by nlinarith
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn
  have htsn : t < √(n : ℝ) := (Real.lt_sqrt ht.le).mpr htn
  have ha : 1 < √(n : ℝ) / t := (one_lt_div ht).mpr htsn
  have h := th_29_tcheb M hN hP (√(n : ℝ) / t) ha hV
  have hsq : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt hn.le
  have e1 : 1 - 1 / (√(n : ℝ) / t) ^ 2 = 1 - t ^ 2 / n := by
    rw [div_pow, hsq]; field_simp
  rw [e1] at h
  convert h using 2
  refine filter_congr (fun κ _ => ?_)
  have e2 : (∑ i, mean2 (M i)) / n - (∑ i, mean (M i) ^ 2) / n = Vt M / n := by
    unfold Vt; ring
  rw [e2, ← sub_div, abs_div, abs_of_pos hn, Real.sqrt_div' _ hn.le]
  have e3 : 1 / t * (√(Vt M) / √(n : ℝ)) = √(n : ℝ) / t * √(Vt M) / n := by
    field_simp
    rw [hsq]
  rw [e3, div_le_div_iff_of_pos_right hn]

end Family

/-! ## 121 の印刷形 (狭義の <) への反例 -/

/-- 反例の量 (一つ): 値 −2, 0, 2、確率 1/8, 3/4, 1/8 (平均 0、x² の平均 1)。 -/
noncomputable def cexM : Fin 1 → Mag (Fin 3) := fun _ => ⟨![-2, 0, 2], ![1 / 8, 3 / 4, 1 / 8]⟩

theorem sum_fin1 (f : (Fin 1 → Fin 3) → ℝ) : ∑ κ, f κ = ∑ t : Fin 3, f (fun _ => t) :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3)) _ _
    (fun κ => by congr 1; funext i; rw [Subsingleton.elim i default]; rfl)

/-- ch29-121 (✎): 印刷の Σp_κ q_λ r_μ . . . < 1/a² (比 ≥ 1 の組にわたる和) は一般には成り立たない。
上の量と a = 2 では比は ±2 で 1、0 で 0 となり、和は 1/8 + 1/8 = 1/4 = 1/a² (等号)。 -/
theorem nec_29_121 :
    (∀ i, ∑ j, (cexM i).P j = 1) ∧ (∀ i j, 0 ≤ (cexM i).P j) ∧ (1 : ℝ) < 2 ∧ 0 < Vt cexM ∧
      ∑ κ ∈ univ.filter (fun κ => 1 ≤ ratio cexM 2 κ), jp cexM κ = 1 / 2 ^ 2 := by
  have hV : Vt cexM = 1 := by
    simp [Vt, mean, mean2, cexM, Fin.sum_univ_three]; norm_num
  have hA : Atot cexM = 0 := by
    simp [Atot, mean, cexM, Fin.sum_univ_three]
  refine ⟨fun i => ?_, fun i j => ?_, by norm_num, by rw [hV]; norm_num, ?_⟩
  · simp [cexM, Fin.sum_univ_three]; norm_num
  · fin_cases j <;> norm_num [cexM]
  · rw [sum_filter, sum_fin1]
    simp [ratio, hV, hA, jp, Ssum, cexM, Fin.sum_univ_three]
    norm_num

/-! ## §13 (folio 355): 勝ち負けの例 (134・135) -/

/-- ch29-134・146 (定): q := 1 − p (「p[p = 1 − q]」「where q = 1 − p」)。 -/
noncomputable def q (p : ℝ) : ℝ := 1 - p

/-- ch29-134 (定): 確率 p の事象が起これば A を得、起こらなければ B を失う (一回の勝ち)。 -/
noncomputable def gainMag (p A B : ℝ) : Mag Bool := ⟨fun b => if b then A else -B, fun b => if b then p else q p⟩

/-- s 回の試行の勝ち (互いに独立)。 -/
noncomputable def gains (s : ℕ) (p A B : ℝ) : Fin s → Mag Bool := fun _ => gainMag p A B

theorem gains_N (s : ℕ) (p A B : ℝ) : ∀ i, ∑ j, (gains s p A B i).P j = 1 := by
  intro i; simp [gains, gainMag, q]

theorem gains_P (s : ℕ) (p A B : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i j, 0 ≤ (gains s p A B i).P j := by
  intro i j; cases j <;> simp [gains, gainMag, q] <;> linarith

theorem gains_A (s : ℕ) (p A B : ℝ) : Atot (gains s p A B) = s * (p * A - q p * B) := by
  simp [Atot, mean, gains, gainMag]; ring

theorem gains_V (s : ℕ) (p A B : ℝ) :
    Vt (gains s p A B) = (A + B) ^ 2 * (s * p * q p) := by
  simp [Vt, mean, mean2, gains, gainMag, q]; ring

/-- ch29-135 (記法の行の主張): s 回の試行の勝ち (または負け) の合計が限界 s(pA − qB) ± a(A + B)√(spq) の間に
ある確率は 1 − 1/a² より大きい (Tchebycheff の定理から; A + B > 0、0 < p < 1、a > 1)。 -/
theorem th_29_135 (s : ℕ) (hs : 1 ≤ s) (p A B : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hAB : 0 < A + B)
    (a : ℝ) (ha : 1 < a) :
    ∑ κ ∈ univ.filter (fun κ => |Ssum (gains s p A B) κ - s * (p * A - q p * B)|
        ≤ a * (A + B) * √(s * p * q p)), jp (gains s p A B) κ > 1 - 1 / a ^ 2 := by
  have hq : 0 < q p := by unfold q; linarith
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hV : 0 < Vt (gains s p A B) := by rw [gains_V]; positivity
  have h := th_29_tcheb (gains s p A B) (gains_N s p A B) (gains_P s p A B hp0.le hp1.le) a ha hV
  rw [gains_A, gains_V, Real.sqrt_mul (by positivity), Real.sqrt_sq hAB.le] at h
  simpa only [mul_assoc] using h

/-! ## §14 (folio 356): Bernoulli の定理を Tchebycheff の定理から (138〜148) -/

/-- ch29-138・139 (定): x = 1 (事象が起こる)、x = 0 (起こらない); 確率は p と q。 -/
noncomputable def indMag (p : ℝ) : Mag Bool := ⟨fun b => if b then 1 else 0, fun b => if b then p else q p⟩

/-- ch29-140・141 (✓): a = p、b = p、etc. -/
theorem th_29_140 (p : ℝ) : mean (indMag p) = p := by simp [mean, indMag]

/-- ch29-142・143 (✓): a_1 = p、b_1 = p、etc. -/
theorem th_29_142 (p : ℝ) : mean2 (indMag p) = p := by simp [mean2, indMag]

/-- s 回の観測 (試行) と s 個の量 x_1 x_2 . . . x_s (各回の確率 p)。 -/
noncomputable def bern (s : ℕ) (p : ℝ) : Fin s → Mag Bool := fun _ => indMag p

theorem bern_N (s : ℕ) (p : ℝ) : ∀ i, ∑ j, (bern s p i).P j = 1 := by
  intro i; simp [bern, indMag, q]

theorem bern_P (s : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∀ i j, 0 ≤ (bern s p i).P j := by
  intro i j; cases j <;> simp [bern, indMag, q] <;> linarith

/-- ch29-144 (記法の行の主張): a + b + . . . = sp、a_1 + b_1 + . . . − a² − b² − . . . = sp − sp²。 -/
theorem th_29_144 (s : ℕ) (p : ℝ) :
    Atot (bern s p) = s * p ∧ Vt (bern s p) = s * p - s * p ^ 2 := by
  constructor
  · simp [Atot, bern, th_29_140]
  · simp [Vt, bern, th_29_140, th_29_142]

/-- ch29-145 (記法の行の主張): sp − sp² = spq (q = 1 − p)。 -/
theorem th_29_145 (s : ℕ) (p : ℝ) : s * p - s * p ^ 2 = s * p * q p := by unfold q; ring

/-- ch29-147 (✓): 事象の生起の回数が限界 sp ± a√(spq) の間にある確率 P は > 1 − 1/a²
(s ≥ 1、0 < p < 1、a > 1)。 -/
theorem th_29_147 (s : ℕ) (hs : 1 ≤ s) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (a : ℝ) (ha : 1 < a) :
    ∑ κ ∈ univ.filter (fun κ => |Ssum (bern s p) κ - s * p| ≤ a * √(s * p * q p)), jp (bern s p) κ
      > 1 - 1 / a ^ 2 := by
  have hq : 0 < q p := by unfold q; linarith
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hV : 0 < Vt (bern s p) := by rw [(th_29_144 s p).2, th_29_145]; positivity
  have h := th_29_tcheb (bern s p) (bern_N s p) (bern_P s p hp0.le hp1.le) a ha hV
  rwa [(th_29_144 s p).1, (th_29_144 s p).2, th_29_145] at h

/-- ch29-148 (✓): 「where this formula gives P > 1 − 1/a²」(147 と同じ P)。 -/
theorem th_29_148 (s : ℕ) (hs : 1 ≤ s) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (a : ℝ) (ha : 1 < a) :
    ∑ κ ∈ univ.filter (fun κ => |Ssum (bern s p) κ - s * p| ≤ a * √(s * p * q p)), jp (bern s p) κ
      > 1 - 1 / a ^ 2 :=
  th_29_147 s hs p hp0 hp1 a ha

/-! ## §14 (folio 356): Bernoulli の定理の P = Θ(a/√2) (149、外部公理 ax_normal_approx) -/

/-- 二項の一般項 C(m, n) p^n q^{m−n} (phase14b と同一)。 -/
noncomputable def bterm (m : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  (m.choose n : ℝ) * p ^ n * q p ^ (m - n)

/-- mpq (phase14b と同一)。 -/
noncomputable def mpq (m : ℕ) (p : ℝ) : ℝ := m * p * q p

/-- Θ(t) = 2/√π ∫_0^t e^{−u²} du (phase14b と同一)。 -/
noncomputable def Θ (t : ℝ) : ℝ := 2 / √π * ∫ u in (0 : ℝ)..t, exp (-(u ^ 2))

/-- 二項分布で |n − mp| < a となる確率 (phase14b と同一)。 -/
noncomputable def probWithin (m : ℕ) (p a : ℝ) : ℝ :=
  ∑ n ∈ (range (m + 1)).filter (fun n : ℕ => |(n : ℝ) - m * p| < a), bterm m p n

/-- 積分形の de Moivre–Laplace 定理 (外部公理、phase14b の ax_normal_approx を再掲): p ∈ (0, 1)、γ > 0 なら
|n − mp| < √(2mpq) γ の確率は m → ∞ で Θ(γ) に近づく。 -/
axiom ax_normal_approx (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (γ : ℝ) (hγ : 0 < γ) :
  Tendsto (fun m : ℕ => probWithin m p (√(2 * mpq m p) * γ)) atTop (𝓝 (Θ γ))

/-- ch29-149 (外部公理依存): Bernoulli の定理 (§2 の式) では、生起の回数が限界 sp ± a√(spq) の間にある
確率は s → ∞ で Θ(a/√2) (√(2spq) γ = a√(spq) より γ = a/√2)。 -/
theorem th_29_149 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun s : ℕ => probWithin s p (a * √(s * p * q p))) atTop (𝓝 (Θ (a / √2))) := by
  have h := ax_normal_approx p hp0 hp1 (a / √2) (by positivity)
  refine h.congr (fun s => ?_)
  congr 1
  unfold mpq
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have : (0 : ℝ) < √2 := by positivity
  field_simp

/-! ## §14 (folio 356): 表の列 1 − 1/a² (152) -/

/-- ch29-152 (記法の行、数値評価): 表の列 1 − 1/a² の値 ·333、·5、·7778、·875、·92 (印刷の桁で)。 -/
theorem th_29_152 :
    |(1 - 1 / (3 / 2) : ℝ) - 333 / 1000| < 1 / 1000 ∧ (1 - 1 / 2 : ℝ) = 5 / 10 ∧
      |(1 - 1 / (9 / 2) : ℝ) - 7778 / 10000| < 1 / 20000 ∧ (1 - 1 / 8 : ℝ) = 875 / 1000 ∧
      (1 - 1 / (25 / 2) : ℝ) = 92 / 100 := by
  refine ⟨?_, by norm_num, ?_, by norm_num, by norm_num⟩ <;>
    rw [abs_lt] <;> constructor <;> norm_num

/-- ch29-152 (F29.8): 最後の行の ·9445 は 1 − 1/18 = ·94444 . . . を 4 桁に丸めた値 (·9444) でない。 -/
theorem nec_29_152 : 1 / 20000 < |(9445 / 10000 : ℝ) - (1 - 1 / 18)| := by
  rw [lt_abs]; left; norm_num

/-! ## §14 (folio 356–357): Poisson の定理を Tchebycheff の定理から (154〜160) -/

/-- §8 の記法 (脚注 1): λ 回目の試行 (λ = 1, . . . , s) で事象の確率は p_λ。量 x_λ は起これば 1、
起こらなければ 0。 -/
noncomputable def poi (s : ℕ) (p : ℕ → ℝ) : Fin s → Mag Bool := fun l => indMag (p (l.val + 1))

theorem poi_N (s : ℕ) (p : ℕ → ℝ) : ∀ i, ∑ j, (poi s p i).P j = 1 := by
  intro i; simp [poi, indMag, q]

theorem poi_P (s : ℕ) (p : ℕ → ℝ) (hp : ∀ l, 0 ≤ p l ∧ p l ≤ 1) : ∀ i j, 0 ≤ (poi s p i).P j := by
  intro i j; have := hp (i.val + 1); cases j <;> simp [poi, indMag, q] <;> linarith

/-- ch29-154 (定 の行の補助; 印刷は「For we put」): a = p_1 (x = 1/0 の量の平均として導く)。 -/
theorem th_29_154 (s : ℕ) (hs : 1 ≤ s) (p : ℕ → ℝ) : mean (poi s p ⟨0, hs⟩) = p 1 := by
  simp [poi, th_29_140]

/-- ch29-155 (定 の行の補助): b = p_2。 -/
theorem th_29_155 (s : ℕ) (hs : 2 ≤ s) (p : ℕ → ℝ) : mean (poi s p ⟨1, hs⟩) = p 2 := by
  simp [poi, th_29_140]

/-- ch29-156 (定 の行の補助): a_1 = p_1。 -/
theorem th_29_156 (s : ℕ) (hs : 1 ≤ s) (p : ℕ → ℝ) : mean2 (poi s p ⟨0, hs⟩) = p 1 := by
  simp [poi, th_29_142]

/-- ch29-157 (定 の行の補助): b_1 = p_2。 -/
theorem th_29_157 (s : ℕ) (hs : 2 ≤ s) (p : ℕ → ℝ) : mean2 (poi s p ⟨1, hs⟩) = p 2 := by
  simp [poi, th_29_142]

/-- ch29-158 (記法の行の主張): 生起の回数が限界 Σp_λ ± a√(Σp_λ − Σp_λ²) の間にある確率は 1 − 1/a² より大きい
(各 0 ≤ p_λ ≤ 1、Σp_λ − Σp_λ² > 0、a > 1; Σ は λ = 1 から s まで)。 -/
theorem th_29_158 (s : ℕ) (p : ℕ → ℝ) (hp : ∀ l, 0 ≤ p l ∧ p l ≤ 1)
    (hV : 0 < ∑ l : Fin s, p (l.val + 1) - ∑ l : Fin s, p (l.val + 1) ^ 2) (a : ℝ) (ha : 1 < a) :
    ∑ κ ∈ univ.filter (fun κ => |Ssum (poi s p) κ - ∑ l : Fin s, p (l.val + 1)|
        ≤ a * √(∑ l : Fin s, p (l.val + 1) - ∑ l : Fin s, p (l.val + 1) ^ 2)), jp (poi s p) κ
      > 1 - 1 / a ^ 2 := by
  have hA : Atot (poi s p) = ∑ l : Fin s, p (l.val + 1) := by simp [Atot, poi, th_29_140]
  have hV' : Vt (poi s p) = ∑ l : Fin s, p (l.val + 1) - ∑ l : Fin s, p (l.val + 1) ^ 2 := by
    simp [Vt, poi, th_29_140, th_29_142]
  have h := th_29_tcheb (poi s p) (poi_N s p) (poi_P s p hp) a ha (by rw [hV']; exact hV)
  rwa [hA, hV'] at h

/-- ch29-161 (✎、F29.1): 印刷の「is greater than t − 1/a²」の t を §13 の定義 a = √n/t (130; n は量の個数で、ここでは
s) で読むと偽。s = 16、t = 2 なら a = √16/2 = 2 で t − 1/a² = 7/4 だが、確率は 1 を超えない (各 0 ≤ p_λ ≤ 1)。
t を 1 と読んだ修正形 1 − 1/a² は th_29_158。 -/
theorem nec_29_161 (p : ℕ → ℝ) (hp : ∀ l, 0 ≤ p l ∧ p l ≤ 1) :
    aT 16 2 = 2 ∧
      ¬ (∑ κ ∈ univ.filter (fun κ => |Ssum (poi 16 p) κ - ∑ l : Fin 16, p (l.val + 1)|
          ≤ aT 16 2 * √(∑ l : Fin 16, p (l.val + 1) - ∑ l : Fin 16, p (l.val + 1) ^ 2)), jp (poi 16 p) κ
        > 2 - 1 / aT 16 2 ^ 2) := by
  have ha : aT 16 2 = 2 := by
    unfold aT
    rw [show ((16 : ℕ) : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  refine ⟨ha, not_lt.mpr ?_⟩
  refine le_trans (jp_sum_le_one (poi 16 p) (poi_N 16 p) (poi_P 16 p hp) _) ?_
  rw [ha]; norm_num

/-- ch29-159 (記法の行の主張): Σp_λ − Σp_λ² = Σp_λ q_λ。 -/
theorem th_29_159 (s : ℕ) (p : ℕ → ℝ) :
    ∑ l : Fin s, p (l.val + 1) - ∑ l : Fin s, p (l.val + 1) ^ 2
      = ∑ l : Fin s, p (l.val + 1) * q (p (l.val + 1)) := by
  rw [← sum_sub_distrib]; exact sum_congr rfl (fun l _ => by unfold q; ring)

/-- ch29-160 の修正形 (F29.2): k = √(2Σp_λq_λ/s) (§8) なら a√(Σp_λq_λ) = ak√s/√2。 -/
theorem th_29_160_fix (a Q : ℝ) (s : ℕ) (hs : 0 < s) :
    a * √Q = a * √(2 * Q / s) * √s / √2 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [Real.sqrt_div' _ hs'.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have : (0 : ℝ) < √2 := by positivity
  have : (0 : ℝ) < √(s : ℝ) := Real.sqrt_pos.mpr hs'
  field_simp

/-- ch29-160 (F29.2): 印刷の限界 sp ± √2 ak√s の幅は a√(Σp_λq_λ) の 2 倍 (a ≠ 0、Σp_λq_λ > 0 なら一致しない)。 -/
theorem nec_29_160 (a Q : ℝ) (s : ℕ) (hs : 0 < s) (hQ : 0 < Q) (ha : a ≠ 0) :
    √2 * a * √(2 * Q / s) * √s = 2 * (a * √Q) ∧ √2 * a * √(2 * Q / s) * √s ≠ a * √Q := by
  have e : √2 * a * √(2 * Q / s) * √s = 2 * (a * √Q) := by
    rw [th_29_160_fix a Q s hs]
    have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : (0 : ℝ) < √2 := by positivity
    field_simp
    rw [h2]
  refine ⟨e, ?_⟩
  rw [e]
  have : 0 < √Q := Real.sqrt_pos.mpr hQ
  intro h
  have : a * √Q = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact ha h1
  · linarith

/-! ## §14 (folio 357): Tchebycheff (1846) の補足の結果 I.–III. (163〜170) -/

/-- ch29-164・169 (定): 但し書き m > s + 1。 -/
def provI (m s : ℝ) : Prop := m > s + 1

/-- ch29-166・170 (定): 但し書き n < s − 1。 -/
def provII (n s : ℝ) : Prop := n < s - 1

/-- ch29-163 の印刷形 (I.): 1/(2(m − s)) √(m(μ − m)/μ) (s/μ)^m ((μ − s)/(μ − m))^{μ−m+1}。 -/
noncomputable def tchI (μ m : ℕ) (s : ℝ) : ℝ :=
  1 / (2 * (m - s)) * √(m * (μ - m) / μ) * (s / μ) ^ m * ((μ - s) / (μ - m)) ^ (μ - m + 1)

/-- 二項の一般項は非負。 -/
theorem bterm_nonneg (m : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (k : ℕ) : 0 ≤ bterm m p k := by
  unfold bterm q
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- ch29-163 (記法の行、F29.5): 印刷の I. は第 2 因子を (s/μ)^m とするので偽になる。μ = 10 回、各回の確率 1/5
(s = 2)、m = 5 (但し書き m > s + 1 を満たす) で、少なくとも 5 回起こる確率は C(10, 5)(1/5)^5(4/5)^5 ≥ ·026 だが、
印刷の I. の値は 1/100 より小さい。 -/
theorem nec_29_163 :
    provI 5 2 ∧ tchI 10 5 2 < 1 / 100 ∧ 1 / 100 < bterm 10 (1 / 5) 5 ∧
      bterm 10 (1 / 5) 5 ≤ ∑ k ∈ (range 11).filter (fun k => 5 ≤ k), bterm 10 (1 / 5) k := by
  refine ⟨by unfold provI; norm_num, ?_, ?_, ?_⟩
  · unfold tchI
    have hs : √((5 : ℕ) * ((10 : ℕ) - (5 : ℕ)) / (10 : ℕ) : ℝ) < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hpos : 0 ≤ √((5 : ℕ) * ((10 : ℕ) - (5 : ℕ)) / (10 : ℕ) : ℝ) := Real.sqrt_nonneg _
    generalize √((5 : ℕ) * ((10 : ℕ) - (5 : ℕ)) / (10 : ℕ) : ℝ) = A at hs hpos
    norm_num
    nlinarith
  · have c : Nat.choose 10 5 = 252 := by decide
    simp only [bterm, q, c]; norm_num
  · exact single_le_sum (f := fun k => bterm 10 (1 / 5) k)
      (fun k _ => bterm_nonneg 10 (by norm_num) (by norm_num) k) (by simp)

/-- ch29-165 の印刷形 (II.): 1/(2(s − n)) √(μ(μ − n)/μ) ((μ − s)/(μ − n))^{μ−n} (s/n)^{n+1}。 -/
noncomputable def tchII (μ n : ℕ) (s : ℝ) : ℝ :=
  1 / (2 * (s - n)) * √(μ * (μ - n) / μ) * ((μ - s) / (μ - n)) ^ (μ - n) * (s / n) ^ (n + 1)

/-- I. を III. の形 (因子 (s/m)^m) で読み、起こらない回数に写した形 (m ↦ μ − n、s ↦ μ − s): 根号は √(n(μ − n)/μ)
(III. の第 2 行の根号と同じ)。 -/
noncomputable def tchIIsym (μ n : ℕ) (s : ℝ) : ℝ :=
  1 / (2 * (s - n)) * √(n * (μ - n) / μ) * ((μ - s) / (μ - n)) ^ (μ - n) * (s / n) ^ (n + 1)

/-- ch29-166 の但し書き provII を前提に取る (F29.5 の II.): n < s − 1、n ≥ 1、s < μ なら、印刷の II. は I. を起こらない
回数に写した形以上 (根号 √(μ(μ − n)/μ) ≥ √(n(μ − n)/μ); 但し書きは因子 1/(2(s − n)) の正に要る)。印刷の II. は
写した形より弱い上界で、写した形が成り立てば印刷の II. も成り立つ (I.・II. そのものは証明していない)。 -/
theorem th_29_165_cmp (μ n : ℕ) (s : ℝ) (hII : provII n s) (hn : 1 ≤ n) (hsμ : s < μ) :
    tchIIsym μ n s ≤ tchII μ n s := by
  unfold provII at hII
  unfold tchIIsym tchII
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnμ : (n : ℝ) < μ := by linarith
  have hμ : (0 : ℝ) < μ := by linarith
  have hA : 0 ≤ 1 / (2 * (s - n)) := by
    have : 0 < s - n := by linarith
    positivity
  have hB : 0 ≤ ((μ - s) / (μ - n) : ℝ) ^ (μ - n) := by
    apply pow_nonneg; apply div_nonneg <;> linarith
  have hD : 0 ≤ (s / n : ℝ) ^ (n + 1) := by
    apply pow_nonneg; apply div_nonneg <;> linarith
  have hr : √(n * (μ - n) / μ : ℝ) ≤ √(μ * (μ - n) / μ : ℝ) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff_of_pos_right hμ]
    exact mul_le_mul_of_nonneg_right hnμ.le (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hr hA
  have h2 := mul_le_mul_of_nonneg_right h1 hB
  exact mul_le_mul_of_nonneg_right h2 hD

/-! ## §16 (folio 359–360): Simmons の定理と表 (178〜190) -/

/-- ch29-186 (定): p = 1/(a + 1)。 -/
noncomputable def pS (a : ℝ) : ℝ := 1 / (a + 1)

/-- ch29-187 (定): m = n(a + 1)。 -/
def mS (n a : ℕ) : ℕ := n * (a + 1)

/-- Δ: m 回の試行で頻度が c (= pm) より小さい確率から大きい確率を引いた値。 -/
noncomputable def deltaS (m : ℕ) (p : ℝ) (c : ℕ) : ℝ :=
  ∑ k ∈ range c, bterm m p k - ∑ k ∈ (range (m + 1)).filter (fun k => c < k), bterm m p k

theorem bterm_sum_one (m : ℕ) (p : ℝ) : ∑ k ∈ range (m + 1), bterm m p k = 1 := by
  have h := add_pow p (q p) m
  rw [show p + q p = 1 by unfold q; ring, one_pow] at h
  rw [h]
  exact sum_congr rfl (fun k _ => by unfold bterm; ring)

/-- Δ = 2Σ_{k<c} + (c の項) − 1 (c ≤ m)。 -/
theorem deltaS_eq (m : ℕ) (p : ℝ) (c : ℕ) (hc : c ≤ m) :
    deltaS m p c = 2 * ∑ k ∈ range c, bterm m p k + bterm m p c - 1 := by
  have hsplit := sum_filter_add_sum_filter_not (range (m + 1)) (fun k => c < k) (bterm m p)
  rw [bterm_sum_one] at hsplit
  have hf : (range (m + 1)).filter (fun k => ¬ c < k) = range (c + 1) := by
    ext k; simp only [mem_filter, mem_range]; omega
  rw [hf, sum_range_succ] at hsplit
  unfold deltaS
  linarith

/-- ch29-178 (未: 数値 9 点の検算のみ、一般の証明なし): 差 Δ は n = 1 で最大で、n とともに減る。a = 2 (p = 1/3)、
a = 3 (p = 1/4)、a = 9 (p = 1/10) で n = 1, 2, 3 (m = n(a + 1)) の 9 点を厳密に計算して確かめるだけで、一般の n、a の
証明ではない。 -/
theorem th_29_178 :
    deltaS 6 (1 / 3) 2 < deltaS 3 (1 / 3) 1 ∧ deltaS 9 (1 / 3) 3 < deltaS 6 (1 / 3) 2 ∧
      deltaS 8 (1 / 4) 2 < deltaS 4 (1 / 4) 1 ∧ deltaS 12 (1 / 4) 3 < deltaS 8 (1 / 4) 2 ∧
      deltaS 20 (1 / 10) 2 < deltaS 10 (1 / 10) 1 ∧ deltaS 30 (1 / 10) 3 < deltaS 20 (1 / 10) 2 := by
  have c1 : Nat.choose 6 1 = 6 := by decide
  have c2 : Nat.choose 6 2 = 15 := by decide
  have c3 : Nat.choose 9 1 = 9 := by decide
  have c4 : Nat.choose 9 2 = 36 := by decide
  have c5 : Nat.choose 9 3 = 84 := by decide
  have c6 : Nat.choose 8 1 = 8 := by decide
  have c7 : Nat.choose 8 2 = 28 := by decide
  have c8 : Nat.choose 12 1 = 12 := by decide
  have c9 : Nat.choose 12 2 = 66 := by decide
  have c10 : Nat.choose 12 3 = 220 := by decide
  have c11 : Nat.choose 20 1 = 20 := by decide
  have c12 : Nat.choose 20 2 = 190 := by decide
  have c13 : Nat.choose 30 1 = 30 := by decide
  have c14 : Nat.choose 30 2 = 435 := by decide
  have c15 : Nat.choose 30 3 = 4060 := by decide
  have c16 : Nat.choose 3 1 = 3 := by decide
  have c17 : Nat.choose 4 1 = 4 := by decide
  have c18 : Nat.choose 10 1 = 10 := by decide
  simp only [deltaS_eq _ _ _ (by norm_num : 1 ≤ 3), deltaS_eq _ _ _ (by norm_num : 2 ≤ 6),
    deltaS_eq _ _ _ (by norm_num : 3 ≤ 9), deltaS_eq _ _ _ (by norm_num : 1 ≤ 4),
    deltaS_eq _ _ _ (by norm_num : 2 ≤ 8), deltaS_eq _ _ _ (by norm_num : 3 ≤ 12),
    deltaS_eq _ _ _ (by norm_num : 1 ≤ 10), deltaS_eq _ _ _ (by norm_num : 2 ≤ 20),
    deltaS_eq _ _ _ (by norm_num : 3 ≤ 30), sum_range_succ, sum_range_zero, bterm, q,
    c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
    Nat.choose_zero_right]
  norm_num

/-- ch29-187 の表 (記法の行に付く数値、数値評価): Simmons の Δ の値を印刷の桁で検算する (印刷は切り捨て; 差は
印刷の最後の桁の数単位以内)。p = 1/3 (m = 3, 15, 24)、1/4 (m = 4, 20)、1/10 (m = 10, 20)、1/100 (m = 200)、
1/1000 (m = 1000)。 -/
theorem th_29_187_table :
    |deltaS 3 (1 / 3) 1 - 37037 / 10 ^ 6| < 1 / 10 ^ 6 ∧
      |deltaS 15 (1 / 3) 5 - 2243662 / 10 ^ 8| < 1 / 10 ^ 8 ∧
      |deltaS 24 (1 / 3) 8 - 182706 / 10 ^ 7| < 2 / 10 ^ 7 ∧
      |deltaS 4 (1 / 4) 1 - 54687 / 10 ^ 6| < 1 / 10 ^ 6 ∧
      |deltaS 20 (1 / 4) 5 - 3201413 / 10 ^ 8| < 3 / 10 ^ 8 ∧
      |deltaS 10 (1 / 10) 1 - 84777 / 10 ^ 6| < 1 / 10 ^ 6 ∧
      |deltaS 20 (1 / 10) 2 - 68673713 / 10 ^ 9| < 1 / 10 ^ 7 ∧
      |deltaS 200 (1 / 100) 2 - 81324387 / 10 ^ 9| < 1 / 10 ^ 8 := by
  have d1 : Nat.choose 15 1 = 15 := by decide
  have d2 : Nat.choose 15 2 = 105 := by decide
  have d3 : Nat.choose 15 3 = 455 := by decide
  have d4 : Nat.choose 15 4 = 1365 := by decide
  have d5 : Nat.choose 15 5 = 3003 := by decide
  have e1 : Nat.choose 24 1 = 24 := by decide
  have e2 : Nat.choose 24 2 = 276 := by decide
  have e3 : Nat.choose 24 3 = 2024 := by decide
  have e4 : Nat.choose 24 4 = 10626 := by decide
  have e5 : Nat.choose 24 5 = 42504 := by decide
  have e6 : Nat.choose 24 6 = 134596 := by decide
  have e7 : Nat.choose 24 7 = 346104 := by decide
  have e8 : Nat.choose 24 8 = 735471 := by decide
  have f1 : Nat.choose 20 1 = 20 := by decide
  have f2 : Nat.choose 20 2 = 190 := by decide
  have f3 : Nat.choose 20 3 = 1140 := by decide
  have f4 : Nat.choose 20 4 = 4845 := by decide
  have f5 : Nat.choose 20 5 = 15504 := by decide
  have g1 : Nat.choose 200 1 = 200 := by simp
  have g2 : Nat.choose 200 2 = 19900 := by rw [Nat.choose_two_right]
  have h1 : Nat.choose 3 1 = 3 := by decide
  have h2 : Nat.choose 4 1 = 4 := by decide
  have h3 : Nat.choose 10 1 = 10 := by decide
  simp only [deltaS_eq _ _ _ (by norm_num : 1 ≤ 3), deltaS_eq _ _ _ (by norm_num : 5 ≤ 15),
    deltaS_eq _ _ _ (by norm_num : 8 ≤ 24), deltaS_eq _ _ _ (by norm_num : 1 ≤ 4),
    deltaS_eq _ _ _ (by norm_num : 5 ≤ 20), deltaS_eq _ _ _ (by norm_num : 1 ≤ 10),
    deltaS_eq _ _ _ (by norm_num : 2 ≤ 20), deltaS_eq _ _ _ (by norm_num : 2 ≤ 200),
    sum_range_succ, sum_range_zero, bterm, q, d1, d2, d3, d4, d5, e1, e2, e3, e4, e5, e6, e7, e8,
    f1, f2, f3, f4, f5, g1, g2, h1, h2, h3, Nat.choose_zero_right]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> norm_num

/-- ch29-187 の表 (n = 1、p = 1/1000、m = 1000; 数値評価): Δ = 2q^m + mpq^{m−1} − 1 は ·103454 (印刷の桁で)。 -/
theorem th_29_187_table_1000 : |deltaS 1000 (1 / 1000) 1 - 103454 / 10 ^ 6| < 1 / 10 ^ 6 := by
  rw [deltaS_eq _ _ _ (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, bterm, q, Nat.choose_one_right, Nat.choose_zero_right]
  set_option exponentiation.threshold 1100 in
  rw [abs_lt]; constructor <;> norm_num

/-- ch29-187 の表 8 行目 (F29.9): p = 1/100、m = 100 の Δ は ·101794 . . . で、印刷の ·101813 と 10⁻⁵ 以上違う。 -/
theorem nec_29_187_table : 1 / 10 ^ 5 < |deltaS 100 (1 / 100) 1 - 101813 / 10 ^ 6| := by
  rw [deltaS_eq _ _ _ (by norm_num)]
  simp only [sum_range_succ, sum_range_zero, bterm, q, Nat.choose_one_right, Nat.choose_zero_right]
  rw [lt_abs]; right; norm_num

/-- 頻度が c より大きい確率と小さい確率。 -/
noncomputable def probGt (m : ℕ) (p : ℝ) (c : ℕ) : ℝ :=
  ∑ k ∈ (range (m + 1)).filter (fun k => c < k), bterm m p k

noncomputable def probLt (m : ℕ) (p : ℝ) (c : ℕ) : ℝ := ∑ k ∈ range c, bterm m p k

theorem probGt_eq (m : ℕ) (p : ℝ) (c : ℕ) (hc : c ≤ m) :
    probGt m p c = 1 - ∑ k ∈ range c, bterm m p k - bterm m p c := by
  have := deltaS_eq m p c hc
  unfold deltaS at this; unfold probGt; linarith

/-- ch29-189 (定: 例の前提 p = 1/4 を前提 hp に写す; 検算): 4 回ずつ 100 組で、最確値 1 を超える組は 26
(100 · 67/256 = 26·17)、下回る組は 31 (100 · 81/256 = 31·64; 印刷は端数を切り捨てた数)。 -/
theorem th_29_189 (p : ℝ) (hp : p = 1 / 4) :
    (26 : ℝ) ≤ 100 * probGt 4 p 1 ∧ 100 * probGt 4 p 1 < 27 ∧
      (31 : ℝ) ≤ 100 * probLt 4 p 1 ∧ 100 * probLt 4 p 1 < 32 := by
  subst hp
  rw [probGt_eq _ _ _ (by norm_num)]
  simp only [probLt, sum_range_succ, sum_range_zero, bterm, q, Nat.choose_one_right,
    Nat.choose_zero_right]
  norm_num

/-- ch29-190 (定: 例の前提 p = 1/10 を前提 hp に写す; 検算): 10 回ずつ 100 組で、超える組は 26 (26·39)、
下回る組は 34 (34·87; 切り捨て)。 -/
theorem th_29_190 (p : ℝ) (hp : p = 1 / 10) :
    (26 : ℝ) ≤ 100 * probGt 10 p 1 ∧ 100 * probGt 10 p 1 < 27 ∧
      (34 : ℝ) ≤ 100 * probLt 10 p 1 ∧ 100 * probLt 10 p 1 < 35 := by
  subst hp
  rw [probGt_eq _ _ _ (by norm_num)]
  simp only [probLt, sum_range_succ, sum_range_zero, bterm, q, Nat.choose_one_right,
    Nat.choose_zero_right]
  norm_num

/-! ## §12 (folio 351–352): Czuber の出生数の例 (089〜095) -/

/-- ch29-089 (定): m = 4,311,076 (男の出生数、1866–1877)。 -/
def mB : ℕ := 4311076

/-- ch29-090 (定): n = 4,052,193 (女の出生数)。 -/
def nB : ℕ := 4052193

/-- ch29-092 (定): m′ = 6,533,961 (1877–1899 の男の出生数)。 -/
def mB' : ℕ := 6533961

/-- ch29-091 (数値評価): s = m + n = 8,363,269。 -/
theorem th_29_091 : mB + nB = 8363269 := by norm_num [mB, nB]

/-- ch29-093 (✎): n_0′ = nm′/m は 6,141,592·27 . . . で、印刷の 6,141,587 ではない。 -/
theorem nec_29_093 : ((nB : ℝ) * mB') / mB ≠ 6141587 := by
  norm_num [mB, nB, mB']

/-- ch29-093 の修正形 (✎): 6,141,592 < nm′/m < 6,141,593。 -/
theorem th_29_093_fix : (6141592 : ℝ) < (nB : ℝ) * mB' / mB ∧ (nB : ℝ) * mB' / mB < 6141593 := by
  norm_num [mB, nB, mB']

/-- 限界 6,118,361 と 6,164,813 は 6,141,587 ± 23,226 (印刷の中心値の両側に等しい幅)。 -/
theorem th_29_094_limits : (6141587 : ℤ) - 23226 = 6118361 ∧ (6141587 : ℤ) + 23226 = 6164813 := by
  norm_num

/-- Czuber の分散の読み (推定、印刷にない): nm′s(m + m′)/m³。 -/
noncomputable def czV : ℝ := (nB : ℝ) * mB' * (mB + nB) * (mB + mB') / (mB : ℝ) ^ 3

/-- 094 の γ (推定の読み): 幅 23,226 = √(2V) γ とすると γ は 3 にきわめて近い (2·9998 < γ < 2·9999)。
P = ·9999779 は Θ(3) の表の値 (Lean では検算していない)。 -/
theorem th_29_094_gamma : (29998 / 10000 : ℝ) < 23226 / √(2 * czV) ∧ 23226 / √(2 * czV) < 29999 / 10000 := by
  have hV : 0 < 2 * czV := by unfold czV; norm_num [mB, nB, mB']
  have hs : 0 < √(2 * czV) := Real.sqrt_pos.mpr hV
  constructor
  · rw [lt_div_iff₀ hs]
    have : √(2 * czV) < 23226 / (29998 / 10000) := by
      rw [Real.sqrt_lt' (by norm_num)]; unfold czV; norm_num [mB, nB, mB']
    have h2 : (29998 / 10000 : ℝ) * (23226 / (29998 / 10000)) = 23226 := by norm_num
    nlinarith
  · rw [div_lt_iff₀ hs]
    have : 23226 / (29999 / 10000) < √(2 * czV) := by
      rw [Real.lt_sqrt (by norm_num)]; unfold czV; norm_num [mB, nB, mB']
    have h2 : (29999 / 10000 : ℝ) * (23226 / (29999 / 10000)) = 23226 := by norm_num
    nlinarith

/-- ch29-094 (外部公理依存): ax_normal_approx の当てはめ (p = n/s、γ = 3) のみ。二項分布で |k − mp| < √(2mpq) · 3 と
なる確率は m → ∞ で Θ(3)。Czuber の問題 (m′ を与えたときの n′ の中心 nm′/m と限界) は模型化していない。γ = 3 の読みは
th_29_094_gamma (推定の分散による数値評価)、Θ(3) = ·9999779 は表の値で検算していない。 -/
theorem th_29_094 :
    Tendsto (fun m : ℕ => probWithin m (nB / (mB + nB)) (√(2 * mpq m (nB / (mB + nB))) * 3)) atTop
      (𝓝 (Θ 3)) :=
  ax_normal_approx _ (by norm_num [mB, nB]) (by norm_num [mB, nB]) 3 (by norm_num)

/-- ch29-095 (数値評価): ·9999779 = 1 − 1/45250 (印刷の 7 桁で; 1 − 1/45250 = ·99997790055 . . .)。 -/
theorem th_29_095 : |(9999779 / 10 ^ 7 : ℝ) - (1 - 1 / 45250)| < 1 / (2 * 10 ^ 7) := by
  rw [abs_lt]; constructor <;> norm_num

end KeynesXXIXd

/-! ## #print axioms -/
#print axioms KeynesXXIXd.evalB
#print axioms KeynesXXIXd.Taut
#print axioms KeynesXXIXd.interp
#print axioms KeynesXXIXd.itrue_certain
#print axioms KeynesXXIXd.true_conj
#print axioms KeynesXXIXd.th_13_1_i
#print axioms KeynesXXIXd.taut_neg_zero
#print axioms KeynesXXIXd.conj_neg_cert_zero
#print axioms KeynesXXIXd.th_12_i_short
#print axioms KeynesXXIXd.subst_taut
#print axioms KeynesXXIXd.x
#print axioms KeynesXXIXd.pr_false
#print axioms KeynesXXIXd.pr_or_excl
#print axioms KeynesXXIXd.cond_mul
#print axioms KeynesXXIXd.cond_mul_not
#print axioms KeynesXXIXd.x_zero
#print axioms KeynesXXIXd.GenSucc
#print axioms KeynesXXIXd.φ
#print axioms KeynesXXIXd.th_29_086
#print axioms KeynesXXIXd.rf
#print axioms KeynesXXIXd.rf_pos
#print axioms KeynesXXIXd.phiP
#print axioms KeynesXXIXd.th_29_086_sol
#print axioms KeynesXXIXd.th_29_086_closed
#print axioms KeynesXXIXd.x_true_zero
#print axioms KeynesXXIXd.rel_cons_gensucc_trivial
#print axioms KeynesXXIXd.y
#print axioms KeynesXXIXd.x_diag
#print axioms KeynesXXIXd.gensucc_succ
#print axioms KeynesXXIXd.th_29_086_data
#print axioms KeynesXXIXd.th_29_086_closed_data
#print axioms KeynesXXIXd.Mag
#print axioms KeynesXXIXd.mean
#print axioms KeynesXXIXd.mean2
#print axioms KeynesXXIXd.th_29_111
#print axioms KeynesXXIXd.th_29_112
#print axioms KeynesXXIXd.var_one
#print axioms KeynesXXIXd.th_29_114
#print axioms KeynesXXIXd.th_29_115
#print axioms KeynesXXIXd.th_29_116
#print axioms KeynesXXIXd.dev_zero
#print axioms KeynesXXIXd.jp
#print axioms KeynesXXIXd.Ssum
#print axioms KeynesXXIXd.Atot
#print axioms KeynesXXIXd.Vt
#print axioms KeynesXXIXd.marg1
#print axioms KeynesXXIXd.marg2
#print axioms KeynesXXIXd.th_29_113
#print axioms KeynesXXIXd.th_29_117
#print axioms KeynesXXIXd.th_29_119
#print axioms KeynesXXIXd.nec_29_119
#print axioms KeynesXXIXd.ratio
#print axioms KeynesXXIXd.Pt
#print axioms KeynesXXIXd.term_eq
#print axioms KeynesXXIXd.jp_nonneg
#print axioms KeynesXXIXd.jp_sum_le_one
#print axioms KeynesXXIXd.ratio_nonneg
#print axioms KeynesXXIXd.th_29_120
#print axioms KeynesXXIXd.th_29_121_fix
#print axioms KeynesXXIXd.th_29_124
#print axioms KeynesXXIXd.th_29_125
#print axioms KeynesXXIXd.ratio_le_one_iff
#print axioms KeynesXXIXd.th_29_tcheb
#print axioms KeynesXXIXd.aT
#print axioms KeynesXXIXd.th_29_130
#print axioms KeynesXXIXd.th_29_133
#print axioms KeynesXXIXd.cexM
#print axioms KeynesXXIXd.sum_fin1
#print axioms KeynesXXIXd.nec_29_121
#print axioms KeynesXXIXd.q
#print axioms KeynesXXIXd.gainMag
#print axioms KeynesXXIXd.gains
#print axioms KeynesXXIXd.gains_N
#print axioms KeynesXXIXd.gains_P
#print axioms KeynesXXIXd.gains_A
#print axioms KeynesXXIXd.gains_V
#print axioms KeynesXXIXd.th_29_135
#print axioms KeynesXXIXd.indMag
#print axioms KeynesXXIXd.th_29_140
#print axioms KeynesXXIXd.th_29_142
#print axioms KeynesXXIXd.bern
#print axioms KeynesXXIXd.bern_N
#print axioms KeynesXXIXd.bern_P
#print axioms KeynesXXIXd.th_29_144
#print axioms KeynesXXIXd.th_29_145
#print axioms KeynesXXIXd.th_29_147
#print axioms KeynesXXIXd.th_29_148
#print axioms KeynesXXIXd.bterm
#print axioms KeynesXXIXd.mpq
#print axioms KeynesXXIXd.Θ
#print axioms KeynesXXIXd.probWithin
#print axioms KeynesXXIXd.th_29_149
#print axioms KeynesXXIXd.th_29_152
#print axioms KeynesXXIXd.nec_29_152
#print axioms KeynesXXIXd.poi
#print axioms KeynesXXIXd.poi_N
#print axioms KeynesXXIXd.poi_P
#print axioms KeynesXXIXd.th_29_154
#print axioms KeynesXXIXd.th_29_155
#print axioms KeynesXXIXd.th_29_156
#print axioms KeynesXXIXd.th_29_157
#print axioms KeynesXXIXd.th_29_158
#print axioms KeynesXXIXd.nec_29_161
#print axioms KeynesXXIXd.th_29_159
#print axioms KeynesXXIXd.th_29_160_fix
#print axioms KeynesXXIXd.nec_29_160
#print axioms KeynesXXIXd.provI
#print axioms KeynesXXIXd.provII
#print axioms KeynesXXIXd.tchI
#print axioms KeynesXXIXd.bterm_nonneg
#print axioms KeynesXXIXd.nec_29_163
#print axioms KeynesXXIXd.tchII
#print axioms KeynesXXIXd.tchIIsym
#print axioms KeynesXXIXd.th_29_165_cmp
#print axioms KeynesXXIXd.pS
#print axioms KeynesXXIXd.mS
#print axioms KeynesXXIXd.deltaS
#print axioms KeynesXXIXd.bterm_sum_one
#print axioms KeynesXXIXd.deltaS_eq
#print axioms KeynesXXIXd.th_29_178
#print axioms KeynesXXIXd.th_29_187_table
#print axioms KeynesXXIXd.th_29_187_table_1000
#print axioms KeynesXXIXd.nec_29_187_table
#print axioms KeynesXXIXd.probGt
#print axioms KeynesXXIXd.probLt
#print axioms KeynesXXIXd.probGt_eq
#print axioms KeynesXXIXd.th_29_189
#print axioms KeynesXXIXd.th_29_190
#print axioms KeynesXXIXd.mB
#print axioms KeynesXXIXd.nB
#print axioms KeynesXXIXd.mB'
#print axioms KeynesXXIXd.th_29_091
#print axioms KeynesXXIXd.nec_29_093
#print axioms KeynesXXIXd.th_29_093_fix
#print axioms KeynesXXIXd.th_29_094_limits
#print axioms KeynesXXIXd.czV
#print axioms KeynesXXIXd.th_29_094_gamma
#print axioms KeynesXXIXd.th_29_094
#print axioms KeynesXXIXd.th_29_095
