/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 9x
#
# 新井一成・Claude共著、2026年10月18日
# **第17章 §3–§12 (Folio 194–214): 誤差法則と最確値 — 1911 JRSS 論文の再録部分**
#
# ## 対象
#   Keynes (1911) "The Principal Averages and the Laws of Error which Lead to Them",
#   JRSS vol. lxxiv pp. 322–331 の番号 (1)–(12), (i)–(vi), (a)–(e)、無番号の前提式
#   U1–U9、および 1921 加筆層 N0–N8 (台帳_1911番号.md の 41 行)。
#
# ## 基準
#   1921 Macmillan 初版の頁画像 (原典照合1921/img/folio_194–214.png) が唯一の基準。
#   第 1 回 (2026-10-18) は Folio 194–198 を 1911 JRSS 画像 + Gutenberg tex で代替したが、
#   第 2 回 (2026-10-20) に folio_194–198.png を画像で照合し、U1–U9, (i)-1〜6, (ii)-1〜4 の
#   folio 番号と印刷形を本ヘッダ・各 docstring に反映した。1911 画像と tex は補助。
#
# ## 担体
#   §3–§4 (U1–U7) は KeynesI 担体 (IProp, PrI; phase6c と同形の公理) の上で、
#   §5–§7 の誤差法則は U8 の代数関数 f : ℝ → ℝ → ℝ の上で形式化する。
#   `Prop → Prop → ℝ` 型の確率関係は新設しない (CLAUDE.md 不変条件 3)。
#   U8 が両者の接点: x_q/a_s h = f(y_q, b_s)。
#   公理のうち def_IX_i・ax_range_lo_i・ax_range_hi_i・inot は phase6c と同形の公理系を
#   保つために宣言するが、U1–U7 の証明は Def.X の左右二形だけで閉じるので使わない
#   (範囲 0 < f_q < 1 は第 II 部で (v)-2 の実関数版の仮定として入力化する)。
#   itrue は空連言 (m = 0 の iconj) の値にのみ使う。連言の長さ m で帰納する U4・U5・U6 は
#   0 < m を仮定する。U2 系 (U2_src, U2_corrected) は iconj m x を一つの命題として U1 に
#   渡すだけなので m を仮定しない (m = 0 なら itrue についての U1 になる)。
#   def_X_right_i の必要性は反例モデル (th_17_1911_U1_needs_X_right) で示す。
#
# ## 原典の記法 (ToP 1921)
#   真値候補 b_s、命題 a_s (真値は b_s)、測定値 y_q、命題 x_q (測定値 y_q を得た)、
#   一般証拠 h、最確値 y、絶対誤差 z_q = |y − y_q|、誤差法則 f_q = f(y_q, y)。
#   本ファイルでは最確値の変数を t と書く (Lean の束縛変数の衝突回避)。
#
# ## 1921 印刷と Gutenberg tex の相違 (画像に従った箇所)
#   F200 (ii)-8 : tex `k^2el` → 印刷 k²e^l           (Lean: e^l)
#   F203 (v)   : tex 「= 0」欠落 → 印刷 Σθ(y_q,y) = 0  (Lean: = 0)
#   F203 (vi)  : tex 指数 2 → 印刷 (y−y_q)⁴          (Lean: 4 乗)
#   F203 (vi)  : tex `A/(y−y_q) = 0` → 印刷 A/(y−y_q)^{2k²}
#   F204 (5)   : tex `φ'(y−y_q)` → 印刷 φ'(y)(y−y_q)
#   F205 (10)  : 印刷に dy なし (tex 校訂者が補完) — 意味に影響なし
#   F208 N5    : tex 「=」 → 印刷 「≠」                  (Lean: ≠ を反例で)
#
# ## 原著側の誤り候補 (印刷形の機械反駁 + 修正形)
#   F200 (iii)-3 : 1921 印刷は e^{(k²/y_q)(y−y_q)²} (負号欠落; 1911 p.328 と (11) F205 は負号あり)
#   F200 (ii)-9  : 「∫φ₁'(z)/z dz = φ(log z)」は符号が逆 (1911 p.327 も同じ)。
#                  Keynes 自身の例 φ(l)=k²e^l で反駁できる
#   F200 (ii)-9  : T-3 — 幾何法則の指数の積分項が印刷では ∫φ₁(z)/z dz (プライム欠落)。
#                  直後の where 行は ∫φ₁'(z)/z dz と印刷されており、同じ頁内で不整合。
#                  Lean は where 行の φ₁' を採る (th_17_1911_ii_9_src の hΦ)
#   F195 U2      : Σ の上限 「r = x」 (1911 p.323 と同じ誤植; 1921 印刷 F195 で確認。
#                  F194 の U1 は r = n と正しく印刷)
#   F198 (ii)-4  : 「最も簡単な幾何法則」の k が (8) F205 では k² (両版同じ)。
#                  F200 の (ii)-8 書き出し「simplest geometric law」も k² — 1921 内部で
#                  F198 と F200 が既に不整合
#   F198 (ii)-3  : 対称条件の右辺が印刷では φ(y−y_q)² (φ の使い回し; (i)-6 F198 は θ)。
#                  Lean は θ に置換 (T 候補; th_17_1911_ii_3_src)
#   F197 (i)-4   : f_q = e^{φ'(y)(y−y_q)−φ(y)+ψ(y_q)} と A なしで印刷、(5) F204 は A あり。
#                  Lean は A ありの一本 (th_17_1911_5_src; A は ψ に吸収できる)
#   F202 (iv)-6  : Laplace の結果式が印刷では φ(z) = (m/2)e^{−my} (z = φ(y) と定義した直後)
#   F207 N2      : Maclaurin 展開の左辺が印刷では φ(x) (右辺は z)
#
# ## 原文が証明なしに断言した命題の証明 (所見候補)
#   (ii)-3 F198 「which is impossible」: th_17_1911_ii_3_impossible (φ'' ≡ 0 に限る)
#   (i)-2  F197 「∴ f'_q/f_q = φ''(y)(y−y_q)」: th_17_1911_i_2_src (全データ同値 + 連続性で正当化)
#   (iv)-2 F201 Fechner の性質: th_17_1911_iv_2_src (個数条件の中央値で証明)
#   (vi)-4 F203 対数型の法則は 0 < f_q < 1 に反する: th_17_1911_vi_4_exceeds_one
#
# ## 実行方法
#   lake env lean phases/keynes_part_ii_phase9x.lean
-/

import Mathlib

open Classical

/-! # 第 I 部: KeynesI 担体 — §4 の逆確率と独立乗法 (U1–U7) -/

namespace KeynesI

/-! ## 内包的キャリアと公理 (phase6c と同形、本ファイルで使う分) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom itrue : IProp
axiom PrI : IProp → IProp → ℝ

axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1

/-! ## U1 (p.323 / F194): 単一測定の事後確率 — 逆確率の定理

原文: a_s/x_p h = (x_p/a_s h · a_s/h) / Σ_{r=1}^{n} (x_p/a_r h · a_r/h)。
前提 hexh は「a_1,…,a_n が h に相対的に排反かつ網羅」の帰結 x_p/h = Σ_r x_p a_r/h
(第14章 (25) 全確率; phase7g th_14_25_src) を入力化したもの。
分母 ≠ 0 は原文が暗黙に仮定する。F194 にこの点の脚注はない。F196 脚注 2
「実際になされた測定が不可能であることはないので f(y_q, y) は 0 にならない」は
f(y_q, y) ≠ 0 についての注で、U1 の分母 Σ_r x_p/a_r h · a_r/h を直接は言っていない
(分母 = x_p/h は hexh から従う量で、その非零は別途の仮定 hD)。 -/
theorem th_17_1911_U1_src {n : ℕ} (a : Fin n → IProp) (xp h : IProp) (s : Fin n)
    (hexh : PrI xp h = ∑ r, PrI (iand xp (a r)) h)
    (hD : (∑ r, PrI xp (iand (a r) h) * PrI (a r) h) ≠ 0) :
    PrI (a s) (iand xp h)
      = PrI xp (iand (a s) h) * PrI (a s) h
        / ∑ r, PrI xp (iand (a r) h) * PrI (a r) h := by
  have hDx : (∑ r, PrI xp (iand (a r) h) * PrI (a r) h) = PrI xp h := by
    rw [hexh]
    exact Finset.sum_congr rfl (fun r _ => (def_X_left_i xp (a r) h).symm)
  have hl := def_X_left_i xp (a s) h
  have hr := def_X_right_i xp (a s) h
  rw [hDx] at hD ⊢
  rw [eq_div_iff hD, ← hr]
  exact hl

/-! ## U1 の必要性: Def.X 右形 (def_X_right_i) を満たさないモデルでは U1 が破れる

反例モデル: 担体 Bool、連言 cxAnd p q := p (左射影)、cxP p h := g p / g h (g true = 2, g false = 1)。
このモデルは Def.X 左形 P(pq/h) = P(p/qh)·P(q/h) を全 p, q, h で満たすが、右形
P(pq/h) = P(q/ph)·P(p/h) は p ≠ q で破れる。n = 1, a_1 = false, x_p = true, h = false で
U1 の前提 (網羅 hexh と分母 ≠ 0) は成り立つのに、U1 の結論は 1/2 ≠ 1 で偽。
U2 (U2_corrected) は U1 に帰着する (iconj m x を一つの命題として U1 を適用するだけ) ので、
def_X_right_i の必要性は U2 についても同じ反例に帰着する。U5・U6 はさらに U4 と
IndepGiven を経由するので、本反例モデルは直接には扱わない (U5・U6 での必要性は未証明)。
(範囲 0 ≤ P ≤ 1 もこのモデルでは破れるが、U1 の証明は範囲公理を使わないので
反例の妨げにならない。) -/

/-- 反例モデルの連言 (左射影)。 -/
def cxAnd (p _ : Bool) : Bool := p

/-- 反例モデルの確率関係 g p / g h。 -/
noncomputable def cxP (p h : Bool) : ℝ := (if p then 2 else 1) / (if h then 2 else 1)

/-- 反例モデルの真値候補 (n = 1, a_1 = false)。 -/
def cxA : Fin 1 → Bool := fun _ => false

theorem th_17_1911_U1_needs_X_right :
    (∀ p q h, cxP (cxAnd p q) h = cxP p (cxAnd q h) * cxP q h)
    ∧ (∃ p q h, cxP (cxAnd p q) h ≠ cxP q (cxAnd p h) * cxP p h)
    ∧ (cxP true false = ∑ r, cxP (cxAnd true (cxA r)) false)
    ∧ ((∑ r, cxP true (cxAnd (cxA r) false) * cxP (cxA r) false) ≠ 0)
    ∧ (cxP (cxA 0) (cxAnd true false)
        ≠ cxP true (cxAnd (cxA 0) false) * cxP (cxA 0) false
          / ∑ r, cxP true (cxAnd (cxA r) false) * cxP (cxA r) false) := by
  refine ⟨?_, ⟨true, false, false, ?_⟩, ?_, ?_, ?_⟩
  · intro p q h
    cases p <;> cases q <;> cases h <;> norm_num [cxAnd, cxP]
  · norm_num [cxAnd, cxP]
  · norm_num [cxAnd, cxP, cxA]
  · norm_num [cxAnd, cxP, cxA]
  · norm_num [cxAnd, cxP, cxA]

/-! ## 測定の連言と「独立」(U3) -/

/-- m 個の測定命題の連言 x_1 x_2 … x_m。印刷の添字 q = 1 … m は Lean の Fin m の
0 … m−1 に対応 (x_q = x ⟨q−1, _⟩)。m = 0 の空連言は itrue とする。
連言の長さで帰納する U4 と、それを使う U5・U6 は 0 < m を仮定する。
U2 系 (U2_src, U2_corrected) は iconj m x を一つの命題として扱うので m を仮定しない。 -/
noncomputable def iconj : (m : ℕ) → (Fin m → IProp) → IProp
  | 0, _ => itrue
  | 1, x => x 0
  | m+2, x => iand (x 0) (iconj (m+1) (Fin.tail x))

/-- **U3 (p.323 / F195)** 真値既知の下での測定の「独立」(Keynes の意味):
x_r/x_p…x_s a_r h = x_r/a_r h。先頭の測定が残りの連言に相対的に無関連、の連鎖形。
前提 (b) に対応。 -/
def IndepGiven (H : IProp) : (m : ℕ) → (Fin m → IProp) → Prop
  | 0, _ => True
  | 1, _ => True
  | m+2, x => PrI (x 0) (iand (iconj (m+1) (Fin.tail x)) H) = PrI (x 0) H
      ∧ IndepGiven H (m+1) (Fin.tail x)

/-- **U4 (p.324 / F195)** 独立乗法: x_1…x_m/a_s h = Π_{q=1}^{q=m} x_q/a_s h。
第14章の乗法定理 (Def.X 左形) を連言の長さで帰納 (0 < m)。 -/
theorem th_17_1911_U4_src (H : IProp) :
    ∀ (m : ℕ), 0 < m → ∀ (x : Fin m → IProp), IndepGiven H m x →
      PrI (iconj m x) H = ∏ q, PrI (x q) H
  | 0, hm, _, _ => absurd hm (lt_irrefl 0)
  | 1, _, x, _ => by simp [iconj]
  | m+2, _, x, hind => by
      obtain ⟨h0, hrest⟩ := hind
      rw [iconj, def_X_left_i, h0,
        th_17_1911_U4_src H (m+1) (Nat.succ_pos m) (Fin.tail x) hrest]
      conv_rhs => rw [Fin.prod_univ_succ]
      rfl

/-- **U2 修正形 (p.323 / F195)** m 個の測定の事後確率 (修正形: Σ の上限 r = n)。
測定 x_1 … x_m は Fin m (印刷と同じ m 個)。印刷形 (上限 r = x) は th_17_1911_U2_src。 -/
theorem th_17_1911_U2_corrected {n m : ℕ} (a : Fin n → IProp) (x : Fin m → IProp)
    (h : IProp) (s : Fin n)
    (hexh : PrI (iconj m x) h = ∑ r, PrI (iand (iconj m x) (a r)) h)
    (hD : (∑ r, PrI (iconj m x) (iand (a r) h) * PrI (a r) h) ≠ 0) :
    PrI (a s) (iand (iconj m x) h)
      = PrI (iconj m x) (iand (a s) h) * PrI (a s) h
        / ∑ r, PrI (iconj m x) (iand (a r) h) * PrI (a r) h :=
  th_17_1911_U1_src a (iconj m x) h s hexh hD

/-- **U2 印刷形 (p.323 / F195)**: 分母の Σ の上限が「r = x」と印刷されている
(1911・tex とも; 1921 印刷 F195 で確認。x は測定命題であって数ではない)。
上限を任意の自然数 N と読んだ印刷形は、省かれた項の和が 0 である場合に限って成り立つ:
  (事後確率 = 分子 / Σ_{r<N}) ⟺ Σ_{r<N} = Σ_{r<n}。
したがって印刷形が正しいのは N = n (修正形 th_17_1911_U2_corrected) の読みのときに限る。 -/
theorem th_17_1911_U2_src {n m : ℕ} (a : Fin n → IProp) (x : Fin m → IProp)
    (h : IProp) (s : Fin n) (N : ℕ)
    (hexh : PrI (iconj m x) h = ∑ r, PrI (iand (iconj m x) (a r)) h)
    (hD : (∑ r, PrI (iconj m x) (iand (a r) h) * PrI (a r) h) ≠ 0)
    (hDN : (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val < N),
              PrI (iconj m x) (iand (a r) h) * PrI (a r) h) ≠ 0)
    (hNum : PrI (iconj m x) (iand (a s) h) * PrI (a s) h ≠ 0) :
    (PrI (a s) (iand (iconj m x) h)
        = PrI (iconj m x) (iand (a s) h) * PrI (a s) h
          / ∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val < N),
              PrI (iconj m x) (iand (a r) h) * PrI (a r) h)
      ↔ (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val < N),
            PrI (iconj m x) (iand (a r) h) * PrI (a r) h)
          = ∑ r, PrI (iconj m x) (iand (a r) h) * PrI (a r) h := by
  rw [th_17_1911_U2_corrected a x h s hexh hD, div_eq_div_iff hD hDN]
  constructor
  · intro hh
    exact mul_left_cancel₀ hNum hh
  · intro hh
    rw [hh]

/-- **U5 (p.324 / F195)** U2 に U4 を代入:
a_s/x_1…x_m h = (a_s/h · Π_q x_q/a_s h) / Σ_r [Π_q x_q/a_r h · a_r/h] (0 < m)。 -/
theorem th_17_1911_U5_src {n m : ℕ} (hm : 0 < m) (a : Fin n → IProp) (x : Fin m → IProp)
    (h : IProp) (s : Fin n)
    (hexh : PrI (iconj m x) h = ∑ r, PrI (iand (iconj m x) (a r)) h)
    (hind : ∀ r, IndepGiven (iand (a r) h) m x)
    (hD : (∑ r, (∏ q, PrI (x q) (iand (a r) h)) * PrI (a r) h) ≠ 0) :
    PrI (a s) (iand (iconj m x) h)
      = PrI (a s) h * (∏ q, PrI (x q) (iand (a s) h))
        / ∑ r, (∏ q, PrI (x q) (iand (a r) h)) * PrI (a r) h := by
  have hU4 : ∀ r, PrI (iconj m x) (iand (a r) h) = ∏ q, PrI (x q) (iand (a r) h) :=
    fun r => th_17_1911_U4_src (iand (a r) h) m hm x (hind r)
  have hD' : (∑ r, PrI (iconj m x) (iand (a r) h) * PrI (a r) h) ≠ 0 := by
    simpa only [hU4] using hD
  rw [th_17_1911_U2_corrected a x h s hexh hD']
  simp only [hU4]
  ring

/-- **U6 (p.324 / F196)** 一様事前 a_1/h = … = a_n/h (前提 (a)) の下での **U7**:
分母が共通なので、事後確率を最大にする s は尤度 Π_q x_q/a_s h を最大にする s。
post r = c · L r / D (c = 共通の事前確率 > 0, D = 分母 > 0) として、
「post が s で最大」⟺「L が s で最大」。 -/
theorem th_17_1911_U7_src {n : ℕ} (post L : Fin n → ℝ) (c D : ℝ)
    (hc : 0 < c) (hD : 0 < D) (hpost : ∀ r, post r = c * L r / D) (s : Fin n) :
    (∀ r, post r ≤ post s) ↔ (∀ r, L r ≤ L s) := by
  have key : ∀ r, post r ≤ post s ↔ L r ≤ L s := by
    intro r
    rw [hpost r, hpost s, div_le_div_iff_of_pos_right hD]
    constructor
    · intro hh
      exact le_of_mul_le_mul_left hh hc
    · intro hh
      exact mul_le_mul_of_nonneg_left hh hc.le
  exact forall_congr' key

/-- U6 を U5 に代入した形 (原文 F196「分子を最大にすればよい」): 一様事前の下で
事後確率 = c · Π_q x_q/a_s h / Σ_r [Π_q x_q/a_r h · c] (0 < m)。 -/
theorem th_17_1911_U6_src {n m : ℕ} (hm : 0 < m) (a : Fin n → IProp) (x : Fin m → IProp)
    (h : IProp) (s : Fin n) (c : ℝ)
    (hexh : PrI (iconj m x) h = ∑ r, PrI (iand (iconj m x) (a r)) h)
    (hind : ∀ r, IndepGiven (iand (a r) h) m x)
    (hU6 : ∀ r, PrI (a r) h = c)
    (hD : (∑ r, (∏ q, PrI (x q) (iand (a r) h)) * c) ≠ 0) :
    PrI (a s) (iand (iconj m x) h)
      = c * (∏ q, PrI (x q) (iand (a s) h))
        / ∑ r, (∏ q, PrI (x q) (iand (a r) h)) * c := by
  have hD' : (∑ r, (∏ q, PrI (x q) (iand (a r) h)) * PrI (a r) h) ≠ 0 := by
    simpa only [hU6] using hD
  rw [th_17_1911_U5_src hm a x h s hexh hind hD']
  simp only [hU6]

end KeynesI

/-! # 第 II 部: 誤差法則 f(y_q, y) と最確値 (U8–U9, (i)–(vi), (1)–(12))

U8 (p.324 / F196, 前提 (c)(e)): x_q/a_s h = f(y_q, b_s)。f は既知の代数関数。
以下、f を実関数 f : ℝ → ℝ → ℝ (第1引数 = 測定値 y_q, 第2引数 = 真値 t) とし、
尤度 Π_q f(y_q, t) の最大化を扱う。 -/

namespace KeynesLawOfError

/-- **最確値**: 対数尤度 ℓ を領域 S の上で最大にする t。 -/
def IsMostProbable (ℓ : ℝ → ℝ) (S : Set ℝ) (t : ℝ) : Prop :=
  t ∈ S ∧ ∀ s ∈ S, ℓ s ≤ ℓ t

/-- 算術平均 (1/m)Σ y_q。 -/
noncomputable def amean {m : ℕ} (y : Fin m → ℝ) : ℝ := (∑ q, y q) / m

/-- 幾何平均 (Π y_q)^{1/m}。 -/
noncomputable def gmean {m : ℕ} (y : Fin m → ℝ) : ℝ := (∏ q, y q) ^ ((1 : ℝ) / m)

/-- 調和平均 m / Σ(1/y_q)。 -/
noncomputable def hmean {m : ℕ} (y : Fin m → ℝ) : ℝ := m / ∑ q, (y q)⁻¹

/-- **(iv)-1 (p.328 / F200–201)** 中央値 (順序統計の定義を個数条件で言い換えたもの):
c 以下の測定値が半数以上、かつ c 以上の測定値が半数以上。m 奇数なら第 (m+1)/2 番目、
m 偶数なら第 m/2 番目と第 m/2+1 番目の間の全値がこれを満たす。 -/
def IsMedian {m : ℕ} (y : Fin m → ℝ) (c : ℝ) : Prop :=
  m ≤ 2 * (Finset.univ.filter (fun q => y q ≤ c)).card
    ∧ m ≤ 2 * (Finset.univ.filter (fun q => c ≤ y q)).card

/-! ## U9 (p.324 / F196): 尤度の対数微分 = 0 — 最確値の方程式

原文: 「Π f(y_q, y) を最大にする y を求める。微分係数を 0 とおいて Σ f'(y_q,y)/f(y_q,y) = 0」。
F196 脚注 2: 実際になされた測定が不可能であることはないので f(y_q, y) は 0 にならない
(hpos の根拠。U1 の分母については言っていない)。
前提 (d) (連続近似) は、t が実数区間を動き f が微分可能、という形で入力化する。
証明するのは原文が用いる向き: 局所最大 ⇒ 停留 (Fermat)。逆向き (停留 ⇒ 最大) の
議論は原文に無い (台帳【観察】)。 -/
theorem th_17_1911_U9_src {m : ℕ} (f f' : ℝ → ℝ → ℝ) (y : Fin m → ℝ) (t : ℝ)
    (hpos : ∀ q s, 0 < f (y q) s)
    (hder : ∀ q, HasDerivAt (fun s => f (y q) s) (f' (y q) t) t)
    (hmax : IsLocalMax (fun s => ∏ q, f (y q) s) t) :
    ∑ q, f' (y q) t / f (y q) t = 0 := by
  -- 対数尤度 Σ log f_q も t で局所最大 (log は単調)
  have hlog : IsLocalMax (fun s => ∑ q, Real.log (f (y q) s)) t := by
    have h1 : IsLocalMax (fun s => Real.log (∏ q, f (y q) s)) t :=
      hmax.mono (fun s hs =>
        Real.log_le_log (Finset.prod_pos (fun q _ => hpos q s)) hs)
    have h2 : (fun s => Real.log (∏ q, f (y q) s)) = fun s => ∑ q, Real.log (f (y q) s) := by
      funext s
      exact Real.log_prod (fun q _ => (hpos q s).ne')
    rwa [h2] at h1
  -- 対数尤度の微分 = Σ f'_q/f_q
  have hd : HasDerivAt (fun s => ∑ q, Real.log (f (y q) s))
      (∑ q, f' (y q) t / f (y q) t) t := by
    have := HasDerivAt.sum (u := Finset.univ)
      (A := fun q s => Real.log (f (y q) s))
      (A' := fun q => f' (y q) t / f (y q) t) (x := t)
      (fun q _ => (hder q).log (hpos q t).ne')
    convert this using 1
    funext s
    simp [Finset.sum_apply]
  exact hlog.hasDerivAt_eq_zero hd

/-! ## (v)-1 = (1) (p.329–331 / F203–204): 誤差法則の最一般形

原文 (1): f_q = A e^{∫φ''(y)θ(y_q,y)dy + ψ(y_q)} は Σθ(y_q, y) = 0 を導く。
形式化: 指数 E_q(t) の微分が c·θ_q (c = φ''(t) ≠ 0) なら、対数尤度の停留条件は Σθ_q = 0 と同値。
**最一般性 ("the most general form") は境界記録**: この定理は「この形 ⇒ 停留条件 ⟺ Σθ = 0」の
十分性のみを述べる。逆向き (Σθ = 0 を導く法則はすべてこの形) には追加原理
((i)-2 型の全データ同値 + 連続性; th_17_1911_i_2_src) が要り、本定理には含めない
(台帳 5-2 の指摘どおり)。(5)(7)(10)(12) も同じ。 -/
theorem th_17_1911_1_src {m : ℕ} (A c : ℝ) (E : Fin m → ℝ → ℝ) (θ : Fin m → ℝ) (t : ℝ)
    (hA : 0 < A) (hc : c ≠ 0) (hE : ∀ q, HasDerivAt (E q) (c * θ q) t) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (E q s))) t = 0 ↔ ∑ q, θ q = 0 := by
  have hfun : (fun s => ∑ q, Real.log (A * Real.exp (E q s)))
      = fun s => ∑ q, (Real.log A + E q s) := by
    funext s
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hd : HasDerivAt (fun s => ∑ q, (Real.log A + E q s)) (∑ q, (0 + c * θ q)) t := by
    have := HasDerivAt.sum (u := Finset.univ) (A := fun q s => Real.log A + E q s)
      (A' := fun q => 0 + c * θ q) (x := t)
      (fun q _ => (hasDerivAt_const t (Real.log A)).add (hE q))
    convert this using 1
    funext s
    simp [Finset.sum_apply]
  rw [hfun, hd.deriv]
  simp only [zero_add, ← Finset.mul_sum]
  constructor
  · intro hh
    rcases mul_eq_zero.mp hh with h0 | h0
    · exact absurd h0 hc
    · exact h0
  · intro hh
    rw [hh, mul_zero]

/-! ## (i) 算術平均 (p.325 / F197) -/

/-- **(i)-1 (p.325 / F197)** Σ(y − y_q) = 0 ⟺ y = (1/m) Σ y_q。 -/
theorem th_17_1911_i_1_src {m : ℕ} (hm : 0 < m) (y : Fin m → ℝ) (t : ℝ) :
    (∑ q, (t - y q)) = 0 ↔ t = amean y := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold amean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, eq_div_iff hm']
  constructor
  · intro hh
    linarith
  · intro hh
    linarith

/-- **(i)-2 (p.325 / F197)** 「∴ f'_q/f_q = φ''(y)(y − y_q)」— 原文は Σ f'_q/f_q = 0 と
Σ(y − y_q) = 0 の同値から項ごとの比例を証明なしに導く (台帳【論理的飛躍】)。
**形式化の境界の記録**: この段は追加原理を要する。ここでは、その飛躍を埋める十分条件を
定理にする: g(y_q, t) := f'_q/f_q について
  (α) 同値が m = 2, 3 の**全データ**で成り立ち、(β) g が y_q について連続
ならば g(u, t) = c·(t − u), c ≠ 0 (c = φ''(t))。証明は (α) から Cauchy の関数方程式
G(v+w) = G(v) + G(w) を取り出し、(β) で線形性に落とす。
Keynes の前提 (c)「代数関数」は (β) を含意するので、原文の飛躍は (α) の読み
(「同値」を全データで要求する) の下では正当化される。 -/
theorem th_17_1911_i_2_src (g : ℝ → ℝ → ℝ) (t : ℝ)
    (hcont : Continuous (fun u => g u t))
    (h2 : ∀ y₁ y₂, g y₁ t + g y₂ t = 0 ↔ (t - y₁) + (t - y₂) = 0)
    (h3 : ∀ y₁ y₂ y₃, g y₁ t + g y₂ t + g y₃ t = 0
        ↔ (t - y₁) + (t - y₂) + (t - y₃) = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ u, g u t = c * (t - u) := by
  -- G(v) := g(t − v, t)
  set G : ℝ → ℝ := fun v => g (t - v) t with hG
  have hGcont : Continuous G := hcont.comp (continuous_const.sub continuous_id)
  have hodd : ∀ v, G (-v) = -G v := by
    intro v
    have := (h2 (t - v) (t - (-v))).mpr (by ring)
    simp only [hG] at this ⊢
    linarith
  have hadd : ∀ v w, G (v + w) = G v + G w := by
    intro v w
    have := (h3 (t - v) (t - w) (t - (-(v + w)))).mpr (by ring)
    have h' := hodd (v + w)
    simp only [hG] at this h' ⊢
    linarith
  -- 連続な加法写像は線形
  let Gh : ℝ →+ ℝ := AddMonoidHom.mk' G hadd
  have hlin : ∀ v, G v = v * G 1 := by
    intro v
    have := map_real_smul Gh hGcont v 1
    simpa [Gh, smul_eq_mul] using this
  refine ⟨G 1, ?_, ?_⟩
  · intro hzero
    have := (h2 (t - 1) (t - 1)).mp (by
      show g (t - 1) t + g (t - 1) t = 0
      have h1 : g (t - 1) t = G 1 := rfl
      rw [h1, hzero]; ring)
    norm_num at this
  · intro u
    have : g u t = G (t - u) := by simp [hG]
    rw [this, hlin]
    ring

/-- **(i)-3 (p.325 / F197)** ∫φ''(y)(y − y_q)dy = φ'(y)(y − y_q) − φ(y) (微分形)。 -/
theorem th_17_1911_i_3_src (φ φ' φ'' : ℝ → ℝ) (yq t : ℝ)
    (h1 : HasDerivAt φ (φ' t) t) (h2 : HasDerivAt φ' (φ'' t) t) :
    HasDerivAt (fun s => φ' s * (s - yq) - φ s) (φ'' t * (t - yq)) t := by
  have key : HasDerivAt (fun s => φ' s * (s - yq) - φ s)
      ((φ'' t * (t - yq) + φ' t * 1) - φ' t) t :=
    (h2.mul ((hasDerivAt_id' t).sub_const yq)).sub h1
  convert key using 1
  ring

/-- **(i)-4 = (5) (p.325, 331 / F197, 204)** 算術平均を導く最一般形:
f_q = A e^{φ'(y)(y − y_q) − φ(y) + ψ(y_q)} の停留条件は Σ(y − y_q) = 0 (φ''(y) ≠ 0)。
印刷 F197 の (i)-4 は f_q = e^{φ'(y)(y−y_q)−φ(y)+ψ(y_q)} と A なし、(5) F204 は A あり。
本定理は両者を A ありの一本にまとめたもの (A は ψ(y_q) に log A として吸収できる;
F197 の (i)-5 がまさに ψ(y_q) = −k²y_q² + log A と置く)。
印刷 F204 は φ'(y)(y − y_q) (tex は引数 (y) 欠落)。
**最一般性は境界記録**: 「この形 ⇒ 停留条件 ⟺ Σ(y−y_q) = 0」の十分性のみ。最一般性
(逆向き) には追加原理 ((i)-2 型の全データ同値 + 連続性; th_17_1911_i_2_src) が要る。 -/
theorem th_17_1911_5_src {m : ℕ} (A : ℝ) (φ φ' φ'' ψ : ℝ → ℝ) (y : Fin m → ℝ) (t : ℝ)
    (hA : 0 < A) (h1 : HasDerivAt φ (φ' t) t) (h2 : HasDerivAt φ' (φ'' t) t)
    (hne : φ'' t ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (φ' s * (s - y q) - φ s + ψ (y q)))) t = 0
      ↔ ∑ q, (t - y q) = 0 := by
  refine th_17_1911_1_src A (φ'' t) (fun q s => φ' s * (s - y q) - φ s + ψ (y q))
    (fun q => t - y q) t hA hne (fun q => ?_)
  exact (th_17_1911_i_3_src φ φ' φ'' (y q) t h1 h2).add_const (ψ (y q))

/-- **(i)-5 = (3) の導出 (p.325 / F197)** φ(y) = −k²y², ψ(y_q) = −k²y_q² + log A を (5) に代入:
指数の恒等式 −2k²y(y − y_q) + k²y² − k²y_q² = −k²(y − y_q)²。 -/
theorem th_17_1911_i_5_src (k t yq : ℝ) :
    (-2 * k^2 * t) * (t - yq) - (-(k^2) * t^2) + (-(k^2) * yq^2) = -(k^2) * (t - yq)^2 := by
  ring

/-- (i)-5 の法則形: A e^{上の指数} = A e^{−k²(y−y_q)²} = A e^{−k² z_q²}, z_q = |y − y_q|。 -/
theorem th_17_1911_i_5_law (A k t yq : ℝ) :
    A * Real.exp ((-2 * k^2 * t) * (t - yq) - (-(k^2) * t^2) + (-(k^2) * yq^2))
      = A * Real.exp (-(k^2) * |t - yq|^2) := by
  rw [th_17_1911_i_5_src, sq_abs]

/-- **(i)-6 (p.325–326 / F197–198)** 対称誤差 (SYM) の下で正規法則が算術平均を導く唯一の法則。
原文: φ'(y)(y−y_q) − φ(y) + ψ(y_q) = θ((y−y_q)²) を y で微分して φ''(y) = 2θ'((y−y_q)²);
φ'' は y_q に依らないから θ' は定数 −k²; 積分して θ(u) = −k²u + log C。
**形式化の境界の記録**: 「θ' が定数」の段は u = (y−y_q)² と y を独立に動かすことを要する。
ここでは θ の微分可能性を仮定し、その段を定理にする: 恒等式が全 y, y_q で成り立ち
θ が微分可能なら、θ'(u) は u ≥ 0 で定数 (= φ''(y)/2, したがって φ'' も定数)。 -/
theorem th_17_1911_i_6_src (φ φ' φ'' ψ θ θ' : ℝ → ℝ)
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (φ'' t) t)
    (hθ : ∀ u, HasDerivAt θ (θ' u) u)
    (hid : ∀ t yq, φ' t * (t - yq) - φ t + ψ yq = θ ((t - yq)^2)) :
    (∀ t yq, t ≠ yq → φ'' t = 2 * θ' ((t - yq)^2)) ∧ (∀ u v, 0 < u → 0 < v → θ' u = θ' v) := by
  have hdiff : ∀ t yq, t ≠ yq → φ'' t = 2 * θ' ((t - yq)^2) := by
    intro t yq hty
    -- 左辺 s ↦ φ'(s)(s−y_q) − φ(s) + ψ(y_q) の微分 = φ''(t)(t−y_q)
    have hL : HasDerivAt (fun s => φ' s * (s - yq) - φ s + ψ yq) (φ'' t * (t - yq)) t :=
      (th_17_1911_i_3_src φ φ' φ'' yq t (hφ t) (hφ' t)).add_const (ψ yq)
    -- 右辺 s ↦ θ((s−y_q)²) の微分 = θ'((t−y_q)²)·2(t−y_q)
    have hR : HasDerivAt (fun s => θ ((s - yq)^2))
        (θ' ((t - yq)^2) * (2 * (t - yq))) t := by
      have hin : HasDerivAt (fun s => (s - yq)^2) (2 * (t - yq)) t := by
        have := ((hasDerivAt_id' t).sub_const yq).pow 2
        convert this using 1
        ring
      exact (hθ _).comp t hin
    have hfun : (fun s => φ' s * (s - yq) - φ s + ψ yq) = fun s => θ ((s - yq)^2) := by
      funext s
      exact hid s yq
    rw [hfun] at hL
    have huniq := hL.unique hR
    -- (φ''(t) − 2θ'(u))(t − y_q) = 0 かつ t ≠ y_q
    have hmul : (φ'' t - 2 * θ' ((t - yq)^2)) * (t - yq) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h0 | h0
    · linarith
    · exact absurd (sub_eq_zero.mp h0) hty
  refine ⟨hdiff, fun u v hu hv => ?_⟩
  -- u = (0 − (−√u))², v = (0 − (−√v))² なので θ'(u) = φ''(0)/2 = θ'(v)
  have hsu := Real.sqrt_pos.mpr hu
  have hsv := Real.sqrt_pos.mpr hv
  have hu' := hdiff 0 (-Real.sqrt u) (by linarith)
  have hv' := hdiff 0 (-Real.sqrt v) (by linarith)
  rw [show (0 - -Real.sqrt u)^2 = u by rw [sub_neg_eq_add, zero_add, Real.sq_sqrt hu.le]] at hu'
  rw [show (0 - -Real.sqrt v)^2 = v by rw [sub_neg_eq_add, zero_add, Real.sq_sqrt hv.le]] at hv'
  linarith

/-- (i)-6 の結び: θ' が [0,∞) で定数 c なら θ(u) = c·u + θ(0) (u ≥ 0)。
原文の「積分して θ(u) = −k²u + log C」。c の符号 (−k²) は f_q ≤ 1 (範囲公理) から従う
(次の定理)。 -/
theorem th_17_1911_i_6_integrate (θ θ' : ℝ → ℝ) (c : ℝ)
    (hθ : ∀ u, HasDerivAt θ (θ' u) u) (hconst : ∀ u, 0 < u → θ' u = c) :
    ∀ u, 0 ≤ u → θ u = c * u + θ 0 := by
  intro u hu
  -- g(s) := θ(s) − c·s は (0, u) で微分 0、[0, u] で連続
  have hg : ∀ s, 0 < s → HasDerivAt (fun s => θ s - c * s) 0 s := by
    intro s hs
    have := (hθ s).sub ((hasDerivAt_id' s).const_mul c)
    rw [hconst s hs] at this
    convert this using 1
    ring
  rcases eq_or_lt_of_le hu with h0 | hpos
  · rw [← h0]; ring
  · have hcont : ContinuousOn (fun s => θ s - c * s) (Set.Icc 0 u) :=
      fun s _ => ((hθ s).sub ((hasDerivAt_id' s).const_mul c)).continuousAt.continuousWithinAt
    have hder : ∀ s ∈ Set.Ioo 0 u, HasDerivAt (fun s => θ s - c * s) 0 s :=
      fun s hs => hg s hs.1
    have := exists_hasDerivAt_eq_slope (fun s => θ s - c * s) (fun _ => 0) hpos hcont hder
    obtain ⟨ξ, _, hξ⟩ := this
    have h1 : ((θ u - c * u) - (θ 0 - c * 0)) / (u - 0) = 0 := hξ.symm
    rcases div_eq_zero_iff.mp h1 with h2 | h2
    · linarith
    · linarith

/-- (i)-6 の符号: f_q = B e^{θ(u)} ≤ 1 (範囲公理) かつ θ(u) = c·u + θ(0) (u ≥ 0) かつ B > 0
なら c ≤ 0。すなわち原文の −k² の負号は確率の範囲から従う。 -/
theorem th_17_1911_i_6_sign (B c θ0 : ℝ) (hB : 0 < B)
    (hle : ∀ u, 0 ≤ u → B * Real.exp (c * u + θ0) ≤ 1) : c ≤ 0 := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc
  exfalso
  -- u := (|θ0| + |log B| + 1)/c をとると指数 ≥ 1 − log B
  set u := (|θ0| + |Real.log B| + 1) / c with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 := hle u hu0
  have h2 : Real.log (B * Real.exp (c * u + θ0)) ≤ Real.log 1 :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at h2
  have h3 : c * u = |θ0| + |Real.log B| + 1 := by
    rw [hu]; field_simp
  have h4 := neg_abs_le (Real.log B)
  have h5 := neg_abs_le θ0
  linarith

/-! ## (ii) 幾何平均 (p.326–327 / F198–200) -/

/-- **(ii)-1 (p.326 / F198)** Σ log(y_q/y) = 0 ⟺ Π y_q = y^m ⟺ y = 幾何平均 (y, y_q > 0)。 -/
theorem th_17_1911_ii_1_src {m : ℕ} (hm : 0 < m) (y : Fin m → ℝ) (hy : ∀ q, 0 < y q)
    (t : ℝ) (ht : 0 < t) :
    ((∑ q, Real.log (y q / t)) = 0 ↔ ∏ q, y q = t ^ m)
      ∧ ((∑ q, Real.log (y q / t)) = 0 ↔ t = gmean y) := by
  have hprod : 0 < ∏ q, y q := Finset.prod_pos (fun q _ => hy q)
  have hsum : (∑ q, Real.log (y q / t)) = Real.log (∏ q, y q) - m * Real.log t := by
    rw [Real.log_prod (fun q _ => (hy q).ne')]
    simp_rw [Real.log_div (hy _).ne' ht.ne']
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · rw [hsum]
    constructor
    · intro hh
      have : Real.log (∏ q, y q) = Real.log (t ^ m) := by rw [Real.log_pow]; linarith
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hprod) (Set.mem_Ioi.mpr (pow_pos ht m)) this
    · intro hh
      rw [hh, Real.log_pow]; ring
  · rw [hsum]
    have hg : 0 < gmean y := Real.rpow_pos_of_pos hprod _
    have hlg : Real.log (gmean y) = Real.log (∏ q, y q) / m := by
      unfold gmean
      rw [Real.log_rpow hprod]
      ring
    constructor
    · intro hh
      have : Real.log t = Real.log (gmean y) := by
        rw [hlg]; field_simp; linarith
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr hg) this
    · intro hh
      rw [hh, hlg]; field_simp; ring

/-- **(ii)-2 = (7) (p.326, 331 / F198, 204)** 幾何平均を導く最一般形:
f_q = A e^{φ'(y) log(y_q/y) + ∫φ'(y)/y dy + ψ(y_q)} の停留条件は Σ log(y_q/y) = 0。
Φ は ∫φ'(y)/y dy (Φ' = φ'/y)。
**最一般性は境界記録**: 「この形 ⇒ 停留条件 ⟺ Σ log(y_q/y) = 0」の十分性のみ。最一般性
(逆向き) には追加原理 ((i)-2 型の全データ同値 + 連続性; th_17_1911_i_2_src) が要る。 -/
theorem th_17_1911_7_src {m : ℕ} (A : ℝ) (φ' φ'' Φ ψ : ℝ → ℝ) (y : Fin m → ℝ)
    (hy : ∀ q, 0 < y q) (t : ℝ) (ht : 0 < t)
    (hA : 0 < A) (h2 : HasDerivAt φ' (φ'' t) t) (hΦ : HasDerivAt Φ (φ' t / t) t)
    (hne : φ'' t ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (φ' s * Real.log (y q / s) + Φ s + ψ (y q)))) t = 0
      ↔ ∑ q, Real.log (y q / t) = 0 := by
  refine th_17_1911_1_src A (φ'' t) (fun q s => φ' s * Real.log (y q / s) + Φ s + ψ (y q))
    (fun q => Real.log (y q / t)) t hA hne (fun q => ?_)
  -- d/ds [φ'(s) log(y_q/s)] = φ''(s) log(y_q/s) − φ'(s)/s
  have hlog : HasDerivAt (fun s => Real.log (y q / s)) (-(1 / t)) t := by
    have : HasDerivAt (fun s => Real.log (y q) - Real.log s) (0 - t⁻¹) t :=
      (hasDerivAt_const t (Real.log (y q))).sub (Real.hasDerivAt_log ht.ne')
    have hfun : (fun s => Real.log (y q / s)) =ᶠ[nhds t] fun s => Real.log (y q) - Real.log s := by
      filter_upwards [lt_mem_nhds ht] with s hs
      rw [Real.log_div (hy q).ne' hs.ne']
    rw [show -(1 / t) = 0 - t⁻¹ by ring]
    exact this.congr_of_eventuallyEq hfun
  have key := ((h2.mul hlog).add hΦ).add_const (ψ (y q))
  convert key using 1
  field_simp
  ring

/-- **(ii)-3 (p.326 / F198)** 「幾何法則は対称条件と両立しない — which is impossible」。
原文は断言のみで証明なし。ここでは、原文が与える中間式
φ''(y) log(y_q/y) = d/dy θ((y−y_q)²) を微分形の定理として置く (恒等式の下で左辺の微分 = 右辺の微分)。
**印刷との差 (T 候補)**: 印刷 F198 は対称条件の右辺を φ(y−y_q)²、中間式の右辺を
d/dy φ(y−y_q)² と印刷する — 直前まで φ'(y) として使っている φ の使い回し。(i)-6 (F198 上段) は
同じ役割の関数を θ(y−y_q)² と書くので、Lean は θ に置換した。
不可能性そのもの (関数方程式の解は φ'' ≡ 0 に限る) は次の th_17_1911_ii_3_impossible で証明する。 -/
theorem th_17_1911_ii_3_src (φ' φ'' Φ ψ θ θ' : ℝ → ℝ) (yq t : ℝ) (ht : 0 < t) (hyq : 0 < yq)
    (h2 : HasDerivAt φ' (φ'' t) t) (hΦ : HasDerivAt Φ (φ' t / t) t)
    (hθ : HasDerivAt θ (θ' ((t - yq)^2)) ((t - yq)^2))
    (hid : ∀ s, φ' s * Real.log (yq / s) + Φ s + ψ yq = θ ((s - yq)^2)) :
    φ'' t * Real.log (yq / t) = θ' ((t - yq)^2) * (2 * (t - yq)) := by
  have hlog : HasDerivAt (fun s => Real.log (yq / s)) (0 - t⁻¹) t := by
    have : HasDerivAt (fun s => Real.log yq - Real.log s) (0 - t⁻¹) t :=
      (hasDerivAt_const t (Real.log yq)).sub (Real.hasDerivAt_log ht.ne')
    have hfun : (fun s => Real.log (yq / s)) =ᶠ[nhds t] fun s => Real.log yq - Real.log s := by
      filter_upwards [lt_mem_nhds ht] with s hs
      rw [Real.log_div hyq.ne' hs.ne']
    exact this.congr_of_eventuallyEq hfun
  have hL : HasDerivAt (fun s => φ' s * Real.log (yq / s) + Φ s + ψ yq)
      (φ'' t * Real.log (yq / t) + φ' t * (0 - t⁻¹) + φ' t / t) t :=
    ((h2.mul hlog).add hΦ).add_const (ψ yq)
  have hR : HasDerivAt (fun s => θ ((s - yq)^2)) (θ' ((t - yq)^2) * (2 * (t - yq))) t := by
    have hin : HasDerivAt (fun s => (s - yq)^2) (2 * (t - yq)) t := by
      have := ((hasDerivAt_id' t).sub_const yq).pow 2
      convert this using 1
      ring
    exact hθ.comp t hin
  have hfun : (fun s => φ' s * Real.log (yq / s) + Φ s + ψ yq) = fun s => θ ((s - yq)^2) := by
    funext s
    exact hid s
  rw [hfun] at hL
  have := hL.unique hR
  rw [← this]
  field_simp
  ring

/-- **(ii)-3 の不可能性の証明** (原文は「which is impossible」と断言するのみ)。
幾何平均を導く法則 (7) の指数が (y − y_q)² のみの関数 Θ((y−y_q)²) に等しい、すなわち
  φ'(y) log(y_q/y) + ∫φ'(y)/y dy + ψ(y_q) = Θ((y − y_q)²)  (全 y, y_q > 0)
が成り立つなら、φ'' ≡ 0 (y > 0)。したがって Keynes の要求「φ''(y) は 0 でない」(F197) の下では
解は存在しない — 原文の主張が成り立つ。
証明: (1) y_q = y とおいて ψ = Θ(0) − Φ。(2) 差 d = y_q − y を固定すると左辺は y について定数、
微分して φ''(y) log(y_q/y)·y_q + φ'(y) − φ'(y_q) = 0。(3) y と y_q を入れ替えて加えると
(y_q φ''(y) − y φ''(y_q)) log(y_q/y) = 0、ゆえに φ''(y) = C y。(4) (2) で y = 1 とおくと
φ'(y_q) = φ'(1) + C y_q log y_q、微分して φ''(y_q) = C(log y_q + 1) = C y_q、
y_q = 2 で C(1 − log 2) = 0、log 2 < 1 より C = 0。 -/
theorem th_17_1911_ii_3_impossible (φ' φ'' Φ ψ Θ : ℝ → ℝ)
    (hφ' : ∀ t, 0 < t → HasDerivAt φ' (φ'' t) t)
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (φ' t / t) t)
    (hid : ∀ s yq, 0 < s → 0 < yq →
      φ' s * Real.log (yq / s) + Φ s + ψ yq = Θ ((s - yq)^2)) :
    ∀ t, 0 < t → φ'' t = 0 := by
  -- (1) ψ(w) = Θ(0) − Φ(w)
  have hψ : ∀ w, 0 < w → ψ w = Θ 0 - Φ w := by
    intro w hw
    have := hid w w hw hw
    rw [div_self hw.ne', Real.log_one, mul_zero, zero_add, sub_self] at this
    norm_num at this
    linarith
  -- (2) 差を固定した恒等式の微分
  have hE1 : ∀ s w, 0 < s → 0 < w →
      φ'' s * Real.log (w / s) * w + (φ' s - φ' w) = 0 := by
    intro s w hs hw
    set d := w - s with hd
    have hsd : 0 < s + d := by rw [hd]; linarith
    have hpos : ∀ᶠ x in nhds s, 0 < x ∧ 0 < x + d := by
      have h1 : ∀ᶠ x in nhds s, 0 < x := lt_mem_nhds hs
      have h2 : ∀ᶠ x in nhds s, -d < x := lt_mem_nhds (by linarith : -d < s)
      filter_upwards [h1, h2] with x hx hxd
      exact ⟨hx, by linarith⟩
    -- x ↦ φ'(x) log((x+d)/x) + Φ(x) − Φ(x+d) は s の近傍で定数 Θ(d²) − Θ(0)
    have hconst : (fun x => φ' x * Real.log ((x + d) / x) + Φ x - Φ (x + d))
        =ᶠ[nhds s] fun _ => Θ (d^2) - Θ 0 := by
      filter_upwards [hpos] with x hx
      have := hid x (x + d) hx.1 hx.2
      rw [hψ (x + d) hx.2, show (x - (x + d))^2 = d^2 by ring] at this
      linarith
    have hderiv0 : HasDerivAt (fun x => φ' x * Real.log ((x + d) / x) + Φ x - Φ (x + d)) 0 s :=
      (hasDerivAt_const s (Θ (d^2) - Θ 0)).congr_of_eventuallyEq hconst
    -- 計算による微分
    have hlog : HasDerivAt (fun x => Real.log ((x + d) / x)) ((s + d)⁻¹ * 1 - s⁻¹) s := by
      have ha : HasDerivAt (fun x => Real.log (x + d)) ((s + d)⁻¹ * 1) s := by
        have := (Real.hasDerivAt_log hsd.ne').comp s ((hasDerivAt_id' s).add_const d)
        exact this
      have h1 : HasDerivAt (fun x => Real.log (x + d) - Real.log x) ((s + d)⁻¹ * 1 - s⁻¹) s :=
        ha.sub (Real.hasDerivAt_log hs.ne')
      have hfun : (fun x => Real.log ((x + d) / x))
          =ᶠ[nhds s] fun x => Real.log (x + d) - Real.log x := by
        filter_upwards [hpos] with x hx
        rw [Real.log_div hx.2.ne' hx.1.ne']
      exact h1.congr_of_eventuallyEq hfun
    have hΦd : HasDerivAt (fun x => Φ (x + d)) (φ' (s + d) / (s + d) * 1) s :=
      (hΦ (s + d) hsd).comp s ((hasDerivAt_id' s).add_const d)
    have hcalc : HasDerivAt (fun x => φ' x * Real.log ((x + d) / x) + Φ x - Φ (x + d))
        (φ'' s * Real.log ((s + d) / s) + φ' s * ((s + d)⁻¹ * 1 - s⁻¹) + φ' s / s
          - φ' (s + d) / (s + d) * 1) s :=
      (((hφ' s hs).mul hlog).add (hΦ s hs)).sub hΦd
    have huniq := hderiv0.unique hcalc
    rw [show s + d = w by rw [hd]; ring] at huniq
    have hs0 := hs.ne'
    have hw0 := hw.ne'
    have key : φ'' s * Real.log (w / s) * w + (φ' s - φ' w)
        = w * (φ'' s * Real.log (w / s) + φ' s * (w⁻¹ * 1 - s⁻¹) + φ' s / s - φ' w / w * 1) := by
      field_simp
      ring
    rw [key, ← huniq, mul_zero]
  -- (3) φ''(s)/s は定数
  set C := φ'' 1 with hCdef
  have hC : ∀ s, 0 < s → φ'' s = C * s := by
    intro s hs
    by_cases h1 : s = 1
    · rw [h1, hCdef]; ring
    · have e1 := hE1 s 1 hs one_pos
      have e2 := hE1 1 s one_pos hs
      rw [one_div, Real.log_inv] at e1
      rw [div_one] at e2
      have hlog : Real.log s ≠ 0 := by
        intro h0
        rcases Real.log_eq_zero.mp h0 with h | h | h
        · linarith
        · exact h1 h
        · linarith
      have key : (C * s - φ'' s) * Real.log s = 0 := by
        rw [hCdef]
        linear_combination e1 + e2
      rcases mul_eq_zero.mp key with h | h
      · linarith
      · exact absurd h hlog
  -- (4) φ'(w) = φ'(1) + C w log w、微分して φ''(w) = C(log w + 1)
  have hφ'form : ∀ w, 0 < w → φ' w = φ' 1 + C * w * Real.log w := by
    intro w hw
    have := hE1 1 w one_pos hw
    rw [div_one] at this
    rw [hCdef]
    linear_combination (-1 : ℝ) * this
  have hderiv_form : ∀ w, 0 < w → φ'' w = C * (Real.log w + 1) := by
    intro w hw
    have hfun : φ' =ᶠ[nhds w] fun x => φ' 1 + C * x * Real.log x := by
      filter_upwards [lt_mem_nhds hw] with x hx
      exact hφ'form x hx
    have hd : HasDerivAt (fun x => φ' 1 + C * x * Real.log x)
        (0 + (C * 1 * Real.log w + C * w * w⁻¹)) w :=
      (hasDerivAt_const w (φ' 1)).add
        (((hasDerivAt_id' w).const_mul C).mul (Real.hasDerivAt_log hw.ne'))
    have h2 : HasDerivAt φ' (0 + (C * 1 * Real.log w + C * w * w⁻¹)) w :=
      hd.congr_of_eventuallyEq hfun
    have := (hφ' w hw).unique h2
    rw [this]
    have hw0 := hw.ne'
    field_simp
    ring
  have hC0 : C = 0 := by
    have h1 := hC 2 (by norm_num)
    have h2 := hderiv_form 2 (by norm_num)
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    have h3 : C * (1 - Real.log 2) = 0 := by
      linear_combination h2 - h1
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · linarith
  intro t ht
  rw [hC t ht, hC0, zero_mul]

/-- **(ii)-4 印刷形 (p.326 / F198)** 最も簡単な幾何法則: φ'(y) = −ky, ψ = 0 ⇒
f_q = A (y/y_q)^{ky} e^{−ky}。印刷は k の 1 乗 (1911・1921 とも)。
指数の恒等式: −ky log(y_q/y) + ∫(−ky)/y dy = ky log(y/y_q) − ky。 -/
theorem th_17_1911_ii_4_src (A k t yq : ℝ) (ht : 0 < t) (hyq : 0 < yq) :
    A * Real.exp (-k * t * Real.log (yq / t) + (-k * t))
      = A * (t / yq) ^ (k * t) * Real.exp (-k * t) := by
  rw [Real.rpow_def_of_pos (div_pos ht hyq), Real.log_div ht.ne' hyq.ne',
    Real.log_div hyq.ne' ht.ne']
  simp only [mul_assoc]
  rw [← Real.exp_add]
  congr 2
  ring

/-- **(8) (p.331 / F205)** 結論の形: f_q = A (y/y_q)^{k²y} e^{−k²y} (k²; (ii)-4 の k と不整合)。
(ii)-4 の k を k² に置き換えたものと同一の族 — 両版共通の不整合は記号のみ。 -/
theorem th_17_1911_8_src (A k t yq : ℝ) (ht : 0 < t) (hyq : 0 < yq) :
    A * Real.exp (-(k^2) * t * Real.log (yq / t) + (-(k^2) * t))
      = A * (t / yq) ^ (k^2 * t) * Real.exp (-(k^2) * t) :=
  th_17_1911_ii_4_src A (k^2) t yq ht hyq

/-- (8) は幾何平均を導く: 指数 k²y log(y/y_q) − k²y の微分は −k² log(y_q/y)。
停留条件 ⟺ Σ log(y_q/y) = 0 (k ≠ 0)。(ii)-4 の k 版も同じ (k ≠ 0 なら)。 -/
theorem th_17_1911_8_leads_gmean {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (hy : ∀ q, 0 < y q)
    (t : ℝ) (ht : 0 < t) (hA : 0 < A) (hk : k ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * s * Real.log (y q / s) + (-(k^2) * s)))) t = 0
      ↔ ∑ q, Real.log (y q / t) = 0 := by
  have hk2 : -(k^2) ≠ 0 := by
    intro h0
    exact hk (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (neg_eq_zero.mp h0))
  refine th_17_1911_1_src A (-(k^2)) (fun q s => -(k^2) * s * Real.log (y q / s) + (-(k^2) * s))
    (fun q => Real.log (y q / t)) t hA hk2 (fun q => ?_)
  have hlog : HasDerivAt (fun s => Real.log (y q / s)) (0 - t⁻¹) t := by
    have : HasDerivAt (fun s => Real.log (y q) - Real.log s) (0 - t⁻¹) t :=
      (hasDerivAt_const t (Real.log (y q))).sub (Real.hasDerivAt_log ht.ne')
    have hfun : (fun s => Real.log (y q / s)) =ᶠ[nhds t] fun s => Real.log (y q) - Real.log s := by
      filter_upwards [lt_mem_nhds ht] with s hs
      rw [Real.log_div (hy q).ne' hs.ne']
    exact this.congr_of_eventuallyEq hfun
  have key := (((hasDerivAt_id' t).const_mul (-(k^2))).mul hlog).add
    ((hasDerivAt_id' t).const_mul (-(k^2)))
  convert key using 1
  field_simp
  ring

/-- **(ii)-5 = (9) (p.326–327, 331 / F199, 205)** McAlister の対数正規型:
対数 l_q = log y_q が正規法則に従う ⇒ f(y_q, y) = A e^{−k²(log y_q − log y)²} = A e^{−k²(log(y_q/y))²}。 -/
theorem th_17_1911_9_src (A k t yq : ℝ) (ht : 0 < t) (hyq : 0 < yq) :
    A * Real.exp (-(k^2) * (Real.log yq - Real.log t)^2)
      = A * Real.exp (-(k^2) * (Real.log (yq / t))^2) := by
  rw [Real.log_div hyq.ne' ht.ne']

/-- **(ii)-6 (p.327 / F199)** McAlister 法則が (7) の特殊形であること:
ψ(y_q) = −k²(log y_q)², φ'(y) = 2k² log y, ∫2k² log y / y dy = k²(log y)² を代入すると
指数は −k²(log(y_q/y))²。(恒等式部分) -/
theorem th_17_1911_ii_6_src (k t yq : ℝ) (ht : 0 < t) (hyq : 0 < yq) :
    2 * k^2 * Real.log t * Real.log (yq / t) + k^2 * (Real.log t)^2 + (-(k^2) * (Real.log yq)^2)
      = -(k^2) * (Real.log (yq / t))^2 := by
  rw [Real.log_div hyq.ne' ht.ne']
  ring

/-- (ii)-6 の解析部分: ∫ 2k² log y / y dy = k² (log y)² (微分形)。 -/
theorem th_17_1911_ii_6_int (k t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => k^2 * (Real.log s)^2) (2 * k^2 * Real.log t / t) t := by
  have := ((Real.hasDerivAt_log ht.ne').pow 2).const_mul (k^2)
  convert this using 1
  field_simp
  ring

/-- **(ii)-8 (p.327 / F200)** 幾何法則 (8) を l = log y, l_q = log y_q で書き直すと算術法則
f_q = A e^{k² e^l (l − l_q) − k² e^l} (印刷 F200 は e^l; tex は `el` に崩れ)。
これは (5) で φ(l) = k² e^l, ψ = 0 とおいたもの。 -/
theorem th_17_1911_ii_8_src (A k t yq : ℝ) (ht : 0 < t) (hyq : 0 < yq) :
    A * (t / yq) ^ (k^2 * t) * Real.exp (-(k^2) * t)
      = A * Real.exp (k^2 * Real.exp (Real.log t) * (Real.log t - Real.log yq)
          - k^2 * Real.exp (Real.log t)) := by
  rw [Real.rpow_def_of_pos (div_pos ht hyq), Real.log_div ht.ne' hyq.ne', Real.exp_log ht]
  simp only [mul_assoc]
  rw [← Real.exp_add]
  congr 2
  ring

/-- **補助** (ii)-8 の φ(l) = k²e^l が (5) の形を与えること: φ' = φ (微分の確認) と、
指数 φ'(l)(l − l_q) − φ(l) = k²e^l(l − l_q) − k²e^l (第 2 連言は rfl で閉じる表記合わせ)。 -/
theorem th_17_1911_ii_8_phi (k l lq : ℝ) :
    HasDerivAt (fun s => k^2 * Real.exp s) (k^2 * Real.exp l) l
      ∧ (k^2 * Real.exp l) * (l - lq) - k^2 * Real.exp l
          = k^2 * Real.exp l * (l - lq) - k^2 * Real.exp l :=
  ⟨(Real.hasDerivAt_exp l).const_mul (k^2), rfl⟩

/-- **(ii)-9 印刷形 (p.327 / F200)** 算術法則 ↔ 幾何法則の一般の変換:
y = log z, y_q = log z_q, 「∫φ₁'(z)/z dz = φ(log z)」, ψ₁(z_q) = ψ(log z_q)。
印刷の同定 ∫φ₁'(z)/z dz = φ(log z) は、微分すると φ₁'(z) = φ'(log z) を強いる。
**誤植 T-3 (F200)**: 幾何法則 f_q = A e^{φ₁'(z) log(z_q/z) + ∫φ₁(z)/z dz + ψ₁(z_q)} の指数の
積分項は印刷ではプライムなしの φ₁(z) (folio_200.png で確認)。直後の where 行は
∫φ₁'(z)/z dz と印刷されており、同じ頁内で不整合。Lean は where 行の φ₁' を採り、
hΦ : Φ₁' = φ₁'/z とする (指数の項を where 行が定義する、という読み)。 -/
theorem th_17_1911_ii_9_src (φ φ' φ₁' Φ₁ : ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (hφ : HasDerivAt φ (φ' (Real.log z)) (Real.log z))
    (hΦ : HasDerivAt Φ₁ (φ₁' z / z) z)
    (hprinted : ∀ w, 0 < w → Φ₁ w = φ (Real.log w)) :
    φ₁' z = φ' (Real.log z) := by
  have h1 : HasDerivAt (fun w => φ (Real.log w)) (φ' (Real.log z) * z⁻¹) z :=
    hφ.comp z (Real.hasDerivAt_log hz.ne')
  have hfun : Φ₁ =ᶠ[nhds z] fun w => φ (Real.log w) := by
    filter_upwards [lt_mem_nhds hz] with w hw
    exact hprinted w hw
  have h2 : HasDerivAt Φ₁ (φ' (Real.log z) * z⁻¹) z := h1.congr_of_eventuallyEq hfun
  have := hΦ.unique h2
  field_simp at this
  linarith

/-- **(ii)-9 印刷形の反駁 (F200)**: 印刷の同定「∫φ₁'(z)/z dz = φ(log z)」を仮定 hprinted として置く
(Φ₁ = ∫φ₁'(z)/z dz、すなわち Φ₁' = φ₁'/z が hΦ)。Keynes 自身の例 φ(l) = k²e^l ((ii)-8, F200),
ψ = ψ₁ = 0 について、この同定を満たす**任意の** Φ₁, φ₁' で、z = 1, z_q = e のとき
算術法則の指数 φ'(log z)(log z − log z_q) − φ(log z) = −2k² と
幾何法則の指数 φ₁'(z) log(z_q/z) + Φ₁(z) = 2k² は一致しない (k ≠ 0)。
φ₁'(1) = φ'(log 1) は th_17_1911_ii_9_src (印刷の同定 ⇒ φ₁'(z) = φ'(log z)) から得る。 -/
theorem th_17_1911_ii_9_printed_fails (k : ℝ) (hk : k ≠ 0) (φ₁' Φ₁ : ℝ → ℝ)
    (hΦ : ∀ z, 0 < z → HasDerivAt Φ₁ (φ₁' z / z) z)
    (hprinted : ∀ w, 0 < w → Φ₁ w = k^2 * Real.exp (Real.log w)) :
    ∃ z zq : ℝ, 0 < z ∧ 0 < zq ∧
      (k^2 * Real.exp (Real.log z)) * (Real.log z - Real.log zq) - k^2 * Real.exp (Real.log z)
        ≠ φ₁' z * Real.log (zq / z) + Φ₁ z := by
  refine ⟨1, Real.exp 1, one_pos, Real.exp_pos 1, ?_⟩
  have hφ : HasDerivAt (fun l => k^2 * Real.exp l) (k^2 * Real.exp (Real.log 1)) (Real.log 1) :=
    (Real.hasDerivAt_exp _).const_mul (k^2)
  have h1 : φ₁' 1 = k^2 * Real.exp (Real.log 1) :=
    th_17_1911_ii_9_src (fun l => k^2 * Real.exp l) (fun l => k^2 * Real.exp l) φ₁' Φ₁ 1
      one_pos hφ (hΦ 1 one_pos) hprinted
  rw [h1, hprinted 1 one_pos]
  simp only [Real.log_one, Real.exp_zero, Real.log_exp, div_one, mul_one, zero_sub]
  intro h
  have hk2 : k^2 = 0 := by linarith
  exact hk (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk2)

/-- **(ii)-9 修正形**: 符号を直せば恒等的に一致する。
φ₁'(z) := −φ'(log z), ∫φ₁'(z)/z dz := −φ(log z), ψ₁(z_q) := ψ(log z_q) のとき
φ'(y)(y − y_q) − φ(y) + ψ(y_q) = φ₁'(z) log(z_q/z) + ∫φ₁'(z)/z dz + ψ₁(z_q) (y = log z)。 -/
theorem th_17_1911_ii_9_corrected (φ φ' ψ : ℝ → ℝ) (z zq : ℝ) (hz : 0 < z) (hzq : 0 < zq) :
    φ' (Real.log z) * (Real.log z - Real.log zq) - φ (Real.log z) + ψ (Real.log zq)
      = (-φ' (Real.log z)) * Real.log (zq / z) + (-φ (Real.log z)) + ψ (Real.log zq) := by
  rw [Real.log_div hzq.ne' hz.ne']
  ring

/-- (ii)-9 修正形の整合: Φ₁(z) := −φ(log z) は Φ₁' = φ₁'/z (φ₁'(z) = −φ'(log z)) を満たす。 -/
theorem th_17_1911_ii_9_corrected_int (φ φ' : ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (hφ : HasDerivAt φ (φ' (Real.log z)) (Real.log z)) :
    HasDerivAt (fun w => -φ (Real.log w)) ((-φ' (Real.log z)) / z) z := by
  have := (hφ.comp z (Real.hasDerivAt_log hz.ne')).neg
  convert this using 1
  field_simp

/-! ## (iii) 調和平均 (p.328 / F200) -/

/-- **(iii)-1 (p.328 / F200)** Σ(1/y_q − 1/y) = 0 ⟺ y = m / Σ(1/y_q)。 -/
theorem th_17_1911_iii_1_src {m : ℕ} (hm : 0 < m) (y : Fin m → ℝ) (hy : ∀ q, 0 < y q)
    (t : ℝ) (ht : 0 < t) :
    (∑ q, ((y q)⁻¹ - t⁻¹)) = 0 ↔ t = hmean y := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hS : 0 < ∑ q, (y q)⁻¹ := by
    have : (0 : ℝ) < ∑ q, (y q)⁻¹ := by
      apply Finset.sum_pos (fun q _ => inv_pos.mpr (hy q))
      exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact this
  unfold hmean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, eq_div_iff hS.ne']
  constructor
  · intro hh
    have : (m : ℝ) * t⁻¹ = ∑ q, (y q)⁻¹ := by linarith
    rw [← this]
    field_simp
  · intro hh
    rw [← hh]
    field_simp
    ring

/-- **(iii)-2 = (10) (p.328, 331 / F200, 205)** 調和平均を導く最一般形:
f_q = A e^{φ'(y)[1/y_q − 1/y] − ∫φ'(y)/y² dy + ψ(y_q)} の停留条件は Σ(1/y_q − 1/y) = 0。
Φ は ∫φ'(y)/y² dy (Φ' = φ'/y²; 印刷 F205 は dy なし)。
**最一般性は境界記録**: 「この形 ⇒ 停留条件 ⟺ Σ(1/y_q − 1/y) = 0」の十分性のみ。最一般性
(逆向き) には追加原理 ((i)-2 型の全データ同値 + 連続性; th_17_1911_i_2_src) が要る。 -/
theorem th_17_1911_10_src {m : ℕ} (A : ℝ) (φ' φ'' Φ ψ : ℝ → ℝ) (y : Fin m → ℝ)
    (t : ℝ) (ht : 0 < t) (hA : 0 < A)
    (h2 : HasDerivAt φ' (φ'' t) t) (hΦ : HasDerivAt Φ (φ' t / t^2) t) (hne : φ'' t ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (φ' s * ((y q)⁻¹ - s⁻¹) - Φ s + ψ (y q)))) t = 0
      ↔ ∑ q, ((y q)⁻¹ - t⁻¹) = 0 := by
  refine th_17_1911_1_src A (φ'' t) (fun q s => φ' s * ((y q)⁻¹ - s⁻¹) - Φ s + ψ (y q))
    (fun q => (y q)⁻¹ - t⁻¹) t hA hne (fun q => ?_)
  have hinv : HasDerivAt (fun s => (y q)⁻¹ - s⁻¹) (0 - (-(t^2)⁻¹)) t :=
    (hasDerivAt_const t (y q)⁻¹).sub (hasDerivAt_inv ht.ne')
  have key := (((h2.mul hinv).sub hΦ)).add_const (ψ (y q))
  convert key using 1
  field_simp
  ring

/-- **(iii)-3 = (11) 修正形 (p.328, 331 / F200, 205)** φ'(y) = −k²y², ψ(y_q) = −k²y_q を (10) に代入:
指数の恒等式 −k²y²(1/y_q − 1/y) + k²y − k²y_q = −k²(y − y_q)²/y_q = −k² z_q²/y_q。
(∫φ'(y)/y² dy = ∫(−k²) dy = −k²y なので −∫ = +k²y。) -/
theorem th_17_1911_11_src (k t yq : ℝ) (ht : t ≠ 0) (hyq : yq ≠ 0) :
    (-(k^2) * t^2) * (yq⁻¹ - t⁻¹) - (-(k^2) * t) + (-(k^2) * yq)
      = -(k^2) * (t - yq)^2 / yq
    ∧ -(k^2) * (t - yq)^2 / yq = -(k^2) * |t - yq|^2 / yq := by
  constructor
  · field_simp
    ring
  · rw [sq_abs]

/-- **(iii)-3 印刷形 (F200) の反駁**: 1921 印刷は f_q = A e^{(k²/y_q)(y−y_q)²} = A e^{−k²z_q²/y_q}
(第1の指数に負号なし; 1911 p.328 と (11) F205 は負号あり)。この等式は y = y_q 以外で偽:
k = 1, y_q = 1, y = 2 で e^{1} ≠ e^{−1}。 -/
theorem th_17_1911_iii_3_printed_fails :
    ∃ k yq t : ℝ, Real.exp (k^2 / yq * (t - yq)^2) ≠ Real.exp (-(k^2) * |t - yq|^2 / yq) := by
  refine ⟨1, 1, 2, ?_⟩
  intro h
  have := Real.exp_eq_exp.mp h
  norm_num at this

/-- (11) は調和平均を導く: 指数 −k²(y−y_q)²/y_q の微分は −2k²(y−y_q)/y_q = (−2k²y)(1/y_q − 1/y)。
停留条件 ⟺ Σ(1/y_q − 1/y) = 0 (k ≠ 0, y ≠ 0)。 -/
theorem th_17_1911_11_leads_hmean {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (hy : ∀ q, y q ≠ 0)
    (t : ℝ) (ht : t ≠ 0) (hA : 0 < A) (hk : k ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * (s - y q)^2 / y q))) t = 0
      ↔ ∑ q, ((y q)⁻¹ - t⁻¹) = 0 := by
  have hc : -2 * k^2 * t ≠ 0 := by
    have : k^2 ≠ 0 := pow_ne_zero 2 hk
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h3 | h3
      · norm_num at h3
      · exact this h3
    · exact ht h1
  refine th_17_1911_1_src A (-2 * k^2 * t) (fun q s => -(k^2) * (s - y q)^2 / y q)
    (fun q => (y q)⁻¹ - t⁻¹) t hA hc (fun q => ?_)
  have hyq := hy q
  have key := ((((hasDerivAt_id' t).sub_const (y q)).pow 2).const_mul (-(k^2))).div_const (y q)
  convert key using 1
  field_simp
  ring

/-! ## (iv) 中央値 (p.328–329 / F200–203) -/

/-- (iv)-2 の片側: c ≤ t で c 以下の測定値が半数以上なら Σ|c − y_q| ≤ Σ|t − y_q|。 -/
theorem median_aux_right {m : ℕ} (y : Fin m → ℝ) (c t : ℝ) (hct : c ≤ t)
    (hcount : m ≤ 2 * (Finset.univ.filter (fun q => y q ≤ c)).card) :
    ∑ q, |c - y q| ≤ ∑ q, |t - y q| := by
  have hd : 0 ≤ t - c := by linarith
  have key : ∀ q, (if y q ≤ c then (t - c) else -(t - c)) ≤ |t - y q| - |c - y q| := by
    intro q
    split_ifs with h
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · have := abs_sub_abs_le_abs_sub (c - y q) (t - y q)
      rw [show c - y q - (t - y q) = -(t - c) by ring, abs_neg, abs_of_nonneg hd] at this
      linarith
  have hsum := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => key q)
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul] at hsum
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun q => y q ≤ c)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have h1 : (m : ℝ) ≤ 2 * ((Finset.univ.filter (fun q => y q ≤ c)).card : ℝ) := by
    exact_mod_cast hcount
  have h2 : ((Finset.univ.filter (fun q => y q ≤ c)).card : ℝ)
      + ((Finset.univ.filter (fun q => ¬ y q ≤ c)).card : ℝ) = m := by
    exact_mod_cast hcard
  have h3 := mul_nonneg hd (by linarith : (0 : ℝ) ≤ 2 * ((Finset.univ.filter (fun q => y q ≤ c)).card : ℝ) - m)
  nlinarith [h3, hsum, h2]

/-- **(iv)-2 (p.328 / F201)** Fechner の性質: y が中央値なら Σ|y_q − y| は最小。
「If y is the median of a number of magnitudes, the sum of the absolute differences … is a minimum.」 -/
theorem th_17_1911_iv_2_src {m : ℕ} (y : Fin m → ℝ) (c : ℝ) (hc : IsMedian y c) (t : ℝ) :
    ∑ q, |y q - c| ≤ ∑ q, |y q - t| := by
  simp_rw [abs_sub_comm (y _) c, abs_sub_comm (y _) t]
  rcases le_total c t with hct | htc
  · exact median_aux_right y c t hct hc.1
  · -- 反転 y ↦ −y で右側の場合に帰着
    have h := median_aux_right (fun q => -y q) (-c) (-t) (by linarith) (by
      have : (Finset.univ.filter (fun q => -y q ≤ -c)) = Finset.univ.filter (fun q => c ≤ y q) := by
        ext q; simp
      rw [this]; exact hc.2)
    simp only [neg_sub_neg] at h
    simpa [abs_sub_comm] using h

/-- **(iv)-3 (p.328 / F201)** z_q = |y − y_q|; Σ z_q が最小なら Σ (y − y_q)/z_q = 0
(局所最小 ⇒ 符号和 = 0; y ≠ y_q を要する: |·| は y = y_q で微分不能)。 -/
theorem th_17_1911_iv_3_src {m : ℕ} (y : Fin m → ℝ) (t : ℝ) (hne : ∀ q, t ≠ y q)
    (hmin : IsLocalMin (fun s => ∑ q, |s - y q|) t) :
    ∑ q, (t - y q) / |t - y q| = 0 := by
  have hder : ∀ q, HasDerivAt (fun s => |s - y q|) ((t - y q) / |t - y q|) t := by
    intro q
    rcases lt_or_gt_of_ne (hne q) with h | h
    · have := (hasDerivAt_abs_neg (sub_neg.mpr h)).comp t ((hasDerivAt_id' t).sub_const (y q))
      convert this using 1
      rw [abs_of_neg (sub_neg.mpr h), div_neg, div_self (sub_ne_zero.mpr (hne q))]
      norm_num
    · have := (hasDerivAt_abs_pos (sub_pos.mpr h)).comp t ((hasDerivAt_id' t).sub_const (y q))
      convert this using 1
      rw [abs_of_pos (sub_pos.mpr h), div_self (sub_ne_zero.mpr (hne q))]
      norm_num
  have hd : HasDerivAt (fun s => ∑ q, |s - y q|) (∑ q, (t - y q) / |t - y q|) t := by
    have := HasDerivAt.sum (u := Finset.univ) (A := fun q s => |s - y q|)
      (A' := fun q => (t - y q) / |t - y q|) (x := t) (fun q _ => hder q)
    convert this using 1
    funext s
    simp [Finset.sum_apply]
  exact hmin.hasDerivAt_eq_zero hd

/-- **(iv)-4 = (12) (p.328, 331 / F201, 205)** 中央値を導く最一般形 (積分を実行した形 (12)):
f_q = A e^{φ'(y)(y − y_q)/z_q + ψ(y_q)} の停留条件は Σ(y − y_q)/z_q = 0 (y ≠ y_q, φ''(y) ≠ 0)。
(iv)-4 の積分形 ∫(y−y_q)/z_q φ''(y)dy は、y ≠ y_q の近傍で (y−y_q)/z_q が定数 (±1) なので
φ'(y)(y−y_q)/z_q に等しい。
**最一般性は境界記録**: 「この形 ⇒ 停留条件 ⟺ Σ(y−y_q)/z_q = 0」の十分性のみ。最一般性
(逆向き) には追加原理 ((i)-2 型の全データ同値 + 連続性; th_17_1911_i_2_src) が要る。 -/
theorem th_17_1911_12_src {m : ℕ} (A : ℝ) (φ' φ'' ψ : ℝ → ℝ) (y : Fin m → ℝ) (t : ℝ)
    (hne : ∀ q, t ≠ y q) (hA : 0 < A) (h2 : HasDerivAt φ' (φ'' t) t) (hφ'' : φ'' t ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (φ' s * ((s - y q) / |s - y q|) + ψ (y q)))) t = 0
      ↔ ∑ q, (t - y q) / |t - y q| = 0 := by
  refine th_17_1911_1_src A (φ'' t) (fun q s => φ' s * ((s - y q) / |s - y q|) + ψ (y q))
    (fun q => (t - y q) / |t - y q|) t hA hφ'' (fun q => ?_)
  -- s ↦ (s − y_q)/|s − y_q| は t の近傍で定数
  have hsgn : HasDerivAt (fun s => (s - y q) / |s - y q|) 0 t := by
    rcases lt_or_gt_of_ne (hne q) with h | h
    · have hfun : (fun s => (s - y q) / |s - y q|) =ᶠ[nhds t] fun _ => (-1 : ℝ) := by
        filter_upwards [gt_mem_nhds h] with s hs
        rw [abs_of_neg (sub_neg.mpr hs), div_neg, div_self (sub_ne_zero.mpr hs.ne)]
      exact (hasDerivAt_const t (-1 : ℝ)).congr_of_eventuallyEq hfun
    · have hfun : (fun s => (s - y q) / |s - y q|) =ᶠ[nhds t] fun _ => (1 : ℝ) := by
        filter_upwards [lt_mem_nhds h] with s hs
        rw [abs_of_pos (sub_pos.mpr hs), div_self (sub_ne_zero.mpr hs.ne')]
      exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hfun
  have key := (h2.mul hsgn).add_const (ψ (y q))
  convert key using 1
  ring

/-- **(iv)-5 = (4) の導出 (p.328 / F201)** φ''(y) = −k², ψ(y_q) = ((y−y_q)/z_q) k² y_q を代入:
φ'(y) = −k²y として指数は −k²y(y−y_q)/z_q + ((y−y_q)/z_q)k²y_q = −k²|y − y_q| = −k² z_q。
(台帳【観察】: この ψ は y の符号に依存し、厳密には y_q のみの関数でない。) -/
theorem th_17_1911_iv_5_src (k t yq : ℝ) (hne : t ≠ yq) :
    (-(k^2) * t) * ((t - yq) / |t - yq|) + ((t - yq) / |t - yq|) * (k^2 * yq)
      = -(k^2) * |t - yq| := by
  have h0 : |t - yq| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hsq : (t - yq)^2 = |t - yq|^2 := (sq_abs _).symm
  field_simp
  linear_combination (-(k^2)) * hsq

/-- **(iv)-6 印刷形 (p.329 / F202)** Laplace 1774 の誤差法則。印刷 F202 は直前で
「z = φ(y), z は誤差 y の確率」と定義した直後に、結果式を φ(z) = (m/2)e^{−my} と印刷する
(1911 p.329 は y = φ(x), φ(x) = … で整合; 誤記 T-1)。印刷形を字義どおり z = φ(y) で読むと
φ(φ(y)) = (m/2)e^{−my} となり、Laplace の法則 φ(y) = (m/2)e^{−my} 自身がこれを満たさない:
m = 2, y = 0 で φ(φ(0)) = φ(1) = e^{−2} ≠ 1 = (m/2)e^{0}。
修正形 φ(y) = (m/2)e^{−my} は th_17_1911_iv_6_corrected。 -/
theorem th_17_1911_iv_6_src :
    ∃ mm y : ℝ, 0 < mm ∧
      (mm / 2) * Real.exp (-mm * ((mm / 2) * Real.exp (-mm * y)))
        ≠ (mm / 2) * Real.exp (-mm * y) := by
  refine ⟨2, 0, by norm_num, ?_⟩
  norm_num

/-- **(iv)-6 修正形** φ(y) = (m/2)e^{−my} (y は絶対誤差、y ≥ 0; m ≥ 0)。歴史注記だが、
法則としては (4) の A = m/2, k² = m: (m/2)e^{−my} = A e^{−k²z_q}, z_q = |y|。
印刷形 (φ(z) = …) の反駁は th_17_1911_iv_6_src。 -/
theorem th_17_1911_iv_6_corrected (mm y : ℝ) (hm : 0 ≤ mm) (hy : 0 ≤ y) :
    (mm / 2) * Real.exp (-mm * y) = (mm / 2) * Real.exp (-(Real.sqrt mm)^2 * |y|) := by
  rw [Real.sq_sqrt hm, abs_of_nonneg hy]

/-! ## (v) 一般形 (p.329–330 / F203) -/

/-- **(v)-2 (p.329–330 / F203)** 0 < f_q < 1 ⇒ ∫θφ''dy + ψ(y_q) + log A < 0。
f_q = A e^{E} < 1 かつ A > 0 なら E + log A < 0 (log の単調性)。 -/
theorem th_17_1911_v_2_src (A E : ℝ) (hA : 0 < A) (hlt : A * Real.exp E < 1) :
    E + Real.log A < 0 := by
  have := Real.log_lt_log (by positivity) hlt
  rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at this
  linarith

/-- **(v)-3 (p.330 / F203)** 正規化 Σ A e^{∫θφ''dy + ψ(y_q)} = 1 (y_q の a priori 可能な全値について)。
**形式化の境界の記録**: これは「測定命題 x_v (v は可能値) が a_s h に相対的に排反かつ網羅」
から第14章 (24.7) (Σ p_r/h = 1; phase7g th_14_24_7_src) で従う命題で、KeynesI 担体上では
ior・def_IX_i・ax_iii_taut (phase6c) を要する。本ファイルは誤差法則の側 (実関数) に限るので、
正規化は仮定として置く。以下はその仮定の下で法則の各値が 1 以下であることのみ
(範囲公理 ax_range_hi_i に相当)。 -/
theorem th_17_1911_v_3_src {V : Type} [Fintype V] (A : ℝ) (E : V → ℝ) (hA : 0 < A)
    (hnorm : ∑ v, A * Real.exp (E v) = 1) (v : V) :
    A * Real.exp (E v) ≤ 1 := by
  rw [← hnorm]
  exact Finset.single_le_sum (f := fun w => A * Real.exp (E w))
    (fun w _ => by positivity) (Finset.mem_univ v)

/-! ## (vi) 対称誤差法則の一般形 = (2) (p.330–331 / F203–204) -/

/-- **(vi)-1 = (2) (p.330, 331 / F203, 204)** SYM 下の最一般形 f_q = A e^{−k² f((y−y_q)²)}:
停留条件は Σ(y − y_q) f'((y−y_q)²) = 0 (k ≠ 0; 連鎖律の定数 2 は吸収)。 -/
theorem th_17_1911_2_src {m : ℕ} (A k : ℝ) (F F' : ℝ → ℝ) (y : Fin m → ℝ) (t : ℝ)
    (hA : 0 < A) (hk : k ≠ 0) (hF : ∀ q, HasDerivAt F (F' ((t - y q)^2)) ((t - y q)^2)) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * F ((s - y q)^2)))) t = 0
      ↔ ∑ q, (t - y q) * F' ((t - y q)^2) = 0 := by
  have hc : -2 * k^2 ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · norm_num at h1
    · exact hk (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
  refine th_17_1911_1_src A (-2 * k^2) (fun q s => -(k^2) * F ((s - y q)^2))
    (fun q => (t - y q) * F' ((t - y q)^2)) t hA hc (fun q => ?_)
  have hin : HasDerivAt (fun s => (s - y q)^2) (2 * (t - y q)) t := by
    have := ((hasDerivAt_id' t).sub_const (y q)).pow 2
    convert this using 1
    ring
  have key := ((hF q).comp t hin).const_mul (-(k^2))
  convert key using 1
  ring

/-- **(vi)-2 (p.330 / F203)** f(u) = u ⇒ 算術平均 ((3) の形); f(u) = +√u ⇒ 中央値 ((4) の形):
−k²√((y−y_q)²) = −k²|y − y_q|。 -/
theorem th_17_1911_vi_2_src (A k t yq : ℝ) :
    A * Real.exp (-(k^2) * ((t - yq)^2)) = A * Real.exp (-(k^2) * |t - yq|^2)
    ∧ A * Real.exp (-(k^2) * Real.sqrt ((t - yq)^2)) = A * Real.exp (-(k^2) * |t - yq|) := by
  constructor
  · rw [sq_abs]
  · rw [Real.sqrt_sq_eq_abs]

/-- (vi)-2 の停留条件: f(u) = u のとき Σ(y − y_q)·1 = 0 すなわち Σ(y−y_q) = 0 (算術平均)。 -/
theorem th_17_1911_vi_2_arith {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (t : ℝ) (hA : 0 < A) (hk : k ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * ((s - y q)^2)))) t = 0
      ↔ ∑ q, (t - y q) = 0 := by
  have := th_17_1911_2_src A k (fun u => u) (fun _ => 1) y t hA hk (fun q => hasDerivAt_id' _)
  simpa only [mul_one] using this

/-- **(vi)-3 (p.330 / F203)** f(u) = u² ⇒ 法則 A e^{−k²(y−y_q)⁴} (印刷は 4 乗; tex は 2 乗に崩れ)。 -/
theorem th_17_1911_vi_3_law (A k t yq : ℝ) :
    A * Real.exp (-(k^2) * ((t - yq)^2)^2) = A * Real.exp (-(k^2) * (t - yq)^4) := by
  ring_nf

/-- (vi)-3 の最確値: Σ(y − y_q)³ = 0 ⟺ m y³ − 3y² Σy_q + 3y Σy_q² − Σy_q³ = 0。 -/
theorem th_17_1911_vi_3_src {m : ℕ} (y : Fin m → ℝ) (t : ℝ) :
    (∑ q, (t - y q)^3 = 0)
      ↔ m * t^3 - 3 * t^2 * ∑ q, y q + 3 * t * ∑ q, (y q)^2 - ∑ q, (y q)^3 = 0 := by
  have hexp : ∑ q, (t - y q)^3
      = m * t^3 - 3 * t^2 * ∑ q, y q + 3 * t * ∑ q, (y q)^2 - ∑ q, (y q)^3 := by
    have : ∀ q, (t - y q)^3 = t^3 - 3 * t^2 * y q + 3 * t * (y q)^2 - (y q)^3 := by
      intro q; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexp]

/-- (vi)-3 の停留条件は (2) の f(u) = u² から: Σ(y−y_q)·2(y−y_q)² = 0 ⟺ Σ(y−y_q)³ = 0。 -/
theorem th_17_1911_vi_3_stationary {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (t : ℝ)
    (hA : 0 < A) (hk : k ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * ((s - y q)^2)^2))) t = 0
      ↔ ∑ q, (t - y q)^3 = 0 := by
  have := th_17_1911_2_src A k (fun u => u^2) (fun u => 2 * u) y t hA hk (fun q => by
    have := hasDerivAt_pow 2 ((t - y q)^2)
    convert this using 1
    ring)
  rw [this]
  have hh : ∑ q, (t - y q) * (2 * (t - y q)^2) = 2 * ∑ q, (t - y q)^3 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [hh]
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · norm_num at h1
    · exact h1
  · intro h0
    rw [h0, mul_zero]

/-- **(vi)-4 (p.330 / F203)** f(u) = log u ⇒ 法則 A/(y−y_q)^{2k²} (印刷; tex は崩れ):
A e^{−k² log((y−y_q)²)} = A / |y − y_q|^{2k²} (y ≠ y_q)。
**逸脱の記録**: 印刷は (y−y_q)^{2k²} と絶対値なしで印刷する。負数の実指数冪 (y < y_q のとき)
は定義されない (Lean の rpow は負数で cos 因子を持つ) ので、z_q = |y−y_q| の冪と読み、
y > y_q と y < y_q の両側で示す。 -/
theorem th_17_1911_vi_4_law (A k t yq : ℝ) (h : t ≠ yq) :
    A * Real.exp (-(k^2) * Real.log ((t - yq)^2)) = A / |t - yq| ^ (2 * k^2) := by
  have hpos : 0 < |t - yq| := abs_pos.mpr (sub_ne_zero.mpr h)
  rw [← sq_abs (t - yq), Real.rpow_def_of_pos hpos, Real.log_pow, div_eq_mul_inv,
    ← Real.exp_neg]
  congr 2
  push_cast
  ring

/-- (vi)-4 の最確値: Σ 1/(y − y_q) = 0 (停留条件; y ≠ y_q)。 -/
theorem th_17_1911_vi_4_src {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (t : ℝ) (hne : ∀ q, t ≠ y q)
    (hA : 0 < A) (hk : k ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (-(k^2) * Real.log ((s - y q)^2)))) t = 0
      ↔ ∑ q, 1 / (t - y q) = 0 := by
  have := th_17_1911_2_src A k Real.log (fun u => u⁻¹) y t hA hk (fun q =>
    Real.hasDerivAt_log (pow_ne_zero 2 (sub_ne_zero.mpr (hne q))))
  rw [this]
  have hh : ∀ q, (t - y q) * ((t - y q)^2)⁻¹ = 1 / (t - y q) := by
    intro q
    have := sub_ne_zero.mpr (hne q)
    field_simp
  simp_rw [hh]

/-- **(vi)-4 の観察** (台帳【観察】): 法則 A/(y−y_q)^{2k²} は y → y_q で 1 を超え、
(v)-2 の範囲制約 0 < f_q < 1 と両立しない (A > 0, k ≠ 0)。 -/
theorem th_17_1911_vi_4_exceeds_one (A k yq : ℝ) (hA : 0 < A) (hk : k ≠ 0) :
    ∃ t, yq < t ∧ 1 < A * Real.exp (-(k^2) * Real.log ((t - yq)^2)) := by
  have hk2 : 0 < k^2 := by positivity
  -- t − y_q := e^{−M}, M := (|log A| + 1)/(2k²)
  set M := (|Real.log A| + 1) / (2 * k^2) with hM
  refine ⟨yq + Real.exp (-M), by linarith [Real.exp_pos (-M)], ?_⟩
  rw [add_sub_cancel_left, ← Real.exp_nat_mul, Real.log_exp]
  have h1 : -(k^2) * ((2 : ℕ) * -M) = |Real.log A| + 1 := by
    rw [hM]; push_cast; field_simp
  rw [h1]
  have h2 : Real.exp (|Real.log A| + 1) = Real.exp |Real.log A| * Real.exp 1 := Real.exp_add _ _
  rw [h2]
  have h3 : 1 ≤ A * Real.exp |Real.log A| := by
    have : Real.exp (-Real.log A) ≤ Real.exp |Real.log A| :=
      Real.exp_le_exp.mpr (neg_le_abs _)
    rw [Real.exp_neg, Real.exp_log hA] at this
    calc (1 : ℝ) = A * A⁻¹ := (mul_inv_cancel₀ hA.ne').symm
      _ ≤ A * Real.exp |Real.log A| := mul_le_mul_of_nonneg_left this hA.le
  have h4 : 1 < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ < A * Real.exp |Real.log A| * Real.exp 1 := by
        apply mul_lt_mul' h3 h4 (by norm_num) (by positivity)
    _ = A * (Real.exp |Real.log A| * Real.exp 1) := by ring

/-! ## 結論 (3)(4)(6)(9)(11) と最確値の大域的対応 (p.331 / F204–205) -/

/-- Σ(s − y_q)² = Σ(ȳ − y_q)² + m(s − ȳ)² (ȳ = 算術平均)。 -/
theorem sum_sq_decomp {m : ℕ} (y : Fin m → ℝ) (s ybar : ℝ) (hybar : (m : ℝ) * ybar = ∑ q, y q) :
    ∑ q, (s - y q)^2 = ∑ q, (ybar - y q)^2 + m * (s - ybar)^2 := by
  have : ∀ q, (s - y q)^2 = (ybar - y q)^2 + ((s - ybar)^2 + 2 * (s - ybar) * (ybar - y q)) := by
    intro q; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination (2 * (s - ybar)) * hybar

/-- 正規法則 (3) の対数尤度 Σ log(A e^{−k²(y−y_q)²})。 -/
noncomputable def logLik_normal {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (s : ℝ) : ℝ :=
  ∑ q, Real.log (A * Real.exp (-(k^2) * (s - y q)^2))

theorem logLik_normal_eq {m : ℕ} (A k : ℝ) (hA : 0 < A) (y : Fin m → ℝ) (s : ℝ) :
    logLik_normal A k y s = m * Real.log A - k^2 * ∑ q, (s - y q)^2 := by
  unfold logLik_normal
  have : ∀ q, Real.log (A * Real.exp (-(k^2) * (s - y q)^2))
      = Real.log A + (-(k^2) * (s - y q)^2) := by
    intro q
    rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- **(3) (p.331 / F204)** 正規法則 f_q = A e^{−k²(y−y_q)²} = A e^{−k²z_q²} は算術平均を最確値とする:
大域的に、かつ一意に (k ≠ 0)。 -/
theorem th_17_1911_3_src {m : ℕ} (hm : 0 < m) (A k : ℝ) (hA : 0 < A) (hk : k ≠ 0)
    (y : Fin m → ℝ) :
    IsMostProbable (logLik_normal A k y) Set.univ (amean y)
      ∧ ∀ s, logLik_normal A k y s = logLik_normal A k y (amean y) → s = amean y := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hybar : (m : ℝ) * amean y = ∑ q, y q := by
    unfold amean; field_simp
  have hdec : ∀ s, logLik_normal A k y s
      = logLik_normal A k y (amean y) - k^2 * m * (s - amean y)^2 := by
    intro s
    rw [logLik_normal_eq A k hA, logLik_normal_eq A k hA, sum_sq_decomp y s (amean y) hybar]
    ring
  have hk2 : 0 < k^2 * m := by
    have : 0 < k^2 := by positivity
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  refine ⟨⟨Set.mem_univ _, fun s _ => ?_⟩, fun s hs => ?_⟩
  · rw [hdec s]
    have := mul_nonneg hk2.le (sq_nonneg (s - amean y))
    linarith
  · rw [hdec s] at hs
    have h0 : k^2 * m * (s - amean y)^2 = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hk2.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith

/-- (3) の印刷形 (z_q = |y − y_q| での表示) との同一性。 -/
theorem th_17_1911_3_abs {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (s : ℝ) :
    logLik_normal A k y s = ∑ q, Real.log (A * Real.exp (-(k^2) * |s - y q|^2)) := by
  unfold logLik_normal
  simp_rw [sq_abs]

/-- 中央値法則 (4) の対数尤度 Σ log(A e^{−k² z_q}), z_q = |y − y_q|。 -/
noncomputable def logLik_median {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (s : ℝ) : ℝ :=
  ∑ q, Real.log (A * Real.exp (-(k^2) * |s - y q|))

theorem logLik_median_eq {m : ℕ} (A k : ℝ) (hA : 0 < A) (y : Fin m → ℝ) (s : ℝ) :
    logLik_median A k y s = m * Real.log A - k^2 * ∑ q, |s - y q| := by
  unfold logLik_median
  have : ∀ q, Real.log (A * Real.exp (-(k^2) * |s - y q|))
      = Real.log A + (-(k^2) * |s - y q|) := by
    intro q
    rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- **(4) (p.331 / F204)** 中央値法則 f_q = A e^{−k²z_q} は中央値を最確値とする (大域的; Fechner)。 -/
theorem th_17_1911_4_src {m : ℕ} (A k : ℝ) (hA : 0 < A) (y : Fin m → ℝ) (c : ℝ)
    (hc : IsMedian y c) :
    IsMostProbable (logLik_median A k y) Set.univ c := by
  refine ⟨Set.mem_univ _, fun s _ => ?_⟩
  rw [logLik_median_eq A k hA, logLik_median_eq A k hA]
  have h := th_17_1911_iv_2_src y c hc s
  simp_rw [abs_sub_comm (y _)] at h
  have := mul_le_mul_of_nonneg_left h (sq_nonneg k)
  linarith

/-- McAlister 法則 (9) の対数尤度 Σ log(A e^{−k²(log(y_q/y))²})。 -/
noncomputable def logLik_mcal {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (s : ℝ) : ℝ :=
  ∑ q, Real.log (A * Real.exp (-(k^2) * (Real.log (y q / s))^2))

theorem logLik_mcal_eq {m : ℕ} (A k : ℝ) (hA : 0 < A) (y : Fin m → ℝ) (hy : ∀ q, 0 < y q)
    (s : ℝ) (hs : 0 < s) :
    logLik_mcal A k y s = m * Real.log A - k^2 * ∑ q, (Real.log s - Real.log (y q))^2 := by
  unfold logLik_mcal
  have : ∀ q, Real.log (A * Real.exp (-(k^2) * (Real.log (y q / s))^2))
      = Real.log A + (-(k^2) * (Real.log s - Real.log (y q))^2) := by
    intro q
    rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div (hy q).ne' hs.ne']
    ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- **(9) (p.331 / F205)** McAlister 法則は幾何平均を最確値とする (y > 0 の上で大域的・一意)。
「the most probable value of y must, clearly, be the geometric mean」(F199)。 -/
theorem th_17_1911_9_leads_gmean {m : ℕ} (hm : 0 < m) (A k : ℝ) (hA : 0 < A) (hk : k ≠ 0)
    (y : Fin m → ℝ) (hy : ∀ q, 0 < y q) :
    IsMostProbable (logLik_mcal A k y) (Set.Ioi 0) (gmean y)
      ∧ ∀ s ∈ Set.Ioi (0 : ℝ), logLik_mcal A k y s = logLik_mcal A k y (gmean y) → s = gmean y := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hprod : 0 < ∏ q, y q := Finset.prod_pos (fun q _ => hy q)
  have hg : 0 < gmean y := Real.rpow_pos_of_pos hprod _
  -- log(幾何平均) = 対数の算術平均
  set l : Fin m → ℝ := fun q => Real.log (y q) with hl
  have hlg : Real.log (gmean y) = amean l := by
    unfold gmean amean
    rw [Real.log_rpow hprod, Real.log_prod (fun q _ => (hy q).ne')]
    simp only [hl]
    ring
  have hlbar : (m : ℝ) * amean l = ∑ q, l q := by
    unfold amean; field_simp
  have hdec : ∀ s, 0 < s → logLik_mcal A k y s
      = logLik_mcal A k y (gmean y) - k^2 * m * (Real.log s - amean l)^2 := by
    intro s hs
    rw [logLik_mcal_eq A k hA y hy s hs, logLik_mcal_eq A k hA y hy _ hg, hlg,
      sum_sq_decomp l (Real.log s) (amean l) hlbar]
    simp only [hl]
    ring
  have hk2 : 0 < k^2 * m := by
    have : 0 < k^2 := by positivity
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  refine ⟨⟨Set.mem_Ioi.mpr hg, fun s hs => ?_⟩, fun s hs heq => ?_⟩
  · rw [hdec s (Set.mem_Ioi.mp hs)]
    have := mul_nonneg hk2.le (sq_nonneg (Real.log s - amean l))
    linarith
  · have hs' := Set.mem_Ioi.mp hs
    rw [hdec s hs'] at heq
    have h0 : k^2 * m * (Real.log s - amean l)^2 = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hk2.ne'
    · have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      have h3 : Real.log s = Real.log (gmean y) := by rw [hlg]; linarith
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hs') (Set.mem_Ioi.mpr hg) h3

/-- **(6) (p.331 / F204)** f_q = A e^{k²e^y(y−y_q) − k²e^y} は算術平均を導く:
指数の微分は k²e^y(y − y_q)。停留条件 ⟺ Σ(y − y_q) = 0 (k ≠ 0)。 -/
theorem th_17_1911_6_src {m : ℕ} (A k : ℝ) (y : Fin m → ℝ) (t : ℝ) (hA : 0 < A) (hk : k ≠ 0) :
    deriv (fun s => ∑ q, Real.log (A * Real.exp (k^2 * Real.exp s * (s - y q) - k^2 * Real.exp s))) t = 0
      ↔ ∑ q, (t - y q) = 0 := by
  have hc : k^2 * Real.exp t ≠ 0 := by positivity
  refine th_17_1911_1_src A (k^2 * Real.exp t)
    (fun q s => k^2 * Real.exp s * (s - y q) - k^2 * Real.exp s) (fun q => t - y q) t hA hc
    (fun q => ?_)
  have key := (((Real.hasDerivAt_exp t).const_mul (k^2)).mul ((hasDerivAt_id' t).sub_const (y q))).sub
    ((Real.hasDerivAt_exp t).const_mul (k^2))
  convert key using 1
  ring

/-! ## 反例: 二つの誤差法則で最確値が異なる (受け入れ条件 2)

測定値 (0, 0, 3): 正規法則 (3) の最確値は算術平均 1、中央値法則 (4) の最確値は中央値 0。
算術平均 1 は中央値法則の下では最確値でなく、中央値 0 は正規法則の下では最確値でない。 -/

/-- 反例データ (0, 0, 3)。 -/
noncomputable def y₀ : Fin 3 → ℝ := ![0, 0, 3]

theorem y₀_amean : amean y₀ = 1 := by
  unfold amean y₀
  rw [Fin.sum_univ_three]
  simp

theorem y₀_median : IsMedian y₀ 0 := by
  unfold IsMedian y₀
  have h1 : (Finset.univ.filter (fun q : Fin 3 => ![(0:ℝ), 0, 3] q ≤ 0)) = {0, 1} := by
    ext q; fin_cases q <;> simp
  have h2 : (Finset.univ.filter (fun q : Fin 3 => (0:ℝ) ≤ ![(0:ℝ), 0, 3] q)) = Finset.univ := by
    ext q; fin_cases q <;> simp
  rw [h1, h2]
  simp

/-- **反例定理**: 正規法則では 1 が最確値で 0 はそうでなく、中央値法則では 0 が最確値で 1 はそうでない。 -/
theorem th_17_1911_counterexample (A k : ℝ) (hA : 0 < A) (hk : k ≠ 0) :
    IsMostProbable (logLik_normal A k y₀) Set.univ 1
    ∧ ¬ IsMostProbable (logLik_normal A k y₀) Set.univ 0
    ∧ IsMostProbable (logLik_median A k y₀) Set.univ 0
    ∧ ¬ IsMostProbable (logLik_median A k y₀) Set.univ 1 := by
  have hk2 : 0 < k^2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (th_17_1911_3_src (by norm_num) A k hA hk y₀).1
    rwa [y₀_amean] at this
  · intro h
    have h1 := h.2 1 (Set.mem_univ _)
    rw [logLik_normal_eq A k hA, logLik_normal_eq A k hA] at h1
    unfold y₀ at h1
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h1
    simp at h1
    nlinarith
  · exact th_17_1911_4_src A k hA y₀ 0 y₀_median
  · intro h
    have h1 := h.2 0 (Set.mem_univ _)
    rw [logLik_median_eq A k hA, logLik_median_eq A k hA] at h1
    unfold y₀ at h1
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h1
    simp at h1
    norm_num at h1
    nlinarith

/-- 幾何平均との相違も (測定値 (1, 4)): 算術平均 5/2 ≠ 幾何平均 2。 -/
theorem th_17_1911_counterexample_gmean :
    amean (![1, 4] : Fin 2 → ℝ) ≠ gmean (![1, 4] : Fin 2 → ℝ) := by
  unfold amean gmean
  rw [Fin.sum_univ_two, Fin.prod_univ_two]
  simp
  norm_num

/-! ## 1921 加筆層 (§8–§12, F205–214) -/

/-- **N3 (F207)** 対称性 φ(z) = φ(−z) ⇒ φ'(0) = 0 (偶関数の微分は奇関数)。 -/
theorem deriv_even_is_odd (φ φ' : ℝ → ℝ) (heven : ∀ z, φ z = φ (-z))
    (hd : ∀ z, HasDerivAt φ (φ' z) z) : ∀ z, φ' z = -φ' (-z) := by
  intro z
  have h1 : HasDerivAt (fun w => φ (-w)) (φ' (-z) * (-1)) z :=
    (hd (-z)).comp z ((hasDerivAt_id' z).neg)
  have hfun : (fun w => φ (-w)) = φ := by
    funext w; exact (heven w).symm
  rw [hfun] at h1
  have := (hd z).unique h1
  linarith

/-- 奇関数の微分は偶関数。 -/
theorem deriv_odd_is_even (φ φ' : ℝ → ℝ) (hodd : ∀ z, φ z = -φ (-z))
    (hd : ∀ z, HasDerivAt φ (φ' z) z) : ∀ z, φ' z = φ' (-z) := by
  intro z
  have h1 : HasDerivAt (fun w => -φ (-w)) (-(φ' (-z) * (-1))) z :=
    ((hd (-z)).comp z ((hasDerivAt_id' z).neg)).neg
  have hfun : (fun w => -φ (-w)) = φ := by
    funext w; exact (hodd w).symm
  rw [hfun] at h1
  have := (hd z).unique h1
  linarith

/-- **N3 (F207)** 「positive and negative errors are equally probable, i.e. φ(z) = φ(−z), so that
φ'(0) and φ'''(0) vanish」。三階まで微分可能な偶関数について φ'(0) = 0 かつ φ'''(0) = 0。 -/
theorem th_17_1921_N3_src (φ φ' φ'' φ''' : ℝ → ℝ) (heven : ∀ z, φ z = φ (-z))
    (h1 : ∀ z, HasDerivAt φ (φ' z) z) (h2 : ∀ z, HasDerivAt φ' (φ'' z) z)
    (h3 : ∀ z, HasDerivAt φ'' (φ''' z) z) :
    φ' 0 = 0 ∧ φ''' 0 = 0 := by
  have hodd1 := deriv_even_is_odd φ φ' heven h1
  have heven2 := deriv_odd_is_even φ' φ'' hodd1 h2
  have hodd3 := deriv_even_is_odd φ'' φ''' heven2 h3
  constructor
  · have := hodd1 0; rw [neg_zero] at this; linarith
  · have := hodd3 0; rw [neg_zero] at this; linarith

/-- **N2, N4 (F207)** Maclaurin 展開 φ(z) = φ(0) + zφ'(0) + (z²/2!)φ''(0) + … と
「z⁴ を無視して a + bz² = a e^{bz²/a}」。**形式化の境界の記録**: 近似等式 (高次項の無視) は
主張として不定で形式化対象外。ここでは N4 の厳密な対応物のみ: 下界 a + bz² ≤ a e^{bz²/a}
(a > 0; e^u ≥ 1 + u)。差の評価は次の th_17_1921_N4_order。印刷 F207 の左辺 φ(x) は φ(z) の誤植。 -/
theorem th_17_1921_N4_src (a b z : ℝ) (ha : 0 < a) :
    a + b * z^2 ≤ a * Real.exp (b * z^2 / a) := by
  have := Real.add_one_le_exp (b * z^2 / a)
  have h2 : a + b * z^2 = a * (b * z^2 / a + 1) := by field_simp; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left this ha.le

/-- N4「z⁴ を無視して a + bz² = a e^{bz²/a}」の差の評価: u = bz²/a, |u| ≤ 1 のとき
|a e^{u} − (a + bz²)| ≤ b²z⁴/a (Mathlib の |e^u − 1 − u| ≤ u²)。差は z⁴ のオーダー。 -/
theorem th_17_1921_N4_order (a b z : ℝ) (ha : 0 < a) (hu : |b * z^2 / a| ≤ 1) :
    |a * Real.exp (b * z^2 / a) - (a + b * z^2)| ≤ b^2 * z^4 / a := by
  have h := Real.abs_exp_sub_one_sub_id_le hu
  have h1 : a * Real.exp (b * z^2 / a) - (a + b * z^2)
      = a * (Real.exp (b * z^2 / a) - 1 - b * z^2 / a) := by
    field_simp
    ring
  rw [h1, abs_mul, abs_of_pos ha]
  calc a * |Real.exp (b * z^2 / a) - 1 - b * z^2 / a| ≤ a * (b * z^2 / a)^2 :=
        mul_le_mul_of_nonneg_left h ha.le
    _ = b^2 * z^4 / a := by
        field_simp

/-- **N5 (F208)** 「(1/n Σx_r)² ≠ (1/n)Σx_r²」(印刷は ≠; tex は = に崩れ)。
一般には ≠: 反例 n = 2, x = (0, 2): 1 ≠ 2。また恒等式 (1/2)(x₁²+x₂²) − ((x₁+x₂)/2)² = ((x₁−x₂)/2)²
により、等号は x₁ = x₂ のときに限る。 -/
theorem th_17_1921_N5_src :
    (amean (![0, 2] : Fin 2 → ℝ))^2 ≠ amean (fun q => ((![0, 2] : Fin 2 → ℝ) q)^2) := by
  unfold amean
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp
  norm_num

theorem th_17_1921_N5_identity (x₁ x₂ : ℝ) :
    (x₁^2 + x₂^2) / 2 - ((x₁ + x₂) / 2)^2 = ((x₁ - x₂) / 2)^2 := by
  ring

/-- N5 の一般形「(1/n)Σf(x_r) ≠ f((1/n)Σx_r)」: f(x) = x² で上の反例。 -/
theorem th_17_1921_N5_general :
    ∃ (f : ℝ → ℝ) (x : Fin 2 → ℝ), amean (fun q => f (x q)) ≠ f (amean x) :=
  ⟨fun u => u^2, ![0, 2], fun h => th_17_1921_N5_src h.symm⟩

/-- **N7 (F210)** 「these proofs involve the normal law of error y = k e^{−k²x²}」: (3) で A = k。
**補助** (表記合わせ): x² = |x − 0|² の書き換えのみで、(3) の y_q = 0, A = k への対応を記す。 -/
theorem th_17_1921_N7_src (k x : ℝ) :
    k * Real.exp (-(k^2) * x^2) = k * Real.exp (-(k^2) * |x - 0|^2) := by
  rw [sub_zero, sq_abs]

end KeynesLawOfError

/-! ## 境界記録 (定理化しない行)

- **(a)–(e) (p.330 / F203–204)**: 前提は仮定として入力化した。(a) 一様事前 = `hU6`
  (th_17_1911_U6_src)、(b) 独立 = `IndepGiven` (U3)、(c)(e) 代数関数 f が既知 = f を
  パラメータとする実関数 (U8)、(d) 連続近似 = 真値を実数 t とし微分可能性を仮定 (U9)。
- **U8 (p.324 / F196)**: x_q/a_s h = f(y_q, b_s) は KeynesI の確率関係 PrI と実関数 f を結ぶ
  仮定 (hf : ∀ q s, PrI (x q) (iand (a s) h) = f (y q) (b s))。第 I 部の尤度 Π_q PrI (x q) (a_s h)
  が第 II 部の Π_q f(y_q, t) になる接点であり、定理化する内容はない。
- **(i)-2**: 追加原理 (同値の全データ要求 + 連続性) を明記して定理化 (th_17_1911_i_2_src)。
- **(ii)-3**: 「which is impossible」は原文に証明なし。中間式の微分形 (th_17_1911_ii_3_src) に加え、
  不可能性そのものを証明した (th_17_1911_ii_3_impossible): 恒等式が全 y, y_q > 0 で成り立てば
  φ'' ≡ 0、すなわち Keynes の要求 φ'' ≠ 0 の下で解はない。前提は φ', Φ の微分可能性 (y > 0) のみ。
- **(ii)-7 (F199–200)**: Kapteyn の歪曲線 z = F(y) は変換の宣言のみ。
- **(iv)-6 (F202)**: Laplace 1774 の歴史注記。印刷の φ(z) は φ(y) の誤記 (所見候補)。
- **(v)-3 (F203)**: 正規化は第14章 (24.7) の帰結。KeynesI 担体上では ior と ax_iii_taut を
  要するため仮定化 (th_17_1911_v_3_src)。
- **N0, N1, N6, N8**: 出典注記・文言加筆・最小二乗の問題設定・哲学的加筆 (数式なし)。
- **N2, N4**: Maclaurin 近似と z⁴ 無視は非厳密 — 厳密な下界 (th_17_1921_N4_src) のみ。
-/

/-! ## 監査クエリ -/

#print axioms KeynesI.th_17_1911_U1_src
#print axioms KeynesI.th_17_1911_U1_needs_X_right
#print axioms KeynesI.th_17_1911_U2_src
#print axioms KeynesI.th_17_1911_U2_corrected
#print axioms KeynesI.th_17_1911_U4_src
#print axioms KeynesI.th_17_1911_U5_src
#print axioms KeynesI.th_17_1911_U6_src
#print axioms KeynesI.th_17_1911_U7_src
#print axioms KeynesLawOfError.th_17_1911_U9_src
#print axioms KeynesLawOfError.th_17_1911_1_src
#print axioms KeynesLawOfError.th_17_1911_2_src
#print axioms KeynesLawOfError.th_17_1911_3_src
#print axioms KeynesLawOfError.th_17_1911_3_abs
#print axioms KeynesLawOfError.th_17_1911_4_src
#print axioms KeynesLawOfError.th_17_1911_5_src
#print axioms KeynesLawOfError.th_17_1911_6_src
#print axioms KeynesLawOfError.th_17_1911_7_src
#print axioms KeynesLawOfError.th_17_1911_8_src
#print axioms KeynesLawOfError.th_17_1911_8_leads_gmean
#print axioms KeynesLawOfError.th_17_1911_9_src
#print axioms KeynesLawOfError.th_17_1911_9_leads_gmean
#print axioms KeynesLawOfError.th_17_1911_10_src
#print axioms KeynesLawOfError.th_17_1911_11_src
#print axioms KeynesLawOfError.th_17_1911_11_leads_hmean
#print axioms KeynesLawOfError.th_17_1911_12_src
#print axioms KeynesLawOfError.th_17_1911_i_1_src
#print axioms KeynesLawOfError.th_17_1911_i_2_src
#print axioms KeynesLawOfError.th_17_1911_i_3_src
#print axioms KeynesLawOfError.th_17_1911_i_5_src
#print axioms KeynesLawOfError.th_17_1911_i_5_law
#print axioms KeynesLawOfError.th_17_1911_i_6_src
#print axioms KeynesLawOfError.th_17_1911_i_6_integrate
#print axioms KeynesLawOfError.th_17_1911_i_6_sign
#print axioms KeynesLawOfError.th_17_1911_ii_1_src
#print axioms KeynesLawOfError.th_17_1911_ii_3_src
#print axioms KeynesLawOfError.th_17_1911_ii_3_impossible
#print axioms KeynesLawOfError.th_17_1911_ii_4_src
#print axioms KeynesLawOfError.th_17_1911_ii_6_src
#print axioms KeynesLawOfError.th_17_1911_ii_6_int
#print axioms KeynesLawOfError.th_17_1911_ii_8_src
#print axioms KeynesLawOfError.th_17_1911_ii_8_phi
#print axioms KeynesLawOfError.th_17_1911_ii_9_src
#print axioms KeynesLawOfError.th_17_1911_ii_9_printed_fails
#print axioms KeynesLawOfError.th_17_1911_ii_9_corrected
#print axioms KeynesLawOfError.th_17_1911_ii_9_corrected_int
#print axioms KeynesLawOfError.th_17_1911_iii_1_src
#print axioms KeynesLawOfError.th_17_1911_iii_3_printed_fails
#print axioms KeynesLawOfError.th_17_1911_iv_2_src
#print axioms KeynesLawOfError.th_17_1911_iv_3_src
#print axioms KeynesLawOfError.th_17_1911_iv_5_src
#print axioms KeynesLawOfError.th_17_1911_iv_6_src
#print axioms KeynesLawOfError.th_17_1911_iv_6_corrected
#print axioms KeynesLawOfError.th_17_1911_v_2_src
#print axioms KeynesLawOfError.th_17_1911_v_3_src
#print axioms KeynesLawOfError.th_17_1911_vi_2_src
#print axioms KeynesLawOfError.th_17_1911_vi_2_arith
#print axioms KeynesLawOfError.th_17_1911_vi_3_law
#print axioms KeynesLawOfError.th_17_1911_vi_3_src
#print axioms KeynesLawOfError.th_17_1911_vi_3_stationary
#print axioms KeynesLawOfError.th_17_1911_vi_4_law
#print axioms KeynesLawOfError.th_17_1911_vi_4_src
#print axioms KeynesLawOfError.th_17_1911_vi_4_exceeds_one
#print axioms KeynesLawOfError.th_17_1911_counterexample
#print axioms KeynesLawOfError.th_17_1911_counterexample_gmean
#print axioms KeynesLawOfError.th_17_1921_N3_src
#print axioms KeynesLawOfError.th_17_1921_N4_src
#print axioms KeynesLawOfError.th_17_1921_N4_order
#print axioms KeynesLawOfError.th_17_1921_N5_src
#print axioms KeynesLawOfError.th_17_1921_N5_identity
#print axioms KeynesLawOfError.th_17_1921_N5_general
#print axioms KeynesLawOfError.th_17_1921_N7_src
