/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 7h
#
# 新井一成・Claude共著、2026年7月14日
# **7f照合キューの原文正確形 (その2): Johnson多重証拠Π形・Ch.17パイプライン**
# ⚠ DRAFT v1 — サンドボックスでは未コンパイル。正準ラン v6 前にローカル確認。
#
# ## 照合ソース (7f インデックス準拠)
#   佐藤訳 印字175-178頁 (欄外169-172): (46.1)(46.2)(47)(47.1)(48)(48.1)(49)(49.1)
#     — Johnson 累積公式の多重証拠形 (訳注1: (41)-(49)は Johnson のノートに全面依拠)
#   佐藤訳 印字219-220頁 (欄外210-211): (57)(i)(ii) の連鎖補元基底 n_r
#   佐藤訳 印字222-223頁 (欄外213-214): (58)-(58.3) ブール第X問題 (閉形式・単調増加・事後)
#   Boole (1854) LoT Problem X: 暗黙仮定「x₁=x₂=…=xₙ」→ 本ファイルでは
#     hnegind (NegChainIndep 型) として明示 (ケインズ脚注9の機械化)
#
# ## 設計方針
#   Johnson 恒等式群は **除算なしの積恒等式** に正規化して形式化する。
#   核となるのは def_X の両向き形から出る交換補題 pr_swap と、
#   その積への持ち上げ (prodSwap / prodConj)。係数 {a^{xh}b^{xh}…} は
#   InflN 型の比として現れるが、分母を払った形では一切の非零ガードが不要。
#
# ## 本ファイルの新規項目 (7gキュー #4,5,8,9)
#   pr_swap / prodSwap / prodConj : 交換エンジン
#   th_14_46_1_src : Johnson 逆公式の核 (除算なし積恒等式)
#   th_14_47_1_src : 凝縮係数公式の核
#   th_14_48_src   : 2択の比形式 (46.1 の2適用)
#   th_14_48_1_src : 1証拠追加によるオッズ更新
#   th_14_49_step_src : (49) の G-交換段 (原文表示の不等式そのもの)
#   th_14_49_1_src : (49.1) の混合恒等式核
#   th_17_57_step / booleDecomp / th_17_57_i_src : (57)(i) の連鎖補元再帰
#   th_17_57_ii_n2 : (ii) の n=2 例化 ((56) と整合)
#   th_17_57_1_mr  : n_r = m_r · (¬N∧a)/h (m_r の定義的恒等式)
#   chainN / th_17_58_closed : ブール第X問題の閉形式 a + (1−a)qⁿ
#   th_17_58_1_src : p=a (q=0) → 逐次確率一定 (「unless a=0」は等式形で不要)
#   th_17_58_2_core / th_17_58_2_src : y_{n+1} > y_n の交差乗算形 (log-凸性)
#     — 旧 th_17_58_2 (連鎖積の単調減少) の再ラベルに伴う真正 (58.2)
#   th_17_58_3_src : 不変原因の事後確率 t_n · f(n) = a (除算なし形)
#   q_value        : q(1−a) = p−a (x_s/t̄h の導出、除算なし)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (継承) -/

axiom Pr : Prop → Prop → ℝ
axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1
axiom def_IX (p q h : Prop) : Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h
axiom def_X_left  (p q h : Prop) : Pr (p ∧ q) h = Pr p (q ∧ h) * Pr q h
axiom def_X_right (p q h : Prop) : Pr (p ∧ q) h = Pr q (p ∧ h) * Pr p h

/-! ## 基本補題 -/

theorem th_13_1 (a h : Prop) : Pr a h + Pr (¬a) h = 1 := by
  have step := def_IX True a h
  have e1 : (True ∧ ¬a) ↔ (¬a) := by tauto
  have e2 : (True ∧ a) ↔ a := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, ax_iii_true] at step
  linarith

theorem pr_false (h : Prop) : Pr False h = 0 := by
  have hc := th_13_1 True h
  have e : (¬True) ↔ False := by tauto
  rw [ax_iii_op _ _ h e] at hc
  have ht := ax_iii_true h
  linarith

/-- **交換補題** (def_X 両向き形の帰結)。
p/(q∧h)·q/h = q/(p∧h)·p/h — Johnson 恒等式群のエンジン。 -/
theorem pr_swap (p q h : Prop) :
    Pr p (q ∧ h) * Pr q h = Pr q (p ∧ h) * Pr p h := by
  rw [← def_X_left p q h, def_X_right p q h]

/-! ## リスト機構 -/

def bigAnd : List Prop → Prop
  | [] => True
  | p :: rest => p ∧ bigAnd rest

noncomputable def prodPr : List Prop → Prop → ℝ
  | [], _ => 1
  | p :: rest, h => Pr p h * prodPr rest h

/-- **交換の積持ち上げ** (帰納)。
Π aᵢ/(x∧h) · (x/h)^m = Π [x/(aᵢ∧h)·aᵢ/h]。 -/
theorem prodSwap (x h : Prop) : ∀ (l : List Prop),
    prodPr l (x ∧ h) * (Pr x h) ^ l.length
      = ((l.map (fun a => Pr x (a ∧ h) * Pr a h)).prod) := by
  intro l
  induction l with
  | nil => simp [prodPr]
  | cons a rest ih =>
      simp only [prodPr, List.map, List.prod_cons, List.length_cons]
      have hs := pr_swap a x h
      rw [pow_succ]
      calc Pr a (x ∧ h) * prodPr rest (x ∧ h) * ((Pr x h) ^ rest.length * Pr x h)
          = (Pr a (x ∧ h) * Pr x h) * (prodPr rest (x ∧ h) * (Pr x h) ^ rest.length) := by
            ring
        _ = (Pr x (a ∧ h) * Pr a h) * (prodPr rest (x ∧ h) * (Pr x h) ^ rest.length) := by
            rw [hs]
        _ = (Pr x (a ∧ h) * Pr a h) * ((rest.map (fun a => Pr x (a ∧ h) * Pr a h)).prod) := by
            rw [ih]

/-- 連言積の分解 (帰納)。Π (aᵢ∧x)/h = Π aᵢ/(x∧h) · (x/h)^m。 -/
theorem prodConj (x h : Prop) : ∀ (l : List Prop),
    ((l.map (fun a => Pr (a ∧ x) h)).prod)
      = prodPr l (x ∧ h) * (Pr x h) ^ l.length := by
  intro l
  induction l with
  | nil => simp [prodPr]
  | cons a rest ih =>
      simp only [prodPr, List.map, List.prod_cons, List.length_cons]
      rw [def_X_left a x h, ih, pow_succ]
      ring

/-! ## (46.1) Johnson 逆公式の核 — 除算なし積恒等式 -/

/-- **Th.(14.46.1) 核** (除算なし形)。証拠列 a::l (m = l.length+1 個) について
  x/(L∧h) · L/h · (x/h)^{m−1} · Π aᵢ/(x∧h)
    = L/(x∧h) · Π [x/(aᵢ∧h)·aᵢ/h]
(L = bigAnd (a::l))。原文の
  x/habc… ∝ (x/h)^{−(m−1)} {a^{xh}b^{xh}c…} Π x/ah
の分母・係数 ({…} = L/(x∧h) ÷ Π aᵢ/(x∧h)) を払った不変量。ガード不要。 -/
theorem th_14_46_1_src (x h a : Prop) (l : List Prop) :
    Pr x (bigAnd (a :: l) ∧ h) * Pr (bigAnd (a :: l)) h
        * (Pr x h) ^ l.length * prodPr (a :: l) (x ∧ h)
      = Pr (bigAnd (a :: l)) (x ∧ h)
        * (((a :: l).map (fun b => Pr x (b ∧ h) * Pr b h)).prod) := by
  have h1 := pr_swap x (bigAnd (a :: l)) h
  have h2 := prodSwap x h (a :: l)
  simp only [List.length_cons] at h2
  -- h1 : x/(L∧h)·L/h = L/(x∧h)·x/h
  -- h2 : Π(a::l)/(x∧h)·(x/h)^{m} = Πmap
  linear_combination
    ((Pr x h) ^ l.length * prodPr (a :: l) (x ∧ h)) * h1
    + Pr (bigAnd (a :: l)) (x ∧ h) * h2

/-! ## (47.1) 凝縮係数公式の核 -/

/-- **Th.(14.47.1) 核** (除算なし形)。
  (L∧x)/h · Π aᵢ/(x∧h) · (x/h)^m = x/h · L/(x∧h) · Π (aᵢ∧x)/h。
原文 {abc…^h x} = {a^h b^h c^h…}^{−1}·{a^{xh}b^{xh}c^{xh}…}·Π{aᵢ^h x} の
分母払い形。 -/
theorem th_14_47_1_src (x h : Prop) (l : List Prop) :
    Pr (bigAnd l ∧ x) h * prodPr l (x ∧ h) * (Pr x h) ^ l.length
      = Pr x h * Pr (bigAnd l) (x ∧ h)
        * ((l.map (fun a => Pr (a ∧ x) h)).prod) := by
  have hx := def_X_left (bigAnd l) x h
  have hc := prodConj x h l
  rw [hx, hc]
  ring

/-! ## (48)(48.1) 比形式とオッズ更新 -/

/-- **Th.(14.48) 核**: 2択 x, x′ の比形式は (46.1) の2適用で閉じる。
原文の {x/h}ⁿx/habc… : {x̄/h}ⁿx̄/habc… 表示の交差乗算形。 -/
theorem th_14_48_src (x x' h a : Prop) (l : List Prop) :
    (Pr x (bigAnd (a :: l) ∧ h) * Pr (bigAnd (a :: l)) h
        * (Pr x h) ^ l.length * prodPr (a :: l) (x ∧ h))
      * (Pr (bigAnd (a :: l)) (x' ∧ h)
        * (((a :: l).map (fun b => Pr x' (b ∧ h) * Pr b h)).prod))
    = (Pr x' (bigAnd (a :: l) ∧ h) * Pr (bigAnd (a :: l)) h
        * (Pr x' h) ^ l.length * prodPr (a :: l) (x' ∧ h))
      * (Pr (bigAnd (a :: l)) (x ∧ h)
        * (((a :: l).map (fun b => Pr x (b ∧ h) * Pr b h)).prod)) := by
  rw [th_14_46_1_src x h a l, th_14_46_1_src x' h a l]
  ring

/-- 1証拠追加の分解 (def_X_left の bigAnd 版)。 -/
theorem chain_extend (a y h : Prop) (l : List Prop) :
    Pr (bigAnd (a :: l)) (y ∧ h)
      = Pr a (bigAnd l ∧ (y ∧ h)) * Pr (bigAnd l) (y ∧ h) := by
  simp only [bigAnd]
  exact def_X_left a (bigAnd l) (y ∧ h)

/-- **Th.(14.48.1) 核**: 証拠 a の追加によるオッズ更新は
更新因子 a/(L∧y∧h) のみに依存する (交差乗算形)。 -/
theorem th_14_48_1_src (a x x' h : Prop) (l : List Prop) :
    Pr (bigAnd (a :: l)) (x ∧ h) * Pr (bigAnd l) (x' ∧ h)
        * Pr a (bigAnd l ∧ (x' ∧ h))
      = Pr (bigAnd (a :: l)) (x' ∧ h) * Pr (bigAnd l) (x ∧ h)
        * Pr a (bigAnd l ∧ (x ∧ h)) := by
  rw [chain_extend a x h l, chain_extend a x' h l]
  ring

/-! ## (49)(49.1) 相互強化 -/

/-- **Th.(14.49) の G-交換段** (原文 印字177頁の表示不等式そのもの):
G > G′, x/kh > x/h, かつ x/kh − x/h = x̄/h − x̄/kh ならば
x/kh·G + x̄/kh·G′ > x/h·G + x̄/h·G′。 -/
theorem th_14_49_step_src (G G' xk x0 xk' x0' : ℝ)
    (hGG : G' < G) (hup : x0 < xk) (hbal : xk - x0 = x0' - xk') :
    x0 * G + x0' * G' < xk * G + xk' * G' := by
  -- 原文の G(x/kh − x/h) > G′(x̄/h − x̄/kh) の段: 差の恒等式 + 差積の正値性
  have hd : 0 < (xk - x0) * (G - G') :=
    mul_pos (by linarith) (by linarith)
  have key : (xk * G + xk' * G') - (x0 * G + x0' * G')
      = (xk - x0) * (G - G') := by
    linear_combination G' * hbal
  linarith [hd, key]

/-- **Th.(14.49.1) 核** (混合恒等式): 選択肢 x, x̄ による係数分解の土台
L/h = L/(x∧h)·x/h + L/(x̄∧h)·x̄/h。 -/
theorem th_14_49_1_src (x h : Prop) (l : List Prop) :
    Pr (bigAnd l) h
      = Pr (bigAnd l) (x ∧ h) * Pr x h
        + Pr (bigAnd l) (¬x ∧ h) * Pr (¬x) h := by
  have hsplit := def_IX (bigAnd l) x h
  have h1 := def_X_left (bigAnd l) x h
  have h2 := def_X_left (bigAnd l) (¬x) h
  linarith

/-! ## (57)(i)(ii) 連鎖補元基底 n_r -/

/-- **(57)(i) の一段** (原文の再帰そのもの):
E∧N /h = E∧a /h − (E∧a)∧¬N /h + E∧(N∧¬a) /h。 -/
theorem th_17_57_step (E N a h : Prop) :
    Pr (E ∧ N) h
      = Pr (E ∧ a) h - Pr ((E ∧ a) ∧ ¬N) h + Pr (E ∧ (N ∧ ¬a)) h := by
  have s1 := def_IX (E ∧ N) a h
  have s2 := def_IX (E ∧ a) N h
  have e1 : ((E ∧ N) ∧ a) ↔ ((E ∧ a) ∧ N) := by tauto
  have e2 : ((E ∧ N) ∧ ¬a) ↔ (E ∧ (N ∧ ¬a)) := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at s1
  linarith

/-- ブール分解 (Arai 拡張定義)。booleDecomp E h l N は (57)(i) を
リスト l に沿って展開した値。N は否定連鎖の累積 (初期値 True)。 -/
noncomputable def booleDecomp (E h : Prop) : List Prop → Prop → ℝ
  | [], N => Pr (E ∧ N) h
  | a :: rest, N =>
      Pr (E ∧ a) h - Pr ((E ∧ a) ∧ ¬N) h + booleDecomp E h rest (N ∧ ¬a)

/-- **Th.(17.57)(i) 一般形**: E∧N /h = booleDecomp E h l N。
r=1 の補正項は ¬True で消える (原文の Σ が r=2 から始まる機械的対応)。 -/
theorem th_17_57_i_src (E h : Prop) : ∀ (l : List Prop) (N : Prop),
    Pr (E ∧ N) h = booleDecomp E h l N := by
  intro l
  induction l with
  | nil => intro N; rfl
  | cons a rest ih =>
      intro N
      simp only [booleDecomp]
      rw [← ih (N ∧ ¬a)]
      exact th_17_57_step E N a h

/-- **Th.(17.57)(ii) の n=2 例化**: 網羅性 (E∧ā₁ā₂ /h = 0) の下で
e/h = e∧a₁/h + e∧a₂/h − n₂、n₂ = (e∧a₂)∧a₁ /h。
(56) の a₁a₂-重なり補正と整合。 -/
theorem th_17_57_ii_n2 (E a₁ a₂ h : Prop)
    (hexh : Pr (E ∧ ((True ∧ ¬a₁) ∧ ¬a₂)) h = 0) :
    Pr E h = Pr (E ∧ a₁) h + Pr (E ∧ a₂) h - Pr ((E ∧ a₂) ∧ a₁) h := by
  have hi := th_17_57_i_src E h [a₁, a₂] True
  simp only [booleDecomp] at hi
  have eE : (E ∧ True) ↔ E := by tauto
  rw [ax_iii_op _ _ h eE] at hi
  have e1 : ((E ∧ a₁) ∧ ¬True) ↔ False := by tauto
  rw [ax_iii_op _ _ h e1, pr_false] at hi
  have e2 : ((E ∧ a₂) ∧ ¬(True ∧ ¬a₁)) ↔ ((E ∧ a₂) ∧ a₁) := by tauto
  rw [ax_iii_op _ _ h e2] at hi
  rw [hexh] at hi
  linarith

/-- **Th.(17.57.1) の m_r 恒等式**: n_r = m_r · (¬N∧a)/h、
m_r := E/((¬N∧a)∧h) (原文の定義)。 -/
theorem th_17_57_1_mr (E N a h : Prop) :
    Pr ((E ∧ a) ∧ ¬N) h = Pr E ((¬N ∧ a) ∧ h) * Pr (¬N ∧ a) h := by
  have e : ((E ∧ a) ∧ ¬N) ↔ ((¬N ∧ a) ∧ E) := by tauto
  rw [ax_iii_op _ _ h e]
  exact def_X_right (¬N ∧ a) E h

/-! ## (58)-(58.3) ブール第X問題パイプライン -/

/-- 試行連鎖: chainN x n = xₙ ∧ … ∧ x₁ ∧ True。 -/
def chainN (x : ℕ → Prop) : ℕ → Prop
  | 0 => True
  | n + 1 => x (n + 1) ∧ chainN x n

/-- q の値の導出 (原文: x_s/t̄h = (p−a)/(1−a))。除算なし形:
q·(1−a) = p − a。前提は x_r/h = p, x_r/th = 1, t/h = a。 -/
theorem q_value (xr t h : Prop) (p aa : ℝ)
    (hxh : Pr xr h = p) (hxt : Pr xr (t ∧ h) = 1) (hta : Pr t h = aa) :
    Pr xr (¬t ∧ h) * (1 - aa) = p - aa := by
  have hsplit := def_IX xr t h
  have h1 := def_X_left xr t h
  -- (xr∧t)/h = xr/(t∧h)·t/h = 1·aa
  have h2 := def_X_left xr (¬t) h
  have hc := th_13_1 t h
  -- (xr∧¬t)/h = xr/(¬t∧h)·(1−aa)
  rw [hxt, hta] at h1
  rw [hxh] at hsplit
  have hnt : Pr (¬t) h = 1 - aa := by linarith
  rw [hnt] at h2
  linarith [hsplit, h1, h2]

/-- 確実側の連鎖積: 不変原因 t の下で全試行が確実なら連鎖も確実。 -/
theorem chain_cert (x : ℕ → Prop) (t h : Prop)
    (hcert : ∀ n k, Pr (x (n + 1)) (chainN x k ∧ (t ∧ h)) = 1) :
    ∀ n, Pr (chainN x n) (t ∧ h) = 1 := by
  intro n
  induction n with
  | zero => exact ax_iii_true (t ∧ h)
  | succ k ih =>
      have hd := def_X_left (x (k + 1)) (chainN x k) (t ∧ h)
      simp only [chainN]
      rw [hd, hcert k k, ih, one_mul]

/-- 否定側の連鎖積: NegChainIndep (ブールの暗黙仮定の明示形、
ケインズ脚注9) の下で chainN /(t̄∧h) = qⁿ。 -/
theorem chain_neg (x : ℕ → Prop) (t h : Prop) (q : ℝ)
    (hnegind : ∀ n, Pr (x (n + 1)) (chainN x n ∧ (¬t ∧ h)) = q) :
    ∀ n, Pr (chainN x n) (¬t ∧ h) = q ^ n := by
  intro n
  induction n with
  | zero => simpa [chainN] using ax_iii_true (¬t ∧ h)
  | succ k ih =>
      have hd := def_X_left (x (k + 1)) (chainN x k) (¬t ∧ h)
      simp only [chainN]
      rw [hd, hnegind k, ih, pow_succ]
      ring

/-- **Th.(17.58) 閉形式** (ブール第X問題の核):
Pr(x₁…xₙ)/h = a + (1−a)·qⁿ。
原文の a + (p−a)((p−a)/(1−a))^{n−1} は q(1−a) = p−a (q_value) による同値形。
仮定: t/h = a、確実性連鎖 (x_r/th = 1 の連鎖強化形)、NegChainIndep。 -/
theorem th_17_58_closed (x : ℕ → Prop) (t h : Prop) (aa q : ℝ)
    (hta : Pr t h = aa)
    (hcert : ∀ n k, Pr (x (n + 1)) (chainN x k ∧ (t ∧ h)) = 1)
    (hnegind : ∀ n, Pr (x (n + 1)) (chainN x n ∧ (¬t ∧ h)) = q) :
    ∀ n, Pr (chainN x n) h = aa + (1 - aa) * q ^ n := by
  intro n
  have hsplit := def_IX (chainN x n) t h
  have h1 := def_X_left (chainN x n) t h
  have h2 := def_X_left (chainN x n) (¬t) h
  have hc := th_13_1 t h
  have hcert' := chain_cert x t h hcert n
  have hneg' := chain_neg x t h q hnegind n
  rw [hcert', hta, one_mul] at h1
  have hnt : Pr (¬t) h = 1 - aa := by linarith
  rw [hneg', hnt] at h2
  linarith [hsplit, h1, h2]

/-- **Th.(17.58.1)** p = a の場合 (q = 0): 一度の生起以後、逐次確率は一定
(y_{n+1} = 1 の等式形 — 除算を避けるため連鎖確率の一致で表す)。
ブールの「unless a = 0」但書は、この等式形では不要になる (7f 正誤メモ)。 -/
theorem th_17_58_1_src (x : ℕ → Prop) (t h : Prop) (aa : ℝ)
    (hta : Pr t h = aa)
    (hcert : ∀ n k, Pr (x (n + 1)) (chainN x k ∧ (t ∧ h)) = 1)
    (hnegind : ∀ n, Pr (x (n + 1)) (chainN x n ∧ (¬t ∧ h)) = 0) :
    ∀ n, Pr (chainN x (n + 2)) h = Pr (chainN x (n + 1)) h := by
  intro n
  have hcl := th_17_58_closed x t h aa 0 hta hcert hnegind
  rw [hcl (n + 2), hcl (n + 1)]
  norm_num

/-- **Th.(17.58.2) 核** (代数): 0 < a, 0 < u, 0 < Q, 0 < ql < 1 ならば
(a + u·Q·ql²)(a + u·Q) > (a + u·Q·ql)²。
f(n) = a + u·qⁿ の log-凸性 = y_{n+1} > y_n の交差乗算形。
LHS − RHS = a·u·Q·(1 − ql)²。 -/
theorem th_17_58_2_core (a u Q ql : ℝ)
    (ha : 0 < a) (hu : 0 < u) (hQ : 0 < Q) (hql : ql < 1) :
    (a + u * Q * ql ^ 2) * (a + u * Q) > (a + u * Q * ql) ^ 2 := by
  -- LHS − RHS = a·u·Q·(1−ql)² を恒等式として明示し、正値性で閉じる
  have key : (a + u * Q * ql ^ 2) * (a + u * Q) - (a + u * Q * ql) ^ 2
      = a * (u * Q) * (1 - ql) ^ 2 := by ring
  have h1 : 0 < u * Q := mul_pos hu hQ
  have h2 : 0 < (1 - ql) ^ 2 := pow_pos (by linarith) 2
  have pos : 0 < a * (u * Q) * (1 - ql) ^ 2 :=
    mul_pos (mul_pos ha h1) h2
  linarith [key, pos]

/-- **Th.(17.58.2) 原文形**: 0 < a < 1, 0 < q < 1 のとき
f(n+2)·f(n) > f(n+1)² (f(n) = Pr(chainN n) h)。
y_{n+1} = f(n+1)/f(n) の単調増加の除算なし表現。
旧 th_17_58_2 (phase5) は連鎖積の単調減少 — 真だが別命題 (7f ✎)。 -/
theorem th_17_58_2_src (x : ℕ → Prop) (t h : Prop) (aa q : ℝ)
    (hta : Pr t h = aa)
    (hcert : ∀ n k, Pr (x (n + 1)) (chainN x k ∧ (t ∧ h)) = 1)
    (hnegind : ∀ n, Pr (x (n + 1)) (chainN x n ∧ (¬t ∧ h)) = q)
    (ha : 0 < aa) (ha1 : aa < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ n, Pr (chainN x (n + 2)) h * Pr (chainN x n) h
          > (Pr (chainN x (n + 1)) h) ^ 2 := by
  intro n
  have hcl := th_17_58_closed x t h aa q hta hcert hnegind
  rw [hcl (n + 2), hcl (n + 1), hcl n]
  have hu : (0 : ℝ) < 1 - aa := by linarith
  have hQ : (0 : ℝ) < q ^ n := pow_pos hq0 n
  have hcore := th_17_58_2_core aa (1 - aa) (q ^ n) q ha hu hQ hq1
  have e2 : q ^ (n + 2) = q ^ n * q ^ 2 := by ring
  have e1 : q ^ (n + 1) = q ^ n * q := by ring
  rw [e2, e1]
  nlinarith [hcore]

/-- **Th.(17.58.3)** 不変原因の事後確率 (除算なし形):
t/(chainN n ∧ h) · Pr(chainN n) h = a。
原文の t_n = a / (a + (p−a)((p−a)/(1−a))ⁿ) の分母払い形。
n → ∞ で t_n → 1 (a > 0 のとき) は f(n) → a と本式から。 -/
theorem th_17_58_3_src (x : ℕ → Prop) (t h : Prop) (aa : ℝ)
    (hta : Pr t h = aa)
    (hcert : ∀ n k, Pr (x (n + 1)) (chainN x k ∧ (t ∧ h)) = 1) :
    ∀ n, Pr t (chainN x n ∧ h) * Pr (chainN x n) h = aa := by
  intro n
  have hd := def_X_right (chainN x n) t h
  have h1 := def_X_left (chainN x n) t h
  have hcert' := chain_cert x t h hcert n
  rw [hcert', hta, one_mul] at h1
  -- h1 : Pr (chainN∧t) h = aa、hd : Pr (chainN∧t) h = Pr t (chainN∧h)·Pr chainN h
  rw [h1] at hd
  linarith [hd]

end Keynes

/-! ## 監査クエリ (Phase 7h) -/

#check @Keynes.pr_swap
#check @Keynes.th_14_46_1_src
#check @Keynes.th_14_47_1_src
#check @Keynes.th_14_48_src
#check @Keynes.th_14_48_1_src
#check @Keynes.th_14_49_step_src
#check @Keynes.th_14_49_1_src
#check @Keynes.th_17_57_i_src
#check @Keynes.th_17_57_ii_n2
#check @Keynes.th_17_57_1_mr
#check @Keynes.th_17_58_closed
#check @Keynes.th_17_58_1_src
#check @Keynes.th_17_58_2_src
#check @Keynes.th_17_58_3_src

#print axioms Keynes.th_14_46_1_src
#print axioms Keynes.th_14_47_1_src
#print axioms Keynes.th_14_48_src
#print axioms Keynes.th_14_48_1_src
#print axioms Keynes.th_14_49_step_src
#print axioms Keynes.th_14_49_1_src
#print axioms Keynes.th_17_57_i_src
#print axioms Keynes.th_17_57_ii_n2
#print axioms Keynes.th_17_57_1_mr
#print axioms Keynes.q_value
#print axioms Keynes.th_17_58_closed
#print axioms Keynes.th_17_58_1_src
#print axioms Keynes.th_17_58_2_core
#print axioms Keynes.th_17_58_2_src
#print axioms Keynes.th_17_58_3_src
