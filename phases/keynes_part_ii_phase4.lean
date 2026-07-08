/-
# Keynes (1921) *A Treatise on Probability* Part II — Lean 4 Phase 4
#
# 新井一成・Claude共著、2026年7月6日
# Phase 3d (累積 Bayes, 42 ノード) → Phase 4 (Ch.15 数値測定, +Ch.15 全 9 ノード)
#
# ## 本ファイルで追加したもの
#   Axioms (新規昇格):
#     ax_range_lo / ax_range_hi : 範囲原理 0 ≤ α/h ≤ 1
#         Keynes が本文散文で主張しながら Ch.12 公理リストに載せなかった原理。
#         Ch.15 の数値限界定理は範囲原理なしには導出不能 (それ自体が発見)。
#         DB が th15_51 に th13_2/th13_3 を引かせているのは Def.IV/V 経由の
#         範囲原理へのジェスチャーであり、本ファイルでは公理として顕在化させる。
#   Ch.15 の 3 公理の監査:
#     Ax.XVIII (加算公理)   → 定理として証明 = substrate に完全吸収 (Mode B∩C 判定)
#     Ax.XIX   (比例公理)   → 定理として証明 = substrate に完全吸収 (Mode B∩C 判定)
#     Ax.(前)  (実数値存在) → 素朴形は系を矛盾させる (Naive.collapse : False)
#                             → 内包的命題型 IProp 上の修復形で再導入 (Intensional)
#   Theorems:
#     th_13_1  (再掲, 補完律)        ――― (54) の証明で使用
#     th_24    (再掲, 加法定理)      ――― (51) 下界で使用
#     pr_false / th_15_degeneracy    ――― 縮退監査 (Pr α h ∈ {0,1} が導出可能)
#     Naive.collapse : False         ――― 素朴 Ax.(前) との結合矛盾証明書
#     th_15_50 (Intensional)         ――― 数値確率の加算可能性 (Ax.(前) 修復形から)
#     th_15_51 : Boole–Fréchet 限界  ――― α/h+y/h−1 ≤ αy/h ≤ min(α/h, y/h)
#     th_15_52 : n 項 Bonferroni     ――― List 帰納法による n 項下界 (本物の induction)
#     th_15_53 : 対角和の上界        ――― αy/h + ᾱȳ/h の二重上界
#     th_15_54 : 対角差の恒等式      ――― αy/h − ᾱȳ/h = α/h + y/h − 1
#     th_15_55 : Boole 消去法 scheme ――― 未知確率の範囲消去 (純 ℝ 算術)
#
# ## 検証したい仮説 (実行結果が最終判定)
#   H1 (引き継ぎ書の予測): 「Ch.15 で induction が新規 Mode C kernel axiom として
#      surface する」。
#      本ファイルの反対予測: Lean 4 の再帰子 (Nat.rec / List.rec) は公理ではなく
#      CIC 型理論の一部なので、th_15_52 の #print axioms には帰納法由来の新規
#      公理は「現れない」。Mode C シグネチャは {propext, Classical.choice,
#      Quot.sound} で飽和していると予測する。どちらが正しいかは出力が決める。
#   H2: th_15_54 は DB 引用 (th15_51, th15_53) を必要とせず、象限分解
#      (def_IX + ax_iii_op + ax_iii_true) だけで閉じる → Mode S 第 3 例。
#   H3: th_15_51〜53 は ax_range_lo/hi に依存する (範囲原理が Ch.15 で初めて
#      load-bearing になる)。
#   H4: Ax.XVIII / Ax.XIX は Keynes 名前空間の公理を一切使わずに証明される
#      (= 4-axiom floor、Mode B∩C の機械証明書)。
#
# ## 縮退監査について (本 Phase の中心的発見候補)
#   ax_iii_op は「証明された同値」(Keynes の論証的同値) ではなく「実質的同値」
#   (material biconditional) を受け取る。古典 em の下で任意の命題は True か
#   False と実質同値になるため、Pr α h = 0 ∨ Pr α h = 1 が定理になる
#   (th_15_degeneracy)。これは:
#     (a) 既存 Phase 1–3d の条件文型定理を無効化しない (すべて真のまま)。
#     (b) しかし素朴 Ax.(前) (∃ α h, Pr α h = 1/2 型の存在主張) とは直接矛盾する。
#     (c) Pilot の Limitations 「融合形 Ax.(iii) は propext 的同一視を先取りして
#         いる」の精密化・機械証明化である。
#   修復は Pr の定義域を外延的 Prop から内包的命題型 IProp に取り替えること。
#   Keynes の確率関係の項が真理値ではなく「知識の対象」であることの、
#   カーネルレベルの確認である。
#
# ## 実行方法 (Mac ローカル)
#   cd ~/keynes-lean/keynes_audit
#   lake env lean phases/keynes_part_ii_phase4.lean
#   (警告 [unused variable 等] は想定内。エラーが 0 で #print axioms 出力が
#    出ていれば成功)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Keynes

/-! ## プリミティブ・公理 (Phase 3d から継承 + 範囲原理の昇格) -/

axiom Pr : Prop → Prop → ℝ

axiom ax_iii_op (p q h : Prop) : (p ↔ q) → Pr p h = Pr q h
axiom ax_iii_true (h : Prop) : Pr True h = 1

axiom def_IX (p q h : Prop) :
    Pr (p ∧ ¬q) h + Pr (p ∧ q) h = Pr p h

/-- **範囲原理 (下界)**. Keynes は「すべての確率は不可能性と確実性の間に
ある」と散文で繰り返し主張する (Def.IV/V はその両端の定義) が、Ch.12 の
操作公理群には数え入れていない。Ch.15 の数値限界定理はこの原理なしには
導出できないため、Phase 4 で明示公理に昇格させる。DB の
cites(th15_51, th13_2/th13_3) は本原理への間接参照と解釈する。 -/
axiom ax_range_lo (α h : Prop) : 0 ≤ Pr α h

/-- **範囲原理 (上界)**. 同上。 -/
axiom ax_range_hi (α h : Prop) : Pr α h ≤ 1

-- 注: def_X 族・def_XI・def_XII は Phase 4 の証明経路では不要のため宣言しない。
-- DB は th15_51 に def_x を引かせているが、kernel 経路は def_IX + 範囲原理で
-- 閉じる (Mode S 系のデータ点として §7.10 で報告)。

/-! ## 再掲定理 (Phase 2 / Pilot から、証明付き) -/

/-- **Th.(13.1)** 補完律 α/h + ᾱ/h = 1 (Phase 2 再掲)。(54) で使用。 -/
theorem th_13_1 (α h : Prop) : Pr α h + Pr (¬α) h = 1 := by
  have step := def_IX True α h
  have e1 : (True ∧ ¬α) ↔ ¬α := by tauto
  have e2 : (True ∧ α) ↔ α := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2, ax_iii_true] at step
  linarith

/-- **Th.(24)** 加法定理 (Pilot 再掲)。(51) の Fréchet 下界で使用。 -/
theorem th_24 (α β h : Prop) :
    Pr (α ∨ β) h = Pr α h + Pr β h - Pr (α ∧ β) h := by
  have step1 : Pr ((α ∨ β) ∧ ¬β) h + Pr ((α ∨ β) ∧ β) h = Pr (α ∨ β) h :=
    def_IX (α ∨ β) β h
  have eq1 : ((α ∨ β) ∧ ¬β) ↔ (α ∧ ¬β) := by tauto
  have eq2 : ((α ∨ β) ∧ β) ↔ β := by tauto
  rw [ax_iii_op _ _ h eq1, ax_iii_op _ _ h eq2] at step1
  have step3 : Pr (α ∧ ¬β) h + Pr (α ∧ β) h = Pr α h :=
    def_IX α β h
  linarith

/-! ## 縮退監査 (Phase 4 新規) -/

/-- 不可能命題の確率は 0。def_IX を (False, False) に特殊化するだけで出る。
(Keynes Th.(1.2)/Def.III 相当の操作形。) -/
theorem pr_false (h : Prop) : Pr False h = 0 := by
  have step := def_IX False False h
  have e1 : (False ∧ ¬False) ↔ False := by tauto
  have e2 : (False ∧ False) ↔ False := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at step
  linarith

/-- **縮退定理 (Phase 4 中心監査)**.
現行エンコーディング (融合形 ax_iii_op + 古典論理) の下では、すべての確率は
0 か 1 である。証明は Classical.em による場合分け: α が真なら α ↔ True、
偽なら α ↔ False が「実質同値」として成立し、ax_iii_op がそれを受理して
しまう。Keynes の Ax.(iii) は論証的 (demonstrative) 同値にのみ適用される
はずなので、これは融合形が古典 substrate 上で厳密に強すぎることの
カーネル証明である。Pilot の Limitations 第 2 項の精密化。

## 検証対象
- 依存集合に Classical.choice が必ず入る (em 経由) こと
- def_IX, ax_iii_op, ax_iii_true 以外の Keynes 公理が不要なこと -/
theorem th_15_degeneracy (α h : Prop) : Pr α h = 0 ∨ Pr α h = 1 := by
  by_cases hα : α
  · right
    have e : α ↔ True := by tauto
    rw [ax_iii_op _ _ h e, ax_iii_true]
  · left
    have e : α ↔ False := by tauto
    rw [ax_iii_op _ _ h e, pr_false]

/- **素朴 Ax.(前) の隔離監査**: Keynes の字面通り「p ≤ n に対し値 p/n を取る
確率関係が存在する」を外延的 Prop 上で公理化すると、縮退定理と直接衝突して
系全体が矛盾する。`collapse : False` はその結合矛盾の機械証明書である。
この namespace の公理は Keynes 名前空間本体には**含めない** (隔離)。 -/
namespace Naive

/-- Ax.(前) 素朴形 (隔離)。 -/
axiom ax_mae_prop (p n : ℕ) (hpn : p ≤ n) (hn : n ≠ 0) :
    ∃ (α h : Prop), Pr α h = (p : ℝ) / (n : ℝ)

/-- **結合矛盾証明書**: 素朴 Ax.(前) + 縮退定理 → False。
p/n = 1/2 の確率関係の存在が Pr ∈ {0,1} と両立しない。 -/
theorem collapse : False := by
  obtain ⟨α, h, hval⟩ := ax_mae_prop 1 2 (by norm_num) (by norm_num)
  have h12 : Pr α h = (1 : ℝ) / 2 := by
    rw [hval]; norm_num
  rcases th_15_degeneracy α h with h0 | h1
  · rw [h0] at h12; norm_num at h12
  · rw [h1] at h12; norm_num at h12

end Naive

/-! ## Ch.15 の 3 公理の監査 -/

/-- **Ax.XVIII 用の反復加算** (Arai 拡張定義)。Keynes の省略記号
α/h + {α/h + [α/h + …]} を再帰で厳密化したもの。Keynes の「…」は
文字通り再帰子である、という点が Phase 4 の観察の一つ。 -/
noncomputable def addTimes : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, P => P + addTimes n P

/-- **Ax.XVIII (加算公理) の吸収判定**: 「α/h の γ 回の反復加算 = γ·(α/h)」は
公理として宣言する必要がなく、substrate (ℝ 算術 + 帰納法) の定理である。
Keynes 名前空間の公理を一切使わずに証明されること (= floor 到達) が
Mode B∩C の機械証明書となる。 -/
theorem th_ax_xviii_absorbed (P : ℝ) : ∀ n : ℕ, addTimes n P = (n : ℝ) * P := by
  intro n
  induction n with
  | zero => simp [addTimes]
  | succ k ih =>
      simp only [addTimes, ih]
      push_cast
      ring

/-- **Ax.XIX (比例公理) の吸収判定**: 「確実性が n 個の同値な排反選択肢に
分割されるとき、各選択肢の確率は 1/n」の値レベル核心 (n·v = 1 → v = 1/n) は
substrate の定理である。同じく floor 到達を予測。 -/
theorem th_ax_xix_absorbed (n : ℕ) (v : ℝ) (hn : (n : ℝ) ≠ 0)
    (total : (n : ℝ) * v = 1) : v = 1 / (n : ℝ) := by
  have h2 : v * (n : ℝ) = 1 := by rw [mul_comm]; exact total
  rw [eq_div_iff hn]
  exact h2

/- **Ax.(前) 修復形**: 確率関係の定義域を外延的 Prop から内包的命題型
IProp に取り替える。IProp は真理値に潰れないため縮退が起きず、素朴形の
矛盾が解消される。Keynes の確率の項が「知識の対象」(内包的実体) であって
真理値ではないことの、カーネルレベルでの確認。IProp 上の演算体系
(def_IX 等の移植) は Phase 6 以降の課題として明示的に残す。 -/
namespace Intensional

/-- 内包的命題のキャリア (Arai 拡張)。 -/
axiom IProp : Type

/-- 内包的確率関係 (Arai 拡張)。外延的 Pr とは独立の公理であり、
Pr の公理群を継承しないため縮退定理の影響を受けない。 -/
axiom PrI : IProp → IProp → ℝ

/-- **Ax.(前)** (修復形): p ≤ n なる自然数に対し、値 p/n を取る内包的
確率関係が存在する。 -/
axiom ax_mae (p n : ℕ) (hpn : p ≤ n) (hn : n ≠ 0) :
    ∃ (a e : IProp), PrI a e = (p : ℝ) / (n : ℝ)

/-- **Th.(15.50)** 数値確率の加算可能性。
p/n と q/n が数値確率として存在するなら、その和 (p+q)/n も
(p + q ≤ n の限り) 数値確率として存在する。存在部分は Ax.(前) 修復形、
算術部分 ((p+q)/n = p/n + q/n) は substrate。

Keynes Prolog DB: cites(th15_50, ax_xix), cites(th15_50, ax_mae).

## 検証対象
- PrI と ax_mae のみが Keynes 側依存として surface すること
- Ax.XIX の引用が kernel 経路では不要なこと (比例部分は field 算術) -/
theorem th_15_50 (p q n : ℕ) (hpq : p + q ≤ n) (hn : n ≠ 0) :
    ∃ (a e : IProp), PrI a e = (p : ℝ) / (n : ℝ) + (q : ℝ) / (n : ℝ) := by
  obtain ⟨a, e, hval⟩ := ax_mae (p + q) n hpq hn
  refine ⟨a, e, ?_⟩
  rw [hval]
  push_cast
  ring

end Intensional

/-! ## Ch.15 数値限界定理 (51)–(55) -/

/-- **Th.(15.51)** Boole–Fréchet 限界.
$\alpha/h + y/h - 1 \le \alpha y/h \le \min(\alpha/h,\ y/h)$.

Keynes Prolog DB: cites(th15_51, th14_24_2), cites(th15_51, def_x),
cites(th15_51, th13_2), cites(th15_51, th13_3).

## Proof architecture
| Step | Mechanism                          | Cites                  |
|------|------------------------------------|------------------------|
| 下界 | th_24 + ax_range_hi (α∨y ≤ 1)      | (24) + 範囲原理        |
| 上β  | def_IX α y h + ax_range_lo         | Def.IX + 範囲原理      |
| 上y  | def_IX y α h + ax_iii_op 交換      | Def.IX + Ax.(iii)      |

## 検証対象
- H3: ax_range_lo と ax_range_hi の両方が surface する (範囲原理の初 load-bearing)
- DB 引用の def_x は kernel 経路では不要 (Mode S 系データ点) -/
theorem th_15_51 (α y h : Prop) :
    (Pr α h + Pr y h - 1 ≤ Pr (α ∧ y) h) ∧
    (Pr (α ∧ y) h ≤ Pr α h) ∧
    (Pr (α ∧ y) h ≤ Pr y h) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Fréchet 下界: (24) と範囲原理上界から
    have h24 := th_24 α y h
    have hub := ax_range_hi (α ∨ y) h
    linarith
  · -- 上界 (対 α): def_IX の左分解と範囲原理下界から
    have h9 := def_IX α y h
    have hlo := ax_range_lo (α ∧ ¬y) h
    linarith
  · -- 上界 (対 y): def_IX を y 側に適用し、∧ 交換を ax_iii_op で処理
    have h9 := def_IX y α h
    have hlo := ax_range_lo (y ∧ ¬α) h
    have e : (y ∧ α) ↔ (α ∧ y) := by tauto
    rw [ax_iii_op _ _ h e] at h9
    linarith

/-- **n 項連言** (Arai 拡張定義)。Keynes の α₁α₂…αₙ を List で厳密化。 -/
def bigAnd : List Prop → Prop
  | [] => True
  | p :: rest => p ∧ bigAnd rest

/-- **確率の n 項和** (Arai 拡張定義)。Σ αᵢ/h。 -/
noncomputable def sumPr : List Prop → Prop → ℝ
  | [], _ => 0
  | p :: rest, h => Pr p h + sumPr rest h

/-- **Th.(15.52)** n 項 Bonferroni 下界.
$\alpha_1\alpha_2\cdots\alpha_n/h \ \ge\ \sum_i \alpha_i/h - (n-1)$.

Keynes Prolog DB: cites(th15_52, th15_51) — 「(51) の繰り返し適用」。
「繰り返し適用」は現代的には数学的帰納法である。本定理は監査全体で初めて
**本物の帰納法** (List.rec 経由の構造的再帰) を要求する。

## Proof architecture
| Step | Mechanism                     | Cites             |
|------|-------------------------------|-------------------|
| 基底 | ax_iii_true (空連言 = True)   | Ax.(iii)          |
| 帰納 | th_15_51 下界 + IH + linarith | (51) + 帰納法     |

## 検証対象 (H1 の判定点)
- #print axioms th_15_52 に List.rec / Nat.rec 型の新規公理が現れるか。
  予測: 現れない (再帰子は CIC の一部であり公理ではない)。
  現れなければ「公理監査は帰納法を検出できない」= Mode C シグネチャの
  測定限界が確定する。現れれば引き継ぎ書の予測が正しかったことになる。 -/
theorem th_15_52 (h : Prop) (l : List Prop) :
    sumPr l h - ((l.length : ℝ) - 1) ≤ Pr (bigAnd l) h := by
  induction l with
  | nil =>
      have h1 : Pr True h = 1 := ax_iii_true h
      simp only [sumPr, bigAnd, List.length_nil, Nat.cast_zero]
      rw [h1]
      norm_num
  | cons p rest ih =>
      have lower := (th_15_51 p (bigAnd rest) h).1
      simp only [sumPr, bigAnd, List.length_cons]
      push_cast
      linarith

/-- **Th.(15.53)** 対角和の二重上界.
$\alpha y/h + \bar\alpha\bar y/h \ \le\ 1 - \alpha/h + y/h$ かつ
$\alpha y/h + \bar\alpha\bar y/h \ \le\ 1 - y/h + \alpha/h$.

Keynes Prolog DB: cites(th15_53, th15_51).

## Proof architecture
4 象限分解 (def_IX ×3 + 補完律 th_13_1) + 範囲原理 + linarith。 -/
theorem th_15_53 (α y h : Prop) :
    (Pr (α ∧ y) h + Pr (¬α ∧ ¬y) h ≤ 1 - Pr α h + Pr y h) ∧
    (Pr (α ∧ y) h + Pr (¬α ∧ ¬y) h ≤ 1 - Pr y h + Pr α h) := by
  have hq1 := def_IX α y h          -- P(α∧¬y) + P(α∧y) = P α
  have hq2 := def_IX (¬α) y h       -- P(¬α∧¬y) + P(¬α∧y) = P ¬α
  have hcompl := th_13_1 α h        -- P α + P ¬α = 1
  have hq3 := def_IX y α h          -- P(y∧¬α) + P(y∧α) = P y
  have e1 : (y ∧ ¬α) ↔ (¬α ∧ y) := by tauto
  have e2 : (y ∧ α) ↔ (α ∧ y) := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at hq3
  have r1 := ax_range_lo (α ∧ ¬y) h
  have r2 := ax_range_lo (¬α ∧ y) h
  constructor <;> linarith

/-- **Th.(15.54)** 対角差の恒等式.
$\alpha y/h - \bar\alpha\bar y/h \ =\ \alpha/h + y/h - 1$.

Keynes Prolog DB: cites(th15_54, th15_51), cites(th15_54, th15_53)
— 「(51)(53) から直接導出」。

## 検証対象 (H2 の判定点)
Keynes は (54) を限界定理 (51)(53) の帰結として導くが、(54) は限界では
なく**恒等式**であり、4 象限分解だけで無条件に閉じる。予測される依存集合は
{def_IX, ax_iii_op, ax_iii_true} のみで、範囲原理も (51)(53) も不要。
確認されれば **Mode S 第 3 例** (DB 引用連鎖の kernel-level 短絡)。 -/
theorem th_15_54 (α y h : Prop) :
    Pr (α ∧ y) h - Pr (¬α ∧ ¬y) h = Pr α h + Pr y h - 1 := by
  have hq2 := def_IX (¬α) y h       -- P(¬α∧¬y) + P(¬α∧y) = P ¬α
  have hcompl := th_13_1 α h        -- P α + P ¬α = 1
  have hq3 := def_IX y α h          -- P(y∧¬α) + P(y∧α) = P y
  have e1 : (y ∧ ¬α) ↔ (¬α ∧ y) := by tauto
  have e2 : (y ∧ α) ↔ (α ∧ y) := by tauto
  rw [ax_iii_op _ _ h e1, ax_iii_op _ _ h e2] at hq3
  linarith

/-- **Th.(15.55)** Boole 消去法 scheme (系統的近似法).
未知確率 t が線型に入る量 P = A + B·t は、t の範囲原理 0 ≤ t ≤ 1 を代入
することで A ≤ P ≤ A + B に挟める (B ≥ 0 の場合の標準形)。
Keynes が Ch.15 で Boole の挑戦問題に適用する消去法の 1 ステップの厳密化。

Keynes Prolog DB: cites(th15_55, th13_2), cites(th15_55, th13_3),
cites(th15_55, ax_mae).

## 検証対象
- 純 ℝ 算術であり Keynes 公理はゼロ (floor 到達) と予測。
  Boole 消去法それ自体は substrate の営みであり、確率論的内容は
  「t に範囲原理を供給する」一点に集中している、という判定になる。
  (Ch.17 の Boole 問題群 [Phase 5] への橋渡し。) -/
theorem th_15_55 (P A B t : ℝ) (hB : 0 ≤ B) (hP : P = A + B * t)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : A ≤ P ∧ P ≤ A + B := by
  have hbt0 : 0 ≤ B * t := mul_nonneg hB h0
  have hbtB : B * t ≤ B := by
    nlinarith [mul_nonneg hB (sub_nonneg.mpr h1)]
  constructor <;> linarith

end Keynes

/-! ## 監査クエリ (Phase 4 新規) -/

#check @Keynes.th_15_degeneracy
#check @Keynes.Naive.collapse
#check @Keynes.th_ax_xviii_absorbed
#check @Keynes.th_ax_xix_absorbed
#check @Keynes.Intensional.th_15_50
#check @Keynes.th_15_51
#check @Keynes.th_15_52
#check @Keynes.th_15_53
#check @Keynes.th_15_54
#check @Keynes.th_15_55

-- Kernel 依存. 注目点:
--   th_15_degeneracy      : Classical.choice が em 経由で必須になるはず
--   Naive.collapse        : 結合矛盾に関与した公理の全リスト (監査証明書)
--   th_ax_xviii_absorbed  : floor 予測 (Keynes 公理ゼロ) — H4
--   th_ax_xix_absorbed    : floor 予測 (Keynes 公理ゼロ) — H4
--   Intensional.th_15_50  : PrI + ax_mae のみ
--   th_15_51              : 範囲原理 2 本が初 surface — H3
--   th_15_52              : ★ H1 判定点: 帰納法由来の新規公理が出るか
--   th_15_53              : 範囲原理 + 4 象限分解
--   th_15_54              : ★ H2 判定点: {def_IX, ax_iii_op, ax_iii_true} のみか
--   th_15_55              : floor 予測 (純 ℝ 算術)
#print axioms Keynes.th_15_degeneracy
#print axioms Keynes.Naive.collapse
#print axioms Keynes.th_ax_xviii_absorbed
#print axioms Keynes.th_ax_xix_absorbed
#print axioms Keynes.Intensional.th_15_50
#print axioms Keynes.th_15_51
#print axioms Keynes.th_15_52
#print axioms Keynes.th_15_53
#print axioms Keynes.th_15_54
#print axioms Keynes.th_15_55

-- 回帰テスト (再掲定理)
#print axioms Keynes.th_13_1
#print axioms Keynes.th_24
#print axioms Keynes.pr_false
