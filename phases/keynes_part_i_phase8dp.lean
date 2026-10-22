/- ============================================================
   PHASE 8d′ — 第6章「推論の重み」を推論 a/h の型の上で再構成する
   (第 I 部, Keynes (1921) Ch. VI, folio 71–79)

   出典アンカー (1921 年 Macmillan 初版の頁画像 folio_73.png, folio_74.png で照合):
   - folio 71 §1: "New evidence will sometimes decrease the probability
     of an argument, but it will always increase its 'weight.'"
   - folio 72 §2: 「関連」と「重みの増加」は相関語 (定義的同値)。
   - folio 73 §3 (ii): "V(a/hh₁) > V(a/h), unless h₁ is irrelevant, in
     which case V(a/hh₁) = V(a/h)." (iii) に対応する重みの規則は無い:
     "It might be thought that V(ab/h) < V(a/h) ... But this is invalid."
     同じ段落の末尾: "V(a/h) = V(ā/h). For an argument is always as near
     proving or disproving a proposition, as it is to disproving or
     proving its contradictory."
   - folio 73 §4 冒頭 (folio_73.png で照合; 印刷で斜体の語を *…* で示す):
     "It may be pointed out that if a/h = b/h, it does not necessarily
     follow that V(a/h) = V(b/h). It has been asserted already that if the
     first equality follows *directly* from a single application of the
     Principle of Indifference, the second equality also holds. But the
     first equality can exist in other cases also. If, for instance, a and
     b are members respectively of *different* sets of three equally
     probable exclusive and exhaustive alternatives, then a/h = b/h; but
     these arguments may have very different weights."
     第 2 文は §3 (i) を指す: "Arguments, that is to say, to which the
     Principle of Indifference is applicable, have equal evidential weights."
     — 同じ前提 h のもとで確率関係の値 α が等しくても重みは等しいとは
     限らない。第三段の写像は第二段の値 α の関数ではない。ただし同じ
     無差別原理の一適用から出る等式どうしは同じ重みをもつ。有限モデルの
     証人 (th_8dp_indifference_witness) はこの配置に従う:
     Ω = Fin 3 × Fin 3、h = Ω、第一の三択は行 {row 0, row 1, row 2}、
     第二の三択は列 {col 0, col 1, col 2} (th_8dp_two_triads)。
     V_rows のもとで行どうし・列どうしは同じ重み、row 0 と col 0 は
     a/h = b/h = 1/3 なのに重みが異なる。
   - folio 73 §4: "if a/bh = 1 and b/ah = 1, then V(a/h) = V(b/h)."
   - folio 73 末 – folio 74 冒頭 §4: 三つの排反網羅的選択肢 a, b, c について
     a/h = b/h (無差別原理) から V(a/h) = V(b/h) と V(a/h) = V(ā/h)、
     "since ā/(b+c)h = 1 and (b+c)/āh = 1, that V(ā/h) = V((b+c)/h).
     Hence V(b/h) = V((b+c)/h)."

   引用文献 (本ファイルで参照する既刊; 以下の本文では著者名・年で略記する):
   - 高籔・新井 (2011a) = 高籔 (名は語録に無く要裁定)・新井一成「Keynes「確率」
     の特殊性に関する研究：束および Prolog を用いて」『東京学芸大学紀要
     人文社会科学系II』第62集 (2011), pp. 175–187。
   - 新井 (2011) = 新井一成「Keynes『確率論』の構造分析」修士論文 (2011;
     大学・研究科は語録ヘッダに無く要裁定)。
     本文の「修論 3-3-3」は同論文の章-節-項、頁は同論文の頁。
   - 塩沢 (1983) = 塩沢由典「ケインズ『確率論』の論理構造」『別冊経済セミナー』
     (1983)。頁は手元で確定できず要裁定 (語録は「付録・第一二章への読者案内」
     p.78 として引くが、同誌の同論文内の付録かは手元で確定できない)。
     Γ (命題集合)・Π (確率集合)・π (写像集合) の三者の区別と、埋め込み
     規則 I/II・加法の一意性・外部算法の指摘の出典 (修論 3-3-3 が引く)。

   設計 (高籔・新井 2011a 注16 の第一段・第二段・第三段の写像、修論 3-3-3 の Γ/Π/π):
   - 命題集合 Γ は不透明型 IProp (phase6c の KeynesI と同じ公理)。
     命題を真偽で同一視しないので、propext による退化
     (phase8d の V_collapse: V a h = V True h) の経路が型レベルで無い。
   - 第一段の写像 (h, a) ↦ a/h は推論の型 Arg の構成子。単射
     (th_first_tier_injective)。
   - 第二段の写像 (確率関係相互の関係 π) は PrI と Keynes の操作公理
     def_IX_i / def_X_left_i / def_X_right_i (phase6c と同文) と
     確実性 I (ax_cert_i)。値の集合が Π。
   - 第三段の写像 V は推論の型の上に置く: V : Arg → ℝ。
     V の引数に Prop は使わない (phase8d の、命題を真偽で同一視する形は撤回)。
   - 重みの公理 ax_vi_mono_i / ax_vi_compl_i / ax_vi_equiv_i は phase8d の
     文言を IProp に移す。前提の連言は印刷の語順 (hh₁, (b+c)h, āh) に従う
     (phase8d の ax_vi_mono は h₁ ∧ h の語順だった)。IProp では
     iand h h₁ と iand h₁ h は別の項であり、どの公理も両者の重みを
     同一視しない (所見候補)。
   - 各定理の被導出関係は末尾の #print axioms の出力で確認する。

   有限モデル (必要性の判定): Γ = Finset Ω (Ω 有限)、Pr(a/h) = |a∩h|/|h|
   (h = ∅ では 0)。この Pr は def_IX_i, def_X_left_i, def_X_right_i,
   ax_range を満たす (一般の有限 Ω で証明)。用語:
     「h が a を証明または反証する」 = h ⊆ a または a ∩ h = ∅
       (decides; folio 73 "proving or disproving" に対応)。
     |hᶜ| = 前提 h と両立しない場合の数 (evid; h が狭まるほど増える)。
   V の候補:
     V₁ a h = |hᶜ| + [h が a を証明または反証する]
              … mono, compl, equiv すべて成立。ただし V₁ は第二段の値の
                関数 (V₁_function_of_prF) なので §4 冒頭の証人にならない。
     V_split S a h = |hᶜ| + [a∩h = S∩h または a∩h = h∖S] (S 固定)
              … mono, compl, equiv すべて成立。同じ h で a/h = b/h なのに
                V が異なる。ただし同じ三択の元どうしでも V が異なる
                (th_8dp_V_split_breaks_indifference) ので §3 (i) に反し、
                §4 の証人にはならない (第 3 回まではこれを証人にしていた)。
                S = Ω のとき V₁ に一致する (a∩h = h は h ⊆ a、a∩h = h∖Ω は
                a∩h = ∅)。
     V_rows a h = |hᶜ| + [a∩h が行の和 (ある I ⊆ Fin 3 で (I ×ˢ univ) ∩ h)]
              (Ω = Fin 3 × Fin 3)
              … mono, compl, equiv すべて成立。行どうし・列どうしは同じ V、
                行と列は a/h = b/h なのに V が異なる (§3 (i) を守る §4 の証人、
                th_8dp_indifference_witness)。
     V_half S a h = |hᶜ| + [a∩h = h∖S]     … compl 不成立、連鎖が破れる
     V₃ a h = |hᶜ| + |a|·|aᶜ|              … equiv 不成立、連鎖が破れる
     V₄ a h = |h| + [h が a を証明または反証する]
              … mono 不成立、連鎖は立つ

   埋め込み規則 I/II (修論 3-3-3 表6 = 塩沢 (1983) による埋め込み表):
   「Π の乗法は ab/h = a/bh · b/h で定義されるが、これは Π(bh) の元と
   Π(h) の元に対し積を Π(h) として与えるという外部算法となる。
   そのため一意的な「埋め込み」を決定しなければならない」(修論 p.50)。
   表6 は三原子 p, q, r について Π(ah) の元 ↦ j ∈ Π(h) を列挙する:
     規則 I : q/ph ↦ q/h, r/ph ↦ r/h, p/qh ↦ p/h, r/qh ↦ r/h,
              p/rh ↦ p/h, q/rh ↦ q/h    (乗法の規則 j · a = 元, 例 q·p = pq)
     規則 II: q/ph ↦ p/h, r/ph ↦ r/h, p/qh ↦ q/h, r/qh ↦ r/h,
              p/rh ↦ p/h, q/rh ↦ q/h    (例 p·p = pq)
   本ファイルの読み (裁定待ち): 規則 I の一般形は a/bh ↦ a/h (全 6 行が
   一致)。規則 II の一般形は pq 行から a/bh ↦ b/h と読む (pr, qr 行は
   規則 I と一致するため、規則 II の一般形は表6 だけからは確定しない)。
   判定:
     (d-0) 表6 の各行 (個別の式) は両列とも Ω = Fin 4 の有限モデルで
           同時に満たせる (p = {0,1}, q = {0,2}, r = {0,3}, h = Ω)。
           各行が満たせる以上のことは言えない: この証人は規則 I と
           規則 II を区別しない。
     (d-I) 一般形の規則 I は第二段の公理 (def_IX, def_X 両形, 値域) と
           無矛盾。有限モデル Γ = Bool (Pr(a/h) = [a]) がこれを満たし
           (th_8dp_rule_I_finite_model)、有限の Γ をもつモデルはすべて
           Π ⊆ {O, I} に退化する (th_8dp_rule_I_finite_degenerate)。
           すなわち有限の Γ では Pr は Γ 上の真偽評価 (各 a/h に O か I を
           与える写像) になる。Γ そのものの形は定理で言えていない。
           無限の Γ では Π = [0,1] の乗法モデルが値 1/2 をもつ
           (a∧a と a の確率が異なる)。
     (d-II) 一般形の規則 II は def_IX と def_X 左形だけから Pr ≡ 0 を
           強制する (定理)。Pr ≡ 0 自体は def_IX, def_X, 値域, 規則 II の
           解なので矛盾ではない (zeroModel, th_8dp_rule_II_zero_model:
           ax_cert_i の必要性の反例) が、確実性 I (ax_cert_i:
           PrI itrue h = 1) とは両立しない (th_8dp_rule_II_i_no_certainty)。
   ============================================================ -/

import Mathlib

noncomputable section
namespace KeynesWeightVIp

/-! ## 命題集合 Γ: 命題を真偽で同一視しない形式化 (phase6c の KeynesI と同文) -/

axiom IProp : Type
axiom iand : IProp → IProp → IProp
axiom ior  : IProp → IProp → IProp
axiom inot : IProp → IProp
axiom itrue : IProp

/-- 第二段の写像の値: 確率関係 a/h の値 α。 -/
axiom PrI : IProp → IProp → ℝ

/-- Def. IX (phase6c と同文)。 -/
axiom def_IX_i (p q h : IProp) :
    PrI (iand p (inot q)) h + PrI (iand p q) h = PrI p h
/-- Def. X 左形 (phase6c と同文): ab/h = (a/bh)·(b/h)。 -/
axiom def_X_left_i (p q h : IProp) :
    PrI (iand p q) h = PrI p (iand q h) * PrI q h
/-- Def. X 右形 (phase6c と同文): ab/h = (b/ah)·(a/h)。 -/
axiom def_X_right_i (p q h : IProp) :
    PrI (iand p q) h = PrI q (iand p h) * PrI p h
axiom ax_range_lo_i (p h : IProp) : 0 ≤ PrI p h
axiom ax_range_hi_i (p h : IProp) : PrI p h ≤ 1
/-- 確実性 I: itrue/h = 1。phase6c では ax_iii_taut から itrue_certain として
    導かれる。本ファイルでは第二段の公理として直接置く
    (規則 II との両立判定 th_8dp_rule_II_i_no_certainty にのみ用いる)。 -/
axiom ax_cert_i (h : IProp) : PrI itrue h = 1

/-! ## 第一段の写像: 推論 a/h の型 -/

/-- 推論 a/h: 後件命題 (結論) a と前件命題 (前提) h の対。 -/
structure Arg where
  concl : IProp
  prem  : IProp

/-- 第一段の写像 (h, a) ↦ a/h。 -/
def arg (a h : IProp) : Arg := ⟨a, h⟩

/-- 第一段の写像は単射: 推論 a/h は前提と結論を落とさない
    (高籔・新井 2011a §3.2 末尾の問いの、Γ を真偽で潰さない形式化での答)。 -/
theorem th_first_tier_injective :
    Function.Injective (fun p : IProp × IProp => arg p.1 p.2) := by
  intro p q hpq
  simp only [arg, Arg.mk.injEq] at hpq
  exact Prod.ext hpq.1 hpq.2

/-! ## 第三段の写像: 推論の重み V (推論の型の上に置く) -/

/-- 証拠 h のもとでの推論 a の「推論の重み」 V(a/h)。§3 の記法。 -/
axiom V : Arg → ℝ

/-- §1 核文の弱形 (folio 73 §3 (ii): "V(a/hh₁) > V(a/h), unless h₁ is
    irrelevant, in which case V(a/hh₁) = V(a/h)"): 証拠の追加は重みを
    決して減らさない。phase8d の ax_vi_mono は前提を h₁ ∧ h の語順で
    書いていた。本公理は印刷の語順 hh₁ に従い iand h h₁ とする (語順変更;
    IProp では iand h h₁ と iand h₁ h は別の項なので同文ではない)。 -/
axiom ax_vi_mono_i (a h h₁ : IProp) : V (arg a h) ≤ V (arg a (iand h h₁))

/-- §2 の相関性定義: 新しい証拠 h₁ が「関連」であるとは、
    それが推論の「重み」を増すことである。 -/
def Rel (h₁ a h : IProp) : Prop := V (arg a h) < V (arg a (iand h h₁))

/-- §3 folio 73: 補元対称性 V(a/h) = V(ā/h)。 -/
axiom ax_vi_compl_i (a h : IProp) : V (arg a h) = V (arg (inot a) h)

/-- §4 folio 73: 相互推論則 — a/bh = 1 かつ b/ah = 1 ならば V(a/h) = V(b/h)。 -/
axiom ax_vi_equiv_i (a b h : IProp) :
    PrI a (iand b h) = 1 → PrI b (iand a h) = 1 → V (arg a h) = V (arg b h)

/-! ## §2 の二分律と §4 の連鎖 (phase8d の再証明) -/

/-- 任意の証拠追加は「関連 (真に増加)」か「重み不変」のどちらか。 -/
theorem th_vi_2_dichotomy_i (a h h₁ : IProp) :
    Rel h₁ a h ∨ V (arg a (iand h h₁)) = V (arg a h) := by
  rcases lt_or_eq_of_le (ax_vi_mono_i a h h₁) with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'.symm

/-- §4 末尾の連鎖 (folio 73–74): 三つの排反網羅的選択肢 a, b, c について、
    無差別原理による V(a/h) = V(b/h) と、ā と b+c の相互推論
    (ā/(b+c)h = 1, (b+c)/āh = 1) から V(b/h) = V((b+c)/h)。 -/
theorem th_vi_4_chain_i (a b c h : IProp)
    (hind : V (arg a h) = V (arg b h))
    (h1 : PrI (inot a) (iand (ior b c) h) = 1)
    (h2 : PrI (ior b c) (iand (inot a) h) = 1) :
    V (arg b h) = V (arg (ior b c) h) := by
  calc V (arg b h) = V (arg a h) := hind.symm
    _ = V (arg (inot a) h) := ax_vi_compl_i a h
    _ = V (arg (ior b c) h) := ax_vi_equiv_i (inot a) (ior b c) h h1 h2

/-! ## 三段の写像を一つの構造として読む (有限モデルによる必要性の判定のため) -/

/-- 第6章の三段の写像をまとめた構造: 命題集合 Γ 上の結合子、
    第二段の値 Pr (Π の元)、第三段の値 V。
    V の型は Γ → Γ → ℝ (推論 a/h の二引数形)。 -/
structure WeightStructure (Γ : Type) where
  and_ : Γ → Γ → Γ
  or_  : Γ → Γ → Γ
  not_ : Γ → Γ
  Pr : Γ → Γ → ℝ
  V  : Γ → Γ → ℝ

namespace WeightStructure

variable {Γ : Type} (S : WeightStructure Γ)

/-- 第二段の公理 (def_IX_i, def_X_left_i, def_X_right_i, ax_range) の構造版。 -/
def KeynesPr : Prop :=
  (∀ p q h, S.Pr (S.and_ p (S.not_ q)) h + S.Pr (S.and_ p q) h = S.Pr p h) ∧
  (∀ p q h, S.Pr (S.and_ p q) h = S.Pr p (S.and_ q h) * S.Pr q h) ∧
  (∀ p q h, S.Pr (S.and_ p q) h = S.Pr q (S.and_ p h) * S.Pr p h) ∧
  (∀ p h, 0 ≤ S.Pr p h) ∧ (∀ p h, S.Pr p h ≤ 1)

/-- ax_cert_i の構造版: 確実性 I をとる定命題 (itrue の役をする元 t) がある。 -/
def Cert : Prop := ∃ t, ∀ h, S.Pr t h = 1

/-- ax_vi_mono_i の構造版。 -/
def Mono : Prop := ∀ a h h₁, S.V a h ≤ S.V a (S.and_ h h₁)
/-- ax_vi_compl_i の構造版。 -/
def Compl : Prop := ∀ a h, S.V a h = S.V (S.not_ a) h
/-- ax_vi_equiv_i の構造版。 -/
def Equiv : Prop := ∀ a b h,
  S.Pr a (S.and_ b h) = 1 → S.Pr b (S.and_ a h) = 1 → S.V a h = S.V b h
/-- th_vi_4_chain_i の主張の構造版。 -/
def Chain : Prop := ∀ a b c h,
  S.V a h = S.V b h →
  S.Pr (S.not_ a) (S.and_ (S.or_ b c) h) = 1 →
  S.Pr (S.or_ b c) (S.and_ (S.not_ a) h) = 1 →
  S.V b h = S.V (S.or_ b c) h

/-- 埋め込み規則 I の一般形: a/bh ↦ a/h。 -/
def RuleI : Prop := ∀ a b h, S.Pr a (S.and_ b h) = S.Pr a h
/-- 埋め込み規則 II の一般形 (表6 の pq 行の読み): a/bh ↦ b/h。 -/
def RuleII : Prop := ∀ a b h, S.Pr a (S.and_ b h) = S.Pr b h

/-- 連鎖は compl と equiv だけから立つ (th_vi_4_chain_i と同じ導出)。 -/
theorem chain_of_compl_equiv (hc : S.Compl) (he : S.Equiv) : S.Chain := by
  intro a b c h hind h1 h2
  calc S.V b h = S.V a h := hind.symm
    _ = S.V (S.not_ a) h := hc a h
    _ = S.V (S.or_ b c) h := he (S.not_ a) (S.or_ b c) h h1 h2

/-- (d-II) 規則 II の一般形は def_IX と def_X 左形だけから Pr ≡ 0 を強制する。 -/
theorem ruleII_zero
    (hIX : ∀ p q h, S.Pr (S.and_ p (S.not_ q)) h + S.Pr (S.and_ p q) h = S.Pr p h)
    (hX : ∀ p q h, S.Pr (S.and_ p q) h = S.Pr p (S.and_ q h) * S.Pr q h)
    (hII : S.RuleII) (p h : Γ) : S.Pr p h = 0 := by
  have hsq : ∀ p q, S.Pr (S.and_ p q) h = S.Pr q h * S.Pr q h := by
    intro p q; rw [hX, hII]
  have hconst : ∀ p', S.Pr p' h = S.Pr p h := by
    intro p'
    have e1 := hIX p p h
    have e2 := hIX p' p h
    rw [hsq, hsq] at e1 e2
    linarith
  have e1 := hIX p p h
  rw [hsq, hsq, hconst (S.not_ p)] at e1
  have e2 := hsq p p
  rw [hconst (S.and_ p p)] at e2
  have h1 : S.Pr p h * (2 * S.Pr p h - 1) = 0 := by linear_combination e1
  have h2 : S.Pr p h * (S.Pr p h - 1) = 0 := by linear_combination -e2
  rcases mul_eq_zero.mp h1 with h | h
  · exact h
  · rcases mul_eq_zero.mp h2 with h' | h'
    · exact h'
    · linarith

/-- (d-II) 規則 II の一般形は、値 I (= 1) をとる確率関係を一つも許さない。 -/
theorem ruleII_no_certainty
    (hIX : ∀ p q h, S.Pr (S.and_ p (S.not_ q)) h + S.Pr (S.and_ p q) h = S.Pr p h)
    (hX : ∀ p q h, S.Pr (S.and_ p q) h = S.Pr p (S.and_ q h) * S.Pr q h)
    (hII : S.RuleII) : ¬ ∃ p h, S.Pr p h = 1 := by
  rintro ⟨p, h, hp⟩
  have := S.ruleII_zero hIX hX hII p h
  linarith

/-- 規則 I の下では p∧p/h = (p/h)²。 -/
theorem ruleI_square
    (hX : ∀ p q h, S.Pr (S.and_ p q) h = S.Pr p (S.and_ q h) * S.Pr q h)
    (hI : S.RuleI) (p h : Γ) : S.Pr (S.and_ p p) h = S.Pr p h * S.Pr p h := by
  rw [hX, hI]

/-- p∧p の反復。 -/
def iterAnd (T : WeightStructure Γ) (p : Γ) : ℕ → Γ
  | 0 => p
  | n + 1 => T.and_ (iterAnd T p n) (iterAnd T p n)

/-- (d-I) 規則 I の一般形の下では、Γ が有限なら Π ⊆ {O, I} に退化する。 -/
theorem ruleI_finite_degenerate [Finite Γ]
    (hX : ∀ p q h, S.Pr (S.and_ p q) h = S.Pr p (S.and_ q h) * S.Pr q h)
    (hlo : ∀ p h, 0 ≤ S.Pr p h) (hhi : ∀ p h, S.Pr p h ≤ 1)
    (hI : S.RuleI) (p h : Γ) : S.Pr p h = 0 ∨ S.Pr p h = 1 := by
  by_contra hne
  rw [not_or] at hne
  have hv0 : 0 < S.Pr p h := lt_of_le_of_ne (hlo p h) (Ne.symm hne.1)
  have hv1 : S.Pr p h < 1 := lt_of_le_of_ne (hhi p h) hne.2
  have hval : ∀ n, S.Pr (iterAnd S p n) h = S.Pr p h ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp [iterAnd]
    | succ n ih =>
      simp only [iterAnd]
      rw [ruleI_square S hX hI, ih, ← pow_add, pow_succ, mul_two]
  have hanti : StrictAnti (fun n : ℕ => S.Pr p h ^ (2 ^ n)) := by
    intro m n hmn
    exact pow_lt_pow_right_of_lt_one₀ hv0 hv1 (Nat.pow_lt_pow_right (by norm_num) hmn)
  have hinj : Function.Injective (iterAnd S p) := by
    intro m n hmn
    have : S.Pr p h ^ (2 ^ m) = S.Pr p h ^ (2 ^ n) := by rw [← hval, ← hval, hmn]
    exact hanti.injective this
  exact not_injective_infinite_finite _ hinj

end WeightStructure

/-! ## 公理層を構造として読む (IProp 上の体系は WeightStructure の一例) -/

/-- IProp 上の公理そのもの。 -/
def axiomatic : WeightStructure IProp where
  and_ := iand
  or_ := ior
  not_ := inot
  Pr := PrI
  V := fun a h => V (arg a h)

theorem axiomatic_KeynesPr : axiomatic.KeynesPr :=
  ⟨def_IX_i, def_X_left_i, def_X_right_i, ax_range_lo_i, ax_range_hi_i⟩
theorem axiomatic_Cert : axiomatic.Cert := ⟨itrue, ax_cert_i⟩
theorem axiomatic_Mono : axiomatic.Mono := ax_vi_mono_i
theorem axiomatic_Compl : axiomatic.Compl := ax_vi_compl_i
theorem axiomatic_Equiv : axiomatic.Equiv := ax_vi_equiv_i

/-- (d-II) IProp 版: 規則 II の一般形を公理に加えると、すべての確率関係が 0 になる
    (Pr ≡ 0 を強制する)。被導出関係を正確に残すため、構造版を経由せず
    def_IX_i と def_X_left_i から直接導く。 -/
theorem th_8dp_rule_II_i (hII : ∀ a b h, PrI a (iand b h) = PrI b h) (p h : IProp) :
    PrI p h = 0 := by
  have hsq : ∀ p q, PrI (iand p q) h = PrI q h * PrI q h := by
    intro p q; rw [def_X_left_i, hII]
  have hconst : ∀ p', PrI p' h = PrI p h := by
    intro p'
    have e1 := def_IX_i p p h
    have e2 := def_IX_i p' p h
    rw [hsq, hsq] at e1 e2
    linarith
  have e1 := def_IX_i p p h
  rw [hsq, hsq, hconst (inot p)] at e1
  have e2 := hsq p p
  rw [hconst (iand p p)] at e2
  have h1 : PrI p h * (2 * PrI p h - 1) = 0 := by linear_combination e1
  have h2 : PrI p h * (PrI p h - 1) = 0 := by linear_combination -e2
  rcases mul_eq_zero.mp h1 with h | h
  · exact h
  · rcases mul_eq_zero.mp h2 with h' | h'
    · exact h'
    · linarith

/-- (d-II) IProp 版: 規則 II の一般形は確実性 I (ax_cert_i) と両立しない。
    被導出関係: def_IX_i, def_X_left_i, ax_cert_i。 -/
theorem th_8dp_rule_II_i_no_certainty
    (hII : ∀ a b h, PrI a (iand b h) = PrI b h) : False := by
  have h0 := th_8dp_rule_II_i hII itrue itrue
  have h1 := ax_cert_i itrue
  linarith

/-- (d-I) IProp 版: 規則 I の一般形の下では pp/h = (p/h)² (def_X_left_i のみ)。 -/
theorem th_8dp_rule_I_i_square (hI : ∀ a b h, PrI a (iand b h) = PrI a h) (p h : IProp) :
    PrI (iand p p) h = PrI p h * PrI p h := by
  rw [def_X_left_i, hI]

/-- (d-I) IProp 版: 規則 I に Th.(12) 型の同一視 pp/h = p/h を加えると
    p/h ∈ {0, 1} (Π が {I, O} に退化する)。 -/
theorem th_8dp_rule_I_i_degenerate (hI : ∀ a b h, PrI a (iand b h) = PrI a h)
    (p h : IProp) (h12 : PrI (iand p p) h = PrI p h) : PrI p h = 0 ∨ PrI p h = 1 := by
  have e := th_8dp_rule_I_i_square hI p h
  rw [h12] at e
  have : PrI p h * (PrI p h - 1) = 0 := by linear_combination -e
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-! ## 有限モデル: Γ = Finset Ω, Pr(a/h) = |a∩h|/|h| -/

section FiniteModel

variable {Ω : Type} [DecidableEq Ω]

/-- 第二段の値: Pr(a/h) = |a ∩ h| / |h|、h = ∅ では 0。 -/
def prF (a h : Finset Ω) : ℝ :=
  if h = ∅ then 0 else ((a ∩ h).card : ℝ) / (h.card : ℝ)

/-- prF の有理数版 (決定手続きで値を比べるため)。 -/
def prQ (a h : Finset Ω) : ℚ :=
  if h = ∅ then 0 else ((a ∩ h).card : ℚ) / (h.card : ℚ)

theorem prF_eq_prQ (a h : Finset Ω) : prF a h = (prQ a h : ℝ) := by
  unfold prF prQ
  split_ifs <;> push_cast <;> rfl

/-- h が a を証明または反証する (folio 73 "proving or disproving"):
    h ⊆ a (証明) または a ∩ h = ∅ (反証)。 -/
def decides (a h : Finset Ω) : Prop := h ⊆ a ∨ a ∩ h = ∅

instance (a h : Finset Ω) : Decidable (decides a h) := by
  unfold decides; infer_instance

/-- [h が a を証明または反証する] の指示量 (1 または 0)。 -/
def dec (a h : Finset Ω) : ℝ := if decides a h then 1 else 0

/-- h が a を証明または反証するなら、h ∩ h₁ もそうする。 -/
theorem decides_mono {a h : Finset Ω} (h₁ : Finset Ω) (hd : decides a h) :
    decides a (h ∩ h₁) := by
  rcases hd with hd | hd
  · exact Or.inl (Finset.inter_subset_left.trans hd)
  · right
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    simp only [Finset.mem_inter] at hx
    have : x ∈ a ∩ h := Finset.mem_inter.mpr ⟨hx.1, hx.2.1⟩
    rw [hd] at this
    exact Finset.notMem_empty x this

theorem dec_mono (a h h₁ : Finset Ω) : dec a h ≤ dec a (h ∩ h₁) := by
  unfold dec
  by_cases hd : decides a h
  · rw [if_pos hd, if_pos (decides_mono h₁ hd)]
  · rw [if_neg hd]; split_ifs <;> norm_num

/-- Pr(a/h) = 1 は「h ≠ ∅ かつ h ⊆ a」と同じ。 -/
theorem prF_eq_one_iff (a h : Finset Ω) : prF a h = 1 ↔ h ≠ ∅ ∧ h ⊆ a := by
  unfold prF
  by_cases hh : h = ∅
  · simp [hh]
  · rw [if_neg hh]
    have hpos : (0 : ℝ) < h.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hh)
    rw [div_eq_one_iff_eq hpos.ne']
    constructor
    · intro hc
      refine ⟨hh, ?_⟩
      have hsub : a ∩ h ⊆ h := Finset.inter_subset_right
      have heq : a ∩ h = h := Finset.eq_of_subset_of_card_le hsub (by exact_mod_cast hc.ge)
      intro x hx
      rw [← heq] at hx
      exact (Finset.mem_inter.mp hx).1
    · rintro ⟨_, hs⟩
      rw [Finset.inter_eq_right.mpr hs]

/-- h ≠ ∅ のとき Pr(a/h) = 0 は a ∩ h = ∅ と同じ。 -/
theorem prF_eq_zero_iff (a h : Finset Ω) (hh : h ≠ ∅) : prF a h = 0 ↔ a ∩ h = ∅ := by
  unfold prF
  rw [if_neg hh]
  have hpos : (0 : ℝ) < h.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [div_eq_zero_iff]
  constructor
  · rintro (hc | hc)
    · exact Finset.card_eq_zero.mp (by exact_mod_cast hc)
    · exact absurd hc hpos.ne'
  · intro he
    left
    rw [he, Finset.card_empty]; simp

/-- h ≠ ∅ のとき「h が a を証明または反証する」は Pr(a/h) ∈ {1, 0} と同じ。 -/
theorem decides_iff_prF (a h : Finset Ω) (hh : h ≠ ∅) :
    decides a h ↔ (prF a h = 1 ∨ prF a h = 0) := by
  unfold decides
  rw [prF_eq_one_iff, prF_eq_zero_iff a h hh]
  constructor
  · rintro (hs | he)
    · exact Or.inl ⟨hh, hs⟩
    · exact Or.inr he
  · rintro (⟨_, hs⟩ | he)
    · exact Or.inl hs
    · exact Or.inr he

/-- 相互推論 (a/bh = 1, b/ah = 1) は a ∩ h = b ∩ h を与える。 -/
theorem inter_eq_of_mutual {a b h : Finset Ω}
    (h1 : prF a (b ∩ h) = 1) (h2 : prF b (a ∩ h) = 1) : a ∩ h = b ∩ h := by
  obtain ⟨_, hs1⟩ := (prF_eq_one_iff _ _).mp h1
  obtain ⟨_, hs2⟩ := (prF_eq_one_iff _ _).mp h2
  apply Finset.Subset.antisymm
  · intro x hx
    exact Finset.mem_inter.mpr ⟨hs2 hx, (Finset.mem_inter.mp hx).2⟩
  · intro x hx
    exact Finset.mem_inter.mpr ⟨hs1 hx, (Finset.mem_inter.mp hx).2⟩

/-- 「証明または反証する」は a ∩ h だけで決まる。 -/
theorem decides_congr {a b h : Finset Ω} (hab : a ∩ h = b ∩ h) :
    decides a h ↔ decides b h := by
  unfold decides
  have key : ∀ {x y : Finset Ω}, x ∩ h = y ∩ h → h ⊆ x → h ⊆ y := by
    intro x y hxy hs z hz
    have : z ∈ x ∩ h := Finset.mem_inter.mpr ⟨hs hz, hz⟩
    rw [hxy] at this
    exact (Finset.mem_inter.mp this).1
  constructor
  · rintro (hs | he)
    · exact Or.inl (key hab hs)
    · right; rw [← hab]; exact he
  · rintro (hs | he)
    · exact Or.inl (key hab.symm hs)
    · right; rw [hab]; exact he

theorem dec_congr {a b h : Finset Ω} (hab : a ∩ h = b ∩ h) : dec a h = dec b h := by
  unfold dec
  by_cases hd : decides a h
  · rw [if_pos hd, if_pos ((decides_congr hab).mp hd)]
  · rw [if_neg hd, if_neg (fun h' => hd ((decides_congr hab).mpr h'))]

theorem prF_X_left (p q h : Finset Ω) : prF (p ∩ q) h = prF p (q ∩ h) * prF q h := by
  unfold prF
  by_cases hh : h = ∅
  · simp [hh]
  · rw [if_neg hh, if_neg hh]
    by_cases hqh : q ∩ h = ∅
    · rw [if_pos hqh, zero_mul]
      have : p ∩ q ∩ h = ∅ := by
        rw [Finset.inter_assoc, hqh, Finset.inter_empty]
      rw [this, Finset.card_empty]; simp
    · rw [if_neg hqh]
      have hc : ((q ∩ h).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hqh)).ne'
      rw [Finset.inter_assoc]
      field_simp

theorem prF_X_right (p q h : Finset Ω) : prF (p ∩ q) h = prF q (p ∩ h) * prF p h := by
  rw [Finset.inter_comm p q]
  exact prF_X_left q p h

theorem prF_nonneg (p h : Finset Ω) : 0 ≤ prF p h := by
  unfold prF; split_ifs
  · exact le_rfl
  · positivity

theorem prF_le_one (p h : Finset Ω) : prF p h ≤ 1 := by
  unfold prF
  by_cases hh : h = ∅
  · simp [hh]
  · rw [if_neg hh]
    have hpos : (0 : ℝ) < h.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hh)
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right

variable [Fintype Ω]

/-- 証拠の量の指標: 前提 h と両立しない場合の数 |hᶜ|。h が狭まるほど増える。 -/
def evid (h : Finset Ω) : ℝ := (hᶜ.card : ℝ)

/-- 証拠の追加は |hᶜ| を減らさない。 -/
theorem evid_mono (h h₁ : Finset Ω) : evid h ≤ evid (h ∩ h₁) := by
  unfold evid
  exact_mod_cast Finset.card_le_card (Finset.compl_subset_compl.mpr Finset.inter_subset_left)

/-- 前提が真に狭まれば |hᶜ| は少なくとも 1 増える。 -/
theorem evid_succ_le_of_ssubset {h h' : Finset Ω} (hs : h' ⊂ h) : evid h + 1 ≤ evid h' := by
  unfold evid
  rw [Finset.card_compl, Finset.card_compl, Nat.cast_sub (Finset.card_le_univ h),
    Nat.cast_sub (Finset.card_le_univ h')]
  have hlt := Finset.card_lt_card hs
  have : (h'.card : ℝ) + 1 ≤ h.card := by exact_mod_cast hlt
  linarith

/-- h が a を証明または反証することと、h が ā を証明または反証することは同じ。 -/
theorem decides_compl (a h : Finset Ω) : decides a h ↔ decides aᶜ h := by
  unfold decides
  constructor
  · rintro (hs | he)
    · right
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_compl] at hx
      exact hx.1 (hs hx.2)
    · left
      intro x hx
      rw [Finset.mem_compl]
      intro ha
      have : x ∈ a ∩ h := Finset.mem_inter.mpr ⟨ha, hx⟩
      rw [he] at this
      exact Finset.notMem_empty x this
  · rintro (hs | he)
    · right
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      simp only [Finset.mem_inter] at hx
      exact (Finset.mem_compl.mp (hs hx.2)) hx.1
    · left
      intro x hx
      by_contra ha
      have : x ∈ aᶜ ∩ h := Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr ha, hx⟩
      rw [he] at this
      exact Finset.notMem_empty x this

theorem dec_compl (a h : Finset Ω) : dec a h = dec aᶜ h := by
  unfold dec
  by_cases hd : decides a h
  · rw [if_pos hd, if_pos ((decides_compl a h).mp hd)]
  · rw [if_neg hd, if_neg (fun h' => hd ((decides_compl a h).mpr h'))]

theorem prF_IX (p q h : Finset Ω) : prF (p ∩ qᶜ) h + prF (p ∩ q) h = prF p h := by
  unfold prF
  by_cases hh : h = ∅
  · simp [hh]
  · rw [if_neg hh, if_neg hh, if_neg hh, ← add_div]
    congr 1
    have : (p ∩ qᶜ ∩ h).card + (p ∩ q ∩ h).card = (p ∩ h).card := by
      have e1 : p ∩ qᶜ ∩ h = (p ∩ h).filter (fun x => x ∉ q) := by
        ext x; simp [Finset.mem_filter, Finset.mem_inter, Finset.mem_compl]; tauto
      have e2 : p ∩ q ∩ h = (p ∩ h).filter (fun x => x ∈ q) := by
        ext x; simp [Finset.mem_filter, Finset.mem_inter]; tauto
      rw [e1, e2, add_comm]
      exact Finset.card_filter_add_card_filter_not _
    exact_mod_cast this

/-- 有限モデルの構造 (第三段の写像 V を差し替えて使う)。 -/
def finModel (Vf : Finset Ω → Finset Ω → ℝ) : WeightStructure (Finset Ω) where
  and_ := fun a b => a ∩ b
  or_ := fun a b => a ∪ b
  not_ := fun a => aᶜ
  Pr := prF
  V := Vf

theorem finModel_V (Vf : Finset Ω → Finset Ω → ℝ) (a h : Finset Ω) :
    (finModel Vf).V a h = Vf a h := rfl
theorem finModel_Pr (Vf : Finset Ω → Finset Ω → ℝ) (a h : Finset Ω) :
    (finModel Vf).Pr a h = prF a h := rfl
theorem finModel_and (Vf : Finset Ω → Finset Ω → ℝ) (a b : Finset Ω) :
    (finModel Vf).and_ a b = a ∩ b := rfl
theorem finModel_or (Vf : Finset Ω → Finset Ω → ℝ) (a b : Finset Ω) :
    (finModel Vf).or_ a b = a ∪ b := rfl
theorem finModel_not (Vf : Finset Ω → Finset Ω → ℝ) (a : Finset Ω) :
    (finModel Vf).not_ a = aᶜ := rfl

theorem finModel_KeynesPr (Vf : Finset Ω → Finset Ω → ℝ) : (finModel Vf).KeynesPr :=
  ⟨prF_IX, prF_X_left, prF_X_right, prF_nonneg, prF_le_one⟩

/-! ### V₁ = |hᶜ| + [h が a を証明または反証する]: 三公理すべてが成立 -/

def V₁ (a h : Finset Ω) : ℝ := evid h + dec a h

theorem V₁_mono : (finModel (Ω := Ω) V₁).Mono := by
  intro a h h₁
  show evid h + dec a h ≤ evid (h ∩ h₁) + dec a (h ∩ h₁)
  exact add_le_add (evid_mono h h₁) (dec_mono a h h₁)

theorem V₁_compl : (finModel (Ω := Ω) V₁).Compl := by
  intro a h
  show evid h + dec a h = evid h + dec aᶜ h
  rw [dec_compl]

theorem V₁_equiv : (finModel (Ω := Ω) V₁).Equiv := by
  intro a b h h1 h2
  show evid h + dec a h = evid h + dec b h
  rw [dec_congr (inter_eq_of_mutual h1 h2)]

/-- V₁ は第二段の値の関数: 同じ h で a/h = b/h なら V₁(a/h) = V₁(b/h)。
    したがって V₁ は folio 73 §4 冒頭の主張の証人にならない (V_split が要る)。 -/
theorem V₁_function_of_prF (a b h : Finset Ω) (hp : prF a h = prF b h) :
    V₁ a h = V₁ b h := by
  unfold V₁ dec
  by_cases hh : h = ∅
  · subst hh
    have ha : decides a ∅ := Or.inl (Finset.empty_subset a)
    have hb : decides b ∅ := Or.inl (Finset.empty_subset b)
    rw [if_pos ha, if_pos hb]
  · have key : decides a h ↔ decides b h := by
      rw [decides_iff_prF a h hh, decides_iff_prF b h hh, hp]
    by_cases hd : decides a h
    · rw [if_pos hd, if_pos (key.mp hd)]
    · rw [if_neg hd, if_neg (fun h' => hd (key.mpr h'))]

/-! ### |hᶜ| + g(a∩h, h) の形の重み (g は 0 と 1 の間)
    第二段の値 Pr(a/h) が a ∩ h だけで決まるのと同じく、g も a ∩ h (と h) だけで決まる。
    mono は、前提が真に狭まれば |hᶜ| が少なくとも 1 増え、g の変化は高々 1 であることから
    (|hᶜ| の項を落とすと mono は証明できない: 必要性テスト済み)。 -/

def Vg (g : Finset Ω → Finset Ω → ℝ) (a h : Finset Ω) : ℝ := evid h + g (a ∩ h) h

theorem Vg_mono (g : Finset Ω → Finset Ω → ℝ)
    (hg0 : ∀ X h, 0 ≤ g X h) (hg1 : ∀ X h, g X h ≤ 1) :
    (finModel (Ω := Ω) (Vg g)).Mono := by
  intro a h h₁
  show Vg g a h ≤ Vg g a (h ∩ h₁)
  unfold Vg
  by_cases heq : h ∩ h₁ = h
  · rw [heq]
  · have hs : h ∩ h₁ ⊂ h := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, heq⟩
    have e := evid_succ_le_of_ssubset hs
    have g0 := hg0 (a ∩ (h ∩ h₁)) (h ∩ h₁)
    have g1 := hg1 (a ∩ h) h
    linarith

theorem Vg_equiv (g : Finset Ω → Finset Ω → ℝ) : (finModel (Ω := Ω) (Vg g)).Equiv := by
  intro a b h h1 h2
  show Vg g a h = Vg g b h
  unfold Vg
  rw [inter_eq_of_mutual h1 h2]

/-- ā ∩ h は h から a ∩ h を除いたもの。 -/
theorem compl_inter_eq (a h : Finset Ω) : aᶜ ∩ h = h \ (a ∩ h) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
  tauto

/-- g が h の中の補元 (X ↦ h ∖ X) で不変なら、Vg g は compl を満たす。 -/
theorem Vg_compl (g : Finset Ω → Finset Ω → ℝ)
    (hg : ∀ X h, X ⊆ h → g (h \ X) h = g X h) : (finModel (Ω := Ω) (Vg g)).Compl := by
  intro a h
  show Vg g a h = Vg g aᶜ h
  unfold Vg
  rw [compl_inter_eq, hg _ _ Finset.inter_subset_right]

omit [Fintype Ω] in
theorem sdiff_inter_right_eq (S h : Finset Ω) : h \ (S ∩ h) = h \ S := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

omit [Fintype Ω] in
theorem sdiff_sdiff_eq_inter (S h : Finset Ω) : h \ (h \ S) = S ∩ h := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-! ### V_split S = |hᶜ| + [a∩h = S∩h または a∩h = h∖S]: 三公理すべてが成立し、
    同じ h で a/h = b/h なのに V が異なる (folio 73 §4 冒頭の証人)。
    固定した区分 S について、h のもとで a が S 側か S の反対側かに一致するとき 1。 -/

/-- h のもとで X (= a ∩ h) が S 側か S の反対側かに一致する。 -/
def splits (S X h : Finset Ω) : Prop := X = S ∩ h ∨ X = h \ S

instance (S X h : Finset Ω) : Decidable (splits S X h) := by
  unfold splits; infer_instance

def splitInd (S X h : Finset Ω) : ℝ := if splits S X h then 1 else 0

omit [Fintype Ω] in
theorem splitInd_nonneg (S X h : Finset Ω) : 0 ≤ splitInd S X h := by
  unfold splitInd; split_ifs <;> norm_num

omit [Fintype Ω] in
theorem splitInd_le_one (S X h : Finset Ω) : splitInd S X h ≤ 1 := by
  unfold splitInd; split_ifs <;> norm_num

omit [Fintype Ω] in
/-- X ⊆ h のとき、h ∖ X が S 側か反対側かに一致することと X がそうであることは同じ。 -/
theorem splits_sdiff_iff {S X h : Finset Ω} (hX : X ⊆ h) :
    splits S (h \ X) h ↔ splits S X h := by
  unfold splits
  constructor
  · rintro (e | e)
    · right
      calc X = h \ (h \ X) := (Finset.sdiff_sdiff_eq_self hX).symm
        _ = h \ (S ∩ h) := by rw [e]
        _ = h \ S := sdiff_inter_right_eq S h
    · left
      calc X = h \ (h \ X) := (Finset.sdiff_sdiff_eq_self hX).symm
        _ = h \ (h \ S) := by rw [e]
        _ = S ∩ h := sdiff_sdiff_eq_inter S h
  · rintro (e | e)
    · right; rw [e]; exact sdiff_inter_right_eq S h
    · left; rw [e]; exact sdiff_sdiff_eq_inter S h

theorem splits_compl (S a h : Finset Ω) : splits S (aᶜ ∩ h) h ↔ splits S (a ∩ h) h := by
  rw [compl_inter_eq]
  exact splits_sdiff_iff Finset.inter_subset_right

def V_split (S : Finset Ω) : Finset Ω → Finset Ω → ℝ := Vg (splitInd S)

theorem V_split_mono (S : Finset Ω) : (finModel (Ω := Ω) (V_split S)).Mono :=
  Vg_mono _ (splitInd_nonneg S) (splitInd_le_one S)

theorem V_split_equiv (S : Finset Ω) : (finModel (Ω := Ω) (V_split S)).Equiv :=
  Vg_equiv _

theorem V_split_compl (S : Finset Ω) : (finModel (Ω := Ω) (V_split S)).Compl := by
  intro a h
  show Vg (splitInd S) a h = Vg (splitInd S) aᶜ h
  unfold Vg splitInd
  by_cases hs : splits S (a ∩ h) h
  · rw [if_pos hs, if_pos ((splits_compl S a h).mpr hs)]
  · rw [if_neg hs, if_neg (fun h' => hs ((splits_compl S a h).mp h'))]

/-! ### V_half S = |hᶜ| + [a∩h = h∖S]: V_split の片側だけを残す。
    compl が落ち、連鎖が破れる。 -/

/-- h のもとで X (= a ∩ h) が S の反対側に一致する (片側)。 -/
def half (S X h : Finset Ω) : Prop := X = h \ S

instance (S X h : Finset Ω) : Decidable (half S X h) := by
  unfold half; infer_instance

def halfInd (S X h : Finset Ω) : ℝ := if half S X h then 1 else 0

omit [Fintype Ω] in
theorem halfInd_nonneg (S X h : Finset Ω) : 0 ≤ halfInd S X h := by
  unfold halfInd; split_ifs <;> norm_num

omit [Fintype Ω] in
theorem halfInd_le_one (S X h : Finset Ω) : halfInd S X h ≤ 1 := by
  unfold halfInd; split_ifs <;> norm_num

def V_half (S : Finset Ω) : Finset Ω → Finset Ω → ℝ := Vg (halfInd S)

theorem V_half_mono (S : Finset Ω) : (finModel (Ω := Ω) (V_half S)).Mono :=
  Vg_mono _ (halfInd_nonneg S) (halfInd_le_one S)

theorem V_half_equiv (S : Finset Ω) : (finModel (Ω := Ω) (V_half S)).Equiv :=
  Vg_equiv _

/-! ### V₃ = |hᶜ| + |a|·|aᶜ|: equiv が落ちると連鎖が破れる -/

def V₃ (a h : Finset Ω) : ℝ := evid h + (a.card : ℝ) * (aᶜ.card : ℝ)

theorem V₃_mono : (finModel (Ω := Ω) V₃).Mono := by
  intro a h h₁
  show evid h + (a.card : ℝ) * (aᶜ.card : ℝ) ≤ evid (h ∩ h₁) + (a.card : ℝ) * (aᶜ.card : ℝ)
  exact add_le_add (evid_mono h h₁) le_rfl

theorem V₃_compl : (finModel (Ω := Ω) V₃).Compl := by
  intro a h
  show evid h + (a.card : ℝ) * (aᶜ.card : ℝ) = evid h + (aᶜ.card : ℝ) * (aᶜᶜ.card : ℝ)
  rw [compl_compl, mul_comm]

/-! ### V₄ = |h| + [h が a を証明または反証する]: mono が落ちても連鎖は立つ -/

def V₄ (a h : Finset Ω) : ℝ := (h.card : ℝ) + dec a h

theorem V₄_compl : (finModel (Ω := Ω) V₄).Compl := by
  intro a h
  show (h.card : ℝ) + dec a h = (h.card : ℝ) + dec aᶜ h
  rw [dec_compl]

theorem V₄_equiv : (finModel (Ω := Ω) V₄).Equiv := by
  intro a b h h1 h2
  show (h.card : ℝ) + dec a h = (h.card : ℝ) + dec b h
  rw [dec_congr (inter_eq_of_mutual h1 h2)]

end FiniteModel

/-! ## 具体例 Ω = Fin 2, Fin 3, Fin 4: 退化しないこと・必要性 -/

section Witnesses

open WeightStructure

/-- (a) 退化が起きない: 三公理と第二段の公理をすべて満たし、同じ前提 h の
    二つの推論で V が異なる有限モデルが存在する (phase8d の V_collapse の否定形)。
    証人: Ω = Fin 2, h = univ, a = univ (h が証明する) と b = {0} (証明も反証もしない)。 -/
theorem th_8dp_nondegenerate :
    ∃ (Γ : Type) (S : WeightStructure Γ), S.KeynesPr ∧ S.Mono ∧ S.Compl ∧ S.Equiv ∧
      ∃ a b h : Γ, S.V a h ≠ S.V b h := by
  refine ⟨Finset (Fin 2), finModel V₁, finModel_KeynesPr _, V₁_mono, V₁_compl, V₁_equiv,
    Finset.univ, {0}, Finset.univ, ?_⟩
  have e1 : decides (Finset.univ : Finset (Fin 2)) Finset.univ := Or.inl (subset_refl _)
  have e2 : ¬ decides ({0} : Finset (Fin 2)) Finset.univ := by decide +kernel
  have c1 : (Finset.univ : Finset (Fin 2))ᶜ.card = 0 := by decide +kernel
  simp only [finModel_V, V₁, dec, evid, if_pos e1, if_neg e2, c1]
  norm_num

/-- Ω = Fin 3 × Fin 3 の行 i: 第一の三択 (行) の i 番目の選択肢。 -/
def row (i : Fin 3) : Finset (Fin 3 × Fin 3) := {i} ×ˢ Finset.univ
/-- Ω = Fin 3 × Fin 3 の列 j: 第二の三択 (列) の j 番目の選択肢。 -/
def col (j : Fin 3) : Finset (Fin 3 × Fin 3) := Finset.univ ×ˢ {j}

/-- folio 73 §4 の配置 "different sets of three equally probable exclusive and
    exhaustive alternatives": h = Ω のもとで、行 {row 0, row 1, row 2} と
    列 {col 0, col 1, col 2} はそれぞれ三つの等確率 (1/3) な排反網羅的選択肢の組で、
    a = row 0 と b = col 0 は別々の組の元 (row 0 ≠ col 0)。 -/
theorem th_8dp_two_triads :
    let h : Finset (Fin 3 × Fin 3) := Finset.univ
    (∀ i, prF (row i) h = 1 / 3) ∧ (∀ j, prF (col j) h = 1 / 3) ∧
    (∀ i j, i ≠ j → row i ∩ row j = ∅) ∧ (∀ i j, i ≠ j → col i ∩ col j = ∅) ∧
    (row 0 ∪ row 1 ∪ row 2 = h) ∧ (col 0 ∪ col 1 ∪ col 2 = h) ∧ row 0 ≠ col 0 := by
  intro h
  have e1 : ∀ i, prF (row i) h = 1 / 3 := by
    intro i
    rw [prF_eq_prQ]
    have : prQ (row i) h = 1 / 3 := by revert i; decide +kernel
    rw [this]; norm_num
  have e2 : ∀ j, prF (col j) h = 1 / 3 := by
    intro j
    rw [prF_eq_prQ]
    have : prQ (col j) h = 1 / 3 := by revert j; decide +kernel
    rw [this]; norm_num
  exact ⟨e1, e2, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-! ### §4 の証人 V_rows = |hᶜ| + [a∩h が行の和]: Ω = Fin 3 × Fin 3 で、
    h の中で a が「行の和」(ある I ⊆ Fin 3 について (I ×ˢ univ) ∩ h) に一致するとき 1。
    行の和は h の中の補元で閉じる (I ↦ Iᶜ) ので compl が立つ。
    同じ三択 (行どうし、列どうし) では V が等しく、別の三択 (行と列) では V が異なる。 -/

/-- 行の和: ある I ⊆ Fin 3 について X = (I ×ˢ univ) ∩ h。 -/
def rowSum (X h : Finset (Fin 3 × Fin 3)) : Prop :=
  ∃ I : Finset (Fin 3), X = (I ×ˢ Finset.univ) ∩ h

instance (X h : Finset (Fin 3 × Fin 3)) : Decidable (rowSum X h) := by
  unfold rowSum; infer_instance

/-- 行の和は h の中の補元で閉じる: X = (I ×ˢ univ) ∩ h なら h ∖ X = (Iᶜ ×ˢ univ) ∩ h。 -/
theorem rowSum_sdiff {X h : Finset (Fin 3 × Fin 3)} (hr : rowSum X h) : rowSum (h \ X) h := by
  obtain ⟨I, hI⟩ := hr
  refine ⟨Iᶜ, ?_⟩
  ext x
  simp only [hI, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_product, Finset.mem_univ,
    Finset.mem_compl, and_true]
  tauto

theorem rowSum_sdiff_iff {X h : Finset (Fin 3 × Fin 3)} (hX : X ⊆ h) :
    rowSum (h \ X) h ↔ rowSum X h := by
  constructor
  · intro hr
    have := rowSum_sdiff hr
    rwa [Finset.sdiff_sdiff_eq_self hX] at this
  · exact rowSum_sdiff

def rowSumInd (X h : Finset (Fin 3 × Fin 3)) : ℝ := if rowSum X h then 1 else 0

theorem rowSumInd_nonneg (X h : Finset (Fin 3 × Fin 3)) : 0 ≤ rowSumInd X h := by
  unfold rowSumInd; split_ifs <;> norm_num

theorem rowSumInd_le_one (X h : Finset (Fin 3 × Fin 3)) : rowSumInd X h ≤ 1 := by
  unfold rowSumInd; split_ifs <;> norm_num

theorem rowSumInd_sdiff (X h : Finset (Fin 3 × Fin 3)) (hX : X ⊆ h) :
    rowSumInd (h \ X) h = rowSumInd X h := by
  simp only [rowSumInd, rowSum_sdiff_iff hX]

def V_rows : Finset (Fin 3 × Fin 3) → Finset (Fin 3 × Fin 3) → ℝ := Vg rowSumInd

theorem V_rows_mono : (finModel V_rows).Mono :=
  Vg_mono _ rowSumInd_nonneg rowSumInd_le_one

theorem V_rows_equiv : (finModel V_rows).Equiv :=
  Vg_equiv _

theorem V_rows_compl : (finModel V_rows).Compl :=
  Vg_compl _ rowSumInd_sdiff

/-- (a′) folio 73 §4 第 1–3 文 (folio_73.png; 印刷で斜体の語を *…* で示す):
    "It may be pointed out that if a/h = b/h, it does not necessarily follow that
    V(a/h) = V(b/h). It has been asserted already that if the first equality
    follows *directly* from a single application of the Principle of
    Indifference, the second equality also holds. But the first equality can
    exist in other cases also. If, for instance, a and b are members
    respectively of *different* sets of three equally probable exclusive and
    exhaustive alternatives, then a/h = b/h; but these arguments may have very
    different weights."
    第 2 文が指す §3 (i) (folio 73): "V(φa/ψa.h₁) = V(φb/ψb.h₂), where h₁ and h₂
    are irrelevant in the strict sense. Arguments, that is to say, to which the
    Principle of Indifference is applicable, have equal evidential weights."
    証人 (原典の配置に従う; th_8dp_two_triads): Ω = Fin 3 × Fin 3, h = univ,
    第一の三択 = 行, 第二の三択 = 列。V_rows のもとで
    (1) 同じ無差別原理の一適用から出る等式 (行どうし、列どうし) は同じ重み:
        V(row i/h) = V(row j/h), V(col i/h) = V(col j/h) (§3 (i), §4 第 2 文);
    (2) 別の三択の元どうしは a/h = b/h (= 1/3) なのに V が異なる:
        V(row 0/h) = 1 ≠ 0 = V(col 0/h) (§4 第 3 文)。
    三公理と第二段の公理をすべて満たす同じモデルの中でこれが起きる。 -/
theorem th_8dp_indifference_witness :
    let S := finModel (Ω := Fin 3 × Fin 3) V_rows
    let h : Finset (Fin 3 × Fin 3) := Finset.univ
    S.KeynesPr ∧ S.Mono ∧ S.Compl ∧ S.Equiv ∧
    (∀ i j, S.Pr (row i) h = S.Pr (col j) h) ∧
    (∀ i j, S.V (row i) h = S.V (row j) h) ∧
    (∀ i j, S.V (col i) h = S.V (col j) h) ∧
    S.V (row 0) h ≠ S.V (col 0) h := by
  intro S h
  have hr : ∀ i, rowSum (row i ∩ h) h := by decide +kernel
  have hc : ∀ j, ¬ rowSum (col j ∩ h) h := by decide +kernel
  have c1 : hᶜ.card = 0 := by decide +kernel
  have vr : ∀ i, S.V (row i) h = 1 := by
    intro i
    show Vg rowSumInd (row i) h = 1
    unfold Vg rowSumInd evid
    rw [if_pos (hr i), c1]; norm_num
  have vc : ∀ j, S.V (col j) h = 0 := by
    intro j
    show Vg rowSumInd (col j) h = 0
    unfold Vg rowSumInd evid
    rw [if_neg (hc j), c1]; norm_num
  refine ⟨finModel_KeynesPr _, V_rows_mono, V_rows_compl, V_rows_equiv, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [S, h, finModel_Pr, prF_eq_prQ, Rat.cast_inj]
    revert i j; decide +kernel
  · intro i j; rw [vr i, vr j]
  · intro i j; rw [vc i, vc j]
  · rw [vr 0, vc 0]; norm_num

/-- (a′) folio 73 §4 第 3 文の存在形: 同じ h のもとで第二段の値が等しく第三段の値が
    異なる二つの推論が、三公理と第二段の公理を満たす同じモデルにある
    (th_8dp_indifference_witness の系; a = row 0, b = col 0)。 -/
theorem th_8dp_weight_not_function_of_probability :
    ∃ (Γ : Type) (S : WeightStructure Γ), S.KeynesPr ∧ S.Mono ∧ S.Compl ∧ S.Equiv ∧
      ∃ a b h : Γ, S.Pr a h = S.Pr b h ∧ S.V a h ≠ S.V b h := by
  obtain ⟨hK, hM, hC, hE, hp, _, _, hne⟩ := th_8dp_indifference_witness
  exact ⟨Finset (Fin 3 × Fin 3), finModel V_rows, hK, hM, hC, hE,
    row 0, col 0, Finset.univ, hp 0 0, hne⟩

/-- 旧証人 V_split (row 0) (第 3 回まで) は §3 (i) に反する: 同じ三択の元 row 0 と
    row 1 で V が異なる (V_split(row 0/h) = 1, V_split(row 1/h) = 0)。
    この理由で §4 の証人を V_rows に差し替えた (差し替えの必要性の記録)。 -/
theorem th_8dp_V_split_breaks_indifference :
    V_split (row 0) (row 0) Finset.univ ≠ V_split (row 0) (row 1) Finset.univ := by
  have e1 : splits (row 0) (row 0 ∩ Finset.univ) Finset.univ := by decide +kernel
  have e2 : ¬ splits (row 0) (row 1 ∩ Finset.univ) Finset.univ := by decide +kernel
  have c1 : (Finset.univ : Finset (Fin 3 × Fin 3))ᶜ.card = 0 := by decide +kernel
  unfold V_split Vg splitInd evid
  rw [if_pos e1, if_neg e2, c1]
  norm_num

/-- (c-1) compl を落とすと連鎖が破れる: mono と equiv を満たすが compl を
    満たさず、連鎖の仮定をすべて満たして結論が破れる有限モデル。
    証人: Ω = Fin 3, h = univ, a = {0}, b = {1}, c = {2} は h のもとで対等な
    三つの選択肢 (a/h = b/h = c/h = 1/3)。S = {0} の V_half は
    V(a/h) = V(b/h) = 0, ā/(b+c)h = 1, (b+c)/āh = 1 だが V((b+c)/h) = 1。
    compl の破れ: V(a/h) = 0 ≠ V(ā/h) = 1。 -/
theorem th_8dp_chain_needs_compl :
    ∃ (Γ : Type) (S : WeightStructure Γ),
      S.KeynesPr ∧ S.Mono ∧ S.Equiv ∧ ¬ S.Compl ∧ ¬ S.Chain ∧
      ∃ a b c h : Γ, S.Pr a h = S.Pr b h ∧ S.V a h = S.V b h ∧
        S.Pr (S.not_ a) (S.and_ (S.or_ b c) h) = 1 ∧
        S.Pr (S.or_ b c) (S.and_ (S.not_ a) h) = 1 ∧
        S.V b h ≠ S.V (S.or_ b c) h := by
  have c1 : (Finset.univ : Finset (Fin 3))ᶜ.card = 0 := by decide +kernel
  have ha : ¬ half ({0} : Finset (Fin 3)) ({0} ∩ Finset.univ) Finset.univ := by decide +kernel
  have hb : ¬ half ({0} : Finset (Fin 3)) ({1} ∩ Finset.univ) Finset.univ := by decide +kernel
  have hbc : half ({0} : Finset (Fin 3)) (({1} ∪ {2}) ∩ Finset.univ) Finset.univ := by
    decide +kernel
  have hac : half ({0} : Finset (Fin 3)) ({0}ᶜ ∩ Finset.univ) Finset.univ := by decide +kernel
  have hp : prF ({0} : Finset (Fin 3)) Finset.univ = prF ({1} : Finset (Fin 3)) Finset.univ := by
    simp only [prF_eq_prQ, Rat.cast_inj]; decide +kernel
  have hind : V_half ({0} : Finset (Fin 3)) {0} Finset.univ =
      V_half ({0} : Finset (Fin 3)) {1} Finset.univ := by
    unfold V_half Vg halfInd evid
    rw [if_neg ha, if_neg hb]
  have h1 : prF ({0} : Finset (Fin 3))ᶜ (({1} ∪ {2}) ∩ Finset.univ) = 1 :=
    (prF_eq_one_iff _ _).mpr ⟨by decide +kernel, by decide +kernel⟩
  have h2 : prF (({1} : Finset (Fin 3)) ∪ {2}) ({0}ᶜ ∩ Finset.univ) = 1 :=
    (prF_eq_one_iff _ _).mpr ⟨by decide +kernel, by decide +kernel⟩
  have hV : V_half ({0} : Finset (Fin 3)) {1} Finset.univ ≠
      V_half ({0} : Finset (Fin 3)) ({1} ∪ {2}) Finset.univ := by
    unfold V_half Vg halfInd evid
    rw [if_neg hb, if_pos hbc, c1]
    norm_num
  have hnc : ¬ (finModel (Ω := Fin 3) (V_half {0})).Compl := by
    intro hc
    have h0 := hc {0} Finset.univ
    simp only [finModel_V, finModel_not] at h0
    unfold V_half Vg halfInd evid at h0
    rw [if_neg ha, if_pos hac, c1] at h0
    norm_num at h0
  refine ⟨Finset (Fin 3), finModel (V_half {0}), finModel_KeynesPr _, V_half_mono _,
    V_half_equiv _, hnc, ?_, {0}, {1}, {2}, Finset.univ, hp, hind, ?_, ?_, hV⟩
  · intro hch
    simp only [Chain, finModel_V, finModel_Pr, finModel_not, finModel_and, finModel_or] at hch
    exact hV (hch {0} {1} {2} Finset.univ hind h1 h2)
  · simpa only [finModel_Pr, finModel_not, finModel_and, finModel_or] using h1
  · simpa only [finModel_Pr, finModel_not, finModel_and, finModel_or] using h2

/-- (c-2) equiv を落とすと連鎖が破れる: mono と compl を満たすが equiv を
    満たさず、連鎖の仮定をすべて満たして結論が破れる有限モデル。
    証人: Ω = Fin 4, h = {0,1,2}, a = {0}, b = {1}, c = {2} (h のもとで
    a/h = b/h = c/h = 1/3)。|a|·|aᶜ| = |b|·|bᶜ| = 3 だが |b∪c|·|(b∪c)ᶜ| = 4。 -/
theorem th_8dp_chain_needs_equiv :
    ∃ (Γ : Type) (S : WeightStructure Γ),
      S.KeynesPr ∧ S.Mono ∧ S.Compl ∧ ¬ S.Equiv ∧ ¬ S.Chain ∧
      ∃ a b c h : Γ, S.Pr a h = S.Pr b h ∧ S.V a h = S.V b h ∧
        S.Pr (S.not_ a) (S.and_ (S.or_ b c) h) = 1 ∧
        S.Pr (S.or_ b c) (S.and_ (S.not_ a) h) = 1 ∧
        S.V b h ≠ S.V (S.or_ b c) h := by
  have hp : prF ({0} : Finset (Fin 4)) {0, 1, 2} = prF {1} {0, 1, 2} := by
    simp only [prF_eq_prQ, Rat.cast_inj]; decide +kernel
  have h1 : prF ({0} : Finset (Fin 4))ᶜ (({1} ∪ {2}) ∩ {0, 1, 2}) = 1 :=
    (prF_eq_one_iff _ _).mpr ⟨by decide +kernel, by decide +kernel⟩
  have h2 : prF (({1} : Finset (Fin 4)) ∪ {2}) ({0}ᶜ ∩ {0, 1, 2}) = 1 :=
    (prF_eq_one_iff _ _).mpr ⟨by decide +kernel, by decide +kernel⟩
  have c0 : ({0, 1, 2} : Finset (Fin 4))ᶜ.card = 1 := by decide +kernel
  have c1 : ({0} : Finset (Fin 4)).card = 1 := by decide +kernel
  have c2 : ({0} : Finset (Fin 4))ᶜ.card = 3 := by decide +kernel
  have c3 : ({1} : Finset (Fin 4)).card = 1 := by decide +kernel
  have c4 : ({1} : Finset (Fin 4))ᶜ.card = 3 := by decide +kernel
  have c5 : (({1} : Finset (Fin 4)) ∪ {2}).card = 2 := by decide +kernel
  have c6 : (({1} : Finset (Fin 4)) ∪ {2})ᶜ.card = 2 := by decide +kernel
  have hind : V₃ ({0} : Finset (Fin 4)) {0, 1, 2} = V₃ ({1} : Finset (Fin 4)) {0, 1, 2} := by
    simp only [V₃, evid, c0, c1, c2, c3, c4]
  have hV : V₃ ({1} : Finset (Fin 4)) {0, 1, 2} ≠ V₃ (({1} : Finset (Fin 4)) ∪ {2}) {0, 1, 2} := by
    simp only [V₃, evid, c0, c3, c4, c5, c6]
    norm_num
  have hne : ¬ (finModel (Ω := Fin 4) V₃).Equiv := by
    intro he
    simp only [WeightStructure.Equiv, finModel_V, finModel_Pr, finModel_and] at he
    -- a = {0}, b = {0,1}, h = {0}: a ∩ h = b ∩ h なので相互推論が成り立つが V₃ が違う
    have hp1 : prF ({0} : Finset (Fin 4)) ({0, 1} ∩ {0}) = 1 :=
      (prF_eq_one_iff _ _).mpr ⟨by decide +kernel, by decide +kernel⟩
    have hp2 : prF ({0, 1} : Finset (Fin 4)) ({0} ∩ {0}) = 1 :=
      (prF_eq_one_iff _ _).mpr ⟨by decide +kernel, by decide +kernel⟩
    have h0 := he {0} {0, 1} {0} hp1 hp2
    have d3 : ({0, 1} : Finset (Fin 4)).card = 2 := by decide +kernel
    have d4 : ({0, 1} : Finset (Fin 4))ᶜ.card = 2 := by decide +kernel
    simp only [V₃, evid, c1, c2, d3, d4] at h0
    norm_num at h0
  refine ⟨Finset (Fin 4), finModel V₃, finModel_KeynesPr _, V₃_mono, V₃_compl, hne, ?_,
    {0}, {1}, {2}, {0, 1, 2}, ?_, hind, ?_, ?_, hV⟩
  · intro hch
    simp only [Chain, finModel_V, finModel_Pr, finModel_not, finModel_and, finModel_or] at hch
    exact hV (hch {0} {1} {2} {0, 1, 2} hind h1 h2)
  · simpa only [finModel_Pr] using hp
  · simpa only [finModel_Pr, finModel_not, finModel_and, finModel_or] using h1
  · simpa only [finModel_Pr, finModel_not, finModel_and, finModel_or] using h2

/-- (c-3) mono を落としても連鎖は立つ: compl と equiv を満たし mono を満たさない
    有限モデルで連鎖が成立する (連鎖の被導出関係に mono が無いことの裏づけ)。
    証人: Ω = Fin 2, V₄ univ univ = 3 > V₄ univ (univ ∩ {0}) = 2。 -/
theorem th_8dp_chain_without_mono :
    ∃ (Γ : Type) (S : WeightStructure Γ),
      S.KeynesPr ∧ S.Compl ∧ S.Equiv ∧ ¬ S.Mono ∧ S.Chain := by
  refine ⟨Finset (Fin 2), finModel V₄, finModel_KeynesPr _, V₄_compl, V₄_equiv, ?_,
    chain_of_compl_equiv _ V₄_compl V₄_equiv⟩
  intro hm
  have h0 := hm (Finset.univ : Finset (Fin 2)) Finset.univ {0}
  simp only [finModel_V, finModel_and] at h0
  have e1 : decides (Finset.univ : Finset (Fin 2)) Finset.univ := Or.inl (subset_refl _)
  have e2 : decides (Finset.univ : Finset (Fin 2)) (Finset.univ ∩ {0}) :=
    Or.inl (Finset.subset_univ _)
  have c1 : (Finset.univ : Finset (Fin 2)).card = 2 := by decide +kernel
  have c2 : ((Finset.univ : Finset (Fin 2)) ∩ {0}).card = 1 := by decide +kernel
  simp only [V₄, dec, if_pos e1, if_pos e2, c1, c2] at h0
  norm_num at h0

/-! ### (d) 埋め込み規則 I/II の判定 -/

/-- (d-0) 表6 の各行は両列とも有限モデルで同時に満たせる。
    Ω = Fin 4, p = {0,1}, q = {0,2}, r = {0,3}, h = Ω。
    規則 I の 6 行 (a/bh = a/h) と規則 II の pq 行 (q/ph = p/h, p/qh = q/h)。
    注記: 各行が満たせる以上のことは言えない。この証人では p, q, r が
    h のもとで同じ値 1/2 をとるため、規則 I の行と規則 II の行が同じ等式になり、
    規則 I と規則 II を区別しない。両規則の一般形の区別は
    th_8dp_rule_I_finite_model / th_8dp_rule_II_scheme_zero による。 -/
theorem th_8dp_table6_rows_sat :
    let S := finModel (Ω := Fin 4) V₁
    let p : Finset (Fin 4) := {0, 1}
    let q : Finset (Fin 4) := {0, 2}
    let r : Finset (Fin 4) := {0, 3}
    let h : Finset (Fin 4) := Finset.univ
    S.KeynesPr ∧
    (S.Pr q (S.and_ p h) = S.Pr q h) ∧ (S.Pr r (S.and_ p h) = S.Pr r h) ∧
    (S.Pr p (S.and_ q h) = S.Pr p h) ∧ (S.Pr r (S.and_ q h) = S.Pr r h) ∧
    (S.Pr p (S.and_ r h) = S.Pr p h) ∧ (S.Pr q (S.and_ r h) = S.Pr q h) ∧
    (S.Pr q (S.and_ p h) = S.Pr p h) ∧ (S.Pr p (S.and_ q h) = S.Pr q h) := by
  intro S p q r h
  refine ⟨finModel_KeynesPr _, ?_⟩
  simp only [S, p, q, r, h, finModel_Pr, finModel_and, prF_eq_prQ, Rat.cast_inj]
  decide +kernel

/-- (d-I) 規則 I の一般形の有限モデル: Γ = Bool (真偽二値)、
    Pr(a/h) = 1 (a = true) / 0 (a = false)。前提 h に依存しない。 -/
def boolModel : WeightStructure Bool where
  and_ := fun a b => a && b
  or_ := fun a b => a || b
  not_ := fun a => !a
  Pr := fun a _ => if a then 1 else 0
  V := fun _ _ => 0

/-- (d-I) 規則 I の一般形は第二段の公理と無矛盾で、有限モデルをもつ:
    Γ = Bool が def_IX, def_X 両形, 値域, 規則 I を満たし、値 I をとる確率関係をもつ。
    所見: th_8dp_rule_I_finite_degenerate により有限の Γ では Π ⊆ {O, I} に
    退化し、Pr は Γ 上の真偽評価 (各 a/h に O か I を与える写像) になる。
    Γ そのものの形 (Γ = Bool かどうか) は定理で言えていない。 -/
theorem th_8dp_rule_I_finite_model :
    Finite Bool ∧ boolModel.KeynesPr ∧ boolModel.RuleI ∧ ∃ a h, boolModel.Pr a h = 1 := by
  refine ⟨inferInstance, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨true, true, by simp [boolModel]⟩⟩
  · intro p q h; cases p <;> cases q <;> simp [boolModel]
  · intro p q h; cases p <;> cases q <;> simp [boolModel]
  · intro p q h; cases p <;> cases q <;> simp [boolModel]
  · intro p h; cases p <;> simp [boolModel]
  · intro p h; cases p <;> simp [boolModel]
  · intro a b h; cases a <;> simp [boolModel]

/-- 本ファイルの公理層 (def_IX_i, def_X 両形, 値域, ax_cert_i, 重みの公理 3 本) を
    同時に満たすモデル: boolModel (Pr(a/h) = [a], V ≡ 0)。確実性 I の役は t = true。
    したがって公理層は無矛盾で、th_8dp_rule_II_i_no_certainty の False は
    公理層そのものからではなく規則 II の一般形との組合せからのみ出る。 -/
theorem th_8dp_axiom_layer_model :
    boolModel.KeynesPr ∧ boolModel.Cert ∧ boolModel.Mono ∧ boolModel.Compl ∧
      boolModel.Equiv := by
  refine ⟨th_8dp_rule_I_finite_model.2.1, ⟨true, fun _ => by simp [boolModel]⟩, ?_, ?_, ?_⟩
  · intro a h h₁; exact le_rfl
  · intro a h; rfl
  · intro a b h _ _; rfl

/-- (d-I) 規則 I の一般形の無限モデル: Π = [0,1] 上の乗法モデル
    (a∧b ↦ ab, ā ↦ 1−a, a∨b ↦ a+b−ab, Pr(a/h) = a) は def_IX, def_X 両形,
    値域, 規則 I を満たし、値 1/2 をもつ。
    (この Γ では a∧a と a の確率が異なる — Th.(12) 型の同一視を欠く。) -/
def iccModel : WeightStructure (Set.Icc (0 : ℝ) 1) where
  and_ := fun a b => ⟨a.1 * b.1,
    ⟨mul_nonneg a.2.1 b.2.1, by nlinarith [a.2.1, a.2.2, b.2.1, b.2.2]⟩⟩
  or_ := fun a b => ⟨a.1 + b.1 - a.1 * b.1,
    ⟨by nlinarith [a.2.1, a.2.2, b.2.1, b.2.2], by nlinarith [a.2.1, a.2.2, b.2.1, b.2.2]⟩⟩
  not_ := fun a => ⟨1 - a.1, ⟨by linarith [a.2.2], by linarith [a.2.1]⟩⟩
  Pr := fun a _ => a.1
  V := fun _ _ => 0

theorem th_8dp_rule_I_scheme_model :
    iccModel.KeynesPr ∧ iccModel.RuleI ∧ ∃ a h, iccModel.Pr a h = 1 / 2 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p q h; simp only [iccModel]; ring
  · intro p q h; simp only [iccModel]
  · intro p q h; simp only [iccModel]; ring
  · intro p h; exact p.2.1
  · intro p h; exact p.2.2
  · intro a b h; rfl
  · exact ⟨⟨1 / 2, by norm_num, by norm_num⟩, ⟨1, by norm_num, by norm_num⟩, rfl⟩

/-- (d-I) 規則 I の一般形の下で、有限の Γ をもつ第二段の公理のモデルは
    Π ⊆ {O, I} に退化する (構造版の系)。 -/
theorem th_8dp_rule_I_finite_degenerate {Γ : Type} [Finite Γ] (S : WeightStructure Γ)
    (hK : S.KeynesPr) (hI : S.RuleI) (p h : Γ) : S.Pr p h = 0 ∨ S.Pr p h = 1 :=
  S.ruleI_finite_degenerate hK.2.1 hK.2.2.2.1 hK.2.2.2.2 hI p h

/-- (d-II) Pr ≡ 0 のモデル: Γ = Bool (結合子は boolModel と同じ)、Pr(a/h) = 0、
    V ≡ 0。第二段の公理と規則 II の一般形を満たし、値 I をとる確率関係をもたない。 -/
def zeroModel : WeightStructure Bool where
  and_ := fun a b => a && b
  or_ := fun a b => a || b
  not_ := fun a => !a
  Pr := fun _ _ => 0
  V := fun _ _ => 0

/-- (d-II) ax_cert_i の必要性の反例: 第二段の公理 (def_IX, def_X 両形, 値域) と
    規則 II の一般形は、確実性 I を外せば同時に満たせる (zeroModel)。
    したがって th_8dp_rule_II_i_no_certainty の False は ax_cert_i なしには
    導けない。 -/
theorem th_8dp_rule_II_zero_model :
    zeroModel.KeynesPr ∧ zeroModel.RuleII ∧ ¬ ∃ p h, zeroModel.Pr p h = 1 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p q h; simp [zeroModel]
  · intro p q h; simp [zeroModel]
  · intro p q h; simp [zeroModel]
  · intro p h; simp [zeroModel]
  · intro p h; simp [zeroModel]
  · intro a b h; simp [zeroModel]
  · rintro ⟨p, h, hp⟩
    simp [zeroModel] at hp

/-- (d-II) 規則 II の一般形は第二段の公理の下で Pr ≡ 0 を強制する (構造版の系)。 -/
theorem th_8dp_rule_II_scheme_zero {Γ : Type} (S : WeightStructure Γ)
    (hK : S.KeynesPr) (hII : S.RuleII) (p h : Γ) : S.Pr p h = 0 :=
  S.ruleII_zero hK.1 hK.2.1 hII p h

/-- (d-II) 規則 II の一般形の下では、値 I をとる確率関係が一つも無い
    (確実性 I をもつ体系とは両立しない; 構造版)。 -/
theorem th_8dp_rule_II_scheme_no_certainty {Γ : Type} (S : WeightStructure Γ)
    (hK : S.KeynesPr) (hII : S.RuleII) : ¬ ∃ p h, S.Pr p h = 1 :=
  S.ruleII_no_certainty hK.1 hK.2.1 hII

end Witnesses

end KeynesWeightVIp

/-! ## 監査クエリ (Phase 8d′) -/

#check @KeynesWeightVIp.th_first_tier_injective
#check @KeynesWeightVIp.th_vi_4_chain_i
#check @KeynesWeightVIp.th_8dp_indifference_witness
#check @KeynesWeightVIp.th_8dp_weight_not_function_of_probability
#check @KeynesWeightVIp.th_8dp_axiom_layer_model
#check @KeynesWeightVIp.th_8dp_rule_II_i_no_certainty

#print axioms KeynesWeightVIp.th_first_tier_injective
#print axioms KeynesWeightVIp.th_vi_2_dichotomy_i
#print axioms KeynesWeightVIp.th_vi_4_chain_i
#print axioms KeynesWeightVIp.WeightStructure.chain_of_compl_equiv
#print axioms KeynesWeightVIp.axiomatic_KeynesPr
#print axioms KeynesWeightVIp.V₁_function_of_prF
#print axioms KeynesWeightVIp.th_8dp_nondegenerate
#print axioms KeynesWeightVIp.th_8dp_two_triads
#print axioms KeynesWeightVIp.th_8dp_indifference_witness
#print axioms KeynesWeightVIp.th_8dp_weight_not_function_of_probability
#print axioms KeynesWeightVIp.th_8dp_V_split_breaks_indifference
#print axioms KeynesWeightVIp.axiomatic_Cert
#print axioms KeynesWeightVIp.th_8dp_axiom_layer_model
#print axioms KeynesWeightVIp.th_8dp_chain_needs_compl
#print axioms KeynesWeightVIp.th_8dp_chain_needs_equiv
#print axioms KeynesWeightVIp.th_8dp_chain_without_mono
#print axioms KeynesWeightVIp.th_8dp_table6_rows_sat
#print axioms KeynesWeightVIp.th_8dp_rule_I_finite_model
#print axioms KeynesWeightVIp.th_8dp_rule_I_scheme_model
#print axioms KeynesWeightVIp.th_8dp_rule_I_finite_degenerate
#print axioms KeynesWeightVIp.th_8dp_rule_I_i_square
#print axioms KeynesWeightVIp.th_8dp_rule_I_i_degenerate
#print axioms KeynesWeightVIp.th_8dp_rule_II_zero_model
#print axioms KeynesWeightVIp.th_8dp_rule_II_scheme_zero
#print axioms KeynesWeightVIp.th_8dp_rule_II_scheme_no_certainty
#print axioms KeynesWeightVIp.th_8dp_rule_II_i
#print axioms KeynesWeightVIp.th_8dp_rule_II_i_no_certainty
