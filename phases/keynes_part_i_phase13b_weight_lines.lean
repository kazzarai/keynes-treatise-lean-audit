/- ============================================================
   PHASE 13b — 第6章「推論の重み」: 証明の中にだけあった行を定理文に昇格する
   (第 I 部, Keynes (1921) Ch. VI, folio 73–75)

   対象行 (docs/全数台帳/ch06.md): ch06-019, 020, 024, 027, 030, 045, 047, 049,
   051, 053。どれも phase8d / phase8d′ の証明の中・有限モデルの証人の中・
   分布の和の定理にはあるが、定理文には現れなかった行。ここでは 1 行 = 1 定理名で
   定理文に置く。

   出典アンカー (1921 年 Macmillan 初版の頁画像 folio_73.png, folio_74.png,
   folio_75.png で照合; 印刷で斜体の語を *…* で示す):
   - folio 73 §4 第 1 文: "It may be pointed out that if a/h = b/h, it does not
     necessarily follow that V(a/h) = V(b/h)."                     (ch06-019)
   - folio 73 §4 第 3–4 文: "But the first equality can exist in other cases
     also. If, for instance, a and b are members respectively of *different*
     sets of three equally probable exclusive and exhaustive alternatives,
     then a/h = b/h; but these arguments may have very different weights."
                                                                      (ch06-020)
   - folio 73 末: "Suppose, for instance, that we have three exclusive and
     exhaustive alternatives, a, b, and c, and that a/h = b/h in virtue of the
     Principle of Indifference, then we have V(a/h) = V(b/h) and
     V(a/h) = V(ā/h), so that V(b/h) = V(ā/h)."              (ch06-024, 027)
   - folio 74 冒頭: "It is also true, since ā/(b+c)h = 1 and (b+c)/āh = 1,
     that V(ā/h) = V((b+c)/h). Hence V(b/h) = V((b+c)/h)."      (ch06-030)
   - folio 75 §6: "We may have *data* on which the probability of x = 5 is ⅓,
     of x = 6 is ¼, of x = 7 is ⅕, of x = 8 is ⅙, and of x = 9 is 1/20."
                                                    (ch06-045, 047, 049, 051, 053)

   設計:
   - 担体は phase8d′ (keynes_part_i_phase8dp.lean) と同じ内包担体 IProp と
     推論の型 Arg。公理 (IProp の結合子、PrI と def_IX_i / def_X_left_i /
     def_X_right_i / 値域 / ax_cert_i、V : Arg → ℝ、ax_vi_mono_i /
     ax_vi_compl_i / ax_vi_equiv_i) を同名・同形で再掲する。phase8d の
     外延担体 (V : Prop → Prop → ℝ) は再掲しない (外延担体では重みが
     V a h = V True h に退化する; phase8d V_collapse)。
   - 構造 WeightStructure (KeynesPr / Mono / Compl / Equiv) と有限モデル
     (Γ = Finset Ω, Pr(a/h) = |a∩h|/|h|, V_rows) も phase8d′ と同文で再掲する
     (ch06-019 の「必ずしも従わない」を、公理を満たして等式が成り立たない
     モデルの存在で述べるため)。
   - 行ごとの読み (弱い読みにした箇所は各定理の注釈に書く):
     ch06-019: 印刷の主張は「a/h = b/h から V(a/h) = V(b/h) は従わない」。
       公理をすべて満たし、含意 ∀ a b h, a/h = b/h → V(a/h) = V(b/h) が
       成り立たないモデルがある、を定理文にする。印刷の等式は否定された
       含意の帰結としてそのまま現れる。
     ch06-020: 「等確率な排反網羅的三択」は、IProp 版では値が等しく和が 1
       (排反網羅から加法で出る帰結; 加法の公理は phase8d′ に無いので前提に
       置く) と読む。有限モデル版では排反 (Disjoint) と網羅 (h ⊆ 和) を
       そのまま前提にし、和が 1 であることを導く。どちらも結論は a/h = b/h。
     ch06-024: 前提 a/h = b/h を明示する。「in virtue of the Principle of
       Indifference … then we have V(a/h) = V(b/h)」の「無差別原理の一適用
       なら重みも等しい」(§3 (i)) は phase8d′ に公理として無いので、
       この組 (a, b) に当てた形を前提 hPI として置く。hpr は hPI を通して
       だけ使われる (前提の組は phase8d′ の hind と同じ強さ)。
     ch06-027, 030: th_vi_4_chain_i の calc の中間段をそれぞれ定理にする。
     ch06-045–053: 第 1 分布 (五つの値の確率と、排反な選択肢の確率の和が
       1 を超えないこと) から、確率 ⅓ をもつ大きさは x = 5 に限る、…、
       確率 1/20 をもつ大きさは x = 9 に限る (x : ℕ の読み)。結論に
       x = 5 … x = 9 を置くが、印刷の「x = 5」は確率の引数の命題なので、
       これは印刷の命題とは別の命題である (台帳ではこの 5 行を 未 とする)。
   ============================================================ -/

import Mathlib

noncomputable section
namespace KeynesWeightVIlines

/-! 以下 (IProp 公理群から ax_vi_equiv_i まで) は phase8d′ と同文の再掲。 -/

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

/-! ## §4 (folio 73–74) の行: 連鎖の中間段と前提 (IProp 上) -/

/-- ch06-027 (folio 73 末): "then we have V(a/h) = V(b/h) and V(a/h) = V(ā/h),
    so that V(b/h) = V(ā/h)." 前の等式は前提 hind (無差別原理による)、
    後の等式は補元対称性 ax_vi_compl_i。th_vi_4_chain_i の calc の第 1–2 段を
    合わせたもの。 -/
theorem th_vi_4_027_b_eq_compl (a b h : IProp)
    (hind : V (arg a h) = V (arg b h)) :
    V (arg b h) = V (arg (inot a) h) :=
  hind.symm.trans (ax_vi_compl_i a h)

/-- ch06-030 (folio 74 冒頭): "since ā/(b+c)h = 1 and (b+c)/āh = 1,
    that V(ā/h) = V((b+c)/h)." 相互推論則 ax_vi_equiv_i を ā と b+c に当てたもの
    (th_vi_4_chain_i の calc の第 3 段)。 -/
theorem th_vi_4_030_compl_eq_sum (a b c h : IProp)
    (h1 : PrI (inot a) (iand (ior b c) h) = 1)
    (h2 : PrI (ior b c) (iand (inot a) h) = 1) :
    V (arg (inot a) h) = V (arg (ior b c) h) :=
  ax_vi_equiv_i (inot a) (ior b c) h h1 h2

/-- ch06-024 (folio 73 末): "three exclusive and exhaustive alternatives, a, b,
    and c, and that a/h = b/h in virtue of the Principle of Indifference, then we
    have V(a/h) = V(b/h) …" 印刷の前提 a/h = b/h を hpr として明示する。
    「無差別原理の一適用から出た a/h = b/h なら重みも等しい」(§3 (i),
    folio 73: "Arguments … to which the Principle of Indifference is applicable,
    have equal evidential weights") は phase8d′ の公理に無いので、この組に
    当てた形 hPI を前提に足す (前提の追加)。結論は印刷の二つの帰結
    V(a/h) = V(b/h) と、§4 末の V(b/h) = V((b+c)/h)。
    hpr は hPI を通してだけ使われる (hpr と hPI の組は th_vi_4_chain_i の
    hind と同じ強さ)。folio 73 の「無差別原理の一回の直接適用」という限定と
    「三つの排反・網羅な選択肢」は定理文に入っていない。 -/
theorem th_vi_4_024_indiff_premise (a b c h : IProp)
    (hpr : PrI a h = PrI b h)
    (hPI : PrI a h = PrI b h → V (arg a h) = V (arg b h))
    (h1 : PrI (inot a) (iand (ior b c) h) = 1)
    (h2 : PrI (ior b c) (iand (inot a) h) = 1) :
    V (arg a h) = V (arg b h) ∧ V (arg b h) = V (arg (ior b c) h) := by
  have hind := hPI hpr
  exact ⟨hind, (th_vi_4_027_b_eq_compl a b h hind).trans (th_vi_4_030_compl_eq_sum a b c h h1 h2)⟩

/-- 三つの等確率な排反網羅的選択肢 (IProp 版の弱い読み): h のもとで三つの値が
    互いに等しく、和が 1。排反網羅から和が 1 になるのは加法の定理によるが、
    加法の公理は phase8d′ に無いので、その帰結を定義に置く。 -/
def EqTriad (h a₁ a₂ a₃ : IProp) : Prop :=
  PrI a₁ h = PrI a₂ h ∧ PrI a₂ h = PrI a₃ h ∧ PrI a₁ h + PrI a₂ h + PrI a₃ h = 1

/-- ch06-020 (folio 73 §4): "If, for instance, a and b are members respectively
    of *different* sets of three equally probable exclusive and exhaustive
    alternatives, then a/h = b/h." a は第一の三択 (a, a₂, a₃)、b は第二の三択
    (b, b₂, b₃) の元。結論は印刷の a/h = b/h (どちらも 1/3)。
    組が「別」であることは結論に使われない (同じ組でも成り立つ)。 -/
theorem th_vi_4_020_different_triads (h a a₂ a₃ b b₂ b₃ : IProp)
    (ha : EqTriad h a a₂ a₃) (hb : EqTriad h b b₂ b₃) :
    PrI a h = PrI b h := by
  obtain ⟨e1, e2, s⟩ := ha
  obtain ⟨f1, f2, t⟩ := hb
  linarith

/-! ## 構造 WeightStructure と有限モデル (phase8d′ と同文の再掲) -/

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

end WeightStructure

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

end FiniteModel

/-! ## ch06-020 の有限モデル版: 排反と網羅をそのまま前提にする -/

section Triads

variable {Ω : Type} [DecidableEq Ω]

/-- h ≠ ∅ のもとで、互いに排反で h を覆う三つの選択肢の確率の和は 1。 -/
theorem prF_triad_sum {a₁ a₂ a₃ h : Finset Ω} (hh : h ≠ ∅)
    (d12 : Disjoint a₁ a₂) (d13 : Disjoint a₁ a₃) (d23 : Disjoint a₂ a₃)
    (hcov : h ⊆ a₁ ∪ a₂ ∪ a₃) :
    prF a₁ h + prF a₂ h + prF a₃ h = 1 := by
  unfold prF
  rw [if_neg hh, if_neg hh, if_neg hh, ← add_div, ← add_div]
  have hpos : (0 : ℝ) < h.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hh)
  rw [div_eq_one_iff_eq hpos.ne']
  have hu : (a₁ ∩ h) ∪ (a₂ ∩ h) ∪ (a₃ ∩ h) = h := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ((⟨_, hx⟩ | ⟨_, hx⟩) | ⟨_, hx⟩) <;> exact hx
    · intro hx
      have := hcov hx
      simp only [Finset.mem_union] at this
      tauto
  have i12 : Disjoint (a₁ ∩ h) (a₂ ∩ h) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left d12)
  have i13 : Disjoint (a₁ ∩ h) (a₃ ∩ h) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left d13)
  have i23 : Disjoint (a₂ ∩ h) (a₃ ∩ h) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left d23)
  have c1 := Finset.card_union_of_disjoint i12
  have c2 := Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨i13, i23⟩)
  rw [hu, c1] at c2
  exact_mod_cast c2.symm

/-- ch06-020 (folio 73 §4) の有限モデル版 (一般形: 特定の Ω や組に限らない):
    a = a₁ は排反網羅的な等確率の三択 (a₁, a₂, a₃) の元、b = b₁ は別の三択
    (b₁, b₂, b₃) の元なら、a/h = b/h。排反は Disjoint、網羅は h ⊆ 三つの和、
    等確率は値の等式で、そのまま前提に置く。h ≠ ∅ は前提に置かない
    (h = ∅ では prF の約定により両辺 0)。 -/
theorem th_vi_4_020_triads_finset (h a₁ a₂ a₃ b₁ b₂ b₃ : Finset Ω)
    (da : Disjoint a₁ a₂ ∧ Disjoint a₁ a₃ ∧ Disjoint a₂ a₃) (ca : h ⊆ a₁ ∪ a₂ ∪ a₃)
    (pa : prF a₁ h = prF a₂ h ∧ prF a₂ h = prF a₃ h)
    (db : Disjoint b₁ b₂ ∧ Disjoint b₁ b₃ ∧ Disjoint b₂ b₃) (cb : h ⊆ b₁ ∪ b₂ ∪ b₃)
    (pb : prF b₁ h = prF b₂ h ∧ prF b₂ h = prF b₃ h) :
    prF a₁ h = prF b₁ h := by
  by_cases hh : h = ∅
  · simp [prF, hh]
  have sa := prF_triad_sum hh da.1 da.2.1 da.2.2 ca
  have sb := prF_triad_sum hh db.1 db.2.1 db.2.2 cb
  linarith [pa.1, pa.2, pb.1, pb.2]

end Triads

/-! ## ch06-019: 公理を満たし「a/h = b/h ならば V(a/h) = V(b/h)」が成り立たないモデル -/

section Witnesses

open WeightStructure

/-- Ω = Fin 3 × Fin 3 の行 i: 第一の三択 (行) の i 番目の選択肢。 -/
def row (i : Fin 3) : Finset (Fin 3 × Fin 3) := {i} ×ˢ Finset.univ
/-- Ω = Fin 3 × Fin 3 の列 j: 第二の三択 (列) の j 番目の選択肢。 -/
def col (j : Fin 3) : Finset (Fin 3 × Fin 3) := Finset.univ ×ˢ {j}

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


/-- ch06-019 (folio 73 §4 第 1 文): "if a/h = b/h, it does not necessarily follow
    that V(a/h) = V(b/h)." 第二段の公理 (KeynesPr) と重みの三公理
    (Mono, Compl, Equiv) をすべて満たし、含意
    ∀ a b h, a/h = b/h → V(a/h) = V(b/h) が成り立たないモデルがある。
    印刷の等式 V(a/h) = V(b/h) は、否定された含意の帰結としてそのまま現れる
    (印刷の主張そのものが「従わない」= 否定なので、この形を印刷の読みとする)。
    証人は phase8d′ と同じ V_rows (Ω = Fin 3 × Fin 3, a = row 0, b = col 0,
    h = univ; a/h = b/h = 1/3, V(a/h) = 1, V(b/h) = 0)。 -/
theorem th_vi_4_019_not_necessarily :
    ∃ (Γ : Type) (S : WeightStructure Γ), S.KeynesPr ∧ S.Mono ∧ S.Compl ∧ S.Equiv ∧
      ¬ (∀ a b h : Γ, S.Pr a h = S.Pr b h → S.V a h = S.V b h) := by
  refine ⟨Finset (Fin 3 × Fin 3), finModel V_rows, finModel_KeynesPr _, V_rows_mono,
    V_rows_compl, V_rows_equiv, ?_⟩
  intro hall
  have hp : prF (row 0) Finset.univ = prF (col 0) Finset.univ := by
    simp only [prF_eq_prQ, Rat.cast_inj]
    decide +kernel
  have hv := hall (row 0) (col 0) Finset.univ hp
  have hr : rowSum (row 0 ∩ Finset.univ) Finset.univ := by decide +kernel
  have hc : ¬ rowSum (col 0 ∩ Finset.univ) Finset.univ := by decide +kernel
  have c1 : (Finset.univ : Finset (Fin 3 × Fin 3))ᶜ.card = 0 := by decide +kernel
  change Vg rowSumInd (row 0) Finset.univ = Vg rowSumInd (col 0) Finset.univ at hv
  unfold Vg rowSumInd evid at hv
  rw [if_pos hr, if_neg hc, c1] at hv
  norm_num at hv

end Witnesses

/-! ## §6 (folio 75) の第 1 分布: x = 5, …, 9 -/

/-- folio 75 §6: "We may have *data* on which the probability of x = 5 is ⅓,
    of x = 6 is ¼, of x = 7 is ⅕, of x = 8 is ⅙, and of x = 9 is 1/20."
    p n は data のもとで「x = n」である確率。x の大きさどうしは排反な選択肢
    (folio 75: "a summation of a number of alternative and exclusive
    probabilities") なので、有限個の大きさの確率の和は 1 を超えない (total)。 -/
structure Dist1 (p : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ p n
  total : ∀ s : Finset ℕ, ∑ n ∈ s, p n ≤ 1
  v5 : p 5 = 1 / 3
  v6 : p 6 = 1 / 4
  v7 : p 7 = 1 / 5
  v8 : p 8 = 1 / 6
  v9 : p 9 = 1 / 20

/-- 五つの値の和は 1 なので、ほかの大きさの確率は 0。 -/
theorem Dist1.zero_off {p : ℕ → ℝ} (hp : Dist1 p) {x : ℕ}
    (hx : x ∉ ({5, 6, 7, 8, 9} : Finset ℕ)) : p x = 0 := by
  have h := hp.total (insert x {5, 6, 7, 8, 9})
  rw [Finset.sum_insert hx] at h
  have hs : ∑ n ∈ ({5, 6, 7, 8, 9} : Finset ℕ), p n = 1 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      hp.v5, hp.v6, hp.v7, hp.v8, hp.v9]
    norm_num
  have := hp.nonneg x
  linarith

/-- 第 1 分布の場合分け: x は 5, 6, 7, 8, 9 のどれかで印刷の値をとるか、確率 0。 -/
theorem Dist1.cases {p : ℕ → ℝ} (hp : Dist1 p) (x : ℕ) :
    (x = 5 ∧ p x = 1 / 3) ∨ (x = 6 ∧ p x = 1 / 4) ∨ (x = 7 ∧ p x = 1 / 5) ∨
    (x = 8 ∧ p x = 1 / 6) ∨ (x = 9 ∧ p x = 1 / 20) ∨ p x = 0 := by
  by_cases hm : x ∈ ({5, 6, 7, 8, 9} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, hp.v5⟩
    · exact Or.inr (Or.inl ⟨rfl, hp.v6⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hp.v7⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hp.v8⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hp.v9⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hp.zero_off hm)))))

/-- ch06-045 (folio 75): 第 1 分布で確率 ⅓ をもつ大きさは x = 5 に限る。 -/
theorem th_vi_6_045_x_eq_5 {p : ℕ → ℝ} (hp : Dist1 p) (x : ℕ) (hx : p x = 1 / 3) :
    x = 5 := by
  rcases hp.cases x with ⟨rfl, _⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | e <;>
    first | rfl | (rw [e] at hx; norm_num at hx)

/-- ch06-047 (folio 75): 第 1 分布で確率 ¼ をもつ大きさは x = 6 に限る。 -/
theorem th_vi_6_047_x_eq_6 {p : ℕ → ℝ} (hp : Dist1 p) (x : ℕ) (hx : p x = 1 / 4) :
    x = 6 := by
  rcases hp.cases x with ⟨rfl, e⟩ | ⟨rfl, _⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | e <;>
    first | rfl | (rw [e] at hx; norm_num at hx)

/-- ch06-049 (folio 75): 第 1 分布で確率 ⅕ をもつ大きさは x = 7 に限る。 -/
theorem th_vi_6_049_x_eq_7 {p : ℕ → ℝ} (hp : Dist1 p) (x : ℕ) (hx : p x = 1 / 5) :
    x = 7 := by
  rcases hp.cases x with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, _⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | e <;>
    first | rfl | (rw [e] at hx; norm_num at hx)

/-- ch06-051 (folio 75): 第 1 分布で確率 ⅙ をもつ大きさは x = 8 に限る。 -/
theorem th_vi_6_051_x_eq_8 {p : ℕ → ℝ} (hp : Dist1 p) (x : ℕ) (hx : p x = 1 / 6) :
    x = 8 := by
  rcases hp.cases x with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, _⟩ | ⟨rfl, e⟩ | e <;>
    first | rfl | (rw [e] at hx; norm_num at hx)

/-- ch06-053 (folio 75): 第 1 分布で確率 1/20 をもつ大きさは x = 9 に限る。 -/
theorem th_vi_6_053_x_eq_9 {p : ℕ → ℝ} (hp : Dist1 p) (x : ℕ) (hx : p x = 1 / 20) :
    x = 9 := by
  rcases hp.cases x with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, _⟩ | e <;>
    first | rfl | (rw [e] at hx; norm_num at hx)

/-- 第 1 分布をもつ p が実際にある (Dist1 の前提が空でないこと)。 -/
theorem th_vi_6_dist1_exists : ∃ p : ℕ → ℝ, Dist1 p := by
  let p : ℕ → ℝ := fun n =>
    if n = 5 then 1 / 3 else if n = 6 then 1 / 4 else if n = 7 then 1 / 5 else
    if n = 8 then 1 / 6 else if n = 9 then 1 / 20 else 0
  have hoff : ∀ n, n ∉ ({5, 6, 7, 8, 9} : Finset ℕ) → p n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [p, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2]
  have hnn : ∀ n, 0 ≤ p n := by
    intro n; simp only [p]; split_ifs <;> norm_num
  refine ⟨p, hnn, ?_, by simp [p], by simp [p], by simp [p], by simp [p], by simp [p]⟩
  intro s
  have hsub : ∑ n ∈ s, p n ≤ ∑ n ∈ s ∪ {5, 6, 7, 8, 9}, p n :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun n _ _ => hnn n)
  have hsplit : ∑ n ∈ s ∪ {5, 6, 7, 8, 9}, p n = ∑ n ∈ ({5, 6, 7, 8, 9} : Finset ℕ), p n := by
    refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro n _ hn
    exact hoff n hn
  have hval : ∑ n ∈ ({5, 6, 7, 8, 9} : Finset ℕ), p n = 1 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [p]; norm_num
  linarith

end KeynesWeightVIlines

/- ---------- 監査 (Phase 13b) ---------- -/

#print axioms KeynesWeightVIlines.th_vi_4_019_not_necessarily
#print axioms KeynesWeightVIlines.th_vi_4_020_different_triads
#print axioms KeynesWeightVIlines.th_vi_4_020_triads_finset
#print axioms KeynesWeightVIlines.th_vi_4_024_indiff_premise
#print axioms KeynesWeightVIlines.th_vi_4_027_b_eq_compl
#print axioms KeynesWeightVIlines.th_vi_4_030_compl_eq_sum
#print axioms KeynesWeightVIlines.th_vi_6_045_x_eq_5
#print axioms KeynesWeightVIlines.th_vi_6_047_x_eq_6
#print axioms KeynesWeightVIlines.th_vi_6_049_x_eq_7
#print axioms KeynesWeightVIlines.th_vi_6_051_x_eq_8
#print axioms KeynesWeightVIlines.th_vi_6_053_x_eq_9
#print axioms KeynesWeightVIlines.th_vi_6_dist1_exists
