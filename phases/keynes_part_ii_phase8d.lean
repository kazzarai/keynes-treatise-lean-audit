/- ============================================================
   PHASE 8d — 第6章「推論の重み」の文言アンカー層
   (第I部への監査拡張の第一号)

   出典: Keynes (1921) Ch. VI, 英tex l.4251-4597, Folio 71-79
   - §1 核文: "New evidence will sometimes decrease the probability
     of an argument, but it will always increase its 'weight.'"
   - §2: 「関連」と「重み増」の相関性 (定義的同値)。厳密な無関連なら不変
   - §3: V記法。(ii) V(a/hh₁) > V(a/h) (無関連なら等号)。
     (iii)型の規則 V(ab/h) < V(a/h) はケインズ自身が却下 —
     「証明からは遠いが反証には近い」(ab/h=0 ∧ a/h>0 の場合の逆転)。
     補元対称性 V(a/h) = V(ā/h)
   - §4: 相互推論則 (a/bh=1 ∧ b/ah=1 ⟹ V等号) と、三択例での
     ケインズ自身の導出連鎖 V(b/h) = V((b+c)/h)
   - §6: 確率誤差との分離の数値例 + 壺のペア (Ellsberg 1961 の祖型)
   - §8: 「重みは和を測り、確率は差を測る」

   公理化せず記録のみとした項目:
   - §3の(iii)却下は形式原理が明文化されておらず、補間なしには
     公理化できない (ケインズは「確実性に達した議論の重み優位」を
     暗黙に使うが、その原理を述べていない)
   - §5: De Morgan流「確率の確率」による重みの説明をケインズが拒否
   - §10: Nitsche の「信頼性 (Sicherheit)」読みも同型の誤りとして拒否

   T21 (8c橋): §1テーゼの成立域の切り分け —
   Brady模型 V=K/(K+I) で「証拠の増加 = Kのみ増加」と読めば
   テーゼは厳密に成立し (subjective_time_mono と同内容)、
   「K と I がともに増加」する間主観的読みでは反例が存在する。
   ============================================================ -/

import Mathlib

noncomputable section
namespace KeynesWeightVI

/-- 確率関係 (監査本体と同じ形の原始関係)。 -/
axiom Pr : Prop → Prop → ℝ

/-- 証拠 h のもとでの議論 a の「証拠的重み」 V(a/h)。§3 の記法。 -/
axiom V : Prop → Prop → ℝ

/- ---------- §1/§2/§3: 公理層 (source-exact) ---------- -/

/-- §1核文の弱形: 証拠の追加は重みを決して減らさない。
    "it will always increase its 'weight'" — 増加は§2により
    「関連な部分がある場合」に限り厳密。 -/
axiom ax_vi_mono (a h h₁ : Prop) : V a h ≤ V a (h₁ ∧ h)

/-- §2の相関性定義: 「新しい証拠が『関連』だと言うことは、それが
    議論の『重み』を増すと言うことと同じである」。 -/
def Rel (h₁ a h : Prop) : Prop := V a h < V a (h₁ ∧ h)

/-- §3: 補元対称性 V(a/h) = V(ā/h)。
    「議論は、命題を証明ないし反証することに近いのとちょうど同じだけ、
    その矛盾命題を反証ないし証明することに近い」。 -/
axiom ax_vi_compl (a h : Prop) : V a h = V (¬a) h

/-- §4: 相互推論則 — h に相対して互いに推論し合える二命題の重みは等しい。
    「一方を証明ないし反証するとき、我々は必然的に他方を証明ないし
    反証しているのである」。 -/
axiom ax_vi_equiv (a b h : Prop) :
    Pr a (b ∧ h) = 1 → Pr b (a ∧ h) = 1 → V a h = V b h

/- ---------- §2の二分律 (公理からの帰結) ---------- -/

/-- 任意の証拠追加は「関連 (真に増加)」か「重み不変」のどちらか。 -/
theorem th_vi_2_dichotomy (a h h₁ : Prop) :
    Rel h₁ a h ∨ V a (h₁ ∧ h) = V a h := by
  rcases lt_or_eq_of_le (ax_vi_mono a h h₁) with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'.symm

/- ---------- §4: ケインズ自身の導出連鎖の監査 ---------- -/

/-- §4末尾の連鎖 (Folio 73-74)。三つの排反網羅的選択肢 a, b, c について、
    無差別原理による V(a/h) = V(b/h) と、ā と b∨c の相互推論
    (ā/(b+c)h = 1, (b+c)/āh = 1) から、V(b/h) = V((b+c)/h)。
    ケインズが本文で行った導出そのものを、彼の公理から再現する。 -/
theorem th_vi_4_chain (a b c h : Prop)
    (hind : V a h = V b h)
    (h1 : Pr (¬a) ((b ∨ c) ∧ h) = 1)
    (h2 : Pr (b ∨ c) ((¬a) ∧ h) = 1) :
    V b h = V (b ∨ c) h := by
  calc V b h = V a h := hind.symm
    _ = V (¬a) h := ax_vi_compl a h
    _ = V (b ∨ c) h := ax_vi_equiv (¬a) (b ∨ c) h h1 h2

/- ---------- §6数値例①: 重みと確率誤差の分離 (公理フリー) ---------- -/

/- 元の分布: x = 5,6,7,8,9 に確率 1/3, 1/4, 1/5, 1/6, 1/20。
   追加証拠後: x = 5,8,9 に確率 7/16, 5/16, 4/16。
   最確値はどちらも 5。確率誤差 (最確値からの偏差が「超えるのと
   超えないのが同程度」となる量) は 1 から 3 へ増加する —
   重みは増しながら、誤差は増える。 -/

/-- 元の分布は正規化されている (ケインズの数の検算)。 -/
theorem th_vi_6_dist1_sums :
    (1 : ℚ)/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1 := by norm_num

/-- 追加証拠後の分布も正規化されている。 -/
theorem th_vi_6_dist2_sums : (7 : ℚ)/16 + 5/16 + 4/16 = 1 := by norm_num

/-- 元の分布: 偏差1以内 (x=5,6) の確率 1/3+1/4 = 7/12 は 1/2 以上
    — 確率誤差は 1 以下。 -/
theorem th_vi_6_pe1_le_one : (1 : ℚ)/2 ≤ 1/3 + 1/4 := by norm_num

/-- 新分布: 偏差2以内は x=5 のみで確率 7/16 は 1/2 未満
    — 確率誤差は 3 以上 (次の値 x=8 は偏差3)。 -/
theorem th_vi_6_pe2_ge_three : (7 : ℚ)/16 < 1/2 := by norm_num

/- ---------- §6数値例②: 壺のペア (Ellsberg 1961 の祖型) ---------- -/

/-- 構成不明の二球壺: 構成 {WW, WB, BW, BB} が等確率なら
    白を引く確率は (1 + 1/2 + 1/2 + 0)/4 = 1/2 —
    構成既知 (50:50) の壺と同じ確率、しかし重みは異なる (§6)。 -/
theorem th_vi_6_urn_unknown_half :
    ((1 : ℚ) + 1/2 + 1/2 + 0) / 4 = 1/2 := by norm_num

/- ---------- T21: Brady模型での§1テーゼの成立域 (8c橋) ---------- -/

/-- Brady の重み (8c と同じ)。ローカル再掲 (ファイル自己完結のため)。 -/
def VB (K I : ℝ) : ℝ := K / (K + I)

/-- §1テーゼの成立側: 「証拠の増加 = 知識 K のみの増加」と読めば、
    Brady模型は ax_vi_mono を厳密に満たす (8c subjective_time_mono と同内容)。 -/
theorem th_vi_1_brady_holds {K K' I : ℝ} (hK : 0 < K) (hI : 0 ≤ I)
    (hKK : K ≤ K') : VB K I ≤ VB K' I := by
  have h1 : 0 < K + I := by linarith
  have h2 : 0 < K' + I := by linarith
  rw [VB, VB, div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul_of_nonneg_right hKK hI]

/-- §1テーゼの限界側: 「証拠の増加」に無知 I の増加が含まれる読み
    (2012年の間主観的時間) では、テーゼは破れる (8c 反例と同一証人)。 -/
theorem th_vi_1_brady_exits :
    ∃ K I K' I' : ℝ, 0 < K ∧ 0 < I ∧ K < K' ∧ I < I' ∧
      VB K' I' < VB K I := by
  refine ⟨1, 1, 2, 6, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [VB]

/- ---------- 監査 (Phase 8d) ---------- -/

#check @th_vi_4_chain
#check @th_vi_1_brady_holds

#print axioms KeynesWeightVI.th_vi_2_dichotomy
#print axioms KeynesWeightVI.th_vi_4_chain
#print axioms KeynesWeightVI.th_vi_6_dist1_sums
#print axioms KeynesWeightVI.th_vi_6_dist2_sums
#print axioms KeynesWeightVI.th_vi_6_pe1_le_one
#print axioms KeynesWeightVI.th_vi_6_pe2_ge_three
#print axioms KeynesWeightVI.th_vi_6_urn_unknown_half
#print axioms KeynesWeightVI.th_vi_1_brady_holds
#print axioms KeynesWeightVI.th_vi_1_brady_exits

end KeynesWeightVI
