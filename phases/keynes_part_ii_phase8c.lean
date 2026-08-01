/- ============================================================
   PHASE 8c — 重みの公理層 V = K/(K+I) (三部作の最終章)

   出典アンカー:
   - Brady (2004) 経由の重みの定式化 w = K/(K+I)
     (K = 関連知識の絶対量、I = 関連無知の絶対量)
     — 高籔・新井 (2012) 紀要63 が採用。Keynes (1921) 第6章の
     「有利・不利のバランスではなく、知識と無知の絶対量のバランス」
     (佐藤訳 p.82) の比率化
   - 紀要 式(1.1): lim_{I→∞} V = 0
   - 2012年の独自導入「時間概念」:
     * 主観的時間 = K のみ増加 → 重み単調増加 (Keynes/O'Donnell の
       単調増加テーゼに対応)
     * 間主観的時間 = K と I がともに増加 → 重みは減少しうる
       (単調増加テーゼへの反例可能性、2012年の理論的主張)

   本ファイルの決着 (WEIGHT_DESIGN §3 T14-T16):
   - T14 : V は K について単調増加 (主観的時間 = ケインズ的単調性)
           + I について単調減少 (無知の増加は重みを下げる)
   - T15 : Brady 極限 — I→∞ で V→0 (式(1.1) の機械化)
   - T16 : ★間主観的時間の反例★ — K も I も増加して V が減少する
           具体例 (1,1)→(2,6): 1/2 → 1/4。2012年の主張の定理化
   - 併せて 0 ≤ V ≤ 1 (8a の重み w の値域仮定 0≤w≤1 の裏づけ)

   注: この V は 8a の係数 c(p,w) の w に入る量。8a・8b・8c で
   三部作 (係数c / 加重関数W / 重みV) が閉じる。
   ============================================================ -/

import Mathlib

noncomputable section
namespace KeynesWeightV

open Filter Topology

/-- Brady の重み V(K,I) = K/(K+I)。K = 知識の絶対量、I = 無知の絶対量。 -/
def V (K I : ℝ) : ℝ := K / (K + I)

/- ---------- 値域 (8a の 0 ≤ w ≤ 1 の裏づけ) ---------- -/

theorem V_nonneg {K I : ℝ} (hK : 0 ≤ K) (hI : 0 ≤ I) : 0 ≤ V K I :=
  div_nonneg hK (by linarith)

theorem V_le_one {K I : ℝ} (hK : 0 ≤ K) (hI : 0 ≤ I) : V K I ≤ 1 := by
  have h0 : (0 : ℝ) ≤ K + I := by linarith
  rcases h0.eq_or_lt with h | h
  · rw [V, ← h, div_zero]
    norm_num
  · rw [V, div_le_one h]
    linarith

/-- 知識ゼロなら重みゼロ。 -/
theorem V_zero_knowledge (I : ℝ) : V 0 I = 0 := by
  simp [V]

/-- 無知ゼロ・知識正なら重みは最大値 1 (確実性)。 -/
theorem V_full_knowledge {K : ℝ} (hK : 0 < K) : V K 0 = 1 := by
  rw [V, add_zero, div_self hK.ne']

/- ---------- T14: 主観的時間 — K の単調増加は重みを上げる ---------- -/

/-- ★ T14 (主観的時間): I を固定して K が増えれば V は増加。
    Keynes/O'Donnell の「証拠の増加は重みを常に増す」テーゼの、
    「増えるのが知識だけの場合」としての成立形。 -/
theorem subjective_time_mono {K K' I : ℝ} (hK : 0 < K) (hI : 0 ≤ I)
    (hKK : K ≤ K') : V K I ≤ V K' I := by
  have h1 : 0 < K + I := by linarith
  have h2 : 0 < K' + I := by linarith
  rw [V, V, div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul_of_nonneg_right hKK hI]

/-- T14補: K を固定して I (無知) が増えれば V は減少。 -/
theorem ignorance_decreases_weight {K I I' : ℝ} (hK : 0 < K) (hI : 0 ≤ I)
    (hII : I ≤ I') : V K I' ≤ V K I := by
  have h1 : 0 < K + I := by linarith
  have h2 : 0 < K + I' := by linarith
  rw [V, V, div_le_div_iff₀ h2 h1]
  nlinarith [mul_le_mul_of_nonneg_left hII hK.le]

/- ---------- T15: Brady 極限 (紀要 式(1.1)) ---------- -/

/-- ★ T15: 無知が無限に増大すれば重みは 0 に収束する。
    lim_{I→∞} K/(K+I) = 0。仮定不要 (K は任意の実数でよい)。 -/
theorem brady_limit (K : ℝ) :
    Tendsto (fun I : ℝ => V K I) atTop (𝓝 0) := by
  have h1 : Tendsto (fun I : ℝ => K + I) atTop atTop :=
    tendsto_atTop_add_const_left atTop K tendsto_id
  have h2 : Tendsto (fun I : ℝ => (K + I)⁻¹) atTop (𝓝 0) :=
    h1.inv_tendsto_atTop
  have h3 : Tendsto (fun I : ℝ => K * (K + I)⁻¹) atTop (𝓝 (K * 0)) :=
    h2.const_mul K
  simpa [V, div_eq_mul_inv] using h3

/- ---------- T16: 間主観的時間の反例 (2012年の主張の定理化) ---------- -/

/-- ★ T16 (間主観的時間): 知識 K と無知 I が「ともに」増加すると、
    重みは減少しうる。具体例: (K,I) = (1,1) → (2,6) で V は 1/2 → 1/4。
    「証拠の増加は重みを常に増す」という単調増加テーゼは、
    増えるものに無知が含まれる場合には成立しない —
    高籔・新井 (2012) が理論的に主張した反例可能性の機械実現。 -/
theorem intersubjective_time_counterexample :
    ∃ K I K' I' : ℝ, 0 < K ∧ 0 < I ∧ K < K' ∧ I < I' ∧
      V K' I' < V K I := by
  refine ⟨1, 1, 2, 6, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [V]

/-- T16補 (一般形): K が α 倍、I が β 倍に増え α < β なら重みは真に減少。
    間主観的時間の「無知の膨張が知識の獲得を上回る」場合の一般法則。 -/
theorem intersubjective_general {K I a b : ℝ} (hK : 0 < K) (hI : 0 < I)
    (ha : 1 ≤ a) (hab : a < b) : V (a * K) (b * I) < V K I := by
  have hb : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have h1 : 0 < a * K + b * I := by positivity
  have h2 : 0 < K + I := by linarith
  rw [V, V, div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos hK hI, mul_pos ha0 (mul_pos hK hI)]

/- ---------- 監査 (Phase 8c) ---------- -/

#check @V_nonneg
#check @brady_limit
#check @intersubjective_time_counterexample

#print axioms KeynesWeightV.V_nonneg
#print axioms KeynesWeightV.V_le_one
#print axioms KeynesWeightV.V_zero_knowledge
#print axioms KeynesWeightV.V_full_knowledge
#print axioms KeynesWeightV.subjective_time_mono
#print axioms KeynesWeightV.ignorance_decreases_weight
#print axioms KeynesWeightV.brady_limit
#print axioms KeynesWeightV.intersubjective_time_counterexample
#print axioms KeynesWeightV.intersubjective_general

end KeynesWeightV
