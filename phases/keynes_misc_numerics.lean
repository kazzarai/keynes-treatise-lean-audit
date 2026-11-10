/-
# Keynes (1921) *A Treatise on Probability* — 数値例の検算 (B50)

## 目的
  台帳 (docs/全数台帳) で「数値を伴う式」「数値例」とされ、Lean に対応がなかった式行のうち、
  `norm_num` / `decide` で算術として検算できるものを定理にする。判定は ch21-005 が ✓ (印刷の算術等式が
  そのまま定理)、ch21-002・004 が「≈ (数値評価: 定理名)」、ch04-090・091 が 定 (例の仮定):
  印刷の数値関係を、数え上げ・素数判定・等式として機械的に評価した形で述べる。
  Keynes の公理 (確率関係の公理) には依らない。第 29 章の数値例は本ファイルの対象外 (別依頼)。

## 本ファイルの判定対象 (台帳の行 → 定理)
  ch04-090  x = ½ ,  ch04-091  y = ¼     th_4_17_example_premises (定: 例の仮定 x = ½, y = ¼ を前提 hx, hy として運ぶ)
                                        備考: th_4_17_four_balls (folio 57 §17: 4 個の球のうち黒が ½ になる場合は
                                              6 通り (A, B / A, C / … / C, D)、¼ になる場合は 4 通り)
  ch21-002  a = 1, 2, 3, and 4          th_21_fermat_primes  (2^(2^a) + 1 は a = 1, 2, 3, 4 で素数)
  ch21-004  a = 4                       th_21_fermat_a4      (a = 4 の値 65537 まで素数)
  ch21-005  2^(2^5) + 1 = 4294967297 = 641 × 6700417    th_21_euler_641  (脚注 1; 印刷の算術等式がそのまま定理 ✓;
                                                        合成数であること、因数も素数は付加)

## 検算できず 未 のままにした行 (理由は台帳の備考)
  ch25-008〜010 (Playfair の比重 3·48 = √12, 2·29 = ∛12, 1·88 = ⁴√12): 印刷は "approximately" で許容誤差が
    印刷にない (folio 305 の 3·48 等は実測の比重で、√12 等に「approximately」等しいと言っているだけ)。
    参考として th_25_playfair_roots_within (差が 1/50 未満) と th_25_playfair_gap_sizes (差の大きさ) を
    置くが、行の判定には使わない。
  ch04-007/008 (a/h = ½, ab/h = ½)、ch06-032/033 (x/h₁h₂ = ⅔, x/h₁ = ¾)、ch16-082〜084:
    確率の値が無差別原理や例の仮定として与えられており、算術の検算で出せる関係ではない。
  ch06-045〜053 (x = 5〜9): 台帳では未。phase8d/th_vi_6_dist1_sums は分布の和 1 のみを述べ、phase13b に
    別命題の定理 (確率 ⅓ などをもつ大きさは 5 などに限る; th_vi_6_045_x_eq_5 等) があるが、印刷の命題
    (「x = 5」の確率が ⅓) ではないので判定は付けていない (本ファイルは触らない)。

## 予測: 本ファイルの全定理は Lean の標準の三公理 (propext, Classical.choice, Quot.sound) のみに依存する。
-/

import Mathlib

namespace KeynesNumerics

open Finset

/-! ## ch04 folio 57 §17 — 4 個の球 (x = ½, y = ¼) -/

/-- 4 個の球 A, B, C, D (Fin 4) のうち、黒の個数が 2 (比 x = 2/4 = ½) の組は 6 通り、
黒の個数が 1 (比 y = 1/4 = ¼) の組は 4 通り。印刷: 「黒が半分なら A, B / A, C / A, D / B, C / B, D / C, D、
四分の一なら A または B または C または D が黒」。 -/
theorem th_4_17_four_balls :
    ((univ : Finset (Fin 4)).powersetCard 2).card = 6 ∧
    ((univ : Finset (Fin 4)).powersetCard 1).card = 4 ∧
    (∀ s ∈ (univ : Finset (Fin 4)).powersetCard 2, ((s.card : ℚ) / 4) = 1 / 2) ∧
    (∀ s ∈ (univ : Finset (Fin 4)).powersetCard 1, ((s.card : ℚ) / 4) = 1 / 4) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [hs.2]; norm_num
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [hs.2]; norm_num

/-- **ch04-090・091 (定: 例の仮定)**: 「If x = ½ and y = ¼」の x, y を名前付きの前提 hx, hy として運ぶ。
その下で、4 個の球 (Fin 4) のうち黒が x の割合の組 (2 個) と y の割合の組 (1 個) が存在し、x ≠ y
(φ(x) と φ(y) は別の選択肢)。比の値そのものは例の仮定であって、算術から出る関係ではない。 -/
theorem th_4_17_example_premises {x y : ℚ} (hx : x = 1 / 2) (hy : y = 1 / 4) :
    (∃ s ∈ (univ : Finset (Fin 4)).powersetCard 2, (s.card : ℚ) / 4 = x) ∧
    (∃ s ∈ (univ : Finset (Fin 4)).powersetCard 1, (s.card : ℚ) / 4 = y) ∧ x ≠ y := by
  subst hx; subst hy
  refine ⟨?_, ?_, by norm_num⟩
  · obtain ⟨s, hs⟩ := Finset.powersetCard_nonempty.mpr (show 2 ≤ (univ : Finset (Fin 4)).card by simp)
    refine ⟨s, hs, ?_⟩
    rw [(Finset.mem_powersetCard.mp hs).2]; norm_num
  · obtain ⟨s, hs⟩ := Finset.powersetCard_nonempty.mpr (show 1 ≤ (univ : Finset (Fin 4)).card by simp)
    refine ⟨s, hs, ?_⟩
    rw [(Finset.mem_powersetCard.mp hs).2]; norm_num

/-- th_4_17_example_premises から hx : x = ½ を落とすと崩れる: x = 1 では黒が x の割合の 2 個組は存在しない。 -/
theorem th_4_17_example_needs_hx :
    ¬ (∃ s ∈ (univ : Finset (Fin 4)).powersetCard 2, (s.card : ℚ) / 4 = 1) := by
  rintro ⟨s, hs, h⟩
  rw [(Finset.mem_powersetCard.mp hs).2] at h
  norm_num at h

/-- th_4_17_example_premises から hy : y = ¼ を落とすと崩れる: y = ½ では黒が y の割合の 1 個組は存在しない
(1 個組の割合は ¼ だけ)。 -/
theorem th_4_17_example_needs_hy :
    ¬ (∃ s ∈ (univ : Finset (Fin 4)).powersetCard 1, (s.card : ℚ) / 4 = 1 / 2) := by
  rintro ⟨s, hs, h⟩
  rw [(Finset.mem_powersetCard.mp hs).2] at h
  norm_num at h

/-! ## ch21 folio 242 — Fermat の式 2^(2^a) + 1 -/

/-- a = 1, 2, 3, 4 で 2^(2^a) + 1 (= 5, 17, 257, 65537) は素数。 -/
theorem th_21_fermat_primes : ∀ a ∈ ({1, 2, 3, 4} : Finset ℕ), Nat.Prime (2 ^ (2 ^ a) + 1) := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num

/-- a = 4 の値は 65537 で素数 (「a = 4 まで素数を与える」)。 -/
theorem th_21_fermat_a4 : 2 ^ (2 ^ 4) + 1 = 65537 ∧ Nat.Prime 65537 := by
  constructor <;> norm_num

/-- 脚注 1: 2^(2^5) + 1 = 4,294,967,297 = 641 × 6,700,417。したがって a = 5 の値は合成数 (因数 641, 6700417 は素数)。 -/
theorem th_21_euler_641 :
    2 ^ (2 ^ 5) + 1 = 4294967297 ∧ 4294967297 = 641 * 6700417 ∧
    Nat.Prime 641 ∧ Nat.Prime 6700417 ∧ ¬ Nat.Prime (2 ^ (2 ^ 5) + 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h : 2 ^ (2 ^ 5) + 1 = 641 * 6700417 := by norm_num
  rw [h]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-! ## ch25 folio 305 — Playfair の比重 (参考; 行の判定には使わない) -/

/-- 冪の比較による根の評価 (補助): r > 0, r^n = 12, lo^n < 12 < hi^n ⟹ lo < r < hi。 -/
theorem root_between (n : ℕ) {r lo hi : ℝ} (hr : 0 < r) (_hlo : 0 < lo) (hhi : 0 < hi)
    (h : r ^ n = 12) (h1 : lo ^ n < 12) (h2 : 12 < hi ^ n) : lo < r ∧ r < hi := by
  constructor
  · by_contra hc
    have := pow_le_pow_left₀ hr.le (not_lt.mp hc) n
    linarith
  · by_contra hc
    have := pow_le_pow_left₀ hhi.le (not_lt.mp hc) n
    linarith

theorem rpow_root_pow (n : ℕ) (hn : 0 < n) : ((12 : ℝ) ^ ((1 : ℝ) / n)) ^ n = 12 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : (1 : ℝ) / n * n = 1 := by field_simp
  rw [this, Real.rpow_one]

/-- 印刷の 3·48, 2·29, 1·88 は √12, ∛12, ⁴√12 に 1/50 未満の差で近い (許容誤差 1/50 は本ファイルの置き方)。 -/
theorem th_25_playfair_roots_within :
    |(3.48 : ℝ) - Real.sqrt 12| < 1 / 50 ∧
    |(2.29 : ℝ) - (12 : ℝ) ^ ((1 : ℝ) / 3)| < 1 / 50 ∧
    |(1.88 : ℝ) - (12 : ℝ) ^ ((1 : ℝ) / 4)| < 1 / 50 := by
  have s2 := root_between 2 (r := Real.sqrt 12) (lo := 3.46) (hi := 3.50)
    (Real.sqrt_pos.mpr (by norm_num)) (by norm_num) (by norm_num)
    (by rw [Real.sq_sqrt (by norm_num)]) (by norm_num) (by norm_num)
  have s3 := root_between 3 (r := (12 : ℝ) ^ ((1 : ℝ) / 3)) (lo := 2.27) (hi := 2.31)
    (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num) (by norm_num)
    (by simpa using rpow_root_pow 3 (by norm_num)) (by norm_num) (by norm_num)
  have s4 := root_between 4 (r := (12 : ℝ) ^ ((1 : ℝ) / 4)) (lo := 1.86) (hi := 1.90)
    (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num) (by norm_num)
    (by simpa using rpow_root_pow 4 (by norm_num)) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> linarith [s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

/-- 差の大きさ: 3·48 − √12 > 1/100、|2·29 − ∛12| < 1/200、1·88 − ⁴√12 > 1/100。
印刷の "approximately" に許容誤差はないので、行の判定には使わない。 -/
theorem th_25_playfair_gap_sizes :
    (3.48 : ℝ) - Real.sqrt 12 > 1 / 100 ∧
    |(2.29 : ℝ) - (12 : ℝ) ^ ((1 : ℝ) / 3)| < 1 / 200 ∧
    (1.88 : ℝ) - (12 : ℝ) ^ ((1 : ℝ) / 4) > 1 / 100 := by
  have s2 := root_between 2 (r := Real.sqrt 12) (lo := 3.46) (hi := 3.47)
    (Real.sqrt_pos.mpr (by norm_num)) (by norm_num) (by norm_num)
    (by rw [Real.sq_sqrt (by norm_num)]) (by norm_num) (by norm_num)
  have s3 := root_between 3 (r := (12 : ℝ) ^ ((1 : ℝ) / 3)) (lo := 2.285) (hi := 2.295)
    (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num) (by norm_num)
    (by simpa using rpow_root_pow 3 (by norm_num)) (by norm_num) (by norm_num)
  have s4 := root_between 4 (r := (12 : ℝ) ^ ((1 : ℝ) / 4)) (lo := 1.85) (hi := 1.87)
    (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num) (by norm_num)
    (by simpa using rpow_root_pow 4 (by norm_num)) (by norm_num) (by norm_num)
  refine ⟨by linarith [s2.2], ?_, by linarith [s4.2]⟩
  rw [abs_lt]; constructor <;> linarith [s3.1, s3.2]

end KeynesNumerics

/-! ## 監査クエリ -/

#print axioms KeynesNumerics.th_4_17_four_balls
#print axioms KeynesNumerics.th_4_17_example_premises
#print axioms KeynesNumerics.th_4_17_example_needs_hx
#print axioms KeynesNumerics.th_4_17_example_needs_hy
#print axioms KeynesNumerics.th_21_fermat_primes
#print axioms KeynesNumerics.th_21_fermat_a4
#print axioms KeynesNumerics.th_21_euler_641
#print axioms KeynesNumerics.th_25_playfair_roots_within
#print axioms KeynesNumerics.th_25_playfair_gap_sizes
