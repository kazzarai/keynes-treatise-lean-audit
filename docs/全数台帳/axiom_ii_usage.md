# 公理 (ii) の中身 (前提側の置換) への依存の再集計 (全 phases)

- 作った元の記録: `logs/check_20261112T113959Z.log`、`logs/check_20261112T114444Z.log`、`logs/check_20261112T114609Z.log`、`logs/check_20261112T114824Z.log` (58 ファイル; git には入らない)。再生成: `bash tools/check_all.sh` の後に `python3 -I tools/axiom_ii_usage.py phases docs/全数台帳/axiom_ii_usage.md logs/check_<日時>.log` (関門には入れていない)。
- 公理 (ii) (folio 135): (a ≡ b)/h = 1 ならば x/ah = x/bh。前提 (証拠) の側の置換。列は名前ではなく中身で分ける。
- (A) 前提側の置換の公理: 型が「前提の同値 → 同じ結論の確率が等しい」の形の公理 (下の表 A; 名前が (ii) でないものも含む)。(B) 整合性の移送の公理 `cons_iff_taut` (論証的同値な命題は整合性を共有する)。(C) どちらにも依存しない。
- #print axioms の行数は関門 [3] の verdicts と同じ数え方 (「depends on axioms」の数)。

#print axioms の **1,949** 行 (58 ファイル) のうち、(A) 前提側の置換の公理に依存するのは **5** 行、(B) 整合性の移送の公理に依存するのは **1** 行、(C) どちらにも依存しないのは **1,943** 行 ((A) と (B) の両方に依存するのは 0 行)。内訳は下表。

| ファイル | #print axioms の行数 | (A) 前提側の置換 | (B) 整合性の移送 | (C) どちらにも依存しない |
|---|---|---|---|---|
| `keynes_misc_numerics.lean` | 9 | 0 | 0 | 9 |
| `keynes_part_i_phase12a_order.lean` | 48 | 0 | 0 | 48 |
| `keynes_part_i_phase13a_irrelevance.lean` | 42 | 0 | 0 | 42 |
| `keynes_part_i_phase13b_weight_lines.lean` | 12 | 0 | 0 | 12 |
| `keynes_part_i_phase15a_ch05_ch08.lean` | 25 | 0 | 0 | 25 |
| `keynes_part_i_phase17_closing.lean` | 16 | 0 | 0 | 16 |
| `keynes_part_i_phase8dp.lean` | 27 | 0 | 0 | 27 |
| `keynes_part_ii_phase10a.lean` | 36 | 0 | 0 | 36 |
| `keynes_part_ii_phase10b.lean` | 101 | 0 | 1 | 100 |
| `keynes_part_ii_phase10c.lean` | 121 | 0 | 0 | 121 |
| `keynes_part_ii_phase10d.lean` | 119 | 0 | 0 | 119 |
| `keynes_part_ii_phase10e.lean` | 47 | 0 | 0 | 47 |
| `keynes_part_ii_phase10f.lean` | 35 | 0 | 0 | 35 |
| `keynes_part_ii_phase10g.lean` | 19 | 0 | 0 | 19 |
| `keynes_part_ii_phase10h.lean` | 60 | 0 | 0 | 60 |
| `keynes_part_ii_phase12b_underdetermination.lean` | 22 | 0 | 0 | 22 |
| `keynes_part_ii_phase16a_boole_challenge.lean` | 48 | 0 | 0 | 48 |
| `keynes_part_ii_phase2.lean` | 7 | 0 | 0 | 7 |
| `keynes_part_ii_phase3a.lean` | 7 | 0 | 0 | 7 |
| `keynes_part_ii_phase3b.lean` | 7 | 0 | 0 | 7 |
| `keynes_part_ii_phase3c.lean` | 7 | 0 | 0 | 7 |
| `keynes_part_ii_phase3d.lean` | 4 | 0 | 0 | 4 |
| `keynes_part_ii_phase4.lean` | 13 | 0 | 0 | 13 |
| `keynes_part_ii_phase5.lean` | 22 | 0 | 0 | 22 |
| `keynes_part_ii_phase6a.lean` | 14 | 1 | 0 | 13 |
| `keynes_part_ii_phase6b.lean` | 37 | 4 | 0 | 33 |
| `keynes_part_ii_phase6c.lean` | 12 | 0 | 0 | 12 |
| `keynes_part_ii_phase6c_inconsistency.lean` | 2 | 0 | 0 | 2 |
| `keynes_part_ii_phase6c_model.lean` | 19 | 0 | 0 | 19 |
| `keynes_part_ii_phase6c_necessity.lean` | 29 | 0 | 0 | 29 |
| `keynes_part_ii_phase6c_skeleton.lean` | 3 | 0 | 0 | 3 |
| `keynes_part_ii_phase7a.lean` | 3 | 0 | 0 | 3 |
| `keynes_part_ii_phase7b.lean` | 8 | 0 | 0 | 8 |
| `keynes_part_ii_phase7c.lean` | 8 | 0 | 0 | 8 |
| `keynes_part_ii_phase7d.lean` | 7 | 0 | 0 | 7 |
| `keynes_part_ii_phase7e.lean` | 4 | 0 | 0 | 4 |
| `keynes_part_ii_phase7g.lean` | 14 | 0 | 0 | 14 |
| `keynes_part_ii_phase7h.lean` | 15 | 0 | 0 | 15 |
| `keynes_part_ii_phase7i.lean` | 25 | 0 | 0 | 25 |
| `keynes_part_ii_phase7i_model.lean` | 36 | 0 | 0 | 36 |
| `keynes_part_ii_phase8a.lean` | 13 | 0 | 0 | 13 |
| `keynes_part_ii_phase8b.lean` | 16 | 0 | 0 | 16 |
| `keynes_part_ii_phase8c.lean` | 9 | 0 | 0 | 9 |
| `keynes_part_ii_phase8d.lean` | 9 | 0 | 0 | 9 |
| `keynes_part_ii_phase9x.lean` | 71 | 0 | 0 | 71 |
| `keynes_part_ii_pilot.lean` | 2 | 0 | 0 | 2 |
| `keynes_part_iii_phase18_notation.lean` | 1 | 0 | 0 | 1 |
| `keynes_part_iii_phase9a.lean` | 60 | 0 | 0 | 60 |
| `keynes_part_iii_phase9b.lean` | 28 | 0 | 0 | 28 |
| `keynes_part_iii_phase9c.lean` | 36 | 0 | 0 | 36 |
| `keynes_part_iv_phase8a2.lean` | 36 | 0 | 0 | 36 |
| `keynes_part_iv_phase8a3_endpoints.lean` | 19 | 0 | 0 | 19 |
| `keynes_part_v_phase14a_bernoulli_premises.lean` | 57 | 0 | 0 | 57 |
| `keynes_part_v_phase14b_bernoulli_analytic.lean` | 70 | 0 | 0 | 70 |
| `keynes_part_v_phase15b_laplace.lean` | 59 | 0 | 0 | 59 |
| `keynes_part_v_phase15c_lexis_constructive.lean` | 95 | 0 | 0 | 95 |
| `keynes_part_v_phase16b_poisson_succession.lean` | 145 | 0 | 0 | 145 |
| `keynes_part_v_phase16c_tchebycheff.lean` | 133 | 0 | 0 | 133 |
| **計** | **1,949** | **5** | **1** | **1,943** |

## 表 A — (A) に数えた公理

`tools/axiom_ii_usage.py` の表 `A_AXIOMS` の写し。型は宣言の名前の後をそのまま写す (空白は詰める)。

| 公理の完全名 | 置いてあるファイル | 型 |
|---|---|---|
| `Keynes.ax_ii` | `keynes_part_ii_phase2.lean` | `(α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)` |
| `Keynes.ax_ii` | `keynes_part_ii_phase3a.lean` | `(α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)` |
| `Keynes.ax_ii` | `keynes_part_ii_phase3b.lean` | `(α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)` |
| `Keynes.ax_ii` | `keynes_part_ii_phase3c.lean` | `(α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)` |
| `Keynes.ax_iii_ev` | `keynes_part_ii_phase6a.lean` | `(p h k : Prop) : (h ↔ k) → Pr p h = Pr p k` |
| `Keynes.ax_iii_ev` | `keynes_part_ii_phase6b.lean` | `(p h k : Prop) : (h ↔ k) → Pr p h = Pr p k` |

## (A) に依存する定理 (5 本)

- `keynes_part_ii_phase6a.lean`: `Keynes.th_14_46_1` (依存: `Keynes.ax_iii_ev`)
- `keynes_part_ii_phase6b.lean`: `Keynes.th_13_21` (依存: `Keynes.ax_iii_ev`)
- `keynes_part_ii_phase6b.lean`: `Keynes.th_14_26` (依存: `Keynes.ax_iii_ev`)
- `keynes_part_ii_phase6b.lean`: `Keynes.th_14_26_1` (依存: `Keynes.ax_iii_ev`)
- `keynes_part_ii_phase6b.lean`: `Keynes.th_14_29` (依存: `Keynes.ax_iii_ev`)

## (B) に依存する定理 (1 本)

- `keynes_part_ii_phase10b.lean`: `KeynesI.th_13_13_r090`

## 脚注

1. 名前と中身の対応: `Keynes.ax_ii` (phase2・3a–3c) は名前も中身も公理 (ii) で、前提の同値を `KEq α β h` (β/αh = 1 かつ α/βh = 1) で述べる。`Keynes.ax_iii_ev` (phase6a・6b) は名前は (iii) だが、中身は前提側の置換で、前提の同値を論理的同値 `h ↔ k` で述べる。`cons_iff_taut` は docstring が「公理 (ii) と公理 (iii) を合わせると」と述べるが、述べるのは整合性 `Cons` の移送で、確率の等式ではない。
2. 記録で (A) の公理名を定理名に含むが、(A) に依存しない定理 (模型の上の検算など; 数えていない): `keynes_part_ii_phase12b_underdetermination.lean` の `KeynesI_underdet.model_ax_ii` (依存: [propext, Classical.choice, Quot.sound])、`keynes_part_ii_phase7i_model.lean` の `KeynesExtModel.m_ax_ii` (依存: [propext, Classical.choice, Quot.sound])、`keynes_part_ii_phase7i_model.lean` の `KeynesExtModel.m_ax_iii_ev` (依存: [propext, Classical.choice, Quot.sound])。
3. Prop 担体 (`Pr : Prop → Prop → ℝ`) のファイル: Lean の `propext : (a ↔ b) → a = b` があるので、`h ↔ k` から `h = k` が出て、`Pr p h = Pr p k` は書換え 1 回 (`rw [propext e]`) で得られる。これは `ax_iii_ev` の型そのもので、公理を置かなくても得られる。`ax_ii` の前提 `KEq α β h` は確率 1 の相互含意で `↔` ではないので、この書換えはそのままは当てはまらない。
4. IProp 担体 (`PrI : IProp → IProp → ℝ`、内包的) のファイル: (A) に当たる公理を置いていない (上の洗い出しで 0 本)。`propext` は Lean の `Prop` の等式を与えるだけで、`IProp` の値の等式は与えない。(ii) の中身は定理 `prem_subst` (Cons h、(a ≡ b)/h = 1、ah が整合のとき x/ah = x/bh) として、公理 (i) の但し書きの下で Def. X と (12) から導いている: `keynes_part_ii_phase10b.lean` の `KeynesI.prem_subst`。
