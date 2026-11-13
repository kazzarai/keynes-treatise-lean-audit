# 外部公理の依存表 (external axioms)

この表は `tools/external_axioms.py` が台帳 (`chNN.md`・`notes_III.md`) の「外」(外部公理依存) の式行と `phases/*.lean` の宣言から作る。手で直さない。関門 [9] が `--check` で台帳との一致を確かめる。

- 外部公理: **11** 本 = 統計的前提 **10** 本＋データの整合性 **1** 本 (名前の数; 同じ名前を再掲したファイルは 1 本に数え、置いてあるファイルの欄に並べる)。
- 外 の式行: **15** 行 = 統計的前提に寄る行 15＋データの整合性だけに寄る行 0。
- 種別 (道具の中の表 `KIND` で与える): **統計的前提** は独立・等確率・近似・継起の規則・頻度と確率の一致など、Keynes の公理から出ない内容の前提。**データの整合性** は例のデータが矛盾しないことだけを置く前提。
- 公理の拾い方: Lean 欄 (括弧の中も含む) の `ax_…` のうち、同じ欄が挙げるファイルで `axiom` として宣言されているもの。1 行が複数の公理に寄るなら全部数える (表 1 の行数の和は 外 の行数より多くなりうる)。
- 必要性の定理: 公理と同じファイルの `nec_…` で、定理文が公理の結論の述語の否定 (`¬ 述語`) を述べるもの (公理を落とすと偽になる模型)、または `…_needs_ax` で docstring が公理の名前を挙げるもの。無ければ「なし」。

## 表 1 — 公理ごと

| 公理名 | 種別 | 置いてあるファイル | 中身の一文 (docstring の先頭文) | 寄りかかる行 (章ごと) | 行数 | 必要性の定理 |
|---|---|---|---|---|---|---|
| `ax_truth_frequency` | 統計的前提 | `keynes_part_i_phase15a_ch05_ch08.lean` | 外部公理: 頻度と確率の一致 (頻度理論の主張): 確率 a/h は、h が a に定める参照類の真理頻度a_α/h = α_f に等しい。 | ch08: 024 | 1 | `phase15a_ch05_ch08/th_8_r024_needs_ax` |
| `ax_bernoulli_independence` | 統計的前提 | `keynes_part_v_phase14a_bernoulli_premises.lean` | 外部公理 (ch29-043) (folio 343、§6): Bernoulli の定理が要する典型的条件`_{m+1}x_{n+1} / _m x_n . h = _1x_1 / h`。 | ch29: 043, 047 | 2 | `phase14a_bernoulli_premises/nec_29_043_model` |
| `ax_data_cons29` | データの整合性 | `keynes_part_v_phase14a_bernoulli_premises.lean` | 外部公理: h は矛盾する連言でない (公理 (i) の但し書きを第 29 章の data に当てはめたもの)。 | ch29: 047 | 1 | なし |
| `ax_equal_chance` | 統計的前提 | `keynes_part_v_phase14a_bernoulli_premises.lean` | 外部公理 (ch29-052) (folio 344、§7 (i.)): `a_1/h = a_2/h . . . = a_r/h`。 | ch29: 047, 052 | 2 | `phase14a_bernoulli_premises/nec_29_052_model` |
| `ax_independence_ii` | 統計的前提 | `keynes_part_v_phase14a_bernoulli_premises.lean` | 外部公理 (ch29-053) (folio 344、§7 (ii.)): `a_r / a_s . . . ā_t . . . h = a_r / h`。 | ch29: 047, 053 | 2 | `phase14a_bernoulli_premises/nec_29_053_model` |
| `ax_poisson_approx` | 統計的前提 | `keynes_part_v_phase16b_poisson_succession.lean` | Poisson の定理の解析的近似 (外部公理; Lindeberg–Feller の中心極限定理の Poisson 二項分布の場合):各 p_λ が δ ≤ p_λ ≤ 1 − δ (δ > 0) を満たし γ > 0 なら、\|m − sp\| < γk√s の確率は s → ∞ で Θ(γ) に近づく。 | ch29: 058, 063 | 2 | なし |
| `ax_poisson_independence` | 統計的前提 | `keynes_part_v_phase16b_poisson_succession.lean` | Poisson の定理の暗黙の前提 (folio 344–345 「It does not dispense, however, with the other inexplicit assumption」): 各回の生起は、それまでの生起の回数を知っても変わらない。 | ch29: 058, 063 | 2 | `phase16b_poisson_succession/nec_poisson_model` |
| `ax_succession_rule` | 統計的前提 | `keynes_part_v_phase16b_poisson_succession.lean` | 人工例の仮定 (folio 349–350): 起こるたびに次の回の確率が (r + k)/(s + k) に上がる (0 < r < s)。 | ch29: 075 | 1 | `phase16b_poisson_succession/nec_succession_model` |
| `ax_gen_succ` | 統計的前提 | `keynes_part_v_phase16c_tchebycheff.lean` | 一般の問題の前提 (folio 351): 最初の y 回で x 回起こったと知れば、y + 1 回目の確率は (r + x)/(s + y) (0 < r < s)。 | ch29: 086 | 1 | なし |
| `ax_normal_approx` | 統計的前提 | `keynes_part_v_phase15b_laplace.lean`<br>`keynes_part_v_phase16c_tchebycheff.lean` | 積分形の de Moivre–Laplace 定理 (外部公理、phase14b の ax_normal_approx の再掲): p ∈ (0, 1)、γ > 0 なら\|n − mp\| < √(2mpq) γ の確率は m → ∞ で Θ(γ) に近づく。 | ch29: 094, 149; ch30: 007 | 3 | なし |
| `ax_statistical_generalisation` | 統計的前提 | `keynes_part_v_phase15c_lexis_constructive.lean` | 外部公理: 統計的一般化の確率は既知の真理頻度に等しい: h が S の φ の真理頻度 f を知らせるなら、random member x について φ(x)/R(x, S, φ, h) . h = f。 | ch33: 021, 022, 026 | 3 | `phase15c_lexis_constructive/th_33_022_needs_ax` |

## 表 2 — 外 の行ごと

| 外の行 | 公理名 | 行の種別 |
|---|---|---|
| ch08-024 | `ax_truth_frequency` | 統計的前提 |
| ch29-043 | `ax_bernoulli_independence` | 統計的前提 |
| ch29-047 | `ax_bernoulli_independence`, `ax_data_cons29`, `ax_equal_chance`, `ax_independence_ii` | 統計的前提 |
| ch29-052 | `ax_equal_chance` | 統計的前提 |
| ch29-053 | `ax_independence_ii` | 統計的前提 |
| ch29-058 | `ax_poisson_independence`, `ax_poisson_approx` | 統計的前提 |
| ch29-063 | `ax_poisson_independence`, `ax_poisson_approx` | 統計的前提 |
| ch29-075 | `ax_succession_rule` | 統計的前提 |
| ch29-086 | `ax_gen_succ` | 統計的前提 |
| ch29-094 | `ax_normal_approx` | 統計的前提 |
| ch29-149 | `ax_normal_approx` | 統計的前提 |
| ch30-007 | `ax_normal_approx` | 統計的前提 |
| ch33-021 | `ax_statistical_generalisation` | 統計的前提 |
| ch33-022 | `ax_statistical_generalisation` | 統計的前提 |
| ch33-026 | `ax_statistical_generalisation` | 統計的前提 |
