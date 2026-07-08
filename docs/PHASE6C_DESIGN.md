# Phase 6c 設計メモ: 内包移行 (pedantic Ax.(iii) + Th.(12) over IProp)

**日付**: 2026-07-07 / **作成**: Fable 5 セッション / **実装対象**: Phase 6c 本番 (後継セッション可)
**スケルトン**: `修論Prolog復元/keynes_part_ii_phase6c_skeleton.lean` (コンパイル確認対象)
**動機**: Finding 15–16 (縮退定理・素朴Ax.(前)の矛盾) の原因である融合形 `ax_iii_op` を、Keynes の字面に忠実な pedantic 形に置換し、縮退が消えるかを判定する (論文の Open question)。

---

## 1. 何を作るか (成果物)

1. `keynes_part_ii_phase6c.lean` — 完成版: KTaut 生成子の全収録 + `th_12_i` の定理降格 + アンカー定理の内包版再証明 (最低限: 補完律・(24)・(36)・(38))
2. **縮退不能の反例証明書**: 値 1/2 を実現する Popper 関数モデル (§4)
3. §7.15 (仮) への結果追記: pedantic 経路の kernel コスト初測定

## 2. 公理層の設計 (スケルトンで確定済み)

- `IProp : Type` — **不透明型**。Prop ではないので `Classical.em` の対象外。これが縮退遮断の型レベル機構。
- 結合子 `iand/ior/inot/iiff/itrue` を公理化 (IProp が不透明なので演算も公理)。
- Keynes 操作公理 (`def_IX_i`, `def_X_left_i/right_i`, 範囲原理) は外延版の写し。
- `KTaut : IProp → Prop` + 生成子 = **Keynes が Ch.12 §5 で列挙したトートロジー図式そのもの**。
- `ax_iii_pedantic : KTaut t → PrI t h = 1` — これが Ax.(iii) の字面に忠実な形。

## 3. 実装上の規律 (破ると縮退が再侵入する)

### 3.1 生成子は閉じた図式のみ
`KTaut` の生成子に「p が真なら KTaut (iiff p itrue)」のような**真理条件つき生成子を絶対に追加しない**。それは実質的同値の再導入であり、Finding 15 の縮退がそのまま復活する。生成子は全称量化された閉スキーマ (交換・結合・冪等・二重否定・De Morgan・分配・吸収) に限る。

### 3.2 ktaut_subst の扱い (設計判断が要る)
スケルトンでは文脈代入 `KTaut (iiff a b) → KTaut (iiff (p∧a) (p∧b))` を公理で仮置きした。本番の選択肢:
- **案A (shallow のまま)**: 代入生成子を必要な文脈形ごとに公理追加。速いが公理数が増え、監査の美観が落ちる。
- **案B (deep embedding)**: 構文型 `inductive Form` + 評価 `⟦·⟧ : Form → IProp` + 決定可能なトートロジー判定 (真理表) を Lean 内で実装し、`KTaut ⟦f⟧ ↔ taut_check f = true` で生成。公理が激減し「論証的同値」の意味が計算になる。工数 +3–4h。**推奨は案B** (論文的にも「demonstrated equivalence = 決定手続き」はケインズの論証観の良い形式化)。
- 案Bなら `Decidable` インスタンス経由の `decide` が使える。再帰子を使うので C_rec 消費 — Finding 17 の枠組みで報告。

### 3.3 th_12_i の定理降格
外延版 `th_13_12` (Phase 6b) の証明構造を移植する: 象限分解 (def_IX_i) + 確実双条件の連言消去。必要な KTaut 生成子: `(a ∧ (a↔b)) ↔ (b ∧ (a↔b))` 型 — 案Bなら真理表で自動。降格成功後の `#print axioms th_12_i` が「pedantic 経路の実コスト」の初測定になる。

### 3.4 移植する定理の優先順
1. 補完律 (13.1 内包版) — `ktaut_and_true` 系で True 消去
2. 加法定理 (24) — `(α∨β)∧¬β ↔ α∧¬β` 等の生成子が必要 (ior 系)
3. 乗法 (36)・Bayes (38) — def_X_i 系のみ、生成子不要のはず
4. Ax.(前) 内包版 (Phase 4 の Intensional.ax_mae を IProp に合流) — H16
5. Ch.15 限界定理の内包版 — 範囲原理は移植済みなので機械的

## 4. 縮退不能の反例証明書 (H15 の証明方法)

構文的独立性証明は重すぎるので、**モデル構成**で行う:

- **Popper 関数** (Popper 1955 / Rényi 1955 / van Fraassen 1976 の条件付き確率プリミティブ) が自然なモデル。歴史的にも Popper は Keynes Ch.12 を意識して条件付き確率を公理化しており、系譜として論文に書ける。
- 最小実装: `IProp := Bool → Bool` (2 世界の命題) または有限集合代数、`PrI a e := (a∩e の測度)/(e の測度)`、零測度証拠には Popper 規約 (PrI a e := 1) を使う。
- 検証すべきこと: def_IX_i / def_X 両形 / 範囲原理 / ax_iii_pedantic (KTaut 生成子は全て真理表恒真なので測度 1) が成立し、かつ **PrI がどこかで 1/2 を取る**。
- Lean 実装は `noncomputable def modelPrI : ...` + `example : modelPrI a₀ e₀ = 1/2 := by norm_num` + 各公理のモデル内証明 (`theorem model_def_IX : ...`)。これで「公理系は値 1/2 と両立する」= 縮退定理の否定が**機械証明書**になる。
- ⚠️ 注意: モデルは KeynesI の公理を「充足する構造がある」ことを示すのであって、Lean の axiom 宣言と直接は繋がらない (axiom は無条件仮定)。論文では「反例モデルの存在により、KeynesI 公理系からの縮退導出は健全性に反する = 導出不能」という標準的なモデル論的独立性論法で書く。

## 5. 予想される結果と論文への接続

- H15 成立なら: **縮退は融合形の人工物**と確定 → Finding 15–16 の解釈が「エンコーディングの教訓」として完結し、§7.12 の非対称性議論はそのまま強化される (Ch.15 が内包性を要求するという主張は、素朴形→pedantic 形の対比として残る)。
- H15 不成立 (縮退が pedantic でも出る) なら: 内包性要求は表層より深い — それ自体が大発見なので、どちらに転んでも論文になる。
- 投稿論文への影響: JPKE 稿 (master rev4) は Phase 6c の結果を**要求しない** (Open question として明示済み)。6c の結果は論文 B (自動推論系) の主素材。

## 6. 工数見積

案A: 3–4h / 案B: 6–8h (真理表判定器の実装込み)。検証ラン 1–2 回。

## 7. 開始手順 (後継セッション向け)

1. スケルトンを実行し 3 つの煙試験が通ることを確認 (`lake env lean phases/keynes_part_ii_phase6c_skeleton.lean`)
2. 案A/案B を新井さんに選んでもらう (推奨 B)
3. §3.4 の順に移植、各段で `#print axioms`
4. §4 のモデルを最後に (独立作業可)
