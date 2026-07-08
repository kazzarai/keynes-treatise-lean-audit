% ============================================================
% keynes_axioms_v2.pl
% ケインズ『確率論』第II部（第12章〜第17章）v2: Ch.17 追補版
% 公理・定義の引用・被引用関係 Prolog ホーン節データベース
%
% 新井一成 再作成版（2026年3月）→ 2026年4月 v2 拡張（新井一成・Claude Opus 4.7）
% 旧版: 高籔研究室PC（没収）→ Ruby/Prolog, 修士論文付属データ
%
% v1 → v2 差分:
%   - 第17章（逆確率ならびに平均に関する若干の問題）の定理 17 本を追加
%   - 引用関係 25 本を追加
%   - Def.X 引用数: 24 → 29（Paper 7&8 主張と一致）
%   - 総引用関係: 152 → 177
%   - 定理総数: 83 → 100
%
% 構造:
%   defined_in(節点ID, 章, 節番号, 種別, ラベル, 説明).
%   cites(定理/定義ID, 引用元ID, 引用の種別).
%   theorem_proves(定理ID, 内容).
% ============================================================

:- encoding(utf8).

% ============================================================
% 第12章 定義 (Definitions I〜XIV)
% ============================================================

defined_in(def_i,    12, 4, definition, 'Def.I',
    '確率関係記号: α/h = P').
defined_in(def_ii,   12, 4, definition, 'Def.II',
    '確実性: P = 1').
defined_in(def_iii,  12, 4, definition, 'Def.III',
    '不可能性: P = 0').
defined_in(def_iv,   12, 4, definition, 'Def.IV',
    '非確実性: P < 1').
defined_in(def_v,    12, 4, definition, 'Def.V',
    '非不可能性: P > 0').
defined_in(def_vi,   12, 4, definition, 'Def.VI',
    '不整合性: α/h=0 ならば αh は不整合').
defined_in(def_vii,  12, 4, definition, 'Def.VII',
    '群: α/h=1 であるような命題クラスα = hによって定まる群').
defined_in(def_viii, 12, 4, definition, 'Def.VIII',
    '等値: b/αh=1 かつ α/bh=1 ならば (α=b)/h=1').
defined_in(def_ix,   12, 6, definition, 'Def.IX',
    '加法定義: αb̄/h + αb/h = α/h').
defined_in(def_x,    12, 6, definition, 'Def.X',
    '乗法定義: α/h・αb/h = α/bh・b/h = b/αh').
defined_in(def_xi,   12, 6, definition, 'Def.XI',
    '除法定義: PQ=R ならば P=R/Q').
defined_in(def_xii,  12, 6, definition, 'Def.XII',
    '減法定義: P+Q=R ならば P=R-Q').
defined_in(def_xiii, 12, 8, definition, 'Def.XIII',
    '独立性: α₁/α₂h=α₁/h かつ α₂/α₁h=α₂/h').
defined_in(def_xiv,  12, 8, definition, 'Def.XIV',
    '無関連性: α₁/α₂h=α₁/h ならば α₂ は α₁/h に無関連').

% ============================================================
% 第12章 公理 (Preliminary Axioms + Operation Axioms)
% ============================================================

defined_in(ax_i,   12, 5, axiom, 'Ax.(i)',
    '存在・一意性公理: 整合的hに対し確率関係は唯一存在').
defined_in(ax_ii,  12, 5, axiom, 'Ax.(ii)',
    '等値公理: (α=b)/h=1 かつ c命題 ならば c/αh = c/bh').
defined_in(ax_iii, 12, 5, axiom, 'Ax.(iii)',
    'トートロジー公理群: (α+b≡ᾱb)/h=1等; α/h=1→αh=h').
defined_in(ax_iva, 12, 6, axiom, 'Ax.(iva)',
    '交換律: PQ=QP, P+Q=Q+P').
defined_in(ax_ivb, 12, 6, axiom, 'Ax.(ivb)',
    '順序公理: Q≠1またはP≠0→PQ<P; Q≠0→P+Q>P 等').
defined_in(ax_ivc, 12, 6, axiom, 'Ax.(ivc)',
    '消去律: PQ≠PR かつP≠0→Q≠R; P+Q≠P+R→Q≠R').
defined_in(ax_v,   12, 6, axiom, 'Ax.(v)',
    '混合演算結合律: [±P±Q]+[±R±S]=[±P±R]∓[±Q∓S]').
defined_in(ax_vi,  12, 6, axiom, 'Ax.(vi)',
    '分配律: P(R±S)=PR±PS').

% ============================================================
% 第15章 公理 (数値測定公理)
% ============================================================

defined_in(ax_xviii, 15, 2, axiom, 'Ax.XVIII',
    '加算公理: α/h+{α/h+[α/h+...]}=γ・α/h').
defined_in(ax_xix,   15, 2, axiom, 'Ax.XIX',
    '比例公理: γ=b//ならばα/h=テ/...').
defined_in(ax_mae,   15, 2, axiom, 'Ax.(前)',
    '実数値存在公理: p<nに対し確率関係p/nが存在する').

% ============================================================
% 第13章 定理 (必然的推理の基本定理)
% ============================================================

theorem_proves(th13_1,
    '(1) α/h + ᾱ/h = 1 [矛盾命題の確率の和=1]').
theorem_proves(th13_2,
    '(2) α/h < 1 [非確実なら1未満]').
theorem_proves(th13_3,
    '(3) α/h > 0 [非不可能なら0超]').
theorem_proves(th13_4,
    '(4) αb/h ≤ b/h [結合確率の上界]').
theorem_proves(th13_5,
    '(5) P+Q=0 → P=0 かつ Q=0').
theorem_proves(th13_6,
    '(6) PQ=0 → P=0 または Q=0').
theorem_proves(th13_7,
    '(7) PQ=1 → P=1 かつ Q=1').
theorem_proves(th13_8,
    '(8) α/h=0 かつ bh整合 → αb/h=0, α/bh=0 [不可能命題の前提追加不変性]').
theorem_proves(th13_9,
    '(9) α/h=1 かつ bh整合 → α/bh=1 [確実命題の前提追加不変性]').
theorem_proves(th13_10,
    '(10) α/h=1 → αb/h = b/h').
theorem_proves(th13_11,
    '(11) αb/h=1 → α/b=1').
theorem_proves(th13_12,
    '(12) (α=b)/h=1 → α/h=b/h [等値命題の確率等値性]').
theorem_proves(th13_12_1,
    '(12.1) (α=b)/h=1 かつ ᾱh整合 → α/hᾱ=b/hᾱ').
theorem_proves(th13_13,
    '(13) αが整合 → α/α=1 [同語反復]').
theorem_proves(th13_13_1,
    '(13.1) αが整合 → ᾱ/α=0').
theorem_proves(th13_13_2,
    '(13.2) ᾱが整合 → α/ᾱ=0').
theorem_proves(th13_14,
    '(14) α/b=0 かつ α整合 → b/α=0 [不可能性の対称性]').
theorem_proves(th13_15,
    '(15) h₁/h₂=0 → h₁h₂/h=0').
theorem_proves(th13_15_1,
    '(15.1) h₂/h=0 かつ h₂h整合 → h₁/h₂h=0 [(15)の逆]').
theorem_proves(th13_16,
    '(16) h₁/h₂=1 → (h₁+h₂)/h=1').
theorem_proves(th13_16_1,
    '(16.1) h₁/h₂=1 → (h₂⊃h₁)/h=1').
theorem_proves(th13_16_2,
    '(16.2) (h₁+h₂)/h=1 かつ h₂h整合 → h₁/h₂h=1').
theorem_proves(th13_16_3,
    '(16.3) (h₂⊃h₁)/h=1 かつ h₂h整合 → h₁/h₂h=1').
theorem_proves(th13_17,
    '(17) (h₁⊃:α=b)/h=1 かつ h₁h整合 → α/h₁h=b/h₁h').
theorem_proves(th13_18,
    '(18) α/α=1 または ᾱ/ᾱ=1 [同語反復の普遍性]').
theorem_proves(th13_19,
    '(19) αᾱ/h=0 [矛盾原理]').
theorem_proves(th13_20,
    '(20) (α+ᾱ)/h=1 [排中原理]').
theorem_proves(th13_21,
    '(21) α/h₁=1 かつ α/h₂=0 → h₁h₂/h=0').
theorem_proves(th13_22,
    '(22) α/h₁=0 かつ h₁/h=1 → α/h=0').
theorem_proves(th13_23,
    '(23) b/α=0 かつ bᾱ=0 → b/h=0').

% ============================================================
% 第14章 定理 (蓋然的推理の基本定理)
% ============================================================

theorem_proves(th14_24,
    '(24) 加法定理: (α+b)/h = α/h + b/h - αb/h').
theorem_proves(th14_24_1,
    '(24.1) αb/h=0 → (α+b)/h = α/h + b/h [排反選択肢の加法]').
theorem_proves(th14_24_2,
    '(24.2) αb/h + ᾱb/h = b/h').
theorem_proves(th14_24_3,
    '(24.3) (α+b)/h = α/h + ᾱb/h').
theorem_proves(th14_24_4,
    '(24.4) (α+b+c)/h への拡張').
theorem_proves(th14_24_5,
    '(24.5) n項への一般化').
theorem_proves(th14_24_6,
    '(24.6) 相互排反ならば (p₁+...+pₙ)/h = Σpₙ/h').
theorem_proves(th14_24_7,
    '(24.7) 相互排反かつ完全なら Σpₙ/h=1').
theorem_proves(th14_25,
    '(25) 全確率公式: α/h = Σpₙ α/pₙh [相互排反完全系]').
theorem_proves(th14_25_1,
    '(25.1) (25)の整理形').
theorem_proves(th14_26,
    '(26) α/h = (α+h)/h [前提の群への吸収]').
theorem_proves(th14_26_1,
    '(26.1) α/h = (h⊃α)/h').
theorem_proves(th14_27,
    '(27) (α+b)/h=0 → α/h=0').
theorem_proves(th14_27_1,
    '(27.1) α/h=0 かつ b/h=0 → (α+b)/h=0').
theorem_proves(th14_28,
    '(28) α/h=1 → (α+b)/h=1 [確実命題はすべて合意する]').
theorem_proves(th14_28_1,
    '(28.1) α/h=0 → (ᾱ+b)/h=1').
theorem_proves(th14_29,
    '(29) α/(h₁+h₂)=1 → α/h₁=1 かつ α/h₂=1').
theorem_proves(th14_30,
    '(30) α/h₁h₂=α/h₁ かつ h₁h₂整合 → α/h₁h₂=α/h₁ [無関連定理]').
theorem_proves(th14_31,
    '(31) α₂/α₁h=α₂/h かつ α₂h整合 → α₁/α₂h=α₁/h [独立性の対称性]').
theorem_proves(th14_32,
    '(32) α/hh₁>α/h → h₁/αh>h₁/h [好都合な関連の対称性]').
theorem_proves(th14_33,
    '(33) 関連の推移性').
theorem_proves(th14_34,
    '(34) 関連の合成').
theorem_proves(th14_35,
    '(35) 複合関連').
theorem_proves(th14_36,
    '(36) 乗法定理: α₁/h と α₂/h が独立 → α₁α₂/h = α₁/h・α₂/h').
theorem_proves(th14_37,
    '(37) 連鎖乗法: pᵢ/h が条件付き等確率 → p₁p₂...pₙ/h = {p₁/h}ⁿ').
theorem_proves(th14_38,
    '(38) 逆原理 (ベイズ定理): α₁/bh / α₂/bh = (α₁/h・b/α₁h) / (α₂/h・b/α₂h)').
theorem_proves(th14_38_1,
    '(38.1) ベイズ定理の2仮説形: α₁/bh = p₁q₁/(p₁q₁+p₂q₂)').
theorem_proves(th14_39,
    '(39) 前提結合定理').
theorem_proves(th14_40,
    '(40) 前提結合の一般形').
theorem_proves(th14_41,
    '(41) W.E.ジョンソン累積公式: αb/h = α/bh・b/h [影響係数展開]').
theorem_proves(th14_41_1,
    '(41.1) αbc/h = {αbc}・α/h・b/h・c/h [3項影響係数展開]').
theorem_proves(th14_41_2,
    '(41.2) 一般n項累積: α₁α₂...αₙ/h = {α₁α₂...αₙ}・α₁/h・α₂/h・...・αₙ/h').
theorem_proves(th14_42,
    '(42) {αb}={bα} [影響係数の交換律]').
theorem_proves(th14_42_1,
    '(42.1) {αbc}={αcb} [3項交換律]').
theorem_proves(th14_42_2,
    '(42.2) 一般交換規則: 項の順序を任意に入れ替え可能').
theorem_proves(th14_43,
    '(43) 分離因数規則: 乗数として分離因数は被乗数における連合を分離する').
theorem_proves(th14_44,
    '(44) {αb}={α}・{b} [独立な場合の積分解]').
theorem_proves(th14_44_1,
    '(44.1) {αb}=1 ならば α/h と b/h は独立な推論').
theorem_proves(th14_45,
    '(45) 反復規則: {ααb}={αb} [(ii)と(12)より αα/h=α/h]').
theorem_proves(th14_46,
    '(46) 累積公式: (38)より Π n/αh・n/bh・... = (n/h)ⁿ {αbε...}・Π n/αh・Π n/bh・...').
theorem_proves(th14_46_1,
    '(46.1) もし αbc...{α nb...}=n/nh ならば α.../nh ≅ {αnε...}n/αh・n/bh・...').
theorem_proves(th14_46_2,
    '(46.2) 相互排反完全系への拡張: Σ n/h αbc...=(n/h)ⁿ{αttε磁...}Πn/αh のベイズ展開').
theorem_proves(th14_47,
    '(47) 逆公式: n/h αbc... / n/h αbc... = (n/h)Π[n/αh]/[(n/h)Π[n/αh]] [比率形]').
theorem_proves(th14_47_1,
    '(47.1) (47)の凝縮形').
theorem_proves(th14_48,
    '(48) 2仮説の比率形展開').
theorem_proves(th14_49,
    '(49) 証拠累積定理: α,b,c,...が命題nを支持するとき，各データの相互確率を強化する').
theorem_proves(th14_49_1,
    '(49.1) 相互排反完全系への一般化').

% ============================================================
% 第15章 定理 (確率の数値測定)
% ============================================================

theorem_proves(th15_50,
    '(50) α/n+b/nが存在条件: (前)の公理より').
theorem_proves(th15_51,
    '(51) αy/h は α/h と α/h+y/h-1 の間，かつ y/h と y/h+α/h-1 の間').
theorem_proves(th15_52,
    '(52) α₁α₂...αₙ/h は常に Σαₙ/h - n+1 より大').
theorem_proves(th15_53,
    '(53) αy/h+πy/h は常に y/h-α/h+1 より小，かつ α/h-y/h+1 より小').
theorem_proves(th15_54,
    '(54) αy/h - πȳ/h = α/h + y/h - 1 [(51)(53)から直接導出]').
theorem_proves(th15_55,
    '(55) 確率記号から消去法による系統的近似法 [Booleの問題への適用]').

% ============================================================
% 引用関係 cites(定理ID, 引用先ID, メモ)
% ============================================================

% === 第13章 ===

% (1) α/h + ᾱ/h = 1
cites(th13_1, def_ix,   '加法定義から展開').
cites(th13_1, def_x,    '乗法定義で変形').
cites(th13_1, ax_iii,   'b=h置換のトートロジー').

% (2) α/h < 1
cites(th13_2, def_iv,   '非確実性の定義直接適用').

% (3) α/h > 0
cites(th13_3, def_v,    '非不可能性の定義直接適用').

% (4) αb/h ≤ b/h
cites(th13_4, def_x,    '乗法定義から分解').
cites(th13_4, ax_ivb,   '順序公理').

% (5) P+Q=0 → P=0, Q=0
cites(th13_5, ax_ivb,   '順序公理: Q≠0→P+Q>P').
cites(th13_5, def_v,    '非不可能性の定義').

% (6) PQ=0 → P=0 or Q=0
cites(th13_6, def_v,    'Vにより条件の対偶').
cites(th13_6, ax_ivb,   '(ivb)による積の正値性').

% (7) PQ=1 → P=1, Q=1
cites(th13_7, ax_ivb,   '(ivb)直接').
cites(th13_7, def_iv,   'Ⅳにより1未満の否定').

% (8) α/h=0 ∧ bh整合 → αb/h=0, α/bh=0
cites(th13_8, def_x,    '乗法定義: Xにより').
cites(th13_8, th13_5,   '(5)の適用').
cites(th13_8, def_vi,   'Ⅵにより不整合の定義').

% (9) α/h=1 ∧ bh整合 → α/bh=1
cites(th13_9, th13_1,   '(1.1)の適用').
cites(th13_9, th13_8,   '(8)の適用').
cites(th13_9, th13_1,   '(1.4)の適用').

% (10) α/h=1 → αb/h = b/h
cites(th13_10, def_x,   'Xによる展開').
cites(th13_10, th13_9,  '(9)の適用').
cites(th13_10, ax_ivc,  '(ivc)による等式変形').

% (11) αb/h=1 → α/b=1
cites(th13_11, def_x,   'Xによる分解').
cites(th13_11, th13_7,  '(7)の適用').

% (12) (α=b)/h=1 → α/h=b/h
cites(th13_12, def_x,   'Xにより双方向展開').
cites(th13_12, def_viii, 'Ⅷ等値定義').
cites(th13_12, ax_ivb,  '(ivb)順序').

% (12.1)
cites(th13_12_1, def_ii,  'Ⅱ確実性').
cites(th13_12_1, th13_12, '(12)の適用').
cites(th13_12_1, def_x,   'Xによる変形').
cites(th13_12_1, ax_ii,   '等値公理(ii)').

% (13) αが整合 → α/α=1
cites(th13_13, ax_iii,   '(iii)トートロジー').
cites(th13_13, th13_12,  '(12)等値').
cites(th13_13, def_x,    'Xにより').
cites(th13_13, ax_ii,    '(ii)等値公理').
cites(th13_13, def_vi,   'Ⅵ不整合定義').
cites(th13_13, ax_i,     '(i)存在・一意性').

% (13.1)
cites(th13_13_1, th13_13, '(13)').
cites(th13_13_1, th13_1,  '(1.1)').

% (13.2)
cites(th13_13_2, th13_13_1, '(13.1)αをᾱで置換').
cites(th13_13_2, ax_iii,    '(iii)').

% (14) α/b=0 ∧ α整合 → b/α=0
cites(th13_14, ax_iii,   '(iii)で仮想基底群j導入').
cites(th13_14, th13_12,  '(12)等値変換').
cites(th13_14, def_x,    'Xにより積分解').

% (15) h₁/h₂=0 → h₁h₂/h=0
cites(th13_15, def_x,    'Xにより').
cites(th13_15, th13_8,   '(8)の適用').
cites(th13_15, ax_ivb,   '(ivb)').
cites(th13_15, th13_14,  '(14)の適用').

% (15.1)
cites(th13_15_1, th13_15, '(15)の逆').
cites(th13_15_1, def_x,   'X').
cites(th13_15_1, th13_6,  '(6)').

% (16) h₁/h₂=1 → (h₁+h₂)/h=1
cites(th13_16, th13_1,   '(1)適用').
cites(th13_16, th13_15,  '(15)適用').
cites(th13_16, th13_1,   '(1.3)適用').
cites(th13_16, th13_12,  '(12)適用').
cites(th13_16, ax_i,     '(i)存在・一意性').

% (16.2)
cites(th13_16_2, th13_15_1, '(15.1)適用').
cites(th13_16_2, th13_1,    '(1.4)').

% (17)
cites(th13_17, th13_16_3, '(16.3)').
cites(th13_17, th13_12,   '(12)').

% (18)
cites(th13_18, th13_13,  '(13)αが整合の場合').
cites(th13_18, th13_1,   '(1.3)αが不整合の場合').

% (19) αᾱ/h=0 [矛盾原理]
cites(th13_19, th13_18,  '(18)').
cites(th13_19, th13_1,   '(1.1)(1.2)').
cites(th13_19, th13_15,  '(15)').

% (20) (α+ᾱ)/h=1 [排中原理]
cites(th13_20, ax_iii,   '(iii): α+ᾱ≡αᾱ が定理').
cites(th13_20, th13_19,  '(19)矛盾原理').
cites(th13_20, th13_12,  '(12)等値').
cites(th13_20, th13_1,   '(1.3)').

% (21)
cites(th13_21, def_x,    'X').
cites(th13_21, th13_1,   '(1)適用').
cites(th13_21, th13_15,  '(15)').

% (22)
cites(th13_22, th13_15,  '(15)').
cites(th13_22, th13_9,   '(9)').

% (23)
cites(th13_23, th13_15,  '(15)').
cites(th13_23, def_ii,   'Ⅱ確実性').
cites(th13_23, ax_iii,   '(iii)').
cites(th13_23, th13_1,   '(1.4)').

% === 第14章 ===

% (24) 加法定理
cites(th14_24, def_ix,   'Ⅸ加法定義: (α+b)代入').
cites(th14_24, ax_iii,   '(iii)によりαb̄b=bを適用').

% (24.1)-(24.3)
cites(th14_24_1, ax_iii, '(iii)').
cites(th14_24_2, th13_19,'(19)矛盾原理').
cites(th14_24_2, th13_8, '(8)').
cites(th14_24_3, th14_24,'(24)').
cites(th14_24_3, th14_24_2, '(24.2)').

% (24.6) 相互排反加法
cites(th14_24_6, def_x,   'Xを繰り返し適用').

% (25) 全確率公式
cites(th14_25, th13_9,    '(9)').
cites(th14_25, th14_24_6, '(24.6)').
cites(th14_25, def_x,     'X').
cites(th14_25, th13_8,    '(8)').

% (26)
cites(th14_26, th14_24,   '(24)加法定理').
cites(th14_26, th13_13_1, '(13.1)').
cites(th14_26, th13_8,    '(8)').

% (27)
cites(th14_27, th14_24,   '(24)と仮説').
cites(th14_27, th13_5,    '(5)').

% (28)
cites(th14_28, th14_24_3, '(24.3)').
cites(th14_28, th13_1,    '(1.1)').
cites(th14_28, th13_8,    '(8)').

% (29)
cites(th14_29, th13_1,    '(1)').
cites(th14_29, th13_15,   '(15)').
cites(th14_29, th14_27,   '(27)').

% (30) 無関連定理
cites(th14_30, th14_24_2, '(24.2)').
cites(th14_30, def_xiv,   'XIV無関連定義').

% (31) 独立性の対称性
cites(th14_31, def_x,    'X乗法定義').
cites(th14_31, ax_ivc,   '(ivc)消去律').
cites(th14_31, def_xiii, 'XIII独立性定義').
cites(th14_31, def_xiv,  'XIV無関連定義（参照）').

% (32) 逆関連
cites(th14_32, def_x,    'X').

% (36) 乗法定理
cites(th14_36, def_x,    'X乗法定義').
cites(th14_36, def_xiii, 'XIII独立性定義').

% (37) 連鎖乗法
cites(th14_37, def_x,    'Xを繰り返し適用').

% (38) 逆原理（ベイズ定理）
cites(th14_38, def_x,    'X乗法定義').

% (41) 影響係数・累積公式 (W.E.Johnson)
cites(th14_41, def_x,    'X乗法定義ベース').
cites(th14_41, def_xiii, 'XIII独立性').

% (41.1)-(41.2)
cites(th14_41_1, th14_41,  '(41)を3項に拡張').
cites(th14_41_2, th14_41,  '(41)をn項に帰納').

% (42) 影響係数の交換律
cites(th14_42, def_x,    'Xにより α/bh・b/h = b/αh・α/h').
cites(th14_42_1, th14_42, '(42)を3項に拡張').
cites(th14_42_2, th14_42, '(42)の一般化').

% (43) 分離因数規則
cites(th14_43, th14_41_2, '(41.2)の応用').
cites(th14_43, def_x,     'X乗法定義').

% (44) {αb}の積分解
cites(th14_44, def_x,    'X').
cites(th14_44, th14_41_2,'(41.2)').
cites(th14_44_1, th14_44, '(44)から独立性の導出').
cites(th14_44_1, def_xiii,'XIII独立性定義').

% (45) 反復規則
cites(th14_45, ax_ii,    '(ii)等値公理').
cites(th14_45, th13_12,  '(12)').

% (46) 累積公式
cites(th14_46, th14_38,  '(38)逆原理ベース').
cites(th14_46, th14_41_2,'(41.2)累積展開').
cites(th14_46_1, th14_46, '(46)の特殊化').
cites(th14_46_2, th14_24_7,'(24.7)相互排反完全系').
cites(th14_46_2, th14_46, '(46)から展開').

% (47) 逆公式
cites(th14_47, th14_46,  '(46)累積公式').
cites(th14_47, th14_38,  '(38)逆原理').
cites(th14_47_1, th14_47, '(47)の凝縮').

% (48) 2仮説比率形
cites(th14_48, th14_46_2, '(46.2)').

% (49) 証拠累積
cites(th14_49, th14_24_2, '(24.2)').
cites(th14_49, th14_41_2, '(41.2)影響係数').
cites(th14_49_1, th14_46_2,'(46.2)相互排反完全系').

% === 第15章 ===

% (50) 数値加算性
cites(th15_50, ax_xix,   'XIX比例公理').
cites(th15_50, ax_mae,   '(前)実数値存在公理').

% (51) αy/h の限界
cites(th15_51, th14_24_2,'(24.2)').
cites(th15_51, def_x,    'X').
cites(th15_51, th13_2,   '(2)').
cites(th15_51, th13_3,   '(3)').

% (52) 積確率の下限
cites(th15_52, th15_51,  '(51)の繰り返し適用').

% (53) 和確率の上限
cites(th15_53, th15_51,  '(51)と同様').

% (54) 差の等式
cites(th15_54, th15_51,  '(51)から直接').
cites(th15_54, th15_53,  '(53)から直接').

% (55) 消去法による近似
cites(th15_55, th13_2,   '(2)').
cites(th15_55, th13_3,   '(3)').
cites(th15_55, ax_mae,   '(前)').

% ============================================================
% 第17章 定理 (逆確率ならびに平均に関する若干の問題)
% ブールの挑戦問題 (56), n原因への一般化 (57), ラプラスの継承則 (58)
% ------------------------------------------------------------
% 原典: ケインズ『確率論』第17章第2節 (Boole の『思考の法則』第20章 問題 I–X への回答)
% ------------------------------------------------------------

defined_in(th17_56,    17, 2, theorem, 'Th.(56)',
    'ブール挑戦問題: 2原因 A1,A2 事前確率 e1,e2, 条件付 p1,p2, π = e1p1+e2p2-e1e2·z').
defined_in(th17_56_1,  17, 2, theorem, 'Th.(56.1)',
    'π の範囲: max(e1p1,e2p2)≤π≤min(1-e1(1-p1),1-e2(1-p2),e1p1+e2p2)').
defined_in(th17_56_2,  17, 2, theorem, 'Th.(56.2)',
    'e1,e2 消去: π < p1+p2 のみが得られる限界').
defined_in(th17_56_3,  17, 2, theorem, 'Th.(56.3)',
    'e2 消去: e1p1 < π < 1-e1+e1p1').
defined_in(th17_56_4,  17, 2, theorem, 'Th.(56.4)',
    'p2 消去: e1p1 < π < e1p1+e2 < e1p1+1-e1').
defined_in(th17_56_5,  17, 2, theorem, 'Th.(56.5)',
    '原因の知識が独立 (α1/α2h=α1/h): π > e1p1+e2p2-e1e2').
defined_in(th17_57,    17, 2, theorem, 'Th.(57)',
    'n 原因への一般化 (ブール問題 VI): P(E|h) = Σe_k p_k - Σα1…α_{k-1}α_k/h').
defined_in(th17_57_1,  17, 2, theorem, 'Th.(57.1)',
    '原因知識独立: P(E|h) = Σe_k p_k - Σe_k[1-Π(1-e_i)]π_k').
defined_in(th17_57_2,  17, 2, theorem, 'Th.(57.2)',
    '(57)方程式(i)(ii)より範囲: max Σe_k p_k ≤ P(E|h) ≤ min{1-e_k(1-p_k), e_k p_k/(1-e_k(1-p_k))}').
defined_in(th17_57_3,  17, 2, theorem, 'Th.(57.3)',
    '独立性下の範囲: Σe_k p_k/[1-Π(1-e_k)] ≤ P(E|h) ≤ 1-e_1(1-p_1)').
defined_in(th17_57_4,  17, 2, theorem, 'Th.(57.4)',
    '諸原因十分 (p_k=1) かつ独立: P(E|h) = 1-Π(1-e_k)').
defined_in(th17_57_5,  17, 2, theorem, 'Th.(57.5)',
    '事前確率小: P(E|h) ≈ Σe_k p_k (諸原因は排反に近づく)').
defined_in(th17_57_6,  17, 2, theorem, 'Th.(57.6)',
    '事後確率 α_r/Eh = e_r p_r/(E/h) (ブール問題 IX)').
defined_in(th17_58,    17, 2, theorem, 'Th.(58)',
    'ラプラスの継承則 (ブール問題 X): y_{n+1} = p1·p2·…·p_n, p_k連鎖 via α').
defined_in(th17_58_1,  17, 2, theorem, 'Th.(58.1)',
    'p=α: y_n=1 (不変原因のみ → 1回観測で確実性)').
defined_in(th17_58_2,  17, 2, theorem, 'Th.(58.2)',
    'y_{n+1}-y_n は正かつ n 増加で減少; y_n → 1 (α≠0)').
defined_in(th17_58_3,  17, 2, theorem, 'Th.(58.3)',
    '不変原因の事後確率 t_n → 1 as n → ∞ (α≠0)').

% ---- 定理内容 ----
theorem_proves(th17_56,
    '(56) π = e1p1 + e2p2 - e1e2·z [z=P(A1A2|Eh); ブール挑戦問題]').
theorem_proves(th17_56_1,
    '(56.1) π の範囲: max(e1p1, e2p2) ≤ π ≤ min(1-e1(1-p1), 1-e2(1-p2), e1p1+e2p2)').
theorem_proves(th17_56_2,
    '(56.2) e1, e2 消去すると唯一の限界は π < p1+p2').
theorem_proves(th17_56_3,
    '(56.3) e2 消去: e1p1 < π < 1-e1+e1p1').
theorem_proves(th17_56_4,
    '(56.4) p2 消去: e1p1 < π < e1p1+e2 < e1p1+1-e1').
theorem_proves(th17_56_5,
    '(56.5) 原因知識独立ならば π > e1p1+e2p2-e1e2').
theorem_proves(th17_57,
    '(57) n 原因一般化: P(E|h) = Σe_k p_k - Σα1…α_{k-1}α_k/h').
theorem_proves(th17_57_1,
    '(57.1) 原因知識独立: P(E|h) = Σe_k p_k - Σe_k[1-Π(1-e_i)]π_k').
theorem_proves(th17_57_2,
    '(57.2) (i)(ii) より範囲: max Σe_k p_k ≤ P(E|h) ≤ min{1-e_k(1-p_k), e_k p_k/(1-e_k(1-p_k))}').
theorem_proves(th17_57_3,
    '(57.3) 独立性下の範囲: Σe_k p_k/[1-Π(1-e_k)] ≤ P(E|h) ≤ 1-e_1(1-p_1)').
theorem_proves(th17_57_4,
    '(57.4) p_k=1 かつ独立: P(E|h) = 1-Π(1-e_k)').
theorem_proves(th17_57_5,
    '(57.5) 事前確率 e_i 小: P(E|h) ≈ Σe_k p_k').
theorem_proves(th17_57_6,
    '(57.6) 事後確率 α_r/Eh = e_r p_r/(E/h) [ブール問題 IX]').
theorem_proves(th17_58,
    '(58) ラプラス継承則 [ブール問題 X]: y_{n+1} = p1·p2·…·p_n, p_k 連鎖').
theorem_proves(th17_58_1,
    '(58.1) p=α ならば y_n=1 (不変原因下 1 回観測で確実)').
theorem_proves(th17_58_2,
    '(58.2) y_{n+1} - y_n > 0 かつ n につれて減少; y_n → 1 (α≠0)').
theorem_proves(th17_58_3,
    '(58.3) 不変原因の事後確率 t_n → 1 as n → ∞ (α≠0)').

% ---- 引用関係 (25 本) ----

% (56) ブール挑戦問題
cites(th17_56,    th14_24,    '(24)加法定理: α1/eh+α2/eh=1+α1α2/eh').
cites(th17_56,    def_x,      'X乗法定義: α_i/h=e_i, E/α_ih=p_i の連鎖展開').

% (56.1) π の範囲
cites(th17_56_1,  th14_24_2,  '(24.2) αb/h+ᾱb/h=b/h による限界導出').
cites(th17_56_1,  th13_4,     '(4) αb/h≤b/h による上界').

% (56.2)–(56.4) 変数消去による限界
cites(th17_56_2,  th17_56,    '(56) e1,e2 消去の代数変形').
cites(th17_56_3,  th17_56,    '(56) e2 消去の代数変形').
cites(th17_56_4,  th17_56,    '(56) p2 消去の代数変形').

% (56.5) 知識独立ケース
cites(th17_56_5,  th17_56,    '(56) の特殊化').
cites(th17_56_5,  def_x,      'X: z = e/α1α2h·α1/α2h·α2/h の連鎖展開').

% (57) n 原因への一般化
cites(th17_57,    th17_56,    '(56) を n 原因に一般化').
cites(th17_57,    th14_24,    '(24) 加法定理を n-ary に再利用').
cites(th17_57,    def_x,      'X: n 原因連鎖の反復乗法').

% (57.1)–(57.6) (57) の系
cites(th17_57_1,  th17_57,    '(57) 原因知識独立ケース').
cites(th17_57_2,  th17_57,    '(57) 方程式(i)(ii) より範囲').
cites(th17_57_3,  th17_57_1,  '(57.1) 独立性下の範囲').
cites(th17_57_4,  th17_57_1,  '(57.1) 特殊ケース p_k=1').
cites(th17_57_5,  th17_57,    '(57) 小事前確率近似').
cites(th17_57_6,  th17_57,    '(57) ベイズ反転').
cites(th17_57_6,  def_x,      'X: 事後確率 α_r/Eh = e_r p_r/(E/h)').

% (58) ラプラスの継承則
cites(th17_58,    th14_38,    '(38) ベイズ定理を反復適用し信念更新').
cites(th17_58,    def_x,      'X: ラプラス継承則導出の連鎖律').

% (58.1)–(58.3) (58) の系
cites(th17_58_1,  th17_58,    '(58) 特殊ケース p=α').
cites(th17_58_2,  th17_58,    '(58) 代数変形による単調増加').
cites(th17_58_3,  th17_58,    '(58) 不変原因の事後確率導出').
cites(th17_58_3,  th14_38,    '(38) 不変原因の事後に対するベイズ適用').

% ============================================================
% 照会用ルール
% ============================================================

% 定理Xが公理/定義Yを直接または間接に引用するか？
uses(Theorem, Source) :- cites(Theorem, Source, _).
uses(Theorem, Source) :-
    cites(Theorem, Intermediate, _),
    uses(Intermediate, Source).

% 公理/定義Yを直接引用する定理を全て列挙
cited_by(Source, Theorem) :- cites(Theorem, Source, _).

% 第N章の定理一覧
chapter_theorems(13, Th) :- theorem_proves(Th, _), atom_chars(Th, ['t','h','1','3'|_]).
chapter_theorems(14, Th) :- theorem_proves(Th, _), atom_chars(Th, ['t','h','1','4'|_]).
chapter_theorems(15, Th) :- theorem_proves(Th, _), atom_chars(Th, ['t','h','1','5'|_]).
chapter_theorems(17, Th) :- theorem_proves(Th, _), atom_chars(Th, ['t','h','1','7'|_]).

% 公理の引用回数
citation_count(Source, Count) :-
    findall(T, cited_by(Source, T), Ts),
    length(Ts, Count).

% EOF
