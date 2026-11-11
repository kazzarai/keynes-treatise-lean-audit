# others/ — 他の著者の原著の式 (比較用、台帳に対応する行なし)

**このディレクトリのファイルは比較用で、docs/全数台帳 に対応する行は無い。判定数・ファイル数
(tools/check_all.sh の [3]、logs/progress.json) にも数えない。**

## 線引き (2026-11-08 の裁定、B47)

- 台帳 docs/全数台帳 と判定数は『確率論』(1921) の印刷行だけ。他の著者の原著の式は台帳に入れない。
- Keynes が本文・脚注で引いた他の著者の式 (台帳の「他の著者の式」、例: ch17-002 Boole の方程式、
  ch17-005 Wilbraham) は従来どおり台帳側 (phases/) で扱う。原著そのものの式と、その比較だけを
  others/ に置く。
- phases/ は others/ を import しない (check_all の [1i] で検査)。phases/ と others/ を結ぶのは
  比較ファイル (例: boole/compare_keynes_56.lean) だけで、比較ファイルが phases/ の定理を import する。
- 他の著者の前提は、その著者の名前空間の名前付き公理 (例: `Boole.ax_*`) として置く。
  Keynes 側の定理の `#print axioms` にそれらが出ないことを比較ファイルの中で検査する。

## check_all での扱い

- 引数なしの check_all は phases/*.lean に続けて others/**/*.lean を検査する ([1o] コンパイル、
  [2o] sorryAx)。[3] の判定数・ファイル数は phases/ だけから数え、others/ の
  `#print axioms` の行は数えない。
- 比較ファイルの `import phases.X` / `import others.X.Y` は、check_all が一時ディレクトリに
  `lake env lean -R . -o` で olean を作り、LEAN_PATH に足してから解決する
  (lakefile は変えていない)。
- 単体の検査: `bash tools/check_all.sh others/boole/compare_keynes_56.lean`
  (phases/ のファイルを渡さないときは logs/progress.json を書き換えない)。

## 内容

| ファイル | 名前空間 | 中身 |
|---|---|---|
| boole/boole_1854.lean | `Boole` | Boole の挑戦問題 (1851) の方程式・限界・解 (存在と一意性)、構成要素の理想的条件と積の形、Keynes の批判「do not reduce」の算術形。import Mathlib のみ。 |
| boole/compare_keynes_56.lean | `Boole` | phase16a の (56)–(56.5) と比べる。理想的条件から Boole の解 (KeynesI 担体)、比較定理 1 (Boole の解は Keynes の区間に入る)、比較定理 2 (Keynes の公理 13 本を満たす模型で Boole の方程式が偽)、Wilbraham の形、外延 (真偽) 担体では data を置けないこと。 |
| gt12/interval_decision.lean | `GT12` | Keynes の式ではなく、(56.1) の区間の上に報告者が置いた決定モデル (B53)。Invest u k := k ⩽ u。内側 (k ⩽ L で Invest、U < k で ¬Invest)、沈黙 (L < k ⩽ U で公理 13 本と data を満たす模型が両方の決定を与える、両端の実現)、慣習 (u を一意に定める追加前提: Boole の理想的条件・排反・独立 + 値; 無矛盾・公理から出ない・同じ data に違う u)、血気 (u_α = L + α(U − L)、閾値 (k − L)/(U − L)、α は data と公理から定まらない)、数値例 (c = p = 1/2 で Boole の根 (3 − √2)/4)。帰属は区間の読み Brady (2004)、α 規準 Hurwicz (1951)、血気の読み 新井 (2015)。 |

## 典拠と未照合

Boole・Cayley・Wilbraham の原著は materials/原著/ に未入手。Boole の方程式と限界、
Wilbraham の形は Keynes の転記 (folio 187 本文と脚注 3) から取った (未照合)。
Cayley の解は Keynes の本文・脚注に式が無く、原著も無いので置いていない。
入手予定 (公開域): Boole (1851) Camb. & Dublin Math. J. 6, p. 286; Boole (1853) Phil. Mag.
4th ser. 7, 29–32; Cayley (1853) Phil. Mag. 6, p. 259; Wilbraham (1854) Phil. Mag. 7, 465–476;
Boole (1854) Phil. Mag. 8, 91–98 と 431–444; Boole, *Laws of Thought* (1854) pp. 321–326。
