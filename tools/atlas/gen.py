# gen.py — 全数台帳 (docs/全数台帳/chNN.md) と座標表 (coords.json) から、章ごとの図鑑頁 (既定は英語、1 枚の HTML) を作る。
# 行 ID ごとに 1 カード: 切り抜き画像 / 行 ID・folio・§・位置・種別 / 転記 / Lean 欄 / 照合語 / 備考。
# 集計は台帳の表から数える (手で書かない)。CSS は埋め込み、外部読み込みなし。画像パスは HTML からの相対 (img/<名>)。
# 出力は入力だけで決まる (日時などを埋めない) ので、同じ入力から再生成すれば差分は出ない。
# 列の順序は台帳の見出し行から決める (第I部の台帳は 項目ID が 2 列目、第III部以降は 7 列目)。
# 空欄の印は "—" と "–" の両方を受ける。行が 1 本もない章は 1 行の断り書きだけを出す。
# 見出しの「第N章」は英語の「Chapter <ローマ数字>」に直す。
# 頁の先頭と末尾に目次 (../index.html)・前章・次章へのナビ、集計表に「Lean 済」の 1 行、その下に絞り込みボタンを置く。
# 集計表とナビのリンクは折り返さない (集計表は .wide で包み、幅が足りなければ横スクロール)。
# ボタンは JavaScript で .card の表示を切り替える。JS が無ければボタンは隠れたままで、全カードが見える。
# 表示文言は章頁・目次 (gen_index.py) とも辞書 L から引く (--lang ja で切り替え; 既定は en)。
# --lang ja: 訳書の切り抜きを並べる手元用の頁 (repo の外にだけ置く)。座標表は {"id","page"(訳書の頁),"pdf_page",
#   "y0","y1","x0","x1","img"} と任意の "note" (訳書の備考)。数え方・転記・Lean 欄は初版台帳のまま。
#   訳書で同定できなかった行は座標表に入れない。その行もカードは出し「未同定」と書き、集計表の下に行IDを並べる。
#   行が 0 の章の座標表は空の表 []。英語版は座標表に無い行があれば止まる。
#   この生成器には訳書のデータ (書誌・頁の対応・画像) を入れない。
# 使い方: python3 -I gen.py [--lang ja] <ledger.md> <coords.json> <out.html>
import html
import json
import os
import re
import sys

# 台帳の列 (既定の順序; 見出し行があればそれに従う)
COLS = ["id", "folio", "sec", "pos", "kind", "num", "item", "trans", "type",
        "source", "repeat", "lean", "words", "note"]
# 見出し行の語 (前方一致) → 列名
HEAD = [("行ID", "id"), ("項目ID", "item"), ("folio", "folio"), ("§", "sec"), ("位置", "pos"),
        ("種別", "kind"), ("番号", "num"), ("転記", "trans"), ("式/記法", "type"), ("引用元", "source"),
        ("再掲", "repeat"), ("Lean", "lean"), ("既存の Lean", "lean"), ("照合語", "words"), ("備考", "note")]
BLANK = ("—", "–", "")
# 番号欄の箇条記号 ((i.), (iv.), (a) など) は式番号ではない
ENUM = re.compile(r"^\((?:[ivx]+|[a-z])\.?\)$")

POS = {"本文": "Text", "図": "Figure", "表": "Table"}
KIND = {"表示": "Display", "行内": "Inline", "参考": "Reference", "表": "Table"}
TYPE = {"式": "Formula", "記法": "Notation", "参考": "Reference", "裸記号": "Bare symbol (not counted)"}
MARK = {"✓": ("printed", "Printed form"), "≈": ("equiv", "Equivalent form"),
        "✎": ("corrected", "Corrected form"), "未": ("none", "Not in Lean")}

RULES = (
    "Every count on this page is computed from the census ledger, which is built from the page images "
    "of the 1921 first edition only (no translation, OCR or e-text is used to count). "
    "A <b>formula</b> is an expression containing a relation sign (=, &ne;, &lt;, &gt;, &le;, &ge;, &equiv;, "
    "&sup;, &rarr; and their printed variants, including formulas inside figures, tables and footnotes, and formulas quoted from other authors); a display formula counts one per printed line, so a chain of equalities "
    "set over three lines counts three, and an inline formula counts one per expression. "
    "A compound expression without a relation sign (such as <i>a/h</i>, <i>g</i>(&phi;, <i>f</i>) or "
    "<i>x</i><sub>1</sub><i>x</i><sub>2</sub>&hellip;<i>x<sub>n</sub></i>/<i>&#289;h</i>) is counted "
    "separately as <b>notation</b>; a bare symbol, even with subscripts, primes or bars, is not counted. "
    "Footnote formulas follow the same rule, and a formula reprinted on another page is counted again. "
    "The Lean column of a formula row takes one of four values, fixed mechanically: "
    "<b>&#10003;</b> the printed relation appears as stated in a theorem (only the names of bound variables, Lean notation and the layout of subscripts may differ); "
    "<b>&asymp;</b> a theorem states an algebraically equivalent form (cleared denominators, "
    "a definition substituted, a change of variables); "
    "<b>&#9998;</b> the printed line is refuted or not derivable, and a corrected form is proved; "
    "<b>&#26410;</b> none of these (a line inside a proof, a definition only, or no counterpart)."
)

RULES_JA = (
    "この頁の数はすべて全数台帳から数えたもので、台帳は 1921 年初版の頁画像だけから作っている "
    "(訳書・OCR・電子テキストは数えるのに使わない)。訳書の切り抜きは、台帳の各行に当たる訳書の箇所を並べたもので、"
    "転記・Lean・照合語・備考の欄は初版の台帳の記載である (訳書との違いは「訳書の備考」に書く)。"
    "<b>式</b>は関係記号 (=, &ne;, &lt;, &gt;, &le;, &ge;, &equiv;, &sup;, &rarr; とその印刷上の異体) を含む表現で、"
    "図・表・脚注の中の式と、他の著者から引いた式を含む。表示式は印刷 1 行ごとに 1 と数え "
    "(3 行に組まれた等号の連鎖は 3)、行内の式は 1 式ごとに 1 と数える。"
    "関係記号を含まない複合表現 (<i>a/h</i>、<i>g</i>(&phi;, <i>f</i>)、"
    "<i>x</i><sub>1</sub><i>x</i><sub>2</sub>&hellip;<i>x<sub>n</sub></i>/<i>&#289;h</i> など) は"
    "<b>記法</b>として別に数え、添字・プライム・バーが付いても単独の記号は数えない。"
    "脚注の式も同じ規則に従い、別の頁に再掲された式はもう一度数える。"
    "式の行の Lean 欄は次の 4 値のどれかで、機械的に決める: "
    "<b>&#10003;</b> 印刷された関係が定理の文にそのまま現れる (束縛変数の名前・Lean の記法・添字の組み方だけは違ってよい); "
    "<b>&asymp;</b> 代数的に同値な形を定理が述べる (分母を払う、定義を代入する、変数を替える); "
    "<b>&#9998;</b> 印刷の行は反駁されるか導けず、修正形が証明されている; "
    "<b>&#26410;</b> そのどれでもない (証明の途中の行、定義だけ、対応なし)。"
)

CSS = """
body{background:#fff;color:#111;font-family:Georgia,'Times New Roman',serif;margin:0;padding:24px 12px}
main{max-width:900px;margin:0 auto}
h1{font-size:1.5em;margin:0 0 .2em}
.sub{color:#444;margin:0 0 1em}
table.sum{border-collapse:collapse;margin:.5em 0 1em;font-size:.95em}
table.sum th,table.sum td{border:1px solid #bbb;padding:3px 10px;text-align:left}
.wide{overflow-x:auto}
.wide table.sum{max-width:none}
table.sum td,table.sum th{white-space:nowrap}
table.sum td{font-variant-numeric:tabular-nums}
.rules{font-size:.92em;line-height:1.45;color:#222;border-left:3px solid #ccc;padding-left:12px}
.card{border:1px solid #ccc;border-radius:4px;margin:18px 0;padding:10px 12px}
.card img{display:block;width:100%;height:auto;border:1px solid #eee;margin:4px 0 8px}
.card h2{font-size:1.05em;margin:0 0 4px;font-family:Menlo,Consolas,monospace}
.meta{font-size:.9em;color:#333;margin-bottom:4px}
.shared{font-size:.82em;color:#666;margin:-4px 0 6px}
dl{display:grid;grid-template-columns:8.5em 1fr;gap:3px 10px;margin:0;font-size:.92em}
dt{color:#555}
dd{margin:0;word-break:break-word}
code{font-family:Menlo,Consolas,monospace;font-size:.95em;background:#f5f5f5;padding:0 2px}
.mark{display:inline-block;min-width:1.6em;text-align:center;border-radius:3px;padding:0 4px;margin-right:6px;font-weight:bold}
.printed{background:#e3f2e3}.equiv{background:#e6eef9}.corrected{background:#fbefd9}.none{background:#eee}
.notation{background:#f3eaf6}
footer{font-size:.85em;color:#666;margin-top:2em}
nav.nav{font-size:.92em;margin:0 0 1em}
nav.nav a{white-space:nowrap}
nav.nav.end{margin:2em 0 0}
.filter{font-size:.92em;margin:0 0 1em}
.filter button{font-family:inherit;font-size:1em;border:1px solid #bbb;background:#fff;color:#111;border-radius:3px;padding:2px 8px;margin:0 4px 4px 0;cursor:pointer}
.filter button.on{background:#333;color:#fff;border-color:#333}
"""

# 章の並び (ナビの前後と目次の順序)。Notes on Part III は第23章の後ろ。
ORDER = [f"ch{i:02d}" for i in range(1, 24)] + ["notes_III"] + [f"ch{i:02d}" for i in range(24, 34)]

# 表示文言の辞書 (章頁と目次で共用)。en と ja は同じ鍵を持つ。
#   共通: ch・notes・no_formula・missing。章頁: 見出し・集計表・ボタン・カードの欄名・フッター。
#   目次 (gen_index.py): ix_ で始まる鍵。ja は訳書の切り抜きを並べる手元用の図鑑の文言。
L = {
    "en": {
        # 共通
        "ch": "Ch. {n}", "notes": "Notes on Part III", "no_formula": "no formulae", "missing": "not built",
        # 章頁: 頭
        "index": "Atlas index", "chno": "Chapter {n}", "title": "Formula atlas, {chno}",
        "sub": "J. M. Keynes, <i>A Treatise on Probability</i> (London: Macmillan, 1921), "
               "first edition, pp. {fa}&ndash;{fb} (Cornell copy, PDF pp. {pa}&ndash;{pb}). "
               "Formula atlas: every ledger row of the chapter beside the printed line it records.",
        "no_rows": "No printed formula or notation.",
        "pages": "", "pages_none": "",
        # 章題の邦題 (英語版は使わない) と、章頁の副題に添える原題の文言
        "ch_title": {}, "sub_orig": "",
        # 章頁: 集計表
        "lean_th": "Formulas in Lean",
        "lean_td": "{m} / {n} formulas (&#10003;{a} &asymp;{b} &#9998;{c}), not yet {k} &mdash; {p}",
        "s_rows": "Ledger rows", "s_formula": "Formulas",
        "s_formula_td": "{f} (display {d}, inline {i}; items {it}, numbered {nb})",
        "s_marks": "Formulas by Lean status", "s_notation": "Notation",
        "s_notation_td": "{n} (with a Lean counterpart {k})",
        "s_ref": "Reference rows", "s_bare": "Bare-symbol rows (not counted)",
        # 章頁: 絞り込みボタン
        "show": "Show:", "all": "All", "notyet": "not yet", "notation": "notation",
        "rules": RULES,
        # 章頁: カード
        "shared": 'Same printed line or block as <a href="#{f}">{f}</a>.',
        "meta": "folio {folio} (PDF p. {pdf})",
        # 座標表に無い行 (英語版では起こらない; 鍵をそろえるためだけに置く)
        "unident_list": "Rows with no crop: {ids}", "unident": "No crop.", "meta_unident": "folio {folio}",
        "pos": POS, "kind": KIND, "type": TYPE,
        "fn": "Footnote {n}", "fn_cont": "Footnote {n} (continued from folio {f})",
        "mark": {k: v[1] for k, v in MARK.items()},
        "mark_r": "Reference line (not counted)", "mark_b": "Bare symbol (not counted)", "mark_n": "Notation",
        "d_trans": "Transcription", "d_lean": "Lean", "d_repeat": "Reprint of", "d_source": "Quoted from",
        "d_words": "Anchor words", "d_note": "Remarks", "d_tnote": "", "d_crop": "Crop",
        "crop": "folio {folio}, x {x0}&ndash;{x1}, y {y0}&ndash;{y1} (full-size scan pixels)",
        "footer": "Generated by tools/atlas/gen.py from the ledger {ledger} and {coords}; "
                  "crops by tools/atlas/crops.py. Remarks and Lean entries are quoted "
                  "from the ledger as written. Do not edit this file by hand.",
        # 目次
        "ix_title": "Formula atlas, index",
        "ix_h1": "Formula atlas: index",
        "ix_sub": "J. M. Keynes, <i>A Treatise on Probability</i> (London: Macmillan, 1921), first edition. "
                  "Every row of the formula census beside a crop of the printed line it records, one page per chapter.",
        "ix_b_lines": "Formula lines",
        "ix_d_lines": "Printed lines containing a relation sign, one per line. Notation ({nt}) is counted separately.",
        "ix_b_items": "Items",
        "ix_d_items": "A numbered theorem, definition or axiom, or a single un-numbered formula line; "
                      "the lines of a proof belong to its item.",
        "ix_b_icov": "Items stated in Lean",
        "ix_d_icov": "An item counts if at least one of its lines is &#10003;, &asymp; or &#9998;.",
        "ix_b_ncov": "Numbered items stated in Lean",
        "ix_d_ncov": "Items with a printed number or enumeration mark on one of their lines, "
                     "counted as in the previous box.",
        "ix_b_lcov": "Formula lines in a theorem statement",
        "ix_d_lcov": "&#10003; {a}, &asymp; {b}, &#9998; {c}; not yet {k}.",
        "ix_h_parts": "By part",
        "ix_h_chaps": "Chapters",
        "ix_part": "Part {p}",
        "ix_part_span": "Chapters {a}&ndash;{b}",
        "ix_part_span_notes": "Chapters {a}&ndash;{b} and the Notes on Part III",
        "ix_c_part": "Part", "ix_c_nch": "Chapters", "ix_c_lines": "Formula lines", "ix_c_items": "Items",
        "ix_c_icov": "Items in Lean", "ix_c_ncov": "Numbered items in Lean",
        "ix_c_lcov": "Lines &#10003;+&asymp;+&#9998; / not yet",
        "ix_c_nt": "Notation", "ix_c_cards": "Cards",
        "ix_c_ch": "Ch.", "ix_c_title": "Title", "ix_c_folio": "Folios",
        "ix_c_done": "In Lean (&#10003;+&asymp;+&#9998;) / lines",
        "ix_c_marks": "&#10003; / &asymp; / &#9998; / not yet",
        "ix_notes": "Notes", "ix_total": "All",
        "ix_cards_part": "{c} ({m} of {n} chapters built)",
        "ix_end_marks": "<b>&#10003;</b> the printed relation appears as stated in a theorem; "
                        "<b>&asymp;</b> a theorem states an algebraically equivalent form; "
                        "<b>&#9998;</b> the printed line is refuted or not derivable, and a corrected form is proved; "
                        "<b>not yet</b> none of these.",
        "ix_end_count": "One printed line containing a relation sign (=, &ne;, &lt;, &gt;, &le;, &ge;, &equiv;, "
                        "&sup;, &rarr;) is one formula line; a compound expression without a relation sign is counted "
                        "separately as notation, and a bare symbol is not counted. Every number on this page is "
                        "computed from the census ledger (docs/全数台帳/), never typed.",
        "ix_end_regen": "Rebuild: <code>{cmd}</code> (chapter pages: <code>tools/atlas/gen.py</code>, "
                        "see docs/atlas/README.md).",
        "ix_footer": "Generated by tools/atlas/gen_index.py from docs/全数台帳/ (chNN.md, notes_III.md, summary.csv) "
                     "and the chapter pages. Do not edit this file by hand.",
    },
    "ja": {
        # 共通
        "ch": "第 {n} 章", "notes": "第III部の注", "no_formula": "式なし", "missing": "未作成",
        # 章頁: 頭 ({p0}–{p1} は座標表の訳書の頁から取る。座標表が空なら pages_none)
        "index": "図鑑の目次", "chno": "第 {n} 章", "title": "数式図鑑 (訳書) {chno}",
        "sub": "{pages} (訳書の書誌は同じディレクトリの README.md)。"
               "照合の基準は初版 J. M. Keynes, <i>A Treatise on Probability</i> (London: Macmillan, 1921) "
               "pp. {fa}&ndash;{fb} (Cornell 本、PDF pp. {pa}&ndash;{pb})。"
               "台帳の各行に、それに当たる訳書の箇所を並べる。手元での照合用で、公開しない。",
        "no_rows": "印刷された式・記法はない。",
        "pages": "訳書 pp. {p0}&ndash;{p1} の切り抜き", "pages_none": "訳書の該当章 (切り抜きなし)",
        # 章題の邦題 (訳書の章題ではなく自前の短い題; 鍵は ORDER の章名) と、副題に添える原題
        "ch_title": {
            "ch01": "確率とは何か", "ch02": "確率と知識", "ch03": "確率の測定", "ch04": "無差別原理",
            "ch05": "確率を決める他の方法", "ch06": "推論の重み", "ch07": "歴史的回顧", "ch08": "頻度説",
            "ch09": "第I部の要約", "ch10": "序論", "ch11": "群の理論", "ch12": "定義と公理",
            "ch13": "必然的推論の基本定理", "ch14": "蓋然的推論の基本定理", "ch15": "数値測定と近似",
            "ch16": "第14章の定理の考察・証言", "ch17": "逆確率・平均", "ch18": "第III部 序論",
            "ch19": "類推による議論", "ch20": "純粋帰納", "ch21": "帰納的議論 続", "ch22": "方法の正当化",
            "ch23": "帰納の歴史", "notes_III": "第III部への注", "ch24": "客観的偶然と無作為",
            "ch25": "偶然をめぐる諸問題", "ch26": "確率の行為への適用", "ch27": "統計的推論の本性",
            "ch28": "大数の法則", "ch29": "事前確率による頻度予測", "ch30": "Laplace の方法",
            "ch31": "Bernoulli の定理の逆", "ch32": "Lexis の方法", "ch33": "構成的理論の素描",
        },
        "sub_orig": "原題: <i>{orig}</i>。",
        # 章頁: 集計表
        "lean_th": "Lean 済",
        "lean_td": "{m} / {n} 式 (&#10003;{a} &asymp;{b} &#9998;{c})、未 {k} &mdash; {p}",
        "s_rows": "台帳の行", "s_formula": "式",
        "s_formula_td": "{f} (表示 {d}、行内 {i}; 項目 {it}、番号付き {nb})",
        "s_marks": "式の Lean 状況", "s_notation": "記法",
        "s_notation_td": "{n} (Lean 対応あり {k})",
        "s_ref": "参考行", "s_bare": "裸記号の行 (数えない)",
        # 章頁: 絞り込みボタン
        "show": "表示:", "all": "すべて", "notyet": "未", "notation": "記法",
        "rules": RULES_JA,
        # 章頁: カード (位置・種別は台帳の語のまま、脚注の番号は初版のもの)
        "shared": '<a href="#{f}">{f}</a> と同じ切り抜き (訳書の同じ行またはブロック)。',
        "meta": "訳書 p.{page} (初版 folio {folio})",
        # 訳書で同定できなかった行 (座標表に無い行)
        "unident_list": "訳書で同定できなかった行 (切り抜きなし): {ids}",
        "unident": "訳書で未同定 (切り抜きなし)。", "meta_unident": "訳書 未同定 (初版 folio {folio})",
        "pos": {}, "kind": {}, "type": {"裸記号": "裸記号 (数えない)"},
        "fn": "{s} (初版の番号)", "fn_cont": "{s} (初版の番号)",
        "mark": {"✓": "印刷どおり", "≈": "同値な形", "✎": "修正形", "未": "Lean になし"},
        "mark_r": "参考行 (数えない)", "mark_b": "裸記号 (数えない)", "mark_n": "記法",
        "d_trans": "転記 (初版)", "d_lean": "Lean", "d_repeat": "再掲元", "d_source": "引用元",
        "d_words": "照合語 (初版)", "d_note": "備考 (初版台帳)", "d_tnote": "訳書の備考", "d_crop": "切り抜き",
        "crop": "訳書 p.{page} (PDF p.{pdf_page})、x {x0}&ndash;{x1}、y {y0}&ndash;{y1} (原寸スキャンの画素)",
        "footer": "tools/atlas/gen.py --lang ja が台帳 {ledger} と {coords} から生成した。"
                  "切り抜きは tools/atlas/crops.py。備考と Lean 欄は初版台帳の記載をそのまま引く。手で編集しない。",
        # 目次
        "ix_title": "数式図鑑 (訳書) 目次",
        "ix_h1": "数式図鑑 (訳書) 目次",
        "ix_sub": "全数台帳の行ごとに、それに当たる訳書の箇所の切り抜きを並べる (章ごとに 1 頁、訳書の書誌は同じ"
                  "ディレクトリの README.md)。数と照合の基準は初版 J. M. Keynes, <i>A Treatise on Probability</i> "
                  "(London: Macmillan, 1921)。手元での照合用で、公開しない。",
        "ix_b_lines": "式 (行)",
        "ix_d_lines": "関係記号を含む印刷行、1 行 = 1 本。記法 ({nt}) は別勘定。",
        "ix_b_items": "項目",
        "ix_d_items": "番号付きの定理・定義・公理、または番号のない式 1 行。証明の行はその項目に属する。",
        "ix_b_icov": "Lean で定理になった項目",
        "ix_d_icov": "項目の行のどれかが &#10003;・&asymp;・&#9998; なら数える。",
        "ix_b_ncov": "番号付き項目の対応",
        "ix_d_ncov": "行のどれかに印刷の番号・箇条記号がある項目。数え方は左の枠と同じ。",
        "ix_b_lcov": "定理文に現れる行",
        "ix_d_lcov": "&#10003; {a}・&asymp; {b}・&#9998; {c}、未 {k}。",
        "ix_h_parts": "部ごと",
        "ix_h_chaps": "章の一覧",
        "ix_part": "第{p}部",
        "ix_part_span": "第 {a}〜{b} 章",
        "ix_part_span_notes": "第 {a}〜{b} 章と第III部の注",
        "ix_c_part": "部", "ix_c_nch": "章", "ix_c_lines": "式 (行)", "ix_c_items": "項目",
        "ix_c_icov": "項目の Lean 対応", "ix_c_ncov": "番号付き項目の対応",
        "ix_c_lcov": "行 &#10003;+&asymp;+&#9998; / 未",
        "ix_c_nt": "記法", "ix_c_cards": "カード",
        "ix_c_ch": "章", "ix_c_title": "題", "ix_c_folio": "folio",
        "ix_c_done": "Lean 済 (&#10003;+&asymp;+&#9998;) / 式",
        "ix_c_marks": "&#10003; / &asymp; / &#9998; / 未",
        "ix_notes": "注", "ix_total": "合計",
        "ix_cards_part": "{c} ({n} 章中 {m} 章作成)",
        "ix_end_marks": "<b>&#10003;</b> 印刷の関係がそのまま定理文に現れる。"
                        "<b>&asymp;</b> 代数的に同値な形を定理が述べる。"
                        "<b>&#9998;</b> 印刷の行は反証または導出不能で、訂正形を証明した。"
                        "<b>未</b> そのいずれでもない。",
        "ix_end_count": "関係記号 (=, &ne;, &lt;, &gt;, &le;, &ge;, &equiv;, &sup;, &rarr;) を含む印刷行 1 行 = 式 1 本。"
                        "関係記号のない複合の表現は記法として別に数え、裸の記号は数えない。"
                        "この頁の数はすべて全数台帳 (docs/全数台帳/) から数えたもので、手で書いていない。",
        "ix_end_regen": "再生成: 目次は同じディレクトリの <code>build_index.sh</code> (章が増えたら打ち直す)、"
                        "章頁は <code>tools/atlas/gen.py --lang ja</code> (手順は同じディレクトリの README.md)。",
        "ix_footer": "tools/atlas/gen_index.py が docs/全数台帳/ (chNN.md・notes_III.md・summary.csv) と各章頁から生成。"
                     "手で編集しない。",
    },
}
assert L["en"].keys() == L["ja"].keys(), set(L["en"]) ^ set(L["ja"])
assert set(L["ja"]["ch_title"]) == set(ORDER), set(L["ja"]["ch_title"]) ^ set(ORDER)


def pct(m, n):
    return f"{100 * m / n:.1f}%" if n else "&mdash;"


def nav_label(chap, t):
    return t["notes"] if chap == "notes_III" else t["ch"].format(n=int(chap[2:]))


def nav(chap, t, end=False):
    # 目次・前章・次章へのリンク 1 行 (端の章は片側だけ)
    i = ORDER.index(chap)
    parts = [f'<a href="../index.html">&larr; {html.escape(t["index"])}</a>']
    if i > 0:
        parts.append(f'<a href="../{ORDER[i - 1]}/index.html">&larr; {html.escape(nav_label(ORDER[i - 1], t))}</a>')
    if i + 1 < len(ORDER):
        parts.append(f'<a href="../{ORDER[i + 1]}/index.html">{html.escape(nav_label(ORDER[i + 1], t))} &rarr;</a>')
    return f'<nav class="nav{" end" if end else ""}">' + " | ".join(parts) + "</nav>"


def category(r):
    # 絞り込みの分類: 式は Lean 欄の印、記法は notation、参考・裸記号は All のときだけ見える
    if r["type"] == "式":
        return MARK[lean_mark(r)][0]
    return "notation" if r["type"] == "記法" else ""


def roman(n):
    out = ""
    for v, s in ((40, "XL"), (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I")):
        while n >= v:
            out += s
            n -= v
    return out


def title_en(title):
    # 台帳の見出しは部ごとに書式が違う (「第2章 Title」「第 X 章 Title」「Chapter XX "Title"」「Chapter XXIX. Title」)。
    # 図鑑では一律に「Chapter <ローマ数字>. Title」にそろえる。Notes on Part III はそのまま。
    title = title.strip()
    m = re.match(r"第\s*(\d+)\s*章\s+(.*)$", title)
    if m:
        return f"Chapter {roman(int(m.group(1)))}. {m.group(2).strip()}"
    m = re.match(r"第\s*([IVX]+)\s*章\s+(.*)$", title)
    if m:
        return f"Chapter {m.group(1)}. {m.group(2).strip()}"
    m = re.match(r'Chapter\s+([IVX]+)\.?\s+"?(.*?)"?\s*(\(Part [IVX]+\))?$', title)
    if m:
        tail = f" {m.group(3)}" if m.group(3) else ""
        return f"Chapter {m.group(1)}. {m.group(2).strip()}{tail}"
    m = re.match(r'"?(Notes on Part III)"?\s*(.*)$', title)
    if m:
        return f"{m.group(1)}: {m.group(2).strip()}" if m.group(2) else m.group(1)
    return title


def head_cols(cells):
    # 見出し行のセルを列名に置き換える (長い語を先に照合)
    out = []
    for c in cells:
        key = max((k for k in HEAD if c.startswith(k[0])), key=lambda k: len(k[0]))
        out.append(key[1])
    return out


def read_ledger(path):
    text = open(path, encoding="utf-8").read()
    lines = text.splitlines()
    m = re.match(r"#\s*\S+\s+(ch\d+|notes_III)\s+—\s+(.*)$", lines[0])
    chap, title = m.group(1), title_en(m.group(2).strip())
    fm = re.search(r"^- folio (\d+)–(\d+) \(PDF 頁 (\d+)–(\d+)\)", text, re.M)
    if not fm:
        fm = re.search(r"^- folio: (\d+)–(\d+)\b.*? / PDF 頁: (\d+)–(\d+)", text, re.M)
    if not fm:
        fm = re.search(r"^- folio 範囲: \*\*(\d+)–(\d+)\*\* \(PDF 頁 (\d+)–(\d+)、", text, re.M)
    assert fm, ("folio header not found", path)
    cols = COLS
    rows = []
    for ln in lines:
        if ln.startswith("| 行ID |"):
            cols = head_cols([c.strip() for c in ln.strip().strip("|").split("|")])
            assert sorted(cols) == sorted(COLS), cols
            continue
        if not ln.startswith(f"| {'notes' if chap == 'notes_III' else chap}-"):
            continue
        cells = [c.strip() for c in ln.strip().strip("|").split("|")]
        assert len(cells) == len(cols), (ln[:40], len(cells))
        rows.append(dict(zip(cols, cells)))
    return chap, title, fm.groups(), rows


def inline(s):
    # 台帳セルの `…` を <code> に、他は HTML エスケープ
    parts = s.split("`")
    out = []
    for i, p in enumerate(parts):
        out.append(f"<code>{html.escape(p)}</code>" if i % 2 else html.escape(p))
    return "".join(out)


def strip_ticks(s):
    return s[1:-1] if s.startswith("`") and s.endswith("`") else s


def pos_label(s, t):
    # 位置欄: 脚注は辞書の書式 (ja は台帳の語に「初版の番号」を添える)、他は辞書 pos で置き換え
    m = re.match(r"脚注\s*(\d+)\s*\((\d+) からの続き\)$", s)
    if m:
        return t["fn_cont"].format(n=m.group(1), f=m.group(2), s=s)
    m = re.match(r"脚注\s*(\d+)", s)
    return t["fn"].format(n=m.group(1), s=s) if m else t["pos"].get(s, s)


def reprint_links(chap, s):
    # 再掲欄: 先頭の行ID (章名なしの「001」や「ch05-005 (弱形)」の注記付きも受ける) をリンクに、残りは文字のまま
    prefix = "notes" if chap == "notes_III" else chap
    def one(m):
        tok = m.group(0)
        full = tok if "-" in tok else f"{prefix}-{tok}"
        c = full.split("-")[0]
        href = f"#{full}" if c == prefix else f"../{'notes_III' if c == 'notes' else c}/index.html#{full}"
        return f'<a href="{href}">{html.escape(full)}</a>'
    return re.sub(r"(?:ch\d+|notes)-\d{3}[a-z]?|(?<![\w-])\d{3}(?![\w-])", one, html.escape(s))


def lean_mark(r):
    # 式行は Lean 欄の先頭の記号 (✓ ≈ ✎ 未)、記法行は対応の有無
    if r["type"] == "式":
        c = r["lean"][:1]
        assert c in MARK, (r["id"], r["lean"][:10])
        return c
    if r["type"] == "参考":
        return "R"
    if r["type"] == "裸記号":
        return "B"
    return "未" if r["lean"].startswith("未") or not r["lean"] else "N"


def summary(rows):
    f = [r for r in rows if r["type"] == "式"]
    n = [r for r in rows if r["type"] == "記法"]
    ref = [r for r in rows if r["type"] == "参考"]
    marks = {k: sum(1 for r in f if lean_mark(r) == k) for k in MARK}
    return {
        "rows": len(rows), "formula": len(f), "notation": len(n), "reference": len(ref),
        "f_display": sum(1 for r in f if r["kind"] == "表示"),
        "f_inline": sum(1 for r in f if r["kind"] == "行内"),
        "items": len({r["item"] for r in f}),
        "numbered": sum(1 for r in f if r["num"] not in BLANK and not ENUM.match(r["num"])),
        "bare": sum(1 for r in rows if r["type"] == "裸記号"),
        "marks": marks,
        "n_lean": sum(1 for r in n if lean_mark(r) == "N"),
    }


def main():
    args = sys.argv[1:]
    lang = "en"
    if "--lang" in args:
        i = args.index("--lang")
        lang = args[i + 1]
        del args[i:i + 2]
    t = L[lang]
    ja = lang == "ja"  # 訳書の切り抜きの頁 (座標表に訳書の頁 page・pdf_page・note がある)
    ledger, coords, out = args[0], args[1], args[2]
    chap, title, (fa, fb, pa, pb), rows = read_ledger(ledger)
    co = {e["id"]: e for e in json.load(open(coords, encoding="utf-8"))}
    # 座標表に無い行: 訳書版では「未同定」のカードにする、英語版では止まる
    missing = [r["id"] for r in rows if r["id"] not in co]
    assert ja or not missing, ("no crop for", missing)
    first_of = {}
    for r in rows:
        if r["id"] in co:
            first_of.setdefault(co[r["id"]]["img"], r["id"])
    s = summary(rows)
    mk = s["marks"]
    chno = t["notes"] if chap == "notes_III" else t["chno"].format(n=int(chap[2:]))
    sub_orig = ""
    if ja:
        # 見出しと <title> は「第 N 章　邦題」(第III部の注は邦題だけ)。原題は副題の頭に添える
        sub_orig = t["sub_orig"].format(orig=html.escape(title)) + " "
        jt = t["ch_title"][chap]
        title = jt if chap == "notes_III" else chno + "　" + jt
        chno = title
    pages = sorted({e["page"] for e in co.values()}) if ja else []
    span = t["pages"].format(p0=pages[0], p1=pages[-1]) if pages else t["pages_none"]

    o = []
    o.append("<!DOCTYPE html>")
    o.append(f'<html lang="{lang}"><head><meta charset="utf-8">')
    o.append('<meta name="viewport" content="width=device-width, initial-scale=1">')
    o.append(f"<title>{t['title'].format(chno=chno)}</title>")
    o.append(f"<style>{CSS}</style></head><body><main>")
    o.append(nav(chap, t))
    o.append(f"<h1>{html.escape(title)}</h1>")
    o.append(f'<p class="sub">{sub_orig}{t["sub"].format(fa=fa, fb=fb, pa=pa, pb=pb, pages=span)}</p>')
    if not rows:
        o.append(f"<p>{t['no_rows']}</p>")
    else:
        done = mk["✓"] + mk["≈"] + mk["✎"]
        if s["formula"]:
            lean_td = t["lean_td"].format(m=done, n=s["formula"], a=mk["✓"], b=mk["≈"], c=mk["✎"],
                                          k=mk["未"], p=pct(done, s["formula"]))
        else:
            lean_td = html.escape(t["no_formula"])
        o.append(f'<div class="wide"><table class="sum"><tr><th>{html.escape(t["lean_th"])}</th>'
                 f'<td><b>{lean_td}</b></td></tr>')
        o.append(f'<tr><th>{t["s_rows"]}</th><td>' + str(s["rows"]) + "</td></tr>")
        o.append(f'<tr><th>{t["s_formula"]}</th><td>'
                 + t["s_formula_td"].format(f=s["formula"], d=s["f_display"], i=s["f_inline"],
                                            it=s["items"], nb=s["numbered"]) + "</td></tr>")
        o.append(f'<tr><th>{t["s_marks"]}</th><td>'
                 f'<span class="mark printed">&#10003;</span>{mk["✓"]} &nbsp; '
                 f'<span class="mark equiv">&asymp;</span>{mk["≈"]} &nbsp; '
                 f'<span class="mark corrected">&#9998;</span>{mk["✎"]} &nbsp; '
                 f'<span class="mark none">&#26410;</span>{mk["未"]}</td></tr>')
        o.append(f'<tr><th>{t["s_notation"]}</th><td>'
                 + t["s_notation_td"].format(n=s["notation"], k=s["n_lean"]) + "</td></tr>")
        o.append(f'<tr><th>{t["s_ref"]}</th><td>{s["reference"]}</td></tr>')
        if s["bare"]:
            o.append(f'<tr><th>{t["s_bare"]}</th><td>{s["bare"]}</td></tr>')
        o.append("</table></div>")
        cats = [category(r) for r in rows]
        btns = [("all", t["all"], len(rows)), ("printed", "&#10003;", cats.count("printed")),
                ("equiv", "&asymp;", cats.count("equiv")), ("corrected", "&#9998;", cats.count("corrected")),
                ("none", html.escape(t["notyet"]), cats.count("none")),
                ("notation", html.escape(t["notation"]), cats.count("notation"))]
        on = ' class="on"'
        o.append(f'<div class="filter" hidden>{html.escape(t["show"])} '
                 + "".join(f'<button type="button" data-k="{k}"{on if k == "all" else ""}>'
                           f"{lab} ({n})</button>" for k, lab, n in btns) + "</div>")
        o.append(f'<p class="rules">{t["rules"]}</p>')
    if missing:
        o.append(f'<p class="rules">{t["unident_list"].format(ids=inline(", ".join(missing)))}</p>')

    for r in rows:
        e = co.get(r["id"])
        o.append(f'<section class="card" id="{r["id"]}">')
        o.append(f'<h2>{r["id"]}</h2>')
        if e:
            img = e["img"]
            o.append(f'<img src="img/{html.escape(img)}" alt="{html.escape(strip_ticks(r["trans"]))}" loading="lazy">')
            if first_of[img] != r["id"]:
                o.append(f'<div class="shared">{t["shared"].format(f=first_of[img])}</div>')
            lead = t["meta"].format(folio=r["folio"], pdf=int(r["folio"]) + 20, page=e.get("page"))
        else:
            o.append(f'<div class="shared">{t["unident"]}</div>')
            lead = t["meta_unident"].format(folio=r["folio"])
        pos, kind, typ = pos_label(r["pos"], t), t["kind"].get(r["kind"], r["kind"]), t["type"].get(r["type"], r["type"])
        if ja:
            # 訳書の頁は台帳の語をそのまま出すのでエスケープする (英語版は従来どおり)
            pos, kind, typ = html.escape(pos), html.escape(kind), html.escape(typ)
        o.append(f'<div class="meta">{lead} &middot; '
                 f'&sect;{html.escape(r["sec"])} &middot; {pos} &middot; {kind} &middot; {typ}</div>')
        o.append("<dl>")
        o.append(f'<dt>{t["d_trans"]}</dt><dd>{inline(r["trans"])}</dd>')
        m = lean_mark(r)
        if m in MARK:
            badge = f'<span class="mark {MARK[m][0]}" title="{t["mark"][m]}">{html.escape(m)}</span>'
        elif m == "R":
            badge = f'<span class="mark notation" title="{t["mark_r"]}">R</span>'
        elif m == "B":
            badge = f'<span class="mark notation" title="{t["mark_b"]}">B</span>'
        else:
            badge = f'<span class="mark notation" title="{t["mark_n"]}">N</span>'
        lean = r["lean"]
        if m in MARK and lean.startswith(m):
            lean = lean[len(m):].strip()
        o.append(f'<dt>{t["d_lean"]}</dt><dd>{badge}{inline(lean)}</dd>')
        if r["repeat"] not in BLANK:
            o.append(f'<dt>{t["d_repeat"]}</dt><dd>{reprint_links(chap, r["repeat"])}</dd>')
        if r["source"] not in BLANK:
            o.append(f'<dt>{t["d_source"]}</dt><dd>{inline(r["source"])}</dd>')
        o.append(f'<dt>{t["d_words"]}</dt><dd>{inline(r["words"])}</dd>')
        o.append(f'<dt>{t["d_note"]}</dt><dd>{inline(r["note"])}</dd>')
        if ja and e and e.get("note"):
            o.append(f'<dt>{t["d_tnote"]}</dt><dd>{inline(e["note"])}</dd>')
        if e:
            o.append(f'<dt>{t["d_crop"]}</dt><dd>{t["crop"].format(**e)}</dd>')
        o.append("</dl></section>")

    o.append(nav(chap, t, end=True))
    o.append(f"<footer>{t['footer'].format(ledger=os.path.basename(ledger), coords=os.path.basename(coords))}"
             "</footer>")
    if rows:
        # 絞り込み: 行ID → 分類の表を埋め、押したボタンの分類のカードだけを見せる
        kmap = json.dumps({r["id"]: c for r, c in zip(rows, cats)}, separators=(",", ":"))
        o.append("<script>(function(){")
        o.append(f"var K={kmap};")
        o.append("var f=document.querySelector('.filter'),bs=f.querySelectorAll('button'),"
                 "cs=document.querySelectorAll('section.card');")
        o.append("function show(k){")
        o.append(" for(var i=0;i<cs.length;i++)cs[i].style.display=(k==='all'||K[cs[i].id]===k)?'':'none';")
        o.append(" for(var j=0;j<bs.length;j++)bs[j].className=(bs[j].getAttribute('data-k')===k)?'on':'';}")
        o.append("for(var j=0;j<bs.length;j++)bs[j].onclick=function(){show(this.getAttribute('data-k'));};")
        o.append("f.hidden=false;})();</script>")
    o.append("</main></body></html>")
    open(out, "w", encoding="utf-8").write("\n".join(o) + "\n")
    print(f"{chap}{' (ja)' if ja else ''}: {s['rows']} cards, formulas {s['formula']} "
          f"(✓{mk['✓']} ≈{mk['≈']} ✎{mk['✎']} 未{mk['未']}), notation {s['notation']}"
          + (f", translator notes {sum(1 for r in rows if co.get(r['id'], {}).get('note'))}, "
             f"unidentified {len(missing)}" if ja else ""))


if __name__ == "__main__":
    main()
