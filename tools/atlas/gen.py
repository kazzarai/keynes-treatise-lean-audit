# gen.py — 全数台帳 (docs/全数台帳/chNN.md) と座標表 (coords.json) から、章ごとの図鑑頁 (英語、1 枚の HTML) を作る。
# 行 ID ごとに 1 カード: 切り抜き画像 / 行 ID・folio・§・位置・種別 / 転記 / Lean 欄 / 照合語 / 備考。
# 集計は台帳の表から数える (手で書かない)。CSS は埋め込み、外部読み込みなし。画像パスは HTML からの相対 (img/<名>)。
# 出力は入力だけで決まる (日時などを埋めない) ので、同じ入力から再生成すれば差分は出ない。
# 列の順序は台帳の見出し行から決める (第I部の台帳は 項目ID が 2 列目、第III部以降は 7 列目)。
# 空欄の印は "—" と "–" の両方を受ける。行が 1 本もない章は 1 行の断り書きだけを出す。
# 見出しの「第N章」は英語の「Chapter <ローマ数字>」に直す。
# 頁の先頭と末尾に目次 (../index.html)・前章・次章へのナビ、集計表に「Lean 済」の 1 行、その下に絞り込みボタンを置く。
# 集計表とナビのリンクは折り返さない (集計表は .wide で包み、幅が足りなければ横スクロール)。
# ボタンは JavaScript で .card の表示を切り替える。JS が無ければボタンは隠れたままで、全カードが見える。
# ナビ・Lean 済の行・ボタンの文言は辞書 UI から引く (--lang ja で切り替え; 既定は en)。
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

# 追加した表示文言の辞書 (ナビ・Lean 済の行・絞り込みボタン)
UI = {
    "en": {
        "index": "Atlas index", "ch": "Ch. {n}", "notes": "Notes on Part III",
        "lean_th": "Formulas in Lean",
        "lean_td": "{m} / {n} formulas (&#10003;{a} &asymp;{b} &#9998;{c}), not yet {k} &mdash; {p}",
        "no_formula": "no formulae",
        "show": "Show:", "all": "All", "notyet": "not yet", "notation": "notation",
    },
    "ja": {
        "index": "図鑑の目次", "ch": "第 {n} 章", "notes": "第III部の注",
        "lean_th": "Lean 済",
        "lean_td": "{m} / {n} 式（&#10003;{a} &asymp;{b} &#9998;{c}）、未 {k} &mdash; {p}",
        "no_formula": "式なし",
        "show": "表示:", "all": "すべて", "notyet": "未", "notation": "記法",
    },
}


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


def pos_en(s):
    m = re.match(r"脚注\s*(\d+)\s*\((\d+) からの続き\)$", s)
    if m:
        return f"Footnote {m.group(1)} (continued from folio {m.group(2)})"
    m = re.match(r"脚注\s*(\d+)", s)
    return f"Footnote {m.group(1)}" if m else POS.get(s, s)


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
    t = UI[lang]
    ledger, coords, out = args[0], args[1], args[2]
    chap, title, (fa, fb, pa, pb), rows = read_ledger(ledger)
    co = {e["id"]: e for e in json.load(open(coords, encoding="utf-8"))}
    missing = [r["id"] for r in rows if r["id"] not in co]
    assert not missing, ("no crop for", missing)
    first_of = {}
    for r in rows:
        first_of.setdefault(co[r["id"]]["img"], r["id"])
    s = summary(rows)
    mk = s["marks"]
    chno = "Notes on Part III" if chap == "notes_III" else f"Chapter {int(chap[2:])}"

    o = []
    o.append("<!DOCTYPE html>")
    o.append(f'<html lang="{lang}"><head><meta charset="utf-8">')
    o.append('<meta name="viewport" content="width=device-width, initial-scale=1">')
    o.append(f"<title>Formula atlas, {chno}</title>")
    o.append(f"<style>{CSS}</style></head><body><main>")
    o.append(nav(chap, t))
    o.append(f"<h1>{html.escape(title)}</h1>")
    o.append(f'<p class="sub">J. M. Keynes, <i>A Treatise on Probability</i> (London: Macmillan, 1921), '
             f"first edition, pp. {fa}&ndash;{fb} (Cornell copy, PDF pp. {pa}&ndash;{pb}). "
             f"Formula atlas: every ledger row of the chapter beside the printed line it records.</p>")
    if not rows:
        o.append("<p>No printed formula or notation.</p>")
    else:
        done = mk["✓"] + mk["≈"] + mk["✎"]
        if s["formula"]:
            lean_td = t["lean_td"].format(m=done, n=s["formula"], a=mk["✓"], b=mk["≈"], c=mk["✎"],
                                          k=mk["未"], p=pct(done, s["formula"]))
        else:
            lean_td = html.escape(t["no_formula"])
        o.append(f'<div class="wide"><table class="sum"><tr><th>{html.escape(t["lean_th"])}</th>'
                 f'<td><b>{lean_td}</b></td></tr>')
        o.append('<tr><th>Ledger rows</th><td>' + str(s["rows"]) + "</td></tr>")
        o.append(f'<tr><th>Formulas</th><td>{s["formula"]} (display {s["f_display"]}, inline {s["f_inline"]}; '
                 f'items {s["items"]}, numbered {s["numbered"]})</td></tr>')
        o.append(f'<tr><th>Formulas by Lean status</th><td>'
                 f'<span class="mark printed">&#10003;</span>{mk["✓"]} &nbsp; '
                 f'<span class="mark equiv">&asymp;</span>{mk["≈"]} &nbsp; '
                 f'<span class="mark corrected">&#9998;</span>{mk["✎"]} &nbsp; '
                 f'<span class="mark none">&#26410;</span>{mk["未"]}</td></tr>')
        o.append(f'<tr><th>Notation</th><td>{s["notation"]} (with a Lean counterpart {s["n_lean"]})</td></tr>')
        o.append(f'<tr><th>Reference rows</th><td>{s["reference"]}</td></tr>')
        if s["bare"]:
            o.append(f'<tr><th>Bare-symbol rows (not counted)</th><td>{s["bare"]}</td></tr>')
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
        o.append(f'<p class="rules">{RULES}</p>')

    for r in rows:
        e = co[r["id"]]
        img = e["img"]
        o.append(f'<section class="card" id="{r["id"]}">')
        o.append(f'<h2>{r["id"]}</h2>')
        o.append(f'<img src="img/{html.escape(img)}" alt="{html.escape(strip_ticks(r["trans"]))}" loading="lazy">')
        if first_of[img] != r["id"]:
            o.append(f'<div class="shared">Same printed line or block as '
                     f'<a href="#{first_of[img]}">{first_of[img]}</a>.</div>')
        o.append(f'<div class="meta">folio {r["folio"]} (PDF p. {int(r["folio"]) + 20}) &middot; '
                 f'&sect;{html.escape(r["sec"])} &middot; {pos_en(r["pos"])} &middot; '
                 f'{KIND.get(r["kind"], r["kind"])} &middot; {TYPE.get(r["type"], r["type"])}</div>')
        o.append("<dl>")
        o.append(f'<dt>Transcription</dt><dd>{inline(r["trans"])}</dd>')
        m = lean_mark(r)
        if m in MARK:
            cls, label = MARK[m]
            badge = f'<span class="mark {cls}" title="{label}">{html.escape(m)}</span>'
        elif m == "R":
            badge = '<span class="mark notation" title="Reference line (not counted)">R</span>'
        elif m == "B":
            badge = '<span class="mark notation" title="Bare symbol (not counted)">B</span>'
        else:
            badge = '<span class="mark notation" title="Notation">N</span>'
        lean = r["lean"]
        if m in MARK and lean.startswith(m):
            lean = lean[len(m):].strip()
        o.append(f"<dt>Lean</dt><dd>{badge}{inline(lean)}</dd>")
        if r["repeat"] not in BLANK:
            o.append(f'<dt>Reprint of</dt><dd>{reprint_links(chap, r["repeat"])}</dd>')
        if r["source"] not in BLANK:
            o.append(f'<dt>Quoted from</dt><dd>{inline(r["source"])}</dd>')
        o.append(f'<dt>Anchor words</dt><dd>{inline(r["words"])}</dd>')
        o.append(f'<dt>Remarks</dt><dd>{inline(r["note"])}</dd>')
        o.append(f'<dt>Crop</dt><dd>folio {e["folio"]}, x {e["x0"]}&ndash;{e["x1"]}, '
                 f'y {e["y0"]}&ndash;{e["y1"]} (full-size scan pixels)</dd>')
        o.append("</dl></section>")

    o.append(nav(chap, t, end=True))
    o.append(f"<footer>Generated by tools/atlas/gen.py from the ledger {os.path.basename(ledger)} and "
             f"{os.path.basename(coords)}; crops by tools/atlas/crops.py. Remarks and Lean entries are quoted "
             f"from the ledger as written. Do not edit this file by hand.</footer>")
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
    print(f"{chap}: {s['rows']} cards, formulas {s['formula']} "
          f"(✓{mk['✓']} ≈{mk['≈']} ✎{mk['✎']} 未{mk['未']}), notation {s['notation']}")


if __name__ == "__main__":
    main()
