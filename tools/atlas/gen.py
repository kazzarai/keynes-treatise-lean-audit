# gen.py — 全数台帳 (docs/全数台帳/chNN.md) と座標表 (coords.json) から、章ごとの図鑑頁 (英語、1 枚の HTML) を作る。
# 行 ID ごとに 1 カード: 切り抜き画像 / 行 ID・folio・§・位置・種別 / 転記 / Lean 欄 / 照合語 / 備考。
# 集計は台帳の表から数える (手で書かない)。CSS は埋め込み、外部読み込みなし。画像パスは HTML からの相対 (img/<名>)。
# 出力は入力だけで決まる (日時などを埋めない) ので、同じ入力から再生成すれば差分は出ない。
# 使い方: python3 -I gen.py <ledger.md> <coords.json> <out.html>
import html
import json
import os
import re
import sys

# 台帳の列 (順序どおり)
COLS = ["id", "folio", "sec", "pos", "kind", "num", "item", "trans", "type",
        "source", "repeat", "lean", "words", "note"]

POS = {"本文": "Text", "図": "Figure", "表": "Table"}
KIND = {"表示": "Display", "行内": "Inline", "参考": "Reference"}
TYPE = {"式": "Formula", "記法": "Notation", "参考": "Reference"}
MARK = {"✓": ("printed", "Printed form"), "≈": ("equiv", "Equivalent form"),
        "✎": ("corrected", "Corrected form"), "未": ("none", "Not in Lean")}

RULES = (
    "Every count on this page is computed from the census ledger, which is built from the page images "
    "of the 1921 first edition only (no translation, OCR or e-text is used to count). "
    "A <b>formula</b> is an expression containing a relation sign (=, &ne;, &lt;, &gt;, &le;, &ge;, &equiv; "
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
"""


def read_ledger(path):
    text = open(path, encoding="utf-8").read()
    lines = text.splitlines()
    m = re.match(r"#\s*\S+\s+(ch\d+|notes_III)\s+—\s+(.*)$", lines[0])
    chap, title = m.group(1), m.group(2).strip()
    fm = re.search(r"^- folio (\d+)–(\d+) \(PDF 頁 (\d+)–(\d+)\)", text, re.M)
    rows = []
    for ln in lines:
        if not ln.startswith(f"| {'notes' if chap == 'notes_III' else chap}-"):
            continue
        cells = [c.strip() for c in ln.strip().strip("|").split("|")]
        assert len(cells) == len(COLS), (ln[:40], len(cells))
        rows.append(dict(zip(COLS, cells)))
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
    m = re.match(r"脚注\s*(\d+)", s)
    return f"Footnote {m.group(1)}" if m else POS.get(s, s)


def lean_mark(r):
    # 式行は Lean 欄の先頭の記号 (✓ ≈ ✎ 未)、記法行は対応の有無
    if r["type"] == "式":
        c = r["lean"][:1]
        assert c in MARK, (r["id"], r["lean"][:10])
        return c
    if r["type"] == "参考":
        return "R"
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
        "numbered": sum(1 for r in f if r["num"] not in ("—", "")),
        "marks": marks,
        "n_lean": sum(1 for r in n if lean_mark(r) == "N"),
    }


def main():
    ledger, coords, out = sys.argv[1], sys.argv[2], sys.argv[3]
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
    o.append('<html lang="en"><head><meta charset="utf-8">')
    o.append('<meta name="viewport" content="width=device-width, initial-scale=1">')
    o.append(f"<title>Formula atlas, {chno}</title>")
    o.append(f"<style>{CSS}</style></head><body><main>")
    o.append(f"<h1>{html.escape(title)}</h1>")
    o.append(f'<p class="sub">J. M. Keynes, <i>A Treatise on Probability</i> (London: Macmillan, 1921), '
             f"first edition, pp. {fa}&ndash;{fb} (Cornell copy, PDF pp. {pa}&ndash;{pb}). "
             f"Formula atlas: every ledger row of the chapter beside the printed line it records.</p>")
    o.append('<table class="sum"><tr><th>Ledger rows</th><td>' + str(s["rows"]) + "</td></tr>")
    o.append(f'<tr><th>Formulas</th><td>{s["formula"]} (display {s["f_display"]}, inline {s["f_inline"]}; '
             f'items {s["items"]}, numbered {s["numbered"]})</td></tr>')
    o.append(f'<tr><th>Formulas by Lean status</th><td>'
             f'<span class="mark printed">&#10003;</span>{mk["✓"]} &nbsp; '
             f'<span class="mark equiv">&asymp;</span>{mk["≈"]} &nbsp; '
             f'<span class="mark corrected">&#9998;</span>{mk["✎"]} &nbsp; '
             f'<span class="mark none">&#26410;</span>{mk["未"]}</td></tr>')
    o.append(f'<tr><th>Notation</th><td>{s["notation"]} (with a Lean counterpart {s["n_lean"]})</td></tr>')
    o.append(f'<tr><th>Reference rows</th><td>{s["reference"]}</td></tr></table>')
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
        else:
            badge = '<span class="mark notation" title="Notation">N</span>'
        lean = r["lean"]
        if m in MARK and lean.startswith(m):
            lean = lean[len(m):].strip()
        o.append(f"<dt>Lean</dt><dd>{badge}{inline(lean)}</dd>")
        if r["repeat"] not in ("—", ""):
            o.append(f'<dt>Reprint of</dt><dd><a href="#{r["repeat"]}">{r["repeat"]}</a></dd>')
        if r["source"] not in ("—", ""):
            o.append(f'<dt>Quoted from</dt><dd>{inline(r["source"])}</dd>')
        o.append(f'<dt>Anchor words</dt><dd>{inline(r["words"])}</dd>')
        o.append(f'<dt>Remarks</dt><dd>{inline(r["note"])}</dd>')
        o.append(f'<dt>Crop</dt><dd>folio {e["folio"]}, x {e["x0"]}&ndash;{e["x1"]}, '
                 f'y {e["y0"]}&ndash;{e["y1"]} (full-size scan pixels)</dd>')
        o.append("</dl></section>")

    o.append(f"<footer>Generated by tools/atlas/gen.py from the ledger {os.path.basename(ledger)} and "
             f"{os.path.basename(coords)}; crops by tools/atlas/crops.py. Remarks and Lean entries are quoted "
             f"from the ledger as written. Do not edit this file by hand.</footer>")
    o.append("</main></body></html>")
    open(out, "w", encoding="utf-8").write("\n".join(o) + "\n")
    print(f"{chap}: {s['rows']} cards, formulas {s['formula']} "
          f"(✓{mk['✓']} ≈{mk['≈']} ✎{mk['✎']} 未{mk['未']}), notation {s['notation']}")


main()
