# gen_index.py — 図鑑の目次頁 (docs/atlas/index.html) を作る。
# 上から: 全体の数の枠 5 つ / 部ごとの表 (I〜V と合計) / 章の一覧 (部ごとに区切り、各章頁へのリンク) / 読み方 3 行。
# 数はすべて台帳本体 (chNN.md・notes_III.md) の行から、gen.py と同じ関数 (read_ledger・lean_mark・summary) で数える。
#   式の行: 種別「式」の行。項目: 式の行の項目ID の種類。Lean 対応の項目: その項目の行のどれかが ✓/≈/✎。
#   番号付き項目: 番号欄が空でない式の行を持つ項目 (箇条記号 (i.) なども番号に入れる)。
# 題と folio 範囲は summary.csv から取る。summary.csv の数の列と台帳から数えた値が違えば標準エラーに出す (直さない)。
# カード数は各章頁 (<atlas_dir>/<章>/index.html) の card を数え、台帳の行数と一致することを確かめる。
# 表は数値の列を折り返さず右揃え (桁は tabular-nums)、折り返すのは題の列だけ。幅が足りなければ横スクロール (.wide)。
# 文言は gen.py の辞書 L (ix_ で始まる鍵と共通の鍵) から引く (--lang ja で切り替え; 既定は en)。
# 出力は入力 (台帳と章頁) だけで決まる (日時などを埋めない)。
# --missing-ok: 章頁がまだ無い章は題にリンクを張らず「未作成」と書き、カード数を「—」にする (部の行は作成済の章だけを足す)。
#   章が順に増える図鑑 (訳書版) 用。何度でも再生成してよい。指定しなければ章頁が 1 つでも無いと止まる。
# 使い方: python3 -I tools/atlas/gen_index.py [--lang ja] [--missing-ok] <ledger_dir> <atlas_dir> <out.html>
import csv
import html
import importlib.util
import os
import sys

# gen.py を読み込むときに tools/atlas/__pycache__ を作らない
sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location(
    "atlas_gen", os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen.py"))
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)

# 部と章 (Notes on Part III は第III部の末尾)
PARTS = [("I", G.ORDER[0:9]), ("II", G.ORDER[9:17]), ("III", G.ORDER[17:24]),
         ("IV", G.ORDER[24:27]), ("V", G.ORDER[27:34])]
assert [c for _, cs in PARTS for c in cs] == G.ORDER

CSS = G.CSS + """
.boxes{display:flex;flex-wrap:wrap;gap:10px;margin:1em 0 1.5em}
.box{flex:1 1 150px;border:1px solid #ccc;border-radius:4px;padding:10px 12px}
.box .lab{font-size:.85em;color:#444}
.box .num{font-size:1.6em;font-weight:bold;margin:2px 0;white-space:nowrap;font-variant-numeric:tabular-nums}
.box .num small{font-size:.6em;font-weight:normal;color:#444}
.box .desc{font-size:.8em;color:#555;line-height:1.35}
h2{font-size:1.2em;margin:1.5em 0 .3em}
h3{font-size:1.02em;margin:1.2em 0 .2em}
table.sum td.n,table.sum th.n{text-align:right}
table.sum tr.head th{white-space:normal;vertical-align:bottom}
table.sum.chap{width:100%}
table.sum.chap td.n{width:1%}
table.sum td.t{white-space:normal;width:auto}
table.sum td.nf{text-align:left}
table.sum td .mark{margin:0}
table.sum tr.total th,table.sum tr.total td{font-weight:bold;border-top:2px solid #888}
"""


NC = ' class="n"'


def fmt(n):
    return f"{n:,}"


def chapter_stats(rows):
    s = G.summary(rows)
    items = {}
    for r in rows:
        if r["type"] == "式":
            items.setdefault(r["item"], []).append(r)
    cov = {k for k, v in items.items() if any(G.lean_mark(r) in ("✓", "≈", "✎") for r in v)}
    num = {k for k, v in items.items() if any(r["num"] not in G.BLANK for r in v)}
    mk = s["marks"]
    return {"lines": s["formula"], "items": len(items), "icov": len(cov), "num": len(num),
            "ncov": len(num & cov), "p": mk["✓"], "e": mk["≈"], "c": mk["✎"], "k": mk["未"],
            "nt": s["notation"], "n_lean": s["n_lean"], "rows": s["rows"]}


def add(a, b):
    return {k: a.get(k, 0) + b[k] for k in b}


def frac(m, n):
    return f"{fmt(m)} / {fmt(n)} ({G.pct(m, n)})"


def main():
    args = sys.argv[1:]
    lang = "en"
    if "--lang" in args:
        i = args.index("--lang")
        lang = args[i + 1]
        del args[i:i + 2]
    missing_ok = "--missing-ok" in args
    if missing_ok:
        args.remove("--missing-ok")
    t = G.L[lang]
    ledger_dir, atlas_dir, out = args[0], args[1], args[2]

    meta = {}
    for r in csv.DictReader(open(os.path.join(ledger_dir, "summary.csv"), encoding="utf-8")):
        meta["notes_III" if r["章"] == "N3" else f"ch{int(r['章']):02d}"] = r
    assert sorted(meta) == sorted(G.ORDER), sorted(set(meta) ^ set(G.ORDER))

    st, warn = {}, []
    for c in G.ORDER:
        chap, _, (fa, fb, _, _), rows = G.read_ledger(os.path.join(ledger_dir, f"{c}.md"))
        assert chap == c, (chap, c)
        x = chapter_stats(rows)
        path = os.path.join(atlas_dir, c, "index.html")
        x["built"] = int(os.path.exists(path) or not missing_ok)
        if x["built"]:
            page = open(path, encoding="utf-8").read()
            x["cards"] = page.count('<section class="card"')
            assert x["cards"] == x["rows"], (c, "cards", x["cards"], "ledger rows", x["rows"])
        else:
            x["cards"] = 0
        st[c] = x
        m = meta[c]
        for col, key in (("式", "lines"), ("項目数", "items"), ("記法", "nt"), ("✓", "p"), ("≈", "e"),
                         ("✎", "c"), ("未(式)", "k"), ("記法のLean対応", "n_lean")):
            if int(m[col]) != x[key]:
                warn.append(f"{c}: summary.csv {col}={m[col]}, ledger {x[key]}")
        if (m["folio_from"], m["folio_to"]) != (fa, fb):
            warn.append(f"{c}: summary.csv folio {m['folio_from']}-{m['folio_to']}, ledger {fa}-{fb}")

    part_tot = {p: {} for p, _ in PARTS}
    for p, cs in PARTS:
        for c in cs:
            part_tot[p] = add(part_tot[p], st[c])
    tot = {}
    for p, _ in PARTS:
        tot = add(tot, part_tot[p])
    done = tot["p"] + tot["e"] + tot["c"]
    cmd = "python3 -I tools/atlas/gen_index.py docs/全数台帳 docs/atlas docs/atlas/index.html" + (
        f" --lang {lang}" if lang != "en" else "") + (" --missing-ok" if missing_ok else "")

    o = ["<!DOCTYPE html>", f'<html lang="{lang}"><head><meta charset="utf-8">',
         '<meta name="viewport" content="width=device-width, initial-scale=1">',
         f"<title>{html.escape(t['ix_title'])}</title>", f"<style>{CSS}</style></head><body><main>",
         f"<h1>{html.escape(t['ix_h1'])}</h1>", f'<p class="sub">{t["ix_sub"]}</p>']

    # a. 頭の数字
    def box(lab, num, desc):
        return (f'<div class="box"><div class="lab">{html.escape(lab)}</div>'
                f'<div class="num">{num}</div><div class="desc">{desc}</div></div>')

    def boxfrac(m, n):
        return f"{fmt(m)} <small>/ {fmt(n)} ({G.pct(m, n)})</small>"

    o.append('<div class="boxes">')
    o.append(box(t["ix_b_lines"], fmt(tot["lines"]), t["ix_d_lines"].format(nt=fmt(tot["nt"]))))
    o.append(box(t["ix_b_items"], fmt(tot["items"]), t["ix_d_items"]))
    o.append(box(t["ix_b_icov"], boxfrac(tot["icov"], tot["items"]), t["ix_d_icov"]))
    o.append(box(t["ix_b_ncov"], boxfrac(tot["ncov"], tot["num"]), t["ix_d_ncov"]))
    o.append(box(t["ix_b_lcov"], boxfrac(done, tot["lines"]),
                 t["ix_d_lcov"].format(a=fmt(tot["p"]), b=fmt(tot["e"]), c=fmt(tot["c"]), k=fmt(tot["k"]))))
    o.append("</div>")

    # b. 部ごとの表
    o.append(f"<h2>{html.escape(t['ix_h_parts'])}</h2>")
    o.append('<div class="wide"><table class="sum"><tr class="head">' + "".join(
        f'<th{"" if k == "c_part" else NC}>{t["ix_" + k]}</th>'
        for k in ("c_part", "c_nch", "c_lines", "c_items", "c_icov", "c_ncov", "c_lcov", "c_nt", "c_cards"))
             + "</tr>")

    def part_row(label, nch, x, cls=""):
        d = x["p"] + x["e"] + x["c"]
        # 未作成の章があれば、カード数に作成済の章の数を添える (--missing-ok のときだけ起こる)
        cards = fmt(x["cards"]) if x["built"] == nch else t["ix_cards_part"].format(
            c=fmt(x["cards"]), m=x["built"], n=nch)
        return (f'<tr{cls}><th>{label}</th><td class="n">{nch}</td><td class="n">{fmt(x["lines"])}</td>'
                f'<td class="n">{fmt(x["items"])}</td><td class="n">{frac(x["icov"], x["items"])}</td>'
                f'<td class="n">{fmt(x["ncov"])} / {fmt(x["num"])}</td>'
                f'<td class="n">{fmt(d)} / {fmt(x["k"])}</td><td class="n">{fmt(x["nt"])}</td>'
                f'<td class="n">{cards}</td></tr>')

    for p, cs in PARTS:
        o.append(part_row(html.escape(t["ix_part"].format(p=p)), len(cs), part_tot[p]))
    o.append(part_row(html.escape(t["ix_total"]), len(G.ORDER), tot, ' class="total"'))
    o.append("</table></div>")

    # c. 章の一覧
    o.append(f"<h2>{html.escape(t['ix_h_chaps'])}</h2>")
    for p, cs in PARTS:
        nums = [int(c[2:]) for c in cs if c != "notes_III"]
        span = t["ix_part_span_notes" if "notes_III" in cs else "ix_part_span"].format(a=nums[0], b=nums[-1])
        o.append(f"<h3>{html.escape(t['ix_part'].format(p=p))} &mdash; {span}</h3>")
        o.append('<div class="wide"><table class="sum chap"><tr class="head">' + "".join(
            f'<th{"" if k == "c_title" else NC}>{t["ix_" + k]}</th>'
            for k in ("c_ch", "c_title", "c_folio", "c_lines", "c_done", "c_marks", "c_nt", "c_cards"))
                 + "</tr>")
        for c in cs:
            x, m = st[c], meta[c]
            no = html.escape(t["ix_notes"]) if c == "notes_III" else str(int(c[2:]))
            # 題の列: 英語版は summary.csv の原題、日本語版は邦題 (title 属性に原題)
            ja_t = t["ch_title"].get(c)
            name = html.escape(ja_t or m["題"])
            tip = f' title="{html.escape(m["題"], quote=True)}"' if ja_t else ""
            if x["built"]:
                ttl = f'<a href="{c}/index.html"{tip}>{name}</a>'
            else:
                ttl = f'<span{tip}>{name}</span> ({html.escape(t["missing"])})' if tip else f'{name} ({html.escape(t["missing"])})'
            cells = [f'<td class="n">{no}</td>',
                     f'<td class="t">{ttl}</td>',
                     f'<td class="n">{m["folio_from"]}&ndash;{m["folio_to"]}</td>',
                     f'<td class="n">{fmt(x["lines"])}</td>']
            if x["lines"]:
                k = f'<span class="mark none">{x["k"]}</span>' if x["k"] else "0"
                cells.append(f'<td class="n">{frac(x["p"] + x["e"] + x["c"], x["lines"])}</td>')
                cells.append(f'<td class="n">{x["p"]} / {x["e"]} / {x["c"]} / {k}</td>')
            else:
                cells.append(f'<td colspan="2" class="nf">{html.escape(t["no_formula"])}</td>')
            cells += [f'<td class="n">{fmt(x["nt"])}</td>',
                      f'<td class="n">{fmt(x["cards"]) if x["built"] else "&mdash;"}</td>']
            o.append("<tr>" + "".join(cells) + "</tr>")
        o.append("</table></div>")

    # d. 読み方
    o.append(f'<p class="rules">{t["ix_end_marks"]}<br>{t["ix_end_count"]}<br>'
             f'{t["ix_end_regen"].format(cmd=cmd)}</p>')
    o.append(f"<footer>{t['ix_footer']}</footer>")
    o.append("</main></body></html>")
    open(out, "w", encoding="utf-8").write("\n".join(o) + "\n")
    for w in warn:
        print("WARN", w, file=sys.stderr)
    print(f"index: {len(G.ORDER)} chapters, formula lines {tot['lines']}, items {tot['icov']}/{tot['items']}, "
          f"numbered {tot['ncov']}/{tot['num']}, lines {done}/{tot['lines']} "
          f"(✓{tot['p']} ≈{tot['e']} ✎{tot['c']} 未{tot['k']}), notation {tot['nt']}, cards {tot['cards']}"
          + (f", built {tot['built']}/{len(G.ORDER)}" if missing_ok else ""))


if __name__ == "__main__":
    main()
