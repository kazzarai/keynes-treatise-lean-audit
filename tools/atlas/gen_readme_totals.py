# gen_readme_totals.py — docs/全数台帳/README.md の「Totals」の段落と章別表 (合計行 all を含む) を台帳から作り直す。
# 数はすべて台帳本体 (chNN.md・notes_III.md) の行から、gen_index.py と同じ関数 (chapter_stats) で数える。手で打たない。
# 書き換える範囲: Totals 節 (最初の「## Totals (…)」見出しから「## Per chapter」の前まで) を
#   見出し 1 つと段落 1 つに置き換える (追記しない; 2 つ目以降の「## Totals」見出しと「Formula lines **」で始まる段落は消え、
#   節の他の文章は残る)。
#   「## Per chapter」の表は数値の列と all 行を書き換え、all 行が 2 行以上あれば 1 行にする。
#   部・章・題の列、表の見出し行、他の文章は変えない。
# 版の表示: --version <版> (例 v1.21) を渡せば見出しを「## Totals (<版>)」にする。渡さなければ最後の
#   Totals 見出しの版をそのまま使う (--check は版を渡さずに回す)。
# 出力は入力と --version だけで決まる。何度回しても同じ。
# --check: README.md を書き換えず、作り直した内容とバイト単位で一致するかだけを調べる (違えば終了コード 1)。
# 使い方: python3 -I tools/atlas/gen_readme_totals.py [--check] [--version <版>] <ledger_dir>
#   (README.md は <ledger_dir>/README.md)
import importlib.util
import os
import re
import sys

sys.dont_write_bytecode = True
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("atlas_gen_index", os.path.join(_here, "gen_index.py"))
GI = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(GI)
G = GI.G


def fmt(n):
    return f"{n:,}"


def collect(ledger_dir):
    """章キー → chapter_stats。"""
    st = {}
    for c in G.ORDER:
        _, _, _, rows = G.read_ledger(os.path.join(ledger_dir, f"{c}.md"))
        st[c] = GI.chapter_stats(rows)
    return st


def totals_paragraph(st):
    part_tot = {}
    for p, cs in GI.PARTS:
        t = {}
        for c in cs:
            t = GI.add(t, st[c])
        part_tot[p] = t
    tot = {}
    for p, _ in GI.PARTS:
        tot = GI.add(tot, part_tot[p])
    proved = tot["p"] + tot["e"] + tot["c"]
    done = proved + tot["x"] + tot["d"]
    by_part_k = "; ".join(f"{p} {part_tot[p]['k']}" for p, _ in GI.PARTS)
    by_part_i = ", ".join(f"{p} {part_tot[p]['icov']}/{part_tot[p]['items']}" for p, _ in GI.PARTS)
    p2 = part_tot["II"]
    assert p2["x"] == 0, "第II部に 外 の行がある: 段落の書式を直す"
    return (
        f"Formula lines **{fmt(tot['lines'])}**; notations {fmt(tot['nt'])}; items {fmt(tot['items'])} "
        f"(numbered {fmt(tot['num'])}). Lines whose relation appears in a theorem statement "
        f"(✓+≈+✎, proved): {fmt(proved)} (✓ {fmt(tot['p'])} / ≈ {fmt(tot['e'])} / ✎ {fmt(tot['c'])}); "
        f"lines that depend on a named external axiom (外): {fmt(tot['x'])}; lines whose Lean counterpart is a "
        f"definition or a named premise (定): {fmt(tot['d'])}; lines in Lean in all (✓+≈+✎+外+定): "
        f"**{fmt(done)} / {fmt(tot['lines'])}**; not yet {fmt(tot['k'])} (by part: {by_part_k}). "
        f"Items covered by at least one theorem (✓/≈/✎ only; 外 and 定 are not counted): "
        f"{fmt(tot['icov'])} / {fmt(tot['items'])}; numbered items {fmt(tot['ncov'])} / {fmt(tot['num'])}. "
        f"By part (items covered / items): {by_part_i}. "
        f"Part II (Chapters X–XVII) has {fmt(p2['lines'])} formula lines: ✓ {fmt(p2['p'])} / ≈ {fmt(p2['e'])} / "
        f"✎ {fmt(p2['c'])} / 定 {fmt(p2['d'])} / not yet {fmt(p2['k'])}."
    ), tot


def chapter_cells(x):
    done = x["p"] + x["e"] + x["c"] + x["x"] + x["d"]
    return [fmt(x["lines"]), fmt(x["items"]), fmt(x["icov"]), f"{x['ncov']}/{x['num']}",
            f"{x['p']} / {x['e']} / {x['c']} / {x['x']} / {x['d']} / {x['k']}", fmt(done), fmt(x["nt"])]


TOTALS_RE = re.compile(r"^## Totals(?: \((?P<ver>[^)]*)\))?\s*$")


def rebuild(text, st, version=None):
    lines = text.split("\n")
    # Totals 節: 最初の「## Totals」見出しから「## Per chapter」の前までを、見出し 1 つ・段落 1 つ
    # (+ 節に残る他の文章) にする。古い版の見出しと「Formula lines **」で始まる段落は消す (追記しない)。
    heads = [k for k, l in enumerate(lines) if TOTALS_RE.match(l)]
    assert heads, "README.md に「## Totals」の見出しがない"
    end = next(n for n, l in enumerate(lines) if l.startswith("## Per chapter"))
    assert heads[-1] < end, "Totals の見出しが「## Per chapter」の後にある"
    if version is None:
        version = TOTALS_RE.match(lines[heads[-1]]).group("ver")
    head = "## Totals" + (f" ({version})" if version else "")
    para, tot = totals_paragraph(st)
    rest = [l for l in lines[heads[0] + 1:end]
            if not l.startswith("Formula lines **") and not TOTALS_RE.match(l)]
    lines[heads[0]:end] = [head, para] + rest
    # 章別表
    k = next(n for n, l in enumerate(lines) if l.startswith("## Per chapter"))
    n = k + 1
    while not lines[n].startswith("| Part |"):
        n += 1
    n += 2  # 見出し行と区切り行の次
    # 表では Notes on Part III (N3) は第33章の次の最終行
    order = iter([c for c in G.ORDER if c != "notes_III"] + ["notes_III"])
    seen_all = False
    while n < len(lines) and lines[n].startswith("|"):
        cells = [c.strip() for c in lines[n].strip().strip("|").split("|")]
        if cells[0] == "**all**" and seen_all:
            del lines[n]  # 2 行目以降の all 行は消す
            continue
        if cells[0] == "**all**":
            seen_all = True
            done = tot["p"] + tot["e"] + tot["c"] + tot["x"] + tot["d"]
            new = ["**all**", "", "", f"**{fmt(tot['lines'])}**", f"**{fmt(tot['items'])}**",
                   f"**{fmt(tot['icov'])}**", f"**{tot['ncov']}/{tot['num']}**",
                   f"**{tot['p']} / {tot['e']} / {tot['c']} / {tot['x']} / {tot['d']} / {tot['k']}**",
                   f"**{fmt(done)}**", f"**{fmt(tot['nt'])}**"]
        else:
            c = next(order)
            want = "N3" if c == "notes_III" else str(int(c[2:]))
            assert cells[1] == want, (cells[1], want)
            new = cells[:3] + chapter_cells(st[c])
        row = "| " + " | ".join(new) + " |"
        while "|  |" in row:  # 空の列は元の表と同じく「| |」
            row = row.replace("|  |", "| |")
        lines[n] = row
        n += 1
    assert next(order, None) is None, "章別表の行が足りない"
    assert seen_all, "章別表に all 行がない"
    return "\n".join(lines)


def main():
    args = sys.argv[1:]
    check = "--check" in args
    if check:
        args.remove("--check")
    version = None
    if "--version" in args:
        k = args.index("--version")
        version = args[k + 1]
        del args[k:k + 2]
    ledger_dir = args[0]
    path = os.path.join(ledger_dir, "README.md")
    with open(path, encoding="utf-8", newline="") as f:
        old = f.read()
    new = rebuild(old, collect(ledger_dir), version)
    if check:
        if new != old:
            sys.exit("README.md の合計・章別表が台帳から作り直した内容と一致しない (gen_readme_totals.py で作り直す)")
    elif new != old:
        with open(path, "w", encoding="utf-8", newline="") as f:
            f.write(new)
    print("README.md: totals and per-chapter table " + ("match" if new == old else "rewritten"))


if __name__ == "__main__":
    main()
