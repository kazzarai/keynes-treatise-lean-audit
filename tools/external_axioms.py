#!/usr/bin/env python3
"""external_axioms — 台帳の「外」(外部公理依存) の式行から外部公理の依存表を作る。

使い方: python3 -I tools/external_axioms.py [--check] <ledger_dir> <phases_dir>
出力:   <ledger_dir>/external_axioms.md (手で書かない; --check は書き換えず一致だけを調べ、違えば終了コード 1)

対象の行: 台帳 chNN.md・notes_III.md の式行で、Lean 欄が「外部公理依存」で始まるもの (gen.py の判定「外」と同じ)。
公理の拾い方: Lean 欄 (括弧の中も含む) の `ax_…` の語のうち、同じ欄が `略号/名前` で挙げるファイルの中で
    `axiom` として宣言されているもの。1 行が複数の公理に寄るなら全部挙げる。欄の `ax_…` がそのファイルで
    axiom として宣言されていなければ WARN (終了コード 1)。
中身の一文: そのファイルの公理の docstring (`/-- … -/`) の先頭文 (最初の「。」まで; 強調の ** は外す)。
    同じ名前の公理が複数のファイルにあるときは、ファイル名の順で最初のファイルの docstring を使い、
    置いてあるファイルの欄に全部を並べる。
必要性の定理: 公理と同じファイルの theorem で、次のどちらかに当たるもの。
    (a) 名前が `nec_` で始まり、定理文 (`:=` まで) に `¬ 述語` (`¬ M.述語` も可) があり、述語が公理の結論の
        先頭の名前と同じもの (公理 `ax_equal_chance : EqualChance a29 h29` に対する `¬ M₁.EqualChance aC hC`)。
    (b) 名前が `_needs_ax` で終わり、docstring が公理の名前を挙げるもの。
    どちらも無ければ「なし」。
種別: 下の表 KIND で公理名ごとに与える (人が決める)。「統計的前提」は独立・等確率・近似・継起の規則・頻度と確率の
    一致など、Keynes の公理から出ない内容の前提。「データの整合性」は例のデータが矛盾しないことだけを置く前提。
    表に無い公理名が出たら WARN (終了コード 1)。合計は「統計的前提 n 本＋データの整合性 m 本」の形で書く。
"""
import glob
import importlib.util
import os
import re
import sys

sys.dont_write_bytecode = True
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("atlas_gen", os.path.join(_here, "atlas", "gen.py"))
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)

OUT = "external_axioms.md"
STAT, DATA = "統計的前提", "データの整合性"
KINDS = (STAT, DATA)
# 公理名 → 種別 (司令塔裁定 B54 r1)
KIND = {
    "ax_truth_frequency": STAT,             # 頻度と確率の一致 (第 8 章の頻度説)
    "ax_bernoulli_independence": STAT,      # 独立 (Bernoulli の定理の条件)
    "ax_equal_chance": STAT,                # 等確率 (§7 (i.))
    "ax_independence_ii": STAT,             # 独立 (§7 (ii.))
    "ax_poisson_approx": STAT,              # 近似 (Poisson 二項分布の中心極限定理)
    "ax_poisson_independence": STAT,        # 独立 (Poisson の定理の暗黙の前提)
    "ax_succession_rule": STAT,             # 継起の規則 (人工例)
    "ax_gen_succ": STAT,                    # 継起の規則 (一般の問題)
    "ax_normal_approx": STAT,               # 近似 (de Moivre–Laplace)
    "ax_statistical_generalisation": STAT,  # 頻度と確率の一致 (統計的一般化)
    "ax_data_cons29": DATA,                 # 第 29 章の data が矛盾する連言でない
}
REF = re.compile(r"(?<![\w/])(\w+)/[^\W\d][\w.'′]*")
AXTOK = re.compile(r"(?<![\w.])(ax_[A-Za-z0-9_]+)")
AXDECL = re.compile(r"^axiom\s+(ax_[A-Za-z0-9_]+)\b(.*)$")
THM = re.compile(r"^theorem\s+([^\s:(]+)")


def abbrevs_of(phases_dir):
    """略号 (`14a_bernoulli_premises`・`phase14a_bernoulli_premises`) → ファイル名。"""
    out = {}
    for p in sorted(glob.glob(os.path.join(phases_dir, "*.lean"))):
        stem = os.path.basename(p)[:-5]
        if "phase" in stem:
            suf = stem.split("phase", 1)[-1]
            out[suf] = out["phase" + suf] = os.path.basename(p)
    return out


def docstring_before(lines, k):
    """lines[k] の直前の `/-- … -/` の本文 (無ければ "")。"""
    j = k - 1
    if j < 0 or not lines[j].rstrip().endswith("-/"):
        return ""
    buf = []
    while j >= 0:
        buf.insert(0, lines[j])
        if lines[j].lstrip().startswith("/--"):
            break
        j -= 1
    s = ""
    for l in (x.strip() for x in buf):
        # 和文の行の折り返しは詰め、欧文どうしは空白 1 つで継ぐ
        s += ("" if not s or not l or ord(s[-1]) > 0x2FFF or ord(l[0]) > 0x2FFF else " ") + l
    s = re.sub(r"^/--\s*", "", s)
    s = re.sub(r"\s*-/$", "", s)
    return s


def first_sentence(s):
    s = s.replace("**", "")
    k = s.find("。")
    return s[:k + 1] if k >= 0 else s


def scan_file(path):
    """公理名 → (docstring, 結論の先頭の名前)、定理の列 (名前, 定理文, docstring)。"""
    lines = open(path, encoding="utf-8").read().split("\n")
    axioms, thms = {}, []
    for k, l in enumerate(lines):
        m = AXDECL.match(l)
        if m:
            # 結論: 宣言の最後のトップレベルの「:」の後 (束縛子の括弧の外)
            decl, j = l, k
            while not re.search(r":\s*\S", re.sub(r"\([^()]*\)|\{[^{}]*\}", "", decl)) and j + 1 < len(lines):
                j += 1
                decl += " " + lines[j].strip()
            body = re.sub(r"\([^()]*\)|\{[^{}]*\}", "", decl.split(m.group(1), 1)[1])
            concl = body.split(":", 1)[1].strip() if ":" in body else ""
            hm = re.match(r"([A-Z][\w']*)\b", concl)
            axioms[m.group(1)] = (docstring_before(lines, k), hm.group(1) if hm else None)
            continue
        m = THM.match(l)
        if m:
            stmt, j = l, k
            while ":=" not in stmt and j + 1 < len(lines):
                j += 1
                stmt += " " + lines[j].strip()
            thms.append((m.group(1), stmt.split(":=", 1)[0], docstring_before(lines, k)))
    return axioms, thms


def ext_rows(ledger_dir):
    out = []
    for c in G.ORDER:
        _, _, _, rows = G.read_ledger(os.path.join(ledger_dir, f"{c}.md"))
        out.extend(r for r in rows if r["type"] == "式" and G.lean_mark(r) == "外")
    return out


def build(ledger_dir, phases_dir):
    ab = abbrevs_of(phases_dir)
    scans = {}
    warns = []

    def scan(fn):
        if fn not in scans:
            scans[fn] = scan_file(os.path.join(phases_dir, fn))
        return scans[fn]

    rows = ext_rows(ledger_dir)
    row_ax = []        # (行ID, [(公理名, ファイル)])
    for r in rows:
        files = [ab[a] for a in dict.fromkeys(m.group(1) for m in REF.finditer(r["lean"])) if a in ab]
        found = []
        for name in dict.fromkeys(AXTOK.findall(r["lean"])):
            hit = [fn for fn in files if name in scan(fn)[0]]
            if not hit:
                warns.append(f"WARN external_axioms: {r['id']} の {name} は欄のファイル ({', '.join(files) or 'なし'}) で axiom として宣言されていない")
                continue
            found.append((name, hit[0]))
        if not found:
            warns.append(f"WARN external_axioms: {r['id']} の Lean 欄に外部公理の名前がない")
        row_ax.append((r["id"], found))
    for name in dict.fromkeys(n for _, found in row_ax for n, _ in found):
        if name not in KIND:
            warns.append(f"WARN external_axioms: {name} の種別が tools/external_axioms.py の表 KIND にない")
    by_ax = {}
    for rid, found in row_ax:
        for name, fn in found:
            by_ax.setdefault(name, {"files": {}, "rows": []})
            by_ax[name]["files"].setdefault(fn, []).append(rid)
            by_ax[name]["rows"].append(rid)
    for name, d in by_ax.items():
        fns = sorted(d["files"])
        doc, head = scan(fns[0])[0][name]
        d["doc"] = first_sentence(doc) if doc else "(docstring なし)"
        nec = []
        for fn in fns:
            short = "phase" + fn[:-5].split("phase", 1)[-1]  # 台帳の略号の書式 (phase14a_bernoulli_premises)
            _, h = scan(fn)[0][name]
            for tn, stmt, tdoc in scan(fn)[1]:
                if tn.startswith("nec_") and h and re.search(r"¬\s*(?:[\w₀-₉]+\.)?" + re.escape(h) + r"\b", stmt):
                    nec.append(f"{short}/{tn}")
                elif tn.endswith("_needs_ax") and re.search(r"(?<![\w])" + re.escape(name) + r"(?![\w])", tdoc):
                    nec.append(f"{short}/{tn}")
        d["nec"] = list(dict.fromkeys(nec))
    return rows, row_ax, by_ax, warns


def cell(s):
    return s.replace("|", "\\|")


def chap_of(rid):
    return rid.split("-")[0]


def kind_of(name):
    return KIND.get(name, "(種別なし)")


def render(rows, row_ax, by_ax):
    order = sorted(by_ax, key=lambda n: (min(rows.index(next(r for r in rows if r["id"] == x))
                                            for x in by_ax[n]["rows"]), n))
    n_kind = {k: sum(1 for n in by_ax if kind_of(n) == k) for k in KINDS}
    # 行の種別: 統計的前提に 1 本でも寄れば 統計的前提、データの整合性だけに寄るなら データの整合性
    row_kind = {rid: (STAT if any(kind_of(n) == STAT for n, _ in found) else
                      DATA if found and all(kind_of(n) == DATA for n, _ in found) else "—")
                for rid, found in row_ax}
    r_kind = {k: sum(1 for v in row_kind.values() if v == k) for k in KINDS}
    o = ["# 外部公理の依存表 (external axioms)", "",
         "この表は `tools/external_axioms.py` が台帳 (`chNN.md`・`notes_III.md`) の「外」(外部公理依存) の式行と "
         "`phases/*.lean` の宣言から作る。手で直さない。関門 [9] が `--check` で台帳との一致を確かめる。",
         "",
         f"- 外部公理: **{len(by_ax)}** 本 = {STAT} **{n_kind[STAT]}** 本＋{DATA} **{n_kind[DATA]}** 本 "
         "(名前の数; 同じ名前を再掲したファイルは 1 本に数え、置いてあるファイルの欄に並べる)。",
         f"- 外 の式行: **{len(rows)}** 行 = {STAT}に寄る行 {r_kind[STAT]}＋{DATA}だけに寄る行 {r_kind[DATA]}。",
         f"- 種別 (道具の中の表 `KIND` で与える): **{STAT}** は独立・等確率・近似・継起の規則・頻度と確率の一致など、"
         f"Keynes の公理から出ない内容の前提。**{DATA}** は例のデータが矛盾しないことだけを置く前提。",
         "- 公理の拾い方: Lean 欄 (括弧の中も含む) の `ax_…` のうち、同じ欄が挙げるファイルで `axiom` として宣言されているもの。"
         "1 行が複数の公理に寄るなら全部数える (表 1 の行数の和は 外 の行数より多くなりうる)。",
         "- 必要性の定理: 公理と同じファイルの `nec_…` で、定理文が公理の結論の述語の否定 (`¬ 述語`) を述べるもの (公理を落とすと偽になる模型)、"
         "または `…_needs_ax` で docstring が公理の名前を挙げるもの。無ければ「なし」。",
         "",
         "## 表 1 — 公理ごと",
         "",
         "| 公理名 | 種別 | 置いてあるファイル | 中身の一文 (docstring の先頭文) | 寄りかかる行 (章ごと) | 行数 | 必要性の定理 |",
         "|---|---|---|---|---|---|---|"]
    for n in order:
        d = by_ax[n]
        files = "<br>".join(f"`{fn}`" for fn in sorted(d["files"]))
        groups = {}
        for rid in d["rows"]:
            groups.setdefault(chap_of(rid), []).append(rid.split("-", 1)[1])
        rws = "; ".join(f"{c}: {', '.join(v)}" for c, v in groups.items())
        nec = ", ".join(f"`{x}`" for x in d["nec"]) or "なし"
        o.append(f"| `{n}` | {kind_of(n)} | {files} | {cell(d['doc'])} | {rws} | {len(d['rows'])} | {nec} |")
    o += ["", "## 表 2 — 外 の行ごと", "",
          "| 外の行 | 公理名 | 行の種別 |", "|---|---|---|"]
    for rid, found in row_ax:
        o.append(f"| {rid} | {', '.join(f'`{n}`' for n, _ in found) or '—'} | {row_kind[rid]} |")
    o.append("")
    return "\n".join(o)


def main():
    args = sys.argv[1:]
    check = "--check" in args
    if check:
        args.remove("--check")
    ledger_dir, phases_dir = args
    rows, row_ax, by_ax, warns = build(ledger_dir, phases_dir)
    new = render(rows, row_ax, by_ax)
    path = os.path.join(ledger_dir, OUT)
    for w in warns:
        print(w)
    if check:
        old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
        if old != new:
            print(f"WARN external_axioms: {OUT} が台帳から作り直した内容と一致しない (tools/external_axioms.py で作り直す)")
            sys.exit(1)
    else:
        with open(path, "w", encoding="utf-8", newline="") as f:
            f.write(new)
    n_kind = {k: sum(1 for n in by_ax if kind_of(n) == k) for k in KINDS}
    print(f"external_axioms: axioms={len(by_ax)} (stat={n_kind[STAT]} data={n_kind[DATA]}) rows={len(rows)}"
          + (" match" if check else " written"))
    if warns:
        sys.exit(1)


if __name__ == "__main__":
    main()
