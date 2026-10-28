#!/usr/bin/env python3
"""check_ledger_refs — 台帳の Lean 欄が指す名前が phases/ に実在するかを確かめる。

使い方: python3 -I tools/check_ledger_refs.py docs/全数台帳 phases
対象: 台帳 chNN.md・notes_III.md の表のうち、式行で ✓/≈/✎ のもの、記法行で 未 以外のもの。
抽出: Lean 欄から括弧書きを除き、`ファイル略号/名前` の「名前」(「・」で並べたものも) を取る。
照合: phases/*.lean の theorem・lemma・def・abbrev・structure・instance・axiom 等の宣言名
      (namespace 付きなら末尾一致も可) と突き合わせる。
出力: 末尾に `names=M missing=N`。見つからない名前があれば `MISSING 行ID → 名前` を並べ、終了コード 1。
"""
import glob
import os
import re
import sys

IDENT = r"[^\W\d][\w.'′!?]*"
KINDS = r"theorem|lemma|def|abbrev|structure|instance|axiom|inductive|class|opaque"
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:" + KINDS + r")\s+(" + IDENT + r")"
)
NS_OPEN = re.compile(r"^\s*namespace\s+(" + IDENT + r")")
# `略号/名前`、続けて `・名前` を許す。略号は `10c`、`pilot,P2`、`全 phase` など
REF = re.compile(
    r"(?<![\w/])(全 phase|\w+(?:,\w+)*)/(" + IDENT + r")((?:・" + IDENT + r")*)"
)
SECTION = re.compile(r"^\s*section(?:\s+(" + IDENT + r"))?\s*$")
END = re.compile(r"^\s*end(?:\s+(" + IDENT + r"))?\s*$")
FIELD = re.compile(r"^\s+(" + IDENT + r")\s*:")
STRUCT = re.compile(r"^\s*(?:(?:private|protected)\s+)*structure\s+(" + IDENT + r")")


def strip_parens(s):
    """全角・半角の括弧書き (入れ子可) を除く。"""
    out, depth = [], 0
    for ch in s:
        if ch in "(（":
            depth += 1
        elif ch in ")）":
            depth = max(0, depth - 1)
        elif depth == 0:
            out.append(ch)
    return "".join(out)


def declared_names(phases_dir):
    """宣言名の集合、宣言数、ファイル略号の集合。

    `A.B.C` に対して `C`・`B.C`・`A.B.C` を全部入れる。略号は `phase10c` から
    `10c`・`phase10c`、`pilot` から `pilot`、台帳の群略号 `P2`・`全 phase`。
    """
    names, count = set(), 0
    abbrevs = {"P2", "全 phase"}
    for path in sorted(glob.glob(os.path.join(phases_dir, "*.lean"))):
        stem = os.path.basename(path)[:-5]
        if stem.endswith("_pilot"):
            abbrevs.add("pilot")
        else:
            suffix = stem.split("phase", 1)[-1]
            abbrevs.update({suffix, "phase" + suffix})
        stack = []       # (名前空間か, 名前) の入れ子。section も end で閉じるので積む
        struct = None    # 直近の structure 名。インデントされた `欄 :` 行を欄として拾う
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                ns = [n for is_ns, n in stack if is_ns for n in n.split(".")]
                m = NS_OPEN.match(line)
                if m:
                    stack.append((True, m.group(1)))
                    struct = None
                    continue
                m = SECTION.match(line)
                if m:
                    stack.append((False, m.group(1) or ""))
                    struct = None
                    continue
                if END.match(line):
                    if stack:
                        stack.pop()
                    struct = None
                    continue
                m = DECL.match(line)
                if m:
                    parts = ns + m.group(1).split(".")
                    count += 1
                    for i in range(len(parts)):
                        names.add(".".join(parts[i:]))
                    ms = STRUCT.match(line)
                    struct = parts if ms else None
                    continue
                m = FIELD.match(line)
                if m and struct:
                    parts = struct + [m.group(1)]
                    for i in range(len(parts)):
                        names.add(".".join(parts[i:]))
                elif line.strip() and not line[0].isspace():
                    struct = None
    return names, count, abbrevs


def ledger_refs(ledger_dir, abbrevs):
    """(行ID, 名前) の列と、対象にした行の数。"""
    refs, rows = [], 0
    for path in sorted(glob.glob(os.path.join(ledger_dir, "*.md"))):
        hdr = None
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                if not line.startswith("|"):
                    if not line.strip():
                        hdr = None
                    continue
                cells = [c.strip() for c in line.strip().strip("|").split("|")]
                if cells[0] == "行ID":
                    hdr = cells
                    continue
                if not hdr or len(cells) != len(hdr):
                    continue
                d = dict(zip(hdr, cells))
                col = next((h for h in hdr if h == "Lean" or h.startswith("既存の Lean")), None)
                if col is None:
                    continue
                kind, cell = d.get("式/記法", ""), d[col]
                if kind == "式":
                    if not cell.startswith(("✓", "≈", "✎")):
                        continue
                elif kind == "記法":
                    if cell.startswith("未"):
                        continue
                else:
                    continue
                found = []
                for m in REF.finditer(strip_parens(cell)):
                    # 略号が既知のファイルを指さないもの (本文中の a/hx など) は名前でない
                    if not all(t in abbrevs for t in m.group(1).split(",")):
                        continue
                    found.append(m.group(2))
                    found.extend(n for n in m.group(3).split("・") if n)
                if found:
                    rows += 1
                for n in found:
                    refs.append((d["行ID"], n))
    return refs, rows


def main(argv):
    if len(argv) != 3:
        print(__doc__)
        return 2
    decls, ndecl, abbrevs = declared_names(argv[2])
    refs, rows = ledger_refs(argv[1], abbrevs)
    distinct = {n for _, n in refs}
    missing = sorted({n for n in distinct if n not in decls})
    print(f"rows={rows} decls={ndecl} refs={len(refs)}")
    for rid, n in refs:
        if n in missing:
            print(f"MISSING {rid} → {n}")
    print(f"names={len(distinct)} missing={len(missing)}")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
