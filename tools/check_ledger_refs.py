#!/usr/bin/env python3
"""check_ledger_refs — 台帳の Lean 欄が指す名前が phases/ に実在するかを確かめる。

使い方: python3 -I tools/check_ledger_refs.py docs/全数台帳 phases
対象: 台帳 chNN.md・notes_III.md の表のうち、式行で ✓/≈/✎/外部公理依存/定 のもの、記法行で 未 以外のもの。
「定」の行は定義名 (または前提名を持つ定理名) を必ず 1 つ挙げる。名前がなければ MISSING にする。
抽出: Lean 欄から括弧書きを除き、`ファイル略号/名前` の「名前」を取る。続く 2 本目以降は
      「・」「,」「;」「、」で並べたもの (`10a/th_a, th_b; 6c/th_c` の `th_b`) も取る。
      2 本目以降は英字 (ASCII またはギリシャ文字)・`_` で始まり、直後が区切り (「・」「,」「;」「、」)
      か欄末の語だけを名前とみなす。名前の直後に散文が続く 2 本目 (`; h = 0 の場合は`・
      `, th_b は前提を替えた形` の `th_b`) は名前として検査しない。
      同じ行で同じ名前を 2 度挙げても 1 回に数える (`refs=` は行ID と名前の組の数)。
照合: phases/*.lean の theorem・lemma・def・abbrev・structure・instance・axiom 等の宣言名
      (namespace 付きなら末尾一致も可) と突き合わせる。
備考欄: 表のすべての行 (判定・種別に関わらず) の備考欄に書かれた `略号/名前` (括弧の中も、「・」「,」「;」「、」で並べたものも) も
      同じ規則で拾い、実在だけを確かめる (判定は触らない)。名前空間の名前 (`Witness_F20_11_den` など) も実在とみなす。
出力: `names=M missing=N` (Lean 欄) と `note_refs=K note_names=L note_missing=J` (備考欄)。
      見つからない名前があれば `MISSING 行ID → 名前` (備考欄は末尾に `(備考)`) を並べ、終了コード 1。
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
# `略号/名前` の直後に「, 」「;」「、」「・」で続く 2 本目以降。略号付き (`; 6c/名前`) は REF 側が拾うので飛ばす
TAIL = re.compile(
    r"\s*[,;、・]\s*(?:(?:全 phase|\w+(?:,\w+)*)/)?(?P<bare>[A-Za-zΑ-Ωα-ω_][\w.'′!?]*(?=\s*(?:[,;、・]|$)))?"
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
    """宣言名の集合、宣言数、ファイル略号の集合、名前空間の名前の集合。

    `A.B.C` に対して `C`・`B.C`・`A.B.C` を全部入れる。略号は `phase10c` から
    `10c`・`phase10c`、`pilot` から `pilot`、台帳の群略号 `P2`・`全 phase`。
    """
    names, count = set(), 0
    spaces = set()  # namespace の名前。備考欄が反例の束 (`Witness_F20_11_den`) を名前空間ごと挙げるときのため
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
                    parts = ns + m.group(1).split(".")
                    spaces.update(".".join(parts[i:]) for i in range(len(parts)))
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
    return names, count, abbrevs, spaces


def names_in(text, abbrevs):
    """text の中の `略号/名前` の名前の列 (「・」「,」「;」「、」で並べたものも)。"""
    found = []
    for m in REF.finditer(text):
        # 略号が既知のファイルを指さないもの (本文中の a/hx など) は名前でない
        if not all(t in abbrevs for t in m.group(1).split(",")):
            continue
        found.append(m.group(2))
        found.extend(n for n in m.group(3).split("・") if n)
        pos = m.end()
        while True:
            t = TAIL.match(text, pos)
            if not t or t.end() == pos:
                break
            # 略号付きの項は REF が拾い、その続きは REF 側の 2 本目以降として歩くので、ここで止める
            if "/" in t.group(0):
                break
            pos = t.end()
            if t.group("bare"):
                found.append(t.group("bare"))
    return found


def ledger_refs(ledger_dir, abbrevs):
    """(行ID, 名前) の列、対象にした行の数、備考欄の (行ID, 名前) の列。

    備考欄は括弧の中も含めて拾う (散文の中の `10a/名前`)。判定には使わず、実在だけを確かめる。
    """
    refs, rows, note_refs = [], 0, []
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
                # 備考欄: 行の種別・判定に関わらず、散文中の `略号/名前` の実在だけを確かめる
                for n in dict.fromkeys(names_in(d.get("備考", ""), abbrevs)):
                    note_refs.append((d["行ID"], n))
                col = next((h for h in hdr if h == "Lean" or h.startswith("既存の Lean")), None)
                if col is None:
                    continue
                kind, cell = d.get("式/記法", ""), d[col]
                if kind == "式":
                    if not cell.startswith(("✓", "≈", "✎", "外部公理依存", "定")):
                        continue
                elif kind == "記法":
                    if cell.startswith("未"):
                        continue
                else:
                    continue
                found = names_in(strip_parens(cell), abbrevs)
                if found:
                    rows += 1
                elif kind == "式" and cell.startswith("定"):
                    # 「定」は対応する Lean の定義を挙げる行。名前がなければ実在を確かめられない
                    refs.append((d["行ID"], "(定の行に定義名がない)"))
                # 同じ行で同じ名前を 2 度挙げた (別ファイルの略号違い `8d/V; 8dp/V` など) ときは 1 回に数える
                for n in dict.fromkeys(found):
                    refs.append((d["行ID"], n))
    return refs, rows, note_refs


def main(argv):
    if len(argv) != 3:
        print(__doc__)
        return 2
    decls, ndecl, abbrevs, spaces = declared_names(argv[2])
    refs, rows, note_refs = ledger_refs(argv[1], abbrevs)
    distinct = {n for _, n in refs}
    missing = sorted({n for n in distinct if n not in decls})
    note_distinct = {n for _, n in note_refs}
    note_missing = sorted({n for n in note_distinct if n not in decls and n not in spaces})
    print(f"rows={rows} decls={ndecl} refs={len(refs)}")
    for rid, n in refs:
        if n in missing:
            print(f"MISSING {rid} → {n}")
    for rid, n in note_refs:
        if n in note_missing:
            print(f"MISSING {rid} → {n} (備考)")
    print(f"names={len(distinct)} missing={len(missing)}")
    print(f"note_refs={len(note_refs)} note_names={len(note_distinct)} note_missing={len(note_missing)}")
    return 1 if missing or note_missing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
