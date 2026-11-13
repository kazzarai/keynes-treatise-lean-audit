#!/usr/bin/env python3
"""axiom_ii_usage — 公理 (ii) の中身 (前提側の置換) を持つ公理に依存する定理を、全 phases/*.lean の
#print axioms の出力から数える。名前ではなく中身で数える (司令塔裁定 B54 r1)。

使い方: python3 -I tools/axiom_ii_usage.py [--check] <phases_dir> <out.md> <check_all の記録>...
    記録は tools/check_all.sh が書く logs/check_<日時>.log (git には入らない)。全体の check_all 1 回の記録でも、
    phases/ を何群かに分けて回した記録を並べてもよい (同じファイルが 2 度現れたら後に挙げた記録を使う)。
    phases_dir のすべての *.lean が記録に現れなければ止まる (終了コード 1)。
出力: <out.md> (手で書かない)。--check は書き換えず、作り直した内容と一致するかだけを調べる (違えば終了コード 1)。
    入力が check_all 自身の記録なので、関門 (tools/check_all.sh) には入れない。

列:
    (A) 前提側の置換の公理: 公理 (ii) (folio 135) 「(a ≡ b)/h = 1 ならば x/ah = x/bh」の中身を持つ公理。
        下の表 A_AXIOMS (完全名・ファイル・型) に挙げたもの。表は全 phases/*.lean の axiom 宣言を読み、
        型が「前提の同値 → 同じ結論の確率が等しい」の形のものを人の目で洗い出して作った (B54 r1)。
        依存の列にその完全名があれば (A) に数える (そのファイルに宣言された完全名だけを見る)。
    (B) 整合性の移送の公理: 依存の列に `cons_iff_taut` (名前空間付きなら末尾が `.cons_iff_taut`) があるもの
        (論証的同値な命題は整合性を共有する; (ii) そのものではない)。
    (C) どちらにも依存しない。
    #print axioms の行数は関門 [3] の verdicts と同じ数え方 (「depends on axioms」の数;
        「does not depend on any axioms」は数えない)。
検査: 表の各行がそのファイルにその型で宣言されていなければ止まる。また、結論が「同じ結論の確率 = 同じ結論の
    確率 (前提だけ違う)」の形の axiom 宣言が表の外に見つかれば止まる (表を人の目で見直す合図)。
"""
import glob
import os
import re
import sys

STAGE1 = re.compile(r"^\[1\] (?:ok|RED compile:) (phases/\S+\.lean)")
DEP = re.compile(r"^'(.+?)' depends on axioms: \[(.*?)\]", re.S | re.M)
NS_OPEN = re.compile(r"^\s*namespace\s+(\S+)")
NS_END = re.compile(r"^\s*end\s+(\S+)\s*$")
AXDECL = re.compile(r"^\s*(?:private |protected )?axiom\s+(\S+)(.*)$")
THM = re.compile(r"^\s*theorem\s+(\S+)")
# 前提だけが違う確率の等式 (結論の最後の → の後)
PREM_EQ = re.compile(r"\b(PrI?)\s+(\w+|\([^()]*\))\s+(\S.*?)\s*=\s*\1\s+\2\s+(\S.*)$")
REFC = "cons_iff_taut"

# (A) 前提側の置換の公理: (完全名, ファイル, 型 (宣言の名前の後をそのまま、空白は 1 つに詰める))
A_AXIOMS = [
    ("Keynes.ax_ii", "keynes_part_ii_phase2.lean", "(α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)"),
    ("Keynes.ax_ii", "keynes_part_ii_phase3a.lean", "(α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)"),
    ("Keynes.ax_ii", "keynes_part_ii_phase3b.lean", "(α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)"),
    ("Keynes.ax_ii", "keynes_part_ii_phase3c.lean", "(α β h c : Prop) : KEq α β h → Pr c (α ∧ h) = Pr c (β ∧ h)"),
    ("Keynes.ax_iii_ev", "keynes_part_ii_phase6a.lean", "(p h k : Prop) : (h ↔ k) → Pr p h = Pr p k"),
    ("Keynes.ax_iii_ev", "keynes_part_ii_phase6b.lean", "(p h k : Prop) : (h ↔ k) → Pr p h = Pr p k"),
]


def is_ax(name, base):
    return name == base or name.endswith("." + base)


def read_logs(paths):
    """ファイル (phases/…) → ([(定理名, [公理名])], 記録の名前)。"""
    per = {}
    for p in paths:
        buf = []
        for line in open(p, encoding="utf-8", errors="replace"):
            m = STAGE1.match(line)
            if m:
                text = "".join(buf)
                per[m.group(1)] = ([(n, [a.strip() for a in axs.split(",") if a.strip()])
                                    for n, axs in DEP.findall(text)], os.path.basename(p))
                buf = []
            elif line.startswith("[") and re.match(r"^\[\w+\] ", line) or line.startswith("=== "):
                continue
            else:
                buf.append(line)
    return per


def scan(phases_dir):
    """ファイル名 → ([(公理の完全名, 型)], [定理の完全名])。"""
    out = {}
    for p in sorted(glob.glob(os.path.join(phases_dir, "*.lean"))):
        lines = open(p, encoding="utf-8").read().split("\n")
        ns, axs, thms = [], [], []
        for i, line in enumerate(lines):
            m = NS_OPEN.match(line)
            if m:
                ns.append(m.group(1))
                continue
            m = NS_END.match(line)
            if m and ns and ns[-1] == m.group(1):
                ns.pop()
                continue
            m = THM.match(line)
            if m:
                thms.append(".".join(ns + [m.group(1)]))
                continue
            m = AXDECL.match(line)
            if m:
                body, j = [m.group(2)], i + 1
                while (j < len(lines) and lines[j].startswith((" ", "\t")) and lines[j].strip()
                       and not re.match(r"^\s*(axiom|theorem|lemma|def|/--|--)", lines[j])):
                    body.append(lines[j])
                    j += 1
                axs.append((".".join(ns + [m.group(1)]), " ".join(" ".join(body).split())))
        out[os.path.basename(p)] = (axs, thms)
    return out


def validate(sc):
    errs = []
    for full, fn, ty in A_AXIOMS:
        if (full, ty) not in sc.get(fn, ([], []))[0]:
            errs.append(f"表 A_AXIOMS の {full} ({fn}) がその型で宣言されていない")
    table = {(full, fn) for full, fn, _ in A_AXIOMS}
    for fn, (axs, _) in sorted(sc.items()):
        for full, ty in axs:
            m = PREM_EQ.search(ty.split("→")[-1])
            if m and m.group(3).strip() != m.group(4).strip() and (full, fn) not in table:
                errs.append(f"前提側の置換の形の公理 {full} ({fn}) が表 A_AXIOMS にない")
    return errs


def render(files, per, sc):
    a_of = {}
    for full, fn, _ in A_AXIOMS:
        a_of.setdefault("phases/" + fn, set()).add(full)
    # 定理名の末尾の成分に (A) の公理名が語として現れるか (ax_ii は ax_iii_… には当てない)
    a_word = re.compile("(?<![A-Za-z0-9])(?:" + "|".join(sorted({re.escape(full.rsplit(".", 1)[-1])
                                                                  for full, _, _ in A_AXIOMS})) + ")(?![A-Za-z0-9])")
    rows, tot = [], {"n": 0, "A": 0, "B": 0, "C": 0, "AB": 0}
    a_list, b_list, look = [], [], []
    for f in files:
        ent = per[f][0]
        aset = a_of.get(f, set())
        cnt = {"A": 0, "B": 0, "C": 0}
        for t, axs in ent:
            ina = sorted(a for a in axs if a in aset)
            inb = any(is_ax(a, REFC) for a in axs)
            if ina:
                cnt["A"] += 1
                a_list.append((f, t, ina))
            if inb:
                cnt["B"] += 1
                b_list.append((f, t))
            if ina and inb:
                tot["AB"] += 1
            if not ina and not inb:
                cnt["C"] += 1
            if not ina and a_word.search(t.rsplit(".", 1)[-1]):
                look.append((f, t, axs))
        tot["n"] += len(ent)
        for k in cnt:
            tot[k] += cnt[k]
        rows.append(f"| `{os.path.basename(f)}` | {len(ent)} | {cnt['A']} | {cnt['B']} | {cnt['C']} |")
    logs = sorted(set(per[f][1] for f in files))
    prem = [(fn, t) for fn, (_, thms) in sorted(sc.items()) for t in thms if t.rsplit(".", 1)[-1] == "prem_subst"]
    o = ["# 公理 (ii) の中身 (前提側の置換) への依存の再集計 (全 phases)", "",
         f"- 作った元の記録: {'、'.join(f'`logs/{x}`' for x in logs)} ({len(files)} ファイル; git には入らない)。"
         "再生成: `bash tools/check_all.sh` の後に `python3 -I tools/axiom_ii_usage.py phases docs/全数台帳/axiom_ii_usage.md "
         "logs/check_<日時>.log` (関門には入れていない)。",
         "- 公理 (ii) (folio 135): (a ≡ b)/h = 1 ならば x/ah = x/bh。前提 (証拠) の側の置換。"
         "列は名前ではなく中身で分ける。",
         "- (A) 前提側の置換の公理: 型が「前提の同値 → 同じ結論の確率が等しい」の形の公理 (下の表 A; 名前が (ii) でないものも含む)。"
         "(B) 整合性の移送の公理 `cons_iff_taut` (論証的同値な命題は整合性を共有する)。(C) どちらにも依存しない。",
         "- #print axioms の行数は関門 [3] の verdicts と同じ数え方 (「depends on axioms」の数)。",
         "",
         f"#print axioms の **{tot['n']:,}** 行 ({len(files)} ファイル) のうち、(A) 前提側の置換の公理に依存するのは "
         f"**{tot['A']}** 行、(B) 整合性の移送の公理に依存するのは **{tot['B']}** 行、(C) どちらにも依存しないのは "
         f"**{tot['C']:,}** 行 ((A) と (B) の両方に依存するのは {tot['AB']} 行)。内訳は下表。",
         "",
         "| ファイル | #print axioms の行数 | (A) 前提側の置換 | (B) 整合性の移送 | (C) どちらにも依存しない |",
         "|---|---|---|---|---|"]
    o += rows
    o.append(f"| **計** | **{tot['n']:,}** | **{tot['A']}** | **{tot['B']}** | **{tot['C']:,}** |")
    o += ["", "## 表 A — (A) に数えた公理", "",
          "`tools/axiom_ii_usage.py` の表 `A_AXIOMS` の写し。型は宣言の名前の後をそのまま写す (空白は詰める)。",
          "", "| 公理の完全名 | 置いてあるファイル | 型 |", "|---|---|---|"]
    o += [f"| `{full}` | `{fn}` | `{ty}` |" for full, fn, ty in A_AXIOMS]
    o += ["", f"## (A) に依存する定理 ({len(a_list)} 本)", ""]
    o += [f"- `{os.path.basename(f)}`: `{t}` (依存: {', '.join(f'`{a}`' for a in ina)})" for f, t, ina in a_list] or ["なし (0 本)。"]
    o += ["", f"## (B) に依存する定理 ({len(b_list)} 本)", ""]
    o += [f"- `{os.path.basename(f)}`: `{t}`" for f, t in b_list] or ["なし (0 本)。"]
    o += ["", "## 脚注", "",
          "1. 名前と中身の対応: `Keynes.ax_ii` (phase2・3a–3c) は名前も中身も公理 (ii) で、前提の同値を "
          "`KEq α β h` (β/αh = 1 かつ α/βh = 1) で述べる。`Keynes.ax_iii_ev` (phase6a・6b) は名前は (iii) だが、"
          "中身は前提側の置換で、前提の同値を論理的同値 `h ↔ k` で述べる。`cons_iff_taut` は docstring が"
          "「公理 (ii) と公理 (iii) を合わせると」と述べるが、述べるのは整合性 `Cons` の移送で、確率の等式ではない。"]
    if look:
        o.append("2. 記録で (A) の公理名を定理名に含むが、(A) に依存しない定理 (模型の上の検算など; 数えていない): "
                 + "、".join(f"`{os.path.basename(f)}` の `{t}` (依存: [{', '.join(axs)}])" for f, t, axs in look) + "。")
    else:
        o.append("2. 記録で (A) の公理名を定理名に含むが、(A) に依存しない定理: なし。")
    o += ["3. Prop 担体 (`Pr : Prop → Prop → ℝ`) のファイル: Lean の `propext : (a ↔ b) → a = b` があるので、"
          "`h ↔ k` から `h = k` が出て、`Pr p h = Pr p k` は書換え 1 回 (`rw [propext e]`) で得られる。"
          "これは `ax_iii_ev` の型そのもので、公理を置かなくても得られる。`ax_ii` の前提 `KEq α β h` は確率 1 の"
          "相互含意で `↔` ではないので、この書換えはそのままは当てはまらない。",
          "4. IProp 担体 (`PrI : IProp → IProp → ℝ`、内包的) のファイル: (A) に当たる公理を置いていない "
          "(上の洗い出しで 0 本)。`propext` は Lean の `Prop` の等式を与えるだけで、`IProp` の値の等式は与えない。"
          "(ii) の中身は定理 `prem_subst` (Cons h、(a ≡ b)/h = 1、ah が整合のとき x/ah = x/bh) として、"
          "公理 (i) の但し書きの下で Def. X と (12) から導いている: "
          + ("、".join(f"`{fn}` の `{t}`" for fn, t in prem) or "宣言なし") + "。",
          ""]
    return "\n".join(o), tot


def main():
    args = sys.argv[1:]
    check = "--check" in args
    if check:
        args.remove("--check")
    phases_dir, out, logs = args[0], args[1], args[2:]
    if not logs:
        sys.exit("check_all の記録が 1 本も渡されていない")
    sc = scan(phases_dir)
    errs = validate(sc)
    if errs:
        sys.exit("\n".join(errs))
    per = read_logs(logs)
    files = ["phases/" + os.path.basename(p) for p in sorted(glob.glob(os.path.join(phases_dir, "*.lean")))]
    missing = [f for f in files if f not in per]
    if missing:
        sys.exit("記録に現れない phase: " + ", ".join(missing))
    new, tot = render(files, per, sc)
    if check:
        old = open(out, encoding="utf-8").read() if os.path.exists(out) else None
        if old != new:
            sys.exit(f"{out} が記録から作り直した内容と一致しない (tools/axiom_ii_usage.py で作り直す)")
    else:
        with open(out, "w", encoding="utf-8", newline="") as f:
            f.write(new)
    print(f"axiom_ii_usage: files={len(files)} print_axioms={tot['n']} A={tot['A']} B={tot['B']} C={tot['C']} AB={tot['AB']}"
          + (" match" if check else " written"))


if __name__ == "__main__":
    main()
