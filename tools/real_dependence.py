#!/usr/bin/env python3
"""real_dependence — 第II部の各判定 (theorem/lemma/example) と公理が ℝ のどの性質に依存するかを機械的に分類する。

使い方: python3 -I tools/real_dependence.py                  (引数なし。リポジトリの根から。csv・md を書く)
        python3 -I tools/real_dependence.py --write-ledger   (台帳 ch12–17 に列「ℝ 依存」を足す)
        python3 -I tools/real_dependence.py --write-readme   (台帳 README の小表を、この出力の数字で差し替える)
対象: phases/keynes_part_ii_*.lean の theorem・lemma・example (行頭に置かれたもの) と axiom。
分類 (排他。複数に当たるときは C > D > E > A′ > B > A):
  C  線形順序 (le_total・lt_or_le・linarith・nlinarith・positivity・abs_*・max/min など。比較可能性を使う)
  D  体の構造 (除算・逆元・field_simp・div_*・inv_*・one_div)
  E  数値 (norm_num・Real.*)
  A′ 順序付き環 (mul_pos・mul_nonneg・sub_nonneg・add_pos・sq_nonneg・div_le_*・abs_nonneg など、
     名前全体で判定する「順序と環の演算」の補題。比較可能性は要らない)
  B  加法・乗法 (ring・mul_*・add_*・sub_*・sq_*・Finset.sum_*)
  A  順序のみ (上のどれにも当たらない)
class は宣言の文面と証明の字面に現れる語だけで決める。class_trans は、同じファイルの別定理の呼び出しと
公理の使用 (AXIOM_RULES の表) を本文から辿った最強値。台帳の列は class_trans で付ける。
出力: docs/全数台帳/real_dependence.csv・real_dependence.md
"""
import csv
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PHASES = os.path.join(ROOT, "phases")
LEDGER = os.path.join(ROOT, "docs", "全数台帳")

# 行頭の宣言。check_ledger_refs.py の DECL と同じ流儀で、行頭に置かれた theorem・lemma・example
UNIT = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected)\s+)*(theorem|lemma|example)\b\s*([^\s:({\[]*)")
ANY_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|example|def|abbrev|structure|instance|axiom|inductive|class|opaque|namespace|section|end|open|variable|"
    r"set_option|universe|import|#print|#eval|#check|attribute|noncomputable|macro|syntax|notation|local|scoped|"
    r"/-!|/--)\b"
)

# 語彙。各クラスの正規表現 (識別子の先頭境界つき)
def words(*ws):
    return re.compile(r"(?<![\w.'])(?:" + "|".join(ws) + r")(?![\w'])")

# A′ (順序付き環) の補題。名前全体で判定する。ORD_KEEP は D の語 (div_*・inv_*) にも当たる補題で、
# 消さずに残す (D の方が強いので D になる)。ORD_ERASE は B・C の語彙に取られる前に消す。
ORD_KEEP = words(r"div_nonneg", r"div_pos", r"div_le_\w+", r"div_lt_\w+", r"le_div_iff\w*", r"lt_div_iff\w*",
                 r"one_lt_div", r"inv_pos", r"inv_nonneg")
# 振り分けで迷う語は上位のクラスに置く (裁定 F32.13 以降の一般則)。AMBIGUOUS が .md の「振り分け表」の元。
# (語, 迷った候補, 置いたクラス, 理由)。語は正規表現。
AMBIGUOUS = [
    (r"Finset\.sum_le_sum\w*", "B/A′", "P", "和と順序の両方 (単調性)"),
    (r"Finset\.sum_nonneg|Finset\.sum_pos|Finset\.sum_eq_zero_iff_of_nonneg", "B/A′", "P", "和と順序の両方 (非負・正)"),
    (r"mul_eq_zero|mul_ne_zero|pow_ne_zero|pow_eq_zero_iff|eq_zero_or_eq_zero_of_mul_eq_zero", "B/D", "D", "零因子が無いこと (整域の性質)。環では成り立たない"),
    (r"mul_left_cancel₀|mul_right_cancel₀", "B/D", "D", "0 でない元での簡約 (逆元か整域が要る)"),
    (r"eq_div_iff|eq_div_of_mul_eq|div_eq_iff", "A/D", "D", "除算を含む (旧版は語に当たらず A になっていた)"),
    (r"sq_abs", "B/C", "C", "絶対値を含む"),
    (r"exact_mod_cast|norm_cast|push_cast", "A/E", "E", "ℕ → ℝ の型変換 (旧版は語に当たらず A になっていた)"),
    (r"one_mul|zero_add|zero_mul|eq_sub_of_add_eq|linear_combination", "A/B", "B", "加法・乗法 (旧版は語に当たらず A になっていた)"),
]
AMB_CLASS = {"P": "A′"}

ORD_ERASE = words(r"mul_pos\w*", r"mul_nonneg\w*", r"mul_neg_of_\w+", r"mul_le_mul\w*", r"mul_lt_mul\w*",
                  r"mul_le_of_\w+", r"le_mul_of_\w+", r"one_le_mul_of_\w+", r"lt_of_mul_lt_mul_\w+",
                  r"le_of_mul_le_mul_\w+", r"mul_self_nonneg",
                  r"sub_nonneg", r"sub_pos", r"sub_neg", r"sub_nonpos", r"sub_le_sub\w*", r"sub_lt_sub\w*",
                  r"add_pos\w*", r"add_nonneg\w*", r"add_neg\w*", r"add_le_add\w*", r"add_lt_add\w*",
                  r"lt_add_of_\w+", r"neg_nonneg", r"neg_pos",
                  r"Finset\.sum_le_sum\w*", r"Finset\.sum_nonneg", r"Finset\.sum_pos", r"Finset\.sum_eq_zero_iff_of_nonneg",
                  r"sq_nonneg", r"sq_pos\w*", r"pow_pos", r"pow_nonneg", r"abs_nonneg", r"one_pos", r"zero_le_one")

TOK = [
    # (クラス, 表示名, 正規表現)
    ("C", "linarith", words("linarith")),
    ("C", "nlinarith", words("nlinarith")),
    ("C", "positivity", words("positivity")),
    ("C", "le_total", words("le_total")),
    ("C", "lt_or_le", words("lt_or_le", "lt_or_ge")),
    ("C", "le_or_lt", words("le_or_lt", "le_or_gt")),
    ("C", "lt_trichotomy", words("lt_trichotomy")),
    ("C", "not_lt/not_le", words("not_lt", "not_le", "lt_of_not_ge", "lt_of_not_le", "le_of_not_lt", "le_of_not_gt", "not_lt_of_ge")),
    ("C", "abs_*", re.compile(r"(?<![\w.'])abs_\w+|(?<=[\s(\[,=<≤+\-*/])\|(?=[^\s|])[^|\n]*?(?<=[^\s|])\|(?=[\s)\],=<≤+\-*/]|$)")),
    ("C", "sq_abs", words("sq_abs")),
    ("C", "max/min", words(r"max", "min", r"max_\w+", r"min_\w+", r"le_max_\w+", r"min_le_\w+")),
    ("D", "field_simp", words("field_simp")),
    ("D", "div_*", words(r"div_\w+", r"mul_div\w*", r"div_mul\w*")),
    ("D", "one_div", words("one_div")),
    ("D", "零因子なし・簡約", words("mul_eq_zero", "mul_ne_zero", "pow_ne_zero", "pow_eq_zero_iff", "eq_zero_or_eq_zero_of_mul_eq_zero", "mul_left_cancel₀", "mul_right_cancel₀")),
    ("D", "eq_div_*", words("eq_div_iff", "eq_div_of_mul_eq", "div_eq_iff")),
    ("D", "inv_*", words(r"inv_\w+", r"mul_inv\w*", "inv_eq_one_div")),
    ("E", "norm_num", words("norm_num")),
    ("E", "型変換", words("exact_mod_cast", "norm_cast", "push_cast")),
    ("E", "Real.*", re.compile(r"(?<![\w'])Real\.\w+")),
    ("P", "順序付き環の補題(除算)", ORD_KEEP),
    ("B", "ring", words("ring", "ring_nf", "noncomm_ring", "abel", "group", "linear_combination", "one_mul", "zero_add", "zero_mul", "eq_sub_of_add_eq")),
    ("B", "mul_*", words(r"mul_\w+", "mul_comm", "mul_assoc")),
    ("B", "add_*", words(r"add_\w+", "add_comm", "add_assoc")),
    ("B", "sub_*", words(r"sub_\w+")),
    ("B", "sq_*", words(r"sq_\w+", r"pow_\w+")),
    ("B", "Finset.sum_*", re.compile(r"(?<![\w'])Finset\.sum_\w+")),
    ("A", "lt_irrefl", words("lt_irrefl")),
    ("A", "le_trans", words("le_trans")),
    ("A", "le_antisymm", words("le_antisymm")),
    ("A", "le_refl", words("le_refl")),
]
ORDER = "CDEPBA"  # 強い順 (P = A′ 順序付き環)
SHOW = {"P": "A′"}  # 表示名
# 除算・逆元の記号 (/ ⁻¹) は D の字面として数える。ただし a/h は確率関係の記法で除算ではないので、
# 文面ではなく 'field_simp' 等の語のみで D を数える (記号では数えない)。


def strip_comments(text):
    """/- ... -/ ブロックと -- 行コメント、文字列を除く (行数は保つ)。"""
    def blank(m):
        return re.sub(r"[^\n]", " ", m.group(0))
    text = re.sub(r"/-.*?-/", blank, text, flags=re.S)
    text = re.sub(r"--[^\n]*", blank, text)
    return text


def split_units(path):
    """(宣言名, 開始行, 本文, 種別, 名前空間つきの完全名) の列。次の行頭の宣言・コマンドまでを本文とする。"""
    with open(path, encoding="utf-8") as fh:
        raw = fh.read()
    lines = strip_comments(raw).split("\n")
    units, cur = [], None
    scopes = []  # namespace なら名前、section なら ""
    for i, ln in enumerate(lines, 1):
        if ln and not ln[0].isspace():
            m = UNIT.match(ln)
            if m:
                if cur:
                    units.append(cur)
                name = m.group(2) or f"example@{i}"
                full = ".".join([x for x in scopes if x] + [name])
                cur = [name, i, [ln], m.group(1), full]
                continue
            if ANY_DECL.match(ln) or ln.startswith("#") or re.match(r"^(open|end|namespace|section)\b", ln):
                if cur:
                    units.append(cur)
                cur = None
                mn = re.match(r"^namespace\s+(\S+)", ln)
                if mn:
                    scopes.append(mn.group(1))
                elif re.match(r"^section\b", ln):
                    scopes.append("")
                elif re.match(r"^end\b", ln) and scopes:
                    scopes.pop()
                continue
        if cur:
            cur[2].append(ln)
    if cur:
        units.append(cur)
    return [(n, s, "\n".join(b), k, f) for n, s, b, k, f in units]


# 公理の分類表 (完全一致、先に当たった行を採る)。(名前の正規表現, クラス, 根拠の演算)
# 証明本文でこの名前を使うと、使った側の class_trans がこのクラスまで上がる。
AXIOM_RULES = [
    (r"def_IX(_i)?", "B", "和 (ab/h + ab̄/h = a/h)"),
    (r"def_X_(left|right)(_i)?", "B", "積 (ab/h = a/bh · b/h)"),
    (r"def_XII", "B", "和と差 (P + Q = R ならば P = R − Q)"),
    (r"ax_iva_(mul|add)", "B", "和・積の交換律"),
    (r"ax_ivb", "P", "順序付き環 (0 < Q ならば P < P + Q。裁定 F32.7: B ではなく A′)"),
    (r"ax_ivc", "B", "和の簡約"),
    (r"ax_v", "B", "和の結合・交換"),
    (r"ax_vi", "B", "積の分配律"),
    (r"def_XI(_i)?", "D", "除算 (PQ = R ならば P = R/Q、Q ≠ 0)"),
    (r"ax_mae(_prop)?|ax_vii(_i)?", "D", "p/n の値 (自然数の除算を含む存在。裁定 F32.8: D のまま)"),
    (r"ax_ii|ax_iii_\w+|def_VIII_i(_src)?", "A", "値の等式 (= 1 の前件・後件の移し替え)"),
    (r"cons_of_pos(_src)?|cons_iff_taut|cons_true", "A", "値 ≠ 0 と Cons の関係"),
    (r"ax_range_(lo|hi)(_i)?", "A", "値域 0 ≤ P ≤ 1 (順序のみ)"),
    (r"ax_vi_(mono|compl|equiv)|th_12_i", "A", "等式・単調性 (加法・乗法は使わない)"),
]


def axiom_info(name):
    for rx, cls, basis in AXIOM_RULES:
        if re.fullmatch(rx, name):
            return cls, basis
    return None, None  # 原始概念 (Pr・Cons・IProp・iand など): ℝ の演算を使わない


def classify(name, body, local_names):
    found = {}
    # 宣言名そのものと同じファイルで宣言された名前は語彙に数えない
    scrub = body
    for n in sorted(local_names, key=len, reverse=True):
        if n:
            scrub = re.sub(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'])", " ", scrub)
    k = len(ORD_ERASE.findall(scrub))
    if k:
        found.setdefault("P", {})["順序付き環の補題"] = k
        scrub = ORD_ERASE.sub(" ", scrub)
    for cls, label, rx in TOK:
        k = len(rx.findall(scrub))
        if k:
            found.setdefault(cls, {})[label] = k
    cls = next((c for c in ORDER if c in found), "A")
    tac = []
    for c in ORDER:
        for label, k in found.get(c, {}).items():
            tac.append(f"{label}×{k}" if k > 1 else label)
    return cls, tac


def collect():
    rows = []
    axioms = {}  # {ファイル: {公理名: (クラス, 根拠)}}
    per_file_grep = {}
    for path in sorted(glob.glob(os.path.join(PHASES, "keynes_part_ii_*.lean"))):
        stem = os.path.basename(path)
        with open(path, encoding="utf-8") as fh:
            raw = fh.read()
        per_file_grep[stem] = sum(1 for ln in raw.split("\n") if re.match(r"(theorem|lemma|example)", ln))
        units = split_units(path)
        # 同じファイルで宣言された名前 (def・theorem 等) を集める
        local = set()
        axioms[stem] = {}
        for ln in raw.split("\n"):
            m = re.match(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|axiom|structure|inductive|class|instance)\s+([^\s:({\[]+)", ln)
            if m:
                local.add(m.group(2).split(".")[-1])
                if m.group(1) == "axiom":
                    axioms[stem][m.group(2)] = axiom_info(m.group(2))
        for name, line, body, kind, full in units:
            cls, tac = classify(name, body, local)
            rows.append({"file": stem, "theorem": name, "full": full, "kind": kind, "class": cls,
                         "tactics": " ".join(tac), "line": line, "body": body})
    return rows, per_file_grep, axioms


def add_transitive(rows, axioms):
    """class_trans: 同じファイルの theorem/lemma の呼び出しと公理の使用を本文から辿った最強の分類。"""
    by_file = {}
    for r in rows:
        by_file.setdefault(r["file"], {})[r["theorem"]] = r
    for f, d in by_file.items():
        names = [n for n in d if not n.startswith("example@")]
        rx = {n: re.compile(r"(?<![\w.'])" + re.escape(n.split(".")[-1]) + r"(?![\w'])") for n in names}
        deps = {n: [m for m in names if m != n and rx[m].search(d[n]["body"])] for n in names}
        ax_rx = {a: words(re.escape(a)) for a, (c, _) in axioms.get(f, {}).items() if c}
        memo = {}

        def trans(n, stack=()):
            if n in memo:
                return memo[n]
            best = d[n]["class"]
            for a, (c, _) in ((a, axioms[f][a]) for a in ax_rx):
                if ax_rx[a].search(d[n]["body"]) and ORDER.index(c) < ORDER.index(best):
                    best = c
            for m in deps.get(n, []):
                if m in stack:
                    continue
                c = trans(m, stack + (n,))
                if ORDER.index(c) < ORDER.index(best):
                    best = c
            memo[n] = best
            return best
        for n in d:
            d[n]["class_trans"] = trans(n)


# 台帳の略号 → ファイルの対応表 (略号が指すのは 1 本。6c と 7i は本体、モデル・補助の版は別の略号)
ABBREV = {
    "P2": "phase2", "pilot": "pilot", "3a": "phase3a", "3b": "phase3b", "3c": "phase3c", "3d": "phase3d",
    "4": "phase4", "5": "phase5", "6a": "phase6a", "6b": "phase6b", "6c": "phase6c",
    "6c_inconsistency": "phase6c_inconsistency", "6c_model": "phase6c_model",
    "6c_necessity": "phase6c_necessity", "6c_skeleton": "phase6c_skeleton",
    "7a": "phase7a", "7b": "phase7b", "7c": "phase7c", "7d": "phase7d", "7e": "phase7e",
    "7g": "phase7g", "7h": "phase7h", "7i": "phase7i", "7i_model": "phase7i_model",
    "8a": "phase8a", "8b": "phase8b", "8c": "phase8c", "8d": "phase8d", "9x": "phase9x",
    "10a": "phase10a", "10b": "phase10b", "10c": "phase10c", "10d": "phase10d", "10e": "phase10e",
    "10f": "phase10f", "10g": "phase10g", "10h": "phase10h",
    "12b": "phase12b_underdetermination",
}


def chapter_of_row(rid):
    return rid.split("-")[0]


# ---- 台帳への写し ----
IDENT = r"[^\W\d][\w.'′!?]*"
REF = re.compile(r"(?<![\w/])(全 phase|\w+(?:,\w+)*)/(" + IDENT + r")((?:\s*[・,、]\s*" + IDENT + r")*)")


def strip_parens(s):
    """括弧の中を消す。台帳の判定には使わない (括弧の中の定理名も拾う、裁定 F32.11)。旧版との差を出すためだけに残す。"""
    out, depth = [], 0
    for ch in s:
        if ch in "(（":
            depth += 1
        elif ch in ")）":
            depth = max(0, depth - 1)
        elif depth == 0:
            out.append(ch)
    return "".join(out)


def file_of_abbrev(ab):
    """台帳の略号 (10c・P2・pilot) からファイル名の集合。全 phase は全ファイル。"""
    if ab == "全 phase":
        return {os.path.basename(p) for p in glob.glob(os.path.join(PHASES, "keynes_part_ii_*.lean"))}
    suffix = ABBREV.get(ab)
    if not suffix:
        return set()
    p = os.path.join(PHASES, f"keynes_part_ii_{suffix}.lean")
    return {os.path.basename(p)} if os.path.exists(p) else set()


def suffixes(full):
    parts = full.split(".")
    return {".".join(parts[i:]) for i in range(len(parts))}


def build_index(rows, axioms):
    """名前 (完全名でも短い名前でも) → [(ファイル, クラス, 公理か, 完全名)]。"""
    idx = {}
    for r in rows:
        if r["kind"] not in ("theorem", "lemma"):
            continue
        for k in suffixes(r["full"]) | suffixes(r["theorem"]):
            idx.setdefault(k, []).append((r["file"], r["class_trans"], False, r["full"]))
    for f, d in axioms.items():
        for a, (c, _) in d.items():
            if c:
                for k in suffixes(a):
                    idx.setdefault(k, []).append((f, c, True, a))
    return idx


NOT_COUNTED = ("参考", "裸記号")  # 台帳で数えない行 (補則 1・3): 「式/記法」欄の値


def ledger_pass(rows, axioms, write):
    """台帳 ch12–17 の各行の「ℝ 依存」。返り値: (章別の本数, 行ごとの情報の列)。"""
    idx = build_index(rows, axioms)
    by_ch, infos = {}, []
    for ch in range(12, 18):
        path = os.path.join(LEDGER, f"ch{ch}.md")
        with open(path, encoding="utf-8") as fh:
            lines = fh.read().split("\n")
        hdr = None
        out = []
        for ln in lines:
            if not ln.startswith("|"):
                out.append(ln)
                if not ln.strip():
                    hdr = None
                continue
            cells = [c.strip() for c in ln.strip().strip("|").split("|")]
            if cells[0] == "行ID":
                hdr = [c for c in cells if c != "ℝ 依存"]
                out.append("| " + " | ".join(hdr + ["ℝ 依存"]) + " |")
                continue
            if cells[0].startswith("---"):
                out.append("| " + " | ".join(["---"] * (len(hdr) + 1)) + " |" if hdr else ln)
                continue
            if not hdr or len(cells) not in (len(hdr), len(hdr) + 1):
                out.append(ln)
                continue
            d = dict(zip(hdr, cells[:len(hdr)]))
            lean = d.get("既存の Lean", "")
            items, items_out = [], []  # items = 括弧の中も含めて拾った参照、items_out = 括弧の外だけ (旧版の拾い方)
            if d.get("式/記法") not in NOT_COUNTED:
                for text, acc in ((lean, items), (strip_parens(lean), items_out)):
                    for m in REF.finditer(text):
                        files = set()
                        for ab in m.group(1).split(","):
                            files |= file_of_abbrev(ab)
                        if not files:
                            continue
                        names = [m.group(2)] + [n for n in re.split(r"\s*[・,、]\s*", m.group(3)) if n]
                        for n in names:
                            for (f, c, is_ax, full) in idx.get(n, []):
                                if f in files and (c, is_ax, full) not in [(x[1], x[2], x[3]) for x in acc]:
                                    acc.append((f, c, is_ax, full))
            paren_only = [it for it in items if it[3] not in {x[3] for x in items_out}]
            best_out = None
            for it in items_out:
                if best_out is None or ORDER.index(it[1]) < ORDER.index(best_out):
                    best_out = it[1]
            best = None
            for it in items:
                if best is None or ORDER.index(it[1]) < ORDER.index(best):
                    best = it[1]
            val = SHOW.get(best, best) if best else "—"
            if val == "—":
                if d.get("式/記法") in NOT_COUNTED:
                    why = "数えない行 (" + d["式/記法"] + ")"
                elif lean.startswith("未"):
                    why = "未対応 (定義のみ・境界の記録・Lean に無い)"
                else:
                    why = "定義のみ・記法のみ (Lean 欄が def・原始概念・記号を指し、定理・公理を指さない)"
            else:
                why = ""
            by_ch.setdefault(f"ch{ch}", {}).setdefault(val, 0)
            by_ch[f"ch{ch}"][val] += 1
            infos.append({"id": cells[0], "item": d.get("項目ID", ""), "val": val, "items": items, "why": why,
                          "paren_only": paren_only, "val_out": SHOW.get(best_out, best_out) if best_out else "—"})
            out.append("| " + " | ".join(cells[:len(hdr)] + [val]) + " |")
        if write:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("\n".join(out))
    return by_ch, infos


def ranges(ids):
    """行 ID の列を ch14-087, 089, 090 の形にまとめる。"""
    out, last = [], None
    for i in ids:
        ch, num = i.split("-")
        out.append(i if ch != last else num)
        last = ch
    return ", ".join(out)


NOTE_EX = "✎ 行は反例 (数値模型) の E を含むため強めに出る。"
README_HEAD = "## ℝ 依存 A〜E の本数 (第II部)"


def readme_section(n_files, n_rows, tot, tot_t, by_ch):
    gt = {k: 0 for k in ["A", "A′", "B", "C", "D", "E", "—"]}
    for c in by_ch.values():
        for k in gt:
            gt[k] += c.get(k, 0)
    cols = ["A", "A′", "B", "C", "D", "E"]
    lines = [
        README_HEAD, "",
        f"`tools/real_dependence.py` が `phases/keynes_part_ii_*.lean` の theorem・lemma・example {n_rows:,} 本を分類した値 "
        "(洗い出しのみ、判定ではない)。複数に当たるときは C > D > E > A′ > B > A (A′ = 順序付き環、比較可能性は不要)。"
        "台帳 ch12–ch17 の各行の「ℝ 依存」列は、その行の Lean 欄が指す定理・公理の class_trans (呼び先と公理の使用まで辿った最強値) で、"
        "定義のみ・境界の記録・数えない行・未対応は「—」。定義と内訳は `real_dependence.md`・`real_dependence.csv`。", "",
        "表の数字は `python3 -I tools/real_dependence.py --write-ledger --write-readme` の出力を写したもの (手で直さない)。", "",
        "| 単位 | A 順序のみ | A′ 順序付き環 | B 加法・乗法 | C 線形順序 | D 体の構造 | E 数値 | — | 計 |",
        "|---|---|---|---|---|---|---|---|---|",
        f"| 定理・例 (第II部 {n_files} ファイル、class: 字面のみ) | " + " | ".join(f"{tot[c if c != 'A′' else 'P']:,}" for c in cols) + f" | — | {n_rows:,} |",
        f"| 定理・例 (同、class_trans: 呼び先・公理まで) | " + " | ".join(f"{tot_t[c if c != 'A′' else 'P']:,}" for c in cols) + f" | — | {n_rows:,} |",
        f"| 台帳の行 (ch12–ch17、class_trans) | " + " | ".join(f"{gt[c]:,}" for c in cols) + f" | {gt['—']:,} | {sum(gt.values()):,} |",
        "", NOTE_EX, "",
    ]
    return "\n".join(lines)


def write_readme(text):
    path = os.path.join(LEDGER, "README.md")
    with open(path, encoding="utf-8") as fh:
        body = fh.read()
    if README_HEAD in body:
        a = body.index(README_HEAD)
        m = re.search(r"\n## ", body[a + len(README_HEAD):])
        b = a + len(README_HEAD) + m.start() + 1 if m else len(body)
        body = body[:a] + text + ("\n" + body[b:] if m else "")
    else:
        body = body.rstrip("\n") + "\n\n" + text
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(body)


def main():
    write_ledger = "--write-ledger" in sys.argv
    rows, per_file_grep, axioms = collect()
    add_transitive(rows, axioms)
    out_csv = os.path.join(LEDGER, "real_dependence.csv")
    with open(out_csv, "w", encoding="utf-8", newline="") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["file", "theorem", "class", "tactics", "line", "class_trans"])
        for r in rows:
            w.writerow([r["file"], r["theorem"], SHOW.get(r["class"], r["class"]), r["tactics"], r["line"],
                        SHOW.get(r["class_trans"], r["class_trans"])])

    files = sorted({r["file"] for r in rows} | set(per_file_grep))
    cnt = {f: {c: 0 for c in ORDER} for f in files}
    cnt_t = {f: {c: 0 for c in ORDER} for f in files}
    for r in rows:
        cnt[r["file"]][r["class"]] += 1
        cnt_t[r["file"]][r["class_trans"]] += 1
    n_of = {f: sum(cnt[f].values()) for f in files}
    tot = {c: sum(cnt[f][c] for f in files) for c in ORDER}
    tot_t = {c: sum(cnt_t[f][c] for f in files) for c in ORDER}
    CL = "ABCDE"
    SEQ = "APBCDE"  # 表の列順 (内部記号。P = A′)
    HD = "A | A′ | B | C | D | E"

    by_ch, infos = ledger_pass(rows, axioms, write_ledger)

    md = []
    md.append("# ℝ 依存の洗い出し (第II部、B32)\n")
    md.append("`tools/real_dependence.py` が `phases/keynes_part_ii_*.lean` の theorem・lemma・example を 1 本ずつ字面で分類し、"
              "公理の使用と同じファイル内の呼び出しを辿った値を別に出した結果。洗い出しのみで、証明の良し悪しは判定しない。"
              "分類は排他で、複数に当たるときは C > D > E > A′ > B > A。\n")
    md.append("- **A 順序のみ**: ≤ の推移・反対称・反射など、下のどの語にも当たらない\n"
              "- **A′ 順序付き環 (比較可能性は不要)**: `mul_pos`・`mul_nonneg`・`sub_nonneg`・`sub_pos`・`add_pos`・`add_nonneg`・`sq_nonneg`・"
              "`pow_pos`・`abs_nonneg`・`mul_le_mul*`・`add_le_add*`・`div_pos`・`div_nonneg`・`div_le_*` など、名前全体で判定する「順序と環の演算」の補題 "
              "(`div_*` と `inv_pos` 系は D にも当たるので D になる)\n"
              "- **B 加法・乗法**: `ring`・`mul_*`・`add_*`・`sub_*`・`sq_*`・`Finset.sum_*` (A′ の補題名に当たらないもの。線形順序は使わない)\n"
              "- **C 線形順序**: `linarith`・`nlinarith`・`positivity`・`le_total`・`lt_or_le`・`le_or_lt`・`abs_*` (`abs_nonneg` を除く)・`max`/`min` など\n"
              "- **D 体の構造**: `field_simp`・`div_*`・`inv_*`・`one_div`\n"
              "- **E 数値**: `norm_num`・`Real.*`\n")
    md.append("class は宣言の字面に現れる語だけで決める。`class_trans` は、本文で使う同じファイルの別定理と公理まで辿った最強の分類 "
              "(公理は下の表で分類し、`def_IX*`・`def_X_*`・`def_XII`・`ax_iva_*`・`ax_ivc`・`ax_v`・`ax_vi` を B、"
              "`ax_ivb` を A′、`def_XI*`・`ax_mae*`・`ax_vii*` を D とする)。台帳の列は `class_trans` で付ける。\n")
    md.append("## ファイル別 (class)\n")
    md.append(f"| ファイル | 宣言数 | grep 本数 | 一致 | {HD} |")
    md.append("|---|---|---|---|---|---|---|---|---|---|")
    for f in files:
        ok = "○" if n_of[f] == per_file_grep[f] else "×"
        md.append(f"| {f[:-5]} | {n_of[f]} | {per_file_grep[f]} | {ok} | " + " | ".join(str(cnt[f][c]) for c in SEQ) + " |")
    md.append(f"| **第II部合計** | **{sum(n_of.values())}** | **{sum(per_file_grep.values())}** | "
              f"{'○' if sum(n_of.values()) == sum(per_file_grep.values()) else '×'} | "
              + " | ".join(f"**{tot[c]}**" for c in SEQ) + " |\n")
    md.append("(grep 本数 = 各ファイルの `grep -c '^theorem\\|^lemma\\|^example'`)\n")
    md.append("## 直接 (class) と辿った値 (class_trans) の本数\n")
    md.append(f"| | {HD} | 計 |\n|---|---|---|---|---|---|---|---|")
    md.append("| 直接 (class) | " + " | ".join(str(tot[c]) for c in SEQ) + f" | {sum(tot.values())} |")
    md.append("| 呼び先と公理の使用まで (class_trans) | " + " | ".join(str(tot_t[c]) for c in SEQ) + f" | {sum(tot_t.values())} |\n")
    md.append(NOTE_EX + "\n")
    md.append("原則: 迷ったら強い側 (上位のクラス) に置く。少なめに分類して見落とす方が危険だから (人の裁定、2026-10-30)。"
              "迷った語は下の「振り分け表」に挙げる。\n")

    md.append("## 公理の分類 (使うと呼び側の class_trans が上がる)\n")
    md.append("| 公理名 (規則) | クラス | 根拠の演算 |\n|---|---|---|")
    for rx, cls, basis in AXIOM_RULES:
        md.append(f"| `{rx.replace('|', ' / ')}` | {SHOW.get(cls, cls)} | {basis} |")
    md.append("\n`ax_mae`・`ax_mae_prop`・`ax_vii`・`ax_vii_i` は D のまま (自然数 n での除算 p/n を含む存在の主張なので、B にはしない。裁定 F32.8)。"
              "`ax_ivb` は 0 < Q ならば P < P + Q で、加法と順序の両方を使うので B ではなく A′ (裁定 F32.7)。")
    md.append("\n原始概念 (`Pr`・`PrI`・`Cons`・`IProp`・`iand` など) と命題論理の `ktaut_*` は ℝ の演算を使わないので分類しない。\n")

    md.append("## 台帳 ch12 の公理の行\n")
    md.append("Lean 欄が公理を指す行 (定理も併記する行は、定理を含めた最強値が行のクラス)。\n")
    md.append("| 行ID | 項目ID | 公理名 | 公理のクラス | 行のクラス | 根拠の演算 |\n|---|---|---|---|---|---|")
    for x in infos:
        if not x["id"].startswith("ch12-"):
            continue
        axs = sorted({it[3] for it in x["items"] if it[2]})
        if not axs:
            continue
        ainfo = {a: axiom_info(a) for a in axs}
        md.append(f"| {x['id']} | {x['item']} | " + "・".join(f"`{a}`" for a in axs) + " | "
                  + "・".join(SHOW.get(ainfo[a][0], ainfo[a][0]) for a in axs) + f" | {x['val']} | "
                  + "; ".join(sorted({ainfo[a][1] for a in axs})) + " |")
    md.append("")

    md.append("## 章別 (台帳 ch12–ch17 の行ごとの「ℝ 依存」)\n")
    md.append("行の値は、Lean 欄が指す定理・公理の class_trans のうち最強の分類。「—」は定義のみ・境界の記録・数えない行 (参考・裸記号)・"
              "記法のみ。\n")
    keys = ["A", "A′", "B", "C", "D", "E", "—"]
    md.append("| 章 | 行数 | " + " | ".join(keys) + " |")
    md.append("|---|---|---|---|---|---|---|---|---|")
    gt = {k: 0 for k in keys}
    gn = 0
    for ch in sorted(by_ch):
        c = by_ch[ch]
        n = sum(c.values())
        gn += n
        for k in gt:
            gt[k] += c.get(k, 0)
        md.append(f"| {ch} | {n} | " + " | ".join(str(c.get(k, 0)) for k in keys) + " |")
    md.append(f"| **合計** | **{gn}** | " + " | ".join(f"**{gt[k]}**" for k in keys) + " |\n")
    md.append(NOTE_EX + "\n")

    md.append("## 「—」の行\n")
    dash = {}
    for x in infos:
        if x["val"] == "—":
            dash.setdefault(x["why"], []).append(x["id"])
    for why, ids in dash.items():
        md.append(f"- **{why}** ({len(ids)}): {ranges(ids)}")
    md.append("")

    md.append("## Π への移植の見積り\n")
    n_ct = tot_t["C"]
    md.append(f"Π への移植で比較可能性を作り直す要作業は、C {n_ct} 本 (class_trans、呼び先と公理まで辿った値) を上限とする。"
              "下の「比較可能性を直接使う定理」は、`le_total`・`lt_trichotomy`・`le_or_lt`・`le_or_gt` と、同じ働きの `lt_or_le`・`lt_or_ge`・`lt_or_gt_of_ne` を本文で直接使う定理で、"
              "比較可能性が本質的に要る箇所の下限の参考値である (`linarith` 等は比較可能性を暗に使うだけで数えない。"
              "`lt_or_eq_of_le`・`eq_or_lt_of_le` は半順序でも成り立つので数えない)。\n")
    cmp_rx = words("le_total", "lt_trichotomy", "le_or_lt", "le_or_gt", "lt_or_le", "lt_or_ge", "lt_or_gt", "lt_or_gt_of_ne", "lt_by_cases", "ne_iff_lt_or_gt")
    direct = []
    for r in rows:
        blines = r["body"].split("\n")
        for off, ln in enumerate(blines):
            for m in cmp_rx.finditer(ln):
                direct.append((r["file"], r["theorem"], r["line"] + off, m.group(0)))
    seen, uniq = set(), []
    for f, t, ln, w in direct:
        if (f, t) in seen:
            continue
        seen.add((f, t))
        uniq.append((f, t, ln, w))
    md.append(f"### 比較可能性を直接使う定理 ({len(uniq)} 本)\n")
    md.append("| ファイル | 定理 | 行 (最初の使用) | 使う語 |\n|---|---|---|---|")
    for f, t, ln, w in uniq:
        md.append(f"| {f[:-5]} | `{t}` | {ln} | `{w}` |")
    md.append("")

    md.append("## 振り分け表 (迷った語は上位に置く)\n")
    md.append("語の振り分けで A か A′ か、B か D か迷うときは上位のクラスに置いた (裁定 2026-10-30)。"
              "旧版で語に当たらず A になっていたものは、迷う語として挙げて上げた。"
              "整域の性質 (`mul_eq_zero`・`mul_ne_zero`・`eq_zero_or_eq_zero_of_mul_eq_zero` など零因子が無いこと) は D 扱い (強い側、裁定 F32.14)。\n")
    md.append("| 語 (正規表現) | 迷った候補 | 置いたクラス | 理由 | 使う定理の本数 (class の字面) |\n|---|---|---|---|---|")
    for rx, cands, cl, why in AMBIGUOUS:
        crx = re.compile(r"(?<![\w.'])(?:" + rx + r")(?![\w'])")
        k = sum(1 for r in rows if crx.search(r["body"]))
        md.append(f"| `{rx.replace(chr(124), ' / ')}` | {cands} | {AMB_CLASS.get(cl, cl)} | {why} | {k} |")
    md.append("")

    md.append("## 括弧の中の定理名から拾った台帳の行\n")
    md.append("台帳の Lean 欄は括弧の中の定理名も拾う (括弧を消さない、裁定 F32.11)。括弧の外だけで拾った旧版と比べて、"
              "拾う参照が増えた行を挙げる (値が変わった行は → で示す)。"
              "Lean 欄が「未」でも括弧内に定理名があれば拾って値を付ける (強い側に倒す裁定、2026-10-30。例: ch14-156・ch17-134)。\n")
    pr = [x for x in infos if x["paren_only"]]
    md.append(f"{len(pr)} 行。\n")
    md.append("| 行ID | 項目ID | 括弧の中から拾った定理・公理 | 旧版の値 → 新しい値 |\n|---|---|---|---|")
    for x in pr:
        md.append(f"| {x['id']} | {x['item']} | " + "・".join(f"`{it[3]}` ({it[0][len('keynes_part_ii_'):-5]}, {SHOW.get(it[1], it[1])})" for it in x["paren_only"])
                  + f" | {x['val_out']} → {x['val']} |")
    md.append("")

    md.append("## クラス C の定理 (Π への移植で比較可能性が要る箇所)\n")
    cs = [r for r in rows if r["class"] == "C"]
    md.append(f"{len(cs)} 本 (class が C のもの)。ファイル別に定理名を並べる。\n")
    grouped = {}
    for r in cs:
        grouped.setdefault(r["file"], []).append(f"`{r['theorem']}`")
    for f, names in grouped.items():
        md.append(f"- **{f[:-5]}** ({len(names)}): " + "・".join(names))
    md.append("")
    with open(os.path.join(LEDGER, "real_dependence.md"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(md).replace("\n\n\n", "\n\n") + "\n")

    if "--write-readme" in sys.argv:
        write_readme(readme_section(len(files), len(rows), tot, tot_t, by_ch))

    print(f"theorems={len(rows)} grep={sum(per_file_grep.values())} files={len(files)}")
    print("direct:", " ".join(f"{SHOW.get(c, c)}={tot[c]}" for c in SEQ))
    print("trans: ", " ".join(f"{SHOW.get(c, c)}={tot_t[c]}" for c in SEQ))
    print("ledger:", " ".join(f"{k}={gt[k]}" for k in keys), "rows=", gn)
    bad = [f for f in files if n_of[f] != per_file_grep[f]]
    for f in bad:
        print("MISMATCH", f, n_of[f], per_file_grep[f])
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
