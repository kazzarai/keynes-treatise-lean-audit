# gen_summary.py — docs/全数台帳/summary.csv を台帳 (chNN.md・notes_III.md) から再計算する。
# 再計算する列: folio_from・folio_to・式・項目数・記法・✓・≈・✎・未(式)・記法のLean対応・外・定。
#   数え方は gen.py の summary() と同じ (gen_index.py が突き合わせる値と同一)。
# 書き換えない列: 章・題・うち番号付き (番号付きは章により数え方が違うので、台帳の集計表に従って手で保つ)。
# 「外」は第五の判定 (外部公理依存)、「定」は第六の判定 (定義対応) の式の行の数で、列は末尾に足す (既存の列の位置は変えない)。
# 改行は元のファイルに合わせて CRLF。出力は入力だけで決まる。何度回しても同じ。
# gen_index.py の前に回す。
# --check: summary.csv を書き換えず、台帳から再計算した内容とバイト単位で一致するかだけを調べる (違えば終了コード 1)。
# 使い方: python3 -I tools/atlas/gen_summary.py [--check] <ledger_dir>   (summary.csv は <ledger_dir>/summary.csv)
import csv
import io
import importlib.util
import os
import sys

sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location(
    "atlas_gen", os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen.py"))
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)

EXT_COL = "外"
DEF_COL = "定"


def main():
    args = sys.argv[1:]
    check = "--check" in args
    if check:
        args.remove("--check")
    ledger_dir = args[0]
    path = os.path.join(ledger_dir, "summary.csv")
    with open(path, encoding="utf-8", newline="") as f:
        rd = csv.DictReader(f)
        head = list(rd.fieldnames)
        old = list(rd)
    for col in (EXT_COL, DEF_COL):
        if col not in head:
            head.append(col)
    out = []
    for r in old:
        c = "notes_III" if r["章"] == "N3" else f"ch{int(r['章']):02d}"
        _, _, (fa, fb, _, _), rows = G.read_ledger(os.path.join(ledger_dir, f"{c}.md"))
        s = G.summary(rows)
        mk = s["marks"]
        r.update({"folio_from": fa, "folio_to": fb, "式": s["formula"], "項目数": s["items"],
                  "記法": s["notation"], "✓": mk["✓"], "≈": mk["≈"], "✎": mk["✎"], "未(式)": mk["未"],
                  "記法のLean対応": s["n_lean"], EXT_COL: mk["外"], DEF_COL: mk["定"]})
        out.append(r)
    buf = io.StringIO(newline="")
    w = csv.DictWriter(buf, fieldnames=head, lineterminator="\r\n")
    w.writeheader()
    w.writerows(out)
    new = buf.getvalue().encode("utf-8")
    if check:
        with open(path, "rb") as f:
            if f.read() != new:
                sys.exit("summary.csv が台帳から再計算した内容と一致しない (gen_summary.py で作り直す)")
    else:
        with open(path, "wb") as f:
            f.write(new)
    print(f"summary.csv: {len(out)} chapters, formulas {sum(int(r['式']) for r in out)}, "
          f"外 {sum(int(r[EXT_COL]) for r in out)}, 定 {sum(int(r[DEF_COL]) for r in out)}")


if __name__ == "__main__":
    main()
