# check_ja_titles.py — 日本語版の章題 (gen.py の辞書 L["ja"]["ch_title"]) を、訳書目次と照合する。
# 照合は 2 通りで、どちらかで確かめられれば 1 題が確認済みになる。
#   (1) OCR 一致: 目次 OCR (p9〜p11.txt) の行を順に連ねた文字列の中に、「第<章番号>章」+ 題を正規化した文字列が
#       この順で連続して現れる。「第Ⅲ部への注」は章番号を持たないので、題だけを探す。
#   (2) 画像で確認: OCR が文字を落とす題は、目次頁の画像を目で読んだ題を表ファイルに記録し、辞書の題と
#       正規化した上で 1 字ずつ比べる。表ファイルの画像の欄が指す画像が、表ファイルと同じ場所に在ることも確かめる。
#       画像は repo に置かない (訳書の切り抜きは公開 repo に入れない) ので、表ファイルも画像と同じ場所に置く。
# 正規化: NFKC (全角半角・ローマ数字 Ⅰ→I)、空白・読点・句点・中黒・点線・ダッシュ・括弧を除く。
#         OCR 行の先頭にある座標 (「 429 x 674 」) と、行頭の「#」の見出し行は捨てる。
#         文字の欠落や頁数の混入は補わない (補えば照合が甘くなる)。
#         長音「ー」とダッシュ類は除くので、これらの有無・種類の違いは、OCR 一致でも画像確認でも検出できない
#         (照合が少し甘くなる)。
# 確認済みが全題に満たなければ終了コード 1。check_all.sh には入れない (OCR と画像は materials 側にあるため)。
# 使い方: python3 -I tools/atlas/check_ja_titles.py <OCR を置いたディレクトリ> [<画像確認の表ファイル>]
#   (OCR ディレクトリの p9.txt, p10.txt, p11.txt を読む)
# 表ファイル (UTF-8、タブ区切り、# で始まる行は無視): <key> TAB <画像の相対パス> TAB <画像で読んだ題 (章番号を除く)>
import importlib.util
import os
import re
import sys
import unicodedata

sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location(
    "atlas_gen", os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen.py"))
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)

PAGES = ("p9.txt", "p10.txt", "p11.txt")
COORD = re.compile(r"^\s*\d+\s*x\s*\d+\s?")
DROP = re.compile(r"[\s,.、。，．・･…⋯―—–\-ー‐〜~「」『』()（）\[\]:：;；'’\"]")


def norm(s):
    return DROP.sub("", unicodedata.normalize("NFKC", s))


def read_ocr(d):
    lines = []
    for name in PAGES:
        with open(os.path.join(d, name), "rb") as f:
            b = f.read()
        try:
            t = b.decode("utf-8")
        except UnicodeDecodeError:
            t = b.decode("cp932")
        for ln in t.splitlines():
            if ln.startswith("#"):
                continue
            lines.append(COORD.sub("", ln))
    return lines


def read_image_table(path):
    """key -> (画像の相対パス, 画像で読んだ題)。画像が表ファイルと同じ場所に無い行は捨てる。"""
    table = {}
    if not path:
        return table
    base = os.path.dirname(os.path.abspath(path))
    with open(path, encoding="utf-8") as f:
        for ln in f:
            ln = ln.rstrip("\r\n")
            if not ln or ln.startswith("#"):
                continue
            key, img, read = ln.split("\t")
            if os.path.isfile(os.path.join(base, img)):
                table[key] = (img, read)
    return table


def main():
    lines = read_ocr(sys.argv[1])
    images = read_image_table(sys.argv[2] if len(sys.argv) > 2 else None)
    normed = [norm(ln) for ln in lines]
    joined = "".join(normed)
    titles = G.L["ja"]["ch_title"]
    n_ocr = n_img = bad = 0
    print("key\tneedle\tOCR 一致\t画像で確認\t画像\tnear")
    for key in G.ORDER:
        title = titles[key]
        if key.startswith("ch"):
            needle = norm(f"第{int(key[2:])}章" + title)
        else:
            needle = norm(title)
        ocr_ok = needle in joined
        img_ok = False
        img = ""
        if key in images:
            img, read = images[key]
            img_ok = norm(read) == norm(title)
        n_ocr += ocr_ok
        n_img += (not ocr_ok) and img_ok
        near = ""
        if not (ocr_ok or img_ok):
            bad += 1
            # 題の先頭 4 文字を含む OCR 行を近傍として添える (目視の手がかり)
            head = norm(title)[:4]
            near = " | ".join(ln.strip() for ln, nl in zip(lines, normed) if head in nl)[:80]
        print(f"{key}\t{needle}\t{'一致' if ocr_ok else '欠落'}\t{'一致' if img_ok else '-'}\t{img}\t{near}")
    total = len(G.ORDER)
    print(f"OCR 一致 {n_ocr} + 画像で確認 {n_img} = {n_ocr + n_img} / {total}", file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
