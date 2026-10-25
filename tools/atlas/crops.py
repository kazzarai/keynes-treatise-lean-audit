# crops.py — render_tool が書いた原寸 PNG (背景 0 / 文字 255) から矩形を切り出し、
# 白地・黒文字に反転して上下左右に白余白を付けて書き出す。
# 原典照合1921/crops_pssj/crops.py (B00_0) の複製で、座標表を JSON ファイルから読む形に改めた。
# 行間が詰まった箇所 (隣の行のディセンダ/アセンダが同じ画素行に入る) に対応するため、
# 帯の中のインクを連結成分 (8 近傍) に分け、画素の過半が [y0, y1) に入る成分だけを残す。
# 残した成分は枠の外へはみ出す分も含めて丸ごと描き、残さなかった成分の画素は白にする。
# 出力の上下端は残した成分の最上・最下の画素行から PAD px、左右は本文段の幅 x0–x1 から PAD px。
# 座標表: [{"id": "ch20-002", "folio": 235, "y0": …, "y1": …, "x0": 125, "x1": 1335, "img": "…png"}, …]
#   y1・x1 は排他。複数の行 ID が同じ img を指してよい (その場合 folio と座標は一致していなければならない)。
# 使い方: python3 -I crops.py <hires_dir> <coords.json> <out_dir>
import json
import os
import struct
import sys
import zlib

PAD = 8  # 白余白 (px)
BAND = 60  # 成分を調べる帯の上下の余裕 (px)


def read_gray(path):
    data = open(path, "rb").read()
    assert data[:8] == b"\x89PNG\r\n\x1a\n"
    i = 8
    idat = b""
    while i < len(data):
        ln = struct.unpack(">I", data[i:i + 4])[0]
        tag = data[i + 4:i + 8]
        body = data[i + 8:i + 8 + ln]
        if tag == b"IHDR":
            w, h, bd, ct = struct.unpack(">IIBB", body[:10])
            assert bd == 8 and ct == 0
        elif tag == b"IDAT":
            idat += body
        i += 12 + ln
    raw = zlib.decompress(idat)
    rows = []
    for y in range(h):
        assert raw[y * (w + 1)] == 0  # フィルタ無し行のみを想定
        rows.append(raw[y * (w + 1) + 1:(y + 1) * (w + 1)])
    return w, h, rows


def chunk(tag, body):
    c = struct.pack(">I", len(body)) + tag + body
    return c + struct.pack(">I", zlib.crc32(tag + body) & 0xFFFFFFFF)


def write_gray(path, rows):
    ow = len(rows[0])
    oh = len(rows)
    raw = b"".join(b"\x00" + bytes(r) for r in rows)
    png = b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", ow, oh, 8, 0, 0, 0, 0))
    png += chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b"")
    open(path, "wb").write(png)
    return ow, oh


def components(rows, w, ya, yb):
    # 帯 [ya, yb) のインク画素を 8 近傍で連結成分に分ける。戻り値は画素座標のリストのリスト。
    seen = set()
    comps = []
    for y in range(ya, yb):
        r = rows[y]
        for x in range(w):
            if r[x] > 127 and (x, y) not in seen:
                seen.add((x, y))
                stack = [(x, y)]
                pix = []
                while stack:
                    px, py = stack.pop()
                    pix.append((px, py))
                    for dy in (-1, 0, 1):
                        ny = py + dy
                        if ny < ya or ny >= yb:
                            continue
                        nr = rows[ny]
                        for dx in (-1, 0, 1):
                            nx = px + dx
                            if 0 <= nx < w and nr[nx] > 127 and (nx, ny) not in seen:
                                seen.add((nx, ny))
                                stack.append((nx, ny))
                comps.append(pix)
    return comps


def load_table(path):
    # 行 ID の並びから画像ごとの切り抜き指定を作る。同じ img を指す行は座標が一致することを確かめる。
    table = {}
    ids = {}
    for e in json.load(open(path, encoding="utf-8")):
        key = (e["folio"], e["y0"], e["y1"], e["x0"], e["x1"])
        if e["img"] in table:
            assert table[e["img"]] == key, (e["id"], e["img"], table[e["img"]], key)
        else:
            table[e["img"]] = key
        ids.setdefault(e["img"], []).append(e["id"])
    return table, ids


hires, coords, out = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(out, exist_ok=True)
table, ids = load_table(coords)
cache = {}
for name, (folio, y0, y1, X0, X1) in table.items():
    src = f"{hires}/folio_{folio}.png"
    if not os.path.exists(src):
        src = f"{hires}/folio_{int(folio):03d}.png"  # img_all/hires/ は 3 桁ゼロ埋め
    if src not in cache:
        cache[src] = read_gray(src)
    w, h, rows = cache[src]
    ya, yb = max(0, y0 - BAND), min(h, y1 + BAND)
    keep = []
    notes = []
    for pix in components(rows, w, ya, yb):
        inside = sum(1 for _, py in pix if y0 <= py < y1)
        if max(px for px, _ in pix) < X0 or min(px for px, _ in pix) >= X1:
            # 本文段の外 (頁端の汚れ) は描かない
            if inside:
                notes.append(f"margin noise {len(pix)}px dropped")
            continue
        if 2 * inside > len(pix):
            keep.extend(pix)
            out_rows = sorted({py for _, py in pix if not (y0 <= py < y1)})
            if out_rows:
                notes.append(f"kept {len(pix)}px spills y{out_rows[0]}-{out_rows[-1]}")
        elif inside:
            notes.append(f"dropped {len(pix)}px with {inside}px inside")
    ky0 = min(py for _, py in keep)
    ky1 = max(py for _, py in keep) + 1
    kx0 = min(px for px, _ in keep)
    kx1 = max(px for px, _ in keep) + 1
    assert X0 <= kx0 and kx1 <= X1, (name, kx0, kx1)
    ow = X1 - X0 + 2 * PAD
    canvas = [bytearray(b"\xff" * ow) for _ in range(ky1 - ky0 + 2 * PAD)]
    for px, py in keep:
        canvas[py - ky0 + PAD][px - X0 + PAD] = 255 - rows[py][px]
    ow, oh = write_gray(f"{out}/{name}", canvas)
    print(f"{name}  folio {folio}  pdf {folio + 20}  crop x{X0}-{X1} y{ky0}-{ky1}  ink x{kx0}-{kx1}"
          f"  out {ow}x{oh}  rows {' '.join(ids[name])}")
    for n in notes:
        print("   ", n)
