# Formula atlas (1921 first edition)

The atlas puts every row of the census ledger (`docs/全数台帳/chNN.md`) beside a crop of the printed line it records, so that the transcription and the Lean entry can be checked against the page itself. One HTML page per chapter, in English; the ledger's remarks and Lean entries are quoted as written. Chapter 20 is the trial run (`ch20/index.html`, 40 cards from 24 crops).

## Index, navigation and filters
- **Index page** (`index.html`): the totals of the census (formula lines, items, items stated in Lean, numbered items, lines in a theorem statement), a table by part, and the list of all 33 chapters and the Notes on Part III with links to their pages. Every number is computed from the ledger files.
- **Navigation**: each chapter page has a line at the top and at the bottom leading back to the index and to the previous and next chapter (the Notes on Part III follow Chapter 23).
- **Filters**: under the summary table of a chapter page, buttons show all cards, only the ✓ / ≈ / ✎ / not-yet formula rows, or only the notation rows. Without JavaScript the buttons stay hidden and every card is shown.

## Source of the images
J. M. Keynes, *A Treatise on Probability*, London: Macmillan, 1921 (first edition), Cornell University Library copy, scanned PDF. **PDF page = folio + 20** for the pages used here (checked against the page number in the PDF text layer). Pages are rendered at the scan's native size, 1445 × 2408 px, by the pure-Python tools in `原典照合1921/render_tool/` (`pdf_pages.py`, then `batch_render.py`; outside this repository). Crops are inverted to black on white, cut to the text column (x 125–1335) with an 8 px margin.

## Rebuilding a chapter
```
python3 -I tools/atlas/crops.py <hires_dir> docs/atlas/ch20/coords.json docs/atlas/ch20/img
python3 -I tools/atlas/gen.py docs/全数台帳/ch20.md docs/atlas/ch20/coords.json docs/atlas/ch20/index.html
```
`<hires_dir>` holds the full-size `folio_<N>.png` renderings. `coords.json` gives, for each ledger row, the folio, the pixel band `[y0, y1)` and `[x0, x1)`, and the image name; rows on the same printed line, or in the same display block, share one image. Within the band, ink is split into 8-connected components and a component is kept only if most of its pixels lie inside the band, so ascenders and descenders of neighbouring lines are not drawn. Counts on the page are computed from the ledger, never typed. Both scripts are deterministic: rerunning them gives byte-identical output.

After any chapter page is rebuilt, rebuild the index (it reads the ledger files, `summary.csv` and the chapter pages, and reports any disagreement between `summary.csv` and the ledger):
```
python3 -I tools/atlas/gen_index.py docs/全数台帳 docs/atlas docs/atlas/index.html
```

## Effort
Chapter 20 (9 folios, formulas on 4 of them, 40 rows, 24 crops): about 30 minutes to fix the coordinates (a line-profile listing of each page, reading the page, then a per-row profile where footnote lines touch), plus a visual check of every crop.
