#!/bin/bash
# check_all — mechanical gate for this repository.
# Stages: 0 Mathlib cache present; 1 every phase compiles (exit 0, no "error"); 2 no sorryAx;
#         3 verdict count -> logs/progress.json (phases/ only);
#         1i no phases/*.lean imports others/;
#         1o/2o every others/**/*.lean compiles and has no sorryAx (comparison files, no ledger rows;
#           NOT counted in [3]); `import phases.X` / `import others.X` are first compiled with
#           `lean -R . -o` into a temporary directory that is put on LEAN_PATH;
#         4 every name cited in docs/全数台帳 (Lean column and notes column) exists in phases/
#           (tools/check_ledger_refs.py, no MISSING);
#         8 hygiene (no local absolute paths);
#         9 atlas generators agree with the ledgers (gen.py --check on every ledger, gen_summary.py --check,
#           gen_index.py --missing-ok with no WARN, gen_readme_totals.py --check on docs/全数台帳/README.md);
#           nothing under docs/ is rewritten.
# Usage: bash tools/check_all.sh [phases/file.lean | others/.../file.lean ...]
#        (default: all phases and all others)
set -u
cd "$(dirname "$0")/.." || exit 1
red=0; mkdir -p logs
LOG="logs/check_$(date -u +%Y%m%dT%H%M%SZ).log"
echo "=== check_all $(date -u +%FT%TZ) $(lake env lean --version 2>/dev/null) ===" | tee "$LOG"
n=$(find .lake/packages/mathlib/.lake/build/lib -name "*.olean" 2>/dev/null | wc -l | tr -d ' ')
if [ "$n" -lt 1000 ]; then echo "[0] RED: Mathlib oleans missing ($n). Run: lake exe cache get" | tee -a "$LOG"; red=1; else echo "[0] ok mathlib oleans=$n" | tee -a "$LOG"; fi
FILES=(); OFILES=()
if [ $# -eq 0 ]; then
  FILES=(phases/*.lean)
  while IFS= read -r f; do OFILES+=("$f"); done < <(find others -name '*.lean' 2>/dev/null | sort)
else
  for a in "$@"; do case "$a" in others/*) OFILES+=("$a");; *) FILES+=("$a");; esac; done
fi
total=0
for f in ${FILES[@]+"${FILES[@]}"}; do
  out=$(lake env lean "$f" 2>&1); ec=$?
  printf '%s\n' "$out" >> "$LOG"
  c=$(printf '%s\n' "$out" | grep -c "depends on axioms"); total=$((total+c))
  if [ $ec -ne 0 ] || printf '%s\n' "$out" | grep -q "error"; then echo "[1] RED compile: $f" | tee -a "$LOG"; red=1; else echo "[1] ok $f ($c verdicts)" | tee -a "$LOG"; fi
  if printf '%s\n' "$out" | grep -q "sorryAx"; then echo "[2] RED sorryAx: $f" | tee -a "$LOG"; red=1; fi
done
if [ ${#FILES[@]} -gt 0 ]; then
  printf '{"verdicts": %d, "files": %d, "date": "%s"}\n' "$total" "${#FILES[@]}" "$(date -u +%F)" > logs/progress.json
  echo "[3] verdicts=$total files=${#FILES[@]} -> logs/progress.json" | tee -a "$LOG"
else echo "[3] skipped: no phases/ file given (logs/progress.json unchanged)" | tee -a "$LOG"; fi
# [1i] phases/ never import others/ (Keynes-side theorems cannot depend on comparison files)
bad=$(grep -lE '^[[:space:]]*import[[:space:]]+others([.[:space:]]|$)' phases/*.lean 2>/dev/null)
if [ -n "$bad" ]; then echo "[1i] RED phases import others/:" | tee -a "$LOG"; printf '%s\n' "$bad" | tee -a "$LOG"; red=1
else echo "[1i] ok no phases/*.lean imports others/" | tee -a "$LOG"; fi
# [1o]/[2o] others/: comparison files (no ledger rows), compiled but NOT counted in [3]
if [ ${#OFILES[@]} -gt 0 ]; then
  tmpo=$(mktemp -d); built=" "
  # build_mod M: compile module M (phases.X or others.X.Y) to $tmpo/M.olean after its own imports
  build_mod() {
    local m="$1" src dep o
    case "$built" in *" $m "*) return 0;; esac
    src="$(printf '%s' "$m" | tr '.' '/').lean"
    [ -f "$src" ] || { echo "[1o] RED missing module source: $src" | tee -a "$LOG"; red=1; return 1; }
    for dep in $(grep -oE '^import[[:space:]]+(phases|others)\.[A-Za-z0-9_.]+' "$src" | awk '{print $2}'); do
      build_mod "$dep" || return 1
    done
    mkdir -p "$tmpo/$(dirname "$src")"
    o=$(LEAN_PATH="$tmpo" lake env lean -R . -o "$tmpo/${src%.lean}.olean" "$src" 2>&1) || {
      printf '%s\n' "$o" >> "$LOG"; echo "[1o] RED module build: $src" | tee -a "$LOG"; red=1; return 1; }
    built="$built$m "
  }
  for f in "${OFILES[@]}"; do
    ok=1
    for dep in $(grep -oE '^import[[:space:]]+(phases|others)\.[A-Za-z0-9_.]+' "$f" | awk '{print $2}'); do
      build_mod "$dep" || ok=0
    done
    [ $ok -eq 1 ] || continue
    out=$(LEAN_PATH="$tmpo" lake env lean "$f" 2>&1); ec=$?
    printf '%s\n' "$out" >> "$LOG"
    c=$(printf '%s\n' "$out" | grep -c "depends on axioms")
    if [ $ec -ne 0 ] || printf '%s\n' "$out" | grep -q "error"; then echo "[1o] RED compile: $f" | tee -a "$LOG"; red=1; else echo "[1o] ok $f ($c axiom queries, not counted)" | tee -a "$LOG"; fi
    if printf '%s\n' "$out" | grep -q "sorryAx"; then echo "[2o] RED sorryAx: $f" | tee -a "$LOG"; red=1; fi
  done
  rm -rf "$tmpo"
else echo "[1o] no others/ file given" | tee -a "$LOG"; fi
# [4] ledger references: every cited theorem/definition name is declared in phases/
refs_out=$(python3 -I tools/check_ledger_refs.py docs/全数台帳 phases 2>&1); refs_ec=$?
printf '%s\n' "$refs_out" >> "$LOG"
refs_sum=$(printf '%s\n' "$refs_out" | grep -E '^(rows|names|note_refs)=' | tr '\n' ' ' | sed 's/ $//')
if [ $refs_ec -ne 0 ] || printf '%s\n' "$refs_out" | grep -q "^MISSING"; then
  echo "[4] RED ledger refs: $refs_sum" | tee -a "$LOG"
  printf '%s\n' "$refs_out" | grep "^MISSING" | tee -a "$LOG"; red=1
else echo "[4] ok ledger refs: $refs_sum" | tee -a "$LOG"; fi
# hygiene patterns are assembled at runtime so this script does not match itself
U="/Use""rs/"; H="/ho""me/"; W='C:'"$(printf '\\\\')"
if grep -rIl --exclude-dir=.lake --exclude-dir=.git --exclude=.git --exclude-dir=logs -e "$U" -e "$H" -e "$W" . >/dev/null 2>&1; then
  echo "[8] RED hygiene: local absolute paths in:" | tee -a "$LOG"
  grep -rIl --exclude-dir=.lake --exclude-dir=.git --exclude=.git --exclude-dir=logs -e "$U" -e "$H" -e "$W" . | tee -a "$LOG"; red=1
else echo "[8] ok hygiene" | tee -a "$LOG"; fi
# [9] atlas generators vs ledgers (read-only: the index is written to a temporary directory)
LEDGERS=(docs/全数台帳/ch*.md docs/全数台帳/notes_III.md)
tmp9=$(mktemp -d); atlas_out=""; atlas_ec=0
o=$(python3 -I tools/atlas/gen.py --check "${LEDGERS[@]}" 2>&1) || atlas_ec=1; atlas_out+="$o"$'\n'
o=$(python3 -I tools/atlas/gen_summary.py --check docs/全数台帳 2>&1) || atlas_ec=1; atlas_out+="$o"$'\n'
o=$(python3 -I tools/atlas/gen_readme_totals.py --check docs/全数台帳 2>&1) || atlas_ec=1; atlas_out+="$o"$'\n'
o=$(python3 -I tools/atlas/gen_index.py --missing-ok docs/全数台帳 docs/atlas "$tmp9/index.html" 2>&1) || atlas_ec=1; atlas_out+="$o"$'\n'
rm -rf "$tmp9"
printf '%s\n' "$atlas_out" >> "$LOG"
warns=$(printf '%s\n' "$atlas_out" | grep -c "^WARN")
if [ $atlas_ec -ne 0 ] || [ "$warns" -ne 0 ]; then
  echo "[9] RED atlas: WARN=$warns" | tee -a "$LOG"
  printf '%s\n' "$atlas_out" | grep -v '^$' | tee -a "$LOG"; red=1
else echo "[9] ok atlas: ledgers=${#LEDGERS[@]} WARN=0" | tee -a "$LOG"; fi
echo "=== RESULT: $([ $red -eq 0 ] && echo GREEN || echo RED) ===" | tee -a "$LOG"
exit $red
