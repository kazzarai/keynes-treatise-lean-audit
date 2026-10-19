#!/bin/bash
# check_all — mechanical gate for this repository.
# Stages: 0 Mathlib cache present; 1 every phase compiles (exit 0, no "error"); 2 no sorryAx;
#         3 verdict count -> logs/progress.json; 8 hygiene (no local absolute paths).
# Usage: bash tools/check_all.sh [phases/file.lean ...]   (default: all phases)
set -u
cd "$(dirname "$0")/.." || exit 1
red=0; mkdir -p logs
LOG="logs/check_$(date -u +%Y%m%dT%H%M%SZ).log"
echo "=== check_all $(date -u +%FT%TZ) $(lake env lean --version 2>/dev/null) ===" | tee "$LOG"
n=$(find .lake/packages/mathlib/.lake/build/lib -name "*.olean" 2>/dev/null | wc -l | tr -d ' ')
if [ "$n" -lt 1000 ]; then echo "[0] RED: Mathlib oleans missing ($n). Run: lake exe cache get" | tee -a "$LOG"; red=1; else echo "[0] ok mathlib oleans=$n" | tee -a "$LOG"; fi
FILES=("$@"); [ ${#FILES[@]} -eq 0 ] && FILES=(phases/*.lean)
total=0
for f in "${FILES[@]}"; do
  out=$(lake env lean "$f" 2>&1); ec=$?
  printf '%s\n' "$out" >> "$LOG"
  c=$(printf '%s\n' "$out" | grep -c "depends on axioms"); total=$((total+c))
  if [ $ec -ne 0 ] || printf '%s\n' "$out" | grep -q "error"; then echo "[1] RED compile: $f" | tee -a "$LOG"; red=1; else echo "[1] ok $f ($c verdicts)" | tee -a "$LOG"; fi
  if printf '%s\n' "$out" | grep -q "sorryAx"; then echo "[2] RED sorryAx: $f" | tee -a "$LOG"; red=1; fi
done
printf '{"verdicts": %d, "files": %d, "date": "%s"}\n' "$total" "${#FILES[@]}" "$(date -u +%F)" > logs/progress.json
echo "[3] verdicts=$total files=${#FILES[@]} -> logs/progress.json" | tee -a "$LOG"
# hygiene patterns are assembled at runtime so this script does not match itself
U="/Use""rs/"; H="/ho""me/"; W='C:'"$(printf '\\\\')"
if grep -rIl --exclude-dir=.lake --exclude-dir=.git --exclude=.git --exclude-dir=logs -e "$U" -e "$H" -e "$W" . >/dev/null 2>&1; then
  echo "[8] RED hygiene: local absolute paths in:" | tee -a "$LOG"
  grep -rIl --exclude-dir=.lake --exclude-dir=.git --exclude=.git --exclude-dir=logs -e "$U" -e "$H" -e "$W" . | tee -a "$LOG"; red=1
else echo "[8] ok hygiene" | tee -a "$LOG"; fi
echo "=== RESULT: $([ $red -eq 0 ] && echo GREEN || echo RED) ===" | tee -a "$LOG"
exit $red
