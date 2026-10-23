#!/bin/bash
# ============================================================
# Canonical run: elaborate every phase file and record an
# SHA-256-bound audit log under logs/.
# Usage (from the repository root, pinned toolchain active):
#   bash run_v10.sh
# The #print axioms blocks in the output are the audit data.
# ============================================================
set -u
STAMP="$(date '+%Y%m%d')"
LOG="logs/keynes_audit_canonical_run_${STAMP}_v10.log"
{
  echo "CANONICAL RUN v10 — Keynes audit v1.5: Part II complete (incl. Ch.17 §§3–12), Ch. VI (8d, 8dp), Part III (9a–9c), Ch. 26 (8a2), 6c repair + models"
  echo "date: $(date -u '+%Y-%m-%dT%H:%M:%SZ') UTC"
  lake env lean --version
  echo "--- file hashes (sha256) ---"
  shasum -a 256 phases/*.lean
  echo "==================================================================="
  for f in phases/*.lean; do
    echo ""
    echo "=== FILE: $(basename "$f") ==="
    lake env lean "$f" 2>&1
    echo "EXIT_$(basename "$f" .lean):$?"
  done
  echo ""
  echo "=== CANONICAL RUN COMPLETE $(date -u '+%Y-%m-%dT%H:%M:%SZ') UTC ==="
} | tee "$LOG"
echo ""
grep '^EXIT_' "$LOG" | grep -v ':0$' && echo '>>> WARNING: nonzero exit present' || echo '>>> all files exit 0'
grep -q 'sorryAx' "$LOG" && echo '>>> WARNING: sorryAx present' || echo '>>> no sorryAx'
grep -q 'error' "$LOG" && echo '>>> WARNING: errors present' || echo '>>> no errors'
