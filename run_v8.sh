#!/bin/bash
# ============================================================
# Canonical run: elaborate every phase file and record an
# SHA-256-bound audit log under logs/.
# Usage (from the repository root, pinned toolchain active):
#   bash run_v8.sh
# The #print axioms blocks in the output are the audit data.
# ============================================================
set -u
STAMP="$(date '+%Y%m%d')"
LOG="logs/keynes_audit_canonical_run_${STAMP}_v8.log"
{
  echo "CANONICAL RUN v8 — Keynes Part II audit + weight trilogy + Ch. VI anchors (8d)"
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
