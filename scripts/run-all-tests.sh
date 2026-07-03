#!/usr/bin/env bash
# scripts/run-all-tests.sh — Run all L4YAML test suites and capture output
#
# Usage: scripts/run-all-tests.sh [OUTPUT_DIR]
#   OUTPUT_DIR defaults to "docs".
#   CI uses "docs/reports" to avoid clashing with Verso's docs/Test-Results/.
#
# The script assumes lake build has already been run.
#
# Every suite runs to completion even if an earlier one fails (all report
# files are still produced), but failures are collected and the script
# exits nonzero at the end — CI must not go green over failing suites.

set -euo pipefail

OUT="${1:-docs}"
mkdir -p "$OUT"

BIN="./.lake/build/bin"

FAILED_SUITES=()

run_suite() {
  local name="$1"
  local exe="$2"
  local outfile="$OUT/$name.txt"
  echo "=== Running: $name ==="
  echo "=== $name ===" > "$outfile"
  if ! "$BIN/$exe" 2>&1 | tee -a "$outfile"; then
    FAILED_SUITES+=("$name")
  fi
  echo ""
}

# ---- Lean test suites ----
run_suite "unit-tests"          "tests"
run_suite "demo"                "demo"
run_suite "explicitkeytests"    "explicitkeytests"
run_suite "flowtests"           "flowtests"
run_suite "validationtests"     "validationtests"
run_suite "dumproundtrip"       "dumproundtrip"
run_suite "rawparsetests"       "rawparsetests"
run_suite "specexamples"        "specexamples"
run_suite "schemadump"          "schemadump"
run_suite "scannertests"        "scannertests"
run_suite "scannerspecexamples" "scannerspecexamples"
run_suite "adversarialtests"    "adversarialtests"
run_suite "mutationtests"       "mutationtests"
run_suite "propertytests"       "propertytests"
run_suite "productioncoverage"  "productioncoverage"
run_suite "limittests"          "limittests"

# ---- Diagnostic checks ----
run_suite "flowregressioncheck" "flowregressioncheck"
run_suite "errorstagediag"      "errorstagediag"
run_suite "scalarstagediag"     "scalarstagediag"

# ---- HTML coverage reports from suiterunner ----
# NB: --html mode always exits 0 (report generation succeeded); per-test
# pass/fail accounting lives in the generated reports and is gated by the
# cross-language comparison step in CI. A nonzero exit here means the
# runner itself crashed.
echo "=== Generating HTML coverage reports ==="
if ! "$BIN/suiterunner" --html "$OUT/" | tee "$OUT/coverage-console.txt"; then
  FAILED_SUITES+=("suiterunner-html")
fi

# ---- Concatenate all text results ----
cat \
  "$OUT/unit-tests.txt" \
  "$OUT/demo.txt" \
  "$OUT/explicitkeytests.txt" \
  "$OUT/flowtests.txt" \
  "$OUT/validationtests.txt" \
  "$OUT/dumproundtrip.txt" \
  "$OUT/rawparsetests.txt" \
  "$OUT/specexamples.txt" \
  "$OUT/schemadump.txt" \
  "$OUT/scannertests.txt" \
  "$OUT/scannerspecexamples.txt" \
  "$OUT/adversarialtests.txt" \
  "$OUT/mutationtests.txt" \
  "$OUT/propertytests.txt" \
  "$OUT/productioncoverage.txt" \
  "$OUT/limittests.txt" \
  > "$OUT/all-verified-tests.txt"

if [ "${#FAILED_SUITES[@]}" -gt 0 ]; then
  echo "=== FAILED suites (${#FAILED_SUITES[@]}): ${FAILED_SUITES[*]} ===" >&2
  exit 1
fi

echo "=== All Lean test suites complete. Results in $OUT/ ==="
