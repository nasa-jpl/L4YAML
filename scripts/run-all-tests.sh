#!/usr/bin/env bash
# scripts/run-all-tests.sh — Run all L4YAML test suites and capture output
#
# Usage: scripts/run-all-tests.sh [OUTPUT_DIR]
#   OUTPUT_DIR defaults to "docs".
#   CI uses "docs/reports" to avoid clashing with Verso's docs/Test-Results/.
#
# The script assumes lake build has already been run.

set -euo pipefail

OUT="${1:-docs}"
mkdir -p "$OUT"

BIN="./.lake/build/bin"

run_suite() {
  local name="$1"
  local exe="$2"
  local outfile="$OUT/$name.txt"
  echo "=== Running: $name ==="
  echo "=== $name ===" > "$outfile"
  "$BIN/$exe" 2>&1 | tee -a "$outfile" || true
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
echo "=== Generating HTML coverage reports ==="
"$BIN/suiterunner" --html "$OUT/" | tee "$OUT/coverage-console.txt" || true

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

echo "=== All Lean test suites complete. Results in $OUT/ ==="
