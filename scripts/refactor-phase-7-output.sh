#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p L4YAML/Proofs/Output
git mv L4YAML/Proofs/EmitterScannability.lean L4YAML/Proofs/Output/EmitterScannability.lean
git mv L4YAML/Proofs/ScannerEmitBridge.lean   L4YAML/Proofs/Output/ScannerEmitBridge.lean
git mv L4YAML/Proofs/DumpRoundTrip.lean       L4YAML/Proofs/Output/DumpRoundTrip.lean
find . -type f \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-7-output.sh' -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.Proofs\.EmitterScannability$|import L4YAML.Proofs.Output.EmitterScannability|' \
  -e 's|^import L4YAML\.Proofs\.ScannerEmitBridge$|import L4YAML.Proofs.Output.ScannerEmitBridge|' \
  -e 's|^import L4YAML\.Proofs\.DumpRoundTrip$|import L4YAML.Proofs.Output.DumpRoundTrip|'
