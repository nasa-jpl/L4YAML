#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p L4YAML/Proofs/Coupling
git mv L4YAML/Proofs/CouplingBridge.lean    L4YAML/Proofs/Coupling/CouplingBridge.lean
git mv L4YAML/Proofs/ScannerCoupling.lean   L4YAML/Proofs/Coupling/ScannerCoupling.lean
git mv L4YAML/Proofs/SurfaceCoupling.lean   L4YAML/Proofs/Coupling/SurfaceCoupling.lean
git mv L4YAML/Proofs/StructureCoupling.lean L4YAML/Proofs/Coupling/StructureCoupling.lean
git mv L4YAML/Proofs/ScalarCoupling.lean    L4YAML/Proofs/Coupling/ScalarCoupling.lean
find . -type f \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-9-coupling.sh' -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.Proofs\.CouplingBridge$|import L4YAML.Proofs.Coupling.CouplingBridge|' \
  -e 's|^import L4YAML\.Proofs\.ScannerCoupling$|import L4YAML.Proofs.Coupling.ScannerCoupling|' \
  -e 's|^import L4YAML\.Proofs\.SurfaceCoupling$|import L4YAML.Proofs.Coupling.SurfaceCoupling|' \
  -e 's|^import L4YAML\.Proofs\.StructureCoupling$|import L4YAML.Proofs.Coupling.StructureCoupling|' \
  -e 's|^import L4YAML\.Proofs\.ScalarCoupling$|import L4YAML.Proofs.Coupling.ScalarCoupling|'
