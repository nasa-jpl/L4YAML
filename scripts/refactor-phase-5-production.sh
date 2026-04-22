#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p L4YAML/Proofs/Production
git mv L4YAML/Proofs/StreamAccum.lean              L4YAML/Proofs/Production/StreamAccum.lean
git mv L4YAML/Proofs/StructureProduction.lean      L4YAML/Proofs/Production/StructureProduction.lean
git mv L4YAML/Proofs/ScalarProduction.lean         L4YAML/Proofs/Production/ScalarProduction.lean
git mv L4YAML/Proofs/DocumentProduction.lean       L4YAML/Proofs/Production/DocumentProduction.lean
git mv L4YAML/Proofs/NodeProduction.lean           L4YAML/Proofs/Production/NodeProduction.lean
git mv L4YAML/Proofs/PreprocessProduction.lean     L4YAML/Proofs/Production/PreprocessProduction.lean
git mv L4YAML/Proofs/ScannerPlainScalarValid.lean  L4YAML/Proofs/Production/ScannerPlainScalarValid.lean
find . -type f \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-5-production.sh' -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.Proofs\.StreamAccum$|import L4YAML.Proofs.Production.StreamAccum|' \
  -e 's|^import L4YAML\.Proofs\.StructureProduction$|import L4YAML.Proofs.Production.StructureProduction|' \
  -e 's|^import L4YAML\.Proofs\.ScalarProduction$|import L4YAML.Proofs.Production.ScalarProduction|' \
  -e 's|^import L4YAML\.Proofs\.DocumentProduction$|import L4YAML.Proofs.Production.DocumentProduction|' \
  -e 's|^import L4YAML\.Proofs\.NodeProduction$|import L4YAML.Proofs.Production.NodeProduction|' \
  -e 's|^import L4YAML\.Proofs\.PreprocessProduction$|import L4YAML.Proofs.Production.PreprocessProduction|' \
  -e 's|^import L4YAML\.Proofs\.ScannerPlainScalarValid$|import L4YAML.Proofs.Production.ScannerPlainScalarValid|'
