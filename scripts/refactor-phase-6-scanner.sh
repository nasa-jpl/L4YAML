#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p L4YAML/Proofs/Scanner
git mv L4YAML/Proofs/ScannerCorrectness.lean    L4YAML/Proofs/Scanner/ScannerCorrectness.lean
git mv L4YAML/Proofs/ScannerProgress.lean       L4YAML/Proofs/Scanner/ScannerProgress.lean
git mv L4YAML/Proofs/ScannerBound.lean          L4YAML/Proofs/Scanner/ScannerBound.lean
git mv L4YAML/Proofs/ScannerDispatch.lean       L4YAML/Proofs/Scanner/ScannerDispatch.lean
git mv L4YAML/Proofs/ScannerDocument.lean       L4YAML/Proofs/Scanner/ScannerDocument.lean
git mv L4YAML/Proofs/ScannerSimpleKey.lean      L4YAML/Proofs/Scanner/ScannerSimpleKey.lean
git mv L4YAML/Proofs/ScannerLoopInvariant.lean  L4YAML/Proofs/Scanner/ScannerLoopInvariant.lean
git mv L4YAML/Proofs/ScannerContracts.lean      L4YAML/Proofs/Scanner/ScannerContracts.lean
git mv L4YAML/Proofs/ScannerWhitespace.lean     L4YAML/Proofs/Scanner/ScannerWhitespace.lean
git mv L4YAML/Proofs/ScannerPlainScalar.lean    L4YAML/Proofs/Scanner/ScannerPlainScalar.lean
git mv L4YAML/Proofs/ScannerPlainContent.lean   L4YAML/Proofs/Scanner/ScannerPlainContent.lean
git mv L4YAML/Proofs/ScannerDoubleQuoted.lean   L4YAML/Proofs/Scanner/ScannerDoubleQuoted.lean
git mv L4YAML/Proofs/ScannerScalar.lean         L4YAML/Proofs/Scanner/ScannerScalar.lean
git mv L4YAML/Proofs/ScannerFlowCollection.lean L4YAML/Proofs/Scanner/ScannerFlowCollection.lean
git mv L4YAML/Proofs/ScannerIndentStack.lean    L4YAML/Proofs/Scanner/ScannerIndentStack.lean
git mv L4YAML/Proofs/ScannerIndent.lean         L4YAML/Proofs/Scanner/ScannerIndent.lean
git mv L4YAML/Proofs/ScannerProofs.lean         L4YAML/Proofs/Scanner/ScannerProofs.lean
git mv L4YAML/Proofs/ScanStrictCoupling.lean    L4YAML/Proofs/Scanner/ScanStrictCoupling.lean
find . -type f \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-6-scanner.sh' -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.Proofs\.ScannerCorrectness$|import L4YAML.Proofs.Scanner.ScannerCorrectness|' \
  -e 's|^import L4YAML\.Proofs\.ScannerProgress$|import L4YAML.Proofs.Scanner.ScannerProgress|' \
  -e 's|^import L4YAML\.Proofs\.ScannerBound$|import L4YAML.Proofs.Scanner.ScannerBound|' \
  -e 's|^import L4YAML\.Proofs\.ScannerDispatch$|import L4YAML.Proofs.Scanner.ScannerDispatch|' \
  -e 's|^import L4YAML\.Proofs\.ScannerDocument$|import L4YAML.Proofs.Scanner.ScannerDocument|' \
  -e 's|^import L4YAML\.Proofs\.ScannerSimpleKey$|import L4YAML.Proofs.Scanner.ScannerSimpleKey|' \
  -e 's|^import L4YAML\.Proofs\.ScannerLoopInvariant$|import L4YAML.Proofs.Scanner.ScannerLoopInvariant|' \
  -e 's|^import L4YAML\.Proofs\.ScannerContracts$|import L4YAML.Proofs.Scanner.ScannerContracts|' \
  -e 's|^import L4YAML\.Proofs\.ScannerWhitespace$|import L4YAML.Proofs.Scanner.ScannerWhitespace|' \
  -e 's|^import L4YAML\.Proofs\.ScannerPlainScalar$|import L4YAML.Proofs.Scanner.ScannerPlainScalar|' \
  -e 's|^import L4YAML\.Proofs\.ScannerPlainContent$|import L4YAML.Proofs.Scanner.ScannerPlainContent|' \
  -e 's|^import L4YAML\.Proofs\.ScannerDoubleQuoted$|import L4YAML.Proofs.Scanner.ScannerDoubleQuoted|' \
  -e 's|^import L4YAML\.Proofs\.ScannerScalar$|import L4YAML.Proofs.Scanner.ScannerScalar|' \
  -e 's|^import L4YAML\.Proofs\.ScannerFlowCollection$|import L4YAML.Proofs.Scanner.ScannerFlowCollection|' \
  -e 's|^import L4YAML\.Proofs\.ScannerIndentStack$|import L4YAML.Proofs.Scanner.ScannerIndentStack|' \
  -e 's|^import L4YAML\.Proofs\.ScannerIndent$|import L4YAML.Proofs.Scanner.ScannerIndent|' \
  -e 's|^import L4YAML\.Proofs\.ScannerProofs$|import L4YAML.Proofs.Scanner.ScannerProofs|' \
  -e 's|^import L4YAML\.Proofs\.ScanStrictCoupling$|import L4YAML.Proofs.Scanner.ScanStrictCoupling|'
