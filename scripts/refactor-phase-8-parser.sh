#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p L4YAML/Proofs/Parser
git mv L4YAML/Proofs/ParserSoundness.lean       L4YAML/Proofs/Parser/ParserSoundness.lean
git mv L4YAML/Proofs/ParserCompleteness.lean    L4YAML/Proofs/Parser/ParserCompleteness.lean
git mv L4YAML/Proofs/ParserCorrectness.lean     L4YAML/Proofs/Parser/ParserCorrectness.lean
git mv L4YAML/Proofs/ParserNodeProofs.lean      L4YAML/Proofs/Parser/ParserNodeProofs.lean
git mv L4YAML/Proofs/ParserAnchorProofs.lean    L4YAML/Proofs/Parser/ParserAnchorProofs.lean
git mv L4YAML/Proofs/ParserWfaProofs.lean       L4YAML/Proofs/Parser/ParserWfaProofs.lean
git mv L4YAML/Proofs/ParserWellBehaved.lean     L4YAML/Proofs/Parser/ParserWellBehaved.lean
git mv L4YAML/Proofs/ParserGrammable.lean       L4YAML/Proofs/Parser/ParserGrammable.lean
git mv L4YAML/Proofs/ParserGrammableBase.lean   L4YAML/Proofs/Parser/ParserGrammableBase.lean
find . -type f \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-8-parser.sh' -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.Proofs\.ParserSoundness$|import L4YAML.Proofs.Parser.ParserSoundness|' \
  -e 's|^import L4YAML\.Proofs\.ParserCompleteness$|import L4YAML.Proofs.Parser.ParserCompleteness|' \
  -e 's|^import L4YAML\.Proofs\.ParserCorrectness$|import L4YAML.Proofs.Parser.ParserCorrectness|' \
  -e 's|^import L4YAML\.Proofs\.ParserNodeProofs$|import L4YAML.Proofs.Parser.ParserNodeProofs|' \
  -e 's|^import L4YAML\.Proofs\.ParserAnchorProofs$|import L4YAML.Proofs.Parser.ParserAnchorProofs|' \
  -e 's|^import L4YAML\.Proofs\.ParserWfaProofs$|import L4YAML.Proofs.Parser.ParserWfaProofs|' \
  -e 's|^import L4YAML\.Proofs\.ParserWellBehaved$|import L4YAML.Proofs.Parser.ParserWellBehaved|' \
  -e 's|^import L4YAML\.Proofs\.ParserGrammable$|import L4YAML.Proofs.Parser.ParserGrammable|' \
  -e 's|^import L4YAML\.Proofs\.ParserGrammableBase$|import L4YAML.Proofs.Parser.ParserGrammableBase|'
