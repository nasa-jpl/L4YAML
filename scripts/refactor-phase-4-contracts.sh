#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p L4YAML/Proofs/Contracts
git mv L4YAML/Proofs/BlockScalarContracts.lean L4YAML/Proofs/Contracts/BlockScalarContracts.lean
git mv L4YAML/Proofs/DocumentContracts.lean    L4YAML/Proofs/Contracts/DocumentContracts.lean
find . -type f \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-4-contracts.sh' -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.Proofs\.BlockScalarContracts$|import L4YAML.Proofs.Contracts.BlockScalarContracts|' \
  -e 's|^import L4YAML\.Proofs\.DocumentContracts$|import L4YAML.Proofs.Contracts.DocumentContracts|'
