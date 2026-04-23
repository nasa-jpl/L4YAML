#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
mkdir -p L4YAML/Proofs/RoundTrip
git mv L4YAML/Proofs/RoundTrip.lean            L4YAML/Proofs/RoundTrip/RoundTrip.lean
git mv L4YAML/Proofs/RoundTripComposition.lean L4YAML/Proofs/RoundTrip/RoundTripComposition.lean
git mv L4YAML/Proofs/CommentRoundTrip.lean     L4YAML/Proofs/RoundTrip/CommentRoundTrip.lean
git mv L4YAML/Proofs/CommentProperties.lean    L4YAML/Proofs/RoundTrip/CommentProperties.lean
find . -type f \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-10-roundtrip.sh' -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.Proofs\.RoundTrip$|import L4YAML.Proofs.RoundTrip.RoundTrip|' \
  -e 's|^import L4YAML\.Proofs\.RoundTripComposition$|import L4YAML.Proofs.RoundTrip.RoundTripComposition|' \
  -e 's|^import L4YAML\.Proofs\.CommentRoundTrip$|import L4YAML.Proofs.RoundTrip.CommentRoundTrip|' \
  -e 's|^import L4YAML\.Proofs\.CommentProperties$|import L4YAML.Proofs.RoundTrip.CommentProperties|'
