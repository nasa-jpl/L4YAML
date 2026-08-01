#!/usr/bin/env bash
# CI gate: the `theorem` keyword is reserved for @[capstone] declarations
# (Blueprint/06-discipline.md). Every `theorem` site in the library must
# be whitelisted in scripts/capstones.txt; everything else uses `lemma`.
# The @[capstone]-tagged set itself is pinned in L4YAML/Capstones.lean.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 scripts/rename_lemma.py --check --whitelist scripts/capstones.txt L4YAML
