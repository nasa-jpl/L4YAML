#!/usr/bin/env bash
# Rule 9 gate: every scripts/**/*.py and inline python3 site is on
# scripts/scripts-ledger.txt and the ledger only shrinks (Scripts/Main/CheckScriptsLedger.lean).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec lake exe scripts-check-ledger "$@"
