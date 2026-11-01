#!/usr/bin/env bash
# Rule 9 gate: every scripts/**/*.py and inline python3 invocation is on
# scripts/scripts-ledger.txt and the ledger only shrinks (Scripts/Main/CheckScriptsLedger.lean).
# Builds the exe in the repo, then runs it from the caller's cwd, so a
# relative -C/--root resolves against the caller; without -C the repo root is the root.
set -euo pipefail
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if ! out="$(cd "$repo" && lake build scripts-check-ledger 2>&1)"; then
  printf '%s\n' "$out" >&2
  echo "check-scripts-lean: lake build scripts-check-ledger failed" >&2
  exit 2
fi
exe="$repo/.lake/build/bin/scripts-check-ledger"
for a in "$@"; do
  case "$a" in -C|--root) exec "$exe" "$@";; esac
done
exec "$exe" -C "$repo" "$@"
