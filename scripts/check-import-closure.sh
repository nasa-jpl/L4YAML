#!/usr/bin/env bash
# CI gate: no orphan modules (see scripts/check_import_closure.py).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 scripts/check_import_closure.py
