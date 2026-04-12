#!/usr/bin/env bash
# Generate doc-gen4 API documentation for L4YAML
#
# Usage:
#   ./scripts/build-api-docs.sh [output-dir]
#
# This builds API documentation using doc-gen4's library_facet for the L4YAML
# library only.  Core docs (Init, Std, Lake, Lean) are built as a dependency;
# some timeout warnings from equational lemma generation are expected and
# non-fatal.
#
# Output goes to .lake/build/doc/ by default, or is copied to the specified
# output directory.
#
# Environment variables:
#   DOCGEN_SRC  — Controls source link style (default: file).
#                 Set to "github" for github.com repos, "vscode" for VS Code links,
#                 or "file" for local file:// URIs (avoids errors with non-github.com
#                 remotes like GitHub Enterprise or Codeberg).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

cd "$PROJECT_DIR"

export DOCGEN_SRC="${DOCGEN_SRC:-file}"

echo "Building doc-gen4 API documentation for L4YAML (DOCGEN_SRC=$DOCGEN_SRC)..."
lake build L4YAML:docs

echo ""
echo "doc-gen4 output: .lake/build/doc/"

if [[ $# -ge 1 ]]; then
    DEST="$1"
    mkdir -p "$DEST"
    cp -r .lake/build/doc/* "$DEST/"
    echo "Copied to: $DEST/"
fi
