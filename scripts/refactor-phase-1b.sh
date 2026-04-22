#!/usr/bin/env bash
#
# scripts/refactor-phase-1b.sh
#
# Blueprint Initiative 1 — Phase 1b: move the two remaining umbrella
# files (`L4YAML/Schema.lean` and `L4YAML/Surface.lean`) into their
# respective folders so the folder-based layout from Phase 1 is
# symmetric.
#
# Why this is a separate phase: the top-level `Schema.lean` /
# `Surface.lean` files predate Phase 1 and were legal (Lean 4 permits
# a module file to coexist with a same-named subfolder). They were
# left in place by Phase 1 because the blueprint
# (03-code-organization.md) was ambiguous about their disposition
# ("becomes Surface/default.lean or is deleted").
#
# Decision: move them to `Schema/Schema.lean` / `Surface/Surface.lean`
# — consistent with the `Scanner/Scanner.lean` pattern Phase 1 just
# established — and rewrite every `import L4YAML.Schema` /
# `import L4YAML.Surface` accordingly. Namespaces are untouched; the
# files continue to declare `namespace L4YAML.Schema` / `L4YAML.Surface`
# as umbrella namespaces.
#
# Safety: identical approach to Phase 1 — `git mv` + anchored sed.
# Reverse: revert the resulting commit.

set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

# --- 1. git mv the two umbrella files ------------------------------------
git mv L4YAML/Schema.lean  L4YAML/Schema/Schema.lean
git mv L4YAML/Surface.lean L4YAML/Surface/Surface.lean

# --- 2. Rewrite imports ---------------------------------------------------
# Anchored to `^import L4YAML.Foo$` so bare occurrences of the module
# names elsewhere (namespace declarations, qualified references) are
# not touched. Order does not matter here — the two patterns are
# disjoint — but we list Surface first for symmetry.

find . \
  -type f \
  \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' \
  -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-1*.sh' \
  -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.Surface$|import L4YAML.Surface.Surface|' \
  -e 's|^import L4YAML\.Schema$|import L4YAML.Schema.Schema|'

echo ""
echo "Phase 1b refactor complete."
echo ""
echo "Next:"
echo "  1. Review 'git status' — 2 renames + ~10 touched imports."
echo "  2. lake build  (must succeed before committing)."
echo "  3. git commit."
