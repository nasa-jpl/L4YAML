#!/usr/bin/env bash
#
# scripts/refactor-phase-1.sh
#
# Blueprint Initiative 1 — Phase 1: non-code folder moves.
# See Blueprint/03-code-organization.md "Phase 1 — non-code moves".
#
# Moves 12 top-level files in L4YAML/ into the folder structure proposed
# by the blueprint (Spec/, Parser/, Output/, Config/, FFI/, Token/,
# Scanner/) and rewrites every `import L4YAML.X` line in the repo to
# point at the new module path.
#
# The namespace declarations inside each file are *not* touched — only
# file locations (module paths) and the `import` statements that refer
# to them. This keeps the patch mechanical and reversible.
#
# Safety:
#   - Uses `git mv` so the history follows the files.
#   - Rewrites only anchored `^import L4YAML.Foo$` lines, never bare
#     occurrences of `L4YAML.Foo` (which would corrupt namespace uses
#     like `namespace L4YAML.Scanner`).
#   - Rewrites are ordered longest-first so `L4YAML.TokenParser` is not
#     mangled by the `L4YAML.Token` substitution.
#
# Reverse: `git reset --hard HEAD` before staging, or revert the commit
# after. The individual moves are independent, so a bisect on the
# resulting commit reveals which file caused a build break.

set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

# --- 1. Create target folders --------------------------------------------
mkdir -p L4YAML/Spec L4YAML/Parser L4YAML/Output L4YAML/Config \
         L4YAML/FFI L4YAML/Token L4YAML/Scanner

# --- 2. git mv each file -------------------------------------------------
# Order within this list does not matter; each `git mv` is independent.
git mv L4YAML/CharPredicates.lean L4YAML/Spec/CharPredicates.lean
git mv L4YAML/Grammar.lean        L4YAML/Spec/Grammar.lean
git mv L4YAML/YamlSpec.lean       L4YAML/Spec/YamlSpec.lean
git mv L4YAML/Types.lean          L4YAML/Spec/Types.lean

git mv L4YAML/Token.lean          L4YAML/Token/Token.lean
git mv L4YAML/Scanner.lean        L4YAML/Scanner/Scanner.lean
git mv L4YAML/TokenParser.lean    L4YAML/Parser/TokenParser.lean

git mv L4YAML/Emitter.lean        L4YAML/Output/Emitter.lean
git mv L4YAML/Dump.lean           L4YAML/Output/Dump.lean

git mv L4YAML/Config.lean         L4YAML/Config/Config.lean
git mv L4YAML/Limits.lean         L4YAML/Config/Limits.lean

git mv L4YAML/FFI.lean            L4YAML/FFI/FFI.lean

# --- 3. Rewrite imports ---------------------------------------------------
# sed substitutions must be longest-first so L4YAML.TokenParser is
# rewritten before L4YAML.Token, and L4YAML.Limits before L4YAML.Config
# (in case any future file imports both).
#
# The `$` anchor restricts substitutions to lines whose entire content
# is `import L4YAML.Foo` — i.e. real import statements only. Bare
# occurrences of the module name elsewhere (namespace declarations,
# qualified references, docstrings) are not touched.

find . \
  -type f \
  \( -name '*.lean' -o -name '*.py' \) \
  -not -path './.lake/*' \
  -not -path './docs/api/*' \
  -not -path './scripts/refactor-phase-1.sh' \
  -print0 |
xargs -0 sed -i \
  -e 's|^import L4YAML\.CharPredicates$|import L4YAML.Spec.CharPredicates|' \
  -e 's|^import L4YAML\.YamlSpec$|import L4YAML.Spec.YamlSpec|' \
  -e 's|^import L4YAML\.Grammar$|import L4YAML.Spec.Grammar|' \
  -e 's|^import L4YAML\.Types$|import L4YAML.Spec.Types|' \
  -e 's|^import L4YAML\.TokenParser$|import L4YAML.Parser.TokenParser|' \
  -e 's|^import L4YAML\.Scanner$|import L4YAML.Scanner.Scanner|' \
  -e 's|^import L4YAML\.Emitter$|import L4YAML.Output.Emitter|' \
  -e 's|^import L4YAML\.Dump$|import L4YAML.Output.Dump|' \
  -e 's|^import L4YAML\.Limits$|import L4YAML.Config.Limits|' \
  -e 's|^import L4YAML\.Config$|import L4YAML.Config.Config|' \
  -e 's|^import L4YAML\.FFI$|import L4YAML.FFI.FFI|' \
  -e 's|^import L4YAML\.Token$|import L4YAML.Token.Token|'

# --- 4. Rewrite the python code generator --------------------------------
# gen-suite-guards.py emits `import L4YAML.TokenParser` as a literal
# string inside a Python f-string, so it was covered by step 3 above.
# The `open L4YAML.TokenParser` line in the same file references the
# namespace (not the module path) and is intentionally left unchanged.

echo ""
echo "Phase 1 refactor complete."
echo ""
echo "Next:"
echo "  1. Review 'git status' — 12 renames + touched imports across the repo."
echo "  2. lake build  (must succeed before committing)."
echo "  3. lake test   (optional, slower gate)."
echo "  4. git commit."
