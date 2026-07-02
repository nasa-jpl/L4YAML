#!/usr/bin/env bash
# Publish the generated documentation tree (docs/) to the `gh-pages` branch as a single
# *orphan* commit — no parent, so the branch never accumulates history and the generated,
# often-churning HTML/JS + doc-gen4 API + test reports + PDF stay out of `main`'s history
# entirely. (Mirrors the soil-moisture-model / SMAP-AVS-ATBD blueprint pipelines.)
#
#   ./scripts/publish-pages.sh                 # writes the LOCAL gh-pages branch; does NOT push
#   PAGES_PUSH=1 ./scripts/publish-pages.sh    # also force-pushes gh-pages (CI publishes this way)
#
# GitHub Pages serves it from the branch root (Settings -> Pages -> Deploy from a branch ->
# gh-pages -> / (root)). Each publish *replaces* gh-pages, so it is always force-pushed:
#
#   git push --force origin gh-pages
#
# Why an orphan branch instead of committing docs/ on main: the site is regenerated on every
# push, so committing it churned main's history by hundreds of commits (docs/ touched 437 of
# them before this change) and bloated the pack. Keeping the artifact on a flat, replaced-each-
# -publish branch keeps main's history clean. Never use git-LFS: GitHub Pages does not resolve
# LFS objects — it would serve the pointer stub as the file and break the site.
#
# Implementation: a throwaway index + git plumbing (write-tree / commit-tree / branch -f), so
# the working tree, the real index, and the checked-out branch are all left untouched. Safe to
# run from any branch, including `main` with unrelated proof work still uncommitted.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # repo root
cd "$ROOT"
SITE="$ROOT/docs"
BRANCH="${PAGES_BRANCH:-gh-pages}"
REMOTE="${PAGES_REMOTE:-origin}"
GIT_DIR_ABS="$ROOT/.git"

if [ ! -d "$SITE" ]; then
  echo "error: $SITE not found — generate the documentation first (the CI workflow's Phase 1-5, or 'cd doc && lake exe l4yaml-doc' + copy into docs/)" >&2
  exit 1
fi

# GitHub Pages must serve Verso's `-verso-data/` / `-verso-search/` assets and any other
# dash/underscore-prefixed files verbatim (no Jekyll processing), so drop a .nojekyll marker
# at the site root before staging the tree.
touch "$SITE/.nojekyll"

SRC_REF="$(git --git-dir="$GIT_DIR_ABS" rev-parse --short HEAD 2>/dev/null || echo unknown)"

# Build the commit from a temporary index so the real index is never touched. The index path
# must NOT pre-exist (git rejects a zero-byte index), so point it inside a fresh temp dir.
TMP_DIR="$(mktemp -d -t ghpages-idx.XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT
export GIT_INDEX_FILE="$TMP_DIR/index"

cd "$SITE"
# The root .gitignore's `/docs` rule does not apply here: with --work-tree=docs, git treats
# docs/ as the tree root and never reads gitignore files above it, so the whole site is staged.
git --git-dir="$GIT_DIR_ABS" --work-tree="$SITE" add -A .
TREE="$(git --git-dir="$GIT_DIR_ABS" write-tree)"
# No -p parent: a root commit, so gh-pages stays a single flat commit across publishes.
COMMIT="$(printf 'Publish L4YAML documentation site (source %s)\n' "$SRC_REF" \
  | git --git-dir="$GIT_DIR_ABS" commit-tree "$TREE")"
git --git-dir="$GIT_DIR_ABS" branch -f "$BRANCH" "$COMMIT"

echo "Published $(find "$SITE" -type f | wc -l) files to branch '$BRANCH' (orphan commit ${COMMIT:0:12})."

if [ "${PAGES_PUSH:-0}" = "1" ]; then
  echo "Force-pushing $BRANCH to $REMOTE ..."
  git --git-dir="$GIT_DIR_ABS" push --force "$REMOTE" "$BRANCH"
  echo "Published to $REMOTE/$BRANCH."
else
  echo "Local branch written. Push it with:  git push --force $REMOTE $BRANCH"
fi
