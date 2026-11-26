#!/usr/bin/env bash
# Publish the generated documentation tree (docs/) to the `gh-pages` branch as a single
# *orphan* commit — no parent, so the branch never accumulates history and the generated,
# often-churning HTML/JS + doc-gen4 API + test reports + PDF stay out of `main`'s history
# entirely. (Mirrors the soil-moisture-model / SMAP-AVS-ATBD blueprint pipelines.)
#
#   ./scripts/publish-pages.sh                 # writes the LOCAL gh-pages branch; does NOT push
#   PAGES_PUSH=1 ./scripts/publish-pages.sh    # also force-pushes gh-pages (CI publishes this way)
#   PAGES_ONLY="reports/census-dashboard.html" ./scripts/publish-pages.sh
#       # partial publish: the site as published, with only the named docs/ files replaced
#       # (the integration branch refreshes the census dashboard this way between releases);
#       # with PAGES_PUSH=1 it pushes only if gh-pages is still the commit it read, and
#       # rebuilds on the new one otherwise, so it never replaces a release published meanwhile;
#       # PAGES_IF_TIP=<branch> also skips the publish unless HEAD is that remote branch's tip
#       # (checked on every attempt), so an older run never replaces a newer run's page
#       # PAGES_SED=<sed script> PAGES_SED_FILES="<paths>" PAGES_SED_UNLESS=<text> also rewrites
#       # those *published* files with the script, skipping a file that already contains the
#       # text (scripts/pages-census-link.sed adds the dashboard links to a site released
#       # before its sources carried them)
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

if [ -n "${PAGES_ONLY:-}" ]; then
  if [ -n "${PAGES_IF_TIP:-}" ]; then
    # An older run must not replace a newer run's page: publish only from the branch's tip.
    TIP="$(git --git-dir="$GIT_DIR_ABS" ls-remote "$REMOTE" "refs/heads/$PAGES_IF_TIP" | cut -f1)"
    if [ "$TIP" != "$(git --git-dir="$GIT_DIR_ABS" rev-parse HEAD)" ]; then
      echo "Not published: HEAD ($SRC_REF) is not the tip of $REMOTE/$PAGES_IF_TIP (${TIP:0:12}); the tip's run publishes."
      exit 0
    fi
  fi
  # Partial publish: start from the published tree and replace only the named files.
  git --git-dir="$GIT_DIR_ABS" fetch --depth 1 "$REMOTE" "$BRANCH"
  BASE="$(git --git-dir="$GIT_DIR_ABS" rev-parse FETCH_HEAD)"
  git --git-dir="$GIT_DIR_ABS" read-tree "$BASE"
  for p in $PAGES_ONLY; do
    if [ ! -f "$SITE/$p" ]; then
      echo "error: $SITE/$p not found — nothing to publish for it" >&2
      exit 1
    fi
    BLOB="$(git --git-dir="$GIT_DIR_ABS" hash-object -w "$SITE/$p")"
    git --git-dir="$GIT_DIR_ABS" update-index --add --cacheinfo "100644,$BLOB,$p"
  done
  # Rewrite published files in place (read from $BASE, so a retry re-reads the new site).
  for p in ${PAGES_SED_FILES:-}; do
    if ! git --git-dir="$GIT_DIR_ABS" cat-file -e "$BASE:$p" 2>/dev/null; then
      echo "note: $p is not on $REMOTE/$BRANCH — not rewritten" >&2
      continue
    fi
    git --git-dir="$GIT_DIR_ABS" show "$BASE:$p" > "$TMP_DIR/page"
    if [ -n "${PAGES_SED_UNLESS:-}" ] && grep -qF -- "$PAGES_SED_UNLESS" "$TMP_DIR/page"; then
      continue
    fi
    sed -f "$PAGES_SED" "$TMP_DIR/page" > "$TMP_DIR/page.new"
    if [ -n "${PAGES_SED_UNLESS:-}" ] && ! grep -qF -- "$PAGES_SED_UNLESS" "$TMP_DIR/page.new"; then
      echo "::warning::$PAGES_SED left $p unchanged (anchor not found)"
      continue
    fi
    BLOB="$(git --git-dir="$GIT_DIR_ABS" hash-object -w "$TMP_DIR/page.new")"
    git --git-dir="$GIT_DIR_ABS" update-index --add --cacheinfo "100644,$BLOB,$p"
    echo "Rewrote $p with $PAGES_SED."
  done
else
  cd "$SITE"
  # The root .gitignore's `/docs` rule does not apply here: with --work-tree=docs, git treats
  # docs/ as the tree root and never reads gitignore files above it, so the whole site is staged.
  git --git-dir="$GIT_DIR_ABS" --work-tree="$SITE" add -A .
fi
TREE="$(git --git-dir="$GIT_DIR_ABS" write-tree)"
# No -p parent: a root commit, so gh-pages stays a single flat commit across publishes.
COMMIT="$(printf 'Publish L4YAML documentation site (source %s)\n' "$SRC_REF" \
  | git --git-dir="$GIT_DIR_ABS" commit-tree "$TREE")"
git --git-dir="$GIT_DIR_ABS" branch -f "$BRANCH" "$COMMIT"

echo "Published $(git --git-dir="$GIT_DIR_ABS" ls-tree -r --name-only "$COMMIT" | wc -l) files to branch '$BRANCH' (orphan commit ${COMMIT:0:12})."

if [ "${PAGES_PUSH:-0}" = "1" ]; then
  echo "Force-pushing $BRANCH to $REMOTE ..."
  if [ -n "${PAGES_ONLY:-}" ]; then
    # Push only if the remote is still the commit this was built on ($BASE), so a release
    # published in between is never replaced; on a lost race, rebuild on the new site.
    if ! git --git-dir="$GIT_DIR_ABS" push --force-with-lease="$BRANCH:$BASE" "$REMOTE" "$BRANCH"; then
      TRY="${PAGES_TRY:-1}"
      if [ "$TRY" -ge 3 ]; then
        echo "error: $REMOTE/$BRANCH moved during each of $TRY partial publishes — not pushed" >&2
        exit 1
      fi
      echo "$REMOTE/$BRANCH moved since it was read; rebuilding on the new site (attempt $((TRY + 1)))" >&2
      # `exec` does not run the EXIT trap: drop this attempt's index here.
      rm -rf "$TMP_DIR"
      unset GIT_INDEX_FILE
      PAGES_TRY=$((TRY + 1)) exec bash "${BASH_SOURCE[0]}"
    fi
  else
    git --git-dir="$GIT_DIR_ABS" push --force "$REMOTE" "$BRANCH"
  fi
  echo "Published to $REMOTE/$BRANCH."
else
  echo "Local branch written. Push it with:  git push --force $REMOTE $BRANCH"
fi
