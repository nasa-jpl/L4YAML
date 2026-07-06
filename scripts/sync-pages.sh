#!/usr/bin/env bash
# Mirror the published gh-pages site across all remotes so every GitHub Pages
# host serves the same thing.
#
# Why this is needed: CI runs on the ghe self-hosted runner, and
# scripts/publish-pages.sh force-pushes gh-pages to that checkout's `origin`
# remote — which, on the runner, is the ghe repo. So CI only ever updates
# **ghe**'s gh-pages; the github.com (nasa-jpl) gh-pages drifts. The ghe runner
# has no github.com push credentials, so the fan-out is done here, locally,
# where you have credentials for both remotes.
#
# gh-pages is a flat ORPHAN branch (one commit, force-pushed each publish), so
# "sync" is simply copying that single commit to every target. main/history and
# your working tree are never touched.
#
#   scripts/sync-pages.sh
#       Fetch gh-pages from ghe (the freshest, CI-published copy) and force-push
#       it to origin + ghe, so both match.
#
#   PAGES_SOURCE=<remote-or-path> PAGES_TARGETS="origin ghe" scripts/sync-pages.sh
#       Override the source and/or targets. PAGES_SOURCE may be a remote name, a
#       URL, or a local .git path — useful for recovery, e.g. pointing at the
#       runner's workspace repo when a bad push clobbered gh-pages on the remotes
#       but the good commit still lives in the runner's local gh-pages ref.
set -euo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

SOURCE="${PAGES_SOURCE:-ghe}"
TARGETS="${PAGES_TARGETS:-origin ghe}"

echo "Fetching gh-pages from '$SOURCE' ..."
git fetch --force "$SOURCE" gh-pages
SHA="$(git rev-parse FETCH_HEAD)"
FILES="$(git ls-tree -r --name-only "$SHA" | wc -l | tr -d ' ')"
MATRIX="$(git ls-tree -r --name-only "$SHA" | grep -c '^matrix/' || true)"
SUBJECT="$(git log -1 --format=%s "$SHA")"
echo "Source gh-pages: ${SHA:0:12}  ($FILES files, $MATRIX under matrix/)"
echo "  \"$SUBJECT\""

# Guard against publishing an obviously-empty site by mistake.
if [ "$FILES" -lt 10 ]; then
  echo "error: source gh-pages has only $FILES files — refusing to publish (set PAGES_SOURCE correctly)." >&2
  exit 1
fi

for r in $TARGETS; do
  echo "Force-pushing ${SHA:0:12} -> $r/gh-pages ..."
  git push --force "$r" "$SHA:refs/heads/gh-pages"
done

echo "Done — gh-pages is ${SHA:0:12} on: $TARGETS"
