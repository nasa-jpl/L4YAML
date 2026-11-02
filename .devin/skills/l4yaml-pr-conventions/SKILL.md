---
name: l4yaml-pr-conventions
description: Branch, commit and PR conventions specific to Open-MBEE/L4YAML — fork vs upstream, the fix-a-grammar-completeness base branch (not develop/main), one item per PR, commit subject style from the closure log, and what to run before pushing. Use when creating a branch, committing, or opening/updating a PR on L4YAML.
---

# PRs on L4YAML

This repo overrides the generic Open-MBEE git-flow note: there is no
`develop` here.

- **Remote:** work goes directly to `nasa-jpl/L4YAML` (since 2026-10-21):
  push branches there and open PRs there.  `Open-MBEE/L4YAML` is the old
  fork; do not open new PRs on it.
- **Base branch:** `fix-a-grammar-completeness`.  `main` is release-only.
  ```bash
  git fetch origin && git checkout -B <type>/<slug> origin/fix-a-grammar-completeness
  ```
- **Scope:** one closure-log item, or one fix, per PR; not stacked.  The
  owner merges fast — review findings go in a follow-up PR, never amend a
  merged one, never leave a fix half-pushed.
- **Commit subjects** (from the log): `feat(row 12): step 12.3.3 — …`,
  `docs(row 12): item N — …`, `test(guards): re-pin … after …`,
  `proof(<module>): …`, `fix(scanner): …`, `chore(scripts): …`.
- **Before pushing:** full `lake build` exit 0, the text gates and
  `gate_vocab.py` green, `lake run check-closure-log` green if DOCS.md
  changed, `git status --porcelain` empty (pricing scripts restored).
- **PR body:** what moved, the numbers with the pin that re-derives each, the
  item number if DOCS.md gained one.  No session identifiers, no internal
  URLs.
- **CI:** self-hosted runner; it may queue for a long time.  Report the local
  battery in the PR; do not wait on CI to call the work done.
- **Toolchain / dependency pins:** ask the owner before changing
  `lean-toolchain` or `lake-manifest.json`.
