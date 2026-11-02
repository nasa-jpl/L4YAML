---
name: l4yaml-orientation
description: First ten minutes on Open-MBEE/L4YAML — where the sources of truth are, how to find the active mandate in the 45k-line DOCS.md with scripts/docs_nav.py, and what not to re-derive. Use at the start of any session touching L4YAML proofs, guards, or docs.
---

# L4YAML orientation

1. Read `AGENTS.md` (one screen of rules, build, gates, vocabulary).
2. Confirm the branch: `git status -sb` — work happens on
   `fix-a-grammar-completeness` on `nasa-jpl/L4YAML` (the fork `Open-MBEE/L4YAML` is retired for new work), not `main`.
3. Find the mandate, never by paging DOCS.md:
   ```bash
   lake run docs-nav -- next            # latest item's **NEXT —** paragraph
   lake run docs-nav -- items --last 5  # what the last five items did
   lake run docs-nav -- steps           # Row 12 six-step table with state
   lake run docs-nav -- remaining       # open six-step rows, then the dated dependency chain
   lake run docs-nav -- item 264        # read one item in full
   lake run docs-nav -- grep -i 'noKeyContext'   # which items touched a name
   ```
4. Before trusting any count or name from memory or from an older item:
   grep the tree (`rg -n 'name' L4YAML Tests`) and read the pin that already
   holds it (`rg -n 'expected' Tests/Guards/Proofs | rg 'name'`).  Rule 6.
5. Project-level next steps (not the campaign) are `README.md` → *Next steps*;
   capstone status is `Blueprint/04-capstones.md`.  Neither is restated in DOCS.md.
6. If the task is a proof: `l4yaml-adversarial-before-proof` first, then
   `l4yaml-closure-item` for the record-keeping.  If it is a measurement:
   `l4yaml-price-instruments`.  If a build is red or a pin moved:
   `l4yaml-build-and-gates`.

What not to do: start a `lake build` and a pricing script together; open a
PR against `main` or `develop`; add a `theorem` that is not a capstone; write
a count into prose that no guard pins.
