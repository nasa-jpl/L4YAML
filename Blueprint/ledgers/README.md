# Ledgers

Dated snapshots of where a long-running proof target stands, read off a
named tree, so progress can be compared across dates instead of recollected.

## `parse_iff_grammar/`

One file per snapshot, `YYYY-MM-DD.md`, each with the same sections and row
keys (the first column of every table: `F1`…`B2`, `Row 12`, `S4 block`, …)
and a closing `## Instruments` table of `| key | value |` rows.  Keeping the
keys stable is what makes the diff mechanical; add a row rather than rename
one.

## Recipes

- **Take a snapshot.**  Copy the latest file to today's date, re-read every
  `State` cell and every instrument off the current tree (`git rev-parse
  --short HEAD`, `lake run docs-nav -- items --last 3`, the `PACK-RESIDUE`
  line of the last DOCS item, `Blueprint/04-capstones.md` row 7.7), and
  correct the previous snapshot's errors in the new file — never edit an
  old snapshot's content.
- **Diff the two newest snapshots:** `scripts/ledger_diff.py --latest`
  (add `--out /tmp/ledger-diff.md` to keep the report).
- **Diff any pair:** `scripts/ledger_diff.py Blueprint/ledgers/parse_iff_grammar/2026-10-25.md Blueprint/ledgers/parse_iff_grammar/2026-10-26.md`.
