---
name: l4yaml-price-instruments
description: Run L4YAML's "price before proving" instruments — scripts/*_price.py, flip_*.py, beta5_arms.py, punt_reason_price.py, drop_sweep.py — safely (they edit library source in place and rebuild), read their classifications, and keep their pins agreeing. Use before any deletion, arity change, carrier addition, or when an item needs a count it must not recollect.
---

# Pricing instruments

Every number an item quotes is re-derived by a script in `scripts/`; the
scripts are the campaign's memory.  Read the docstring at the top of the one
you run — each states what it edits, what it restores, and which guard pins
its output.

## Families

| Script | Question it answers | Pin that must agree |
|---|---|---|
| `flip_beta5.py` | If `pendingFlow`/`scannerDrop` were deleted, what breaks to a fixpoint: `sorried / restated / deleted / pins` | `FIX-PIN` (named in the script) |
| `beta5_arms.py` | Which constructor arms are dead vs live obligations | `ARM-PIN` |
| `flip_210.py`, `flip_carrier.py`, `flip_supply.py`, `flip_supplier.py`, `flip_drop.py`; `lake exe scripts-flip-census` (Lean, Rule 9) | Narrowing / carrier / supply-side flips | see each docstring |
| `ride_price.py`, `close_price.py`, `carrier_price.py`, `wire_price.py`, `transport_price.py`, `coordinate_price.py`, `arm_price.py`, `inline_class_price.py`, `punt_reason_price.py`, `*_top_price.py`, `*_nic0_price.py`, `open_map_price.py` | Cost of one specific change, by producer/consumer | `expected…` strings in `Tests/Guards/Proofs/` |
| `drop_sweep.py` | Acceptance sweep (generates `L4YAML/Scratch/*.lean`, removes them) | — (a sweep says REACHED at most; it is not a proof obligation) |
| `narrow_conclusion.py`, `pay_chain_optional.py`, `decline_all_optional.py`, `rename_lemma.py` | Mechanical source transforms used by items | — |

## Protocol

1. **Never concurrently with `lake build`** or with another instrument: they
   patch `L4YAML/Proofs/Production/StreamAccum.lean` (and others) in place
   and rebuild.  Wait for any build to finish (`pgrep -f 'lake build'`).
2. Start from a clean tree (`git status --porcelain` empty) so the restore
   check is meaningful.
3. Run with output captured: `python3 scripts/X_price.py … > scratch/NNN-X.log 2>&1`.
4. Afterwards confirm the restore: the script prints md5 before/after; also
   `git status --porcelain` must be empty.  If not, `git checkout -- <file>`
   and say so in the item.
5. Read the classification, not the headline: *sorried* = a proof broke but
   the statement holds; *restated* = the statement itself no longer
   type-checks; *deleted* = the declaration goes with the thing deleted;
   *pins* = guard strings that move (instrument debt, not proof debt).
6. The number goes into the item **with the pin that agrees with it**.  If
   the pin disagrees, the pin or the script is stale — fix whichever is
   wrong before quoting (§9: how many readings was this taken over?).

## Writing a new instrument

Only when no existing script answers the question.  Copy the shape of
`ride_price.py`: docstring that states the question, what is edited, how it
is restored (checksums both sides), and the pin it must agree with.  Add the
pin to a `Tests/Guards/Proofs/*.lean` guard so the build re-derives it.
Hold a script out of the gate battery if it rebuilds >100 modules
(`coordinate_price.py`'s note), and say so in its docstring.
