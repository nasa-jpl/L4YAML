---
name: l4yaml-price-instruments
description: Run L4YAML's "price before proving" instruments — scripts/*_price.py, `lake exe scripts-flip scripts/flips/*.json`, `lake run flip-beta5`, `lake run beta5-arms`, `lake run punt-price`, `lake run drop-sweep` — safely (they edit library source in place and rebuild), read their classifications, and keep their pins agreeing. Use before any deletion, arity change, carrier addition, or when an item needs a count it must not recollect.
---

# Pricing instruments

Every number an item quotes is re-derived by a script in `scripts/`; the
scripts are the campaign's memory.  Read the docstring at the top of the one
you run — each states what it edits, what it restores, and which guard pins
its output.

## Families

| Script | Question it answers | Pin that must agree |
|---|---|---|
| `lake exe scripts-flip scripts/flips/<item>.json` (Lean, Rule 9) — one spec per flip: file, `rev`, anchored `old`/`new` pairs (each must match exactly once), target, tag; `--dry` checks anchors, `--rev` overrides, `--keep` leaves the patched tree; refuses when another `L4YAML/**` file differs between REV and the working tree (use a `git worktree` of REV) | A flip at a revision: which declarations break, how many sites, by owner | the item that cites it (416: `errors=4 decls=2`) |
| `lake run flip-beta5 [-- --max-rounds N --log-dir DIR --probe LEAN]` (Lean, Rule 9; `-- --dry` checks the anchors) | If `pendingFlow`/`scannerDrop` were deleted, what breaks to a fixpoint: `sorried / restated / deleted / pins` | `FIX-PIN` (`expectedFixpoint` in `ParkBill.lean`) |
| `lake run beta5-arms [-- --end control|arms --log-dir DIR]` (Lean, Rule 9) | Which constructor arms are dead vs live obligations | `ARM-PIN` (`expectedArms` in `ParkBill.lean`) |
| `lake run beta5-map -- LOG` | The declarations enclosing a build log's error locations (item 230's mapper) | — |
| `scripts/flips/item210_implicit_continue.json`, `item375_flip211_stage1.json` (the `[211]` price), `item415_inl_declines.json` (via `scripts-flip`); `item238_scanner_drop.json`, `item233_flow_key_head.json`, `item246_carrier_{arm,retire}.json`, `item240_supplier_{weak,field,retire,producer}.json` (the four loaders of `flip_210.py`, as specs; the `rev` of each is the last tree its anchors matched); `lake exe scripts-flip-census` (Lean, Rule 9) | Narrowing / carrier / supply-side flips | see each docstring |
| `close_price.py`, `inline_class_price.py`, `lake run price -- carrier|wire [--wide]|arm|coordinate|transport|ride [MODE]` (items 266–273, Lean; the `wide` mode of the last three is a `lake build`; `all`/`arm` check `expectedCarrierPrice`/`expectedWirePrice`/`expectedArmTable`), `lake run punt-price`, `lake run price -- park-top|vslot-top|mv-slot-top|open-map|park-nic0|landing-nic0` (items 205–210, Lean) | Cost of one specific change, by producer/consumer | `expected…` strings in `Tests/Guards/Proofs/` |
| `lake run drop-sweep [-- -q]` | Acceptance sweep (generates `L4YAML/Scratch/*.lean`, removes them) | — (a sweep says REACHED at most; it is not a proof obligation) |
| `narrow_conclusion.py`, `pay_chain_optional.py`, `decline_all_optional.py`, `lake exe scripts-theorem-keyword --rewrite` | Mechanical source transforms used by items | — |

## Protocol

1. **Never concurrently with `lake build`** or with another instrument: they
   patch `L4YAML/Proofs/Production/StreamAccum.lean` (and others) in place
   and rebuild.  Wait for any build to finish (`pgrep -f 'lake build'`).
2. Start from a clean tree (`git status --porcelain` empty) so the restore
   check is meaningful.
3. Run with output captured: `mkdir -p scratch && lake run price -- X [MODE] > scratch/NNN-X.log 2>&1`
   (or the instrument's own `lake run …` line from the table above).  `scratch/` may
   not exist yet; only its `*.log` files are gitignored (`.gitignore` has `*.log` and
   `/Scratch`, not lowercase `scratch/`), so keep nothing else there or step 4's
   `git status --porcelain` check will show it.
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

Only when no existing instrument answers the question.  Write it in Lean as a
`Scripts/Price/*.lean` module plus a `scripts-price` sub-command (copy the
shape of `Scripts/Price/Ride.lean` + `rideCmd` in `Scripts/Main/Price.lean`):
a module docstring that states the question, what is edited, how it is
restored (`Scripts.Price.Env.leanOn` backs up, restores and prints both
digests), `#guard` rows for the pure parts, and the pin it must agree with.
Add the pin to a `Tests/Guards/Proofs/*.lean` guard so the build re-derives
it.  Hold a mode out of the gate battery if it rebuilds >100 modules (the
`wide` modes), and say so in the docstring.
