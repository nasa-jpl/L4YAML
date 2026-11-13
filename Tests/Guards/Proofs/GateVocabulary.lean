/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.Scanner

@[expose] public section Blanket

/-! # A name in prose is a claim about the environment (DOCS items 265, 266)

§8.1's floor for a flow open is read at the CLOSE (item 172), and the check
that reads it is `scanNextToken_checkFlowValueIndent`.  The name the prose kept
using for an open-side check, `scanNextToken_checkBlockFlowIndent`, resolves to
no constant at all, and item 265 found it in thirty-two places across fourteen
files — describing a
dispatcher layer `scanNextToken` does not have, and in one place carrying a
claim about a PROOF: that the run-end half of the flow open's under-run "is not
a deferral at all", two lines above the `exact drop_ride` that rides β.5's
escape on exactly that half.

A backticked identifier in a docstring is a claim, and it is the one class of
claim nothing in the build checks.  Lean does not read its own comments; a
census that reads the environment cannot see them.  So the reading is
`lake run check-gate-vocab`'s (`Scripts/Lean/GateVocab.lean`) and the LITERAL is here — the same
pin-from-the-other-side the flip instruments use, turned on prose.

Two vocabularies are read.  The first is the dispatcher's own:
`scanNextToken_…`, `scanLoop_…` and `scanLoopIx_…` spelled out, and the short
`check…` form the prose usually uses, which is required to carry two
capitalized segments so that one-letter macros stay out of it.  The second is
the tree's suffix for a lemma that closes a branch as false, `…_refuted`, added
at item 266 after a second phantom of the same kind turned up in exactly the
place item 265 had just been working: a docstring naming the run-end
refutation as the twin an existing lemma is one production in from, when
items 264-266 measured that no such lemma can be stated at that step.  A name
resolves when it is the final component of a constant in the wide environment,
bare or under any of the three prefixes.

Three numbers stand beside the verdict, because each is a way the check could
pass while reading less than it appears to (§9):

* `families` — references of the form `dispatchStructural_none_*`, which name a
  family and not a constant.  Excluded from the verdict rather than matched.
* `wrapped` — a name a line break splits, whose closing backtick the scan
  cannot see.  Two are genuine wraps in `…FlowMonoChain.Sync.Scenarios.Endpoint`
  and resolve when joined; the third is a `` `` ``-quoted name in
  `PuntCoverInputs`, which the elaborator resolves itself.  A gate's wrap is
  found from its opening half, which carries the prefix; a refutation's cannot
  be, since the suffix is the whole discrimination, so those are found from the
  CONTINUATION line instead, and the continuation is recognized
  without requiring the underscore, which the break may leave on either side.
* `refuted` — how many of the names come from the second vocabulary.  A
  widening that read none of them would pass the same verdict as one that read
  them all.
* `self` — this file's own two mentions.  It has to spell the missing gate out
  in order to say what the check is for, so it is the one file the scan skips,
  and the skip is counted rather than silent.
-/

namespace L4YAML.Tests.Guards.GateVocabulary

/-- What `lake run check-gate-vocab` reads over `L4YAML/` and `Tests/`.

    **`mentions` moves whenever prose cites a gate, and that is the point.**
    Item 268's own sections added four, across two dispatcher names it had to
    cite by name, and all four resolve.  Item 269's add six and retire one, over
    three names: the step function whose check its rail measurement prices, the
    check itself, and the step function whose equation its restated source
    spends — six because the scan reads comments and the three new signatures
    that name the last of those are code.  Item 275's add two, over the two
    checks whose success it carries beside §9.2's; both resolve, and `names`
    does not move because neither check is a new name to the prose.
    Items 280–281's prose in `ScannerFlowOpenUnderRun` adds four, all resolving,
    over three step functions and one check (`names` unmoved); one wildcard
    `…_preserves_*` is the fourteenth family, and one check split by a line
    break is the fourth wrap.  Re-pinned after the fact, when the script
    disagreed with the literal on an otherwise green tree.
    `unresolved` is what the check is for;
    `mentions` is the population it was taken over, and a `mentions` that never
    moved would mean the scan had stopped seeing new prose.  (The names are not
    spelled here: this file is the one the scan skips, so a name written in this
    docstring would move `self` instead, for no reading.) -/
-- 2026-10-22: re-pinned from `scripts/gate_vocab.py` (now `lake run check-gate-vocab`) on the fix-a branch — the literal had been 448 since item 265's
-- successors added gate names to Lean docstrings (items 332–340 each reported the drift as pre-existing); the
-- script is the reading, this literal is the pin, and a disagreement is an item's to repin, not to record.
-- 2026-10-23: 111/466 → 113/468 — the Step 5 status row names two new gates (`parseStream_accepts`,
-- `TokenGrammar`'s module) from Stream D.
-- 2026-10-23 (item 348): 468 → 469 — the `DispatchPrice`/`ParkGapWidth` pin notes name the preprocess step
-- function once more (`preprocess_col0_dead` holds its equation).
-- 2026-10-23 (item 349): 469 → 470 — the item-349 record names a gate in its Gates paragraph.
-- S5 slice 2 (2026-10-28): mentions 476 → 479 — `Tests/Guards/Proofs/TokenEventExtractors.lean` cites three gates in its findings.
-- Item 373 (2026-10-27): mentions 472 → 475 — the entry's prose cites three more gates.
-- S5 slice 2 guard, review round (2026-10-28): mentions 479 → 482 — the Priority 52 bucket's docstring names
-- the grammar and state checkers it runs.
-- S5 slice 2 (2026-10-28): names 113 → 112 — the per-token state checker of `TokenGrammar` (a check-prefixed
-- name, so a gate to this census) is retired with its extractor; `TokenStateOk` is stated over
-- `TokenEvents.tokenEvents` directly.  (Not spelled here: it would move `self`.)
-- S5 slice 2 landing (2026-10-28): mentions 482 → 478 — the seam record's prose spells the retired
-- check-prefixed name without backticks (it no longer resolves) and drops its `ev₁` rows.
-- Item 387 review round (2026-10-29): mentions 478 → 479 — the Priority 58b paragraph names the
-- scanner preprocess entry it walks once more; no name added or retired.
-- Item 430 (2026-11-04): mentions 484 → 485 — Priority 86's docstring names the content dispatch
-- step it calls directly on the seq-top key landings (not spelled here: it would move `self`); no name
-- added or retired.
-- 2026-11-05 (capstone 7.7 S3 (b)): mentions 485 → 491 — the Priority 87 grid's prose names the scanner
-- entry points and the two directive refusals it instantiates.
-- 2026-11-07 (item 447): names 113 → 114, mentions 491 → 495 — item 447's prose names the gates once more (S3 (β2a)).
-- 2026-11-07 (item 449): mentions 495 → 497 — item 449's prose names the gates it ran (S3 (β2b)).
-- 2026-11-08 (item 450): mentions 497 → 499 — item 450's Gates paragraph names the gates (S3 (a), `TagShape`).
-- 2026-11-08 (item 454): mentions 499 → 501 — item 454's Gates paragraph names the gates it ran (S3 proper, READ).
-- 2026-11-08 (item 459, review): mentions 501 → 503 — item 459's gate paragraph names `DispatchPrice` and `ParkGapWidth` rows.
-- 2026-11-08 (item 463, S3 slice (2)): mentions 503 → 506 — item 463's gate paragraph names the guard rows it moved.
-- 2026-11-08 (item 464, S3 slice (3) first PR): mentions 506 → 515 — item 464's gate paragraph names the seven guard files it re-pinned.
-- 2026-11-08 (item 464, review): mentions 515 → 516 — the corrected key-context finding names `check-…` once more.
-- 2026-11-11 (item 484, ContentArm): mentions 516 → 517 — the `ContentArm` docstring names the content dispatch
-- step it is read off (not spelled here: it would move `self`); no name added or retired.
-- 2026-11-12 (item 484, review round 1): names 114 → 115, mentions 517 → 519 — Priority 112's docstring names the
-- flow-value indent check the scanner refuses an under-indented continuation with, and the preprocess / block-indicator
-- dispatch steps it re-derives the arm from (not spelled here: it would move `self`).
def expectedGateVocab : String :=
  "names=115 mentions=519 families=14 refuted=7 wrapped=4 self=2 unresolved=0"

end L4YAML.Tests.Guards.GateVocabulary

end Blanket
