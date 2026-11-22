module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Proofs.Scanner.BlockScalarFlowGuard

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Block scalars inside flow collections are rejected (DOCS item 9c)

`c-l+literal` [170] and `c-l+folded` [174] are reachable only through
`s-l+block-node` [196]; `ns-flow-content` [158] offers plain, flow-seq,
flow-map, single- and double-quoted only.  A block-scalar header inside a flow
collection therefore has no derivation, and before item 9c the scanner admitted
it — `[a, |⏎  x⏎]` scanned clean at 15 tokens in **both** pipelines, which is
what left β.3's flow-interior content step with an arm it could not refute.

These guards pin the strictening on both pipelines at once.  `yaml-test-suite`
has **no** case of this shape (a full sweep moved 0 of 406 cases), so the suite
scores cannot catch a regression here — this file is the only regression net.
-/

namespace Tests.Guards.ScannerBlockScalarInFlow

open L4YAML
open L4YAML.Scanner

/-- Legacy and indexed verdicts, as a comparable pair: `none` on success,
    `some e` on rejection.  Equal pairs mean the two pipelines agree. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` with the same `blockScalarInFlow` error. -/
private def rejects9c (input : String) (indicator : Char) (line col : Nat) : Bool :=
  verdicts input == (some (.blockScalarInFlow indicator line col),
                     some (.blockScalarInFlow indicator line col))

/-- Both pipelines accept `input`. -/
private def bothAccept (input : String) : Bool := verdicts input == (none, none)

/-! ## §1  The shapes item 9c rejects

Position is pinned too: a caller that reports the error must point at the
header, not at the enclosing collection. -/

-- Flow sequence, literal and folded.
#guard rejects9c "[a, |\n  x\n]\n" '|' 0 4
#guard rejects9c "[a, >\n  x\n]\n" '>' 0 4
-- Flow mapping, literal and folded.
#guard rejects9c "{k: |\n  x\n}\n" '|' 0 4
#guard rejects9c "{k: >\n  x\n}\n" '>' 0 4
-- First entry of the collection (no preceding `,`).
#guard rejects9c "[|\n  x\n]\n" '|' 0 1
-- Nested both ways.
#guard rejects9c "{k: [a, |\n  x\n]}\n" '|' 0 8
#guard rejects9c "[{k: |\n  x\n}]\n" '|' 0 5
-- Header with a chomping / explicit-indent modifier.
#guard rejects9c "[a, |-\n  x\n]\n" '|' 0 4
#guard rejects9c "[a, >2\n   x\n]\n" '>' 0 4
-- Flow opened from block context — `inFlow`, not the document root, decides.
#guard rejects9c "top:\n  - [a, |\n      x\n    ]\n" '|' 1 8

/-! ## §2  Block context is untouched

The guard reads `s.inFlow`, so every `s-l+block-node` [196] position still
scans exactly as before. -/

#guard bothAccept "k: |\n  x\n"                  -- block mapping value
#guard bothAccept "k: >\n  x\n"                  -- folded
#guard bothAccept "- |\n  x\n"                   -- block sequence entry
#guard bothAccept "|\n  x\n"                     -- document root
#guard bothAccept "k: |-\n  x\n"                 -- with chomping indicator
#guard bothAccept "a:\n  b: |\n    x\n  c: 1\n"  -- nested, with a sibling after
#guard bothAccept "a: [1, 2]\nb: |\n  x\n"       -- after a flow collection closes
#guard bothAccept "- [1, 2]\n- |\n  x\n"         -- flow sibling, then block scalar

/-! ## §3  `|` and `>` that are *not* block-scalar headers

The guard fires on the dispatcher's `|`/`>` arm only, so these keep scanning:
quoted content never reaches it, and a plain scalar that merely *contains*
`|`/`>` is dispatched on its first character. -/

#guard bothAccept "[a, \"|\"]\n"
#guard bothAccept "{k: '>'}\n"
#guard bothAccept "[a>b]\n"
#guard bothAccept "[a|b]\n"

/-! ## §4  Flow basics, unchanged -/

#guard bothAccept "[a, b]\n"
#guard bothAccept "{a: 1, b: 2}\n"
#guard bothAccept "[]\n"
#guard bothAccept "[[a, [b, {c: [d]}]]]\n"

/-! ## §5  The proof-side handle

`dispatchContent_not_blockScalar_of_inFlow` is the fact item 9c exists to
provide: it is what lets β.3's flow-interior content step refute the
`SCLLiteral ∨ SCLFolded` disjuncts that `dispatchContent_evidence` still
offers.  Pinned by axiom profile, not by a `sorry`-free warning — a delegated
proof can be sorry-free and still ride `sorryAx` through a dependency. -/

open L4YAML.Proofs.BlockScalarFlowGuard in
/-- info: 'L4YAML.Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dispatchContent_not_blockScalar_of_inFlow

open L4YAML.Proofs.BlockScalarFlowGuard in
/-- info: 'L4YAML.Proofs.BlockScalarFlowGuard.blockScalarGuard_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blockScalarGuard_elim

end Tests.Guards.ScannerBlockScalarInFlow

end Blanket
