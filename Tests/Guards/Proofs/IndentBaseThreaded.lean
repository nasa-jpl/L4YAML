module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The indent stack's base, threaded (DOCS item 128)

Item 127 read a popping landing's column off the top entry and had to carry one
escape: `s_prep.indents.size ≤ 1`, a stack popped to a single entry.  That entry
is the sentinel at column `-1`, which no landing column equals — but saying so
is `ScannerState.WellFormed`'s sixth conjunct, and the accumulation carried no
`WellFormed` at all (it is preserved for `advance` and `emit` only).

This item carries the sixth conjunct ALONE — `IndentStackBase.SentinelBase`, a
statement about `indents[0]?` — through every scanner step, in the shape the two
other whole-scanner field walks already use (`ScannerFlowStackPreservation`,
`ScannerEkStackPreservation`).  The stack has exactly four writers
(`pushMappingIndent`, `pushSequenceIndent`, `unwindIndentsLoop` and
`scanValuePrepare`'s own `push`) and each keeps index 0: a push writes past the
end, and the unwind's guard stops at size 1.  So
`preprocess_landing_at_level` is an equation outright now, with no disjunct.

**The escape's family, measured** (§2).  A stack popped to its base is what an
INDENTED root leaves behind — `  a: 1` pushes a mapping level at column 2 over
the sentinel — and every landing to the left of it is `trailingContent` in both
pipelines, at the column the landing sits at rather than at the level's.  The
comment line, the `...` and the `---` do not save it: preprocessing unwinds
before any of them is dispatched.

§1 types the invariant, its seed and its step.  §2 is the runtime.  §3 types the
landing equation, which no longer offers the escape. -/

namespace L4YAML.Tests.Guards.IndentBaseThreaded

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.IndentStackBase L4YAML.Proofs.StreamAccum

/-! ## §1  The invariant, its seed, and its step -/

/-- The predicate is the sixth conjunct, packaged so it carries non-emptiness. -/
example (s : ScannerState) :
    SentinelBase s ↔ s.indents[0]? = some { column := -1, isSequence := false } :=
  Iff.rfl

/-- The seed: the scanner starts on the sentinel alone. -/
example (input : String) : SentinelBase (ScannerState.mk' input) := mk'_base input

/-- The step: every `scanNextToken` keeps it. -/
example {s s' : ScannerState} (hok : scanNextToken s = .ok (some s'))
    (h : SentinelBase s) : SentinelBase s' := scanNextToken_base hok h

/-- …and the two consequences item 127's escape needed: a base is non-empty, and
    a stack that is ONLY its base sits at `-1`. -/
example {s : ScannerState} (h : SentinelBase s) : 0 < s.indents.size := h.size_pos

example {s : ScannerState} (h : SentinelBase s) (hsz : s.indents.size ≤ 1) :
    s.currentIndent = -1 := h.currentIndent_of_size_le_one hsz

/-- The four writers, each keeping index 0. -/
example (s : ScannerState) (col : Int) (h : SentinelBase s) :
    SentinelBase (unwindIndents s col) := unwindIndents_base s col h

example (s : ScannerState) (col : Int) (h : SentinelBase s) :
    SentinelBase (pushMappingIndent s col) := pushMappingIndent_base s col h

example (s : ScannerState) (col : Int) (h : SentinelBase s) :
    SentinelBase (pushSequenceIndent s col) := pushSequenceIndent_base s col h

example (s : ScannerState) (h : SentinelBase s) :
    SentinelBase (scanValuePrepare s) := scanValuePrepare_base s h

/-! ## §2  The escape's family on the runtime -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) && refuses input

/-- Both scanners accept: the input is not this family's. -/
private def scansClean (input : String) : Bool :=
  match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
  | .ok _, .ok _ => true
  | _, _ => false

-- (a) An indented root really does leave a level over the sentinel — and while
-- nothing lands to its left, that is ordinary YAML.
#guard emits "  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "  a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2",
   "-MAP", "-DOC", "-STR"]

-- (b) The escape's own shape — a landing that would pop the last real level —
-- is `trailingContent` in both pipelines, whatever stands at the landing.
#guard scannerRefuses "  a: 1\nb: 2\n"
#guard scannerRefuses "  a: 1\n b: 2\n"
#guard scannerRefuses "  a: 1\n- y\n"
#guard scannerRefuses "  - x\ny: 1\n"
#guard scannerRefuses "  - x\n- y\n"
#guard scannerRefuses "  a:\n    b: 1\nc: 2\n"
-- …and neither a comment line nor a document marker saves it: preprocessing
-- unwinds before any of them is dispatched.
#guard scannerRefuses "  a: 1\n# c\nb: 2\n"
#guard scannerRefuses "  a: 1\n...\nb: 2\n"
#guard scannerRefuses "  a: 1\n---\nb: 2\n"

-- (c) The ORDINARY dedent, for contrast: a level survives the pop, the landing
-- sits at its column, and item 127's equation is about exactly this.
#guard emits "a:\n  b: 1\nc: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :1", "-MAP",
   "=VAL :c", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard accepts "  a:\n    b: 1\n  c: 2\n"

-- (d) The boundary that says the refusal comes from the POP and not from the
-- column: a root flow node pushes no level at all, so this landing pops
-- nothing and the trailing-content check has no reason to fire.  What refuses
-- it is §9.2 — a completed ROOT node with content on a later line — which the
-- scanner runs since item 132 (`ScannerBareDocumentRefusal`).
#guard !scansClean "  [1, 2]\nb: 2\n"
#guard refuses "  [1, 2]\nb: 2\n"

/-! ## §3  The landing equation, with the escape gone -/

/-- Item 127's conclusion, now unconditional: an accepted popping landing sits
    AT an open level's own column, on an entry the park already held. -/
example {sc s_prep : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_pop : s_prep.indents ≠ sc.indents)
    (h_base : SentinelBase sc) :
    ∃ e, s_prep.indents.back? = some e ∧ e ∈ sc.indents ∧
      e.column = (s_prep.col : Int) :=
  preprocess_landing_at_level hok h_pop h_base

end L4YAML.Tests.Guards.IndentBaseThreaded

end Blanket
