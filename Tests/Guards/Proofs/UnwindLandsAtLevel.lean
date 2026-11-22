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

/-! # U3's scanner half, and the mirror that mirrors nothing (DOCS item 127)

Item 121 measured the under-indent invariant as three couplings and named U3
"the frames ↔ indent-stack coupling — an accumulation-invariant conjunct, the
widest of the three".  Pricing it turned up two things.

**The carrier a reader would reach for is empty.**  `BlockStack` is documented
as the accumulation's mirror of the scanner's indent stack, and its levels carry
a `col : Int` "matching scanner's `IndentEntry.column`".  Nothing in the library
builds a level: deleting `seqLevel` and `mapLevel` raises four errors, all of
them match arms in the two absorptions, and both matches are then total on `nil`
alone.  So the column was never read, and `BlockStack` is what `FlowStack`
already is — a position-identity marker.  The block nesting travels on the
PENDING, as `ResumeFrames`, and that is where a coupling has to go.

**The scanner knows more than `resumeAt` asks.**  `ResumeFrames.resumeAt` needs
the landing width to be a MEMBER of the frames.  Preprocessing's own two
inequalities pin it exactly: the trailing-content check refuses a popping
landing that sits deeper than what is left of the floor (item 66), and the
unwind loop stops as soon as the top is at or left of the column it unwinds to
(§1c) — so an accepted popping landing sits AT the top entry's column, and that
entry was already on the incoming stack.  §8.2.1 adds that the entry is not a
sequence.  What is missing is the other direction, from the surface: that every
open mapping level of `sc.indents` is one of the pending's frames.  That is the
conjunct U3 still owes, and it has no carrier today.

§1 pins the two markers' single constructor.  §2 types the scanner half.  §3 is
the runtime, measured: the dedent landings that compose, the sequence-level
landings the scanner refuses, and the no-level landings it refuses. -/

namespace L4YAML.Tests.Guards.UnwindLandsAtLevel

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.StreamAccum

/-! ## §1  The two markers carry one constructor each

A single-constructor match is the deletion's pin: an added level would make
each of these incomplete. -/

/-- The block marker: three coincident positions, and the match is TOTAL. -/
example {a b : SurfPos} (h : BlockStack a b) : a = b := by
  cases h with
  | nil => rfl

/-- …and the flow marker, the same. -/
example {a b : SurfPos} (h : FlowStack a b) : a = b := by
  cases h with
  | nil => rfl

/-- So the absorption is the incoming stream itself. -/
example {sp_start sp_gram sp_block sp_flow : SurfPos}
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block) (h_flow : FlowStack sp_block sp_flow) :
    SLYamlStream sp_start sp_flow :=
  absorb_stacks sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow

/-! ## §2  The scanner half, typed -/

/-- The unwind stops on its GUARD: the top ends at or left of the column, or
    only the sentinel is left. -/
example (s : ScannerState) (col : Int) :
    (unwindIndents s col).currentIndent ≤ col ∨
      (unwindIndents s col).indents.size ≤ 1 :=
  unwindIndents_terminal s col

/-- …and what it stops on was already there — the loop only pops. -/
example (s : ScannerState) (col : Int) (e : IndentEntry)
    (h : (unwindIndents s col).indents.back? = some e) : e ∈ s.indents :=
  unwindIndents_back_mem s col e h

/-- The two inequalities together: an accepted popping landing is AT an open
    level's own column, and that level is one the park already held.  (Item 128
    DISCHARGED the sentinel escape this conclusion used to carry as a
    `s_prep.indents.size ≤ 1` disjunct — the premise below is the scanner-wide
    base it needed; see `IndentBaseThreaded`.) -/
example {sc s_prep : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_pop : s_prep.indents ≠ sc.indents)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    ∃ e, s_prep.indents.back? = some e ∧ e ∈ sc.indents ∧
      e.column = (s_prep.col : Int) :=
  preprocess_landing_at_level hok h_pop h_base

/-- …and §8.2.1 says the level is a MAPPING level: a key at an open SEQUENCE
    level's own column does not validate. -/
example {s : ScannerState} {top : IndentEntry}
    (hok : scanValueValidate s = .ok ())
    (h_poss : s.simpleKey.possible = true) (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.simpleKey.pos.col : Int) = top.column)
    (h_le : (s.simpleKey.pos.col : Int) ≤ s.currentIndent) :
    top.isSequence = false :=
  scanValue_top_not_sequence hok h_poss h_noflow h_top h_at h_le

/-! ## §3  The same three cases on the runtime -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) && refuses input

-- (a) The landing names an open MAPPING level: the sibling composes, one
-- outer mapping, exactly as `ResumeFrames.resumeAt` reads it.
#guard emits "k:\n  a: 1\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a:\n    x: 1\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP", "=VAL :x",
   "=VAL :1", "-MAP", "-MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  :\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- …including a sequence whose column COINCIDES with the enclosing mapping's,
-- where the landing still names the mapping level (§8.2.1 does not fire, the
-- top after the pop is the map at column 0).
#guard emits "a:\n- x\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :x", "-SEQ", "=VAL :b",
   "=VAL :2", "-MAP", "-DOC", "-STR"]

-- (b) The landing names an open SEQUENCE level: §8.2.1 refuses it, so the
-- frames' mapping-only widths lose nothing by not recording it.
#guard scannerRefuses "a:\n  - x\n  b: 2\n"
#guard scannerRefuses "k:\n  - a: 1\n  b: 2\n"
#guard scannerRefuses "k:\n  - - x\n  b: 2\n"
#guard scannerRefuses "- - x\n  b: 2\n"
#guard scannerRefuses "a:\n  - x\n  b:\n"
#guard scannerRefuses "? k\n: - x\n  b: 2\n"

-- (c) The landing names NO level: preprocessing's own unwind check refuses it
-- before any dispatch runs (item 121 §2's family, restated here as the other
-- half of the same disjunction).
#guard scannerRefuses "k:\n    a: 1\n  b: 2\n"
#guard scannerRefuses "k:\n  a:\n      x: 1\n    b: 2\n"

end L4YAML.Tests.Guards.UnwindLandsAtLevel

end Blanket
