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

/-! # The frames cover the indent stack (DOCS item 129)

Item 127 read a popping landing from the SCANNER's side — the column it rests at
is the top entry's own, on an entry the incoming stack already held — and item
128 removed that reading's escape.  `ResumeFrames.resumeAt` asks the SURFACE
question about the same landing: is that width one of the still-open mapping
frames?  The two meet only if every open mapping level of `sc.indents` is a
frame, which is what `IndentStackCover.Covered` says and this item carries
through every scanner step.

**The stack moves in four places and the frames pay at one class of them.**  The
unwind POPS; `[183]`'s `-` opens a SEQUENCE level, which the frames deliberately
do not record; and the three MAPPING pushes are `[187]`'s `?` (at the
indicator's column) and `scanValuePrepare`'s two — the implicit key's column
`[193]`, and the keyless entry's own `:` `[196]`.  So a step is `CoverStep`: the
cover survives, or exactly one mapping level opened, at the top — which is where
item 127 reads the landing from.

**Why the sequence level is exempt, and where that is settled** (§3).  A dedent
landing that rests on a sequence level is `trailing content` when a `:` or a `?`
consumes it (§8.2.1, `scanValue_top_not_sequence` and, since item 131,
`scanKey_top_not_sequence`) and ordinary YAML when a `-` does.  The check lives
in each indicator's own validation, so the refutation is something the CONSUMER
spends, not something the landing carries — item 125's shape.

§1 types the predicate, its transports, its seed and its step.  §2 is the
runtime: the three mapping pushes, each resumed at its own column, and the
sequence level that is not a frame.  §3 is the two ends — the spend and the
refuter — with the discriminating triple.  §4 takes the same discrimination at
the EXPLICIT key. -/

namespace L4YAML.Tests.Guards.FramesCoverIndents

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.IndentStackCover L4YAML.Proofs.StreamAccum

/-! ## §1  The predicate, its transports, its seed, and its step -/

/-- The predicate: every mapping level at or right of the floor is a frame.
    (Item 130 gave `Covered` its floor; at `lo = 0` it is item 129's statement,
    and `0 ≤ e.column` is what exempts the sentinel there.) -/
example (lo : Nat) (ks : List FrameLevel) (s : ScannerState) :
    Covered lo ks s ↔
      ∀ e ∈ s.indents, e.isSequence = false → (lo : Int) ≤ e.column →
        FrameLevel.map e.column.toNat ∈ ks :=
  Iff.rfl

/-- The seed: the sentinel alone is covered by any frames, `[]` included. -/
example (input : String) : Covered 0 [] (ScannerState.mk' input) := mk'_cover input 0 []

/-- The step: a `scanNextToken` either keeps the cover, or opens ONE mapping
    level at the top and the frames gain exactly its column. -/
example {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : Covered lo ks s) :
    Covered lo ks s' ∨ ∃ c : Nat,
      s'.indents.back? = some { column := (c : Int), isSequence := false } ∧
        Covered lo (FrameLevel.map c :: ks) s' :=
  scanNextToken_cover hok h

/-- The four transports: an equal stack, a popped stack, more frames, one more
    frame. -/
example {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} (h : Covered lo ks s)
    (heq : s'.indents = s.indents) : Covered lo ks s' := h.of_indents_eq heq

example {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} (h : Covered lo ks s)
    (hsub : ∀ e ∈ s'.indents, e ∈ s.indents) : Covered lo ks s' := h.of_subset hsub

example {lo : Nat} {ks ks' : List FrameLevel} {s : ScannerState} (h : Covered lo ks s)
    (hsub : ∀ fr ∈ ks, fr ∈ ks') : Covered lo ks' s := h.mono hsub

example {lo : Nat} {ks : List FrameLevel} {s : ScannerState} (c : Nat) (h : Covered lo ks s) :
    Covered lo (FrameLevel.map c :: ks) s := h.cons c

/-- The writers: the unwind pops, `[183]` is exempt, `[187]` is the payment. -/
example {lo : Nat} {ks : List FrameLevel} {s : ScannerState} (col : Int) (h : Covered lo ks s) :
    Covered lo ks (unwindIndents s col) := unwindIndents_cover col h

example {lo : Nat} {ks : List FrameLevel} {s : ScannerState} (col : Int) (h : Covered lo ks s) :
    Covered lo ks (pushSequenceIndent s col) := pushSequenceIndent_cover col h

example {lo : Nat} {ks : List FrameLevel} {s : ScannerState} (c : Nat) (h : Covered lo ks s) :
    Covered lo (FrameLevel.map c :: ks) (pushMappingIndent s (c : Int)) := pushMappingIndent_cover c h

/-! ## §2  The three mapping pushes on the runtime -/

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

/-- Both scanners accept: the input is not the refusal's family. -/
private def scansClean (input : String) : Bool :=
  match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
  | .ok _, .ok _ => true
  | _, _ => false

-- (a) Each mapping push, resumed at its own column by a later sibling: the
-- implicit key `[193]`, the explicit `?` `[187]`, and the keyless `:` `[196]`.
#guard accepts "a:\n  b:\n    x: 1\n  c: 2\n"
#guard accepts "a:\n  ? b\n  : c\n  d: 1\n"
#guard accepts "a:\n  : v\n  b: 1\n"

-- (b) …and the sequence level, which is NOT a frame: the same landing column
-- resumes for a `-` entry and is `trailing content` for a `:`.
#guard accepts "a:\n  - x\n  - y\n"
#guard scannerRefuses "a:\n  - x\n  b: 2\n"

/-! ## §3  The two ends -/

/-- **The spend.**  With the cover on the park's state, item 127's equation
    reads as MEMBERSHIP — which is what `ResumeFrames.resumeAt` asks — unless
    the landing rests on a sequence level. -/
example {sc s_prep : ScannerState} {c : Char} {lo : Nat} {ks : List FrameLevel}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_pop : s_prep.indents ≠ sc.indents)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_floor : lo ≤ s_prep.col)
    (h_cov : Covered lo ks sc) :
    FrameLevel.map s_prep.col ∈ ks ∨
      ∃ e, s_prep.indents.back? = some e ∧ e.isSequence = true ∧
        e.column = (s_prep.col : Int) :=
  preprocess_landing_mem_or_seq hok h_pop h_base h_floor h_cov

/-- **The refuter.**  A `:` that validates at the landing's column has a mapping
    level under it, so the landing is a frame outright. -/
example {lo : Nat} {ks : List FrameLevel} {s : ScannerState} {top : IndentEntry}
    (hok : scanValueValidate s = .ok ())
    (h_poss : s.simpleKey.possible = true) (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.simpleKey.pos.col : Int) = top.column)
    (h_le : (s.simpleKey.pos.col : Int) ≤ s.currentIndent)
    (h_floor : lo ≤ s.simpleKey.pos.col)
    (h_cov : Covered lo ks s) :
    FrameLevel.map s.simpleKey.pos.col ∈ ks :=
  landing_mem_of_value hok h_poss h_noflow h_top h_at h_le h_floor h_cov

-- The discriminating triple, on ONE landing column, with a POP under it (the
-- spend's own `h_pop`): the popping landing rests on a mapping level and
-- resumes; rests on a sequence level and is refused by the `:`; rests on the
-- same sequence level and resumes for a `-`.
#guard accepts "a:\n  b:\n    x: 1\n  c: 2\n"
#guard scannerRefuses "a:\n  - b:\n      x: 1\n  c: 2\n"
#guard accepts "a:\n  - b:\n      x: 1\n  - c: 2\n"

-- …and the same three at the shallower depth where nothing pops, which is where
-- §8.2.1's check alone carries the refusal.
#guard accepts "- a: 1\n  b: 2\n"
#guard scannerRefuses "a:\n  - x\n  : c\n"
#guard emits "a:\n  - x\n  - y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :x", "=VAL :y", "-SEQ",
   "-MAP", "-DOC", "-STR"]

/-! ## §4  The EXPLICIT key at the same landing

The exemption is a statement about the frames, not about the input: a landing on
a sequence level is refused by every indicator that opens a MAPPING entry there,
and `scanKey_top_not_sequence` is the `?`'s half of that (item 131,
`ScannerExplicitKeySequenceIndent`).  The pair below is the same
discrimination as §3's, taken at the `?` instead of at the `:`: the mapping
landing emits one document and the sequence landing is refused. -/

#guard emits "a:\n  b:\n    x: 1\n  ? c\n  : 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+MAP", "=VAL :x",
   "=VAL :1", "-MAP", "=VAL :c", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
#guard scannerRefuses "a:\n  - b:\n      x: 1\n  ? c\n  : 2\n"

end L4YAML.Tests.Guards.FramesCoverIndents

end Blanket
