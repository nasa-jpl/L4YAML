module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The bare-document fallback, named and half refuted (DOCS item 139)

Items 117, 136 and 137 gave the content landing's route face its SUFFIX, HEAD
and MARKER arms.  What they left is the fallback — a completed top-level node
appended to a FINISHED stream as a second bare document, `[211]`'s implicit
continuation with `[207] l-bare-document` in its `l-any-document?` slot — and
what the fallback owed was items 132–134's refusal, threaded to the
accumulation as a contradiction rather than restated as prose.

This item threads it, and MEASURES that it covers exactly half of the
fallback's domain.  The discriminator is the indent stack, and the two halves
are two different mechanisms:

* **the stack is the sentinel alone** — the landed node is a second bare
  document, `scanNextToken_checkBareDocument` fires AT the landing, and the
  accumulation step for that node never runs.  Refutable, and refuted;
* **a level is still open** — the same input is a DANGLING run, and
  `danglingNodePos?` reads the run off the TOKEN ARRAY, so the run has to be
  scanned before the check can see it.  The refusal lands at the NEXT landing,
  or at `scanLoop`'s end.  The step therefore runs, the park it makes owes a
  stream, and this route is the only reading `[211]` has for it.

§1 measures that split on the real scanner: `fireAt` walks `scanNextToken` and
reports which check fired and at which landing.  §2 is the same split read off
the check's own definition.  §3 is `CompletedTail`, the park face the refutation
spends, and the one payment every content dispatch makes for it.  §4 is the
three transports that carry the park's reading to the landing.  §5 is the
fallback at its type, guarded and unguarded.  §6 is what remains.

No runtime file is touched, so every verdict below is the one the pipelines
already gave. -/

namespace L4YAML.Tests.Guards.StreamBareDocumentFallback

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.FlowAdjacency (LastTokenReal)

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-! ## §1  Which check fires, and at which landing

`fireAt` is the step chain read back: at every landing it asks
`scanNextToken_checkDanglingNode` and `scanNextToken_checkBareDocument` the
question `scanNextToken` asks them, in that order, and then takes the step.
The landing index counts landings, so `bare@2` says the refusal happened
BEFORE the node on line 2 was ever scanned, and `eof-dangling@N` says the
scanner accepted every landing and `scanLoop`'s final validation refused. -/

private def fireAt (s : ScannerState) (n : Nat) : Nat → String
  | 0 => "fuel"
  | fuel + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => "preprocess-error"
    | .ok none =>
      match scanLoop_checkDanglingNode s with
      | .error _ => s!"eof-dangling@{n}"
      | .ok _ => "clean"
    | .ok (some (s1, _)) =>
      match scanNextToken_checkDanglingNode s s1 with
      | .error _ => s!"dangling@{n}"
      | .ok _ =>
        match scanNextToken_checkBareDocument s1 with
        | .error _ => s!"bare@{n}"
        | .ok _ =>
          match scanNextToken s with
          | .ok (some s') => fireAt s' (n + 1) fuel
          | .ok none => "no-step"
          | .error _ => "step-error"

private def fires (input : String) : String :=
  fireAt (ScannerState.mk' input) 0 40

-- THE REFUTED HALF.  No block level is open, so the stack at the landing is
-- the sentinel alone and the check fires there — landing 1, before `b`'s own
-- token exists.  (`a⏎b` is ONE multi-line plain scalar; it takes a comment
-- line to stop the walk and reach the landing at all.)
#guard fires "a\n# c\nb\n" == "bare@1"
#guard fires "\"x\"\n# c\ny\n" == "bare@1"
#guard fires "'x'\n# c\ny\n" == "bare@1"
#guard fires "a\n# c\n  b\n" == "bare@1"          -- the landing's column is free
#guard fires "[1, 2]\n# c\nb\n" == "bare@5"       -- a flow close completes too
#guard fires "&p a\n# c\nb\n" == "bare@2"         -- the run's SCALAR completes it
#guard refuses "a\n# c\nb\n"
#guard refuses "\"x\"\n# c\ny\n"
#guard refuses "[1, 2]\n# c\nb\n"

-- THE SURVIVING HALF.  A level at the landing's own column is open, so the
-- bare-document check stands aside and the DANGLING run is what has no
-- production — but the run's token has to exist first, so the refusal is at
-- `scanLoop`'s end and the accumulation step for the run DID run.
#guard fires "a: 1\nb\n" == "eof-dangling@4"
#guard fires "- a\nb\n" == "eof-dangling@3"
#guard fires "k:\n  a\n# c\nb\n" == "eof-dangling@4"
#guard fires "k: [1, 2]\nb\n" == "eof-dangling@8"
#guard refuses "a: 1\nb\n"
#guard refuses "- a\nb\n"

-- …and mid-stream the same run dies one landing later, not at its own.
#guard fires "a: 1\nb\nc: 2\n" == "dangling@4"
#guard fires "a: 1\nb\n...\n" == "dangling@4"

-- THE LEGAL CONTROLS.  Nothing fires, at any landing.
#guard fires "a: 1\nb: 2\n" == "clean"
#guard fires "- a\n- b\n" == "clean"
#guard fires "a: 1\n...\nb\n" == "clean"          -- the `...` opens the next document
#guard fires "a: 1\n---\nb\n" == "clean"
#guard emits "a: 1\n...\nb\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "=VAL :b", "-DOC", "-STR"]

/-! ## §2  The same split, read off the check itself

Three of `scanNextToken_checkBareDocument`'s four conjuncts are what the
landing already holds; the fourth is the stack, and it is the whole
discrimination.  Item 145 reads it at the landing's own COLUMN rather than at
the stack's size. -/

/-- Resting ON an open level the check stands aside — this is the dangling
    family's exemption, stated as the check's own reading rather than as
    prose. -/
example (s : ScannerState)
    (h : (s.indents.any fun e => e.column == (s.col : Int)) = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.not_true, Bool.and_false,
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- And with all four it is an error, which is the shape the refutation
    contradicts. -/
example (s : ScannerState) (t : YamlToken)
    (h_flow : s.inFlow = false) (h_ska : s.simpleKeyAllowed = true)
    (h_sz : (s.indents.any fun e => e.column == (s.col : Int)) = false)
    (h_t : lastRealTokenVal? s.tokens = some t)
    (h_c : t.completesFlowValue = true) :
    scanNextToken_checkBareDocument s = .error (.invalidBareDocument s.line s.col) := by
  unfold ScannerState.inFlow at h_flow
  simp [scanNextToken_checkBareDocument, ScannerState.inFlow, h_flow, h_ska, h_sz,
        h_t, h_c]

/-! ## §3  `CompletedTail`, and the payment every content dispatch makes

`StaleNodeTail` (item 47) is `CompletedTail` plus two LINE facts — `needIndentCheck`
and `simpleKeyAllowed` both DOWN — and neither survives a park at a line start:
the block scalar ends past a break with the flag up, and the break sets the
indent check.  §9.2's landing refusal wants the opposite polarity of the flag
and never reads the indent check, so the half a park can carry unconditionally
is the half that mentions neither. -/

/-- The projection: a stale tail is a node tail. -/
example {sc : ScannerState} (h : StaleNodeTail sc) : CompletedTail sc := h.toCompletedTail

/-- The converse fails at the block scalar, and that is why the field is a new
    one: `stale_of_dispatch` REFUTES its residue there instead of paying. -/
example {s s' : ScannerState} (hok : scanBlockScalar s = .ok s') : CompletedTail s' :=
  completedTail_scanBlockScalar hok

/-- The one payment, per dispatcher: every content scan but the two `[96]`
    property heads finishes a node, and the token array says so with no premise
    about the line at all. -/
example {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (h_amp : c ≠ '&') (h_bang : c ≠ '!') : CompletedTail s' :=
  completedTail_of_dispatch hok h_amp h_bang

/-- The property heads are the exclusion, and it is `completesFlowValue`'s own:
    a `[96]` run precedes a node rather than finishing one.  This is also why
    `pendingProps` gets no field, and why `pendingFlow` — whose producer is the
    block INDICATOR dispatch's escape — gets none either. -/
example : (YamlToken.anchor "p").completesFlowValue = false := by decide
example : (YamlToken.tag "!" "t").completesFlowValue = false := by decide
example : YamlToken.blockEntry.completesFlowValue = false := by decide
example : YamlToken.key.completesFlowValue = false := by decide
example : YamlToken.value.completesFlowValue = false := by decide
example : YamlToken.blockEnd.completesFlowValue = false := by decide
example : (YamlToken.scalar "a" .plain).completesFlowValue = true := by decide
example : YamlToken.flowSequenceEnd.completesFlowValue = true := by decide

/-! ## §4  The three transports

The park's reading is about `sc`; the check reads `s_prep`.  Preprocessing has
three writers between them, and the STACK decides all three. -/

/-- The unwind is the identity at the sentinel alone — the loop's own guard
    wants `1 < s.indents.size`.  This is what keeps the `blockEnd` tokens that
    would displace the reading from ever being emitted. -/
example {s : ScannerState} {col : Int} (h : s.indents.size ≤ 1) :
    unwindIndents s col = s := unwindIndents_of_size_le_one h

/-- So the token reading and the stack both cross the landing unchanged. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_size : sc.indents.size ≤ 1) (h_real : LastTokenReal sc.tokens)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    lastRealTokenVal? s_prep.tokens = lastRealTokenVal? sc.tokens ∧
      s_prep.indents = sc.indents :=
  preprocess_lastRealTokenVal_of_indents_le_one h_size h_real h

/-- The flag only goes UP: a park that carries it hands it to the landing.
    This is the column-0 landing's source, off item 76/77's park arm. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_a : sc.simpleKeyAllowed = true)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.simpleKeyAllowed = true := preprocess_simpleKeyAllowed_mono h_a h

/-- …and the break-crossed landing's source is the WALK, which is item 76's own
    hypothesis read at the flag rather than at the save it gates. -/
example {sc s_prep s_walk : ScannerState} {c : Char}
    (h_skip : skipToContent sc = .ok s_walk)
    (h_a : s_walk.simpleKeyAllowed = true)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.simpleKeyAllowed = true := preprocess_simpleKeyAllowed_of_walk h_skip h_a h

/-- All conjuncts together: the contradiction, at its type.  The stack reading
    is two premises since item 145 — the landing did not dedent, and it rests on
    no open level. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_open : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false)
    (h_tail : CompletedTail sc) : False :=
  bareDocument_refutes_landing h_bare h_pre h_noflow h_ska h_base h_open h_tail

/-! ## §5  The fallback, guarded and unguarded

Naming it is half the item: three call sites built the same term inline, so the
surface was three applications of `implicitContinue` where it is now one
lemma to refute. -/

/-- The route itself — the reading row 19's 1c deletes. -/
example {sp_start sp_anchor : SurfPos} (h : SLYamlStream sp_start sp_anchor) :
    ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m → SLYamlStream sp_start sp_m :=
  bareNodeRoute h

/-- …and the same route with §9.2's landing refusal taken out of its domain.
    The park's arm is `Or.inl` for the two content parks and `Or.inr` for the
    parks whose tail is not a node body. -/
example {sc s_prep : ScannerState} {c : Char} {sp_start sp_anchor : SurfPos}
    (h_stream : SLYamlStream sp_start sp_anchor)
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_tail : CompletedTail sc ∨ True) :
    ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m → SLYamlStream sp_start sp_m :=
  bareNodeRoute_or_refused h_stream h_bare h_pre h_noflow h_ska h_base h_tail

/-- A park with no `CompletedTail` still gets the route: the guard is a NARROWING,
    not a deletion. -/
example {sc s_prep : ScannerState} {c : Char} {sp_start sp_anchor : SurfPos}
    (h_stream : SLYamlStream sp_start sp_anchor)
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m → SLYamlStream sp_start sp_m :=
  bareNodeRoute_or_refused h_stream h_bare h_pre h_noflow h_ska h_base (Or.inr trivial)

/-! ## §6  What remains

`SLYamlStream.implicitContinue` stands at **eight** applications in **eight**
holders (down from ten in nine), and flipping its `[210]` slot to
`GOpt SLExplicitDocument` gives **six** errors in `StreamAccum` (down from
eight) at six lemmas: `topLevelFlowResumeSep`, `rootMapRoute`, `rootMapRouteF`,
`bareNodeRoute`, `structural_dispatch_to_pending` and
`accum_block_on_closeThenBlock`.  Two of those are not over-approximations at
all — `structural_dispatch_to_pending`'s is a `---` document continuing a
stream implicitly, and the flip merely deletes its `SLAnyDocument.explicit`
wrapper (`DocumentProduction.stream_implicit_continue` is the same shape).

What the fallback still serves, measured in §1:

* **the dangling family** — `a: 1⏎b`, `- a⏎b`, `k:⏎  a⏎# c⏎b`.  These reach
  `content_dispatch_after_close` and the landing skeleton's unrefuted arm, and
  they are NOT a gap in the argument: the scanner accepts the run's own step
  and refuses at the next landing, so the accumulation genuinely owes a stream
  for one token.  Closing this half means giving the park a `danglingNodePos?`
  face — the run is already in the token array when the park is made — not a
  better reading of `[211]`.  (Read with DOCS item 140: sizing that face found
  that the INDENTED members of this family were refused by the PARSER only,
  because the landing's unwind displaced the run before the mid-stream check
  saw it.  `Tests/Guards/Proofs/ScannerDanglingNodeDedent.lean` is that
  refusal, and the face has something to contradict now.);
* **the flow lane** — `accum_flow_open_depth0`'s shared `main`, where
  `topLevelFlowResumeSep` is the same fallback for a completed flow
  collection.  Its refutation is this item's, one dispatcher over: `h_bare`
  threaded through `accum_step_flow`, and the park arm it already takes for the
  suffix face;
* **the block `-` landing** — `accum_block_on_closeThenBlock`'s
  `rootBlockSeq`, and `rootMapRoute`/`rootMapRouteF`, the key routes the same
  landings take when the node turns out to be a KEY. -/

end L4YAML.Tests.Guards.StreamBareDocumentFallback

end Blanket
