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

/-! # The content park's own column (DOCS item 77)

Item 76 gave the landed `:` its floor for every park OFF a line start: a break
re-arms `simpleKeyAllowed` outside a flow, so a park that had to cross one to
reach a column-0 landing knows preprocessing re-SAVED.  What it could not fund
was the park AT a line start, and `landing_save_or` handed `True` back there.

Item 77 is the other half, and it is a column rather than a flag.  A block
scalar is the one content scan that parks at column 0, and it re-arms when it
does (`[170]`/`[174]` end past a break).  Every other content scan ends on a
character it consumed: the quoted scans on their closing quote, the alias and
the tag on their name, and the plain walk because it MOVED — the dispatcher's
own guards forbid every `collectPlainScalar_terminates?` exit at the walk's
first character, and `collectPlainScalarLoop_col_or_stuck` says a walk that
moves ends off column 0.

So `dispatchContent_col_pos_or_armed` holds for every content character, the
five parks carry it as a field (`PendingNode.pendingContent.h_arm` and
siblings), `landing_or_park_save` spends the pair, and `colon_open_map`'s floor
is a MEASUREMENT: the `∨ True` items 27/74/76 kept alive is gone.

§1–§3 are compile-time witnesses of the types; §4 pins the runtime measurement
that says the refuted park is refuted for a reason and the surviving one is
reached.
-/

namespace Tests.Guards.ContentParkColumn

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge L4YAML.Proofs.LineOpenGuard
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.CharPredicates

/-! ## §1  Every content dispatch parks armed or off a line start

The disjunction is stated for an ARBITRARY content character — the property
arms included, which is what lets the escape (`pendingFlow`) and the two
content parks carry the same field.  Since item 80 the armed side carries the
cleared key too: the one armed content scan is the block scalar, and §8.1
clears the save on its way out, so an armed park and a live pack cannot
coexist. -/

example {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hpk : s.peek? = some c)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    (s'.simpleKeyAllowed = true ∧ s'.simpleKey.possible = false) ∨ 0 < s'.col :=
  dispatchContent_arm_or_col_any hflow hpk hnotdoc hok

/-! ## §2  The plain walk's own column, and the premise it rests on

`hnotdoc` is not decoration: `---` at column 0 IS a `terminates?` exit at the
walk's first character, and the walk then returns its entry state unchanged.
The structural dispatch takes that input first (§4), which is exactly why the
premise is available where the content producers need it. -/

example {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hpk : s.peek? = some c)
    (hstart : canStartPlainScalarBool c (s.peekAt? 1) false = true)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false)
    (hok : scanPlainScalar s = .ok s') :
    0 < s'.col :=
  scanPlainScalar_col_pos hflow hpk hstart hnotdoc hok

/-! ## §3  The landed `:` measures its floor at EVERY input

`landing_or_park_save` joins item 76's landing with item 77's park, and the
pair is exhaustive: no `∨ True`, no `by_cases` at the call site. -/

example {sc s_prep s' : ScannerState} {sp_prep sp_scan : SurfPos} {k : Nat}
    (hcol_prep : sp_prep.col = k)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_noflow_disp : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).inFlow = false)
    (h_noflow : s_prep.inFlow = false)
    -- Item 139: the landing arm carries the walk's FLAG as its third reading.
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      -- Item 147: the landed arm carries a FOURTH reading now — the landing's
      -- own floor — and these two consumers project past it exactly as they
      -- project past item 139's flag.
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (h_park : sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, ':')))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) ':' = .ok (some s')) :
    -- Item 179: the floor reads at the SHIFTED index, off the same save.
    IndentFloor s' (k + 1) :=
  indicator_floor_colon_at_col_of_save hcol_prep hcorr_prep h_noflow_disp
    (landing_or_park_save h_noflow h_larm h_park h_preprocess) h_preprocess h_dispatch

/-! ## §4  The measurement: the walk moves, and the one input where it does not

`plainParksOffLineStart` runs `scanPlainScalar` at offset 0 in block context.
Every routed shape leaves the cursor off a line start — including the ones that
fold across a break, land at column 0 and are handed back the BREAK's state by
the caller's `result.content.length ≤ prevLen` test.  The single exception is
the document boundary, and `structuralTakesFirst` says the dispatcher never
offers it to the content arm. -/

private def plainParksOffLineStart (input : String) : Bool :=
  match scanPlainScalar (ScannerState.mk' input) with
  | .ok s => 0 < s.col
  | .error _ => true

-- One line, then a fold that lands at column 0 on a `:`, on content, on a
-- document marker, on a comment, on a blank line, at end of input, on a tab.
#guard plainParksOffLineStart "a\n"
#guard plainParksOffLineStart "a\n: b"
#guard plainParksOffLineStart "a\nb: c"
#guard plainParksOffLineStart "a\n---"
#guard plainParksOffLineStart "a\n..."
#guard plainParksOffLineStart "a\n#c"
#guard plainParksOffLineStart "a\n\n"
#guard plainParksOffLineStart "a\n   "
#guard plainParksOffLineStart "a\nb\n"
#guard plainParksOffLineStart "a\nb\n---"
#guard plainParksOffLineStart "a\n\tb"

-- The refuted case is REAL: a `terminates?` exit at the walk's own first
-- character returns the entry state, and at column 0 that state is at a line
-- start.  This is what `hnotdoc` buys.
#guard !plainParksOffLineStart "---"
#guard !plainParksOffLineStart "--- "
#guard !plainParksOffLineStart "..."

/-- …and it never reaches the content arm: `scanNextToken_dispatchStructural`
    answers `some` on it, so the content producers' `h_not_doc` is available. -/
private def structuralTakesFirst (input : String) (c : Char) : Bool :=
  match scanNextToken_dispatchStructural (ScannerState.mk' input) c with
  | .ok (some _) => true
  | _ => false

#guard structuralTakesFirst "---\n" '-'
#guard structuralTakesFirst "--- a\n" '-'
#guard structuralTakesFirst "...\n" '.'

/-! ### The other content scans

The block scalar parks at column 0 and re-arms; the quoted scans, the alias and
the tag end on a character they consumed. -/

private def scanArm (f : ScannerState → Except ScanError ScannerState)
    (input : String) : Bool :=
  match f { ScannerState.mk' input with definedAnchors := #["a"] } with
  | .ok s => s.simpleKeyAllowed || 0 < s.col
  | .error _ => true

#guard scanArm scanDoubleQuoted "\"a\nb\""
#guard scanArm scanSingleQuoted "'a\nb'"
#guard scanArm (fun s => scanAnchorOrAlias s false) "*a"
#guard scanArm (fun s => scanAnchorOrAlias s true) "&a"
#guard scanArm scanTag "!t x"
#guard scanArm scanTag "!!str x"
#guard scanArm scanTag "!<tag:x> y"
#guard scanArm scanBlockScalar "|\n  x\n"
#guard scanArm scanBlockScalar ">\n  x\n"

/-! ### The inputs the closed floor now carries

`a: b⏎: w` and `? a⏎: v` are item 76's rows; `a: |⏎  x⏎: 1` is item 77's — a
`:` landing at column 0 behind a CONTENT park that sits at one. -/

private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

#guard emits "a: |\n  x\n: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "a: b\n: w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :", "=VAL :w", "-MAP", "-DOC", "-STR"]

end Tests.Guards.ContentParkColumn

end Blanket
