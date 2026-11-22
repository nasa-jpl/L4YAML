module

public import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Scanner.StaleCursorFloor
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The stale-cursor floor, landed and spent (DOCS item 123)

Item 122 corrected U1's conclusion to a CURSOR bound and landed the walks'
cross-line floors; this item lands the invariant itself and spends it:

* **`StaleKeyCursorFloor`** (§1's `rfl` pin): in block context, a live saved
  key from an earlier line puts the cursor strictly past `currentIndent`.
  Preserved by `scanNextToken` (the `KeysBehindCursor` skeleton: the walks
  pay via `ScalarWalkColFloor`'s cross-line floors and §3b's same-line
  column monotonicity; preprocessing fresh-saves across block breaks; a
  flow close's own bracket cleared the structural flow floor; everything
  else clears, saves on the cursor's line, or stays in flow).
* **The spend**: `colon_fires_implicit_key`'s stale branch no longer punts
  on item 104's `[197]` pair — `(s_prep.col : Int) = s_prep.currentIndent`
  is refuted by the floor carried across the no-break step, so the stale-key
  `:` is refuted OUTRIGHT (`invalidImplicitKey` / the pair now both
  machine-decided).  `KeyPackPunt.noFrame` / `.noKeyContext` (U2) and
  `.dedent` (R4) are unchanged here (`noFrame` went at item 125, `dedent` at
  item 297).
* §2 re-checks the invariant in its EXACT landed form (with the block-context
  premise) as a step-trace fold over the pinned families, and §4 pins the
  accepted multiline families' event streams — the change is byte-invisible
  to the pipelines (zero runtime edits). -/

namespace L4YAML.Tests.Guards.StaleCursorFloorInvariant

open L4YAML L4YAML.Scanner

/-! ## §1  The invariant and its preservation, as landed -/

example : L4YAML.Proofs.StaleCursorFloor.StaleKeyCursorFloor =
    fun s : ScannerState =>
      s.inFlow = false → s.simpleKey.possible = true →
        s.simpleKey.pos.line ≠ s.line → s.currentIndent < (s.col : Int) := rfl

example : ∀ {s s' : ScannerState},
    scanNextToken s = .ok (some s') →
    L4YAML.Proofs.StaleCursorFloor.StaleKeyCursorFloor s →
    L4YAML.Proofs.StaleCursorFloor.StaleKeyCursorFloor s' :=
  fun h1 h2 =>
    L4YAML.Proofs.StaleCursorFloor.scanNextToken_preserves_StaleKeyCursorFloor
      _ _ h1 h2

example : ∀ {s s2 : ScannerState} {c : Char},
    scanNextToken_preprocess s = .ok (some (s2, c)) →
    L4YAML.Proofs.StaleCursorFloor.StaleKeyCursorFloor s →
    L4YAML.Proofs.StaleCursorFloor.StaleKeyCursorFloor s2 :=
  fun h1 h2 =>
    L4YAML.Proofs.StaleCursorFloor.preprocess_preserves_StaleKeyCursorFloor h1 h2

-- The walks' same-line exits only move the column right (§3b, this item's
-- other half of the walk fuel):
example : ∀ {s s' : ScannerState}, s.inFlow = false →
    scanPlainScalar s = .ok s' → s'.line = s.line → s.col ≤ s'.col :=
  fun h1 h2 h3 =>
    L4YAML.Proofs.ScalarWalkColFloor.scanPlainScalar_sameline_col_ge h1 h2 h3

example : ∀ {s s' : ScannerState}, s.peek? = some '"' →
    scanDoubleQuoted s = .ok s' → s'.line = s.line → s.col ≤ s'.col :=
  fun h1 h2 h3 =>
    L4YAML.Proofs.ScalarWalkColFloor.scanDoubleQuoted_sameline_col_ge h1 h2 h3

example : ∀ {s s' : ScannerState}, s.peek? = some '\'' →
    scanSingleQuoted s = .ok s' → s'.line = s.line → s.col ≤ s'.col :=
  fun h1 h2 h3 =>
    L4YAML.Proofs.ScalarWalkColFloor.scanSingleQuoted_sameline_col_ge h1 h2 h3

/-! ## §2  The landed form at every reachable boundary

Item 122's fold checked the premise-free cursor form; the LANDED invariant
carries the block-context premise, so the fold here is its exact decidable
mirror — seeded at `mk'` and checked after every `scanNextToken`. -/

private def floorHolds (s : ScannerState) : Bool :=
  !(!s.inFlow && s.simpleKey.possible && s.simpleKey.pos.line != s.line) ||
    decide (s.currentIndent < (s.col : Int))

private def staleFloorOkFrom (s : ScannerState) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    match scanNextToken s with
    | .error _ => true
    | .ok none => true
    | .ok (some s') => floorHolds s' && staleFloorOkFrom s' fuel

private def staleFloorOk (input : String) : Bool :=
  floorHolds (ScannerState.mk' input) &&
  staleFloorOkFrom (ScannerState.mk' input) (input.length * 2 + 8)

-- Item 104's refused PAIR family — the walks park stale-live, past the floor:
#guard staleFloorOk "? [1,\n 2]: v\n"
#guard staleFloorOk "? x\n y: v\n"
#guard staleFloorOk "? \"a\n b\": v\n"
-- The compact-in-key deep walk:
#guard staleFloorOk "? a: b\n      c: v\n"
-- The sibling-column probe (the plain walk is self-flooring):
#guard staleFloorOk "a: 1\nb\n: 2\n"
-- Accepted explicit-key families:
#guard staleFloorOk "? a\n: v\n"
#guard staleFloorOk "? earth: blue\n: moon: white\n"
-- Flow restore at the close:
#guard staleFloorOk "? [{a: b},\n   {c: d}]: v\n"
-- Multiline values (cross-line walk exits inside ACCEPTED inputs):
#guard staleFloorOk "k: a\n  b\n"
#guard staleFloorOk "k: \"a\n  b\"\n"
#guard staleFloorOk "k: 'a\n  b'\n"
-- Multiline quoted scalars standing as (refused) implicit keys — the stale
-- key rides a no-break preprocess into the `:`'s own dispatch:
#guard staleFloorOk "k: \"a\n  b\": v\n"
#guard staleFloorOk "k: 'a\n  b': v\n"
-- The directive dispatch (its collect loops stay on the line):
#guard staleFloorOk "%YAML 1.2\n--- a\n"
-- A root flow crossing lines, closed back into block context at EOF:
#guard staleFloorOk "[a,\n b]\n"

/-! ## §3  The spend's family is refused for its own reason, unchanged

`? x⏎ y: v` was the pair's flagship input: the continuation line's `y: v`
puts a stale key at the `:`.  It is scanner-refused (both pipelines), and
the accepted explicit-key reading (`? x⏎: v`) still emits — the spend
changed proofs, not bytes. -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refused (input : String) : Bool :=
  (match Events.streamToEvents input with | .ok _ => false | .error _ => true) &&
  (match Events.streamToEventsIx input with | .ok _ => false | .error _ => true)

#guard refused "? x\n y: v\n"
#guard refused "? [1,\n 2]: v\n"
#guard refused "k: \"a\n  b\": v\n"
#guard emits "? x\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :x", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "[a,\n b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "%YAML 1.2\n--- a\n"
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]

end L4YAML.Tests.Guards.StaleCursorFloorInvariant

end Blanket
