module

public import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Scanner.ScalarWalkColFloor
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The `?`-line bound's conclusion is the CURSOR's, and the walks pay it
(DOCS item 122)

Item 121 recorded U1 as "a live candidate saved on the pending `?`'s line
sits strictly right of `explicitKeyCol`", to be spent refuting item 104's
stale-key PAIR (`scanValueClearKey`'s `?`-line arm).  Pressure-testing that
statement against the actual spend site corrected it:

* **The recorded projection is TRUE but cannot refute the pair.**  The pair's
  decidable half is `(s.col : Int) = s.currentIndent` — a fact about the
  CURSOR — and no bridge leads from the KEY's column to it.  §1's witness
  `W` is machine-checked: the recorded bound holds, item 81's
  `KeysBehindCursor` core holds, `scanValueClearKey`'s `?`-line arm fires,
  and `scanValueValidate` still answers `.ok` — so every fact the recorded
  invariant supplies is consistent with the deferred arm.  Flipping ONLY the
  cursor bound (`W1`) flips the verdict to `misindentedExplicitValue`.
* **The sufficient conclusion is the cursor bound**: at a boundary state
  whose live candidate is saved on an EARLIER line,
  `s.currentIndent < (s.col : Int)`.  §2 pins it as a step-trace fold over
  the pinned families — including `a: 1⏎b⏎: 2`, where the plain walk's own
  gate (`contentIndent = currentIndent + 1`, NOT the walk's start column)
  keeps the park on the content's line.
* **The walks are the only makers of stale-live boundaries, and each pays
  its own floor** — `ScalarWalkColFloor` (landed with this item): a plain,
  double-quoted or single-quoted scan that ends off its entry line ends
  strictly past `currentIndent`.  §3 type-pins the three exports; §4 pins
  runtime non-vacuity (accepted multiline values crossing lines).

What remains of U1 (repriced): the invariant definition over the stale-live
premise, its preservation clone of `scanNextToken_preserves_KeysBehindCursor`
(the walk cases = §3's exports; the flow cases =
`FlowIndentStable.structural_none_col_gt_of_inFlow`; the fresh-save cases
vacuous by `pos.line = line`), the one-premise threading to
`accum_block_on_closeThenBlock`'s stale branch, and the spend replacing the
`by_cases` pair punt with `omega` against the pair's second conjunct — one
more session, not part of item 81's "pre-existing lemmas" claim. -/

namespace L4YAML.Tests.Guards.ScalarWalkCrossLineFloor

open L4YAML L4YAML.Scanner

/-! ## §1  The insufficiency witness

A raw scanner state (reachability not claimed — its unreachability is exactly
the invariant's content): block context, `?` frame from line 0 at column 0,
mapping indent 0, live key saved at (line 0, col 5, offset 2), cursor at
(line 1, col 0, offset 10). -/

private def W : ScannerState :=
  { input := "", inputEnd := 0, offset := 10, line := 1, col := 0,
    indents := #[{ column := -1, isSequence := false },
                 { column := 0, isSequence := false }],
    simpleKey := { possible := true, tokenIndex := 0,
                   pos := { offset := 2, line := 0, col := 5 }, endLine := 0 },
    explicitKeyLine := some 0, explicitKeyCol := 0 }

/-- The cursor bound is the ONE fact separating `W` from `W1`. -/
private def W1 : ScannerState := { W with col := 1 }

-- The recorded projection (key col strictly right of `explicitKeyCol`) HOLDS
-- at `W`, and so does `KeysBehindCursor`'s decidable core (item 81):
#guard (W.explicitKeyCol < (W.simpleKey.pos.col : Int)) &&
       (W.simpleKey.pos.offset < W.offset)
-- …and the clear that fires is the `?`-line arm, not the phantom arm:
#guard W.simpleKey.pos.offset != W.offset
#guard W.simpleKey.possible && !(scanValueClearKey W).simpleKey.possible
-- …yet the `:` VALIDATES — the deferred arm is consistent with everything
-- the recorded invariant supplies:
#guard (match scanValueValidate (scanValueClearKey W) with
        | .ok _ => true | .error _ => false)
-- The cursor bound is false at `W` — and it is the exact discriminant:
#guard !(W.currentIndent < (W.col : Int))
#guard W1.currentIndent < (W1.col : Int)
#guard (match scanValueValidate (scanValueClearKey W1) with
        | .error (.misindentedExplicitValue _ _ _) => true | _ => false)

/-! ## §2  The cursor form at every reachable boundary

`staleCursorOk` folds `scanNextToken` from the initial state and checks, at
every boundary, that a live candidate saved on an earlier line has the cursor
strictly past `currentIndent`. -/

private def staleCursorOkFrom (s : ScannerState) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    match scanNextToken s with
    | .error _ => true
    | .ok none => true
    | .ok (some s') =>
      (!(s'.simpleKey.possible && s'.simpleKey.pos.line != s'.line) ||
        decide (s'.currentIndent < (s'.col : Int))) &&
      staleCursorOkFrom s' fuel

private def staleCursorOk (input : String) : Bool :=
  staleCursorOkFrom (ScannerState.mk' input) (input.length * 2 + 8)

-- Item 104's refused PAIR family — the walks park stale-live, past the floor:
#guard staleCursorOk "? [1,\n 2]: v\n"
#guard staleCursorOk "? x\n y: v\n"
#guard staleCursorOk "? \"a\n b\": v\n"
-- The compact-in-key deep walk (`currentIndent` raised to 2 by `a:`; the
-- walk still parks at col 7):
#guard staleCursorOk "? a: b\n      c: v\n"
-- The sibling-column probe: the plain walk's gate is `currentIndent + 1`,
-- NOT the walk's start column, so `b`'s walk refuses the equal-column
-- landing and parks on its own line — no stale-live boundary at all:
#guard staleCursorOk "a: 1\nb\n: 2\n"
-- Accepted explicit-key families (fresh saves and under-indent stops keep
-- every boundary vacuous or past the floor):
#guard staleCursorOk "? a\n: v\n"
#guard staleCursorOk "? b\n: 2\n"
#guard staleCursorOk "? earth: blue\n: moon: white\n"
-- Flow restore: the ek pair and the key come back from their stacks at the
-- close, and the close's own column pays (`? [{a: b},\n   {c: d}]: v`):
#guard staleCursorOk "? [{a: b},\n   {c: d}]: v\n"
-- Multiline values (the walks' cross-line exits inside ACCEPTED inputs):
#guard staleCursorOk "k: a\n  b\n"
#guard staleCursorOk "k: \"a\n  b\"\n"
#guard staleCursorOk "k: 'a\n  b'\n"

/-! ## §3  The walk floors, as landed -/

example : ∀ {s s' : ScannerState}, s.inFlow = false →
    scanPlainScalar s = .ok s' → s'.line ≠ s.line →
    s.currentIndent < (s'.col : Int) :=
  fun h1 h2 h3 =>
    L4YAML.Proofs.ScalarWalkColFloor.scanPlainScalar_crossline_col_floor h1 h2 h3

example : ∀ {s s' : ScannerState}, s.peek? = some '"' →
    scanDoubleQuoted s = .ok s' → s'.line ≠ s.line →
    s.currentIndent < (s'.col : Int) :=
  fun h1 h2 h3 =>
    L4YAML.Proofs.ScalarWalkColFloor.scanDoubleQuoted_crossline_col_floor h1 h2 h3

example : ∀ {s s' : ScannerState}, s.peek? = some '\'' →
    scanSingleQuoted s = .ok s' → s'.line ≠ s.line →
    s.currentIndent < (s'.col : Int) :=
  fun h1 h2 h3 =>
    L4YAML.Proofs.ScalarWalkColFloor.scanSingleQuoted_crossline_col_floor h1 h2 h3

/-! ## §4  Runtime non-vacuity: the cross-line exits inside accepted inputs -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

#guard emits "k: a\n  b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a b", "-MAP", "-DOC", "-STR"]
#guard emits "k: \"a\n  b\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL \"a b", "-MAP", "-DOC", "-STR"]
#guard emits "k: 'a\n  b'\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL 'a b", "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScalarWalkCrossLineFloor

end Blanket
