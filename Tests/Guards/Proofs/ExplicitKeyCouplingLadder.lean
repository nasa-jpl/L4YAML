module

public import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Scanner.ExplicitKeyCoupling
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
public meta import L4YAML.Scanner.State
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The explicit-key coupling's scanner half (DOCS item 124)

U2 of the under-indent map is a scanner↔surface coupling: a park that cannot
refute `explicitKeyLine` owes the `?` frame's face.  This item lands the
SCANNER half — the transport ladder for `explicitKeyLine`/`explicitKeyCol`
(item 101's `implicitValueLine` ladder, transposed twice) and the LINE-FREE
`scanValue` discriminators that mirror the epilogue's own `explicitValue`
computation conjunct by conjunct:

* §1 pins the discriminators at their landed types — the three stamp routes
  (no pending `?`; the `:` off the frame's column; a resolved key) and the
  two `explicitKeyLine` post-facts (consumed at any coordinate ≤ the frame's
  column; survival preserves the column register from a live pre-state).
* §2 re-checks the register discipline as a step-trace fold: at every
  reachable boundary a live `explicitKeyLine` carries a non-negative
  `explicitKeyCol`, and so does every stacked pair — the coordinate the
  coupling's column conjunct threads.
* §3 pins the register TRACES the ladder describes on the item's measured
  families — the `?` sets the pair, content scans and landings carry it, the
  flow open parks it and the close restores it, the landed `:` AT the column
  consumes it without stamping, the keyed `:` beneath it stamps, and the
  `,` ends the entry.
* §4 pins the families' verdicts on both pipelines. -/

namespace L4YAML.Tests.Guards.ExplicitKeyCouplingLadder

open L4YAML L4YAML.Scanner

/-! ## §1  The discriminators, as landed -/

example : ∀ {s s' : ScannerState},
    scanValue s = .ok s' → s.inFlow = false → s.peek? = some ':' →
    s.explicitKeyLine = none →
    s'.implicitValueLine = some s'.line ∧ s'.explicitKeyLine = none :=
  fun h1 h2 h3 h4 =>
    L4YAML.Proofs.ExplicitKeyCoupling.scanValue_ok_of_ekl_none h1 h2 h3 h4

example : ∀ {s s' : ScannerState},
    scanValue s = .ok s' → s.inFlow = false → s.peek? = some ':' →
    (s.col : Int) ≠ s.explicitKeyCol →
    s'.implicitValueLine = some s'.line :=
  fun h1 h2 h3 h4 =>
    L4YAML.Proofs.ExplicitKeyCoupling.scanValue_stamp_of_col_ne h1 h2 h3 h4

example : ∀ {s s' : ScannerState},
    scanValue s = .ok s' → s.inFlow = false → s.peek? = some ':' →
    s.simpleKey.possible = true → s.simpleKey.pos.offset ≠ s.offset →
    s.simpleKey.pos.line = s.line →
    s'.implicitValueLine = some s'.line :=
  fun h1 h2 h3 h4 h5 h6 =>
    L4YAML.Proofs.ExplicitKeyCoupling.scanValue_stamp_of_key h1 h2 h3 h4 h5 h6

example : ∀ {s s' : ScannerState},
    scanValue s = .ok s' →
    (s.simpleKey.possible = true → (s.simpleKey.pos.col : Int) ≤ s.explicitKeyCol) →
    (s.col : Int) ≤ s.explicitKeyCol →
    s'.explicitKeyLine = none ∨
    ∃ cols pks, s'.explicitKeyLine = (PendingKeys.close cols pks s.explicitKeyCol).2.1 ∧
      s'.explicitKeyCol = (PendingKeys.close cols pks s.explicitKeyCol).2.2 :=
  fun h1 h2 h3 =>
    L4YAML.Proofs.ExplicitKeyCoupling.scanValue_ekl_none_of_col_le h1 h2 h3

example : ∀ {s s' : ScannerState},
    scanValue s = .ok s' → s'.explicitKeyLine.isSome = true →
    (s'.explicitKeyLine = s.explicitKeyLine ∧ s'.explicitKeyCol = s.explicitKeyCol ∧
      s.explicitKeyLine.isSome = true) ∨
    ∃ cols pks, s'.explicitKeyLine = (PendingKeys.close cols pks s.explicitKeyCol).2.1 ∧
      s'.explicitKeyCol = (PendingKeys.close cols pks s.explicitKeyCol).2.2 :=
  fun h1 h2 =>
    L4YAML.Proofs.ExplicitKeyCoupling.scanValue_ekl_some_source h1 h2

example : ∀ {s s' : ScannerState}, scanKey s = .ok s' →
    s'.explicitKeyLine = some s.line ∧ s'.explicitKeyCol = (s.col : Int) :=
  fun h => L4YAML.Proofs.ExplicitKeyCoupling.scanKey_ok_explicitKey h

-- The two transport wrappers a producer reads at its own step:
example : ∀ (s s1 : ScannerState) (c : Char),
    scanNextToken_preprocess s = .ok (some (s1, c)) →
    (s1.explicitKeyLine = s.explicitKeyLine ∧ s1.explicitKeyCol = s.explicitKeyCol) ∨
    (s.explicitKeyLine ≠ none ∧
      ∃ (t : ScannerState) (c' : Char), t.peek? = some c' ∧ s1 = (t.closeStaleAt c').readPendingKey) :=
  L4YAML.Proofs.ExplicitKeyCoupling.preprocess_explicitKey_cases

example : ∀ (s s1 : ScannerState) (c : Char),
    scanNextToken_preprocess s = .ok (some (s1, c)) →
    s.explicitKeyLine = none → s1.explicitKeyLine = none :=
  L4YAML.Proofs.ExplicitKeyCoupling.preprocess_explicitKeyLine_none

example : ∀ (s : ScannerState) (c : Char) (s' : ScannerState),
    scanNextToken_dispatchContent s c = .ok s' →
    s'.explicitKeyLine = s.explicitKeyLine :=
  L4YAML.Proofs.ExplicitKeyCoupling.dispatchContent_preserves_explicitKeyLine

example : ∀ (s : ScannerState) (c : Char) (s' : ScannerState),
    scanNextToken_dispatchContent s c = .ok s' →
    s'.explicitKeyCol = s.explicitKeyCol :=
  L4YAML.Proofs.ExplicitKeyCoupling.dispatchContent_preserves_explicitKeyCol

/-! ## §2  The register discipline at every reachable boundary -/

private def registerOk (s : ScannerState) : Bool :=
  (!s.explicitKeyLine.isSome || decide (s.explicitKeyCol ≥ 0)) &&
  s.explicitKeyStack.all (fun p => !p.1.isSome || decide (p.2 ≥ 0))

private def registerOkFrom (s : ScannerState) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    match scanNextToken s with
    | .error _ => true
    | .ok none => true
    | .ok (some s') => registerOk s' && registerOkFrom s' fuel

private def registerDiscipline (input : String) : Bool :=
  registerOk (ScannerState.mk' input) &&
  registerOkFrom (ScannerState.mk' input) (input.length * 2 + 8)

#guard registerDiscipline "? [a]\n: v\n"
#guard registerDiscipline "? [a]\n: b: c\n"
#guard registerDiscipline "? {x: y}\n: v\n"
#guard registerDiscipline "? [a]\nz: v\n"
#guard registerDiscipline "? a\n: b: c\n"
#guard registerDiscipline "? earth: blue\n: moon: white\n"
#guard registerDiscipline "? [{a: b},\n   {c: d}]: v\n"
#guard registerDiscipline "? a: b\n: c\n"
#guard registerDiscipline "k:\n  ? a\n: v\n"
#guard registerDiscipline "[? a, b: c]\n"
#guard registerDiscipline "?\n: [a]\nx: y\n"
#guard registerDiscipline "%YAML 1.2\n--- ? a\n"

/-! ## §3  The register traces the ladder describes

`stateAfter input n` runs the scanner `n` steps; the pins read the pair
(`explicitKeyLine`, `explicitKeyCol`, `implicitValueLine`) at the boundaries
the item measured (Scratch/Probe124).  These are the transitions the ladder's
lemma-by-lemma story composes into: set → carry → park → restore → consume. -/

private def stateAfter (input : String) : Nat → Option ScannerState
  | 0 => some (ScannerState.mk' input)
  | n + 1 =>
    match stateAfter input n with
    | none => none
    | some s =>
      match scanNextToken s with
      | .ok (some s') => some s'
      | _ => none

private def regs (input : String) (n : Nat) : Option (Option Nat × Int × Option Nat) :=
  (stateAfter input n).map fun s => (s.explicitKeyLine, s.explicitKeyCol, s.implicitValueLine)

-- `? [a]⏎: v` — the `?` SETS (0,0); the `[` PARKS (none,-1); the `]` RESTORES
-- (0,0) across the collection; the landing CARRIES it; the landed `:` AT the
-- column CONSUMES it with NO stamp.
#guard regs "? [a]\n: v\n" 1 == some (some 0, 0, none)
#guard regs "? [a]\n: v\n" 2 == some (none, -1, none)
#guard regs "? [a]\n: v\n" 4 == some (some 0, 0, none)
#guard regs "? [a]\n: v\n" 5 == some (none, -1, none)
-- `? a⏎: b: c` — a plain content scan CARRIES the pair; the keyed `:` in the
-- explicit value slot STAMPS after the explicit `:` consumed the frame.
#guard regs "? a\n: b: c\n" 2 == some (some 0, 0, none)
#guard regs "? a\n: b: c\n" 3 == some (none, -1, none)
#guard regs "? a\n: b: c\n" 5 == some (none, -1, some 1)
-- `? [a]⏎z: v` — the sibling `z` at the frame's own column ENDS the restored
-- pair in preprocessing (item 333: the `?` entry is over, `{[a]: null, z: v}`);
-- the keyed `:` then STAMPS on a dead register.
#guard regs "? [a]\nz: v\n" 5 == some (none, -1, none)
#guard regs "? [a]\nz: v\n" 6 == some (none, -1, some 1)
-- `? earth: blue⏎: moon: white` — the keyed `:` DEEPER than the frame's
-- column stamps and lets the pair SURVIVE (spec 8.19).
#guard regs "? earth: blue\n: moon: white\n" 3 == some (some 0, 0, some 0)
-- `[? a, b: c]` — the flow `?` sets the pair inside the collection and the
-- `,` ENDS the entry (the line clears; the column register is left behind).
#guard regs "[? a, b: c]\n" 2 == some (some 0, 1, none)
#guard regs "[? a, b: c]\n" 4 == some (none, 1, none)

/-! ## §4  The families' verdicts, unchanged on both pipelines -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refused (input : String) : Bool :=
  (match Events.streamToEvents input with | .ok _ => false | .error _ => true) &&
  (match Events.streamToEventsIx input with | .ok _ => false | .error _ => true)

#guard emits "? [a]\n: b: c\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :a", "-SEQ",
   "+MAP", "=VAL :b", "=VAL :c", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "? [a]\nz: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :a", "-SEQ", "=VAL :",
   "=VAL :z", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "? {x: y}\n: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :x", "=VAL :y", "-MAP",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "?\n: [a]\nx: y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "+SEQ []", "=VAL :a", "-SEQ",
   "=VAL :x", "=VAL :y", "-MAP", "-DOC", "-STR"]
-- A keyless `:` DEEPER than a live `?` never parks (§8.2.2 [197]'s
-- `s-indent(n)` is exact), and a second value indicator on a stamped line
-- has no derivation — the two refusals the discriminators lean on.
#guard refused "? a\n  : v\n"
#guard refused ": b: c\n"

end L4YAML.Tests.Guards.ExplicitKeyCouplingLadder

end Blanket
