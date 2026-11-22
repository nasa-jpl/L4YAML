module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The key from an EARLIER line is not this `:`'s key (DOCS item 104)

`colon_fires_implicit_key` asks two decidable questions of the park before it
does anything: is a simple key live, and is it on the park's own line.  The
second had no answer — a live key on an earlier line rode the deferral — and
item 103 recorded the family that lands there as `flowKeyPack_of_close`'s
residue, reading it as the HEAD's `∨ True`.  That reading was wrong about which
punt the input reaches: `[1,⏎ 2]: 3` never gets as far as the pack, because the
pack's own guard is the question above and it is FALSE there.

The answer is §7.4's own check.  `[154] ns-s-implicit-yaml-key` is one line and
`scanValueValidate` says so, throwing `invalidImplicitKey` when the `:` would
resolve a key saved on a different line — so a stale key at the park is an
input the scanner REFUSES, and the branch is a refutation rather than a
deferral.  The transport is item 48's verbatim (`dispatch_refutes_sameLine`'s
shape): the no-break payload carries the key, the line and the cursor to the
dispatch state, and the dispatch's own success contradicts them.

What the refutation does not decide is the one shape §7.4 hands on to §8.2.2
`[197]`: a `?` frame open on the key's own line takes the key down before §7.4
reads it (`scanValueClearKey`), and the misindent check decides the `:`
instead — but only when the `:` stands at the mapping's own indent.  §3 below
measures that pair and finds it empty: the explicit key's continuation lines
must be indented past the `?`, so the `:` that follows them never lands at the
`?`'s column, and the runtime says so with the column pair in its own message. -/

namespace L4YAML.Tests.Guards.ScannerStaleKeyColon

open L4YAML

/-- Refused by BOTH pipelines, and by §7.4 specifically — the error names the
    line the `:` is on, which is what says the one-line key check is what fired
    rather than some other refusal. -/
private def staleKey (input : String) (line : Nat) : Bool :=
  ( (match Events.streamToEvents input with
     | .error (.invalidImplicitKey l) => some l | _ => none)
  , (match Events.streamToEventsIx input with
     | .error (.invalidImplicitKey l) => some l | _ => none) )
    == (some line, some line)

/-- Refused by §8.2.2 `[197]`'s misindent check, pinned with BOTH columns: the
    `:`'s own and the indent it was measured against.  The pair is the residue
    disjunct's second conjunct, and every input here has it FALSE. -/
private def misindented (input : String) (line col expected : Nat) : Bool :=
  ( (match Events.streamToEvents input with
     | .error (.misindentedExplicitValue l c e) => some (l, c, e) | _ => none)
  , (match Events.streamToEventsIx input with
     | .error (.misindentedExplicitValue l c e) => some (l, c, e) | _ => none) )
    == (some (line, col, (expected : Int)), some (line, col, (expected : Int)))

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def emitsOk (input : String) : Bool :=
  ( (Events.streamToEvents input).toOption.isSome
  , (Events.streamToEventsIx input).toOption.isSome ) == (true, true)

-- §1 The three ways a park ends up holding a key from an earlier line: a flow
-- collection closed across a break (the key is the one the `[` stacked), and
-- the two FOLDED scalars (the key is the one saved at their start).
#guard staleKey "[1,\n 2]: 3\n" 1
#guard staleKey "{a: b,\n c: d}: 3\n" 1
#guard staleKey "x\ny: v\n" 1
#guard staleKey "\"a\nb\": c\n" 1
#guard staleKey "'a\nb': c\n" 1
-- The `s-separate-in-line?` a key may carry before its own `:` changes
-- nothing — the refusal is about the key's line, not the run after it.
#guard staleKey "\"a\nb\" : c\n" 1
-- …and neither does how far the break is from the `:`, nor which frame the
-- collection was opened under.
#guard staleKey "[1,\n 2,\n 3]: 4\n" 2
#guard staleKey "k:\n  [1,\n   2]: 3\n" 2
#guard staleKey "- [1,\n  2]: 3\n" 1
#guard staleKey "- - [1,\n    2]: 3\n" 1
#guard staleKey "? a\n: [1,\n  2]: 3\n" 2

-- §2 The boundary, which must NOT move.  The same collections and scalars
-- keyed on the line they end on, and the same multi-line ones with no `:`
-- after them at all.
#guard emitsOk "[1, 2]: 3\n"
#guard emits "x\ny\n" ["+STR", "+DOC", "=VAL :x y", "-DOC", "-STR"]
#guard emits "\"a\nb\"\n" ["+STR", "+DOC", "=VAL \"a b", "-DOC", "-STR"]
#guard emits "k: [1,\n  2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- The EXPLICIT value indicator on its own line reads the multi-line collection
-- as `[197]`'s key — which is the shape the refutation must leave alone.
#guard emits "? [1,\n 2]\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "=VAL :v",
   "-MAP", "-DOC", "-STR"]

-- §3 The residue, measured: the `?` frame open on the stale key's own line is
-- where §7.4 goes silent, and `[197]`'s misindent check decides instead.  Its
-- condition is a column EQUALITY, and the two columns differ in every input we
-- can write — the explicit key's continuation must be indented past the `?`,
-- so the `:` after it is strictly right of the mapping indent.
#guard misindented "? [1,\n 2]: v\n" 1 3 0
#guard misindented "? \"a\n b\": v\n" 1 3 0
#guard misindented "? x\n y: v\n" 1 2 0
#guard misindented " ? [1,\n  ]: v\n" 1 3 1

-- §4 The refutation at its type — §7.4's check, `[197]`'s, the lift that joins
-- them across `scanValueClearKey`, and the transport to the park.
open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- An accepted `:` with a live saved key resolves a key on its OWN line. -/
example {s : ScannerState} (h : scanValueValidate s = .ok ())
    (h_noflow : s.inFlow = false) (h_poss : s.simpleKey.possible = true) :
    s.simpleKey.pos.line = s.line :=
  scanValueValidate_ok_keyLine h h_noflow h_poss

open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- With the key already down and the `?` frame open on an earlier line, an
    accepted `:` stands at the mapping's indent. -/
example {s : ScannerState} {ek : Nat} (h : scanValueValidate s = .ok ())
    (h_noflow : s.inFlow = false) (h_poss : s.simpleKey.possible = false)
    (h_ek : s.explicitKeyLine = some ek) (h_ne : s.line ≠ ek) :
    (s.col : Int) = s.currentIndent :=
  scanValueValidate_ok_explicit_col h h_noflow h_poss h_ek h_ne

open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- The lift: `scanValueClearKey`'s phantom-key arm dies on item 81's
    behind-the-cursor invariant, so the `?`-line arm is the only residue. -/
example {s s' : ScannerState} (h : scanValue s = .ok s')
    (h_noflow : s.inFlow = false) (h_poss : s.simpleKey.possible = true)
    (h_behind : s.simpleKey.pos.offset < s.offset) :
    s.simpleKey.pos.line = s.line ∨
      (s.explicitKeyLine = some s.simpleKey.pos.line ∧
        (s.col : Int) = s.currentIndent) :=
  scanValue_ok_keyLine h h_noflow h_poss h_behind

open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- …and the transport, in `dispatch_refutes_sameLine`'s own shape. -/
example {sc s_prep s' : ScannerState}
    (h_poss : sc.simpleKey.possible = true)
    (h_kline : ¬ (sc.simpleKey.pos.line = sc.line))
    (h_behind : sc.simpleKey.pos.offset < sc.offset)
    (h_inh : s_prep.simpleKey = sc.simpleKey)
    (h_line_eq : s_prep.line = sc.line)
    (h_off_ge : sc.offset ≤ s_prep.offset)
    (h_noflow : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).inFlow = false)
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) ':' = .ok (some s')) :
    s_prep.explicitKeyLine = some sc.simpleKey.pos.line ∧
      (s_prep.col : Int) = s_prep.currentIndent :=
  dispatch_refutes_staleKey h_poss h_kline h_behind h_inh h_line_eq h_off_ge
    h_noflow h_dispatch

end L4YAML.Tests.Guards.ScannerStaleKeyColon

end Blanket
