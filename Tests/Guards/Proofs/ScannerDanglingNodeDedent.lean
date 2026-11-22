module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch
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

/-! # The dangling run a dedent hid (DOCS item 140)

Item 133 landed §9.2 `[211]`'s two refusals for a node that belongs to nothing:
`scanLoop_checkDanglingNode` for the run the stream itself ends, and
`scanNextToken_checkDanglingNode` for the run a line break ends.  The two were
not the same check read at two places — they read DIFFERENT token arrays, and
the difference was the landing's unwind.

`scanLoop` runs its check and only then calls `unwindIndents s (-1)`, so it reads
the array the run is still in.  `scanNextToken` ran its check on the state
`scanNextToken_preprocess` RETURNS, and preprocessing unwinds: it emits a
`blockEnd` for every level the landing dedents past and pops them.  A run whose
own level the landing dedents past is therefore no longer trailing (the
`blockEnd` is behind it) and no longer sits at any open column (the level is
gone) — so the check read `none` where the run was plainly there.

`k:⏎␣␣a: 1⏎␣␣b⏎c: 2` is that shape, and it scanned CLEAN.  Only
`TokenParser.parseStreamLoop`'s `validNextToken` refused it, at the same
position the scanner would have named.  Item 140 gives the check its two
states — the break off the landing, the RUN off the state the landing arrived
with — which makes the mid-stream check the end-of-input check's exact twin and
the scanner's acceptance the parser's.

§1 measures the displacement at the real landing of the real scanner.  §2 is the
family the narrowing adds, with the two pipelines and the parser's own position
beside it.  §3 is the check at its type and the three ways it stands aside.  §4
shows the narrowing is a narrowing.  §5 is what it buys. -/

namespace L4YAML.Tests.Guards.ScannerDanglingNodeDedent

open L4YAML L4YAML.Scanner

/-! ## §1  The displacement, at the landing where it happens

`readingAt input n` runs the real scanner `n` landings in and reports
`danglingNodePos?` at BOTH of the landing's states: `run=` off the state the
landing arrived with, `land=` off the state preprocessing returns.  The two
agree at every landing that does not dedent, and that is the point — the check
was not wrong, it was reading one writer too late. -/

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

private def posStr : Option YamlPos → String
  | some p => s!"{p.line},{p.col}"
  | none => "none"

private def readingAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    let land := match scanNextToken_preprocess s with
      | .ok (some (s1, _)) => s!"{posStr (danglingNodePos? s1)} ind={s1.indents.size}"
      | .ok none => "eof"
      | .error _ => "err"
    s!"run={posStr (danglingNodePos? s)} ind={s.indents.size} | land={land}"

-- THE ROOT LANDING, where nothing is popped: the two readings are the same one.
-- `b` stands at column 0, the mapping's own level is at column 0, and the
-- landing for `c: 2` dedents past nothing.
#guard readingAt "a: 1\nb\nc: 2\n" 4 == "run=1,0 ind=2 | land=1,0 ind=2"

-- THE INDENTED LANDING, where the dedent pops the run's own level: the run is
-- at line 2 column 2 in the array the landing ARRIVED with, and gone from the
-- array preprocessing returns — one `blockEnd` emitted, `ind` 3 → 2.
#guard readingAt "k:\n  a: 1\n  b\nc: 2\n" 6 == "run=2,2 ind=3 | land=none ind=2"

-- …and every landing before it reads `none` at both, so the row above is the
-- only place the two disagree in this input.
#guard (List.range 6).all
  (fun n => readingAt "k:\n  a: 1\n  b\nc: 2\n" n
    == s!"run=none ind={(n / 2) + 1} | land=none ind={(n / 2) + 1}")

/-! ## §2  The family the narrowing adds

Every input here scanned CLEAN before item 140 and was refused by the parser
alone.  Both scanners refuse it now, both pipelines still refuse it, and the
position is the one the parser had already reported — which is what says the
two are one refusal read at two depths rather than two different rules. -/

private def scanErr (input : String) : Option String :=
  match Scanner.scan input with | .error e => some (toString e) | .ok _ => none

private def scanErrIx (input : String) : Option String :=
  match Indexed.ScannerStateIx.scanIx input with
  | .error e => some (toString e) | .ok _ => none

private def pipeErr (input : String) : Option String :=
  match Events.streamToEvents input with | .error e => some (toString e) | .ok _ => none

private def pipeErrIx (input : String) : Option String :=
  match Events.streamToEventsIx input with | .error e => some (toString e) | .ok _ => none

-- All four readings refuse, with one and the same message.
private def refusedAlike (input : String) : Bool :=
  match scanErr input with
  | none => false
  | some e => (scanErrIx input, pipeErr input, pipeErrIx input) == (some e, some e, some e)

#guard refusedAlike "k:\n  a: 1\n  b\nc: 2\n"      -- mapping level, dedent to 0
#guard refusedAlike "k:\n  - a\n  b\nc: 2\n"       -- sequence level
#guard refusedAlike "k:\n  a: 1\n  b\n...\n"       -- the marker dispatch, still after
#guard refusedAlike "k:\n  a: 1\n  b\n---\nz\n"
#guard refusedAlike "j:\n k:\n   a: 1\n   b\n m: 2\n"  -- two levels down, one popped
#guard refusedAlike "k:\n  a: &q 1\n  *q\nc: 2\n"  -- alias run
#guard refusedAlike "k:\n  a: 1\n  &p b\nc: 2\n"   -- the `[96]` run carries the column
#guard refusedAlike "k:\n  a: 1\n  \"q\"\nc: 2\n"  -- quoted
#guard refusedAlike "k:\n  a: [1, 2]\n  b\nc: 2\n"  -- after a flow close

-- And the message names the RUN, not the landing that exposed it: `b` begins at
-- line 2 column 2, one line before the `c` whose landing ran the check.
#guard scanErr "k:\n  a: 1\n  b\nc: 2\n" ==
  some "bare document content at line 2, column 2 — expected '---' or '...' before new document (§9.2)"

-- The run's position is what the PARSER reported before the scanner did — the
-- narrowing moved the refusal earlier without moving where it points.
#guard scanErr "j:\n k:\n   a: 1\n   b\n m: 2\n" ==
  some "bare document content at line 3, column 3 — expected '---' or '...' before new document (§9.2)"

-- A run that dedents to a landing which is ITSELF a dangler used to report the
-- later one; it now reports the first, which is the one that has no reading.
#guard scanErr "k:\n  a: 1\n  b\nc\n" ==
  some "bare document content at line 2, column 2 — expected '---' or '...' before new document (§9.2)"

/-! ## §3  The check, at its two states

The break is a fact about the LANDING; the run is a fact about the array.  Each
of the three exemptions belongs to exactly one of them. -/

/-- The break, off the landing. -/
example (s_run s_land : ScannerState) (h : s_land.simpleKeyAllowed = false) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  simp only [scanNextToken_checkDanglingNode, h, Bool.false_eq_true, ↓reduceIte]

/-- The flow exemption, off the run's array — and `inFlow` is preserved by
    preprocessing, so naming the state changes nothing here. -/
example (s_run s_land : ScannerState) (h : s_run.inFlow = true) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  simp only [scanNextToken_checkDanglingNode, danglingNodePos?, h, ↓reduceIte]
  split <;> rfl

/-- The sentinel exemption, off the run's array: a token's column is a `Nat`, so
    it never matches a negative entry.  At the sentinel alone NOTHING is popped
    either (`unwindIndentsLoop` wants `1 < indents.size`), so this is the half of
    the domain where item 140 changes nothing at all. -/
example (s_run s_land : ScannerState)
    (h : s_run.indents = #[{ column := -1, isSequence := false }])
    -- Item 180: the crossed-block clause reads no column; its `none` rides.
    (hx : crossedPropsExcessIdx? s_run.tokens = none) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  have hneg : ∀ e ∈ s_run.indents, e.column < 0 := by
    intro e he
    rw [h] at he
    have he' : e = { column := -1, isSequence := false } := by simpa using he
    subst he'
    decide
  have hany : ∀ n : Nat, s_run.indents.any (fun e => e.column == (n : Int)) = false := by
    intro n
    rw [Array.any_eq_false]
    intro i hi
    have := hneg s_run.indents[i] (Array.getElem_mem hi)
    simp only [beq_iff_eq]
    omega
  -- Item 180: the crossed-block clause reads no column, so its own `none`
  -- (the `hx` this example now takes) closes the fourth reading.
  have hxp : crossedPropsExcessPos? s_run.tokens = none := by
    unfold crossedPropsExcessPos?; rw [hx]
  -- Item 182: the break-crossing clause keeps its crossing only AT a level's
  -- own column, so the sentinel stack closes the fifth reading on its own.
  have hlc : runLineCrossDanglingPos? s_run.tokens s_run.indents = none := by
    unfold runLineCrossDanglingPos?
    cases hq : runLineCrossPos? s_run.tokens with
    | none => rfl
    | some q => simp [hany q.col]
  have hnone : danglingNodePos? s_run = none := by
    unfold danglingNodePos?
    simp only [hany, Bool.false_eq_true, ↓reduceIte, ite_self, hxp, hlc]
    split
    · rfl
    · split <;> rfl
  simp only [scanNextToken_checkDanglingNode, hnone]
  split <;> rfl

/-- The EOF check is unchanged, and it was already pre-unwind: `scanLoop` runs it
    before its own `unwindIndents s (-1)`.  That is the twin the mid-stream check
    now is. -/
example (s : ScannerState) (p : YamlPos) (h : danglingNodePos? s = some p) :
    scanLoop_checkDanglingNode s = .error (.invalidBareDocument p.line p.col) := by
  simp only [scanLoop_checkDanglingNode, h]

/-! ## §4  The narrowing is a narrowing

`unwindIndents` only APPENDS to the array and only POPS the stack, so the
post-unwind reading is `none` wherever the pre-unwind one is — the new check
refuses a superset.  What matters is that the superset is not bigger than the
parser's, and these are the shapes a dedent walks past legally. -/

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

-- A dedent past a level whose last token OFFERS a slot: the value is awaited,
-- not dangling, and the three offering predecessors are `:`, `?` and `-`.
#guard accepts "k:\n  a: 1\nc: 2\n"
#guard accepts "k:\n  - a\nc: 2\n"
#guard accepts "k:\n  a:\n    b: 1\nc: 2\n"
#guard accepts "k:\n  ? a\n  : b\nc: 2\n"
#guard accepts "k:\n  a: |\n    x\nc: 2\n"
#guard accepts "k:\n  a: &p 1\nc: 2\n"
#guard accepts "k:\n  a: {x: 1}\nc: 2\n"

-- A dedent whose run is the value ITSELF, one level down — the `:` is still the
-- predecessor, whatever the run's column.
#guard accepts "k:\n  a:\n    b\nc: 2\n"
#guard accepts "k:\n  -\n    b\nc: 2\n"

-- Multi-line plain scalars absorb their own continuations, so a dedent never
-- finds a second run behind them.
#guard accepts "k:\n  a: 1\n    2\nc: 3\n"
#guard accepts "k:\n  a\n  b\nc: 2\n"

-- Two dedents in a row, and a dedent straight to the stream's end.
#guard accepts "a:\n  b:\n    c: 1\nd: 2\n"
#guard accepts "a:\n  b:\n    c: 1\n"
#guard accepts "- a\n- - b\n- c\n"

-- Flow interiors are exempt outright, at any depth, dedent or not.
#guard accepts "k: [1,\n 2]\nc: 3\n"
#guard accepts "k: {a: 1,\n b: 2}\nc: 3\n"

-- And item 133's own two arms still fire where they did, which is what says the
-- narrowing did not move the refusal it already had.
#guard scanErr "a: 1\nb\n" ==
  some "bare document content at line 1, column 0 — expected '---' or '...' before new document (§9.2)"
#guard scanErr "a: 1\nb\nc: 2\n" ==
  some "bare document content at line 1, column 0 — expected '---' or '...' before new document (§9.2)"

/-! ## §5  What it buys

The accumulation is a SCANNER invariant: every step the scanner accepts has to
come out of `StreamAccum` with a production in hand.  The indented dangling run
was a step the scanner accepted, so `[211]`'s bare-document fallback
(`bareNodeRoute`, item 139) was the only reading available for it — and no park
face could have refuted it, because there was no refusal to thread.  Row 19's
1c therefore could not be closed at any price while this landing scanned clean;
the parser's verdict is not available to an invariant about the scanner.

With the check at its two states the whole dangling family is refused by the
scanner, one landing after the run — `dangling@6` for the input in §1 — which is
exactly where the park that owes the stream is consumed.  What that leaves is
the item item 139 named: a `danglingNodePos?` face on `pendingContent`, spent at
the landing where `h_closable` is, with this refusal as its contradiction. -/

end L4YAML.Tests.Guards.ScannerDanglingNodeDedent

end Blanket
