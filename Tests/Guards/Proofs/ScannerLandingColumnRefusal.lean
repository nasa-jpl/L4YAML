module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # §9.2's landing refusal reads the landing's COLUMN (DOCS item 145)

`scanNextToken_checkBareDocument` (item 132) asked four things of a landing: not
in flow, the break flag up, a completed node behind the cursor, and **the indent
stack at the sentinel alone**.  Items 139 and 142–144 spent that refusal at four
route faces, and each of them recorded the same residue on the way past: with a
level still open the scanner was clean and only `TokenParser` refused — item
143's `k:⏎␣␣"a"⏎␣␣[1, 2]`, item 144's `k:⏎␣␣"x"⏎␣␣b: 2`.

The residue was the fourth conjunct reading the wrong thing.  What makes a
landing a second bare document is not that no collection is open; it is that
**the landing stands at no OPEN LEVEL** — so the completed node already fills the
slot its predecessor offered, and the collection this landing would roll in has
nowhere to go.  The stack holding the sentinel alone is that condition's special
case, since every landing column is `≥ 0` and the sentinel sits at `-1`.

This file is the widening's measurement.  §1 types it at the check.  §2 is the
family it newly refuses, three of them real `yaml-test-suite` error cases.  §3 is
the half it still stands aside on.  §4 reads both stack conjuncts at every
landing of three inputs.  §5 is the proof side — the transport the refutation
actually rests on, and the narrowing at the four guarded routes.  §6 is what
remains.

Both pipelines carry the widening (`scanNextTokenIx_checkBareDocument` is the
indexed twin), and every verdict below is `scan`'s, not a model's. -/

namespace L4YAML.Tests.Guards.ScannerLandingColumnRefusal

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  The widening, at the check's own type

The check stands aside on four readings and fires on their conjunction.  The
stack one is the landing's COLUMN: an open block collection does not by itself
excuse the landing, its own level does. -/

/-- Inside a flow collection there is no document boundary to police. -/
example (s : ScannerState) (h : s.inFlow = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.not_true, Bool.false_and,
             Bool.false_eq_true, ↓reduceIte]

/-- **The conjunct item 145 replaced.**  A landing that rests ON an open level is
    that collection's own next key, and what is refused there is a DANGLING run
    one token later — `danglingNodePos?`'s question, not this one. -/
example (s : ScannerState)
    (h : (s.indents.any fun e => e.column == (s.col : Int)) = true) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.not_true, Bool.and_false,
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- On the completed node's own line the flag is down and the node is still
    readable as an implicit key (`"x": 1`). -/
example (s : ScannerState) (h : s.simpleKeyAllowed = false) :
    scanNextToken_checkBareDocument s = .ok () := by
  simp only [scanNextToken_checkBareDocument, h, Bool.and_false, Bool.false_and,
             Bool.false_eq_true, ↓reduceIte]

/-- …and with nothing completed behind the cursor there is no first document to
    have ended. -/
example (s : ScannerState)
    (h : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    scanNextToken_checkBareDocument s = .ok () := by
  unfold scanNextToken_checkBareDocument
  cases hx : lastRealTokenVal? s.tokens with
  | none => simp
  | some t => simp [h t hx]

/-- The positive shape, in full, with the error at the cursor. -/
example (s : ScannerState) (t : YamlToken)
    (h_flow : s.inFlow = false) (h_ska : s.simpleKeyAllowed = true)
    (h_open : (s.indents.any fun e => e.column == (s.col : Int)) = false)
    (h_last : lastRealTokenVal? s.tokens = some t)
    (h_cmp : t.completesFlowValue = true) :
    scanNextToken_checkBareDocument s
      = .error (.invalidBareDocument s.line s.col) := by
  simp only [scanNextToken_checkBareDocument, h_flow, h_ska, h_open, h_last, h_cmp,
             Bool.not_false, Bool.and_self, ↓reduceIte]

/-- The old reading is the new one's special case wherever the stack is the one
    the scanner builds: `unwindIndents` never pops the sentinel, so a one-entry
    stack is `{-1}` and no landing column reaches it.  Stated on the array that
    `ScannerState.mk'` seeds and every writer preserves. -/
example (s : ScannerState)
    (h : s.indents = #[{ column := -1, isSequence := false }]) :
    (s.indents.any fun e => e.column == (s.col : Int)) = false := by
  rw [h]; simp

/-! ## §2  The family the widening newly refuses

Every row here was `parse-bare` before item 145 and is `scan-bare` now, at the
SAME line and column: the refusal moves one layer up, it does not appear.  The
first three are real `yaml-test-suite` cases, all three of them `error` tests. -/

private def fireAt (s : ScannerState) (n : Nat) : Nat → String
  | 0 => "fuel"
  | fuel + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => s!"preprocess-error@{n}"
    | .ok none => "clean"
    | .ok (some (s1, _)) =>
      match scanNextToken_checkDanglingNode s s1 with
      | .error _ => s!"dangling@{n}"
      | .ok _ =>
        match scanNextToken_checkBareDocument s1 with
        | .error _ => s!"bare@{n} {s1.line},{s1.col}"
        | .ok _ =>
          match scanNextToken s with
          | .ok (some s') => fireAt s' (n + 1) fuel
          | .ok none => "no-step"
          | .error _ => s!"step-error@{n}"

private def fires (input : String) : String := fireAt (ScannerState.mk' input) 0 60

private def verdict (input : String) : String :=
  match scan input with
  | .error (.invalidBareDocument l c) => s!"scan-bare {l},{c}"
  | .error (.trailingContent l c) => s!"scan-trailing {l},{c}"
  | .error e => s!"scan {toString (repr e)}"
  | .ok _ =>
    match Events.streamToEvents input with
    | .error (.invalidBareDocument l c) => s!"parse-bare {l},{c}"
    | .error e => s!"parse {toString (repr e)}"
    | .ok _ => "OK"

-- **8XDJ** — a comment stops the plain walk, and `word2` lands at column 2 with
-- only `-1` and `0` open.  **BF9H** — the same shape with the completed node a
-- multi-line plain (`a b`) and the landing at column 7.  **U44R** — "bad
-- indentation": a sibling key one space right of its mapping's own level.
#guard ["key: word1\n#  xxx\n  word2\n",
        "---\nplain: a\n       b # end of scalar\n       c\n",
        "map:\n  key1: \"quoted1\"\n   key2: \"bad indentation\"\n"].map fires
  == ["bare@3 2,2", "bare@4 3,7", "bare@5 2,3"]
#guard ["key: word1\n#  xxx\n  word2\n",
        "---\nplain: a\n       b # end of scalar\n       c\n",
        "map:\n  key1: \"quoted1\"\n   key2: \"bad indentation\"\n"].map verdict
  == ["scan-bare 2,2", "scan-bare 3,7", "scan-bare 2,3"]

-- The three lanes the campaign carried the residue through — item 142's block
-- landing, item 143's flow open, item 144's content landing — at one column
-- each.  All three read `("clean", "parse-bare 2,2")` under the size conjunct.
#guard ["k:\n  \"x\"\n  b: 2\n", "k:\n  \"a\"\n  [1, 2]\n", "k:\n  a\n  : v\n"].map fires
  == ["bare@3 2,2", "bare@3 2,2", "bare@3 2,2"]
#guard ["k:\n  \"x\"\n  b: 2\n", "k:\n  \"a\"\n  [1, 2]\n", "k:\n  a\n  : v\n"].map verdict
  == ["scan-bare 2,2", "scan-bare 2,2", "scan-bare 2,2"]

-- The sentinel family is unmoved — it is the widening's special case.
#guard ["\"x\"\nb: 2\n", "a\n# c\nb: 2\n", "[1, 2]\nb: 2\n"].map fires
  == ["bare@1 1,0", "bare@1 2,0", "bare@5 1,0"]

/-! ## §3  The half it still stands aside on

A landing that RESTS on an open level is a sibling, and those are the hottest
path in real YAML — item 141's census counted 2273 of 2275 dangling parks
surviving exactly there.  Nothing below moved. -/

#guard ["a: 1\nb: 2\n", "k:\n  a: 1\n  b: 2\n", "- a\n- b\n", "k:\n  - a\n  - b\n",
        "? \"a\"\n: v\n", "k: [1, 2]\nb: 2\n", "k: |\n  x\nb: 2\n",
        "k:\n  a: 1\nb: 2\n"].map fires
  == ["clean", "clean", "clean", "clean", "clean", "clean", "clean", "clean"]
#guard ["a: 1\nb: 2\n", "k:\n  a: 1\n  b: 2\n", "- a\n- b\n", "k:\n  - a\n  - b\n",
        "? \"a\"\n: v\n", "k: [1, 2]\nb: 2\n", "k: |\n  x\nb: 2\n",
        "k:\n  a: 1\nb: 2\n"].map verdict
  == ["OK", "OK", "OK", "OK", "OK", "OK", "OK", "OK"]

-- The flag keeps the same-line reading out: `"x"` completes and stands at no
-- open level, but it is still readable as an implicit KEY.
#guard (fires "\"x\": 1\n", verdict "\"x\": 1\n") == ("clean", "OK")

-- A SEQUENCE level counts as an open level, which is why the widening does not
-- reach a mapping key at one: `k:⏎␣␣- a⏎␣␣b: 2` is refused, but by the
-- structural dispatch's own check, one token later and under another name.
#guard (fires "k:\n  - a\n  b: 2\n", verdict "k:\n  - a\n  b: 2\n")
  == ("step-error@5", "scan-trailing 2,2")

-- And a landing that DEDENTS past a level is refused before this check runs —
-- preprocessing's own reading, which is why the two stack conjuncts below are
-- separate premises rather than one.
#guard (fires "k:\n    a: 1\n  b: 2\n", verdict "k:\n    a: 1\n  b: 2\n")
  == ("preprocess-error@5", "scan-trailing 2,2")

/-! ## §4  Both stack conjuncts, read at every landing

`readings` prints what the check compares: the landing, the stack, whether the
landing rests on one of its levels, whether preprocessing POPPED to get here,
the flag, whether the tail completes a value, and the verdict. -/

private def stackOf (s : ScannerState) : String :=
  String.intercalate "," (s.indents.toList.map fun e =>
    s!"{e.column}{if e.isSequence then "s" else "m"}")

private def readAt (s : ScannerState) : Nat → List String
  | 0 => ["fuel"]
  | fuel + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => ["preprocess-error"]
    | .ok none => []
    | .ok (some (s1, _)) =>
      let opened := s1.indents.any fun e => e.column == (s1.col : Int)
      let popped := s1.indents != s.indents
      let cmpl := match lastRealTokenVal? s1.tokens with
        | none => false | some t => t.completesFlowValue
      let bare := match scanNextToken_checkBareDocument s1 with
        | .error _ => "BARE" | .ok _ => "-"
      let row := s!"{s1.line},{s1.col}|[{stackOf s1}]|open={opened}|pop={popped}|\
ska={s1.simpleKeyAllowed}|done={cmpl}|{bare}"
      match scanNextToken s with
      | .ok (some s') => row :: readAt s' fuel
      | _ => [row]

private def readings (input : String) : List String :=
  readAt (ScannerState.mk' input) 60

-- U44R.  The last row is the refusal: level 2 is open and the key stands at 3.
#guard readings "map:\n  key1: \"quoted1\"\n   key2: \"bad indentation\"\n"
  == ["0,0|[-1m]|open=false|pop=false|ska=true|done=false|-",
      "0,3|[-1m]|open=false|pop=false|ska=false|done=true|-",
      "1,2|[-1m,0m]|open=false|pop=false|ska=true|done=false|-",
      "1,6|[-1m,0m]|open=false|pop=false|ska=false|done=true|-",
      "1,8|[-1m,0m,2m]|open=false|pop=false|ska=true|done=false|-",
      "2,3|[-1m,0m,2m]|open=false|pop=false|ska=true|done=true|BARE"]

-- The legal dedent, which stands aside on BOTH stack readings at once: the
-- landing popped, so the tail is the `blockEnd` the unwind emitted and completes
-- nothing — and column 0 is open anyway.
#guard readings "k:\n  a: 1\nb: 2\n"
  == ["0,0|[-1m]|open=false|pop=false|ska=true|done=false|-",
      "0,1|[-1m]|open=false|pop=false|ska=false|done=true|-",
      "1,2|[-1m,0m]|open=false|pop=false|ska=true|done=false|-",
      "1,3|[-1m,0m]|open=false|pop=false|ska=false|done=true|-",
      "1,5|[-1m,0m,2m]|open=false|pop=false|ska=true|done=false|-",
      "2,0|[-1m,0m]|open=true|pop=true|ska=true|done=false|-",
      "2,1|[-1m,0m]|open=false|pop=false|ska=false|done=true|-",
      "2,3|[-1m,0m]|open=false|pop=false|ska=true|done=false|-"]

-- The sequence level, from the same instrument: `open=true` on a `2s` entry.
#guard readings "k:\n  - a\n  b: 2\n"
  == ["0,0|[-1m]|open=false|pop=false|ska=true|done=false|-",
      "0,1|[-1m]|open=false|pop=false|ska=false|done=true|-",
      "1,2|[-1m,0m]|open=false|pop=false|ska=true|done=false|-",
      "1,4|[-1m,0m,2s]|open=false|pop=false|ska=true|done=false|-",
      "2,2|[-1m,0m,2s]|open=true|pop=false|ska=true|done=true|-",
      "2,3|[-1m,0m,2s]|open=false|pop=false|ska=false|done=true|-"]

/-! ## §5  The proof side

The refutation reads the check on `s_prep` but holds the completed tail on the
PARK, `sc`, so it needs the park's token array to survive preprocessing.  Item
139 asked for `sc.indents.size ≤ 1`, which is one way to know the unwind did
nothing.  The premise it actually rests on is that the unwind did nothing, and
the unwind announces that itself: one iteration pops, so a loop that ran left
the stack shorter. -/

/-- The loop either is the identity or SHRINKS the stack. -/
example (s : ScannerState) (col : Int) (fuel : Nat) :
    unwindIndentsLoop s col fuel = s ∨
      (unwindIndentsLoop s col fuel).indents.size < s.indents.size :=
  unwindIndentsLoop_eq_or_size_lt s col fuel

/-- …so an unwind that left the stack alone left the TOKENS alone too. -/
example {s : ScannerState} {col : Int}
    (h : (unwindIndents s col).indents = s.indents) : unwindIndents s col = s :=
  unwindIndents_of_indents_eq h

/-- …and the park's §9.2 token reading survives such a landing. -/
example {sc s_prep : ScannerState} {c : Char}
    (h_nopop : s_prep.indents = sc.indents)
    (h_real : L4YAML.Proofs.FlowAdjacency.LastTokenReal sc.tokens)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    lastRealTokenVal? s_prep.tokens = lastRealTokenVal? sc.tokens :=
  preprocess_lastRealTokenVal_of_indents_eq h_nopop h_real h

/-- The contradiction, at its type: the landing's COLUMN is the stack reading,
    and the base is what the accumulation carries to pay for it (item 146). -/
example {sc s_prep : ScannerState} {c : Char}
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_noflow : s_prep.inFlow = false)
    (h_ska : s_prep.simpleKeyAllowed = true)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_open : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false)
    (h_tail : CompletedTail sc) : False :=
  bareDocument_refutes_landing h_bare h_pre h_noflow h_ska h_base h_open h_tail

/-- …and through the bundle the four route faces carry. -/
example {sc s_prep : ScannerState} {c : Char}
    (h : BareLandingFacts sc s_prep c)
    (h_op : (s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = false) :
    False :=
  h.refutes h_op

/-- The three bundle-carrying routes are unchanged at their types — what moved
    is the case split inside them, from the stack's SIZE to the landing's
    column.  The narrowing is still a narrowing: a caller with nothing to say
    passes `Or.inr trivial` and gets the unguarded route. -/
example {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute_or_refused (sc := ScannerState.mk' "") (s_prep := ScannerState.mk' "")
    (c := 'x') (Or.inr trivial) hcol0 h_stream h_ind

/-! ## §6  The dedent exemption, paid

`preprocess_landing_at_level` (item 129) says a landing that popped rests at an
entry the incoming stack already held, so a landing at NO OPEN LEVEL popped
nothing — `pop` and `¬ open` cannot both hold.  That reading asks for
`IndentStackBase.SentinelBase sc`, `ScannerState.WellFormed`'s sixth conjunct,
and item 146 threads it: `BareLandingFacts` carries it, the accumulation carries
it from `mk'` down, and the refutation takes the landing's column alone.
`Tests/Guards/Proofs/AccumIndentBaseCarried.lean` pins that thread.

What the widening buys is the residue every landing item recorded and none could
close: the INDENTED landing is the scanner's refusal, in both pipelines, so the
accumulation never sees it.  Item 141's park face is the answer for what a park
can assert about a run, which is a different question; this input family is
settled at the scanner. -/

end L4YAML.Tests.Guards.ScannerLandingColumnRefusal

end Blanket
