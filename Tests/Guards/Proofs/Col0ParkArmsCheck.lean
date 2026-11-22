module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The column-0 landing pays, off the park's own indent check (DOCS item 154)

Item 152 gave `pendingContent`'s two frames fields a cover and spent it at
`accum_content_pending`'s shared landing skeleton.  It could not spend it on
every landing: the skeleton splits on the park's column, and the COLUMN-0 arm
punted its payer.  Item 147's reading is why — a landing's floor comes off the
walk that carried the park down to column 0, and a park already AT a line start
crosses no such walk.  Item 152 recorded this as item 147's escape "at the
consumer instead of at a producer", and item 153 recorded it as one of two
remaining entries.

**The floor is not the walk's.**  It is preprocessing's UNWIND, and the unwind
runs outside a flow on exactly one condition: `needIndentCheck`.  A park that
reached column 0 got there by consuming a break, and every break arms the flag.
So the datum the arm needs is the PARK's, not the landing's — which is item 77's
own division of labor (`landing_or_park_save`: the landing pays for a park off a
line start, the park's flag pays for one at it), one field over.

`pendingContent` gains `h_nic0`, the block-scalar producers fund it, and both
column-0 landings spend it.

**The escape is measured, not assumed.**  A block-scalar header at end of input
consumes no break, and `"k: |"` really does stop with the flag DOWN (§3 makes
that a checked fact rather than a remark).  It also stops strictly inside its
line, which is why the field is stated as an implication FROM column 0: the one
shape that cannot pay is the one shape that cannot reach the premise.

§1 is the field.  §2 is the producer census.  §3 is the block scalar's arming
and the escape that survives it.  §4 is the payment at the landing.  §5 walks
the corpus.  §6 is what still does not pay.  §7 is the price. -/

namespace L4YAML.Tests.Guards.Col0ParkArmsCheck

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.IndentStackMono
open L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.LineOpenGuard
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.CharPredicates

/-! ## §1  The field

A conditional, not a fact: the park claims nothing about a cursor inside a line,
because nothing is owed there.  `h_arm`'s shape (item 77) states the same
division with the other disjunct spelled out; this one states it as the
implication its consumer reads. -/

/-- The field's own type, written out: what a producer promises and what the
    column-0 arm collects. -/
example {sc : ScannerState} {sp_scan : SurfPos}
    (h : (sp_scan.col = 0 → sc.needIndentCheck = true) ∨ True)
    (hcol : sp_scan.col = 0) :
    sc.needIndentCheck = true ∨ True :=
  match h with
  | Or.inl f => Or.inl (f hcol)
  | Or.inr _ => Or.inr trivial

/-! ## §2  The producer census — fourteen sites, four pay

Established by the compiler rather than by reading: the same payment term was
attempted at every one of the fourteen, and the ten that punt are the ten where
it does not typecheck.

  * **4 PAY** — the block-scalar arms, each holding `hbs : c = '|' ∨ c = '>'`
    from its own `dispatchContent_blockScalar_prod`.
  * **8 punt** — the other content arms (flow, properties, quoted, multi-line,
    plain).  None of them has `hbs`, and none of them can park at column 0:
    item 77's `dispatchContent_col_pos_or_armed` note is that the block scalar
    is the ONE content scan that reaches a line start.
  * **2 punt** — the two flow CLOSES (`]` and `}`), which run no content
    dispatch at all.

The punts are therefore free in the strong sense: they name a premise none of
their parks can satisfy, not a cover that was there to lose.  §5 measures the
claim that carries this — every column-0 park in the suite is behind a block
scalar. -/

/-- What a paying producer has, and what it hands over.  The `hbs` is the arm's
    own, not a case split introduced for this item. -/
example {s_prep s' : ScannerState} {sp' : SurfPos} {c : Char}
    (hbs : c = '|' ∨ c = '>')
    (hpeek : s_prep.peek? = some c)
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s')
    (hcorr' : ScannerSurfCorr s' sp') :
    (sp'.col = 0 → s'.needIndentCheck = true) ∨ True :=
  Or.inl (content_park_nic hbs hpeek h_dispatch hcorr')

/-! ## §3  The block scalar's arming, and the escape that survives it

`[170]`/`[174]` begins its body past a `b-break`; `consumeNewline` raises the
flag on every break and the collection loop only ever raises it again.  The one
header that consumes no break is the one at end of input.

The disjunction below is not defensive vagueness — the right disjunct is
REACHED, and §3b is what makes that a checked fact instead of a claim. -/

example {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanBlockScalar s = .ok s') :
    s'.needIndentCheck = true ∨ 0 < s'.col :=
  scanBlockScalar_nic_or_col_pos hpk hnb hok

/-- The monotonicity the body rides on, stated where the loop can be seen. -/
example {s_orig s_nl s' : ScannerState} {chomp : ChompStyle}
    {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (hs : s_nl.needIndentCheck = true)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.needIndentCheck = true :=
  scanBlockScalarBody_nic_mono hs h

/-! ### §3b  The escape is real

Both halves are checked.  `"k: |"` — a header at end of input — leaves the flag
DOWN, so the unconditional statement would be FALSE and the field's conditional
form is forced.  The same input stops at column 4, which is the
disjunct the lemma returns, and the reason a column-0 consumer never meets it. -/

private def dispatchAtIndicator (inp : String) : Option (Nat × Bool) := Id.run do
  let mut cur := ScannerState.mk' inp
  for _ in [0:40] do
    match scanNextToken_preprocess cur with
    | .ok (some (sp, c)) =>
      if c == '|' || c == '>' then
        match scanNextToken_dispatchContent sp c with
        | .ok s' => return some (s'.col, s'.needIndentCheck)
        | .error _ => return none
    | _ => return none
    match scanNextToken cur with
    | .ok (some c') => cur := c'
    | _ => return none
  return none

-- A header at END OF INPUT: the flag is DOWN.  This is the counterexample to
-- the unconditional claim, and it is why `h_nic0` is an implication.
#guard dispatchAtIndicator "k: |" == some (4, false)
#guard dispatchAtIndicator "k: >" == some (4, false)
#guard dispatchAtIndicator "k: |2" == some (5, false)

-- …and every one of them stops strictly inside its line, which is the other
-- disjunct.  A column-0 consumer therefore never reaches the escape.
#guard ((["k: |", "k: >", "k: |2", "- |", "| # c", "|  "].filterMap
          dispatchAtIndicator).all (fun p => p.2 || 0 < p.1)) == true

-- A header followed by a break: the flag is UP, and the park IS at column 0.
#guard dispatchAtIndicator "k: |\n  x\nc: d\n" == some (0, true)
#guard dispatchAtIndicator "k: >\n  x\nc: d\n" == some (0, true)
#guard dispatchAtIndicator "k:\n  a: |\n    x\n  c: d\n" == some (0, true)

/-! ## §4  The payment

The same two lemmas item 151 factored, with the floor arriving from the park's
flag instead of from the landing's arm.  `preprocess_top_le_col_of_armed` is
what turns the flag into the floor; its sentinel disjunct falls to
`SentinelBase`, exactly as it does inside `landing_floor_of_arm`. -/

example {sc s_prep s_skip : ScannerState} {c : Char}
    {w lo m : Nat} {ksw ksw' : List FrameLevel}
    -- the PARK's own datum, item 154's field
    (h_armed : sc.needIndentCheck = true)
    (h_flow : sc.inFlow = false)
    (h_skip : skipToContent sc = .ok s_skip)
    (h_base : SentinelBase sc) (h_mono : Mono sc)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_fl : Floor lo m ksw) (h_cv : Covered lo ksw sc)
    (hmem : FrameLevel.map w ∈ ksw) (h_ww : ResumeWidths ksw ksw' w) (h_scol : s_prep.col = w) :
    ∃ lo : Nat, Floor lo w (FrameLevel.map w :: ksw') ∧ Covered lo (FrameLevel.map w :: ksw') s_prep := by
  have h_floor : s_prep.currentIndent ≤ (s_prep.col : Int) := by
    rcases preprocess_top_le_col_of_armed h_skip
        (by have hsc := h_flow
            unfold ScannerState.inFlow at hsc ⊢
            rw [skipToContent_preserves_flowLevel sc s_skip h_skip]
            exact hsc)
        (skipToContentLoop_needIndentCheck_mono sc s_skip _ h_skip h_armed)
        h_preprocess with h | h
    · exact h
    · rw [(preprocess_base h_preprocess h_base).currentIndent_of_size_le_one h]; omega
  exact dedent_cover_of_floor (preprocess_mono h_preprocess h_mono)
    (by rw [← h_scol]; exact h_floor) h_fl
    (preprocess_cover h_preprocess h_cv) hmem h_ww

/-! ## §5  The corpus

The tuple is: states seen / states AT column 0 / of those, ARMED / of those,
facing a dedent / of those, floored / **at column 0 with the flag DOWN**.

The last component is the item's claim and the one before it is what keeps it
from passing vacuously: the sweep found column-0 parks with real dedents, and
every one of them was armed.

~~The same walk over the 351-file `yaml-test-suite` reads
`at0=1700 armed=1700 pop=52 popFloor=52 NOT-ARMED=0`, and grouping those 1349
non-initial column-0 states by the token behind them returns ONE kind —
`ScalarStyle.literal`.~~

**That sweep read the wrong files** (item 155).  `yaml-test-suite/src/*.yaml`
are test DESCRIPTORS, not payloads — each is a root sequence of mappings, and
the 8661 states it walks take exactly THREE indent-stack shapes.  The payloads
are in the `yaml: |` blocks, and `Tests.SuiteRunner.parseTestFile` extracts
them.  Re-walked over those, 351 files give 406 cases and 3262 states, and the
census reads **`at0=489 armed=489 pop=2 popFloor=2 NOT-ARMED=0`**.

The claim stands — no park reaches column 0 with the flag down — and the
support is thinner than the descriptor sweep suggested: two real dedents, not
fifty-two.  §2's reading of the ten punting producers is unaffected, since it
turns on the zero. -/

private def factsC (s : ScannerState) : Nat × Nat × Nat × Nat × Nat :=
  if s.col != 0 then (0, 0, 0, 0, 0) else
  let armed := s.needIndentCheck
  let (pop, floor) :=
    match scanNextToken_preprocess s with
    | .ok (some (s', _)) => (decide (s'.indents.size < s.indents.size),
                             decide (s'.currentIndent ≤ (s'.col : Int)))
    | _ => (false, false)
  (1, if armed then 1 else 0, if pop then 1 else 0,
   if pop && floor then 1 else 0, if armed then 0 else 1)

private def walkC (s : ScannerState) : Nat → Nat × Nat × Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, a, b, c, d, e) =>
    let (a', b', c', d', e') := factsC s
    let acc := (seen + 1, a + a', b + b', c + c', d + d', e + e')
    match scanNextToken s with
    | .ok (some s') => walkC s' fuel acc
    | _ => acc

private def censusC (inputs : List String) : Nat × Nat × Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walkC (ScannerState.mk' i) 400 acc) (0, 0, 0, 0, 0, 0)

-- The paying producers' inputs, a nested one, and three controls with no block
-- scalar at all.  **70** states, **11** at column 0, all **11** armed, **3**
-- facing a dedent, all **3** floored — and **0** at column 0 with the flag
-- down.  The three is what keeps the zero honest.
#guard censusC
  ["k:\n  a: |\n    x\nc: d\n",
   "k:\n  a: >\n    x\nc: d\n",
   "k:\n  a: \"p\n    q\"\nc: d\n",
   "k:\n  a: p\n    q\nc: d\n",
   "k:\n  m:\n    a: |\n      x\n  n: 2\n",
   "k:\n  a: b\nc: d\n",
   "- a\n- b\nc: d\n",
   "k:\n  - x\nb: 2\n"] == (70, 11, 11, 3, 3, 0)

-- The flagship, alone.  TWO states at column 0: the stream start and the park
-- the block scalar leaves; both armed.  `a: |` is written at width 2 and
-- `c: d` lands back at width 2 — the resume the punted payer could not justify.
#guard walkC (ScannerState.mk' "k:\n  a: |\n    x\n  c: d\n") 400 (0,0,0,0,0,0)
  == (9, 2, 2, 0, 0, 0)

-- A landing that really dedents: `c: d` at width 0 off a block scalar at width 2.
#guard walkC (ScannerState.mk' "k:\n  a: |\n    x\nc: d\n") 400 (0,0,0,0,0,0)
  == (9, 2, 2, 1, 1, 0)

-- …and the events those two produce, so the census is anchored to a parse.
#guard (match Events.streamToEvents "k:\n  a: |\n    x\n  c: d\n" with
        | .ok s => s | .error _ => "")
  == "+STR\n+DOC\n+MAP\n=VAL :k\n+MAP\n=VAL :a\n=VAL |x\\n\n=VAL :c\n=VAL :d\n-MAP\n-MAP\n-DOC\n-STR\n"

/-! ## §6  What still does not pay

~~One entry, and it is the one item 153 named beside this one: the **sequence
chain**.  `pendingProps.h_closeFE`, `pendingBlockContent.h_closeF` and
`pendingBlock.h_closeF` carry widths alone on one lane, and the sequence park's
relay inside `accum_content_on_pendingBlock_indented` owes a `Mono` and a
`SentinelBase` besides — that lemma takes neither today.~~  (CLOSED by item
155, which found the entry mis-stated: the lane's frames were EMPTY, so the
cover those three fields lacked would have been spendable nowhere.  Item 155
gives the lane frames off the mapping value the sequence fills, then the cover.)

Two things are NOT residue here.  The eight non-block content producers and the
two flow closes punt `h_nic0` into a premise they cannot reach (§2, §5), so
nothing is owed there.  And `h_noBreak`'s own arm is a different split: it is
the park OFF a line start, which has paid since item 152. -/

/-! ## §7  The price

One constructor field, one funding lemma at the accumulation (`content_park_nic`),
and a block-scalar family in `LineOpenGuard` beside item 77's own — the flag
twin of `scanBlockScalar_simpleKeyAllowed`, plus the column floor through the
header that refutes its end-of-input escape.  Four producers pay, ten punt, and
one `have` serves both column-0 landings.

This is the first item since 150 to add declarations, and the reason is that the
fact it needs is about the SCANNER rather than about the accumulation's own
bookkeeping: no rearrangement of the frames could produce it.  What it did not
need is a new invariant threaded through the accumulation — the flag is already
the park's to state, exactly as its save flag has been since item 77. -/

end L4YAML.Tests.Guards.Col0ParkArmsCheck

end Blanket
