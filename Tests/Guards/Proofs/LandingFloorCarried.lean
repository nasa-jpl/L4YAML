module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The landing's own floor, and the cover it seeds (DOCS item 147)

Item 130 built `IndentStackCover.Covered` a floor and named what it does not do:
thread the floored cover to the dedent punt.  The path it measured has a step in
front of it that the ledger did not record.  A producer that opens a mapping at
the landing can only claim the cover if the landing FLOORED the stack — top at
or left of the landing column — and `preprocess_top_le_col` delivers that with an
escape, `s'.indents = s.indents`.  That escape is not "the unwind popped
nothing": an unwind that pops nothing still floors.  It is "the unwind never
ran", and outside a flow the unwind runs on exactly one condition — the indent
check is armed when preprocessing reaches it.

The walk arms it.  `consumeNewline` raises `needIndentCheck` on every `b-break`
and `skipToContentLoop_needIndentCheck_mono` keeps it up, so a park that is NOT
at a line start reaches a column-0 landing with the check armed.  That is the
same premise item 76 read at the SAVE and item 139 at the FLAG; this item reads
it at the FLOOR, and appends the floor to the same landed arm.

§1 is the walk's flag and the floor it buys.  §2 is the indicator's half — a
`?` or `:` pushes at the column the landing already floored.  §3 is the cover
those two make, and the field it is paid into.  §4 checks both readings against
the scanner itself.  §5 is the measured price and what it leaves for U3. -/

namespace L4YAML.Tests.Guards.LandingFloorCarried

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.CouplingBridge (ScannerSurfCorr)

/-! ## §1  The walk's flag, and the floor

The flag is what the landed arm hands over; the floor is what preprocessing
makes of it.  Both are stated for any state, so neither depends on the
accumulation having reached a particular park. -/

/-- The flag survives the rest of the walk once a break has raised it — the
    monotonicity the landed arm's fourth conjunct is proved from. -/
example {s s' : ScannerState} {fuel : Nat}
    (h : skipToContentLoop s fuel = .ok s') (hs : s.needIndentCheck = true) :
    s'.needIndentCheck = true :=
  skipToContentLoop_needIndentCheck_mono s s' fuel h hs

/-- **The floor.**  With the walk armed, preprocessing's unwind ran, and an
    unwind stops with its top at or left of the column it unwound to.  The
    remaining disjunct is the SENTINEL — a stack popped to one entry — which is
    `IndentStackBase.SentinelBase`'s to refute and not the splitter's. -/
example {s s_walk s' : ScannerState} {c : Char}
    (h_skip : skipToContent s = .ok s_walk)
    (h_flow : s_walk.inFlow = false)
    (h_nic : s_walk.needIndentCheck = true)
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) :
    s'.currentIndent ≤ (s'.col : Int) ∨ s'.indents.size ≤ 1 :=
  preprocess_top_le_col_of_armed h_skip h_flow h_nic hok

/-- **The landed arm's own projection.**  The floor travels as the fourth
    conjunct of the payload `landing_or_park_save` reads the second of and
    `landing_or_park_ska` the third; this is the reader that spends the
    sentinel disjunct once for all of them. -/
example {sc s_prep : ScannerState} {sp_scan : SurfPos} {c : Char}
    (h_noflow : s_prep.inFlow = false)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (h_col : sp_scan.col ≠ 0)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.currentIndent ≤ (s_prep.col : Int) :=
  landing_floor_of_arm h_noflow h_larm h_col h_base h_preprocess

/-! ## §2  The indicator cannot undo it

A floored landing is only half the claim: the step that follows pushes a mapping
level, and if it pushed to the right of the landing the cover would be false.
It does not.  `[187]`'s `?` pushes at its own column; `[193]`/`[196]`'s `:`
pushes at the KEY's, which the landing's fresh save puts at the same place. -/

/-- The `?`'s push. -/
example {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanKey s = .ok s') (h_floor : s.currentIndent ≤ (s.col : Int)) :
    s'.currentIndent ≤ (s.col : Int) :=
  scanKey_top_le h_noflow hok h_floor

/-- The `:`'s, with the freshness the landing supplies as its premise.  This is
    the general form: `scanValuePrepare_top_le_keyless` (item 130) is the case
    where no key is live at all, and a landing always leaves one. -/
example {s s' : ScannerState} (hok : scanValue s = .ok s')
    (h_fresh : s.simpleKey.possible = true → s.simpleKey.pos.col = s.col)
    (h_floor : s.currentIndent ≤ (s.col : Int)) :
    s'.currentIndent ≤ (s.col : Int) :=
  scanValue_top_le hok h_fresh h_floor

/-- The key clear between them moves no indent and no column: it either leaves
    the state alone or clears the saved key. -/
example (s : ScannerState) :
    scanValueClearKey s = s ∨
      scanValueClearKey s = { s with simpleKey := { possible := false } } :=
  scanValueClearKey_id_or_clear s

/-! ## §3  The cover, and the field it is paid into

Monotonicity is the third reading: with it, a top at or left of `k` leaves `k`
as the only open mapping level at or right of `k`.  That is the cover a producer
can pay without knowing anything below its own entry — which is the producer's
situation, since the levels under a column-0 landing are fused into the stream
its route closes. -/

/-- The payment, from item 130. -/
example {s : ScannerState} {c : Nat}
    (h_mono : L4YAML.Proofs.IndentStackMono.Mono s)
    (h_top : s.currentIndent ≤ (c : Int)) :
    Covered c [FrameLevel.map c] s :=
  covered_singleton_of_top_le h_mono h_top

/-- The bridge this item adds: the three readings, assembled at the indicator
    into the cover its opener hands the frames.  Item 150 reads the same top
    TWICE — once as the stream lane's `Covered k [k]`, and once as the value
    lane's `Covered (k + 1) []`, which is where a value-line stack's floor has
    to stand since the `?`'s own level is not one of its frames. -/
example {sc s_prep s' : ScannerState} {sp_prep : SurfPos} {k : Nat} {c : Char}
    (hc : c = ':' ∨ c = '?')
    (hcol_prep : sp_prep.col = k)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_noflow : (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).inFlow = false)
    (h_save : s_prep.simpleKey.pos.col = s_prep.col)
    (h_mono : L4YAML.Proofs.IndentStackMono.Mono sc)
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc)
    (h_fl : s_prep.currentIndent ≤ (s_prep.col : Int))
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) c = .ok (some s')) :
    Covered k [FrameLevel.map k] s' ∧ Covered (k + 1) [] s' :=
  indicator_cover_at_col hc hcol_prep hcorr_prep h_noflow h_save h_mono h_base h_fl
    h_preprocess h_dispatch

/-- **The field, at its new shape.**  The cover rides BESIDE the widths, not
    over them: `ResumeFrames` says what the surface can resume at each width and
    the cover says the scanner has no open mapping level at or right of the
    floor that those widths miss.  Its floor is at or below the park's own
    index — which is where the chain bottoms — so the statement is not vacuous
    the way an unbounded `∃ lo` would be, and it is optional so that a producer
    whose stack it cannot measure keeps the route it already pays. -/
example {sc : ScannerState} {k : Nat} (h : Covered k [FrameLevel.map k] sc) :
    (∃ lo : Nat, lo ≤ k ∧ Covered lo [FrameLevel.map k] sc) ∨ True :=
  Or.inl ⟨k, Nat.le_refl k, h⟩

/-- **Why the floor is BOUNDED.**  Raising a cover's floor weakens it
    (`Covered.raise_floor`), and past the stack's own top it weakens to nothing:
    an unbounded `∃ lo, Covered lo ks sc` would be provable for every `ks`, so
    the field's conjunct says `lo ≤ n` and means something. -/
example (s : ScannerState) (ks : List FrameLevel) (hs : ∀ e ∈ s.indents, e.column < 99) :
    Covered 99 ks s := fun e he _ hlo => absurd (hs e he) (by omega)

/-- The stack's SHAPE rides the accumulation for the same reason its base does
    — seeded at `mk'`, re-established at every step. -/
example (input : String) : L4YAML.Proofs.IndentStackMono.Mono (ScannerState.mk' input) :=
  L4YAML.Proofs.IndentStackMono.mk'_mono input

example {s s' : ScannerState} (hok : scanNextToken s = .ok (some s'))
    (h : L4YAML.Proofs.IndentStackMono.Mono s)
    (hb : L4YAML.Proofs.IndentStackBase.SentinelBase s) :
    L4YAML.Proofs.IndentStackMono.Mono s' :=
  L4YAML.Proofs.IndentStackMono.scanNextToken_mono hok h hb

/-- And the whole-loop reading is unchanged by the extra rider. -/
example (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
      sp_final.chars = [] :=
  scan_content_gives_stream_v2 input tokens h

/-! ## §4  Both readings, against the scanner itself

A proof that the stack is monotone and a landing floored is worth checking
against the object it is about.  The walk runs `scanNextToken` from the seed and
reports, per state, whether the stack is strictly increasing and — where the
next step crosses a line — whether preprocessing left its top at or left of the
landing column. -/

private def monoHolds (s : ScannerState) : Bool :=
  (List.range (s.indents.size - 1)).all fun i =>
    decide (s.indents[i]!.column < s.indents[i+1]!.column)

private def floorHolds (s : ScannerState) : Bool :=
  match scanNextToken_preprocess s with
  | .ok (some (s', _)) =>
      if s'.line == s.line then true else decide (s'.currentIndent ≤ (s'.col : Int))
  | _ => true

private def walk (s : ScannerState) : Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, landings, badMono, badFloor) =>
    let isLanding : Bool :=
      match scanNextToken_preprocess s with
      | .ok (some (s', _)) => s'.line != s.line
      | _ => false
    let acc := (seen + 1, landings + (if isLanding then 1 else 0),
                badMono + (if monoHolds s then 0 else 1),
                badFloor + (if floorHolds s then 0 else 1))
    match scanNextToken s with
    | .ok (some s') => walk s' fuel acc
    | _ => acc

private def census (inputs : List String) : Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walk (ScannerState.mk' i) 200 acc) (0, 0, 0, 0)

-- The same eighteen inputs item 146's guard walks, so the state count is a
-- cross-check as well as a measurement: 121 states, 26 of them followed by a
-- landing, no stack out of order and no landing left unfloored.
#guard census
  ["a: 1\nb: 2\n", "k:\n  a: 1\n  b: 2\n", "- a\n- b\n", "k:\n  - a\n  - b\n",
   "? \"a\"\n: v\n", "k: [1, 2]\nb: 2\n", "k: |\n  x\nb: 2\n", "k:\n  a: 1\nb: 2\n",
   "k:\n  \"x\"\n  b: 2\n", "k:\n  \"a\"\n  [1, 2]\n", "k:\n  a\n  : v\n",
   "\"x\"\nb: 2\n", "a\n# c\nb: 2\n", "[1, 2]\nb: 2\n",
   "a:\n  b:\n    c: 1\nd: 2\n", "{a: 1, b: [2, 3]}\n", "k: >\n  folded\n",
   "---\na: 1\n...\n---\nb: 2\n"] == (121, 26, 0, 0)

-- The seed's stack is monotone because it has no consecutive pair.
#guard monoHolds (ScannerState.mk' "a: 1\n") == true

/-! ## §5  The price, and what it leaves

Three edits, measured at the compiler rather than from a caller closure.

* **The landed arm's fourth conjunct** costs the accumulation NOTHING in
  premises, because the sentinel rides as a disjunct instead of as a
  `SentinelBase` hypothesis on the splitter.  Adding that hypothesis instead was
  measured first: **22** sites in **17** declarations at the FIRST level alone,
  before any of their own callers.  What the disjunct form costs is two
  statement sites (`preprocess_some_ssl_comments_anyCol` and `_landing`), the
  two `h_larm` binders in `landing_or_park_save`/`_ska`, three projections that
  move from `.2.2` to `.2.2.1`, and two guard files.
* **`Mono` on the accumulation** is held by **9** declarations —
  `indicator_cover_at_col`, the four block landing arms, `accum_block_pending`,
  `accum_step_block`, `scanNextToken_accum_step` and `scanLoop_grammar_prod` —
  and passed at **47** places.  The FLOW lane carries none: its openers reach no
  `:`/`?` producer, so a premise there would be an unused binder.
* **The field** raises the **6** sites item 130 measured, and the compiler
  agrees with its ledger exactly: the four producers plus the two relays in
  `accum_content_pending`'s per-pending match.

`SLYamlStream.implicitContinue` is unmoved at FIVE `[210]` flip errors and the
raw-route census at TWO holders; no runtime file changed.  This item pays
premises and states a field — it removes no construction site.

What it leaves, in the order the dedent punt needs it:

* **The pack's own cover.**  `colon_open_map_implicit` and `colon_open_map_props`
  chain `FrameLevel.map k :: ks` from `ImplicitKeyPack`'s resume twin, and the cover they would
  inherit rides that pack, which carries none.  Both pay `Or.inr trivial` here.
  Until they pay, every cover on the field is a root producer's `[k]` at floor
  `k`, which a dedent landing at `w < k` cannot use — so the pack's field is
  what makes the conjunct spendable rather than merely true.
* **U3's spend.**  `entryKeyPack_of_dispatch`'s `h_dframes` is still the widths
  alone; the `accum_content_on_pendingMapValue*` relay (one lemma since item 179) project the route
  and drop the cover at seven places.  Widening it and spending
  `preprocess_landing_mem_or_seq` at the dedent branch also wants item 146's
  base residue there — **5** declarations, **10**
  sites — and leaves the SEQUENCE disjunct, which the `:`'s own check refutes a
  step later (`landing_mem_of_value`) and the pack cannot. -/

end L4YAML.Tests.Guards.LandingFloorCarried

end Blanket
