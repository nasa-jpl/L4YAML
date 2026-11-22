import Tests.Guards.Proofs.DeclineArmInvariants
import L4YAML.Proofs.Production.StreamAccum

/-!
# The strength ladder: what one field's second conjunct is worth (item 222)

Item 77 gave every block-context park the same arm — "the save is up, or the
cursor is inside a line".  Item 80 gave the two CONTENT parks a stronger one:
the save is up **and the saved key is down**.  Item 221 ended by naming the gap
that leaves at `pendingFlow`:

> `h_arm` records half of what its producer proves, and nothing has measured
> what the other half would buy at the nine `pendingFlow` sites.

This file is that measurement, and the ledger row it adds is the **STRENGTH
LADDER**: for one fact carried by a family of carriers, the strongest form each
carrier can state **from its own fields**, checked arm by arm, with the residue
NAMED where it fails.  Counting carriers (item 198), sites (200), conclusions
(201) and zeros (221) all leave this unasked.

## The ladder, as the elaborator reads it

| park | pays the tight arm with | before 222 | 222 | 223 |
|---|---|---|---|---|
| `pendingContent` | `h_arm` IS tight (item 80) | yes | yes | yes |
| `pendingBlockContent` | `h_arm` IS tight | yes | yes | yes |
| `pendingProps` | `h_col0 : 0 < sp_scan.col` | yes | yes | yes |
| `pendingBlock` | `h_col : sp_scan.col = n + 1` | yes | yes | yes |
| `pendingMapValue` | `h_col0` (item 221's find) | yes | yes | yes |
| `pendingFlow` | `h_arm`, tightened at 222 | no | **yes** | yes |
| `noPending` | `mk'_simpleKey_false` — ONE payer | no | no | **yes** |
| `pendingDocEnd` | `scanDocumentEnd_simpleKey_false` | no | no | **yes** |
| `pendingDocStart` | `scanDocumentStart_simpleKey_false` | no | no | **yes** |

**Item 223 closed the last three rows and the family is uniform**, so the
reading lives in the library as `PendingNode.arm_tight_or_col` with no
hypothesis at all, and item 78's nine-arm `PendingNode.arm_or_col` is one
`And.left` off it.

**A family's uniform reading is as strong as its weakest carrier, and which
carrier is weakest is a measurement, not a design choice.**  Two of the five
rows that already paid (`pendingBlock`, `pendingMapValue`) pay by a COLUMN field
that `PendingNode.arm_or_col` does not read — it takes `Or.inl` off their
`h_sk` instead.  Free strength, discarded at the uniform reading, for want of
anyone asking which disjunct was cheaper.

## What the escape's nine sites actually cost

Tightening the field alone breaks **three** definitions, not nine: a
constructor's blast radius is its producer's SIGNATURE, not its producer's call
graph.  Tightening `block_dispatch_deferred` with it brings the nine in — eight
block-indicator entrances and one content entrance, exactly the split
`pendingFlow.h_nic0`'s docstring records — and they pay in two different ways:

* the **eight** cannot pay with the conjunct.  §3 measures why: of the three
  indicator scans, only `scanKey` clears the saved key; `scanBlockEntry` and
  `scanValue` hand `simpleKey` through untouched.  They pay on the OTHER
  disjunct instead, with the column the indicator spends
  (`arm_tight_of_block_dispatch`);
* the **one** pays by DELETION — `content_park_arm` has proved the tight arm
  since item 77 and the site wrote `.imp_left And.left` to throw it away.

That deletion is Reflection 662 (`ProjectAtTheConsumer`) caught in the act at a
FIELD rather than at a lemma: a strong producer was already paying, and a weak
field discarded the strength at every site.

## What it buys

§5: the escape's park stops having a state of its own **by construction**.
Item 219 measured `pFlowPark` and `pContentish` equal and said so; with the
tight field the two readings are the SAME EXPRESSION, so item 220's
`ONLYflowPark = 0` is no longer a measurement — which is the floor item 183's
delete-don't-narrow order was waiting on.
-/

namespace Tests.Guards.ArmStrengthLadder

set_option autoImplicit false

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.ScannerCorrectness
open Tests.DeclineReachCensus

variable {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}

/-! ## §1  The ladder, row by row, from each park's own fields

Each row below states the tight arm from exactly the field(s) the named
constructor carries — no park in scope, so no arm can borrow another's
evidence. -/

/-- `pendingProps.h_col0`. -/
example (h_col0 : 0 < sp_scan.col) :
    (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col :=
  Or.inr h_col0

/-- `pendingMapValue.h_col0` — the field item 221 found had been dropped. -/
example (h_col0 : 0 < sp_scan.col) :
    (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col :=
  Or.inr h_col0

/-- `pendingBlock.h_col` — a WIDTH, which is a column once `n + 1` is read. -/
example {n : Nat} (h_col : sp_scan.col = n + 1) :
    (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col :=
  Or.inr (by omega)

/-- `pendingContent.h_arm` and `pendingBlockContent.h_arm` — item 80's shape,
    which is the tight arm itself. -/
example (h_arm : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨
      0 < sp_scan.col) :
    (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col :=
  h_arm

/-- **Why the last three rows could not be closed by rearrangement.**  From the
    loose arm alone the tight one does not follow, and this is the state that
    separates them — the save up, the key live, the cursor at a line start.  It
    is item 220's `sepFlowParkContentish`, which is not a coincidence: that state
    was the escape's corner.  So each of `noPending`, `pendingDocEnd` and
    `pendingDocStart` had to be paid by its PRODUCER's own scan fact (§4), not by
    an algebraic move at the constructor. -/
example : ∃ (ska skp : Bool) (col : Nat),
    ((ska = true ∨ 0 < col) ∧ ¬((ska = true ∧ skp = false) ∨ 0 < col)) :=
  ⟨true, true, 0, by simp⟩

/-! ## §2  The family, uniform

Item 222 could state the family reading only with the missing fact handed in:
`(h_skp : sc.simpleKey.possible = false)`, owed by three carriers and looked at
by none of the other six.  Item 223 paid it at those three producers, so the
hypothesis is gone and the reading is a LIBRARY lemma.  What stands here is the
pin: if the hypothesis ever comes back, or the loose reader stops being a
projection of the tight one, this module fails. -/

/-- The family's uniform tight reading, with no hypothesis but `inFlow = false`
    — which `noPending` alone needs, because its right disjunct is `inFlow` and
    not a column. -/
example (h_noflow : sc.inFlow = false)
    (h : PendingNode sc false sp_start sp_block sp_scan) :
    (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col :=
  PendingNode.arm_tight_or_col h_noflow h

/-- …and item 78's reading is one `And.left` off it, at every one of the nine
    arms rather than at the four that used to need a projection. -/
example (h_noflow : sc.inFlow = false)
    (h : PendingNode sc false sp_start sp_block sp_scan) :
    sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col :=
  (PendingNode.arm_tight_or_col h_noflow h).imp_left And.left

/-- The strengthening is not vacuous at the PARK level either: a park carrying
    the loose arm admits a live saved key, and the tight one refuses it.  This is
    §1's separating state restated where the family reading reads it. -/
example (h : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨
      0 < sp_scan.col) (h_col : sp_scan.col = 0) :
    sc.simpleKey.possible = false := by
  rcases h with ⟨_, h2⟩ | h2
  · exact h2
  · omega

/-! ## §3  Why the eight could not pay with the conjunct

`block_indicator_arm` gives the flag at all three indicators.  Its `_false`
twin exists for exactly ONE of them, and this section is the measurement: the
`?` scan clears the saved key, and the `-` and `:` scans hand `simpleKey`
through their record update untouched.  Anything claiming otherwise would have
to refute the two `example`s below, which state the INHERITANCE. -/

/-- The `?` scan clears — the one indicator that could have paid the conjunct. -/
lemma scanKey_simpleKey_false {s s' : ScannerState}
    (hok : scanKey s = .ok s') : s'.simpleKey.possible = false := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp at hok; done)
    | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
    | (exfalso; simp_all [throw, throwThe, MonadExceptOf.throw])

/-- …and the `-` scan does not: on its main arm the result's `simpleKey` is the
    INCOMING one, so no `_simpleKey_false` twin can exist for it. -/
example (s : ScannerState) :
    ((s.emit YamlToken.blockEntry).advance).simpleKey = s.simpleKey := by
  rw [advance_preserves_simpleKey, emit_preserves_simpleKey]

/-- The payment the eight sites actually make: a block indicator SPENDS a
    column, and the correspondence reads it at the surface.  This is the shape
    `arm_tight_of_block_dispatch` has in the library. -/
example {s s' : ScannerState} {sp : SurfPos} {c : Char}
    (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (hcorr : Proofs.CouplingBridge.ScannerSurfCorr s' sp) :
    (s'.simpleKeyAllowed = true ∧ s'.simpleKey.possible = false) ∨ 0 < sp.col :=
  Or.inr (by rw [hcorr.col_eq]; exact Proofs.LineOpenGuard.dispatchBlockIndicators_col_pos hpk hok)

/-! ## §4  The three rungs, spent

Item 222 proved these three here, as prices rather than payments — nothing
consumed them and they sat in a test module, which is exactly where a library
constructor's payer CANNOT sit.  Item 223 restated all three in
`L4YAML/Proofs/Scanner/LineOpenGuard.lean`, beside the `_simpleKeyAllowed`
siblings item 77 put there, and spent them at the four payer sites.  The pins
below are what is left here: the shapes, and the site arithmetic.

| rung | library lemma | producers | payers |
|---|---|---|---|
| `noPending` | `mk'_simpleKey_false` | 8 | **1** (the stream seed) |
| `pendingDocEnd` | `scanDocumentEnd_simpleKey_false` | 1 | 1 |
| `pendingDocStart` | `scanDocumentStart_simpleKey_false` | 2 | 2 |

**A field's price is its PAYERS, not its sites** (item 222's corollary), and
`noPending` is the case that states it: eight producers, seven of which refute
`inFlow = false` and never look at the arm at all. -/

/-- `noPending`'s rung, at the library. -/
example (input : String) : (ScannerState.mk' input).simpleKey.possible = false :=
  Proofs.LineOpenGuard.mk'_simpleKey_false input

/-- `pendingDocStart`'s rung.  Not `rfl` — `unwindIndents`, `emit` and `advanceN`
    sit between the write and the read, which is why it is a lemma and not a
    projection. -/
example (s : ScannerState) : (scanDocumentStart s).simpleKey.possible = false :=
  Proofs.LineOpenGuard.scanDocumentStart_simpleKey_false s

/-- `pendingDocEnd`'s rung, on every arm of the scan that returns. -/
example {s s' : ScannerState} (h : scanDocumentEnd s = .ok s') :
    s'.simpleKey.possible = false :=
  Proofs.LineOpenGuard.scanDocumentEnd_simpleKey_false h

/-- **And the seed's rung was already in hand, twice.**  `scan_content_gives_stream_v2`
    proves this same fact for item 81's `KeysBehindCursor` and again for item
    123's stale-cursor floor, in the SAME `refine` that then handed the park its
    flag alone.  The shape below is what both of those `have`s state. -/
example (input : String) :
    ((ScannerState.mk' input).emit YamlToken.streamStart).simpleKey.possible = false := by
  simp [ScannerState.emit, ScannerState.mk']

/-! ## §5  What the tightening buys: the escape's reading IS the content reading

Item 219 read `pendingFlow`'s `sc` footprint as `pFlowPark` and measured it
equal to `pContentish` on every sample, calling that "the escape has no state of
its own".  With item 222's field the two are the same expression, so the
equality is definitional and item 220's `ONLYflowPark = 0` stops being a
measurement. -/

/-- `pFlowPark` at the escape's NEW field list. -/
def pFlowParkT (sc : ScannerState) : Bool :=
  ((sc.simpleKeyAllowed && !sc.simpleKey.possible) || 0 < sc.col) &&
  !sc.allowDirectives && (sc.col != 0 || sc.needIndentCheck)

/-- …and it is `pContentish`, on the nose. -/
lemma pFlowParkT_eq_pContentish (sc : ScannerState) :
    pFlowParkT sc = pContentish sc := rfl

/- The tightening is not vacuous at the state level: item 220's separating
   state is admitted by the old reading and refused by the new one. -/
#guard pFlowPark Tests.Guards.DeclineArmLattice.sepFlowParkContentish &&
       !pFlowParkT Tests.Guards.DeclineArmLattice.sepFlowParkContentish

/-- And the corner it separated is now unstatable: `pFlowParkT ∧ ¬pContentish`
    is `false` at every state, by `rfl` rather than by a census. -/
example (sc : ScannerState) : (pFlowParkT sc && !pContentish sc) = false := by
  simp [pFlowParkT_eq_pContentish]

end Tests.Guards.ArmStrengthLadder
