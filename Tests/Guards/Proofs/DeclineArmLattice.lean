import Tests.DeclineArmCensus

/-!
# Which zeros are THEOREMS, and which are invariants nobody has stated (item 220)

`Tests/DeclineArmCensus.lean` reads twelve containments empty over its 50 653
programs and its 402 leaves.  A zero over inputs is a coverage report — item
219's rule — so the census asks the same question of a synthetic state space
instead: 10 240 states, exhaustive over every field the park predicates read.
There the answer splits, and **this module is the half that can be proved**.

Seven containments hold at every synthetic state.  That is a sweep over an
abstraction (`col` in `0..3`, the stack top in `-1..2`), so it is a hypothesis
and not a fact; each one is therefore restated here as a lemma over an
arbitrary `ScannerState` and discharged by the compiler.  All seven go by the
same case split, which is itself the finding: **the park family is a chain
under containment, by Bool algebra, with no scanner reasoning anywhere.**

The remaining five are separated by a synthetic state, so no proof of them
exists.  They are pinned below as `#guard`s on the census's own predicates
evaluated at the separating state the sweep printed, which makes
"this zero is not a theorem" something the build checks rather than something
the entry asserts.  What they are is scanner INVARIANTS — true of every state
the scan reaches and of no theorem — and stating them is the next item's work.

**One of the seven is only a theorem once the reading is tightened.**  Item
219's `pProps` drops `pendingProps.h_col0 : 0 < sp_scan.col`, a field the
constructor carries.  Tightening moves no reachable count at all (4 550 states
either way, none of them at column 0) and moves `props -> flowPark` and
`props -> contentish` from MEASURED to PROVED.  A dropped field costs nothing
in the counts and everything in the classification.
-/

namespace Tests.Guards.DeclineArmLattice

set_option autoImplicit false

open L4YAML L4YAML.Scanner
open Tests.DeclineReachCensus Tests.DeclineArmCensus

variable {sc : ScannerState}

/-! ## The seven entailments -/

/-- The tactic every one of them takes: split the five flags, the column and the
    stack top, and let `simp` close what is left.  No scanner lemma is used. -/
local macro "park_chain" : tactic =>
  `(tactic| (cases hc : sc.col <;>
      cases hska : sc.simpleKeyAllowed <;> cases hskp : sc.simpleKey.possible <;>
      cases hdir : sc.allowDirectives <;> cases hnic : sc.needIndentCheck <;> simp_all))

/-- `pendingDocStart`'s state is a `pendingFlow` state. -/
lemma docStart_flowPark : pDocStart sc = true → pFlowPark sc = true := by
  simp only [pDocStart, pFlowPark]; park_chain

/-- …and a `pendingContent`/`pendingBlockContent` state. -/
lemma docStart_contentish : pDocStart sc = true → pContentish sc = true := by
  simp only [pDocStart, pContentish]; park_chain

/-- `pendingProps`, read WITH `h_col0`, is a `pendingFlow` state. -/
lemma propsT_flowPark : pPropsT sc = true → pFlowPark sc = true := by
  simp only [pPropsT, pProps, pFlowPark]; park_chain

/-- …and a content state. -/
lemma propsT_contentish : pPropsT sc = true → pContentish sc = true := by
  simp only [pPropsT, pProps, pContentish]; park_chain

/-- `pendingBlock`'s state is a `pendingFlow` state. -/
lemma block_flowPark : pBlock sc = true → pFlowPark sc = true := by
  simp only [pBlock, pFlowPark, floorB]; park_chain

/-- …and a content state. -/
lemma block_contentish : pBlock sc = true → pContentish sc = true := by
  simp only [pBlock, pContentish, floorB]; park_chain

/-- **The escape has no state of its own, and half of item 219's evidence for
    that was already a theorem.**  Item 219 reported `flowPark and not
    contentish` and `contentish and not flowPark` as two measurements, both
    zero; the second direction needs no measurement at all. -/
lemma contentish_flowPark : pContentish sc = true → pFlowPark sc = true := by
  simp only [pContentish, pFlowPark]; park_chain

/-- And the other direction is not a theorem — here is exactly where it fails.
    `pendingFlow`'s footprint exceeds the content parks' at one corner and one
    corner only: a possible simple key standing at column 0 with the indent
    check still owed.  The census reads that corner **0** over 216 114
    enumerated states, over 2 946 corpus states and over the 297 472 states of
    an alphabet built to spell it — so it is an invariant, not an entailment. -/
lemma flowPark_not_contentish_corner :
    (pFlowPark sc = true ∧ pContentish sc = false) ↔
      (sc.allowDirectives = false ∧ sc.needIndentCheck = true ∧ sc.col = 0 ∧
       sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = true) := by
  simp only [pContentish, pFlowPark]; park_chain

/-! ## The five that are NOT theorems, each with its separating state

    Every state below is the one the synthetic sweep printed as the first
    witness for its row, rebuilt here so the build checks that the census's own
    predicates really do come apart on it. -/

/-- `ad=false nic=false ska=false skp=false flow=0 col=1 ci=-1 tok=docStart@0`. -/
def sepDocStartMapValue : ScannerState :=
  { ScannerState.mk' "" with
    allowDirectives := false, needIndentCheck := false, simpleKeyAllowed := false,
    col := 1, line := 0, indents := #[{ column := -1, isSequence := false }],
    tokens := #[{ pos := ⟨0, 0, 0⟩, val := .documentStart }] }

/-- `ad=false nic=true ska=true skp=true flow=0 col=0 ci=-1 tok=empty`. -/
def sepFlowParkContentish : ScannerState :=
  { ScannerState.mk' "" with
    allowDirectives := false, needIndentCheck := true, simpleKeyAllowed := true,
    simpleKey := { (ScannerState.mk' "").simpleKey with possible := true },
    col := 0, line := 0, indents := #[{ column := -1, isSequence := false }] }

/-- `ad=false nic=false ska=true skp=false flow=0 col=1 ci=0 tok=empty`. -/
def sepBlockMapValue : ScannerState :=
  { ScannerState.mk' "" with
    allowDirectives := false, needIndentCheck := false, simpleKeyAllowed := true,
    col := 1, line := 0, indents := #[{ column := 0, isSequence := false }] }

/-- `ad=false nic=false ska=true skp=false flow=0 col=0 ci=-1 tok=scalar@0`. -/
def sepMapValueContent : ScannerState :=
  { ScannerState.mk' "" with
    allowDirectives := false, needIndentCheck := false, simpleKeyAllowed := true,
    col := 0, line := 0, indents := #[{ column := -1, isSequence := false }],
    tokens := #[{ pos := ⟨0, 0, 0⟩, val := .scalar "a" .plain }] }

/- `pendingDocStart` is NOT contained in `pendingMapValue`. -/
#guard pDocStart sepDocStartMapValue && !pMapValue sepDocStartMapValue

/- `pendingFlow` is NOT contained in the content parks — the corner. -/
#guard pFlowPark sepFlowParkContentish && !pContentish sepFlowParkContentish

/- `pendingBlock` is NOT contained in `pendingMapValue`. -/
#guard pBlock sepBlockMapValue && !pMapValue sepBlockMapValue

/- `pendingMapValue` is NOT contained in `pendingFlow` … -/
#guard pMapValue sepMapValueContent && !pFlowPark sepMapValueContent

/- … nor in the content parks. -/
#guard pMapValue sepMapValueContent && !pContentish sepMapValueContent

/- And the corner state is the one `flowPark_not_contentish_corner` names. -/
#guard sepFlowParkContentish.allowDirectives == false &&
       sepFlowParkContentish.needIndentCheck == true &&
       sepFlowParkContentish.col == 0 &&
       sepFlowParkContentish.simpleKeyAllowed == true &&
       sepFlowParkContentish.simpleKey.possible == true

/-! ## The single cause behind the one park that DOES stand alone

    `pendingDocEnd` is disjoint from all seven others over both samples, and the
    census says why in one field: `allowDirectives` is UP at every one of the
    2 345 enumerated `docEnd` states and DOWN at every one of the 2 345
    `docStart` states.  Six of the seven other park predicates require it down,
    and the seventh (`noPending`) requires column 0, which no `docEnd` state
    has.  That is not a coincidence of the sample — item 138's own docstring on
    `PendingNode` argues it: "only two constructors can have it, the stream's
    own seed (`noPending`) and a `...` (`pendingDocEnd`)".  What the census adds
    is that the flag is up at EVERY reachable one, which is a field
    `pendingDocEnd` could carry and does not. -/

/-- Six of the eight park predicates are false wherever the directive flag is
    up, whatever else holds. -/
lemma parks_need_flag_down (h : sc.allowDirectives = true) :
    pContentish sc = false ∧ pProps sc = false ∧ pDocStart sc = false ∧
    pFlowPark sc = false ∧ pBlock sc = false ∧ pMapValue sc = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [pContentish, pProps, pDocStart, pFlowPark, pBlock, pMapValue, h] <;> simp

end Tests.Guards.DeclineArmLattice
