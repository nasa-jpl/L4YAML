import Tests.DeclineCornerCensus
import Tests.Guards.Proofs.DeclineArmLattice
import L4YAML.Proofs.Scanner.LineOpenGuard

/-!
# The five residuals, and what each one actually needed (item 221)

Item 220 left five containments "with a separating state and no proof" and
called them scanner invariants nobody had stated.  All five are closed here,
and only ONE of them needed a fact the library did not already have.

The minimal-zero search in `Tests/DeclineCornerCensus.lean` is what sorted
them.  It reads each containment's separator through a seven-atom projection,
finds the smallest sub-conjunction of that profile which still reads zero over
the walk, and the answer says where to look:

| containment | minimal zero | what closes it |
|---|---|---|
| `pendingMapValue ⊆ pendingFlow` | `nic=0 ∧ col0=1` | `pendingMapValue.h_col0`, a field the constructor CARRIES |
| `pendingMapValue ⊆ pendingContent` | `nic=0 ∧ col0=1` | the same field |
| `pendingFlow ⊆ pendingContent` | `skp=1 ∧ col0=1` | `dispatchContent_arm_or_col_any`'s second conjunct, which `h_arm` DROPS |
| `pendingDocStart ⊆ pendingMapValue` | `ska=0 ∧ dsTok=1` | `scanDocumentStart` sets the flag — by `rfl` |
| `pendingBlock ⊆ pendingMapValue` | `real=0` | **the one new lemma**: `dispatchBlockIndicators_lastTokenReal` |

**Two of the five were never invariants.**  `pendingMapValue` carries
`h_col0 : 0 < sp_scan.col` and item 219's reading of it does not — the third
time in three items that a dropped field has misclassified a zero (item 220
found `pendingProps.h_col0`; item 220's own instrument debt named this park's
missing column and did not look for the field).  Tightening the reading moves
no reachable count at all, 105 683 either way over both alphabets, and turns
both containments into one-tactic theorems.

**A third was already paid for by its producer.**  `pendingFlow.h_arm` records
`simpleKeyAllowed = true ∨ 0 < col`; the lemma that discharges it at the content
dispatch proves `(simpleKeyAllowed = true ∧ simpleKey.possible = false) ∨
0 < col`, and the second conjunct is exactly the corner's refutation.  The park
throws it away at the constructor.

So the corner — item 183's delete-don't-narrow order rests on it — is closed by
a conjunct that has been sitting in `LineOpenGuard.lean` since item 77.
-/

namespace Tests.Guards.DeclineArmInvariants

set_option autoImplicit false

open L4YAML L4YAML.Scanner
open Tests.DeclineReachCensus Tests.DeclineArmCensus Tests.DeclineCornerCensus
open L4YAML.Proofs.LineOpenGuard

variable {sc : ScannerState}

/-! ## §1  The separator profiles, proved

    `Tests.DeclineCornerCensus.sepProfile` reads these off the exhaustive
    synthetic space, which is a sweep over an abstraction and therefore a
    hypothesis.  Each one is restated here over an arbitrary `ScannerState` and
    discharged by the compiler, so the minimal-zero search below is running on
    facts about the predicates and not on a sample. -/

/-- The split every one of them takes. -/
local macro "atom_chain" : tactic =>
  `(tactic| (cases hc : sc.col <;>
      cases hska : sc.simpleKeyAllowed <;> cases hskp : sc.simpleKey.possible <;>
      cases hdir : sc.allowDirectives <;> cases hnic : sc.needIndentCheck <;>
      cases hlr : lastRealB sc.tokens <;> simp_all))

/-- `pendingDocStart` outside `pendingMapValue` has the save DOWN — every other
    atom of the profile `pendingDocStart` supplies itself. -/
lemma docStart_sep : pDocStart sc = true → pMapValue sc = false →
    sc.simpleKeyAllowed = false := by
  simp only [pDocStart, pMapValue]; atom_chain

/-- The corner, in the form the minimal-zero search returns: a saved simple key
    standing at column 0. -/
lemma flowPark_sep : pFlowPark sc = true → pContentish sc = false →
    sc.simpleKey.possible = true ∧ sc.col = 0 ∧ sc.needIndentCheck = true := by
  simp only [pFlowPark, pContentish]; atom_chain

/-- `pendingBlock` outside `pendingMapValue` has a placeholder in the final
    slot — its own `h_sk`, `h_nodir` and `h_col` cover the rest. -/
lemma block_sep : pBlock sc = true → pMapValue sc = false →
    lastRealB sc.tokens = false := by
  simp only [pBlock, pMapValue, floorB]; atom_chain

/-- `pendingMapValue` outside `pendingFlow` stands at column 0 with the indent
    check disarmed — which is `h_nic0`'s hypothesis and `h_nic`'s negation at
    once, so the park cannot be there. -/
lemma mapValue_sep : pMapValue sc = true → pFlowPark sc = false →
    sc.col = 0 ∧ sc.needIndentCheck = false := by
  simp only [pMapValue, pFlowPark]; atom_chain

/-- …and the same outside the content parks. -/
lemma mapValue_sep_content : pMapValue sc = true → pContentish sc = false →
    sc.col = 0 ∧ sc.needIndentCheck = false := by
  simp only [pMapValue, pContentish]; atom_chain

/-! ## §2  The two that were never invariants

    `pendingMapValue.h_col0 : 0 < sp_scan.col` is a field of the constructor
    (`StreamAccum.lean`, within the `pendingMapValue` telescope), and
    `ScannerSurfCorr.col_eq` delivers it at the runtime state.  Item 219's
    reading drops it. -/

/-- With the field read, `pendingMapValue`'s state is a `pendingFlow` state. -/
lemma mapValueT_flowPark : pMapValueT sc = true → pFlowPark sc = true := by
  simp only [pMapValueT, pMapValue, pFlowPark]; atom_chain

/-- …and a `pendingContent`/`pendingBlockContent` state. -/
lemma mapValueT_contentish : pMapValueT sc = true → pContentish sc = true := by
  simp only [pMapValueT, pMapValue, pContentish]; atom_chain

/-! ## §3  The corner, closed at the escape's own two producers

    `pendingFlow` has exactly ONE construction site in the whole development —
    inside `block_dispatch_deferred` (`StreamAccum.lean:20667`) — and that
    producer's application sites split eight-plus-one between the
    block-indicator dispatch and the content dispatch, which is the same split
    `h_nic0` is paid over (`StreamAccum.lean:1737-1748`).  Both halves are
    below, and neither needs a lemma that did not already exist. -/

/-- The content dispatch's park is a content park.  `dispatchContent_arm_or_col_any`
    is item 77's arm lemma; `h_arm` keeps its first conjunct and drops the
    second, and the second is the whole proof. -/
lemma flowPark_contentish_of_content_dispatch {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hpk : s.peek? = some c)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    pFlowPark s' = true → pContentish s' = true := by
  have h := dispatchContent_arm_or_col_any hflow hpk hnotdoc hok
  simp only [pFlowPark, pContentish]
  rcases h with ⟨h1, h2⟩ | h <;> simp_all

/-- The block indicator's park is one too, and more cheaply: the indicator
    spends a column, so the content parks' arm holds on the right. -/
lemma flowPark_contentish_of_block_dispatch {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    pFlowPark s' = true → pContentish s' = true := by
  have h := dispatchBlockIndicators_col_pos hpk hok
  simp only [pFlowPark, pContentish]
  simp_all

/-! ## §4  The remaining two, at their own producers -/

/-- `[203] c-directives-end`'s scan re-arms the save, so a `pendingDocStart`
    state is a `pendingMapValue` state.  The flag is a field of the state the
    scan returns and the fact is `rfl`. -/
lemma scanDocumentStart_simpleKeyAllowed (s : ScannerState) :
    (scanDocumentStart s).simpleKeyAllowed = true := rfl

lemma docStart_mapValue_of_scanDocumentStart (s : ScannerState) :
    pDocStart (scanDocumentStart s) = true → pMapValue (scanDocumentStart s) = true := by
  have hska : (scanDocumentStart s).simpleKeyAllowed = true :=
    scanDocumentStart_simpleKeyAllowed s
  simp only [pDocStart, pMapValue, hska]
  intro h
  simp_all

/-- `pendingBlock` is the one block-context park that carries no `h_real`, and
    `dispatchBlockIndicators_lastTokenReal` is the fact that supplies it — the
    only new scanner lemma any of item 220's five residuals needed. -/
lemma block_mapValue_of_block_dispatch {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    pBlock s' = true → pMapValue s' = true := by
  have h := dispatchBlockIndicators_lastTokenReal hok
  have hreal : lastRealB s'.tokens = true := by
    obtain ⟨hsz, hne⟩ := h
    simp only [lastRealB, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨hsz, hne⟩
  simp only [pBlock, pMapValue, floorB, hreal]
  intro h'
  simp_all

/-! ## §5  What the census reads, checked against what is proved

    The profiles below are `sepProfile`'s own output.  §1 proves each one over
    an arbitrary state, so these guards are what ties the two together: if the
    census's projection ever stops seeing what the lemmas state, the build
    says so. -/

/- `pendingDocStart ⊆ pendingMapValue`. -/
#guard profStr (sepProfile 0) == "dir=0,nic=0,ska=0,col0=0,real=1,dsTok=1"

/- `pendingFlow ⊆ pendingContent` — the corner. -/
#guard profStr (sepProfile 1) == "dir=0,nic=1,ska=1,skp=1,col0=1"

/- `pendingBlock ⊆ pendingMapValue`. -/
#guard profStr (sepProfile 2) == "dir=0,nic=0,ska=1,col0=0,real=0,dsTok=0"

/- `pendingMapValue ⊆ pendingFlow` and `⊆ pendingContent`. -/
#guard profStr (sepProfile 3) == "dir=0,nic=0,ska=1,col0=1,real=1"
#guard profStr (sepProfile 4) == "dir=0,nic=0,ska=1,col0=1,real=1"

/- The tightening kills item 220's own separating state for the two
   `pendingMapValue` rows: the state is at column 0, and the field says the
   park is not. -/
#guard pMapValue Tests.Guards.DeclineArmLattice.sepMapValueContent &&
       !pMapValueT Tests.Guards.DeclineArmLattice.sepMapValueContent

/- And the corner's separating state is still a separating state — the corner
   is closed by the PRODUCER, not by tightening the reading. -/
#guard pFlowPark Tests.Guards.DeclineArmLattice.sepFlowParkContentish &&
       !pContentish Tests.Guards.DeclineArmLattice.sepFlowParkContentish

end Tests.Guards.DeclineArmInvariants
