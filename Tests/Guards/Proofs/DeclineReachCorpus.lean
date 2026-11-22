import Tests.DeclineReachCensus
import L4YAML.Proofs.Production.StreamAccum

/-!
# The DECLINE-REACH census is SOUND at the park layer (item 219)

`Tests/DeclineReachCensus.lean` decides, at every state the scan visits, which
`PendingNode` constructor could be covering it.  Every row of both its censuses
rests on those decisions, so the decisions are claims about what Lean does and
§1 says a claim about what Lean does is written as something the compiler
checks.

This module checks them.  Each lemma below takes exactly the fields of one
constructor that mention `sc` (plus `ScannerSurfCorr.col_eq`, which is what
turns a `sp_scan.col` field into a statement about `sc.col`) and proves the
census's `Bool` predicate true — so a state at which the predicate is FALSE
cannot be carrying that park, and a census row reading zero is a statement about
the park and not about the predicate.

**Seven of the nine bridge; two do not, and the two name an asymmetry.**

* `pendingDocEnd` carries its marker as the surface-grammar field
  `h_marker : SCDocumentEnd sp_block sp_scan`, and nothing in the library takes
  that to the token array.  `pendingDocStart` carries the token-level witness as
  a field of its own (`h_marker_tail : ∃ t, lastRealToken? sc.tokens = some t ∧
  t.val = .documentStart ∧ t.pos.line = sc.line`) and bridges below.  So the
  census's `pDocEnd` marker conjunct is a READING; its four companions are
  proved (`bridge_pendingDocEnd_weak`).
* `pendingProps`'s run conjunct needs `PropsRun n c ha ht sp_p sp_scan →
  ha = true ∨ ht = true`, which the library does not state; `h_anchor` and
  `h_tag` are each conditional on their own flag.  The other four fields are
  proved (`bridge_pendingProps_weak`).

Neither gap touches this item's finding, because that finding is a COMPARISON of
one predicate across two domains — `pDocEnd` at a block dispatch reads 0 over the
402 corpus leaves and 1 633 over the 50 653 enumerated programs — and a
comparison under a fixed predicate is insensitive to whether the predicate is
necessary.
-/

namespace Tests.Guards.DeclineReachCorpus

set_option autoImplicit false

open L4YAML L4YAML.Surface L4YAML.Scanner
open L4YAML.Proofs.StreamAccum L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.FlowAdjacency
open Tests.DeclineReachCensus

variable {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}

/-- `noPending`'s four `sc` fields. -/
lemma bridge_noPending
    (hc : ScannerSurfCorr sc sp_scan)
    (h_col : sp_scan.col = 0 ∨ sc.inFlow = true)
    (h_arm : sc.simpleKeyAllowed = true ∨ sc.inFlow = true)
    (h_noek : sc.inFlow = false → sc.explicitKeyLine = none)
    (h_ntop : sc.inFlow = false → sc.currentIndent < 0) :
    pNoPending sc = true := by
  have hcol := hc.col_eq
  unfold pNoPending
  cases hf : sc.inFlow with
  | true => simp
  | false =>
    have h1 : sc.col = 0 := by
      rcases h_col with h | h
      · omega
      · simp [hf] at h
    have h2 : sc.simpleKeyAllowed = true := by
      rcases h_arm with h | h
      · exact h
      · simp [hf] at h
    simp [h1, h2, h_noek hf, h_ntop hf]

/-- `pendingContent`'s and `pendingBlockContent`'s three `sc` fields — the two
    constructors carry the same ones, which is why the census cannot separate
    their rows. -/
lemma bridge_contentish
    (hc : ScannerSurfCorr sc sp_scan)
    (h_arm : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col)
    (h_nodir : sc.allowDirectives = false)
    (h_nic0 : sp_scan.col = 0 → sc.needIndentCheck = true) :
    pContentish sc = true := by
  have hcol := hc.col_eq
  unfold pContentish
  rcases h_arm with ⟨ha, hp⟩ | hlt
  · by_cases h0 : sc.col = 0
    · simp [ha, hp, h_nodir, h0, h_nic0 (by omega)]
    · simp [ha, hp, h_nodir, h0]
  · have hpos : 0 < sc.col := by omega
    have hne0 : ¬ sc.col = 0 := by omega
    simp [h_nodir, hne0, hpos]

/-- `pendingFlow`'s three `sc` fields — β.5's escape park, and item 77's comment
    already says these are "the ONE scanner fact every park has". -/
lemma bridge_pendingFlow
    (hc : ScannerSurfCorr sc sp_scan)
    (h_arm : sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col)
    (h_nodir : sc.allowDirectives = false)
    (h_nic0 : sp_scan.col = 0 → sc.needIndentCheck = true) :
    pFlowPark sc = true := by
  have hcol := hc.col_eq
  unfold pFlowPark
  rcases h_arm with ha | hlt
  · by_cases h0 : sc.col = 0
    · simp [ha, h_nodir, h0, h_nic0 (by omega)]
    · simp [ha, h_nodir, h0]
  · have hpos : 0 < sc.col := by omega
    have hne0 : ¬ sc.col = 0 := by omega
    simp [h_nodir, hne0, hpos]

/-- `pendingBlock`'s five `sc` fields, including the park's own column and the
    stack top item 204 added. -/
lemma bridge_pendingBlock {n : Nat}
    (hc : ScannerSurfCorr sc sp_scan)
    (h_floor : IndentFloor sc (n + 1))
    (h_sk : sc.simpleKeyAllowed = true)
    (h_col : sp_scan.col = n + 1)
    (h_nodir : sc.allowDirectives = false)
    (h_park_top : sc.currentIndent ≤ (n : Int)) :
    pBlock sc = true := by
  have hcol := hc.col_eq
  have hn : sc.col = n + 1 := by omega
  obtain ⟨hnic, hle⟩ := h_floor
  have h1 : 1 ≤ sc.col := by omega
  have h2 : sc.col ≤ (max 0 (sc.currentIndent + 1)).toNat := by
    have := hle
    simp only [minContentIndentOf] at this
    omega
  have h3 : sc.currentIndent ≤ ((sc.col - 1 : Nat) : Int) := by
    have : sc.col - 1 = n := by omega
    rw [this]; exact h_park_top
  simp [pBlock, floorB, h_sk, h_nodir, hnic, h1, h2, h3]

/-- `pendingMapValue`'s four `sc` fields. -/
lemma bridge_pendingMapValue
    (h_nic : sc.needIndentCheck = false)
    (h_real : LastTokenReal sc.tokens)
    (h_sk : sc.simpleKeyAllowed = true)
    (h_nodir : sc.allowDirectives = false) :
    pMapValue sc = true := by
  obtain ⟨hsz, hne⟩ := h_real
  simp [pMapValue, lastRealB, h_nic, h_sk, h_nodir, hsz, hne]

/-- `pendingDocStart`'s six `sc` fields, the token-level marker among them. -/
lemma bridge_pendingDocStart
    (hc : ScannerSurfCorr sc sp_scan)
    (h_nic : sc.needIndentCheck = false)
    (h_real : LastTokenReal sc.tokens)
    (h_marker_tail : ∃ t, lastRealToken? sc.tokens = some t ∧
      t.val = .documentStart ∧ t.pos.line = sc.line)
    (h_arm : sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col)
    (h_nodir : sc.allowDirectives = false)
    (h_nic0 : sp_scan.col = 0 → sc.needIndentCheck = true) :
    pDocStart sc = true := by
  have hcol := hc.col_eq
  obtain ⟨hsz, hne⟩ := h_real
  obtain ⟨t, ht, htv, htl⟩ := h_marker_tail
  have harm : sc.simpleKeyAllowed = true ∨ 0 < sc.col := by
    rcases h_arm with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  unfold pDocStart
  by_cases h0 : sc.col = 0
  · have hnic := h_nic0 (by omega)
    rw [h_nic] at hnic
    exact absurd hnic (by simp)
  · rcases harm with h | h <;>
      simp [lastRealB, h_nic, h_nodir, hsz, hne, ht, htv, htl, h, h0]

/-- `pendingDocEnd`, WITHOUT the marker conjunct: the two fields that do bridge.
    The census's `pDocEnd` is this conjoined with a token-level reading of
    `h_marker : SCDocumentEnd sp_block sp_scan`, which the library does not
    carry — see this module's header. -/
lemma bridge_pendingDocEnd_weak
    (hc : ScannerSurfCorr sc sp_scan)
    (h_arm : sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col)
    (h_nic0 : sp_scan.col = 0 → sc.needIndentCheck = true) :
    ((sc.simpleKeyAllowed || 0 < sc.col) && (sc.col != 0 || sc.needIndentCheck)) = true := by
  have hcol := hc.col_eq
  rcases h_arm with ha | hlt
  · by_cases h0 : sc.col = 0
    · simp [ha, h0, h_nic0 (by omega)]
    · simp [ha, h0]
  · have hpos : 0 < sc.col := by omega
    have hne0 : ¬ sc.col = 0 := by omega
    simp [hne0, hpos]

/-- `pendingProps`, WITHOUT the run conjunct: the four fields that do bridge. -/
lemma bridge_pendingProps_weak
    (h_nic : sc.needIndentCheck = false)
    (h_real : LastTokenReal sc.tokens)
    (h_ska : sc.simpleKeyAllowed = false)
    (h_nodir : sc.allowDirectives = false) :
    (!sc.needIndentCheck && lastRealB sc.tokens && !sc.simpleKeyAllowed &&
      !sc.allowDirectives) = true := by
  obtain ⟨hsz, hne⟩ := h_real
  simp [lastRealB, h_nic, h_ska, h_nodir, hsz, hne]

end Tests.Guards.DeclineReachCorpus
