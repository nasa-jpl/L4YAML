/-!
# Reflection 452 — executing a conjunction-motive producer merge is a MECHANICAL ZIP whose edit count is
# the number of per-child WITNESS-CONSUMPTION sites (own-IH uses + sibling citations), NOT the body size.

Self-contained (core Lean, no `L4YAML` import) toy of the R452 finding — the EXECUTION of R451's de-risk.

Context.  R451 ([[ref-conjunction-motive-breaks-producer-cycle]]) de-risked, on a toy, that two producers
sharing a recursion merge into ONE conjunction-motive theorem (no `mutual theorem` block).  R452 EXECUTED
that merge on the REAL ~760-line producers `emit_scans_in_flow_rec_entry` (#1, value) +
`emit_scans_in_flow_saved_key_rec_entry` (#2, saved-key) → `emit_scans_in_flow_rec_entry_both`, and the
execution revealed the COST law:

  **The merge is a mechanical zip.  Its semantic edit count equals the number of per-child
  DELIVERABLE-WITNESS consumption sites across both bodies — each rewritten to one `(ih …).i` projection of
  the conjunction IH.  The entire rest of both bodies (every `have`/`obtain`/`refine`, all the scanner
  machinery) transports VERBATIM under the two conjunct bullets (a constant indentation shift).**

So a 760-line merge cost exactly TWO edits, because only the two `sequence` arms consume a per-child
witness (the `mapping` and `scalar` arms feed off flat black-box wrappers / are leaves — inert w.r.t. the
IH).  Body bulk is a red herring; before committing to such a merge, COUNT the witness sites (own-IH uses +
sibling citations) — that is the real edit count and the whole risk surface.

This toy mirrors the real arm taxonomy precisely:

* `leaf`  — the `scalar` arm: a leaf, consumes no witness → INERT, transports verbatim.
* `node`  — the `sequence` arm: consumes one per-child witness.  In #1 it is the OWN IH (`ih i`); in #2 it
  is the by-name sibling citation `mkV` (the #2 → #1 cross-edge).  BOTH become `(ih i).1` in the merge.
* `pairs` — the `mapping` arm: produces its deliverable from a flat black box (`FlatOk`, modelling
  `emit_scans_in_flow_block`'s flat facts and the `RecSeqEntry.map` severance that stores only a flat
  witness), consuming NO IH and NOT citing the sibling → INERT, transports verbatim.

`mkV`/`mkK` are the separate "before" producers (acyclic: `mkK` cites `mkV`, never the reverse).  `mkVK` is
the merged "after" — ONE `induction g`, the two `node` witness sites projected, the `leaf`/`pairs` arms
paired verbatim.  `mkV'`/`mkK'` are the thin `.1`/`.2` re-expositions (the real #1/#2 keep their signatures
and all consumers).  `merge_cost_is_two_witness_sites` packages the law.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.ConjunctionMergeCostIsCitationEdges

/-- Toy value tree: `leaf` (scalar-like), `node` (sequence-like, `List`-nested kids), `pairs`
    (mapping-like, `List`-nested key/value pairs).  Mirrors `YamlValue`. -/
inductive Tree where
  | leaf
  | node (kids : List Tree)
  | pairs (ps : List (Tree × Tree))

/-- `Good` mirrors `Grammable`: a `Good` witness on every child under `∀ i : Fin _.length`. -/
inductive Good : Tree → Prop where
  | leaf : Good .leaf
  | node (kids : List Tree) (h : ∀ i : Fin kids.length, Good kids[i]) : Good (.node kids)
  | pairs (ps : List (Tree × Tree))
      (hk : ∀ i : Fin ps.length, Good ps[i].1)
      (hv : ∀ i : Fin ps.length, Good ps[i].2) : Good (.pairs ps)

/-- A flat black-box predicate over a pair list — the toy analogue of the FLAT facts the real `mapping`
    arm reads off `emit_scans_in_flow_block` / `emit_scans_in_flow_saved_key_block`, and of the
    `RecSeqEntry.map` severance that stores only a flat `WellBracketed` witness (no recursive child
    witness).  Trivially inhabited, so the `pairs` arm needs NO induction hypothesis. -/
def FlatOk (_ : List (Tree × Tree)) : Prop := True

/- The two deliverables as a MUTUAL INDUCTIVE — the data-level mutual reference (`V` ↔ `K`) the real types
   already have (`RecSeqEntry` ↔ `RecMapBody`).  `K.node` takes `V` on its kids — the #2 → #1 cross-edge.
   Both `pairs` constructors store only the flat `FlatOk` (the severance — no recursive child witness).
   Plain `/- -/`, not `/-- -/`: a doc comment cannot attach to `mutual` (the Reflection-234 gotcha). -/
mutual
  /-- `V` mirrors the VALUE deliverable #1 (`EmitScansInFlowRecEntry`). -/
  inductive V : Tree → Prop where
    | leaf : V .leaf
    | node (kids : List Tree) (h : ∀ i : Fin kids.length, V kids[i]) : V (.node kids)
    | pairs (ps : List (Tree × Tree)) (flat : FlatOk ps) : V (.pairs ps)   -- severance: flat only
  /-- `K` mirrors the SAVED-KEY deliverable #2 (`EmitScansInFlowSavedKeyRecEntry`). -/
  inductive K : Tree → Prop where
    | leaf : K .leaf
    | node (kids : List Tree) (h : ∀ i : Fin kids.length, V kids[i]) : K (.node kids)  -- #2 → #1 edge
    | pairs (ps : List (Tree × Tree)) (flat : FlatOk ps) : K (.pairs ps)   -- severance: flat only
end

/-! ### The "before": two separate producers, acyclic (`mkK` → `mkV`, never the reverse). -/

/-- #1 value producer.  Its `node` arm consumes its OWN IH (`ih i`) — ONE witness site.  `leaf` is a leaf,
    `pairs` reads the flat black box — both inert (no IH). -/
theorem mkV (t : Tree) (g : Good t) : V t := by
  induction g with
  | leaf => exact .leaf
  | node kids _ ih => exact .node kids (fun i => ih i)        -- witness site: OWN IH
  | pairs ps _ _ _ _ => exact .pairs ps trivial               -- inert: flat black box

/-- #2 saved-key producer.  Its `node` arm cites the sibling `mkV` BY NAME — the #2 → #1 cross-edge, ONE
    witness site.  `leaf`/`pairs` inert, exactly as #1. -/
theorem mkK (t : Tree) (g : Good t) : K t := by
  induction g with
  | leaf => exact .leaf
  | node kids h _ => exact .node kids (fun i => mkV _ (h i))  -- witness site: SIBLING citation (cross-edge)
  | pairs ps _ _ _ _ => exact .pairs ps trivial               -- inert: flat black box

/-! ### The "after": ONE conjunction-motive theorem.  The merge edited EXACTLY the two `node` witness
    sites (`ih i` and `mkV _ (h i)`) into `(ih i).1`; the `leaf` and `pairs` arms are PAIRED VERBATIM. -/

/-- **THE MERGE.**  ONE `induction g` with the conjunction motive `V t ∧ K t`.  The shared IH carries BOTH
    deliverables at every child, so each `node` arm reads `(ih i).1` off it — the value-producer self-IH and
    the saved-key by-name citation collapse to the SAME projection, no sibling call.  Edit count = 2 (the
    two `node` witness sites); the `leaf`/`pairs` arms transport verbatim.  This is the shape the real
    `emit_scans_in_flow_rec_entry_both` takes — 760 lines, 2 edits. -/
theorem mkVK (t : Tree) (g : Good t) : V t ∧ K t := by
  induction g with
  | leaf => exact ⟨.leaf, .leaf⟩
  | node kids _ ih =>
      -- ih i : V kids[i] ∧ K kids[i].  BOTH node arms need V on kids — #1's own-IH site and #2's cross-edge
      -- citation are now the SAME `(ih i).1`.  TWO witness sites, both projections of the one IH.
      exact ⟨.node kids (fun i => (ih i).1), .node kids (fun i => (ih i).1)⟩
  | pairs ps _ _ _ _ =>
      -- INERT arm: no witness consumed (flat black box), transports verbatim, only paired.
      exact ⟨.pairs ps trivial, .pairs ps trivial⟩

/-- The two projections the consumers see — the real #1/#2 become thin `.1`/`.2` wrappers, signatures
    (and all consumers) unchanged. -/
theorem mkV' (t : Tree) (g : Good t) : V t := (mkVK t g).1
theorem mkK' (t : Tree) (g : Good t) : K t := (mkVK t g).2

/-- **The cost law in one proposition.**  The merge delivers BOTH deliverables from ONE theorem (the two
    thin projections are `.1`/`.2`), and the edit that produced it touched exactly the per-child
    witness-consumption sites — here the two `node` arms — independent of how voluminous the `leaf`/`pairs`
    bodies are. -/
theorem merge_cost_is_two_witness_sites :
    (∀ t, Good t → V t ∧ K t)                                  -- one theorem, both deliverables
    ∧ (∀ t, Good t → V t)                                      -- #1 is a thin `.1` projection
    ∧ (∀ t, Good t → K t) :=                                   -- #2 is a thin `.2` projection
  ⟨mkVK, mkV', mkK'⟩

/-- A depth-2 witness — `.node [.pairs [(leaf, .node [leaf])]]` — is `Good`, so `mkVK` descends BOTH the
    `node` (IH-consuming) and `pairs` (inert) arms.  Built bottom-up; each `∀ i : Fin _.length` discharged
    by the single-element case. -/
example : Good (.node [.pairs [(.leaf, .node [.leaf])]]) := by
  refine .node _ (fun i => ?_)
  match i with
  | ⟨0, _⟩ =>
      refine .pairs _ (fun j => ?_) (fun j => ?_)
      · match j with | ⟨0, _⟩ => exact .leaf
      · match j with | ⟨0, _⟩ => exact .node _ (fun k => match k with | ⟨0, _⟩ => .leaf)

end Tests.Reflections.ConjunctionMergeCostIsCitationEdges
