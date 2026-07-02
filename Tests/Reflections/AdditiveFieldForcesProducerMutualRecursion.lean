/-!
# Reflection 450 — an ADDITIVE recursive field is trivial at the TYPE level, but its PRODUCER can force
# a MUTUAL recursion the existing acyclic producer-citation DAG forbids.  Before pricing "additive field
# = cheap" (R449), trace the producer CITATION graph for the new field: if the field's recursive
# assembler must be fed by a SIBLING producer that ALREADY cites the producer you are editing, supplying
# the field closes a citation cycle (#1 ↔ #2) that Lean rejects outside a `mutual` block.  The type edit
# is a DECOY; the real cost is restructuring the two producers into a mutual recursion on the data tree.

Self-contained (core Lean, no `L4YAML` import) toy of the R450 finding — the STEP D producer-side probe.

Context (sharpens R449).  R449 found the seq root carrier's domain `SeqTypedInterior` (path-blind) is a
LADDER of map-nested-seq severances, closable only by storing a RECURSIVE `RecMapBody` at the foreign
constructor `RecSeqEntry.map` (today it stores a flat `WellBracketed`).  R449's route note read "additive
field likely wins — the producer already builds the `RecMapBody` at one level; the gap is only that
`RecSeqEntry.map` discards it."  R450 reads the producers and finds the second clause is the trap: the
TYPE field is one line, but SUPPLYING it forces a producer mutual recursion the codebase has carefully
avoided.

The real producer graph (three theorems, `NonemptyStructure.lean`):

* **#1 `emit_scans_in_flow_rec_entry`** (the VALUE producer): `.seq` arm feeds the recursive seq-body
  producer from its OWN IH and stores `RecSeqEntry.seq … h_rec`; `.map` arm feeds the FLAT pair scan and
  stores `RecSeqEntry.map … h_wb` only (`:3057`, the severance).
* **#2 `emit_scans_in_flow_saved_key_rec_entry`** (the SAVED-KEY producer): its `.seq` value bodies are
  fed by **#1** (`:3233`) — so **#2 → #1** is an existing citation; `.map` arm also stores only `h_wb`
  (`:3509`, the second severance site).
* **#3 `emitPairList_scans_recmapbody`** (the map-body ASSEMBLER): already delivers a full `RecMapBody`
  (a superset of the flat pair producer), but as a hypothesis-parametrized LEAF — it inducts on `pairs`
  and takes `h_all_k : … EmitScansInFlowSavedKeyRecEntry` / `h_all_v : … EmitScansInFlowRecEntry` as
  HYPOTHESES, citing neither #1 nor #2.

To store the additive `h_rec : RecMapBody interior`, BOTH map arms (#1@`:3057`, #2@`:3509`) must call #3,
discharging its per-key hypothesis from #2 and its per-value hypothesis from #1.  So #1 must cite #2.
But #2 already cites #1.  **#1 ↔ #2 is a citation cycle** — Lean forbids mutually-recursive `theorem`s
outside a `mutual` block.  The data-level mutual recursion already exists (`RecSeqEntry` ↔ `RecMapBody`)
and the assembler already exists; the missing piece is purely the PRODUCERS' termination structure: #1
and #2 must become a `mutual theorem` block, structurally recursive on the `emit`/`YamlValue` tree —
exactly where Reflection 234's `mutual`-block gotchas live.  #3 stays out (a leaf).

The reusable rule.  An additive recursive field is cheap at the TYPE level but may force a producer
mutual recursion the existing acyclic citation DAG forbids.  Before pricing it, trace the field's
producer citation graph: if the recursive assembler that builds the field must be fed by a sibling
producer that already cites the producer you are editing, the field closes a cycle (#1 ↔ #2) requiring a
`mutual` block.  The tell: the DATA types already mutually reference each other and the ASSEMBLER already
exists as a parametrized leaf, yet the PRODUCERS discharging its hypotheses form a one-directional DAG
(#2 → #1) the new field would close.

This toy has two parts:

* PART 1 (the citation cycle — the rigorous core): the producer graph as a `Bool` edge relation.
  `currentGraph` (only #2 → #1) is ACYCLIC; `closedGraph` (adds #1 → #2 for the new field) has a CYCLE
  #1 → #2 → #1.  Decided by a 3-step transitive closure over the three nodes.
* PART 2 (the resolution): #1 and #2 as a `mutual` recursion on a toy value tree — it compiles and
  terminates structurally; the assembler #3 stays a SEPARATE non-recursive leaf.  A depth-2 value
  (`[{a:{x:[b]}}]`-shaped) evaluates through both map levels, the producer-side analog of the Guards
  probe's two `map_move_trichotomy` DESCEND-VALUE steps.

All sorry-free; axiom footprint `[propext]` only.
-/

set_option autoImplicit false

namespace Tests.Reflections.AdditiveFieldForcesProducerMutualRecursion

/-! ## PART 1 — the producer CITATION graph: acyclic today, cyclic once the additive field is supplied. -/

/-- The three emit producers (`NonemptyStructure.lean`). -/
inductive PNode where
  | pValue      -- #1  emit_scans_in_flow_rec_entry            (value producer)
  | pSavedKey   -- #2  emit_scans_in_flow_saved_key_rec_entry  (saved-key producer)
  | pMapBody    -- #3  emitPairList_scans_recmapbody           (map-body assembler, a parametrized leaf)
deriving DecidableEq

open PNode

/-- All producers — the node set for the transitive-closure computation. -/
def allP : List PNode := [pValue, pSavedKey, pMapBody]

/-- A citation graph: `g a b = true` iff theorem `a`'s proof cites theorem `b`. -/
abbrev Graph := PNode → PNode → Bool

/-- One transitive-closure step: `b` reachable in `r`, or `a` cites some `m` reaching `b`. -/
def stepG (g r : Graph) : Graph :=
  fun a b => r a b || allP.any (fun m => r a m && g m b)

/-- Transitive closure over three nodes stabilises in ≤ 3 iterations. -/
def reachB (g : Graph) : Graph := stepG g (stepG g (stepG g g))

/-- A graph is acyclic iff no node reaches ITSELF. -/
def acyclic (g : Graph) : Bool := allP.all (fun n => ! reachB g n n)

/-- **The CURRENT producer graph.**  #2's saved-key seq-value bodies are fed by #1
    (`NonemptyStructure.lean:3233`) — the single cross edge.  #1 and #2 use the FLAT pair scan at their
    map arms, so neither cites the assembler #3; #3 is a hypothesis-parametrized leaf citing no one. -/
def currentGraph : Graph
  | pSavedKey, pValue => true   -- #2 → #1  (existing: saved-key's seq values fed by the value producer)
  | _,         _      => false

/-- **The graph after supplying the additive `h_rec` field.**  Both map arms now call the assembler #3,
    whose per-key hypothesis is discharged from #2 — so #1 gains an edge to #2 (#1 → #2).  The existing
    #2 → #1 remains.  (#3 stays a leaf: it cites no one, taking #1/#2's outputs as hypotheses.) -/
def closedGraph : Graph
  | pSavedKey, pValue    => true   -- #2 → #1  (existing)
  | pValue,    pSavedKey => true   -- #1 → #2  (NEW: #1's map arm needs the saved-key recursive deliverable)
  | _,         _         => false

/-- **The current producer graph is ACYCLIC** — #1 and #2 can be separate `theorem`s, as they are. -/
theorem current_acyclic : acyclic currentGraph = true := by decide

/-- **Supplying the additive field makes the graph CYCLIC** — #1 → #2 → #1, so #1 and #2 can no longer
    be separate `theorem`s: they must share a `mutual` block.  This is the real cost of the field. -/
theorem closed_has_cycle : acyclic closedGraph = false := by decide

/-- The cycle exhibited concretely: #1 reaches itself through #2. -/
theorem value_reaches_itself : reachB closedGraph pValue pValue = true := by decide

/-! ## PART 2 — the resolution: #1 and #2 as a MUTUAL recursion; the assembler #3 stays a separate leaf. -/

/-- A toy `emit` value tree (binary, so structural recursion is immediate — the real tree branches via
    `List`, where the equation compiler needs `attach`/`termination_by`, the R234 gotcha the real
    refactor will meet).  `.map k v` is one key/value pair. -/
inductive V where
  | scalar
  | seq (body : V)              -- a sequence wrapping its body
  | map (key : V) (value : V)   -- a mapping pair: key and value sub-values
deriving Repr

/-- **#3 the map-body assembler — a LEAF outside the mutual block.**  It combines the PRECOMPUTED
    per-pair key/value results (modelling `emitPairList_scans_recmapbody`'s `h_all_k`/`h_all_v`
    HYPOTHESES); it does NOT call the producers, so it stays a plain non-recursive `def`. -/
def pMapPair (kResult vResult : Nat) : Nat := kResult + vResult

/- #1 (value) and #2 (saved-key) as a MUTUAL recursion — the resolution the additive field forces.
   #1's `.map` arm cites #2 (the key), #2's `.seq` arm cites #1 (the body): the cycle PART 1 proved,
   here legal because they share one structural recursion on `V`.  (Plain `/- -/`, not `/-- -/`: a doc
   comment cannot attach to a `mutual` keyword — the Reflection 234 gotcha.) -/
mutual
  /-- #1 the VALUE producer: `.seq` body fed by #1; `.map` key fed by #2, value by #1, combined by #3. -/
  def pValue : V → Nat
    | .scalar    => 1
    | .seq b     => 1 + pValue b                              -- #1 → #1
    | .map k v   => 1 + pMapPair (pSavedKey k) (pValue v)     -- #1 → #2 (key), #1 → #1 (value), then #3
  /-- #2 the SAVED-KEY producer: `.seq` body fed by #1 (the existing #2 → #1 edge). -/
  def pSavedKey : V → Nat
    | .scalar    => 1
    | .seq b     => 1 + pValue b                              -- #2 → #1  (NonemptyStructure.lean:3233)
    | .map k v   => 1 + pMapPair (pSavedKey k) (pValue v)     -- #2 → #2 (key), #2 → #1 (value), then #3
end

/-- The mutual producers genuinely cross-reference: a single `.map` invokes BOTH (key via #2, value via
    #1).  `{scalar: scalar}` ⇒ `1 + (pSavedKey .scalar + pValue .scalar) = 1 + (1 + 1) = 3`. -/
theorem mutual_cross_reference : pValue (.map .scalar .scalar) = 3 := rfl

/-- **The mutual recursion descends to ANY map-nesting depth.**  The depth-2 value `[{a:{x:[b]}}]`
    (`.seq (.map .scalar (.map .scalar (.seq .scalar)))`) evaluates through BOTH map levels down to the
    innermost scalar — the producer-side analog of the Guards probe's two `map_move_trichotomy`
    DESCEND-VALUE steps reaching the inner `[b]`.  Node count = 7. -/
theorem depth_two_reaches_innermost :
    pValue (.seq (.map .scalar (.map .scalar (.seq .scalar)))) = 7 := rfl

#guard pValue (.seq (.map .scalar (.map .scalar (.seq .scalar)))) == 7

/-- The finding in one proposition: (PART 1) the additive field turns the acyclic producer graph cyclic
    (#1 ↔ #2), forbidding separate `theorem`s; (PART 2) the resolution is a `mutual` recursion that
    descends any depth, with the assembler #3 a separate leaf. -/
theorem r450_finding :
    (acyclic currentGraph = true)                               -- separate theorems OK today
    ∧ (acyclic closedGraph = false)                             -- the additive field closes a cycle
    ∧ (reachB closedGraph PNode.pValue PNode.pValue = true)     -- the cycle is #1 → #2 → #1
    ∧ (pValue (.map .scalar .scalar) = 3)                       -- the mutual recursion cross-references
    ∧ (pValue (.seq (.map .scalar (.map .scalar (.seq .scalar)))) = 7) := -- and descends any depth
  ⟨by decide, by decide, by decide, rfl, rfl⟩

end Tests.Reflections.AdditiveFieldForcesProducerMutualRecursion
