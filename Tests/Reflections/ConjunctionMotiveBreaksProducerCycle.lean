/-!
# Reflection 451 — when two mutually-citing producers recurse on the SAME inductive, the cycle is broken
# by a CONJUNCTION-MOTIVE single induction, NOT a `mutual theorem` block.  The mutual recursion stays in
# the DATA; the PRODUCER collapses to one ordinary theorem whose shared IH carries BOTH deliverables.

Self-contained (core Lean, no `L4YAML` import) toy of the R451 finding — the de-risk for R450's STEP D.

Context (corrects R450's resolution).  R450 found that supplying an additive recursive field forces the
value producer #1 and the saved-key producer #2 into a citation cycle (#1 ↔ #2): #2 already cites #1, and
the new field makes #1 cite #2.  R450's Blueprint Next step proposed resolving this by restructuring #1 and
#2 into a `mutual theorem` block — dragging in the Reflection-234 `mutual`-block gotchas (doc-comment-on-
`mutual`, the `induction` tactic inside a mutual theorem, `Or`-nesting in the deliverable).

R451 finds a strictly simpler resolution and validates it on the REAL `Grammable`/`YamlValue` recursor
(`Tests/Guards/Proofs/MapProducerMutualResolutionProbe.lean`).  The key observation: #1 and #2 BOTH recurse
on the SAME inductive (`Grammable v inFlow`, structurally recursive on `YamlValue`).  A mutual block of
THEOREMS is only forced when the two recurse on DIFFERENT data.  When they recurse on the SAME data, prove
the CONJUNCTION of their deliverables by ONE induction; the single shared induction hypothesis carries BOTH
deliverables at every sub-value, so each arm reads off the component it needs (`.1`/`.2`) instead of citing
the sibling theorem.  The mutual recursion lives where it already does — in the DATA (`EValue` ↔ `ESkey`
here; `RecSeqEntry` ↔ `RecMapBody` in the real types) — and the PRODUCER is one ordinary theorem.

This toy reproduces the exact cross-citation pattern on a `List`-nested tree (closer to the real
`∀ i : Fin _.size` array nesting than R450's binary tree):

* `Good` mirrors `Grammable`: a `.node` (sequence) carries `Good` on each kid; a `.pairs` (mapping) carries
  `Good` on each key and value.
* `P` mirrors the value deliverable #1; `Q` mirrors the saved-key deliverable #2.  Their constructors encode
  the cross-edges: `P.pairs`/`Q.pairs` take `Q` on keys and `P` on values; `Q.node` takes `P` on kids (the
  #2 → #1 edge).  `P` and `Q` reference each other — a MUTUAL INDUCTIVE — exactly the data-level mutual
  reference the real types already have.

`good_gives_both` proves `P t ∧ Q t` by ONE `induction h`, feeding every cross-edge from the conjunction IH.
No `mutual theorem`, no `Or`-nesting, no `induction`-inside-`mutual`.  `producer_is_one_theorem` packages the
finding; the two projections `good_gives_value`/`good_gives_savedkey` are the thin `.1`/`.2` wrappers the
real refactor exposes so #1/#2's signatures (and all their consumers) stay unchanged.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.ConjunctionMotiveBreaksProducerCycle

/-- A toy value tree with `List`-nested children — `.node` is sequence-like (a list of kids), `.pairs` is
    mapping-like (a list of key/value pairs).  Mirrors `YamlValue`'s `Array`-nested recursion. -/
inductive Tree where
  | leaf
  | node (kids : List Tree)
  | pairs (ps : List (Tree × Tree))

/-- `Good` mirrors `Grammable`: structurally recursive on `Tree`, carrying a `Good` witness on every child
    under `∀ i : Fin _.length` (the list analogue of `Grammable`'s `∀ i : Fin _.size`). -/
inductive Good : Tree → Prop where
  | leaf : Good .leaf
  | node (kids : List Tree) (h : ∀ i : Fin kids.length, Good kids[i]) : Good (.node kids)
  | pairs (ps : List (Tree × Tree))
      (hk : ∀ i : Fin ps.length, Good ps[i].1)
      (hv : ∀ i : Fin ps.length, Good ps[i].2) : Good (.pairs ps)

/- The two mirror deliverables as a MUTUAL INDUCTIVE — the data-level mutual reference (`P` ↔ `Q`) that the
   real types already have (`RecSeqEntry` ↔ `RecMapBody`).  The cross-edges:
   * `P.pairs` / `Q.pairs` take `Q` on the keys and `P` on the values;
   * `Q.node` takes `P` on the kids (the existing #2 → #1 edge).
   Plain `/- -/`, not `/-- -/`: a doc comment cannot attach to `mutual` (the Reflection-234 gotcha). -/
mutual
  /-- `P` mirrors the VALUE deliverable #1 (`EmitScansInFlowRecEntry`). -/
  inductive P : Tree → Prop where
    | leaf : P .leaf
    | node (kids : List Tree) (h : ∀ i : Fin kids.length, P kids[i]) : P (.node kids)
    | pairs (ps : List (Tree × Tree))
        (hk : ∀ i : Fin ps.length, Q ps[i].1)   -- keys need the SAVED-KEY deliverable
        (hv : ∀ i : Fin ps.length, P ps[i].2) : P (.pairs ps)   -- values need the VALUE deliverable
  /-- `Q` mirrors the SAVED-KEY deliverable #2 (`EmitScansInFlowSavedKeyRecEntry`). -/
  inductive Q : Tree → Prop where
    | leaf : Q .leaf
    | node (kids : List Tree) (h : ∀ i : Fin kids.length, P kids[i]) : Q (.node kids)  -- #2 → #1 edge
    | pairs (ps : List (Tree × Tree))
        (hk : ∀ i : Fin ps.length, Q ps[i].1)
        (hv : ∀ i : Fin ps.length, P ps[i].2) : Q (.pairs ps)
end

/-- **THE RESOLUTION.**  ONE `induction h` with the CONJUNCTION motive `P t ∧ Q t` delivers both mirror
    deliverables; every cross-edge is read off the conjunction IH (`.1`/`.2`), never a sibling theorem.  No
    `mutual theorem` block.  This is the shape the real #1/#2 producer refactor takes. -/
theorem good_gives_both (t : Tree) (h : Good t) : P t ∧ Q t := by
  induction h with
  | leaf => exact ⟨.leaf, .leaf⟩
  | node kids _ ih =>
      -- ih i : P kids[i] ∧ Q kids[i].  Both `.node` arms take `P` on kids — the `Q.node` arm is the
      -- #2 → #1 edge, served from the SAME IH's `.1`, no sibling call.
      exact ⟨.node kids (fun i => (ih i).1), .node kids (fun i => (ih i).1)⟩
  | pairs ps _ _ ihk ihv =>
      -- ihk i : P ps[i].1 ∧ Q ps[i].1   (key, BOTH deliverables)
      -- ihv i : P ps[i].2 ∧ Q ps[i].2   (value, BOTH deliverables)
      -- The arms need SAVED-KEY on keys (`.2`) and VALUE on values (`.1`) — the cross pattern that forces
      -- #1 → #2 today; here both come off the one conjunction IH.
      exact ⟨.pairs ps (fun i => (ihk i).2) (fun i => (ihv i).1),
             .pairs ps (fun i => (ihk i).2) (fun i => (ihv i).1)⟩

/-- The two projections the consumers see — the real #1/#2 become thin `.1`/`.2` wrappers, signatures
    (and all consumers) unchanged. -/
theorem good_gives_value (t : Tree) (h : Good t) : P t := (good_gives_both t h).1
theorem good_gives_savedkey (t : Tree) (h : Good t) : Q t := (good_gives_both t h).2

/-- The finding in one proposition: the cycle resolves to ONE theorem (not a mutual block) whose shared IH
    serves both deliverables, including the depth-2 nesting `[{leaf : {leaf : [leaf]}}]`-shaped tree. -/
theorem producer_is_one_theorem :
    (∀ t, Good t → P t ∧ Q t)                                   -- one theorem, both deliverables
    ∧ (∀ t, Good t → P t)                                       -- #1 is a thin projection
    ∧ (∀ t, Good t → Q t) :=                                    -- #2 is a thin projection
  ⟨good_gives_both, good_gives_value, good_gives_savedkey⟩

/-- A depth-2 witness — `.node [.pairs [(leaf, .pairs [(leaf, .node [leaf])])]]`, the toy analogue of
    `[{a:{x:[b]}}]` — is `Good`, so `good_gives_both` descends BOTH `pairs` levels.  Built bottom-up; each
    `∀ i : Fin _.length` discharged by `Fin.elim0` / single-element case. -/
example : Good (.node [.pairs [(.leaf, .pairs [(.leaf, .node [.leaf])])]]) := by
  refine .node _ (fun i => ?_)
  match i with
  | ⟨0, _⟩ =>
      refine .pairs _ (fun j => ?_) (fun j => ?_)
      · match j with | ⟨0, _⟩ => exact .leaf
      · match j with
        | ⟨0, _⟩ =>
            refine .pairs _ (fun k => ?_) (fun k => ?_)
            · match k with | ⟨0, _⟩ => exact .leaf
            · match k with | ⟨0, _⟩ => exact .node _ (fun m => match m with | ⟨0, _⟩ => .leaf)

end Tests.Reflections.ConjunctionMotiveBreaksProducerCycle
