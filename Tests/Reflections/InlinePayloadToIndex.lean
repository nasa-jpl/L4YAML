module


@[expose] public section Blanket

/-!
# Reflection 610 — inline the payload to index it

A state type that *packages* a payload (`state := wrap (p : Payload l)`) cannot be
indexed by "which payload constructor built it": the payload is a `Prop`, so no
function can read its constructor back out, and no index can be attached to the
wrapper after the fact.  When a guard supplied from outside distinguishes exactly
those constructors, the payload has to be **spread into the outer type** — one
outer constructor per payload shape, each naming its own index.

This is what L4YAML's item 9b(ii) had to do: `SeqFrame`/`MapFrame` wrapped a
`PartialFlowSeq` / `PendingFlowSeqEntry`, and the scanner's two flow guards
(`scanFlowEntry`'s `invalidFlowEntry`, `scanNextToken_checkFlowAdjacency`) reject
exactly certain payload constructors.  Inlining the 7 (resp. 8) shapes into the
frame types let each one carry a `FrameTail` index, which is what turned the
scanner guards into hypotheses the frame transitions could use.

The toy below is the smallest faithful model: three shapes of a
partially-built flow collection, and the `,` transition that is **provable on the
inlined type and outright false on the wrapped one**.

`lake build Tests.Reflections.InlinePayloadToIndex`
-/

namespace InlinePayloadToIndex

/-- Two tokens: a value and the entry separator. -/
inductive Tok where
  | atom
  | comma
  deriving DecidableEq, Repr

/-- The payload: the three shapes a partially-built collection can be in.
    `empty` = nothing since the opening bracket (`[`), `items` = a finished entry,
    `held` = a finished entry plus a trailing `,`. -/
inductive Part : List Tok → Prop where
  | empty : Part []
  | items : Part [Tok.atom]
  | held  : Part [Tok.atom, Tok.comma]

/-- **WRAPPED** — the outer state packages the payload. Which of the three
    constructors built it is not recoverable: `Part` is a `Prop`. -/
inductive Wrapped : List Tok → Prop where
  | mk (l : List Tok) (p : Part l) : Wrapped l

/-- The classification the outside guard distinguishes: `sep` = "the last real
    token was the opener or a separator" (`empty`/`held`), `value` = "a value was
    just completed" (`items`). -/
inductive Tail where
  | sep
  | value
  deriving DecidableEq, Repr

/-- **INLINED** — the same three shapes, spread into the outer type, each naming
    its own tail. Structurally identical content; the difference is entirely in
    what the *type* records. -/
inductive Inlined : Tail → List Tok → Prop where
  | empty : Inlined .sep []
  | items : Inlined .value [Tok.atom]
  | held  : Inlined .sep [Tok.atom, Tok.comma]

/-! ## The two types carry the same inhabitants -/

/-- Forgetting the index is free. -/
theorem inlined_forget {tl : Tail} {l : List Tok} (h : Inlined tl l) : Wrapped l := by
  cases h
  · exact .mk _ .empty
  · exact .mk _ .items
  · exact .mk _ .held

/-- All three shapes are `Wrapped`, so no hypothesis phrased on `Wrapped` can
    separate the good shape from the two degenerate ones. -/
theorem wrapped_conflates :
    Wrapped [] ∧ Wrapped [Tok.atom] ∧ Wrapped [Tok.atom, Tok.comma] :=
  ⟨.mk _ .empty, .mk _ .items, .mk _ .held⟩

/-- The inlined type separates them by index — the same three inhabitants, now
    classified in the type. -/
theorem inlined_separates :
    Inlined .sep [] ∧ Inlined .value [Tok.atom] ∧ Inlined .sep [Tok.atom, Tok.comma] :=
  ⟨.empty, .items, .held⟩

/-! ## The crux: the `,` transition -/

/-- **POSITIVE** — appending `,` to a `.value`-tailed state lands in `.held`.
    The index alone rules out the two degenerate shapes: `cases` never reaches
    them, because their index is `.sep`. -/
theorem hold_inlined {l : List Tok} (h : Inlined .value l) :
    Inlined .sep (l ++ [Tok.comma]) := by
  cases h
  exact .held

/-- **NEGATIVE** — the same transition is FALSE on the wrapped type. The
    degenerate leading-comma shape (`[,`) is in scope and `[Tok.comma]` is not a
    `Part` at all, so there is no way to state the transition, let alone prove
    it, without a classification the wrapper does not carry. -/
theorem hold_wrapped_false :
    ¬ (∀ l : List Tok, Wrapped l → Wrapped (l ++ [Tok.comma])) := by
  intro h
  have hc : Wrapped [Tok.comma] := by simpa using h [] (.mk [] .empty)
  cases hc with
  | mk p => cases p

/-- The consecutive-comma shape (`,,`) is the second thing the wrapper conflates
    away: it too leaves `Part`. -/
theorem hold_wrapped_false_held :
    ¬ Wrapped [Tok.atom, Tok.comma, Tok.comma] := by
  intro hc
  cases hc with
  | mk p => cases p

/-! ## The outside guard is a decidable function of the token history

    In the real setting these are `scanFlowEntry`'s `invalidFlowEntry` check and
    `tailOf (lastRealTokenVal? sc.tokens)`. The point of the index is that they
    agree: the guard accepts exactly the `.value`-tailed states. -/

/-- The scanner-side guard: a `,` is rejected right after the opener or after
    another `,`. -/
def guardOk : List Tok → Bool
  | [] => false
  | l  => l.getLast? != some Tok.comma

/-- The tail class read off the token history. -/
def tailOfList : List Tok → Tail
  | [] => .sep
  | l  => if l.getLast? == some Tok.comma then .sep else .value

#guard tailOfList [] == Tail.sep
#guard tailOfList [Tok.atom] == Tail.value
#guard tailOfList [Tok.atom, Tok.comma] == Tail.sep

#guard guardOk [] == false
#guard guardOk [Tok.atom] == true
#guard guardOk [Tok.atom, Tok.comma] == false

/-- Guard and index agree on every shape: the guard passes exactly where the tail
    is `.value`. This is the coupling the invariant has to carry — the index is
    useless unless it is pinned to what the guard actually reads. -/
theorem guard_matches_tail_shapes :
    (guardOk [] = (tailOfList [] == Tail.value)) ∧
    (guardOk [Tok.atom] = (tailOfList [Tok.atom] == Tail.value)) ∧
    (guardOk [Tok.atom, Tok.comma] =
      (tailOfList [Tok.atom, Tok.comma] == Tail.value)) := by
  decide

/-- The transition is reachable: the guard passes on the good shape, and the
    inlined transition fires there. -/
theorem hold_fires : Inlined .sep ([Tok.atom] ++ [Tok.comma]) :=
  hold_inlined .items

#guard guardOk [Tok.atom] == true

/-! ## Axiom audit -/

/-- info: 'InlinePayloadToIndex.hold_inlined' does not depend on any axioms -/
#guard_msgs in
#print axioms hold_inlined

/-- info: 'InlinePayloadToIndex.hold_wrapped_false' does not depend on any axioms -/
#guard_msgs in
#print axioms hold_wrapped_false

end InlinePayloadToIndex

end Blanket
