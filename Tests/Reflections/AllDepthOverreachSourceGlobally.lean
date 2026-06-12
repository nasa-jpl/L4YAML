/-!
# Reflection 394 — an all-depth field over-reaches into the ORTHOGONAL axis; source it globally.

Self-contained core-Lean toy of L4YAML R394, the de-risk that follows R393.  R393 re-scoped a
root-false guard into the root-TRUE all-depth `FlowBodyContentDeepSeq` ([[ref-rescope-by-excluding-premise]]),
keeping its opener field all-depth so the restriction edges stay trivial.  The queued next step was to
PRODUCE its root seed by induction on the owning (seq) axis's recursive deliverable `RecSeqBody`.  Probing
that path FIRST shows it is a DEAD END for the opener field: the all-depth quantifier reaches
`.flowSequenceStart` openers strictly INSIDE flow-MAP interiors, where the entire seq-side family
(`RecSeqBody`/`RecSeqEntry`/`EmitScansInFlowRecEntry`) bottoms out at `WellBracketed` (`RecSeqEntry.map`
stores only `WellBracketed interior`, no recursive content structure).  So the field is NOT projectable
from the single (seq) axis — even though it is TRUE there.

This toy makes the contrast precise with five tokens (`opn`/`cls`/`mopn`/`mcls`/`content`):

* `OpenerOk` (= `FlowBodyContentDeepSeq.openerContentStart`) — every `opn` with a non-`cls` successor is
  followed by `content`, ALL-DEPTH.
* `RecBody` (= `RecSeqBody`) — RECURSES through `opn`-interiors (`seqEntry`) but BOTTOMS OUT at a weak
  `True` substrate for `mopn`-interiors (`mapEntry`).
* `goodBody` = `[mopn, content, opn, content, cls, mcls]` (= the body of `[{a: [b]}]`): the `opn` at index
  2 sits INSIDE the map.  `OpenerOk goodBody` HOLDS (`openerOk_good`) — the field is sound there.
* `badBody` = `[mopn, opn, mopn, mcls, mcls]`: same map-entry SHAPE, but its interior opener is followed
  by `mopn` ≠ `content`.  `RecBody` accepts it (interior opaque to `mapEntry`) yet `OpenerOk badBody` is
  FALSE — so `recBody_underdetermines` proves there is NO projection `RecBody l → OpenerOk l`.

The FIX (`global_entails_openerOk` + `globalAdj_good`): source the all-depth fact GLOBALLY from a uniform
emitter-output adjacency invariant `GlobalAdj` ("every `opn` is followed by `content` or `cls`", indifferent
to which axis it sits in), which DOES reach the map-interior opener and entails `OpenerOk` — no axis
recursion.  And `consumer_reads_head` shows the actual consumer (`flowBodyContent_descend`:
`h_deep.openerContentStart p (Nat.le_refl p)`) reads the field only at the window HEAD, so its map-interior
obligation was pure over-reach all along.

POSITIVE: `openerOk_good` (field true at the map-interior opener); `globalAdj_good` / `global_entails_openerOk`
(the global route reaches it and entails the field); `consumer_reads_head` (consumer needs only the head).
NEGATIVE: `recBody_underdetermines` (the owning-axis deliverable does NOT entail the all-depth field);
`recBody_good` / `recBody_bad` (the deliverable is blind to the map interior — accepts both).

Mapping to L4YAML: `OpenerOk` ~ `FlowBodyContentDeepSeq.openerContentStart`; `RecBody.mapEntry` ~
`RecSeqEntry.map` (`WellBracketed`-only); `goodBody` ~ the scan of `[{a: [b]}]`; `recBody_underdetermines`
~ `flowBodyContentDeepSeq_opener_reaches_map_interior`; `GlobalAdj` ~ the owed global emitter token-adjacency
lemma; `consumer_reads_head` ~ `flowBodyContent_descend`'s head-only instantiation.
-/

namespace Tests.Reflections.AllDepthOverreachSourceGlobally

set_option autoImplicit false

inductive Tok | opn | cls | mopn | mcls | content
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All-depth opener field (= `FlowBodyContentDeepSeq.openerContentStart`): every `opn` (with a
    non-`cls` successor) is followed by `content`.  `List.range`-bounded so it is `decide`-able. -/
def OpenerOk (l : List Tok) : Prop :=
  ∀ i ∈ List.range l.length, i + 1 < l.length →
    l[i]! = .opn → l[i+1]! ≠ .cls → l[i+1]! = .content

/-- The GLOBAL emitter-output adjacency invariant (= "every `[` in `emit _` is followed by `]` or
    content-start"): uniform over the WHOLE list, indifferent to which axis the `opn` sits in. -/
def GlobalAdj (l : List Tok) : Prop :=
  ∀ i ∈ List.range l.length, i + 1 < l.length →
    l[i]! = .opn → (l[i+1]! = .content ∨ l[i+1]! = .cls)

/-- The owning-axis (seq) recursive deliverable (= `RecSeqBody`).  It RECURSES through `opn`-interiors
    (`seqEntry`) but BOTTOMS OUT at a weak `True` substrate for `mopn`-interiors (`mapEntry`) — exactly
    `RecSeqEntry.map` storing only `WellBracketed interior`, no recursive content structure. -/
inductive RecBody : List Tok → Prop where
  | scalarEntry : RecBody [.content]
  | seqEntry (interior : List Tok) (h : RecBody interior) :
      RecBody (.opn :: interior ++ [.cls])
  | mapEntry (interior : List Tok) (h : True) :
      RecBody (.mopn :: interior ++ [.mcls])

/-- Body of `[{a: [b]}]` (window): `{ a [ b ] }` flattened — the `opn` at index 2 is INSIDE the map. -/
def goodBody : List Tok := [.mopn, .content, .opn, .content, .cls, .mcls]

/-- Same map-entry SHAPE, but its interior opener is followed by `mopn` — violates `OpenerOk` at the
    map-interior position.  `RecBody` accepts it all the same (the interior is opaque to `mapEntry`). -/
def badBody : List Tok := [.mopn, .opn, .mopn, .mcls, .mcls]

/-- **POSITIVE — the field is TRUE at the map-interior opener.**  `OpenerOk` fires at index 2 of
    `goodBody` (the `opn` strictly inside the map) and holds — the field is sound there. -/
theorem openerOk_good : OpenerOk goodBody := by unfold OpenerOk; decide

/-- **POSITIVE — sourcing GLOBALLY reaches the map-interior opener.**  The uniform `GlobalAdj` holds on
    `goodBody` (index 2 included) and entails `OpenerOk` — the all-depth fact, produced without any
    axis recursion. -/
theorem globalAdj_good : GlobalAdj goodBody := by unfold GlobalAdj; decide

theorem global_entails_openerOk {l : List Tok} (h : GlobalAdj l) : OpenerOk l := by
  intro i hi hib ho hne
  rcases h i hi hib ho with hc | hcls
  · exact hc
  · exact absurd hcls hne

/-- **NEGATIVE — the owning-axis deliverable does NOT entail the field.**  `RecBody` holds for `badBody`
    (via `mapEntry`, blind to the interior) yet `OpenerOk badBody` is FALSE — so there is no projection
    `RecBody l → OpenerOk l`.  The all-depth field is unproducible from the single (seq) axis. -/
theorem recBody_underdetermines : ¬ ∀ l, RecBody l → OpenerOk l := by
  intro h
  have hrec : RecBody badBody := RecBody.mapEntry [.opn, .mopn, .mcls] trivial
  have hbad : ¬ OpenerOk badBody := by unfold OpenerOk; decide
  exact absurd (h badBody hrec) hbad

/-- **NEGATIVE (structural) — the deliverable is BLIND to the interior.**  Both the OpenerOk-satisfying
    `goodBody` and the OpenerOk-violating `badBody` are accepted by `RecBody` via the same `mapEntry`. -/
theorem recBody_good : RecBody goodBody := RecBody.mapEntry [.content, .opn, .content, .cls] trivial
theorem recBody_bad : RecBody badBody := RecBody.mapEntry [.opn, .mopn, .mcls] trivial

/-- **POSITIVE — the consumer reads the field only at the window HEAD.**  Like
    `flowBodyContent_descend` (`h_deep.openerContentStart p (Nat.le_refl p)`), the only use is at index 0
    — never at the map-interior opener, so its obligation there is pure over-reach. -/
theorem consumer_reads_head (l : List Tok) (h : OpenerOk l)
    (hlen : 1 < l.length) (hhead : l[0]! = .opn) (hne : l[1]! ≠ .cls) : l[1]! = .content :=
  h 0 (List.mem_range.mpr (by omega)) hlen hhead hne

#guard goodBody.length == 6
#guard goodBody[2]! == Tok.opn          -- opener strictly inside the map
#guard goodBody[3]! == Tok.content      -- ... followed by content (field true here)
#guard badBody[1]! == Tok.opn           -- same-shape map entry's opener ...
#guard badBody[2]! == Tok.mopn          -- ... followed by mopn ≠ content (field violated)

end Tests.Reflections.AllDepthOverreachSourceGlobally
