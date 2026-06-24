/-! # Reflection 502 — the carrier-free edges UNIFY as one projection of the recursion's deliverable

Completing the carrier-free `FlowBodyContent` thread (root R501 + descend R500 + advance reused), the two
guard-READING edges turned out to differ ONLY in HOW they obtain a windowed `SafeBodyUnit`; the
content-assembly tail (`seqEnclosingFacts_of_windowed_safebodyunit ▸ flowBodyContent_of_deepSeq`) is
byte-identical, and that `SafeBodyUnit` is in BOTH cases a window's `RecSeqBody.toSafeBodyUnit`. So both
edges are the SAME function of the window's OWN deliverable (`RecSeqBody`): producing the body and reading
it back as content is one projection. `flowBodyContent_of_recseqbody_seq` (R502) names that projection once,
keyed on the deliverable directly — the consume-side dual the JOINT `windowWidth_strongRecOn` co-construction
reads.

Consequence for the JOINT consume step: the recursion's IH yields `RecSeqBody` for any sub-window, so the
sub-window's content is a FREE projection — no second IH call, no oracle re-entry. The only content the
recursion still owes top-down is the CURRENT window's (the head dispatch consumes `h_content` before the
body deliverable exists); the CHILDREN's content is this free projection. Different windows ⇒ no same-window
cycle — which is exactly what splits the co-construction into a top-down content thread (seeded at the root)
and a bottom-up body deliverable.

`Deliv` models `RecSeqBody`; `Inter` models the windowed `SafeBodyUnit`; `Guard` models
`FlowBodyContentDeepSeq`; `Content` models `FlowBodyContent`. `projInter` is `RecSeqBody.toSafeBodyUnit`;
`assemble` is the content-assembly tail; `contentOfDeliv` is `flowBodyContent_of_recseqbody_seq`.
-/

namespace EdgesUnifyAsDeliverableProjection

/-- The recursion's DELIVERABLE (models `RecSeqBody`): a genuine, non-empty, content-only body. -/
def Deliv (l : List Bool) : Prop := l ≠ [] ∧ ∀ x ∈ l, x = true

/-- The intermediate PROJECTION (models the windowed `SafeBodyUnit ContentStartTok`). -/
def Inter (l : List Bool) : Prop := ∀ x ∈ l, x = true

/-- The downstream GUARD threaded as a recursion `G`-conjunct (models `FlowBodyContentDeepSeq`). -/
def Guard (_l : List Bool) : Prop := True

/-- The downstream CONTENT projection threaded carrier-free (models `FlowBodyContent`). -/
def Content (l : List Bool) : Prop := ∀ x ∈ l, x = true

/-- `RecSeqBody.toSafeBodyUnit`: the deliverable projects to the intermediate. -/
theorem projInter {l : List Bool} (d : Deliv l) : Inter l := d.2

/-- The content-assembly TAIL (models `seqEnclosingFacts_of_windowed_safebodyunit ▸
    flowBodyContent_of_deepSeq`): the guard plus the intermediate ⇒ content. Byte-identical across the
    root and descend edges — neither edge touches the deliverable SOURCE here. -/
theorem assemble {l : List Bool} (_g : Guard l) (i : Inter l) : Content l := i

/-- **The UNIFYING lemma** (models `flowBodyContent_of_recseqbody_seq`): content is a projection of the
    window's OWN deliverable + its guard, with NO appeal to how the deliverable was obtained. -/
theorem contentOfDeliv {l : List Bool} (g : Guard l) (d : Deliv l) : Content l :=
  assemble g (projInter d)

/-! Both guard-READING edges reduce to `contentOfDeliv` — they differ ONLY in the deliverable SOURCE. -/

/-- ROOT edge (models `seqRoot_flowBodyContent_seq`, R501): the deliverable comes from a FLAT source
    (emission / `seqRoot_recseqbody`). -/
theorem rootEdge {l : List Bool} (g : Guard l) (flat : Deliv l) : Content l :=
  contentOfDeliv g flat

/-- DESCEND edge (models `flowBodyContent_descend_seq`, R500): the deliverable comes from the IH (the
    child oracle's `RecSeqBody`). -/
theorem descendEdge {l : List Bool} (g : Guard l) (ih : Deliv l) : Content l :=
  contentOfDeliv g ih

/-- The two edges are DEFINITIONALLY the same term once the deliverable is in hand — the SOURCE is the
    only delta, and it has been factored out into the deliverable hypothesis. -/
theorem edges_agree {l : List Bool} (g : Guard l) (d : Deliv l) :
    rootEdge g d = descendEdge g d := rfl

/-! **The split that breaks the carrier↔producer circularity.** The CHILDREN's content is free from the
    IH's deliverable; the CURRENT window's content is the top-down owe (consumed before the body exists). -/

/-- Models the JOINT IH: for any sub-window's deliverable, the sub-window's content is projected with no
    extra IH call and no oracle re-entry — content is FREE wherever the recursion already produced the
    body. -/
theorem childContent_free {l : List Bool} (g : Guard l) (ih_deliv : Deliv l) : Content l :=
  contentOfDeliv g ih_deliv

/-- Concrete witnesses: the deliverable holds on a genuine body, and content projects from it. -/
theorem deliv_demo : Deliv [true, true] := ⟨by decide, by decide⟩
theorem content_demo : Content [true, true] := contentOfDeliv trivial deliv_demo

/-- The unifying lemma genuinely USES the deliverable (it is not vacuous): on an empty list `Deliv` fails,
    so `contentOfDeliv` is only ever invoked where the recursion produced a real body. -/
theorem deliv_needs_nonempty : ¬ Deliv [] := fun h => h.1 rfl

end EdgesUnifyAsDeliverableProjection
