/-! # Reflection 503 — bundle the free projection INTO the producer that already holds the deliverable

R502 ([[EdgesUnifyAsDeliverableProjection]]) named the free projection `content = proj(deliverable)`: the
recursion produces a body deliverable, and reading it back as the downstream projection is one map. R503 is
the CONSUME-side move that follows: realize that projection *at the producer that already computes the
deliverable*, BUNDLING it into the producer's output — so the producer's deliverable does DOUBLE DUTY (its
primary purpose AND the projection) — instead of re-deriving the projection downstream via a PARALLEL edge
that re-runs the deliverable's own producer.

In L4YAML the seq oracle `recseqentry_seqbracket_oracle_seq` already computes the child `RecSeqBody`
`((take j).drop (lo+1))` off a CONTENT-FREE width IH (via `seqChild_safeBodyUnit_seq`). The twin
`recseqentry_seqbracket_oracle_seq_content` (R503) returns that SAME `RecSeqBody` AND the child
`FlowBodyContent` (= R502's `flowBodyContent_of_recseqbody_seq` applied to it) — reusing the one IH-produced
deliverable, NOT re-running the R500 descend edge `flowBodyContent_descend_seq` (which would re-derive the
child `SafeBodyUnit` from scratch). The descend child's content `G`-conjunct is thus emitted by the producer
that was going to compute the body anyway.

`ihFree` models the seq oracle's content-free width IH; `Deliv` the child `RecSeqBody`; `Content` the child
`FlowBodyContent`; `proj` is R502's free projection; `reDerive` the R500-style parallel edge that re-runs the
producer.

The point is NOT that the two routes give different answers — they are definitionally equal (`twin_agrees`).
It is WHERE the projection is realized: bundled into the one producer call (`oracleContent`), the deliverable
serves both consumers; routed through the parallel edge (`reDerive`), the producer runs a second time.
-/

namespace BundleFreeProjectionIntoProducer

/-- The recursion's DELIVERABLE (models the child `RecSeqBody`): a genuine non-empty content-only body. -/
def Deliv (l : List Bool) : Prop := l ≠ [] ∧ ∀ x ∈ l, x = true

/-- The downstream PROJECTION (models the child `FlowBodyContent`). -/
def Content (l : List Bool) : Prop := ∀ x ∈ l, x = true

/-- R502's FREE projection (models `flowBodyContent_of_recseqbody_seq`): content is a projection of the
    deliverable already in hand — no second producer call. -/
theorem proj {l : List Bool} (d : Deliv l) : Content l := d.2

/-- The producer's CONTENT-FREE IH (models the seq oracle's width IH `h_ih`): produces the deliverable with
    NO appeal to content. Here the trivial constructor — the modelling point is that it is the ONE producer
    whose single evaluation the twin shares. -/
def ihFree (l : List Bool) (h1 : l ≠ []) (h2 : ∀ x ∈ l, x = true) : Deliv l := ⟨h1, h2⟩

/-- The OLD producer (models `recseqentry_seqbracket_oracle_seq`): returns ONLY the deliverable. -/
def oracle (l : List Bool) (h1 : l ≠ []) (h2 : ∀ x ∈ l, x = true) : Deliv l := ihFree l h1 h2

/-- **The TWIN** (models `recseqentry_seqbracket_oracle_seq_content`, R503): returns the deliverable AND its
    free projection, from a SINGLE `ihFree` evaluation — the `let`-shared `d` does double duty. -/
def oracleContent (l : List Bool) (h1 : l ≠ []) (h2 : ∀ x ∈ l, x = true) : Deliv l ∧ Content l :=
  let d := ihFree l h1 h2
  ⟨d, proj d⟩

/-- The PARALLEL re-derivation edge (models R500 `flowBodyContent_descend_seq` re-running
    `seqChild_safeBodyUnit_seq`): produces the SAME content but re-invokes the producer `ihFree`. -/
def reDerive (l : List Bool) (h1 : l ≠ []) (h2 : ∀ x ∈ l, x = true) : Content l :=
  proj (ihFree l h1 h2)

/-- **The double duty is manifest**: the twin's content is literally a PROJECTION of the deliverable it
    bundles — the deliverable serves both consumers from one producer call. -/
theorem twin_content_is_projection (l : List Bool) (h1 : l ≠ []) (h2 : ∀ x ∈ l, x = true) :
    (oracleContent l h1 h2).2 = proj (oracleContent l h1 h2).1 := rfl

/-- **One deliverable, shared**: the twin is `(d, proj d)` for the SAME `d := ihFree …`. The single `ihFree`
    evaluation feeds both halves — the structural fact behind "no second producer call". -/
theorem twin_shares_one_deliverable (l : List Bool) (h1 : l ≠ []) (h2 : ∀ x ∈ l, x = true) :
    oracleContent l h1 h2 = (fun d : Deliv l => (⟨d, proj d⟩ : Deliv l ∧ Content l)) (ihFree l h1 h2) :=
  rfl

/-- **The twin AGREES with both separate derivations** — same deliverable as the old oracle, same content as
    the parallel edge — so bundling LOSES NOTHING. The difference is only WHERE the projection runs: in the
    twin it is the bundled `d`'s projection; in `reDerive` it is a SECOND `ihFree` call. -/
theorem twin_agrees (l : List Bool) (h1 : l ≠ []) (h2 : ∀ x ∈ l, x = true) :
    (oracleContent l h1 h2).1 = oracle l h1 h2 ∧ (oracleContent l h1 h2).2 = reDerive l h1 h2 :=
  ⟨rfl, rfl⟩

/-! Concrete witnesses (axiom-free `decide`). -/

/-- A genuine non-empty content-only body. -/
def body : List Bool := [true, true]

theorem body_deliv : Deliv body := ⟨by decide, by decide⟩

/-- The twin fires on a real body, emitting both deliverable and content. -/
theorem twin_demo : Deliv body ∧ Content body := oracleContent body (by decide) (by decide)

/-- The producer is NOT vacuous: on an empty list `Deliv` fails, so the oracle (and its twin) only ever fire
    where the recursion produced a real body — the projection is never over an empty deliverable. -/
theorem deliv_needs_nonempty : ¬ Deliv [] := fun h => h.1 rfl

end BundleFreeProjectionIntoProducer
