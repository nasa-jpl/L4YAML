/-! # Reflection 508 — the cross-frame structural descent reaches what a path-gated walk cannot

R507 ([[ProducerGateCoversFragment]]) found that the spine-walk seq navigator's gate
(`SeqPathAllSeq` — EVERY enclosing bracket frame is `[`) covers only a FRAGMENT of the consumer's
domain: it provably cannot reach a map-nested seq like `[{a: [b]}]`'s inner `[b]`, whose bracket
path is `[`, `{`, `[` (a `{` frame in the middle). The per-window `RecSeqBody` producer is owed
PATH-FREE, for those windows too.

R508 lands the enabling primitive for the PATH-FREE architecture. The key observation: the root
`RecSeqBody` (known off emission, `seqRoot_recseqbody`) ALREADY STORES every nested window's body as
a subterm of the mutual inductive — `RecSeqEntry.seq` stores `RecSeqBody interior`,
`RecSeqEntry.mapRec` stores `RecMapBody interior`, and a `RecMapPair` stores its key/value blocks as
`RecSeqEntry`s. So descending the INDUCTIVE reaches every window regardless of the bracket PATH; the
`SeqPathAllSeq` gate is an artifact of walking the TOKEN SPINE, not of the deliverable.

That descent crosses frames at three structural edges. Two existed (`recseqentry_seq_extract` —
seq entry → nested seq body; the `.mapRec` field — seq entry → nested map body). The THIRD, the
map→seq edge (from a `RecMapPair` into a key/value block that is itself a nested seq), was MISSING —
the spine-walk navigators stop at `{`. R508 (`recmappair_block_descent`) is exactly that edge.

This demo models the mutual inductive abstractly (no tokens) and shows the decisive contrast:
* the map→seq cross-frame primitive (`MPair.blockDescent`, mirroring `recmappair_block_descent`)
  reads a nested seq body off a map pair's value;
* a STRUCTURAL descent reaches the inner body of the map-nested seq `[{a: [b]}]`;
* a PATH-GATED (seq-only spine) walk `spineSeqOnly` provably STOPS at the `{` frame and never
  reaches it — the R507 fragment;
* the bracket path to that body is NOT all-seq (`path_not_all_seq`), yet the structural descent
  succeeds — so the structural route is genuinely path-free.

Every theorem closes by `rfl`/`decide`; the bracket-path lemma `path_not_all_seq` is fully
axiom-free, and the `rfl` computations over the mutual inductive use `[propext]` only.
-/

namespace CrossFrameStructuralDescent

/- The recursive deliverable, modelled abstractly (mirrors the `RecSeqBody`/`RecSeqEntry`/`RecMapBody`/
   `RecMapPair` mutual inductive — Type-valued here so we can compute descents). A `SEntry` may be a
   scalar, a nested seq (storing its `SBody` — the `.seq` edge), or a nested map (storing its `MBody`
   — the `.mapRec` seq→map edge). An `MPair` stores its key and value entries (the map→seq edge: a
   value `SEntry` can itself be a nested `.seq`). -/
mutual
  inductive SBody where
    | nil
    | cons : SEntry → SBody → SBody
  inductive SEntry where
    | scalar
    | seq : SBody → SEntry
    | mapRec : MBody → SEntry
  inductive MBody where
    | nil
    | cons : MPair → MBody → MBody
  inductive MPair where
    | mk : SEntry → SEntry → MPair
end

/-- Seq entry → nested seq body (models `recseqentry_seq_extract`: the `.seq` edge). -/
def SEntry.seqBody : SEntry → Option SBody
  | .seq b => some b
  | _ => none

/-- Seq entry → nested map body (models the `RecSeqEntry.mapRec` stored field: the seq→map edge). -/
def SEntry.mapBody : SEntry → Option MBody
  | .mapRec m => some m
  | _ => none

/-- **The map→seq cross-frame primitive** — the demo analogue of `recmappair_block_descent`. A map
    pair exposes its key and value entries AND, when the value is a nested seq, that seq's body. This
    is the edge the spine-walk navigators lack. -/
def MPair.blockDescent : MPair → SEntry × SEntry × Option SBody
  | .mk k v => (k, v, v.seqBody)

/-- The map→seq edge is correct: a pair whose value is a nested seq exposes that seq's body (the
    `recseqentry_seq_extract h_ve …` half of the real brick). -/
theorem mappair_value_seq_extract (k : SEntry) (b : SBody) :
    (MPair.mk k (.seq b)).blockDescent = (k, .seq b, some b) := rfl

/-- A bracket frame along a structural path: `seqF` for `[`, `mapF` for `{`. -/
inductive Frame | seqF | mapF
  deriving DecidableEq

/-- The `SeqPathAllSeq` predicate, abstractly: every enclosing frame is a seq. -/
def allSeq : List Frame → Bool := fun p => p.all (fun f => f == .seqF)

-- The map-nested seq `[{a: [b]}]`, built bottom-up.
/-- Inner seq `[b]` — one scalar entry. -/
def innerSeq : SBody := .cons .scalar .nil
/-- The pair `a: [b]` — scalar key, nested-seq value. -/
def pair : MPair := .mk .scalar (.seq innerSeq)
/-- The map body `{a: [b]}`. -/
def mapBody : MBody := .cons pair .nil
/-- The seq entry `{a: [b]}` — a nested map (the seq→map `.mapRec` edge). -/
def mapEntry : SEntry := .mapRec mapBody
/-- The root seq body `[{a: [b]}]`. -/
def root : SBody := .cons mapEntry .nil

/-- The bracket path from the root down to the inner seq body: `[`, `{`, `[`. -/
def rootPathToInner : List Frame := [.seqF, .mapF, .seqF]

/-- **The path is NOT all-seq** — the `{` frame in the middle fails `SeqPathAllSeq`. This is exactly
    why the spine-walk navigator (gated on `allSeq`) cannot serve this window: the R507 fragment. -/
theorem path_not_all_seq : allSeq rootPathToInner = false := by decide

/-- **The path-gated (seq-only spine) walk STOPS at the `{` frame.** It can descend only through
    `.seq` edges, so at the map entry it returns `none` — it never reaches the inner body. Models the
    `SeqPathAllSeq`-gated spine navigator hitting a `{`. -/
def spineSeqOnly : SEntry → Option SBody := SEntry.seqBody

theorem spine_stops_at_map : spineSeqOnly mapEntry = none := rfl

/-- **The STRUCTURAL descent reaches the inner body** — crossing seq→map (`.mapRec`) then map→seq
    (`MPair.blockDescent`), with NO path gate. This is the path-free route the residual needs. -/
def structuralDescend : SBody → Option SBody
  | .cons (.mapRec (.cons p _)) _ => (p.blockDescent.2.2)
  | _ => none

theorem structural_reaches_inner : structuralDescend root = some innerSeq := rfl

/-- The demo deliverable: the cross-frame map→seq primitive is correct (`mappair_value_seq_extract`);
    the map-nested seq's path is NOT all-seq so the spine-gated walk STOPS at the `{`
    (`path_not_all_seq` ∧ `spine_stops_at_map`); yet the STRUCTURAL descent reaches its inner body
    path-free (`structural_reaches_inner`). The lesson: the body is STORED in the inductive, so the
    descent that reads it off needs no path knowledge — the `SeqPathAllSeq` gate belongs to the
    token-spine walk, not the deliverable. -/
theorem demo :
    ((MPair.mk .scalar (.seq innerSeq)).blockDescent = (.scalar, .seq innerSeq, some innerSeq))
    ∧ (allSeq rootPathToInner = false ∧ spineSeqOnly mapEntry = none)
    ∧ (structuralDescend root = some innerSeq) :=
  ⟨rfl, ⟨by decide, rfl⟩, rfl⟩

end CrossFrameStructuralDescent
