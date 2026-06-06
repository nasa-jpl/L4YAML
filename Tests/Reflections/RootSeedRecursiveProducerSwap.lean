/-!
# Reflection 302 — the root seed of a recursive-deliverable producer reuses the FLAT derivation's slice/decomposition verbatim and swaps only the body producer; the slice bridge is producer-agnostic

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`seqRoot_safeBodyUnit`, the ROOT instance of `(i'-b-descend-root-provider)`.

A "container framing" wraps a `body` with an opener and closer (`wrap`); the windowing slice
(`windowSlice`) recovers the body by dropping both. The decisive observation: the slice identity
`windowSlice (wrap body) = body` is about the CONTAINER SHAPE, never about any property of `body`
— it is **producer-agnostic**. So the ROOT SEED is generic over the producer `P` (`rootSeed`):
re-running the slice extraction transfers ANY body fact `P body` to the windowed slice. The flat
derivation instantiates `P := Flat` (the flat fact); the recursive root SWAPS only the body
producer to `P := Rec` (the recursive deliverable), gaining the recursion while losing nothing
(`Rec.toFlat` re-projects the flat fact).

Toy substrate: `wrap` = `0 :: body ++ [99]` (opener `0`, closer `99` — toy `[` … `]`);
`Flat` = all-positive (the flat "WellTyped"); `Rec` = the structural all-positive chain (the
recursive "RecSeqBody"), with `Rec.toFlat` the projection (toy "RecSeqBody.toWellBracketed").
-/

namespace Tests.Reflections.RootSeedRecursiveProducerSwap

set_option autoImplicit false

/-- The container FRAMING (toy of the stream-wrap `"[" ++ body ++ "]"` + streamEnd): opener `0`,
    closer `99`. -/
def wrap (body : List Nat) : List Nat := 0 :: (body ++ [99])

/-- The WINDOWING SLICE (toy of `(tokens.toList.take (size-2)).drop 2`): drop the closer
    (`take (len-1)`) and the opener (`drop 1`), recovering the interior. -/
def windowSlice (l : List Nat) : List Nat := (l.take (l.length - 1)).drop 1

/-- **The slice bridge — PRODUCER-AGNOSTIC** (faithful mirror of `h_take_eq`): it recovers the
    body from the framing referring ONLY to the container shape, never to any property of `body`.
    This is why it transfers verbatim between the flat and the recursive derivation. -/
theorem windowSlice_wrap (body : List Nat) : windowSlice (wrap body) = body := by
  unfold windowSlice wrap
  have hlen : (0 :: (body ++ [99])).length - 1 = body.length + 1 := by
    simp only [List.length_cons, List.length_append, List.length_nil]; omega
  rw [hlen, List.take_succ_cons, List.take_left, List.drop_succ_cons, List.drop_zero]

/-- The FLAT deliverable (toy of `WellTyped`): every element is positive. -/
def Flat (l : List Nat) : Prop := ∀ x ∈ l, 0 < x

/-- The RECURSIVE deliverable (toy of `RecSeqBody`): the structural all-positive chain. -/
inductive Rec : List Nat → Prop where
  | nil : Rec []
  | cons (x : Nat) (xs : List Nat) (h : 0 < x) (hr : Rec xs) : Rec (x :: xs)

/-- **The projection** (toy of `RecSeqBody.toWellBracketed`/`.toSafeBodyUnit`): the recursive
    deliverable is strictly stronger — it re-projects the flat fact, so swapping it in loses
    nothing. -/
theorem Rec.toFlat : {l : List Nat} → Rec l → Flat l
  | _, .nil => by intro x hx; cases hx
  | _, .cons x xs h hr => by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hmem
      · exact h
      · exact hr.toFlat y hmem

/-- **The ROOT SEED — generic over the producer `P`** (the heart of R302): the slice bridge
    transfers ANY body fact to the windowed slice, by the SAME `windowSlice_wrap` identity. The
    flat derivation and the recursive root are both instances; only `P` differs. -/
theorem rootSeed (P : List Nat → Prop) (body : List Nat) (h : P body) :
    P (windowSlice (wrap body)) := by rw [windowSlice_wrap]; exact h

/-- **FLAT root** — the existing flat derivation (`P := Flat`). -/
theorem flatRoot (body : List Nat) (h : Flat body) : Flat (windowSlice (wrap body)) :=
  rootSeed Flat body h

/-- **RECURSIVE root** — SWAP only the body producer (`P := Rec`); the slice identity is unchanged,
    and the recursion is gained. This is `seqRoot_safeBodyUnit`'s shape: same chain-replay, swap
    `emitList_body_filtered_characterization` → `emitList_body_recseqbody`, project through the
    same `h_take_eq`. -/
theorem recRoot (body : List Nat) (h : Rec body) : Rec (windowSlice (wrap body)) :=
  rootSeed Rec body h

/-- **Nothing is lost by the swap**: the recursive root re-projects the flat fact (toy of
    `RecSeqBody.toSafeBodyUnit`/`.toWellBracketed` recovering everything the flat path delivered). -/
theorem recRoot_reprojects (body : List Nat) (h : Rec body) :
    Flat (windowSlice (wrap body)) := (recRoot body h).toFlat

/-! ## Decidable witnesses -/

-- The framing and its slice (producer-agnostic shapes).
#guard wrap [1, 2, 3] == [0, 1, 2, 3, 99]
#guard windowSlice (wrap [1, 2, 3]) == [1, 2, 3]
-- The flat fact transfers to the windowed slice.
#guard decide (∀ x ∈ windowSlice (wrap [1, 2, 3]), 0 < x)

/-- POSITIVE — the recursive producer at a concrete body, lifted to the windowed slice. -/
theorem probe_recRoot : Rec (windowSlice (wrap [1, 2, 3])) :=
  recRoot [1, 2, 3]
    (.cons 1 _ (by omega) (.cons 2 _ (by omega) (.cons 3 _ (by omega) .nil)))

/-- **The slice bridge is PRODUCER-AGNOSTIC** — it holds even for a body where `Flat` FAILS
    (contains `0`), proving the identity is about the framing, not the body's property. -/
theorem slice_agnostic_offFlat : windowSlice (wrap [0, 5]) = [0, 5] := windowSlice_wrap _

/-- NEGATIVE — `Flat` genuinely fails on that body, so the agnostic slice above is not
    secretly relying on the flat fact. -/
theorem flat_fails_offFlat : ¬ Flat [0, 5] := by
  intro h; exact absurd (h 0 (by simp)) (by omega)

/-- POSITIVE — the two endpoints together: the recursive root holds AND re-projects the flat
    fact, witnessing that the swap gains the recursion while losing nothing. -/
theorem fold_endpoints :
    Rec (windowSlice (wrap [1, 2, 3])) ∧ Flat (windowSlice (wrap [1, 2, 3])) :=
  ⟨probe_recRoot, probe_recRoot.toFlat⟩

end Tests.Reflections.RootSeedRecursiveProducerSwap
