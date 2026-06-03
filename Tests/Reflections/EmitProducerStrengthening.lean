/-!
# Reflection 249 — the emit-producer strengthening is a consumer-joint-before-producer move,
  and the recursive producer is a *verbatim mirror* of the flat one over one shared induction

Self-contained core-Lean toy (no `L4YAML` import) illustrating Blueprint Reflection 249
(`Blueprint/08-initiative-4-intrinsic-foundations.md`).

The L4YAML situation: a body producer (`emitList_scans_safebody`) already certifies the *flat*
invariant `SafeBody`/`WellBracketed` of the comma-separated body `block`.  The locate needs the
*recursive* `RecSeqBody block` instead.  Two lessons:

1. **Consumer-joint-before-producer at the emit boundary.**  The `RecSeqBody` assembler cannot be
   written until each item delivers a *recursive* `RecSeqEntry` — and the flat per-item handle
   (`EmitScansInFlowBlock`) discards that recursion (it is unrecoverable from the flat invariant).
   So name the per-item recursive deliverable as a bare *keyed superset* hypothesis
   (`EmitScansInFlowRecEntry` ⊃ `EmitScansInFlowBlock`, the lone extra conjunct `RecSeqEntry block`
   keyed to the *same* internal block) and build the assembler on it now — verified-but-unconsumed.

2. **The recursive producer is a character-for-character mirror of the flat producer over the SAME
   induction, differing only at the per-entry leaf constructor** (`RecSeqBody.single`/`.cons` for
   `SafeBody.single`/`.cons`).  The flat and recursive invariants are the same decomposition with
   different leaves, so the producer that builds one builds the other by swapping the leaf.

This toy encodes both with a one-kind bracket language.  `FlatEntry` (a weak count-based invariant,
toy for `WellBracketed`/`EntrySafe`) vs `RecEntry`/`RecBody` (the recursive deliverable).  The key
witnesses:
* `recentry_to_flatentry` — RecEntry ⟹ FlatEntry (the superset projection: recursion implies flat).
* `flatentry_aa` + `not_recentry_aa` — `[a, a]` is FlatEntry but NOT RecEntry: the recursive
  deliverable is *strictly stronger*, unrecoverable from the flat invariant (lesson 1's premise).
* `buildFlatBody` vs `buildRecBody` — the two producers, the SAME induction with the leaf
  constructor swapped (lesson 2); `recbody_to_flatbody` projects rec ⟹ flat.

`lake build Tests.Reflections.EmitProducerStrengthening`
-/

namespace EmitProducerStrengthening

/-- One-kind bracket tokens: open/close, an atom `a`, and a separator `fe` (toy `.flowEntry`). -/
inductive Tok | os | cs | a | fe deriving DecidableEq, Repr

open Tok

/-- Bracket delta: `os` = +1, `cs` = −1, atom and separator = 0. -/
def delta : Tok → Int
  | os => 1
  | cs => -1
  | _ => 0

/-- Running bracket balance of a token list. -/
def bal : List Tok → Int
  | [] => 0
  | t :: ts => delta t + bal ts

theorem bal_append (x y : List Tok) : bal (x ++ y) = bal x + bal y := by
  induction x with
  | nil => simp [bal]
  | cons t ts ih => simp only [List.cons_append, bal, ih]; omega

/-- **Flat per-entry invariant** — a deliberately weak count-based predicate (toy for the real
    `WellBracketed`/`EntrySafe`): balanced and nonempty.  `abbrev` so `decide` discharges it. -/
abbrev FlatEntry (b : List Tok) : Prop := bal b = 0 ∧ b ≠ []

/-! **Recursive per-entry deliverable** (toy `RecSeqEntry`): a lone atom, or a properly nested
    `os :: (interior ++ [cs])` whose interior is itself a recursive body — mutual with `RecBody`
    (toy `RecSeqBody`), `fe`-separated `RecEntry`s.  (No doc-comment immediately before `mutual` — R234 gotcha.) -/
mutual
inductive RecEntry : List Tok → Prop where
  | scalar : RecEntry [a]
  | nest (interior : List Tok) (h : RecBody interior) :
      RecEntry (os :: (interior ++ [cs]))
inductive RecBody : List Tok → Prop where
  | single (e : List Tok) (h : RecEntry e) : RecBody e
  | cons (e rest : List Tok) (h : RecEntry e) (hr : RecBody rest) :
      RecBody (e ++ fe :: rest)
end

/-! **The superset projection (recursion ⟹ flat).**  A `RecEntry` is in particular `FlatEntry` —
    the recursive deliverable implies the flat invariant; mutual with `RecBody.toBal` (`bal l = 0`).
    (No doc-comment immediately before `mutual` — R234 gotcha.) -/
mutual
theorem RecEntry.toFlatEntry : {e : List Tok} → RecEntry e → FlatEntry e
  | _, .scalar => by decide
  | _, .nest interior h => by
      have hb : bal interior = 0 := RecBody.toBal h
      refine ⟨?_, by simp⟩
      show delta os + bal (interior ++ [cs]) = 0
      rw [bal_append, hb]; decide
theorem RecBody.toBal : {l : List Tok} → RecBody l → bal l = 0
  | _, .single _ h => (RecEntry.toFlatEntry h).1
  | _, .cons e rest h hr => by
      have he : bal e = 0 := (RecEntry.toFlatEntry h).1
      have hr' : bal rest = 0 := RecBody.toBal hr
      rw [show e ++ fe :: rest = e ++ ([fe] ++ rest) from rfl, bal_append, bal_append, he, hr']
      decide
end

/-- A `RecBody` is in particular a `FlatBody`-shaped count fact (balanced).  Convenience corollary. -/
theorem RecBody.toFlatBal {l : List Tok} (h : RecBody l) : bal l = 0 := RecBody.toBal h

/-! ## The flat invariant, as an inductive mirror of `RecBody`

To make the "same induction, leaf swapped" point sharp, `FlatBody` mirrors `RecBody`'s
`single`/`cons` shape exactly — only the per-entry payload differs (`FlatEntry` vs `RecEntry`). -/

/-- **Flat body invariant** (toy `SafeBody`): `fe`-separated `FlatEntry`s.  Same shape as `RecBody`. -/
inductive FlatBody : List Tok → Prop where
  | single (e : List Tok) (h : FlatEntry e) : FlatBody e
  | cons (e rest : List Tok) (h : FlatEntry e) (hr : FlatBody rest) :
      FlatBody (e ++ fe :: rest)

/-- **The recursive producer projects to the flat one** (toy `RecSeqBody.toSafeBody`): structural
    recursion, `FlatBody.single`/`.cons` per layer via the per-entry superset projection. -/
theorem RecBody.toFlatBody : {l : List Tok} → RecBody l → FlatBody l
  | _, .single e h => FlatBody.single e (RecEntry.toFlatEntry h)
  | _, .cons e rest h hr => FlatBody.cons e rest (RecEntry.toFlatEntry h) hr.toFlatBody

/-! ## The two producers — the SAME induction, the leaf constructor swapped

`joinFE` concatenates per-item blocks with `fe` separators (toy `emitList`'s comma-separated body).
`buildFlatBody` is keyed on each item being a `FlatEntry`; `buildRecBody` on each being a `RecEntry`.
The two proofs are identical line-for-line except for the per-item hypothesis and the leaf
constructor (`FlatBody.*` vs `RecBody.*`) — exactly the flat-vs-recursive emit-producer mirror. -/

def joinFE : List (List Tok) → List Tok
  | [] => []
  | [b] => b
  | b :: bs => b ++ fe :: joinFE bs

/-- **Flat-body producer** (toy `emitList_scans_safebody`), keyed on per-item `FlatEntry`. -/
theorem buildFlatBody : (bs : List (List Tok)) → bs ≠ [] →
    (∀ b ∈ bs, FlatEntry b) → FlatBody (joinFE bs)
  | [], h, _ => absurd rfl h
  | [b], _, hall => FlatBody.single b (hall b (by simp))
  | b :: b' :: bs', _, hall =>
      FlatBody.cons b (joinFE (b' :: bs')) (hall b (by simp))
        (buildFlatBody (b' :: bs') (by simp)
          (fun x hx => hall x (List.mem_cons_of_mem b hx)))

/-- **Recursive-body producer** (toy `emitList_scans_recseqbody`), keyed on per-item `RecEntry`.
    *Verbatim mirror* of `buildFlatBody`: same induction, same recursion, only `RecBody.*` for
    `FlatBody.*` and the per-item hypothesis `RecEntry` for `FlatEntry`. -/
theorem buildRecBody : (bs : List (List Tok)) → bs ≠ [] →
    (∀ b ∈ bs, RecEntry b) → RecBody (joinFE bs)
  | [], h, _ => absurd rfl h
  | [b], _, hall => RecBody.single b (hall b (by simp))
  | b :: b' :: bs', _, hall =>
      RecBody.cons b (joinFE (b' :: bs')) (hall b (by simp))
        (buildRecBody (b' :: bs') (by simp)
          (fun x hx => hall x (List.mem_cons_of_mem b hx)))

/-! ## Witnesses

### Lesson 1 premise — the recursive deliverable is STRICTLY stronger than the flat one
(unrecoverable from it), which is *why* it must be threaded as a keyed hypothesis, not recovered. -/

/-- `[a, a]` satisfies the flat invariant (balanced, nonempty)… -/
theorem flatentry_aa : FlatEntry [a, a] := by decide

/-- …but is NOT a `RecEntry`: a single entry cannot hold two atoms without a separator/nesting.
    So `FlatEntry ⊉ RecEntry` — the recursion cannot be recovered from the flat invariant. -/
theorem not_recentry_aa : ¬ RecEntry [a, a] := by
  intro h; cases h

/-- The superset direction holds the other way: every `RecEntry` IS `FlatEntry`. -/
theorem recentry_to_flatentry {e : List Tok} (h : RecEntry e) : FlatEntry e :=
  RecEntry.toFlatEntry h

/-! ### Positive — a properly nested entry is both recursive and flat. -/

/-- `[os, a, cs]` is a nested `RecEntry` (interior `[a]` = a single scalar body). -/
theorem recentry_oac : RecEntry [os, a, cs] :=
  RecEntry.nest [a] (RecBody.single [a] RecEntry.scalar)

/-- …hence flat, via the superset projection. -/
theorem flatentry_oac : FlatEntry [os, a, cs] := recentry_oac.toFlatEntry

/-! ### Lesson 2 — the two producers and the projection, on a concrete body. -/

/-- A two-item body `[os,a,cs]` then `[a]`, separated by `fe`: a `RecBody` via the recursive
    producer keyed on per-item `RecEntry`. -/
theorem built_rec : RecBody (joinFE [[os, a, cs], [a]]) :=
  buildRecBody [[os, a, cs], [a]] (by simp) (by
    intro b hb
    rcases List.mem_cons.mp hb with h | h
    · exact h ▸ recentry_oac
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ RecEntry.scalar
      · exact absurd h (by simp))

/-- The recursive body projects to the flat body — the recursive producer subsumes the flat one. -/
theorem built_rec_flat : FlatBody (joinFE [[os, a, cs], [a]]) := built_rec.toFlatBody

/-- The flat producer accepts a body the recursive producer's keyed hypothesis would reject:
    `[a, a]` is a `FlatEntry`, so `buildFlatBody` builds it — but no `RecBody` of it exists
    (`not_recentry_aa`).  This is the gap the keyed superset hypothesis bridges. -/
theorem built_flat_only : FlatBody (joinFE [[a, a]]) :=
  buildFlatBody [[a, a]] (by simp) (by
    intro b hb; rcases List.mem_cons.mp hb with h | h
    · exact h ▸ flatentry_aa
    · exact absurd h (by simp))

/-! ## Decidable checks — fail the build if a witness drifts. -/

-- balance facts
#guard bal [os, a, cs] == 0
#guard bal [a, a] == 0
#guard bal [os, a, a, cs] == 0
#guard bal [os, a] == 1          -- an unclosed opener is NOT balanced
#guard bal [a, cs] == (-1)       -- a stray closer underflows

-- the flat invariant is decidable and weak: it accepts the non-recursive `[a, a]`
#guard decide (FlatEntry [a, a])
#guard decide (FlatEntry [os, a, cs])
#guard ! decide (FlatEntry [os, a])   -- unbalanced ⇒ not even flat

end EmitProducerStrengthening
