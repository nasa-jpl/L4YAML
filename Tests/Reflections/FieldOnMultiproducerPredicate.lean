/-!
# Reflection 426 — a carrier field on a MULTI-PRODUCER predicate is gated by the producer whose
  source is a STRUCTURE-DISCARDING inductive deliverable

Self-contained (core Lean, no `L4YAML` import) toy of the R426 finding.

Adding a structural carrier field `P block` to a predicate `Pred` that has TWO producers obliges
*both* to supply it.  In L4YAML, `EmitScansInFlowBlock` is produced (a) by the GRAMMAR induction
`emit_scans_block_combined` and (b) by the locator coercion `emitScansInFlowBlock_of_flowRecEntry`,
which forwards from `EmitScansInFlowRecEntry` whose body is the inductive deliverable `RecSeqEntry`.
`RecSeqEntry.map` **bottoms out** at `WellBracketed interior` (it discards the map interior's
recursive structure).  So the new field `SepAdj` (every `.flowEntry` separator's non-`.key` successor
is a content start) CANNOT be PROJECTED from `RecSeqEntry` — `RecSeqEntry.toSepAdj` is FALSE, because
the `.map` constructor admits `SepAdj`-violating interiors like `{,,}` (two consecutive separators).

The resolution is NOT to strengthen the inductive (the locator deliberately bottoms out there); it is
to thread `P` as a SEPARATE carrier field of the per-item PREDICATE `EmitScansInFlowRecEntry`, supplied
by its GRAMMAR producer `emit_scans_in_flow_rec_entry` — which retains the scan structure and PROVES
`SepAdj` honestly (the map interior's `SepAdj` is vacuous — separators followed by `.key` — provable
from the scanned `EmitPairListScansInFlowBlock`, never from the deliverable's bare `WellBracketed`).

The toy below models exactly that gap:

* `SepOk` — the structural field (toy of `SepAdj`): every `sep` is followed by a `content`.
* `balanced` — a `WellBracketed`-style invariant that says nothing about `sep`-adjacency.
* `Deliv` — the structure-discarding inductive deliverable (toy of `RecSeqEntry`): its `wrap`
  constructor stores ONLY `balanced interior`.
* NEGATIVE `deliv_toSepOk_fails` — `Deliv.toSepOk` is FALSE: `wrap [sep, sep]` is `balanced` yet
  `SepOk` fails inside it.  Projecting the field from the inductive is impossible.
* POSITIVE `sepOk_of_scanned_wrap` — a producer that KNOWS the scanned interior (here a real
  `content sep content`) PROVES `SepOk` of the wrapped block directly; the grammar producer supplies
  the field as a separate carrier, bypassing the bottoming inductive.
-/

namespace Tests.Reflections.FieldOnMultiproducerPredicate

set_option autoImplicit false

/-- Toy tokens: `content` (a value start), `sep` (a separator), `opener`/`closer` (brackets). -/
inductive Tok | content | sep | opener | closer
  deriving DecidableEq

/-- The structural carrier field (toy of `SepAdj`): every `sep` is followed by a `content`. -/
def SepOk (l : List Tok) : Prop :=
  ∀ (i : Nat) (h : i + 1 < l.length),
    (l[i]'(Nat.lt_of_succ_lt h)) = Tok.sep → (l[i+1]'h) = Tok.content

/-- A `WellBracketed`-style invariant: equal opener/closer counts.  Says NOTHING about `sep`s. -/
def balanced (l : List Tok) : Bool :=
  (l.filter (· == Tok.opener)).length == (l.filter (· == Tok.closer)).length

/-- The **structure-discarding** inductive deliverable (toy of `RecSeqEntry`): the `wrap`
    constructor stores ONLY `balanced interior` — it bottoms out, keeping no `SepOk` evidence. -/
inductive Deliv : List Tok → Prop where
  | leaf : Deliv [Tok.content]
  | wrap (interior : List Tok) (h : balanced interior = true) :
      Deliv (Tok.opener :: (interior ++ [Tok.closer]))

/-! ## The field CANNOT be projected from the bottoming inductive. -/

/-- **NEGATIVE** — `Deliv.toSepOk` is FALSE.  `wrap [sep, sep]` is a legal `Deliv` (its interior is
    `balanced`: zero openers, zero closers), yet inside it `sep` is followed by `sep`, so `SepOk`
    fails.  The `.wrap` constructor discards exactly the structure `SepOk` needs ⇒ no projection. -/
theorem deliv_toSepOk_fails : ¬ (∀ l, Deliv l → SepOk l) := by
  intro h
  have hd : Deliv (Tok.opener :: ([Tok.sep, Tok.sep] ++ [Tok.closer])) :=
    Deliv.wrap [Tok.sep, Tok.sep] (by decide)
  -- the block is `[opener, sep, sep, closer]`; at i = 1 the token is `sep` but i+1 = 2 is `sep`
  exact absurd (h _ hd 1 (by decide) (by decide)) (by decide)

/-! ## The GRAMMAR producer, which keeps the scanned interior, supplies the field directly. -/

/-- **POSITIVE** — a producer that scanned the interior `content sep content` PROVES `SepOk` of the
    wrapped block `[opener, content, sep, content, closer]` directly: its lone `sep` (index 2) is
    followed by `content` (index 3).  This is the separate carrier field the grammar producer
    threads, never projected from `Deliv`. -/
theorem sepOk_of_scanned_wrap :
    SepOk (Tok.opener :: ([Tok.content, Tok.sep, Tok.content] ++ [Tok.closer])) := by
  intro i h hsep
  -- the block is `[opener, content, sep, content, closer]` (length 5); only i = 2 is a `sep`
  have hlen : (Tok.opener :: ([Tok.content, Tok.sep, Tok.content] ++ [Tok.closer])).length = 5 := by
    decide
  rw [hlen] at h
  rcases i with _ | _ | _ | _ | i
  · revert hsep h; decide +revert   -- i = 0 (opener): premise false
  · revert hsep h; decide +revert   -- i = 1 (content): premise false
  · revert hsep h; decide +revert   -- i = 2 (sep):     successor is content ✓
  · revert hsep h; decide +revert   -- i = 3 (content): premise false
  · exact absurd h (by omega)       -- i ≥ 4: out of range

#guard balanced [Tok.sep, Tok.sep] == true   -- the SepOk-violating interior is still `balanced`
#guard balanced [Tok.content] == true

end Tests.Reflections.FieldOnMultiproducerPredicate
