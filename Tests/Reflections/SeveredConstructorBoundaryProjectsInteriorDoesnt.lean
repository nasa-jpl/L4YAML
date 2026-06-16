/-!
# Reflection 455 — a constructor that SEVERS the recursion (storing only a weak balance predicate
# in place of the recursive sub-structure) still admits the BOUNDARY projections (last-token facts)
# but BLOCKS the INTERIOR projections (every-seat adjacency facts).  Which member of a projection
# family is derivable from the deliverable is decided by whether the fact reads the boundary or the
# interior — not by the type's overall "recursiveness".

Self-contained (core Lean, no `L4YAML` import) toy of the R455 finding, made while completing the
`RecMapBody` projection family for the R454 `mapRec` programme.

Context.  The map arms of the emitter producer must build, for the wrapped map block `{ body }`, the
adjacency facts `OpenerAdj`/`SepAdj` AND the boundary facts last-token-`≠ [` / last-token-`≠ ,`.
The natural hope (collapsing the whole assembler-strengthening cascade) was: since the assembler
already produces `RecMapBody body`, DERIVE all four facts from `RecMapBody` via projection methods,
the way `RecSeqBody.lastNonOpener`/`.openerAdjHead` are derived.  R455 found this works for HALF the
family and is IMPOSSIBLE for the other half — and the toy below proves exactly why.

The asymmetry.  `RecSeqEntry` has a FLAT `map` constructor that stores only `WellBracketed interior`
(the R453/R454 severance: the flat `.map` keeps balance but DROPS the recursive `RecMapBody`).

  * `WellBracketed` does NOT imply `OpenerAdj`: a balanced block can still seat a `[` next to a
    non-content token.  So `OpenerAdj`/`SepAdj` — which inspect EVERY interior `[`/`,` seat — are
    NOT recoverable from a flat-`map` entry, hence not from `RecMapBody` either.  They must stay
    SCAN-THREADED (proven by the actual emit, where the tokens really are well-formed).
  * The LAST token, by contrast, is the constructor's stored `cl`/value-end — a BOUNDARY datum fixed
    by the constructor SHAPE, blind to the severed interior.  So `lastNonOpener`/`lastNonSep` ARE
    derivable from `RecMapBody` (via the value entry's balance-based `EntryUnit`), flat `.map` and
    all.  Those four landed this round (`RecMapBody.getLast?_not_opener`/`.lastNonOpener` + sep twins).

This toy mirrors that exactly with a two-token-cheaper alphabet:

* `Weak`        — the balance-only predicate the severed constructor stores (mirror `WellBracketed`),
                  here `fun _ => True`: it constrains NOTHING about interior adjacency.
* `E`           — the entry type (mirror `RecSeqEntry`): `scalar`, a STRUCTURAL `wrapRec` (interior
                  is a recursive `E`), and a SEVERED `wrapFlat` (interior is only `Weak`).
* `E.last_not_bad`    — the BOUNDARY projection: derivable for ALL constructors, `wrapFlat` included,
                        because the last token is the stored close `cl`, not the interior.
* `interior_not_derivable` — the INTERIOR projection (`bad ∉ l`, the every-seat analogue of
                        `OpenerAdj`) is NOT a theorem: `wrapFlat [bad] trivial` is a legal `E` whose
                        interior IS `bad`.  The severed constructor manufactures the counterexample.

The law: a deliverable's projection family splits by READ LOCUS.  Boundary reads survive any interior
severance (`[[ref-severed-edge-bounds-navigator-domain]]` / `[[ref-stored-vs-projected-severs-recursion-edge]]`);
interior reads do not, and must be threaded from whatever proof DID see the interior (the scan).
Sharpens `[[ref-complete-projection-family-for-new-member]]`: completing a new member's family means
completing the BOUNDARY half off the type; the interior half is owed elsewhere.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.SeveredConstructorBoundaryProjectsInteriorDoesnt

/-- Toy alphabet: `sc` content scalar, `op`/`cl` the wrap open/close, `bad` an interior token that an
    every-seat adjacency property would forbid (mirror: a `[` seated next to a non-content token). -/
inductive Tok where
  | sc | op | cl | bad
deriving DecidableEq

/-- The balance-only predicate the SEVERED constructor stores (mirror `WellBracketed`).  It says
    nothing about interior adjacency — exactly the severance: balance kept, structure dropped. -/
def Weak (_ : List Tok) : Prop := True

/-- The entry type (mirror `RecSeqEntry`).  `wrapRec` keeps the recursive sub-structure; `wrapFlat`
    SEVERS it, storing only `Weak`. -/
inductive E : List Tok → Prop where
  | scalar : E [Tok.sc]
  | wrapRec (interior : List Tok) (h_rec : E interior) :
      E (Tok.op :: (interior ++ [Tok.cl]))
  | wrapFlat (interior : List Tok) (h_weak : Weak interior) :
      E (Tok.op :: (interior ++ [Tok.cl]))

/-! ### The BOUNDARY projection — derivable for ALL constructors, severance and all. -/

/-- **Last token is never `bad`** — the boundary projection (mirror `RecMapBody.getLast?_not_opener`
    / `.lastNonOpener`).  Provable uniformly, INCLUDING the severed `wrapFlat`: the last token is the
    constructor's stored close `cl` (a boundary datum fixed by the SHAPE), so the severed interior is
    never consulted.  This is why `RecMapBody.lastNonOpener`/`.lastNonSep` landed off the type. -/
theorem E.last_not_bad : {l : List Tok} → E l → ∃ t, l.getLast? = some t ∧ t ≠ Tok.bad
  | _, .scalar => ⟨Tok.sc, rfl, by decide⟩
  | _, .wrapRec interior _ =>
      ⟨Tok.cl, by rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_concat], by decide⟩
  | _, .wrapFlat interior _ =>
      ⟨Tok.cl, by rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_concat], by decide⟩

/-! ### The INTERIOR projection — NOT derivable; the severed constructor refutes it. -/

/-- **`bad` can appear in the interior** — the every-seat interior property (the `OpenerAdj`/`SepAdj`
    analogue) is NOT a consequence of `E`.  The severed `wrapFlat` admits ANY `Weak` interior, and
    `Weak [bad]` holds, so `E [op, bad, cl]` is inhabited with `bad` interior.  Mirror of: a flat
    `.map` storing only `WellBracketed` cannot yield `OpenerAdj`, so the body adjacency facts must be
    SCAN-THREADED, not projected from `RecMapBody`. -/
theorem severed_admits_bad_interior : E (Tok.op :: ([Tok.bad] ++ [Tok.cl])) :=
  E.wrapFlat [Tok.bad] trivial

/-- The interior projection `∀ l, E l → bad ∉ l` is FALSE — refuted by the severed witness. -/
theorem interior_not_derivable : ¬ (∀ l, E l → Tok.bad ∉ l) := by
  intro h
  have hbad : Tok.bad ∉ (Tok.op :: ([Tok.bad] ++ [Tok.cl])) :=
    h _ severed_admits_bad_interior
  exact hbad (by decide)

/-! ### The law, packaged. -/

/-- **The finding in one proposition.**  Over the SAME severed type `E`: the boundary projection is
    a theorem (derivable off the deliverable, severance and all), while the interior projection is
    refutable (the severed constructor manufactures the counterexample).  A projection family splits
    by READ LOCUS — boundary reads survive severance, interior reads are owed to whatever proof saw
    the interior.  Sharpens `[[ref-complete-projection-family-for-new-member]]` and applies
    `[[ref-stored-vs-projected-severs-recursion-edge]]`. -/
theorem boundary_projects_interior_doesnt :
    (∀ l, E l → ∃ t, l.getLast? = some t ∧ t ≠ Tok.bad)   -- boundary: derivable
    ∧ ¬ (∀ l, E l → Tok.bad ∉ l) :=                        -- interior: not derivable
  ⟨fun _ h => h.last_not_bad, interior_not_derivable⟩

end Tests.Reflections.SeveredConstructorBoundaryProjectsInteriorDoesnt
