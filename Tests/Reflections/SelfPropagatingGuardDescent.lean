/-!
# Reflection 436 — a self-propagating guard's descent lemma is usually already built

Self-contained (core Lean, no `L4YAML` import) toy of the R436 finding.

Context.  R435 ([[ref-probe-the-goal-not-the-intermediate]]) machine-checked that the sorry GOAL
`FlowSubrangesOk tokens` is FALSE: its window-quantifier omits the interior Dyck floor, so cross-matched
windows leak in and `SeqBodyProps.content_start` fails.  The fix adds the floor as a guard at the
DEFINITION — which forces re-proving the parser CONSUMER `flow_parser_ok_of_structure` to supply the floor
at every nested `.seq`/`.map` descend (8 query sites).

The R436 finding.  Before re-proving the consumer, SCOPE it by looking for the added guard's
DESCENT/RESTRICTION lemma.  The Dyck floor is *self-propagating* — an outer window's floor manufactures
each inner window's floor at a depth-`0` opener — and its descent lemma was ALREADY BUILT, twice, for two
sibling consumers:

* `flowBracketBalance_matching_close` (the parser locator) yields the matching close `j` together with
  the depth-`1` interior invariant `balance lo i ≥ 1` over `(k, j]` (its fifth conjunct);
* `flowBracketBalance_interior_dyck` (built to feed `WellTyped_subrange`) re-bases that depth-`1` floor to
  the inner depth-`0` floor `balance (k+1) p ≥ 0`.

Composing them (`flowBracketBalance_inner_floor`) manufactures the inner floor in four lines — no new
combinatorics.  The redirect's true cost is THREADING + EXPOSING the guard, not DERIVING it.

The caveat (why EXPOSE, not reconstruct-in-place).  The descent-output fields (`bracket_seq` etc.) publish
only `balance (k+1) j = 0`, which does NOT pin `j` as the first-return: a *cross-matched* inner `j`
balances too.  So the consumer cannot reconstruct the inner floor at the handed-in `j`
([[ref-reconstruct-in-place-over-relocate]], one level down).  The PRODUCER (which knows the genuine
structure) must EXPOSE the inner floor on the field; the consumer reads it off.

Reusable rule: a self-propagating guard's restriction lemma is usually already built (some sibling
consumer needed the structure); the redirect's cost is THREADING + EXPOSING it on descent-output fields,
not deriving from scratch.

The toy below: PART 1 composes two pre-built descent pieces into the inner-floor manufacturer; PART 2
shows concretely that "balance returns to 0 at `j`" underdetermines the first-return `j` (two distinct
`j`), which is why the guard must be EXPOSED on the field rather than re-derived by the consumer.
-/

namespace Tests.Reflections.SelfPropagatingGuardDescent

set_option autoImplicit false

/-! ## PART 1 — compose the two pre-built descent pieces into the inner-floor manufacturer -/

/-- A running-balance model: `psum a b` is the balance of the window `[a, b)`, additive over a split
    (`add` is the one structural fact, the toy of `flowBracketBalance_compose`). -/
structure Balance where
  psum : Nat → Nat → Int
  add  : ∀ a b c, psum a c = psum a b + psum b c

/-- The self-propagating guard: the Dyck FLOOR of `[lo, hi)` — every prefix balance is `≥ 0`. -/
def Floor (B : Balance) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → B.psum lo i ≥ 0

/-- **PRE-BUILT PIECE A** — the re-base (toy of `flowBracketBalance_dyck_shift`).  A depth-`d` floor over
    `[s, hi)` (start `s` sits at depth `d`) re-bases to a depth-`0` LOCAL floor `Floor s hi`.  By
    additivity `psum s p = psum lo p − psum lo s = psum lo p − d ≥ 0`. -/
theorem rebase (B : Balance) (lo s hi : Nat) (d : Int)
    (h_depth : B.psum lo s = d)
    (h_floor : ∀ p, s ≤ p → p ≤ hi → B.psum lo p ≥ d) :
    Floor B s hi := by
  intro p h_sp h_ph
  have hc := B.add lo s p
  have hf := h_floor p h_sp h_ph
  omega

/-- **The composition** — toy of `flowBracketBalance_inner_floor`.  What the forward locator
    (`matching_close`, PIECE B) HANDS US is the depth-`1` interior invariant `h_pos` over `[k+1, j]` plus
    the depth just after the opener (`psum 0 (k+1) = 1`).  Re-basing it with PIECE A manufactures the
    INNER window's own depth-`0` floor `Floor (k+1) j` — the floor a floor-guarded descend demands. -/
theorem inner_floor (B : Balance) (k j : Nat)
    (h_k1_depth : B.psum 0 (k + 1) = 1)                  -- depth just after the depth-0 opener at k
    (h_pos : ∀ i, k + 1 ≤ i → i ≤ j → B.psum 0 i ≥ 1) :  -- the locator's fifth conjunct
    Floor B (k + 1) j :=
  rebase B 0 (k + 1) j 1 h_k1_depth h_pos

/-! ## PART 2 — why the guard must be EXPOSED on the field, not re-derived by the consumer -/

/-- Deltas of a `[][]`-shaped stream: open, close, open, close. -/
def deltas : List Int := [1, -1, 1, -1]

/-- The prefix balance `bal n = Σ deltas[0:n]` (toy of `flowBracketBalance tokens 0 n`). -/
def bal (n : Nat) : Int := (deltas.take n).foldl (· + ·) 0

#guard bal 0 == 0
#guard bal 1 == 1
#guard bal 2 == 0     -- FIRST return to 0 (matching close of the opener at index 0 is at index 1)
#guard bal 3 == 1
#guard bal 4 == 0     -- a LATER return to 0 — also balances, but is NOT the first-return

/-- **The field underdetermines the witness.**  "balance returns to `0` at `j`" holds at BOTH `j = 2`
    and `j = 4`, so a consumer reading only `psum 0 j = 0` off a descent-output field cannot tell which
    `j` is the genuine matching close — hence cannot reconstruct the inner floor at the handed-in `j`.
    The producer must EXPOSE the floor on the field. -/
theorem field_underdetermines_first_return :
    bal 2 = 0 ∧ bal 4 = 0 ∧ (2 : Nat) ≠ 4 :=
  ⟨by decide, by decide, by decide⟩

end Tests.Reflections.SelfPropagatingGuardDescent
