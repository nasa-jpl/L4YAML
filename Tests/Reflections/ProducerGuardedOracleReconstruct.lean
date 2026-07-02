/-!
# Reflection 292 — discharge a producer-guarded oracle by RECONSTRUCTING the descended guard
in place from the locator's own facts, never by re-running the locating descend-lemma

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`recseqentry_seqbracket_oracle`: the head-shape dispatch's recursive crux discharges a
**producer-guarded quantifier** — a universal over the matching close `j`, guarded by the
locator's output facts, that the `windowWidth_strongRecOn` IH must satisfy.

The trap: to run the IH on the descended interior `[lo+1, j)` you need the window guard there, and
the natural move is to call the *locating* descend-lemma — but that LOCATES its own close `j'` and
hands you a guard about `j'`, not the oracle's `j`, leaving a `j = j'` matching-close **uniqueness**
obligation. The fix is structural: the oracle already handed you `j` *together with the facts that
pin it*, so RECONSTRUCT the descended guard at that very `j` from those facts — no re-location, no
uniqueness proof.

The demo also models the residual the deep-guard pivot surfaced: a strengthened guard that
deliberately DROPPED a field (because its descend edge was the unprovable one) cannot supply that
field to the dispatch, so it reappears as a SEPARATE hypothesis — not a projection of the
strengthened guard.

* POSITIVE — `win_reconstruct` builds the descended guard at the handed-in `j` directly; the
  oracle discharge `oracle_discharge` feeds it to the IH; `reconstruct_fires` runs it on a real
  nested bracket. Parametric in `j`, so it works for whichever close the consumer located.
* NEGATIVE — `firstClose nested` (naive re-location) finds the INNER close `2`, not the outer
  bracket's matching close `3` the oracle was handed, so substituting the re-located witness is
  unsound without uniqueness; and `deep_lacks_succ` shows the dropped `succ` field is genuinely
  not recoverable from the strengthened guard `Deep`, so the dispatch must take `Full` (with
  `succ`) as its own hypothesis.
-/

namespace Tests.Reflections.ProducerGuardedOracleReconstruct

set_option autoImplicit false

/-- Toy token stream: openers / closers carry bracket delta; values/separators are neutral. -/
inductive Tok | opn | cls | val | sep
  deriving DecidableEq, Repr

/-- Bracket delta (toy of `flowBracketDelta`). -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _    => 0

/-- Range balance `bal l a b` over `[a, b)` (toy of `flowBracketBalance`). -/
def bal (l : List Tok) (a b : Nat) : Int :=
  ((l.drop a).take (b - a)).foldl (fun s t => s + delta t) 0

/-- Toy descended-window guard (the bracket half of the real `FlowBodyWindow`). -/
structure Win (l : List Tok) (lo hi : Nat) : Prop where
  lt       : lo < hi
  balanced : bal l lo hi = 0

/-- Stand-in for the per-window deliverable the IH produces (`RecSeqBody`). -/
def P (l : List Tok) (lo hi : Nat) : Prop := Win l lo hi

/-! ## POSITIVE — reconstruct the descended guard in place, then feed the IH

The oracle hands in `j` *together with* the facts that pin it (`lo+1 < j`, `bal l (lo+1) j = 0`).
`win_reconstruct` builds `Win` at THAT `j` directly — no `locate`, so no `j = locate …` obligation.
It is parametric in `j`, so it discharges the oracle for whichever close the consumer located. -/

/-- RECONSTRUCT-IN-PLACE: the descended guard at the handed-in close `j`, from the locator's facts. -/
theorem win_reconstruct (l : List Tok) (lo j : Nat)
    (h_lt : lo + 1 < j) (h_inner : bal l (lo + 1) j = 0) : Win l (lo + 1) j :=
  ⟨h_lt, h_inner⟩

/-- The producer-guarded oracle, DISCHARGED from the IH by reconstruct-in-place: for every close `j`
    the consumer's locator hands in (with its guard facts), build the interior guard and fire the IH.
    No call to a *locating* descend-lemma, hence no matching-close uniqueness proof. -/
theorem oracle_discharge (l : List Tok) (lo hi : Nat)
    (ih : ∀ lo' hi', Win l lo' hi' → P l lo' hi') :
    ∀ j, lo + 1 < j → j < hi → bal l (lo + 1) j = 0 → P l (lo + 1) j := by
  intro j h_lt _h_jhi h_inner
  exact ih (lo + 1) j (win_reconstruct l lo j h_lt h_inner)

/-- A real nested bracket: the OUTER opener at `0` matches the close at `3`; the inner pair is `1..2`. -/
def nested : List Tok := [.opn, .opn, .cls, .cls]

/-- The interior `[1, 3)` of the outer bracket is balanced (`opn cls`). -/
example : bal nested 1 3 = 0 := by decide

/-- The discharge fires on `nested` at the outer matching close `j = 3`, yielding the interior guard. -/
theorem reconstruct_fires : P nested 1 3 :=
  oracle_discharge nested 0 4 (fun _ _ h => h) 3 (by decide) (by decide) (by decide)

/-! ## NEGATIVE — re-locating finds a DIFFERENT witness than the one handed in

`firstClose` is the naive re-locator (first `cls`). On `nested` it returns the INNER close `2`, not
the outer bracket's matching close `3` the oracle was handed — so building the guard at the
re-located witness would target the wrong window. Substituting `firstClose l` for the handed-in `j`
is unsound without a matching-close uniqueness argument; `win_reconstruct` sidesteps it entirely. -/

/-- Naive re-location: the first closer's index. -/
def firstClose (l : List Tok) : Nat := l.findIdx (· == Tok.cls)

-- Re-location finds the INNER close `2`, not the outer matching close `3`.
#guard firstClose nested == 2

-- …so the re-located witness ≠ the handed-in close `3`: a uniqueness obligation the reconstruct
-- path never incurs.
#guard firstClose nested != 3

-- And the guard at the re-located inner witness `[1, 2)` is the WRONG window (not the oracle's
-- `[1, 3)`): `bal nested 1 2 = 1 ≠ 0`, so it isn't even balanced — re-location mistargets.
#guard bal nested 1 2 == 1

/-! ## NEGATIVE (second facet) — the field the strengthened guard DROPPED resurfaces as a hypothesis

`Deep` is the strengthened guard that carries only the restriction-stable balance (toy of
`FlowBodyContentDeep`, which dropped `bodySucc` because its descend edge was the unprovable one).
The dispatch's trailing-separator successor `succ` is NOT a field of `Deep` and is not derivable
from it — so it must be supplied by the un-pivoted `Full` guard (toy of `FlowBodyContent`). -/

/-- The strengthened guard — balance only, no trailing-separator `succ` field. -/
structure Deep (l : List Tok) (lo hi : Nat) : Prop where
  balanced : bal l lo hi = 0

/-- The un-pivoted guard — also carries the trailing-separator successor the dispatch consumes. -/
structure Full (l : List Tok) (lo hi : Nat) : Prop where
  balanced : bal l lo hi = 0
  succ     : hi = l.length ∨ l.getD hi .val = .sep

/-- A balanced window whose successor is NOT a separator (`val` follows the bracket). -/
def noSep : List Tok := [.opn, .cls, .val]

/-- `Deep` holds on `[0, 2)` of `noSep` (balanced)… -/
theorem deep_holds : Deep noSep 0 2 := ⟨by decide⟩

/-- …yet the successor at `2` is `val`, NOT `sep`, so `Deep` cannot supply the dispatch's `succ`:
    the dropped field is genuinely unrecoverable from the strengthened guard. -/
theorem deep_lacks_succ : ¬ (noSep.getD 2 Tok.val = Tok.sep) := by decide

/-- The dispatch therefore takes `Full` (with `succ`) as its OWN hypothesis — available where the
    successor really is a separator. -/
theorem full_supplies_succ : Full [.opn, .cls, .sep] 0 2 :=
  ⟨by decide, Or.inr (by decide)⟩

end Tests.Reflections.ProducerGuardedOracleReconstruct
