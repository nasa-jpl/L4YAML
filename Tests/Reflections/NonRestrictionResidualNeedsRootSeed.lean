/-!
# Reflection 296 — a non-restriction residual needs a ROOT SEED, not a stronger local invariant

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`flowBodyContent_bodySucc_of_part6`: when a fact the recursion needs is NOT a subset-restriction of
itself across the descend edge, NO local guard can carry it — so do not chase a stronger local
invariant; seed its ROOT instance from existing infra and recognize the descended instances as a
bracket-TYPE-context problem.

The contrast that makes the rule:

* `AfterOpener` (toy of `FlowBodyContentDeep`'s `openerContentStart` / `feContentStart`) is **all-depth
  and balance-free** — it quantifies over EVERY position irrespective of any balance condition — so it
  RESTRICTS to any sub-window by subset (`afterOpener_restrict`, the three-line descend/advance edges).
* `Depth0Sep` (toy of `bodySucc`) is keyed on a **depth-`0` balance condition** (`bal lo (k+1) = 0`,
  balance measured FROM the window origin `lo`).  It is provably NOT a subset-restriction: on the
  witness `[ a b ]` (`wt`: `opn scal scal cls`) the parent window `[0,4)` SATISFIES it (its only
  balanced-prefix end is the close at `k = 3`), yet the descended interior `[1,3)` VIOLATES it (there
  `bal 1 2 = 0` fires on the scalar at `k = 1`, which is not followed by a separator).  The child's
  depth-`0` is the parent's depth-`1` — `bal 1 · = bal 0 · − bal 0 1 = bal 0 · − 1` — a level the
  parent's field never speaks of.  So `parent_holds ∧ ¬ child_holds` for the SAME token stream: the
  fact does not descend, no local carrier threads it.

* POSITIVE root-seed move — `bridge_checked_to_bang` is the toy of the landed lemma: existing infra
  delivers the root fact with bounds-checked indexing (`T[k]'h`); the consumer wants panic indexing
  (`T[k]!`); the bridge is a pure `getElem!_pos` conversion.  Pins the base case from what infra
  already provides, leaving only the (genuinely different) descended-window provenance.
-/

namespace Tests.Reflections.NonRestrictionResidualNeedsRootSeed

set_option autoImplicit false

/-- Toy token stream alphabet. -/
inductive Tok | opn | cls | comma | scal
  deriving DecidableEq, Repr, Inhabited

/-- Bracket delta: `[`/`{` open `+1`, `]`/`}` close `-1`, content `0`. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _    => 0

/-- Prefix balance from `0` to `m` (sum of deltas at positions `0 .. m-1`). -/
def balAux (tok : Nat → Tok) : Nat → Int
  | 0       => 0
  | (m + 1) => balAux tok m + delta (tok m)

/-- Window balance from `lo` to `m` as a prefix difference (toy of `flowBracketBalance`). -/
def bal (tok : Nat → Tok) (lo m : Nat) : Int := balAux tok m - balAux tok lo

/-! ## POSITIVE — an all-depth, balance-FREE field RESTRICTS by subset (the descend edge is trivial) -/

/-- Toy of `FlowBodyContentDeep`'s opener field: after every opener strictly inside `[lo, hi)`, the
    next token is not a close.  No balance condition — quantifies all depths. -/
def AfterOpener (lo hi : Nat) (tok : Nat → Tok) : Prop :=
  ∀ k, lo ≤ k → k + 1 < hi → tok k = .opn → tok (k + 1) ≠ .cls

/-- Because it is balance-free, it is a pure SUBSET restriction — exactly why
    `flowBodyContentDeep_descend` / `_advance` are three-line proofs. -/
theorem afterOpener_restrict {lo hi a b : Nat} {tok : Nat → Tok}
    (h : AfterOpener lo hi tok) (h1 : lo ≤ a) (h2 : b ≤ hi) :
    AfterOpener a b tok := by
  intro k hk1 hk2 hop
  exact h k (by omega) (by omega) hop

/-! ## NEGATIVE — a depth-`0`-keyed field is NOT a subset restriction (no local carrier descends) -/

/-- Toy of `bodySucc`: a depth-`0` balanced-prefix end that is not a separator is an entry END.
    Keyed on `bal lo (k+1) = 0` — balance FROM the window origin `lo`. -/
def Depth0Sep (lo hi : Nat) (tok : Nat → Tok) : Prop :=
  ∀ k, lo ≤ k → k < hi → bal tok lo (k + 1) = 0 → tok k ≠ .comma →
    (k + 1 = hi ∨ tok (k + 1) = .comma)

/-- The witness `[ a b ]` — adjacent scalars, no comma (`WellTyped`-accepted, not comma-separated). -/
def wt : Nat → Tok
  | 0 => .opn
  | 1 => .scal
  | 2 => .scal
  | 3 => .cls
  | _ => .cls

/-- The PARENT window `[0,4)` satisfies the depth-`0` field: its only balanced-prefix end is the close
    at `k = 3` (`bal 0 4 = 0`), which ends the window (`3 + 1 = 4`). -/
theorem parent_holds : Depth0Sep 0 4 wt := by
  intro k hk0 hk4 hbal _hc
  match k, hk4 with
  | 0, _ => exact absurd hbal (by decide)
  | 1, _ => exact absurd hbal (by decide)
  | 2, _ => exact absurd hbal (by decide)
  | 3, _ => exact Or.inl rfl
  | (n + 4), h => exact absurd h (by omega)

/-- …yet the DESCENDED interior `[1,3)` VIOLATES it: there `bal 1 2 = 0` fires on the scalar at `k = 1`
    (the child's depth-`0` = the parent's depth-`1`, silent in the parent), and that scalar is followed
    by another scalar, not a separator or the window end.  Parent holds, child fails, SAME `tok` — so
    the fact is not a subset restriction, and no local `{bodySucc, …}` carrier can descend. -/
theorem child_fails : ¬ Depth0Sep 1 3 wt := by
  intro h
  rcases h 1 (by omega) (by omega) (by decide) (by decide) with h1 | h2
  · omega
  · exact absurd h2 (by decide)

/-! ## POSITIVE — the root-seed move: bridge the infra's checked indexing to the consumer's panic form -/

/-- Toy of `flowBodyContent_bodySucc_of_part6`: existing infra delivers the root fact with
    bounds-checked indexing (`T[k]'h`); the consumer (`flowBodyContent_of_deep`) wants panic indexing
    (`T[k]!`).  The bridge is a pure `getElem!_pos` conversion — no re-derivation, pinning the base
    case from what infra already provides. -/
theorem bridge_checked_to_bang (T : Array Tok)
    (h : ∀ k, (hk : k < T.size) → (T[k]'hk) ≠ .comma) :
    ∀ k, k < T.size → T[k]! ≠ .comma := by
  intro k hk
  rw [getElem!_pos T k hk]
  exact h k hk

-- The balance values that drive the negative: parent's only zero-prefix is at the close (k=3);
-- the descended origin shifts every balance down by one unmatched opener (bal 0 1 = 1).
#guard bal wt 0 4 == 0      -- parent: close at k=3 returns to 0
#guard bal wt 0 1 == 1      -- one unmatched opener: parent depth-0 never fires inside
#guard bal wt 1 2 == 0      -- child depth-0 = parent depth-1: fires on the interior scalar
#guard decide (wt 2 = Tok.comma) == false

end Tests.Reflections.NonRestrictionResidualNeedsRootSeed
