/-!
# Reflection 400 — a closure algebra's BRIDGE hypothesis is a WEAKER fact than the rich
field it builds, and is often a CONSEQUENCE of an existing INVARIANT conjunct of the carrier:
test derivability before adding+threading a new structural field.

Self-contained core-Lean toy of L4YAML R400.  The real situation: the `OpenerAdj` closure
algebra's `OpenerAdj_append` carries a bridge `h_tail : a`'s last token ≠ opener.  R397 had ruled
the FULL `OpenerAdj` field orthogonal to the balance carrier — but the BRIDGE is a weaker boundary
fact that the carrier's `EntryUnit` balance invariant DOES pin.

Here `delta`/`balance` ~ `flowBracketDelta`/`pbalance`; `UnitEntry` ~ `EntryUnit`
(`balance = 0 ∧ every proper nonempty prefix ≥ 1`); `lastNotOpener_of_unit` ~
`lastNonOpener_of_entryUnit`.

POSITIVE A (`lastNotOpener_of_unit`): the bridge (last token ≠ `.opn`) is DERIVED from the
  `UnitEntry` invariant alone — no new field needed.  An opener last-token would force the
  `length-1` prefix to balance `-1` (or a singleton to balance `+1 ≠ 0`), both contradicting the
  invariant.
POSITIVE B (`coerce_richunit`): a PARALLEL richer predicate `RichUnit = UnitEntry ∧ tag` down-coerces
  to `UnitEntry ∧ lastNotOpener`, discharging the new `lastNotOpener` conjunct from the SHARED
  `UnitEntry` conjunct — NOT from the extra `tag`, and without mirroring a field into `RichUnit`.
NEGATIVE (`cls_opn_not_unit` / `cls_opn_last_is_opn`): `[cls, opn]` is balance-`0` yet ENDS in `.opn`;
  it is genuinely NOT a `UnitEntry` (prefix `[cls]` balances `-1 < 1`), so `lastNotOpener_of_unit`
  correctly does not apply — the invariant is load-bearing, the bridge is not free.
-/

namespace Tests.Reflections.BridgeDerivableFromInvariant

set_option autoImplicit false

/-- Three tokens with bracket deltas (`.opn` = `+1`, `.cls` = `-1`, `.content` = `0`). -/
inductive Tok | opn | cls | content
  deriving DecidableEq, Repr, BEq, Inhabited

def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | .content => 0

def balance (l : List Tok) : Int := l.foldl (fun acc t => acc + delta t) 0

theorem balance_nil : balance [] = 0 := rfl

theorem balance_singleton (t : Tok) : balance [t] = delta t := by simp [balance]

/-- Folding from a nonzero seed shifts by that seed (the `foldl_add_shift` analog). -/
theorem foldl_shift (b : List Tok) (c : Int) :
    b.foldl (fun acc t => acc + delta t) c = c + b.foldl (fun acc t => acc + delta t) 0 := by
  induction b generalizing c with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (c + delta x), ih (0 + delta x)]; omega

theorem balance_append (a b : List Tok) : balance (a ++ b) = balance a + balance b := by
  simp only [balance, List.foldl_append]
  rw [foldl_shift b (a.foldl _ 0)]

/-- The carrier invariant (`EntryUnit` analog): balance `0`, every proper nonempty prefix `≥ 1`. -/
def UnitEntry (l : List Tok) : Prop :=
  balance l = 0 ∧ ∀ (i : Nat), 0 < i → i < l.length → balance (l.take i) ≥ 1

/-- **POSITIVE A — the bridge is DERIVED from the invariant, not added as a field.**
    A `UnitEntry`'s last token is never an opener. -/
theorem lastNotOpener_of_unit (l : List Tok) (h : UnitEntry l) :
    ∀ (hla : 0 < l.length), (l[l.length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn := by
  intro hla hopen
  obtain ⟨h_bal, h_prefix⟩ := h
  have hne : l ≠ [] := by intro hh; rw [hh] at hla; simp at hla
  have hgl : l.getLast hne = l[l.length - 1]'(Nat.sub_lt hla Nat.one_pos) :=
    List.getLast_eq_getElem hne
  have hopen' : l.getLast hne = .opn := by rw [hgl]; exact hopen
  have hsplit : balance l = balance (l.take (l.length - 1)) + delta (l.getLast hne) := by
    have hh := List.take_append_getLast l hne
    calc balance l
        = balance (l.take (l.length - 1) ++ [l.getLast hne]) := by rw [hh]
      _ = balance (l.take (l.length - 1)) + balance [l.getLast hne] := balance_append _ _
      _ = balance (l.take (l.length - 1)) + delta (l.getLast hne) := by rw [balance_singleton]
  have hdelta : delta (l.getLast hne) = 1 := by rw [hopen']; rfl
  have hneg : balance (l.take (l.length - 1)) = -1 := by rw [hdelta] at hsplit; omega
  have hpos : balance (l.take (l.length - 1)) ≥ 0 := by
    rcases Nat.eq_zero_or_pos (l.length - 1) with h0 | hpos
    · have hz : balance (l.take (l.length - 1)) = 0 := by rw [h0, List.take_zero, balance_nil]
      omega
    · have hp := h_prefix (l.length - 1) hpos (by omega); omega
  omega

/-- **POSITIVE B — the parallel-predicate down-coercion discharges the new field from the
    SHARED conjunct.**  `RichUnit` carries an extra `tag`; coercing to `UnitEntry ∧ lastNotOpener`
    derives `lastNotOpener` from the `UnitEntry` conjunct — `tag` is dropped, never mirrored. -/
def RichUnit (l : List Tok) : Prop := UnitEntry l ∧ l ≠ []   -- the `≠ []` stands in for `tag`

theorem coerce_richunit (l : List Tok) (h : RichUnit l) :
    UnitEntry l ∧ ∀ (hla : 0 < l.length), (l[l.length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn :=
  ⟨h.1, lastNotOpener_of_unit l h.1⟩

/-- **NEGATIVE — without the invariant the bridge fails; the invariant is load-bearing.**
    `[cls, opn]` is balance-`0` but ENDS in `.opn`, and is genuinely not a `UnitEntry`. -/
theorem cls_opn_balanced : balance [Tok.cls, .opn] = 0 := by decide

theorem cls_opn_last_is_opn : ([Tok.cls, .opn])[1] = Tok.opn := by decide

theorem cls_opn_not_unit : ¬ UnitEntry [Tok.cls, .opn] := by
  intro h
  have hp := h.2 1 (by decide) (by decide)   -- prefix `[cls]` must balance ≥ 1
  simp only [List.take_succ_cons, List.take_zero] at hp
  rw [balance_singleton] at hp
  exact absurd hp (by decide)

-- A genuine `UnitEntry` (`[opn, content, cls]`) and a non-opener last token.
#guard ([Tok.opn, .content, .cls])[2]! == Tok.cls
#guard balance [Tok.opn, .content, .cls] == 0
-- The negative: balanced but opener-tailed (hence not a UnitEntry).
#guard balance [Tok.cls, .opn] == 0
#guard ([Tok.cls, .opn])[1]! == Tok.opn

end Tests.Reflections.BridgeDerivableFromInvariant
