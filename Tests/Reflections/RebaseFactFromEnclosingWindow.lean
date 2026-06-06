/-!
# Reflection 304 — a window-relative fact RE-BASES from its enclosing window by balance-`0` composition; the rebase precondition is load-bearing

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`(i'-b-descend-direct-facts)`: the carrier's separator facts at an arbitrary gated sub-window
`[a,b)` do NOT need a per-window `SafeBodyUnit` (R303 showed that route is FALSE); they re-base
from the ENCLOSING seq interior's same fact by balance-`0` composition.

The real situation: `bodySuccFact tokens a b` ("a depth-`0` non-separator entry-end is followed by a
separator or closes the window") holds at every window the gate `SeqTypedInterior` admits. The gate's
enclosing-seq conjunct guarantees the window start `a` sits at the enclosing sequence's TOP level
(`flowBracketBalance tokens loS a = 0`), so the enclosing seq's own `bodySuccFact` over `[loS,hiS)`
transfers to `[a,b)` verbatim — `balance loS (k+1) = balance loS a + balance a (k+1) = 0 + 0` for
every interior end `k`, and the enclosing close disjunct `k+1 = hiS` collapses to `k+1 = b` because
`k < b ≤ hiS`. The rebase precondition `balance loS a = 0` is load-bearing: a `#guard`-backed probe on
`[{a: 1}, 2]` showed every window where the fact FAILS (a mapping key followed by `:`, not a
separator) is exactly one whose start is NOT at a seq top level — non-gated, `balance loS a ≠ 0`.

Toy substrate: tokens are `opn`/`cls`/`sep`/`con`/`val` (open bracket, close, separator, content,
the mapping `:`). `bal` is a telescoping prefix-sum difference (so composition is unconditional and
free). `Succ` is the toy `bodySuccFact`. The KERNEL `succ_rebase` is the toy of `bodySuccFact_rebase`.
The seq list witnesses the POSITIVE (rebase transfers the fact); the map list witnesses the NEGATIVE
(at a position whose start is NOT at the enclosing top level — `bal ≠ 0` — the fact fails and the
rebase precondition correctly does not hold).
-/

namespace Tests.Reflections.RebaseFactFromEnclosingWindow

set_option autoImplicit false

/-- Toy tokens: `opn`/`cls` are brackets (delta `±1`), `sep` a separator (the toy `.flowEntry`),
    `con` a content token, `val` the mapping `:` (a non-separator that breaks `Succ` inside a map). -/
inductive Tok | opn | cls | sep | con | val
  deriving DecidableEq, Inhabited, Repr

def delta : Tok → Int
  | .opn => 1 | .cls => -1 | _ => 0

def isSep : Tok → Bool
  | .sep => true | _ => false

/-- Prefix bracket-sum of the first `n` tokens. -/
def psum (T : List Tok) (n : Nat) : Int :=
  (T.take n).foldl (fun acc t => acc + delta t) 0

/-- Window balance as a prefix-sum difference — telescoping, so composition is FREE. -/
def bal (T : List Tok) (a b : Nat) : Int := psum T b - psum T a

/-- **Unconditional composition** (the toy of `flowBracketBalance_compose`): no `a ≤ m ≤ b` needed,
    because `bal` is a prefix-sum difference. This is the one fact the rebase proof consumes. -/
theorem bal_compose (T : List Tok) (a m b : Nat) :
    bal T a b = bal T a m + bal T m b := by
  simp only [bal]; omega

/-- **The toy `bodySuccFact`** over a window `[a,b)`: every depth-`0` (relative to `a`) non-separator
    position `k` either closes the window or is immediately followed by a separator. -/
def Succ (T : List Tok) (a b : Nat) : Prop :=
  ∀ k, a ≤ k → k < b → bal T a (k + 1) = 0 → isSep (T[k]!) = false →
    k + 1 = b ∨ (k + 1 < b ∧ isSep (T[k + 1]!) = true)

/-- **THE KERNEL — `Succ` RE-BASES from the enclosing window** (toy of `bodySuccFact_rebase`).
    Given the enclosing `Succ T loS hiS` and a sub-window `[a,b) ⊆ [loS,hiS)` whose start `a` is at the
    enclosing top level (`bal T loS a = 0`), `Succ T a b` follows — pure composition + `omega`, no
    per-window structure. The enclosing close disjunct `k+1 = hiS` collapses to `k+1 = b` because
    `k < b ≤ hiS`. -/
theorem succ_rebase (T : List Tok) (loS a b hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b : b ≤ hiS) (h_bal0 : bal T loS a = 0)
    (h_enc : Succ T loS hiS) : Succ T a b := by
  intro k hak hkb hbalk hns
  have hk_hiS : k < hiS := Nat.lt_of_lt_of_le hkb h_b
  have hbal_enc : bal T loS (k + 1) = 0 := by
    have hc := bal_compose T loS a (k + 1)
    rw [h_bal0, hbalk] at hc; omega
  rcases h_enc k (Nat.le_trans h_loS_a hak) hk_hiS hbal_enc hns with h | ⟨h', heq⟩
  · exact Or.inl (by omega)
  · rcases Nat.lt_or_ge (k + 1) b with hlt | hge
    · exact Or.inr ⟨hlt, heq⟩
    · exact Or.inl (by omega)

/-! ## Concrete witnesses -/

-- A SEQ body `[ con , con ]`: content comma-separated.  `Succ` holds on the interior `[1,4)`.
def seqT : List Tok := [.opn, .con, .sep, .con, .cls]

-- A MAP body `{ con : con }`: a key followed by `val` (the `:`), NOT a separator.  `Succ` FAILS
-- inside it — and the failing window's start sits at depth `1`, not the enclosing top level.
def mapT : List Tok := [.opn, .con, .val, .con, .cls]

/-- **Usability** — the kernel applied at a concrete sub-window. Given the enclosing fact over the
    inner seq body `[1,4)`, the last-entry sub-window `[3,4)` (start `3` at depth `0`: `bal seqT 1 3 = 0`)
    inherits it with no re-derivation. -/
example (h : Succ seqT 1 4) : Succ seqT 3 4 :=
  succ_rebase seqT 1 3 4 4 (by decide) (by decide) (by decide) h

-- Bool version of `Succ` for decidable enumeration.
def succB (T : List Tok) (a b : Nat) : Bool :=
  (List.range b).all fun k =>
    if a ≤ k && k < b then
      if (bal T a (k + 1) == 0) && (isSep (T[k]!) == false) then
        (k + 1 == b) || ((k + 1 < b) && (isSep (T[k + 1]!) == true))
      else true
    else true

-- POSITIVE: the enclosing seq interior `[1,4)` satisfies `Succ`, and so does the rebased sub-window
-- `[3,4)` whose start `3` is at the enclosing top level (`bal seqT 1 3 = 0`).
#guard succB seqT 1 4 = true
#guard succB seqT 3 4 = true
#guard bal seqT 1 3 = 0          -- a = 3 IS at the enclosing top level → rebase applies

-- NEGATIVE: inside the map, `Succ` fails on `[1,4)` (the key at `1` is followed by `val`, not a
-- separator).  The failing window's start `1` is NOT at the enclosing top level: `bal mapT 0 1 = 1 ≠ 0`.
-- So the rebase precondition `h_bal0` correctly does NOT hold there — it is load-bearing, exactly as
-- the real gate's enclosing-seq conjunct excludes precisely the mapping-key failure windows.
#guard succB mapT 1 4 = false
#guard bal mapT 0 1 = 1          -- ≠ 0: position 1 is inside the bracket, not at top level

/-- NEGATIVE capstone — `Succ mapT 1 4` is genuinely FALSE: the key `con` at index `1` is a depth-`0`
    non-separator whose successor is `val` (`isSep val = false`), so neither disjunct holds. -/
theorem not_succ_map : ¬ Succ mapT 1 4 := by
  intro h
  rcases h 1 (Nat.le_refl 1) (by decide) (by decide) (by decide) with h1 | ⟨_, h2⟩
  · omega
  · exact absurd h2 (by decide)

end Tests.Reflections.RebaseFactFromEnclosingWindow
