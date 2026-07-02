/-!
# Reflection 313 — a FLOOR-BLIND gate (balance-0 only) admits CROSS-SIBLING windows the deliverable cannot inhabit, so the carrier is FALSE on a valid witness; the missing local-Dyck floor excludes exactly those windows and discharges the consumer's containment bound for free

Self-contained (core Lean) toy of the moment `(i'-b-locator-glue-close)` was de-risked.

The real situation: a separator carrier `SeqInteriorSeparators tokens lo hi` quantifies, over every
gated sub-window `[a,b)`, a `bodySuccFact`.  The gate `SeqTypedInterior` was two conjuncts —
depth-`0`-balanced (`balance a b = 0`) and seq-enclosed.  Probing the close brick exposed that this
gate is **floor-blind**: on the valid value `[[1], [2]]` the CROSS-SIBLING window `[3, 7)` — from
inside the first inner seq to inside the second — is balanced and seq-enclosed, so it passes the
gate, yet `bodySuccFact` is FALSE on it (its first depth-`0`-complete entry is followed by a `]`, not
a separator).  So the carrier is FALSE on a valid witness.  Cross-sibling windows DIP below `0`
(crossing the first sibling's close), so the local-Dyck floor `∀ i ∈ [a,b], balance a i ≥ 0` excludes
EXACTLY them.

Toy alphabet: `op` (`+1`), `cl` (`-1`), `ct` (content, `0`).  The witness models `[[1],[2]]`'s
bracket skeleton: `op op ct cl op ct cl cl`.  `bal L a b` is the running balance over `[a,b)`.

**Finding (NEGATIVE, `#guard`-backed).** The window `[2, 6)` (from `ct` "1" inside the first pair to
`ct` "2" inside the second) has `bal 2 6 = 0` (balanced — passes the bare gate) yet DIPS to `bal 2 4 =
-1` (floor violated) and the deliverable `bodySucc` is FALSE on it (`ct` at `2` is depth-`0`-complete
but the next token is `cl`, not a separator, and `3 ≠ 6`).  The floor SEPARATES it.

**Finding (POSITIVE, proven).** `floored_window_cannot_cross`: a window satisfying the local-Dyck
floor cannot cross a close that underflows its balance — so it cannot extend past the located opener's
matching close `j`.  This is the consumer's containment bound `b ≤ hiS`, FOR FREE from the floor.
-/

namespace Tests.Reflections.FloorBlindGateAdmitsCrossSibling

set_option autoImplicit false

/-- Toy bracket alphabet: open (`+1`), close (`-1`), content (neutral). -/
inductive Tok | op | cl | ct
deriving DecidableEq, Inhabited

/-- Numeric bracket delta. -/
def d : Tok → Int
  | .op => 1 | .cl => -1 | .ct => 0

/-- Running balance over the half-open window `[a, b)`. -/
def bal (L : List Tok) (a b : Nat) : Int :=
  ((L.drop a).take (b - a)).foldl (fun s t => s + d t) 0

/-- The witness — bracket skeleton of `[[1], [2]]`: `op op ct cl op ct cl cl`.
    `0:op` outer, `1:op` first inner, `2:ct` "1", `3:cl`, `4:op` second inner, `5:ct` "2", `6:cl`,
    `7:cl` outer. -/
def W : List Tok := [.op, .op, .ct, .cl, .op, .ct, .cl, .cl]

/-- The BARE gate (pre-R313): balance-`0` only.  Floor-blind. -/
def bareGated (L : List Tok) (a b : Nat) : Bool := decide (bal L a b = 0)

/-- The local-Dyck floor over `[a, b]` (R313's added conjunct). -/
def floored (L : List Tok) (a b : Nat) : Bool :=
  (List.range (b + 1)).all fun i => if a ≤ i ∧ i ≤ b then decide (bal L a i ≥ 0) else true

/-- Decidable `bodySucc` deliverable: every depth-`0`-complete content position is either the
    window end or immediately followed by a separator (here a `cl` standing in for `.flowEntry`'s
    role as "more body follows" is the WRONG token — we model the deliverable as requiring the next
    token NOT to be a `cl`, i.e. the entry is not a bare close).  On a genuine entry window this holds;
    on a cross-sibling window the entry runs straight into the sibling's close. -/
def bodySucc (L : List Tok) (a b : Nat) : Bool :=
  (List.range b).all fun k =>
    if a ≤ k ∧ k < b ∧ decide (bal L a (k + 1) = 0) ∧ (L[k]! == Tok.ct)
    then (k + 1 == b) || (decide (k + 1 < b) && !(L[k + 1]! == Tok.cl))
    else true

-- ════════════════════ NEGATIVE — the cross-sibling window [2,6) breaks the carrier ════════════════════
#guard bal W 2 6 == 0            -- balanced ⇒ passes the BARE gate
#guard bareGated W 2 6
#guard bal W 2 4 == -1           -- ... yet DIPS below 0 (crossing the first close)
#guard !(floored W 2 6)          -- floor VIOLATED ⇒ the R313 gate rejects it
#guard !(bodySucc W 2 6)         -- ... and the deliverable is FALSE on it (carrier would be false)
#guard W[2]! == Tok.ct           -- the failing entry: depth-0-complete content...
#guard W[3]! == Tok.cl           -- ... followed by a close, not a separator

-- ════════════════════ POSITIVE — a genuine entry window is floored AND satisfies bodySucc ════════════════════
#guard bal W 2 3 == 0
#guard floored W 2 3
#guard bodySucc W 2 3

-- floored ⟹ bodySucc at every balanced sub-window of the outer body [1,7):
#guard (List.range 8).all fun a =>
  (List.range 8).all fun b =>
    if 1 ≤ a && a ≤ b && b ≤ 7 && bareGated W a b && floored W a b then bodySucc W a b else true

/-- **The GATE-FLOOR principle (proven).** A window satisfying the local-Dyck floor cannot cross a
    close that takes its balance negative.  So once the located opener's matching close `j` is passed,
    the next step `bal a (j+1) < 0` underflows — contradicting the floor.  This is exactly the
    consumer's containment bound `b ≤ hiS = j`: a gated (hence floored) window cannot extend past the
    enclosing seq's close.  The floor the carrier gate now carries discharges `b ≤ hiS` for FREE. -/
theorem floored_window_cannot_cross
    (L : List Tok) (a b m : Nat)
    (h_floor : ∀ i, a ≤ i → i ≤ b → 0 ≤ bal L a i)
    (h_in : a ≤ m) (h_mb : m + 1 ≤ b)
    (h_under : bal L a (m + 1) < 0) : False := by
  have h := h_floor (m + 1) (by omega) h_mb
  omega

end Tests.Reflections.FloorBlindGateAdmitsCrossSibling
