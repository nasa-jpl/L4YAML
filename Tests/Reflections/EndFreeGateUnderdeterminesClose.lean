/-!
# Reflection 340 — an END-FREE gate underdetermines a window's CLOSE

Self-contained (core Lean, no `L4YAML` import) toy model of the decision behind the
`(i'-b-B2c-provider-from-gate)` probe (`SeqGateWindownessProbe`).

A provider is quantified under a window gate `Gate s a b` whose conjuncts constrain only
window-INTERNAL invariants — here a single balance-`0` conjunct (the real gate adds a local-Dyck
floor `∀ i, a ≤ i → i ≤ b → bal s a i ≥ 0`, equally END-free).  The next-step note suspected the
provider could read its structural CLOSE straight off the window's end coordinate `b` — i.e. that the
gate forces `get s b = close`.  The probe — run BEFORE authoring — REFUTES it:

* the gate is **END-FREE**: every conjunct is a sum/bound over the interior `[a,b)`, blind to the
  token AT `b`;
* so a `b ≠ close` window — one whose end is INTERIOR to the enclosing structure (a trailing-separator
  slice `it sep`) — passes the gate yet has `get s b = it`, **not** the close;
* hence the provider must LOCATE the enclosing genuine structure `[loS, hiS)` and read
  `get s hiS = close` off ITS matching boundary, the gate window SELECTED inside by a proven
  containment `b ≤ hiS`.

`W` mirrors the filtered scan of `[[1, 2], 9]` (drop the stream markers):
`op op it sep it cl sep it cl` at indices `0..8`.  The inner seq body is `[2, 5)` (between `op@1` and
`cl@5`).  The `b ≠ close` gated window `[2, 4)` = `it sep` (mirrors `"1" ,`) passes the gate yet its
end `get W 4 = it`; the enclosing close lives at `hiS = 5` (`get W 5 = cl`), with `b = 4 ≤ 5`.

The bridge mirrors `seqDescent_provider_of_located`: it never inspects `get s b`; it returns the
located `⟨loS, hiS⟩` with `get s hiS = close` and `b ≤ hiS`.  This is the END-dual of the head-blind
gate probe (a HEAD-blind gate admits spurious-HEADED windows; an END-free gate admits spurious-ENDED
ones).

## Reflection 356 — a SETTLED next-step pointer re-credited balance-0 with pinning `b`; the gate admits MANY non-close ends

A later increment (the emission-spine wrapper `nestedSeq_recseqentry_locate`) declared its leaf
obligation `b = head-entry-close` *"pinned by `SeqTypedInterior`'s balance-0"* — re-crediting the very
balance conjunct R340 already proved END-free.  R356 re-runs the probe and sharpens it: the gate admits
not just ONE spurious end but ARBITRARILY MANY — a seq of `n` elements has `n-1` interior separator
ends, ALL balance-0 + floored.  The witness `V = op it sep it sep it cl` (mirror of the `[1,2,3]`
interior at base `op`): from the interior start `a = 1`, the gate holds at b ∈ {2, 4, 6} (the two
separator ends and the close), but only `get V 6 = cl`.  So `b` is pinned by the consumer's explicit
CLOSE hypothesis — `seqWindowRecSeqBody`'s width-guard carries `tokens[hi]!.val = .flowSequenceEnd` as
its fourth `G`-conjunct — and the leaf's `b = close` is derived by MATCHING that token, never by
balance.  The lesson: re-probe a boundary-pinning attribution even when a *settled* pointer states it,
because the pointer phrases the END-free trap as resolved.
-/

namespace Tests.Reflections.EndFreeGateUnderdeterminesClose

set_option autoImplicit false

/-- A toy token: a flow-bracket open/close, a content item, or a separator.  Mirrors the
    `flowSequenceStart`/`flowSequenceEnd`/scalar/`flowEntry` distinction the real probe reads. -/
inductive Tok | op | cl | it | sep
deriving DecidableEq, Repr

/-- The bracket delta — `op` pushes, `cl` pops, content/separator are neutral.  Mirrors
    `flowBracketDelta`. -/
def delta : Tok → Int
  | .op => 1 | .cl => -1 | .it => 0 | .sep => 0

/-- Balance = sum of deltas over a token list.  Mirrors `flowBracketBalance` on a slice. -/
def bal : List Tok → Int
  | [] => 0
  | t :: ts => delta t + bal ts

/-- The window slice `[a, b)` of a stream. -/
def slice (s : List Tok) (a b : Nat) : List Tok := (s.take b).drop a

/-- The window balance over `[a, b)`. -/
def windowBal (s : List Tok) (a b : Nat) : Int := bal (slice s a b)

/-- A toy indexer (`getElem!` analogue). -/
def get (s : List Tok) (i : Nat) : Tok := s.getD i .it

/-- The **END-FREE gate**: the only conjunct constrains the interior balance of `[a, b)` — it says
    NOTHING about the token AT `b`.  Mirrors `SeqTypedInterior`, whose conjuncts (balance-`0`,
    enclosing-seq `btFold`-top, local-Dyck floor) are all window-internal / END-free. -/
structure Gate (s : List Tok) (a b : Nat) : Prop where
  /-- the interior is depth-`0`-balanced — a sum over `[a, b)`, blind to `get s b` -/
  bal0 : windowBal s a b = 0

/-! ## The witness — `op op it sep it cl sep it cl` (mirror of `[[1, 2], 9]`) -/

def W : List Tok := [.op, .op, .it, .sep, .it, .cl, .sep, .it, .cl]

/-! ## THE PROBE — a `b ≠ close` window that passes the gate yet whose END is not the close -/

/-- The trailing-separator window `[2, 4)` = `it sep` (mirrors `"1" ,`) — the gate HOLDS. -/
theorem gate_24 : Gate W 2 4 := ⟨by decide⟩

/-- ...yet its END token `get W 4` is a content `it`, NOT the close `cl` — the gate underdetermines
    the close.  This is the refutation: the provider can NOT read its close off `get W b`. -/
theorem end_24_not_close : get W 4 ≠ .cl := by decide

/-! ## THE BRIDGE — the close comes from the LOCATED enclosing structure, with `b ≤ hiS`

Mirrors `seqDescent_provider_of_located`: never inspects `get s b`; returns the located `⟨loS, hiS⟩`
with `get s hiS = close` and the containment `b ≤ hiS`. -/

/-- The provider for the gated `[2, 4)` window: the enclosing seq body is `[loS, hiS) = [2, 5)`, whose
    matching close at `hiS = 5` is `cl`, and the gate window is selected inside (`4 ≤ 5`).  The close
    is read off `hiS`, never off `b = 4`. -/
theorem located_close_24 :
    ∃ loS hiS, loS ≤ 2 ∧ 4 ≤ hiS ∧ get W hiS = Tok.cl :=
  ⟨2, 5, by decide, by decide, by decide⟩

/-! ## Concrete witnesses -/

-- the `b ≠ close` window passes the gate (END-free balance-0)...
#guard windowBal W 2 4 == 0
-- ...yet its END is NOT the close:
#guard get W 4 != Tok.cl
-- the enclosing located close lives at hiS = 5:
#guard get W 5 == Tok.cl
-- and the gate window is SELECTED inside: b = 4 ≤ hiS = 5:
#guard decide (4 ≤ 5)
-- CONTRAST: the `b = hiS` window [2, 5) — its END coincides with the close, but only because b was
-- chosen = hiS; the gate did not force it (it holds for BOTH [2,4) and [2,5)):
#guard windowBal W 2 5 == 0
#guard get W 5 == Tok.cl

/-- End-to-end: a window where the gate HOLDS but its END is not the close, while the close is read
    off the located enclosing structure — the provider reads its boundary from the enclosing frame,
    never from the window's end `b`. -/
example : Gate W 2 4 ∧ get W 4 ≠ Tok.cl ∧ (∃ loS hiS, loS ≤ 2 ∧ 4 ≤ hiS ∧ get W hiS = Tok.cl) :=
  ⟨gate_24, end_24_not_close, located_close_24⟩

/-! ## R356 — the gate admits MANY non-close ends; only the close token discriminates

`V = op it sep it sep it cl` (mirror of the `[1,2,3]` interior at base `op`).  From the interior start
`a = 1`, the END-free gate holds at all THREE ends b ∈ {2, 4, 6}, but only b = 6 carries the close. -/

def V : List Tok := [.op, .it, .sep, .it, .sep, .it, .cl]

/-- The gate holds at BOTH separator ends AND the close end — it cannot pin `b`. -/
theorem gate_admits_three_ends : Gate V 1 2 ∧ Gate V 1 4 ∧ Gate V 1 6 :=
  ⟨⟨by decide⟩, ⟨by decide⟩, ⟨by decide⟩⟩

/-- Only `b = 6` carries the close token; the two gate-passing separator ends do not.  So the close
    hypothesis, not the interior gate, pins the wrapper's `b`. -/
theorem close_token_separates_three_ends :
    get V 2 = Tok.sep ∧ get V 4 = Tok.sep ∧ get V 6 = Tok.cl := by decide

-- the gate AGREES on a separator end and the close end, but the close token SEPARATES them:
#guard windowBal V 1 4 == windowBal V 1 6     -- both balance-0
#guard get V 4 != get V 6                      -- yet only b = 6 is the close

end Tests.Reflections.EndFreeGateUnderdeterminesClose
