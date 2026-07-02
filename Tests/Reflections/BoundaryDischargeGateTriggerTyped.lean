/-!
# Reflection 418 — a gated-global-adjacency PRODUCER mirror clones its `k`-split SKELETON, but the
PRE-CLOSE boundary cell does NOT: its discharge strategy is TYPED by two axes the trigger token alone
does not fix — (A) does the GATE exclude the close, and (B) is the TRIGGER a balance-changer

Self-contained (core Lean, no `L4YAML` import) toy model of the (R3) seq-rec per-window field producer's
PRODUCE-side joint `globalFlowSeqSepAdj_of_structure` (R418), the `.flowEntry`/`≠ .key` mirror of the
opener producer `globalFlowSeqOpenerAdj_of_structure` (R396).

The producer is proved by a five-way split on the firing index `k`: `k=0` (stream head), `k=1`
(container open), interior body field over `[2, size-2)`, `k+1 = size-2` (PRE-CLOSE), `k=size-2` (the
close).  The head / open / close cells refute their trigger premise by a token inequality and the
interior is the structure-exposed body field — these all CLONE across siblings.  The **pre-close cell**
is the one that does not: at `k+1 = size-2` the successor IS the enclosing close (not a content-start),
so the conclusion is FALSE and the cell must refute a premise.  WHICH premise, and how, is set by two
independent axes:

* **(A) Does the GATE exclude the close?**  If the gate token equals the close, the boundary gate premise
  `tokAt … (k+1) ≠ excl` is self-contradictory once the successor is rewritten to the close — `absurd`.
  Cheapest; no structural fact.  (Seq opener: gate `≠ .flowSequenceEnd`, close IS `.flowSequenceEnd`.)
* **(B) Is the TRIGGER a balance-changer?**  If the gate ADMITS the close, the gate premise survives and
  you must refute the TRIGGER premise instead.  A balance-POSITIVE trigger (an opener, `delta +1`) is
  refuted by the Dyck FLOOR — a pre-close opener forces prefix balance `−1`, contradicting `balance ≥ 0`.
  A balance-NEUTRAL trigger (`delta 0`) moves no balance, so the floor argument is UNAVAILABLE.

Three cells result; the third is the new corner:

| producer            | gate token | close   | gate excludes close? | trigger | delta | discharge                         |
|---------------------|-----------|---------|----------------------|---------|-------|-----------------------------------|
| seq opener (R396)   | close     | `cls`   | YES                  | `opn`   | +1    | `absurd` (gate self-contradiction)|
| map opener (R410)   | `cls`     | `mcls`  | no                   | `opn`   | +1    | Dyck floor (balance-0 + `≥ 0`)    |
| seq separator (R418)| `key`     | `cls`   | no                   | `sep`   | 0     | **no-trailing-X structural fact** |

Cell 3 (the separator) needs a genuinely new EMITTER-level input — the emitter writes no TRAILING
separator before the close (`tokAt l (size-3) ≠ sep`) — that NEITHER opener sibling carried.  The NEGATIVE
below shows it is load-bearing: drop it and the boundary obligation is FALSE on a trailing-separator
witness.

Mirrors L4YAML R418:
* `Prod trig excl`              — the global producer `globalFlowSeq{Opener,Sep}Adj_of_structure`.
* `prod_of_skeleton`           — the five-way split; the head/open/close/body cells CLONE; the pre-close
                                  cell is the abstract `h_boundary` argument (the part that varies).
* `boundary_cell1_gate_excludes` — cell 1, the seq opener's free `absurd` discharge.
* `boundary_cell2_dyck_floor`    — cell 2, the map opener's balance-floor discharge.
* `boundary_cell3_no_trailing`   — cell 3, the seq separator's REQUIRED no-trailing structural fact.
* `boundary_cell3_false_without_no_trailing` — cell 3's obligation is FALSE without that fact.

Sibling of `MirroredGateReprobeWitness` (R417): there the satisfiability PROBE is the consume-side part
that doesn't clone; here the pre-close BOUNDARY DISCHARGE is the produce-side part that doesn't clone —
both because they are fixed by the gate's exclusion semantics, the genuinely-differing part of the mirror.
-/

namespace Tests.Reflections.BoundaryDischargeGateTriggerTyped

set_option autoImplicit false

/-- Toy token kinds: seq opener `opn` / closer `cls`, map closer `mcls`, separator `sep`, map key `key`,
    content scalar `scal`. -/
inductive Tok where
  | opn | cls | mcls | sep | key | scal
  deriving DecidableEq, BEq

/-- Bracket balance delta (toy of `flowBracketDelta`): openers `+1`, closers `−1`, everything else `0`.
    The SEPARATOR has delta `0` — the fact that disarms the Dyck-floor discharge in cell 3. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | .mcls => -1
  | _ => 0

/-- A content start: a scalar or an opener (toy of `isFlowContentStart`).  A `cls` close is NOT content —
    the reason a pre-close boundary obligation is FALSE unless a premise is refuted. -/
def isContent : Tok → Bool
  | .scal | .opn => true
  | _ => false

/-- A token stream, indexed with a default so positions never need bounds proofs (toy of `tokens[·]!`). -/
def tokAt (l : List Tok) (i : Nat) : Tok := l.getD i Tok.scal

/-- Prefix balance (toy of `flowBracketBalance tokens 0 n`), defined recursively so the one-step
    recurrence is definitional. -/
def bal (l : List Tok) : Nat → Int
  | 0 => 0
  | n + 1 => bal l n + delta (tokAt l n)

/-- The one-step balance recurrence (toy of `flowBracketBalance_compose` + `_single`) — here `rfl`. -/
theorem bal_step (l : List Tok) (n : Nat) : bal l (n + 1) = bal l n + delta (tokAt l n) := rfl

/-! ## The cloning SKELETON — the five-way `k`-split, with the pre-close cell left ABSTRACT.

    Every cell EXCEPT the pre-close one is uniform across the opener/separator siblings: the head, the
    container open, and the close all refute the trigger premise by a token inequality, and the interior
    is the structure-exposed body field.  The pre-close cell is the abstract `h_boundary` hypothesis —
    the slot the three discharges below plug into. -/

/-- The global adjacency producer (toy of `GlobalFlowSeq{Opener,Sep}Adj`): every `trig` whose successor
    passes the `≠ excl` gate is followed by a content start. -/
def Prod (trig excl : Tok) (l : List Tok) : Prop :=
  ∀ k, k + 1 < l.length → tokAt l k = trig → tokAt l (k + 1) ≠ excl →
    isContent (tokAt l (k + 1)) = true

/-- **The skeleton clones** — the five-way split is identical for every trigger/gate; only the pre-close
    cell (`h_boundary`) varies, so it is taken as a hypothesis here (mirrors how
    `globalFlowSeq{Opener,Sep}Adj_of_structure` share their `k=0`/`k=1`/`k=size-2`/body structure and
    differ only at `k+1 = size-2`). -/
theorem prod_of_skeleton (trig excl : Tok) (l : List Tok)
    (h0 : tokAt l 0 ≠ trig)
    (h1 : tokAt l 1 ≠ trig)
    (h_body : ∀ k, 2 ≤ k → k + 1 < l.length - 2 →
        tokAt l k = trig → tokAt l (k + 1) ≠ excl → isContent (tokAt l (k + 1)) = true)
    (h_boundary : ∀ k, 2 ≤ k → k + 1 = l.length - 2 →
        tokAt l k = trig → tokAt l (k + 1) ≠ excl → isContent (tokAt l (k + 1)) = true)
    (h_close : tokAt l (l.length - 2) ≠ trig)
    (h_len : 5 ≤ l.length) :
    Prod trig excl l := by
  intro k hk htrig hgate
  by_cases hc0 : k = 0
  · subst hc0; exact absurd htrig h0
  by_cases hc1 : k = 1
  · subst hc1; exact absurd htrig h1
  have hk2 : 2 ≤ k := by omega
  by_cases hcb : k + 1 < l.length - 2
  · exact h_body k hk2 hcb htrig hgate
  by_cases hcb2 : k + 1 = l.length - 2
  · exact h_boundary k hk2 hcb2 htrig hgate
  have hke : k = l.length - 2 := by omega
  rw [hke] at htrig
  exact absurd htrig h_close

/-! ## CELL 1 — gate EXCLUDES the close: the cheapest discharge, no structural fact (the seq opener). -/

/-- **Cell 1** (seq opener `globalFlowSeqOpenerAdj_of_structure`): the gate token IS the close, so the
    boundary gate premise `tokAt l (k+1) ≠ close` becomes `close ≠ close`, absurd.  No balance, no
    no-trailing fact. -/
theorem boundary_cell1_gate_excludes (trig close : Tok) (l : List Tok)
    (h_close_token : tokAt l (l.length - 2) = close) :
    ∀ k, 2 ≤ k → k + 1 = l.length - 2 →
      tokAt l k = trig → tokAt l (k + 1) ≠ close → isContent (tokAt l (k + 1)) = true := by
  intro k _ hk1 _ hgate
  rw [hk1, h_close_token] at hgate
  exact absurd rfl hgate

/-! ## CELL 2 — gate ADMITS the close, trigger is balance-POSITIVE: the Dyck-floor discharge (map opener). -/

/-- **Cell 2** (map opener `globalFlowSeqOpenerAdj_of_map_structure`): the gate admits the close, so the
    trigger premise survives and must be refuted.  The trigger is an opener (`delta = +1`); with the
    balance pinned to `0` at the close and the Dyck floor `≥ 0`, a pre-close opener forces prefix balance
    `−1` — contradiction.  Uses balance, NOT a no-trailing fact; `excl`/`close` are irrelevant. -/
theorem boundary_cell2_dyck_floor (excl : Tok) (l : List Tok)
    (h_bal_close : ∀ k, k + 1 = l.length - 2 → bal l (k + 1) = 0)
    (h_floor : ∀ k, bal l k ≥ 0) :
    ∀ k, 2 ≤ k → k + 1 = l.length - 2 →
      tokAt l k = Tok.opn → tokAt l (k + 1) ≠ excl → isContent (tokAt l (k + 1)) = true := by
  intro k _ hk1 htrig _
  exfalso
  have hstep := bal_step l k
  rw [htrig] at hstep
  have hd : delta Tok.opn = 1 := rfl
  rw [hd, h_bal_close k hk1] at hstep
  have hfl := h_floor k
  omega

/-! ## CELL 3 — gate ADMITS the close, trigger is balance-NEUTRAL: BOTH opener discharges fail, so a
    no-trailing-X structural fact is REQUIRED (the seq separator, the new corner). -/

/-- **Cell 3** (seq separator `globalFlowSeqSepAdj_of_structure`, R418): the gate `≠ key` admits the close
    (`cls ≠ key`) AND the separator has `delta = 0`, so neither cell 1's `absurd` nor cell 2's Dyck floor
    applies.  The pre-close `sep` is excluded ONLY by an emitter-level invariant — no TRAILING separator
    before the close — supplied here as `h_no_trailing`. -/
theorem boundary_cell3_no_trailing (excl : Tok) (l : List Tok)
    (h_no_trailing : ∀ k, k + 1 = l.length - 2 → tokAt l k ≠ Tok.sep) :
    ∀ k, 2 ≤ k → k + 1 = l.length - 2 →
      tokAt l k = Tok.sep → tokAt l (k + 1) ≠ excl → isContent (tokAt l (k + 1)) = true := by
  intro k _ hk1 htrig _
  exact absurd htrig (h_no_trailing k hk1)

/-- **The no-trailing fact is LOAD-BEARING** — cell 3's boundary obligation is FALSE without it.  On a
    trailing-separator witness `[opn, scal, sep, cls, scal]` (length 5, so the close `cls` sits at
    `size-2 = 3` and a `sep` sits at `size-3 = 2`), the `k = 2` instance has trigger `sep`, a gate-passing
    successor (`tokAt 3 = cls ≠ key`), and conclusion `isContent cls = true`, which is FALSE.  So cell 3's
    discharge genuinely cannot be cloned from the opener cells — it requires the structural fact. -/
def wTrail : List Tok := [Tok.opn, Tok.scal, Tok.sep, Tok.cls, Tok.scal]

#guard tokAt wTrail (wTrail.length - 2) == Tok.cls   -- the close sits at size-2
#guard tokAt wTrail (wTrail.length - 3) == Tok.sep   -- a TRAILING separator sits at size-3
#guard (tokAt wTrail 3 == Tok.key) == false          -- the gate `≠ key` ADMITS the close
#guard isContent (tokAt wTrail 3) == false           -- but the close is NOT content — obligation fails

theorem boundary_cell3_false_without_no_trailing :
    ¬ (∀ k, 2 ≤ k → k + 1 = wTrail.length - 2 →
        tokAt wTrail k = Tok.sep → tokAt wTrail (k + 1) ≠ Tok.key →
        isContent (tokAt wTrail (k + 1)) = true) := by
  intro h
  have hc : isContent (tokAt wTrail (2 + 1)) = true :=
    h 2 (by decide) (by decide) (by decide) (by decide)
  exact absurd hc (by decide)

/-! ## Taxonomy summary — the two axes that TYPE the discharge, made concrete. -/

-- Axis (A): does the gate token equal the close?  YES for the seq opener (cell 1) …
#guard (decide (Tok.cls = Tok.cls)) == true     -- seq opener gate = close  ⇒ cell 1 (free `absurd`)
#guard (decide (Tok.key = Tok.cls)) == false    -- separator gate ≠ close   ⇒ no free discharge
-- Axis (B): is the trigger a balance-changer?  YES for the opener (cell 2) …
#guard (decide (delta Tok.opn = 0)) == false    -- opener trigger moves balance ⇒ Dyck floor available
#guard (decide (delta Tok.sep = 0)) == true     -- separator trigger is neutral ⇒ floor UNAVAILABLE (cell 3)

end Tests.Reflections.BoundaryDischargeGateTriggerTyped
