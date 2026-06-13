/-!
# Reflection 416 — a guard re-scope that GATES a field splits its consumers by premise-availability; the consumer that needs the field UNGATED re-sources it from a sibling boundary-fact at the NARROWED window (interior position = sub-window boundary)

Self-contained (core Lean, no `L4YAML` import) toy model of the (R2) seq-rec CONSUMER re-thread —
the round AFTER R415's dispatch/oracle clones, where `seqWindowRecSeqBody_seq` and its inner
`seqWindow_flowBodyContent_seq` migrate onto the re-scoped `FlowBodyContentDeepSeq`.

R415 ([[ref-derisked-migration-one-clone-per-consumer]]) said a de-risked guard re-scope costs ONE
clone-with-one-line per consumer: the field the guard used to DERIVE becomes a SUPPLIED premise. R416
finds the cost model is NON-uniform once the re-scope GATES a field (adds premise `P`):

* **P-available consumer** (the recursion's ADVANCE edge): `P` is derivable at the call site, so the
  clone IS one line. Here `P = succ ≠ key` comes FREE from the content guard's `isContent succ`
  already in hand (a content head is never a key) — the gift→debt of
  [[ref-guarded-universal-fold-relocates-guard]].

* **P-unavailable consumer** (the `FlowBodyContent` projector): it must PRODUCE a downstream type
  whose mirror field is UNGATED (`FlowBodyContent.feContentStart` has no `≠ key` premise), so it needs
  the field's CONCLUSION *without* `P` — and `P` is exactly what the field would conclude. It CANNOT
  route through the re-scoped guard at all (the re-scoped field is strictly weaker at the consume
  boundary: it holds vacuously where the ungated field is FALSE). It must RE-SOURCE the field from a
  SIBLING provider that proves the conclusion UNCONDITIONALLY.

The re-source mechanism — and the reusable trick: the sibling is the separator CARRIER's
BOUNDARY-keyed fact (`noTrailingSepFact`, fires only at a window's LAST separator, whose successor is
the token just PAST the window). To cover an INTERIOR separator `k`, instantiate the boundary fact at
the NARROWED window ending at `k+1`: narrowing the upper bound re-frames interior position `k` as that
sub-window's boundary, and the "token past the sub-window" is the parent's interior `tokens[k+1]`. So a
boundary-only provider covers every interior position for free ([[ref-window-absolute-gate-subset-restriction]]:
the carrier's window-absolute body restricts to any sub-window).

Mirrors L4YAML R416:
* `feGated` / `feUngated`    — `FlowBodyContentDeepSeq.feContentStart` (gated by `≠ key`) vs
  `FlowBodyContent.feContentStart` (ungated); the gated one cannot produce the ungated one.
* `ne_key_of_isContent`      — the P-available supply: `isContent succ → succ ≠ key` (advance edge).
* `Carrier` / `noTrailingSep`— the sibling provider; `feUngated_of_carrier` instantiates it at `k+1`.
-/

namespace Tests.Reflections.GatedFieldResourcedViaNarrow

set_option autoImplicit false

/-- Toy token kinds: opener `[`, closer `]`, content scalar, separator `,`, and a map `key`
    (the token `≠ key` excludes — a map-internal `,` is followed by a key, never seq content). -/
inductive Tok where
  | op | cl | scal | sep | key
  deriving DecidableEq, BEq

/-- A content start: a scalar or an opener (mirrors `isFlowContentStart`).  Crucially `key` is NOT a
    content start — that is the whole point of the re-scope's `≠ key` gate. -/
def isContent : Tok → Bool
  | .scal | .op => true
  | _ => false

/-- A token stream, indexed with a default so positions never need bounds proofs (toy of `tokens[·]!`). -/
def tokAt (l : List Tok) (i : Nat) : Tok := l.getD i Tok.scal

/-- **UNGATED separator-content field** — at a separator `k`, the successor is content; NO `≠ key`
    premise (mirrors `FlowBodyContent.feContentStart`, the downstream field the dispatch consumes). -/
def feUngated (l : List Tok) (k : Nat) : Prop :=
  tokAt l k = Tok.sep → isContent (tokAt l (k + 1)) = true

/-- **GATED separator-content field** — the re-scoped field, fires only when the successor is `≠ key`
    (mirrors `FlowBodyContentDeepSeq.feContentStart`).  It cannot self-derive `≠ key`. -/
def feGated (l : List Tok) (k : Nat) : Prop :=
  tokAt l k = Tok.sep → tokAt l (k + 1) ≠ Tok.key → isContent (tokAt l (k + 1)) = true

/-! ## NEGATIVE — the re-scoped (gated) field CANNOT produce the ungated one: it holds vacuously
    exactly where the ungated field is FALSE, so there is no gated→ungated coercion. -/

/-- A stream whose separator at `0` is followed by a `key` — a map-internal `,` (the region the
    re-scope's `≠ key` gate exists to exclude). -/
def lmap : List Tok := [Tok.sep, Tok.key]

/-- The GATED field HOLDS at this window — vacuously, because its `≠ key` premise is unmet. -/
theorem feGated_holds_vacuously : feGated lmap 0 := by
  intro _ hne; exact absurd rfl hne

/-- The UNGATED field is FALSE at the SAME window: it would force `isContent key = true`.  Together
    with the line above this proves the gated field is strictly weaker — a P-unavailable consumer
    needing the ungated conclusion cannot route through the re-scoped guard. -/
theorem feUngated_false : ¬ feUngated lmap 0 := by
  intro h
  have := h rfl
  simp [isContent, tokAt, lmap] at this

/-! ## The P-AVAILABLE consumer — the advance edge supplies `P = ≠ key` in one line from content in hand -/

/-- `isContent t → t ≠ key`: a content head is never a key.  This is the one-line supply the ADVANCE
    edge uses — it already holds `isContent (tokAt l (m+1))` from the content guard, so the re-scoped
    guard's NEW premise is FREE (R415's "one clone-with-one-line", the case the cost model covers). -/
theorem ne_key_of_isContent (t : Tok) (h : isContent t = true) : t ≠ Tok.key := by
  cases t <;> simp_all [isContent]

/-- The advance-edge supply, in situ: given the content fact in hand, discharge the gated field's
    `≠ key` premise (models `seqWindowRecSeqBody_seq` feeding `flowBodyContentDeepSeq_advance`). -/
theorem advance_supplies_gate (l : List Tok) (k : Nat)
    (h : isContent (tokAt l (k + 1)) = true) : tokAt l (k + 1) ≠ Tok.key :=
  ne_key_of_isContent _ h

/-! ## The P-UNAVAILABLE consumer — re-source the ungated field from the carrier's BOUNDARY fact at
    the NARROWED window (interior position `k` becomes the sub-window `[·, k+1)`'s boundary). -/

/-- The carrier's BOUNDARY fact for the window ending at `b`: if the last in-window position `b-1` is a
    separator, the token AT `b` (just past the window) is content (mirrors `noTrailingSepFact`). -/
def noTrailingSep (l : List Tok) (b : Nat) : Prop :=
  tokAt l (b - 1) = Tok.sep → isContent (tokAt l b) = true

/-- The separator CARRIER: the boundary fact holds at EVERY window-end `b ≤ hi` (mirrors
    `SeqInteriorSeparators` restricted to windows `[lo, b)`). -/
def Carrier (l : List Tok) (hi : Nat) : Prop :=
  ∀ b, b ≤ hi → noTrailingSep l b

/-- **The re-source.**  The UNGATED interior field at separator `k` is the carrier's BOUNDARY fact
    instantiated at the NARROWED window end `b = k + 1`: there, position `k` IS the last in-window
    position and `tokAt l (k+1)` is the token just past it.  No `≠ key` needed — the carrier proves the
    conclusion unconditionally.  Models `seqWindow_flowBodyContent_seq`'s `h_feContent`. -/
theorem feUngated_of_carrier (l : List Tok) (hi k : Nat)
    (hk : k + 1 ≤ hi) (carr : Carrier l hi) : feUngated l k := by
  intro hsep
  have hb := carr (k + 1) hk
  unfold noTrailingSep at hb
  rw [Nat.add_sub_cancel] at hb
  exact hb hsep

/-! ## NEGATIVE — narrowing is NECESSARY: the carrier's fact at the FULL window end is the WRONG
    instance; only `b = k+1` puts the interior separator at the window boundary. -/

/-- A window with an INTERIOR separator at position `1`, whose LAST position `3` is the close `cl`. -/
def l6 : List Tok := [Tok.scal, Tok.sep, Tok.scal, Tok.cl]

-- the interior separator is at position 1 …
#guard tokAt l6 1 == Tok.sep
-- … but the FULL-window boundary fact (end `b = 4`) is about position `3 = cl`, NOT the separator —
-- so `noTrailingSep l6 4` is VACUOUS and says nothing about the interior `,` (narrowing required) …
#guard (tokAt l6 3 == Tok.sep) == false
-- … whereas the NARROWED boundary (end `b = 2`) lands exactly on the interior separator (pos `1`) …
#guard (tokAt l6 (2 - 1) == Tok.sep) == true
-- … and its successor `tokAt l6 2` is content — the interior fact, recovered by narrowing alone.
#guard isContent (tokAt l6 2) == true

/-- The full window's carrier instance, applied at the interior position `1`, is VACUOUS — its premise
    (`tokAt l6 3 = sep`) is false — so it does NOT deliver the interior field without narrowing. -/
theorem fullWindow_fact_vacuous_at_interior : noTrailingSep l6 4 := by
  intro hsep; simp [tokAt, l6] at hsep

/-- … but the carrier (holding at every end ≤ 4) DOES deliver the interior field — via the narrowed
    instance `b = 2`, exactly `feUngated_of_carrier`. -/
theorem interior_recovered_by_narrow (carr : Carrier l6 4) : feUngated l6 1 :=
  feUngated_of_carrier l6 4 1 (by omega) carr

/-! ## Probes — the cost split: P-available (supply) vs P-unavailable (re-source) -/

-- a content head is never a key (the P-available supply fires) …
#guard isContent Tok.scal == true
#guard isContent Tok.op == true
-- … while a key is not content (the gate's reason to exist; the gated field stays vacuous here) …
#guard isContent Tok.key == false
-- … and the discriminator between the two consumer classes is whether `isContent succ` is in hand.
#guard (decide (Tok.scal = Tok.key)) == false

end Tests.Reflections.GatedFieldResourcedViaNarrow
