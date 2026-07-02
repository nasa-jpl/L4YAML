/-!
# Reflection 417 — mirroring a gated global-adjacency predicate to a SIBLING trigger token: the DEF and the WINDOW-RESTRICTION clone for FREE, but the SATISFIABILITY PROBE does NOT clone — re-choose its witness for the NEW gate's non-vacuity axis

Self-contained (core Lean, no `L4YAML` import) toy model of the (R3) seq-rec per-window field producer's
SMALLEST-FIRST step — adding a NEW global separator-adjacency fact `GlobalFlowSeqSepAdj` (trigger
`.flowEntry`, gate `≠ .key`) that mirrors the existing `GlobalFlowSeqOpenerAdj` (trigger
`.flowSequenceStart`, gate `≠ .flowSequenceEnd`).

The mirror is THREE bricks, and only the third is real work:

* **The `def` clones for free** — pure token swap (trigger + excluded successor). Zero proof content.
* **The window-restriction clones for free** — the SAME subset-narrowing lemma; gate-agnostic, it only
  widens the domain bound ([[ref-window-absolute-gate-subset-restriction]]).
* **The satisfiability PROBE does NOT clone** ([[ref-probe-provider-satisfiable-before-assembler]]). The
  sibling's witness was chosen for the SIBLING's trigger+gate and can be doubly wrong for the mirror:
  - **(a) TRIGGER ABSENT** — the opener witness `[{a:[b]}]` has openers but ZERO `.flowEntry` (no
    commas), so the separator body fires VACUOUSLY: no firing position, certifies nothing.
  - **(b) GATE EXCLUDES** — a map-internal `,` has successor `.key`, exactly what `≠ .key` excludes, so
    a separator-bearing-but-wrong-axis witness is vacuous too.
  Re-choose a witness that contains the new trigger AND satisfies the new gate (here a multi-element seq
  `["a","b"]`), so the body fires NON-vacuously. The probe's witness is fixed by the new gate's exclusion
  semantics — exactly the part that differs between siblings ([[ref-minimal-pair-extracts-the-gate]]).

Contrast [[ref-conjunctive-consumer-gates-on-orthogonal-axis]]: there one axis-uniform intermediate
fires on BOTH axes (cross-axis probe); here the mirror'd gate can be axis-EXCLUSIVE, flipping which axis
the predicate is non-vacuous on — so the sibling's cross-axis witness is the WRONG probe.

Mirrors L4YAML R417:
* `Adj trig excl`            — one parameterized def IS both `GlobalFlowSeqOpenerAdj` and `…SepAdj`.
* `adjWindow_of_global`      — one lemma IS both `flowSeq{Opener,Sep}Adj_window_of_global` (free clone).
* `sepAdj_fires_nonvacuously`— the re-chosen probe `globalFlowSeqSepAdj_fires` (witness `["a","b"]`).
* `sepAdj_vacuous_on_*`      — why the opener witness `[{a:[b]}]` cannot be reused.
-/

namespace Tests.Reflections.MirroredGateReprobeWitness

set_option autoImplicit false

/-- Toy token kinds: opener `[`, closer `]`, separator `,`, map `key`, content scalar. -/
inductive Tok where
  | opn | cls | sep | key | scal
  deriving DecidableEq, BEq

/-- A content start: a scalar or an opener (mirrors `isFlowContentStart`).  `key` is NOT content — the
    reason the separator gate `≠ key` exists. -/
def isContent : Tok → Bool
  | .scal | .opn => true
  | _ => false

/-- A token stream, indexed with a default so positions never need bounds proofs (toy of `tokens[·]!`). -/
def tokAt (l : List Tok) (i : Nat) : Tok := l.getD i Tok.scal

/-! ## The mirror's FREE bricks — def + window-restriction clone by a pure token swap. -/

/-- A gated GLOBAL adjacency predicate, parameterized by the TRIGGER token and the EXCLUDED successor.
    This single def IS both siblings (mirrors `GlobalFlowSeqOpenerAdj` / `GlobalFlowSeqSepAdj`): cloning
    the def across trigger tokens is a pure parameter swap, zero proof content. -/
def Adj (trig excl : Tok) (l : List Tok) : Prop :=
  ∀ k, k + 1 < l.length → tokAt l k = trig → tokAt l (k + 1) ≠ excl →
    isContent (tokAt l (k + 1)) = true

/-- The opener sibling (`GlobalFlowSeqOpenerAdj`): trigger `[`, excluded successor `]`. -/
def OpenerAdj (l : List Tok) : Prop := Adj Tok.opn Tok.cls l

/-- The separator MIRROR (`GlobalFlowSeqSepAdj`): trigger `,`, excluded successor `key`. -/
def SepAdj (l : List Tok) : Prop := Adj Tok.sep Tok.key l

/-- The window-relative restriction shape (toy of `FlowBodyContentDeepSeq.feContentStart` over `[·, hi)`). -/
def AdjWindow (trig excl : Tok) (l : List Tok) (hi : Nat) : Prop :=
  ∀ k, k + 1 < hi → tokAt l k = trig → tokAt l (k + 1) ≠ excl →
    isContent (tokAt l (k + 1)) = true

/-- **The window-restriction clones for free** — ONE gate-agnostic lemma (it only widens the domain
    bound) serves BOTH predicates; the SAME proof as `flowSeq{Opener,Sep}Adj_window_of_global`. -/
theorem adjWindow_of_global (trig excl : Tok) (l : List Tok) (hi : Nat)
    (h : Adj trig excl l) (h_hi : hi ≤ l.length) : AdjWindow trig excl l hi := by
  intro k hk ht hne
  exact h k (by omega) ht hne

-- … instantiating the ONE lemma at BOTH triggers — the free clone made explicit:
theorem openerWindow_of_global (l : List Tok) (hi : Nat) (h : OpenerAdj l) (h_hi : hi ≤ l.length) :
    AdjWindow Tok.opn Tok.cls l hi := adjWindow_of_global Tok.opn Tok.cls l hi h h_hi
theorem sepWindow_of_global (l : List Tok) (hi : Nat) (h : SepAdj l) (h_hi : hi ≤ l.length) :
    AdjWindow Tok.sep Tok.key l hi := adjWindow_of_global Tok.sep Tok.key l hi h h_hi

/-! ## POSITIVE — the re-chosen probe: a witness carrying the NEW trigger that satisfies the NEW gate,
    so `SepAdj`'s body fires NON-vacuously (mirrors `globalFlowSeqSepAdj_fires` on `["a","b"]`). -/

/-- The re-chosen SEP witness `["a", "b"]`: a `.flowEntry` at `k = 1` whose successor `scal` is `≠ key`
    and content (toy of the scanned `["a","b"]` whose `.flowEntry` at `k=3` precedes `scalar "b"`). -/
def wSep : List Tok := [Tok.scal, Tok.sep, Tok.scal]

#guard tokAt wSep 1 == Tok.sep            -- firing position EXISTS (the new trigger)
#guard (tokAt wSep 2 == Tok.key) == false -- successor passes the `≠ key` gate
#guard isContent (tokAt wSep 2) == true   -- and is content — the body fires NON-vacuously

/-- The probe must be RE-derived: it witnesses a real firing of `SepAdj` (the `k=1` separator satisfies
    trigger + gate with a content successor), ruling out a vacuously-true provider. -/
theorem sepAdj_fires_nonvacuously :
    tokAt wSep 1 = Tok.sep ∧ tokAt wSep 2 ≠ Tok.key ∧ isContent (tokAt wSep 2) = true :=
  ⟨by decide, by decide, by decide⟩

/-! ## NEGATIVE (a) — TRIGGER ABSENT: the sibling's witness cannot be reused — it has no separator, so
    `SepAdj` holds VACUOUSLY and certifies nothing. -/

/-- The OPENER witness `[opn, scal, cls]` (toy of the opener probe's `[{a:[b]}]`): it fires `OpenerAdj`
    at `k = 0` (opener, successor `scal ≠ cls`, content) but contains ZERO separators. -/
def wOpn : List Tok := [Tok.opn, Tok.scal, Tok.cls]

#guard tokAt wOpn 0 == Tok.opn            -- an opener firing position for OpenerAdj …
#guard isContent (tokAt wOpn 1) == true
-- … but reusing wOpn for the SepAdj probe is wrong: it has the opener and NO separator —
#guard (List.range wOpn.length).any (fun k => tokAt wOpn k == Tok.opn)
#guard (List.range wOpn.length).all (fun k => (tokAt wOpn k == Tok.sep) == false)

/-- **(a) TRIGGER ABSENT** — `SepAdj wOpn` holds VACUOUSLY: every separator premise `tokAt wOpn k = sep`
    is false (wOpn is opn/scal/cls only), so the provider is trivially "true" without any real firing —
    reusing the sibling's witness defeats the probe's purpose. -/
theorem sepAdj_vacuous_on_opener_witness : SepAdj wOpn := by
  intro k hk ht hne
  exfalso
  have hlen : wOpn.length = 3 := rfl
  rw [hlen] at hk
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with h | h <;> subst h
  · exact absurd ht (by decide)   -- tokAt wOpn 0 = opn ≠ sep
  · exact absurd ht (by decide)   -- tokAt wOpn 1 = scal ≠ sep

/-! ## NEGATIVE (b) — GATE EXCLUDES: even a separator-bearing witness on the WRONG axis is vacuous,
    because the NEW gate excludes it. -/

/-- A MAP witness `[sep, key]`: it HAS a separator at `k = 0`, but its successor is `key` — exactly what
    the `≠ key` gate excludes (a flow-map `,` precedes a key, never seq content). -/
def wMap : List Tok := [Tok.sep, Tok.key]

#guard tokAt wMap 0 == Tok.sep            -- the new trigger IS present this time …
#guard tokAt wMap 1 == Tok.key            -- … but the successor IS the excluded token

/-- **(b) GATE EXCLUDES** — `SepAdj wMap` again holds VACUOUSLY: the lone separator's `≠ key` premise is
    false, so the body never fires.  A probe witness must satisfy the NEW gate, not merely contain the
    new trigger. -/
theorem sepAdj_vacuous_on_map_witness : SepAdj wMap := by
  intro k hk ht hne
  exfalso
  have hlen : wMap.length = 2 := rfl
  rw [hlen] at hk
  have hk0 : k = 0 := by omega
  subst hk0
  exact hne (by decide)   -- tokAt wMap 1 = key, contradicts hne : tokAt wMap 1 ≠ key

/-! ## Probe summary — the def/restriction are free, the witness is not: it is fixed by the gate. -/

-- the def + restriction are gate-agnostic (cloned above); the witness is gate-DEPENDENT:
#guard isContent Tok.scal == true                 -- a content head passes the gate (wSep) …
#guard isContent Tok.key == false                 -- … a key does not (the gate's reason to exist) …
#guard (decide (Tok.scal = Tok.key)) == false     -- … and scal ≠ key is the separator gate's pass test.

end Tests.Reflections.MirroredGateReprobeWitness
