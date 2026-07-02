/-
# Reflection 291 — lift once, then MIRROR the easy edge (don't re-derive it)

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in Blueprint
Reflection 291, the sequel to `ref-easy-edge-guard-fails-hard-edge` / R290 and the dividend-collection
step of `ref-converse-forward-invariant-asymmetry`.

**The principle.** R290's diagnosis: a guard sized to its easy (ADVANCE) edge can be structurally
incapable of its hard (DESCEND) edge, and the remedy is to LIFT the guard to a stronger, recursion-stable
form (balance-condition-FREE / all-depth).  R291 is the dividend: once you have lifted, the easy edge is
ALREADY PAID FOR.  A balance-free guard is a pure RESTRICTION of itself on every sub-window, and that
property is direction-agnostic — the advance edge restricts the same all-depth quantifiers to the tail
`[m+1, hi)` exactly as the descend edge restricts them to the interior `[k+1, j)`.  The ONLY difference
is which field re-seats the child head:

  * DESCEND — child head off the OPENER field at the opener `k`.
  * ADVANCE — child head off the SEPARATOR field at the separator `m`.

Everything else is identical.  So after lifting, do NOT re-derive the easy edge with the old
(projection-level) machinery full of balance re-basing — write it as the hard edge's MIRROR, swapping
only the head-seating field.

**What this demo asserts (fails the build if it ever drifts):**
  * POSITIVE — the two edges of the deep (all-depth) guard are MIRRORS.  `deep_descend` and `deep_advance`
    have the identical proof skeleton (`obtain ⟨_, h_op, h_fe⟩; refine ⟨?_, ?_, ?_⟩`; head off one field;
    the two quantifier fields the parent's restricted by `omega`), differing ONLY in the head-seating
    field (`h_op` at the opener vs `h_fe` at the separator).  Crucially `deep_advance` takes NO balance
    hypothesis and no size side condition.  `deep_descend_good` fires descend on `[ a a ]`; `deep_adv` /
    `deep_advance_good` fire advance on `a , a`, re-seating the tail head with zero arithmetic.
  * NEGATIVE — re-deriving the advance edge from the PROJECTION (depth-`0`) guard costs the balance gate.
    On a stream whose separator sits at depth `1` (`[ , , ]`), the shallow guard's separator clause is
    balance-GATED, so it is vacuous there and gives NOTHING about the post-separator head — which
    `interior_after_sep_not_content` shows is itself a separator.  `not_deep_neg` confirms the deep guard's
    UN-gated separator field is exactly the missing piece (it rejects the bad stream).  The gate is the
    projection's cost R291 says not to re-pay on the lifted edge.
-/
set_option autoImplicit false

namespace Tests.Reflections.LiftOnceMirrorEasyEdge

/-! ## The toy token stream and its bracket delta -/

/-- A toy flow token: a content scalar, a body separator, or a bracket opener / closer. -/
inductive Tok | scal | sep | opn | cls
  deriving DecidableEq

/-- Toy of `flowBracketDelta`: openers `+1`, closers `−1`, content/separators `0`. -/
def tokDelta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _ => 0

/-- Toy of `isFlowContentStart`: a head that begins a content entry (scalar or an opener). -/
def isContentStart (t : Tok) : Prop := t = .scal ∨ t = .opn

instance : DecidablePred isContentStart := fun t =>
  decidable_of_iff (t = .scal ∨ t = .opn) Iff.rfl

/-- `bal f a b` — the running depth change over `[a, b)`.  ONLY the shallow projection guard uses it —
    the deep guard is balance-free, which is exactly why its advance edge needs no re-basing. -/
def bal (f : Nat → Int) (a b : Nat) : Int := f b - f a

/-! ## The deep (all-depth, balance-free) guard — descend-stable, advance pays nothing

`Deep` is the toy of `FlowBodyContentDeep`: head content-start, plus EVERY opener and EVERY separator
(any depth, balance-FREE) followed by content-start.  Both recursion edges are restrictions of it. -/

/-- Toy of `FlowBodyContentDeep` — content facts at ALL depths, balance-free. -/
def Deep (hd : Nat → Tok) (lo hi : Nat) : Prop :=
  isContentStart (hd lo) ∧
  (∀ k, lo ≤ k → k + 1 < hi → tokDelta (hd k) = 1 → isContentStart (hd (k + 1))) ∧
  (∀ k, lo ≤ k → k + 1 < hi → hd k = .sep → isContentStart (hd (k + 1)))

/-! ## POSITIVE — the two edges are MIRRORS

`deep_descend` (toy of `flowBodyContentDeep_descend`) and `deep_advance` (toy of
`flowBodyContentDeep_advance`) below.  Read them side by side: the proof skeleton is IDENTICAL; the only
line that differs is the child-head case — `h_op k …` (opener field) for descend, `h_fe m …` (separator
field) for advance.  And `deep_advance` carries NO balance hypothesis and NO size side condition — the
whole point of R291: the strengthening that bought the descend edge bought this one in the same stroke. -/

/-- **DESCEND** (toy of `flowBodyContentDeep_descend`): transport `Deep` into the nested interior
    `[k+1, j)` whose opener is at `k`.  Child head off the OPENER field. -/
theorem deep_descend (hd : Nat → Tok) (lo k j hi : Nat)
    (h_deep : Deep hd lo hi) (h_lo_k : lo ≤ k) (h_open : tokDelta (hd k) = 1)
    (h_kj : k + 1 < j) (h_j_hi : j ≤ hi) :
    Deep hd (k + 1) j := by
  obtain ⟨_h_head, h_op, h_fe⟩ := h_deep
  refine ⟨?_, ?_, ?_⟩
  · -- child head off the OPENER field at `k` (the one differing line)
    exact h_op k h_lo_k (by omega) h_open
  · intro k' hk1 hk2 hopen; exact h_op k' (by omega) (by omega) hopen
  · intro k' hk1 hk2 hsep; exact h_fe k' (by omega) (by omega) hsep

/-- **ADVANCE** (toy of `flowBodyContentDeep_advance`): transport `Deep` into the tail `[m+1, hi)` after
    a separator at `m`.  Child head off the SEPARATOR field.  NOTE: no balance hypothesis, no size side
    condition — the verbatim mirror of `deep_descend`, the dividend of the lifted invariant. -/
theorem deep_advance (hd : Nat → Tok) (lo m hi : Nat)
    (h_deep : Deep hd lo hi) (h_lo_m : lo ≤ m) (h_sep : hd m = .sep) (h_m1_hi : m + 1 < hi) :
    Deep hd (m + 1) hi := by
  obtain ⟨_h_head, h_op, h_fe⟩ := h_deep
  refine ⟨?_, ?_, ?_⟩
  · -- child head off the SEPARATOR field at `m` (the one differing line)
    exact h_fe m h_lo_m h_m1_hi h_sep
  · intro k' hk1 hk2 hopen; exact h_op k' (by omega) (by omega) hopen
  · intro k' hk1 hk2 hsep; exact h_fe k' (by omega) (by omega) hsep

/-! ### Concrete GOOD streams — descend into `[ a a ]`, advance across `a , a` -/

/-- `hdGood`: `opn scal scal cls` — a nested sequence `[ a a ]`. -/
def hdGood : Nat → Tok
  | 0 => .opn
  | 3 => .cls
  | _ => .scal

theorem deep_good : Deep hdGood 0 4 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro k _ hk2 hopen
    match k with
    | 0 => exact (by decide : isContentStart (hdGood 1))
    | 1 => exact absurd hopen (by decide)
    | 2 => exact absurd hopen (by decide)
    | _ + 3 => omega
  · intro k _ hk2 hsep
    match k with
    | 0 => exact absurd hsep (by decide)
    | 1 => exact absurd hsep (by decide)
    | 2 => exact absurd hsep (by decide)
    | _ + 3 => omega

/-- `deep_descend` fires: the interior `[1, 3)` of the nested `[` at `0` is still `Deep`, its head
    re-seated to `hdGood 1 = scal` by the OPENER field. -/
theorem deep_descend_good : Deep hdGood 1 3 :=
  deep_descend hdGood 0 0 3 4 deep_good (by omega) (by decide) (by omega) (by omega)

/-- `hdAdv`: `scal sep scal` — a two-entry body `a , a`. -/
def hdAdv : Nat → Tok
  | 1 => .sep
  | _ => .scal

theorem deep_adv : Deep hdAdv 0 3 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro k _ hk2 hopen
    match k with
    | 0 => exact absurd hopen (by decide)
    | 1 => exact absurd hopen (by decide)
    | _ + 2 => omega
  · intro k _ hk2 hsep
    match k with
    | 0 => exact absurd hsep (by decide)
    | 1 => exact (by decide : isContentStart (hdAdv 2))
    | _ + 2 => omega

/-- `deep_advance` fires: the tail `[2, 3)` after the separator at `1` is still `Deep`, its head
    re-seated to `hdAdv 2 = scal` by the SEPARATOR field — the MIRROR of `deep_descend_good`, with no
    balance arithmetic anywhere. -/
theorem deep_advance_good : Deep hdAdv 2 3 :=
  deep_advance hdAdv 0 1 3 deep_adv (by omega) (by decide) (by omega)

#guard hdGood 1 = Tok.scal
#guard hdAdv 2 = Tok.scal

/-! ## NEGATIVE — re-deriving advance from the PROJECTION costs the balance gate

`Shallow` is the toy of R289's depth-`0` `FlowBodyContent` (the entry-level PROJECTION of `Deep`): its
separator clause is GATED by `bal lo k = 0`.  That gate is the projection's cost — `flowBodyContent_advance`
had to thread `bal lo (m+1) = 0` and re-base every premise.  On a stream whose separator sits at depth
`1`, the gate is false, so the shallow clause is VACUOUS and gives nothing about the post-separator head;
the deep guard's UN-gated separator field is exactly what repairs it.  This is why you must NOT re-derive
the lifted advance edge from the projection — write it as the descend mirror instead. -/

/-- Toy of `FlowBodyContent` (R289) — separators gated by `bal lo k = 0` (depth-`0` only). -/
def Shallow (f : Nat → Int) (hd : Nat → Tok) (lo hi : Nat) : Prop :=
  isContentStart (hd lo) ∧
  (∀ k, lo ≤ k → k + 1 < hi → hd k = .sep → bal f lo k = 0 → isContentStart (hd (k + 1)))

/-- `hdNeg`: `opn sep sep cls` — `[ , , ]`, a bracket whose separators sit at depth `1`. -/
def hdNeg : Nat → Tok
  | 0 => .opn
  | 1 => .sep
  | 2 => .sep
  | _ => .cls

/-- Cumulative depth for `hdNeg`: `0, 1, 1, 1, …` — the opener pushes to `1`, the interior sits there. -/
def fNeg : Nat → Int
  | 0 => 0
  | _ + 1 => 1

/-- The shallow guard HOLDS — its separators (at `1`, `2`) sit at balance `1`, so the depth-`0` gate
    `bal 0 k = 0` is false and the clause is vacuous there. -/
theorem shallow_holds_neg : Shallow fNeg hdNeg 0 4 := by
  refine ⟨by decide, ?_⟩
  intro k _ hk2 hsep hbal
  match k with
  | 0 => exact absurd hsep (by decide)
  | 1 => exact absurd hbal (by decide)
  | 2 => exact absurd hbal (by decide)
  | _ + 3 => omega

/-- …yet the head right AFTER the depth-`1` separator is itself a SEPARATOR, not content-start.  So the
    shallow guard, though true, yields NOTHING toward advancing past that separator — the masked cost the
    balance gate hides. -/
theorem interior_after_sep_not_content : ¬ isContentStart (hdNeg 2) := by
  rintro (h | h) <;> exact absurd h (by decide)

/-- The DEEP guard's UN-gated separator field is exactly the repair: it demands the post-separator head be
    content-start at EVERY depth, so it correctly REJECTS this stream — which is why advance, written as
    the descend mirror over `Deep`, is only ever reached on streams where re-seating succeeds. -/
theorem not_deep_neg : ¬ Deep hdNeg 0 4 := by
  rintro ⟨_, _, h_fe⟩
  exact interior_after_sep_not_content (h_fe 1 (by omega) (by omega) (by decide))

#guard hdNeg 1 = Tok.sep
#guard hdNeg 2 = Tok.sep

end Tests.Reflections.LiftOnceMirrorEasyEdge
