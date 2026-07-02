/-
# Reflection 290 — a guard sized to its easy edge can be structurally incapable of its hard edge

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in Blueprint
Reflection 290, the sequel to `ref-additive-parallel-type-over-shared-edit` / R289 and a fresh
instance of `ref-converse-forward-invariant-asymmetry` (descend needs the strictly-stronger invariant)
fused with `ref-probe-deferred-universal-before-producing` (probe the hard edge before building it).

**The principle.** A body-recursion guard is threaded across two edges: ADVANCE (move to the tail after
a separator) and DESCEND (recurse into a nested bracket's interior).  R289 named a content guard and
landed its ADVANCE edge cheaply — and the very ease of that edge MASKED that the guard, as defined, is
structurally incapable of the DESCEND edge.  The DESCEND edge must hand the nested interior `[k+1, j)`
its head `hd (k+1)` as content-start; but that head sits one nesting level DOWN (balance `1` relative to
the outer origin), while a guard whose fields are all gated by *depth-`0`* facts (`bal lo k = 0`) has
NOTHING that reaches it.  No outer field is even *about* the interior head — the edge is not hard to
prove, the guard is too weak to carry.

The remedy is NOT more proof effort: it is a stronger invariant.  Lift the guard to carry content at
ALL depths (balance-condition-FREE), and the guard becomes a pure RESTRICTION of itself on every
sub-window, so the DESCEND edge falls out as triviality.

**What this demo asserts (fails the build if it ever drifts):**
  * NEGATIVE — the shallow (depth-`0`) guard is too weak for descend: `shallow_holds` shows a nested
    stream `[ , a ]` (a leading-separator interior) satisfies the shallow guard, yet
    `interior_head_not_contentstart` shows its interior head is a separator — so the shallow guard, which
    holds, cannot possibly yield the interior's content guard.  `not_deep` confirms the deep guard
    correctly REJECTS the same stream (its opener field demands the interior head be content-start).
  * POSITIVE — the deep (all-depth) guard descends as a pure restriction: `deep_descend` (toy of
    `flowBodyContentDeep_descend`) transports the deep guard into the interior with no re-basing and no
    bracket arithmetic — child head off the parent's opener field, child fields the parent's quantifiers
    restricted.  `deep_descend_good` fires it concretely on `[ a a ]`, yielding the interior guard on
    `[1, 3)` with head `scal`.
-/
set_option autoImplicit false

namespace Tests.Reflections.DescendStrengthInvariant

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

/-- `bal f a b` — the running depth change over `[a, b)`, `f i` the cumulative depth after `i` tokens
    (toy of `flowBracketBalance`).  ONLY the shallow guard uses it — the deep guard is balance-free. -/
def bal (f : Nat → Int) (a b : Nat) : Int := f b - f a

/-! ## The two guards — shallow (depth-`0`, too weak) and deep (all-depth, descend-stable)

`Shallow` is the toy of R289's `FlowBodyContent`: head content-start, plus *depth-`0`* separators
(gated by `bal lo k = 0`) followed by content-start.  It has NO opener field.
`Deep` is the toy of `FlowBodyContentDeep`: head content-start, plus EVERY opener and EVERY separator
(any depth, balance-FREE) followed by content-start. -/

/-- Toy of `FlowBodyContent` (R289) — content facts at the entry level only (depth-`0` separators). -/
def Shallow (f : Nat → Int) (hd : Nat → Tok) (lo hi : Nat) : Prop :=
  isContentStart (hd lo) ∧
  (∀ k, lo ≤ k → k + 1 < hi → hd k = .sep → bal f lo k = 0 → isContentStart (hd (k + 1)))

/-- Toy of `FlowBodyContentDeep` — content facts at ALL depths, balance-free. -/
def Deep (hd : Nat → Tok) (lo hi : Nat) : Prop :=
  isContentStart (hd lo) ∧
  (∀ k, lo ≤ k → k + 1 < hi → tokDelta (hd k) = 1 → isContentStart (hd (k + 1))) ∧
  (∀ k, lo ≤ k → k + 1 < hi → hd k = .sep → isContentStart (hd (k + 1)))

/-! ## POSITIVE — the deep guard descends as a pure restriction

`deep_descend` is the toy of `flowBodyContentDeep_descend`: transport `Deep` from `[lo, hi)` into the
nested interior `[k+1, j)` whose opener is at `k`.  The child head `hd (k+1)` is the parent's opener
field at `k`; the child's opener/separator fields are the parent's quantifiers restricted.  No
re-basing, no bracket arithmetic — that is the whole dividend of the all-depth formulation. -/

/-- **DESCEND deep-content-preservation** (toy of `flowBodyContentDeep_descend`). -/
theorem deep_descend (hd : Nat → Tok) (lo k j hi : Nat)
    (h_deep : Deep hd lo hi) (h_lo_k : lo ≤ k) (h_open : tokDelta (hd k) = 1)
    (h_kj : k + 1 < j) (h_j_hi : j ≤ hi) :
    Deep hd (k + 1) j := by
  obtain ⟨_h_head, h_op, h_fe⟩ := h_deep
  refine ⟨?_, ?_, ?_⟩
  · -- child head `hd (k+1)` content-start: the parent's opener field at `k` (`k+1 < j ≤ hi`).
    exact h_op k h_lo_k (by omega) h_open
  · -- child opener field: the parent's, restricted to `[k+1, j) ⊆ [lo, hi)`.
    intro k' hk1 hk2 hopen; exact h_op k' (by omega) (by omega) hopen
  · -- child separator field: the parent's, restricted to `[k+1, j) ⊆ [lo, hi)`.
    intro k' hk1 hk2 hsep; exact h_fe k' (by omega) (by omega) hsep

/-! ### A concrete GOOD nested stream — `[ a a ]` — the deep guard descends into `[ a a ]`'s interior -/

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

/-- `deep_descend` fires: the interior `[1, 3)` of the nested `[` at `0` (close at `3`) is still `Deep`,
    its head re-seated to `hdGood 1 = scal` by the opener field — the DESCEND edge landed. -/
theorem deep_descend_good : Deep hdGood 1 3 :=
  deep_descend hdGood 0 0 3 4 deep_good (by omega) (by decide) (by omega) (by omega)

#guard hdGood 0 = Tok.opn
#guard hdGood 1 = Tok.scal

/-! ## NEGATIVE — the shallow guard holds on a stream whose interior head it cannot constrain

`hdBad` = `[ , a ]`: a nested bracket with a LEADING SEPARATOR interior (an empty first entry).  The
shallow guard HOLDS — its only separator sits at balance `1` (inside the bracket), so the depth-`0`
gate `bal 0 k = 0` makes its clause vacuous there.  But the interior head `hdBad 1 = sep` is NOT
content-start, so the shallow guard, though true, gives NOTHING toward the interior's content guard —
exactly the insufficiency the deep guard's opener field repairs (`not_deep`). -/

/-- `hdBad`: `opn sep scal cls` — a nested sequence `[ , a ]` with a leading-separator interior. -/
def hdBad : Nat → Tok
  | 0 => .opn
  | 1 => .sep
  | 3 => .cls
  | _ => .scal

/-- Cumulative depth for `hdBad`: `0, 1, 1, 1, 0` — the opener pushes to `1`, the interior sits there. -/
def fBad : Nat → Int
  | 0 => 0
  | _ + 1 => 1

/-- The shallow guard HOLDS: head `opn` is content-start, and its only separator (at `1`) sits at
    balance `1`, so the depth-`0` gate `bal 0 1 = 0` is false and the clause is vacuous. -/
theorem shallow_holds : Shallow fBad hdBad 0 4 := by
  refine ⟨by decide, ?_⟩
  intro k _ hk2 hsep hbal
  match k with
  | 0 => exact absurd hsep (by decide)
  | 1 => exact absurd hbal (by decide)
  | 2 => exact absurd hsep (by decide)
  | _ + 3 => omega

/-- …yet the interior head is a SEPARATOR, not content-start.  The shallow guard holds but cannot yield
    `Deep hdBad 1 3` (its head field would demand exactly this) — the masked insufficiency. -/
theorem interior_head_not_contentstart : ¬ isContentStart (hdBad 1) := by
  rintro (h | h) <;> exact absurd h (by decide)

/-- The DEEP guard correctly REJECTS the same stream: its opener field at `0` demands the interior head
    `hdBad 1` be content-start, which fails — so the descend edge would never be reached on a bad stream
    (the guard's strength is exactly what excludes it). -/
theorem not_deep : ¬ Deep hdBad 0 4 := by
  rintro ⟨_, h_op, _⟩
  exact interior_head_not_contentstart (h_op 0 (by omega) (by omega) (by decide))

end Tests.Reflections.DescendStrengthInvariant
