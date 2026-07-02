/-!
# Reflection 303 — probing a deferred `provider` universal before producing it catches a FALSE universal: a HEAD-BLIND gate admits spurious windows where the body-structure route is undischargeable

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind the de-risk that
re-scoped `(i'-b-descend-root-provider-descent)`.

The real situation: a recursion plans to prove a separator carrier by a `provider` universal that
delivers `SafeBodyUnit ContentStartTok ((take b).drop a)` at every window `[a,b)` satisfying a gate
`SeqTypedInterior` (balance-`0` ∧ enclosing-seq). But the gate is **head-blind** — it never looks at
whether the window's first token is a content start — so it ADMITS separator-headed windows, where
`SafeBodyUnit` is false (a `SafeBodyUnit`'s head must be a content start). The minimal pair on the
real scan of `[[1, 2], 9]` found two such windows (the depth-`0` commas at indices `4`, `7`). So the
`provider` is undischargeable: probing the deferred universal BEFORE producing it caught the
falsity, converting a planned descent recursion into a retargeted direct discharge.

Toy substrate: tokens are `Nat`s — `0` = the separator (toy `.flowEntry`), positive = a content
token (toy `ContentStartTok`). `Body` = the toy `SafeBodyUnit`: nonempty content-headed entries
separated by single `0`s. `Gate` = the toy head-blind gate: it accepts any nonempty balanced slice
(every toy token has bracket-delta `0`, mirroring that `.flowEntry` and a scalar both have
`flowBracketDelta = 0`) WITHOUT inspecting the head — so `Gate [0]` (a lone separator) holds.
-/

namespace Tests.Reflections.ProbeDeferredProviderHeadBlindGate

set_option autoImplicit false

/-- Toy bracket-delta: every toy token is delta-`0` (a separator `0` and a content `n>0` both, just
    as `flowBracketDelta .flowEntry = 0` and `flowBracketDelta (.scalar …) = 0`). The toy has no
    brackets — it isolates the head-blindness, which is the whole point. -/
def delta (_ : Nat) : Int := 0

/-- **The HEAD-BLIND gate** (toy `SeqTypedInterior`): a nonempty slice whose bracket-balance is `0`.
    It NEVER inspects whether the head token is a content start — exactly the blindness that lets the
    real gate admit separator-headed windows. -/
def Gate (l : List Nat) : Prop := l ≠ [] ∧ (l.map delta).sum = 0

/-- Every toy slice has bracket-balance `0` (every token is delta-`0`). -/
theorem sum_map_delta (l : List Nat) : (l.map delta).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.map_cons, List.sum_cons, delta, ih]

/-- The toy balance is identically `0`, so `Gate` reduces to nonemptiness — head-blind by
    construction. -/
theorem gate_iff_ne_nil (l : List Nat) : Gate l ↔ l ≠ [] := by
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, sum_map_delta l⟩

/-- **The toy `SafeBodyUnit`** (`Body`): nonempty content-headed entries separated by single `0`s.
    `single x` is one content token; `cons x rest` is a content token, a separator `0`, then a `Body`.
    A separator-headed or trailing-separator slice has NO constructor. -/
inductive Body : List Nat → Prop where
  | single (x : Nat) (h : 0 < x) : Body [x]
  | cons (x : Nat) (rest : List Nat) (h : 0 < x) (h_rest : Body rest) : Body (x :: 0 :: rest)

/-- **The kernel — a `Body` forces a CONTENT head** (toy of `SafeBodyUnit_head_Q`): the precondition
    the `provider`'s deliverable carries that the head-blind `Gate` does NOT supply. In both
    constructors the head is the content token `x` with `0 < x`. -/
theorem Body_head_content : ∀ {l : List Nat}, Body l → (h : l ≠ []) → 0 < l.head h
  | _, .single x hx, _ => hx
  | _, .cons x rest hx _hr, _ => hx

/-- **A separator-headed window is NOT a `Body`** (toy of `not_safeBodyUnit_of_head_flowEntry`): the
    dead-end guard. The head is `0`, but a `Body` forces a positive head. -/
theorem not_Body_of_head_zero {l : List Nat} (h_ne : l ≠ []) (h_head : l.head h_ne = 0) :
    ¬ Body l := fun h => by
  have := Body_head_content h h_ne; rw [h_head] at this; exact absurd this (by decide)

/-! ## The minimal pair — both windows satisfy the head-blind gate; only the content-headed one is a `Body` -/

-- GOOD window `[1, 0, 2]` (content, separator, content): satisfies the gate AND is a `Body`.
theorem gate_good : Gate [1, 0, 2] := (gate_iff_ne_nil _).2 (by decide)
theorem body_good : Body [1, 0, 2] := .cons 1 [2] (by decide) (.single 2 (by decide))

-- BAD sibling `[0]` (a lone separator — toy of the gated commas at indices 4, 7 of `[[1,2],9]`):
-- the gate STILL holds (head-blind), but it is NOT a `Body`.
theorem gate_bad : Gate [0] := (gate_iff_ne_nil _).2 (by decide)
theorem not_body_bad : ¬ Body [0] := not_Body_of_head_zero (by decide) (by decide)

-- NECESSARY-BUT-NOT-SUFFICIENT: a CONTENT-headed window can still fail `Body` — the trailing
-- separator `[1, 0]` (toy of the gated, content-start-headed `"1" ,` at window [3,5)). So
-- content-start-alignment alone would NOT rescue the provider.
theorem gate_trailing : Gate [1, 0] := (gate_iff_ne_nil _).2 (by decide)
theorem not_body_trailing : ¬ Body [1, 0] := by
  intro h
  cases h with
  | cons x rest hx h_rest => cases h_rest   -- rest = [] has no `Body`

/-! ## Decidable witnesses -/

-- The gate is head-blind: it accepts the lone separator exactly as it accepts content.
#guard decide ([0] ≠ ([] : List Nat))        -- Gate [0] reduces to this
#guard decide ([1, 0, 2] ≠ ([] : List Nat))  -- Gate [1,0,2] reduces to this
-- The would-be discriminator (head is content) separates the pair...
#guard ([1, 0, 2].head (by decide)) == 1      -- good window: content head
#guard ([0].head (by decide)) == 0            -- bad window: separator head
-- ...but does NOT suffice: the trailing-separator window is content-headed yet not a `Body`.
#guard ([1, 0].head (by decide)) == 1         -- content head, still ¬ Body (not_body_trailing)

/-- POSITIVE — the full lesson in one term: a window can satisfy the head-blind gate yet NOT be a
    `Body`, so a `provider : ∀ window, Gate window → Body window` is FALSE. Witnessed at `[0]`. -/
theorem provider_is_false : ¬ (∀ l, Gate l → Body l) := fun provider =>
  not_body_bad (provider [0] gate_bad)

/-- POSITIVE — but the GOOD window discharges, so the carrier is true where the recursion actually
    instantiates it (real bodies + comma-suffix tails), which the redirect targets directly. -/
theorem good_window_discharges : Gate [1, 0, 2] ∧ Body [1, 0, 2] := ⟨gate_good, body_good⟩

end Tests.Reflections.ProbeDeferredProviderHeadBlindGate
