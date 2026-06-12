/-!
# Reflection 392 — a deferred universal consumed ONLY by restriction lemmas hides its own
falsity; probe it at the ROOT (the un-restricted instance) before producing it.

Self-contained core-Lean toy of L4YAML R392.  A recursion threads an all-depth content guard
`P window` whose only lemmas are RESTRICTIONS (`P` wide-window → `P` narrow-window: descend /
advance / `window_of_root`).  Every such lemma is CONDITIONAL on `P` holding at the wider window,
so the whole family typechecks GREEN whether or not `P` is ever true — `P`'s truth is exercised
nowhere except the ROOT (the widest window, the one a PRODUCER must build from primitives, never
restrict).  R391 ([[ref-deep-conjunct-root-seed-only]]) reduced the per-window provider to that
single root seed; R392 probes the root FIRST and finds it FALSE on real scanned output.

Mapping to L4YAML: `opener`/`content` ~ "position is a flow opener (`[`/`{`)" / "next token is a
content-start head"; the all-depth `AllDeepP` ~ `FlowBodyContentDeep.openerContentStart`
(∀ opener, next is content-start); `restrict_window` ~ `flowBodyContentDeep_descend`/`_advance`/
`_window_of_root` (all CONDITIONAL on the wider `P`); `root_false` ~
`flowBodyContentDeep_root_seed_false` (the `native_decide` refutation on `[[]]`); the `realViolator`
~ a `{` opener whose successor is `.key`, or an empty `[]` whose successor is `]` — positions a
flow-MAP interior or empty bracket forces, where the seq-convention `opener→content` simply does not
hold, but which the recursion routes to LEAVES and so never CONSUMES.

POSITIVE: `restrict_window` — a restriction consumer typechecks for ANY `a`, CONDITIONAL on `AllDeepP`;
it can never expose `AllDeepP`'s falsity.  `scoped_holds` — the correctly-scoped fact (consumed
positions only) IS true, the fix's target.
NEGATIVE: `root_false` — the un-restricted ROOT instance of `AllDeepP` is FALSE (a real `opener`
position whose successor is non-content); and `violator_is_real` — that violating position is REAL,
so a dispatch that READS `AllDeepP` to EXCLUDE it is unsound, not merely unprovable.

Sharpens [[ref-probe-deferred-universal-before-producing]] (probe the ROOT, the un-restricted instance)
and [[ref-probe-provider-head-blind-gate]] (convention-blind, not head-blind).
-/

namespace Tests.Reflections.RestrictionHidesRootFalsity

set_option autoImplicit false

/-! ## The toy positions.

`opener 0` is a genuine flow-sequence opener whose successor (position `1`) is a content-start head.
`opener 3` is a flow-MAPPING opener whose successor (position `4`) is a non-content `.key` token —
the all-depth field over-reaches into this map-interior position, where the seq convention fails. -/

def opener : Nat → Bool
  | 0 => true
  | 3 => true
  | _ => false

def content (k : Nat) : Bool := k != 4   -- position 4 (a `.key`) is NOT a content-start head

/-- The all-depth universal the recursion threads (= `openerContentStart`). -/
def AllDeepP : Prop := ∀ k, opener k = true → content (k + 1) = true

/-- **POSITIVE — a restriction consumer typechecks GREEN, CONDITIONAL on `AllDeepP`.**  It narrows
    the universal to `[a, ∞)` and can never test `AllDeepP`'s truth — exactly `descend`/`advance`/
    `window_of_root`, which is why a whole family of them stays green over a FALSE `AllDeepP`. -/
theorem restrict_window (h : AllDeepP) (a : Nat) :
    ∀ k, a ≤ k → opener k = true → content (k + 1) = true :=
  fun k _ ho => h k ho

/-- **NEGATIVE — the un-restricted ROOT instance of `AllDeepP` is FALSE.**  `opener 3` holds but
    `content 4 = false` (the map opener's successor is a `.key`).  Only probing the root — never any
    restriction consumer — exposes this. -/
theorem root_false : ¬ AllDeepP := by
  intro h
  exact absurd (h 3 (by decide)) (by decide)

/-- **NEGATIVE (sharper) — the violating position is REAL.**  A dispatch that READS `AllDeepP` to
    EXCLUDE such a position (the empty-bracket / map case) is therefore UNSOUND for real inputs. -/
def realViolator : Nat := 3
theorem violator_is_real :
    opener realViolator = true ∧ content (realViolator + 1) = false := by decide

/-- **POSITIVE — the correctly-scoped fact (the fix's target) IS true.**  Restricting the universal
    to the positions the recursion actually CONSUMES (seq openers, here `k = 0`, excluding the map
    opener `k = 3`) gives a true statement — re-scoping, not producing, is the fix. -/
theorem scoped_holds : ∀ k, opener k = true → k ≠ 3 → content (k + 1) = true := by
  intro k _ho hne
  simp only [content, bne_iff_ne, ne_eq]
  omega

#guard opener 0 == true       -- a genuine seq opener
#guard content 1 == true      -- its successor is content-start (consumed position holds)
#guard opener 3 == true       -- a map opener
#guard content 4 == false     -- its successor is a `.key` — the root fails HERE (never consumed)

end Tests.Reflections.RestrictionHidesRootFalsity
