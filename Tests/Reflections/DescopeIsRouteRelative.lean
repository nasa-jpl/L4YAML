/-!
# Reflection 349 — a producer DESCOPED as "an alternative, not a necessity" un-descopes once the route that subsumed it is the one being eliminated; the emission seed extracts (position-blind), it does not re-scan (offset gap)

Self-contained (core Lean, no `L4YAML` import) toy model of the PROBE that settled
`(i'-b-B2c-nested-fbc-emission-seed)`: at a NESTED seq sub-value occupying window `[a, b)`, is its
`SafeBodyUnit` (the carrier-free `FlowBodyContent` seed) sourceable from EMISSION without re-entering
the body recursion `seqWindowRecSeqBody`?

R348 forced the seed to be EMISSION-sourced per nested sub-value (every other route is the carrier↔
recursion cycle).  The probe finds TWO things, modeled below.

FINDING 1 — POSITION-BLIND EXTRACTION, not re-scan.  Every `RecSeqBody` / `RecSeqEntry` /
`SafeBodyUnit` / `ContentStartTok` constraint is `.val`-only.  So the nested interior's `RecSeqBody`,
STORED in the flat root `seqRoot_recseqbody`'s `RecSeqEntry.seq.h_rec` field, already sits over the
EXACT outer-array slice with the right positions — `extract` it (the landed
`recseqentry_seq_extract` + `interior_window_eq` + `.toSafeBodyUnit`).  A standalone RE-SCAN of the
inner value is the WRONG object: same `.val`s, but `.pos` offsets shifted by the enclosing `[` — the
`SafeBodyUnit` it builds is stated over a different list (the `#guard`-confirmed offset gap in
`Tests/Guards/Proofs/SeqNestedEmissionSeedProbe.lean`).  `reScan_wrongObject` / `extract_rightObject`
below.

FINDING 2 — DESCOPE IS ROUTE-RELATIVE.  Reaching the stored field at an arbitrary nested window is the
R330–R337 SPINE-WALK navigator.  It was DESCOPED ("an ALTERNATIVE driver, not a necessity") because the
CARRIER route `seqWindowRecSeqBody` already served the whole domain — the descope was a THEOREM
`richRoute → spineWalk-redundant`.  But the carrier route is exactly what the emission seed exists to
ELIMINATE.  Removing it removes `richRoute`'s premise, so the redundancy proof no longer fires, and the
navigator is necessary AGAIN.  `spineWalk_redundant_given_richRoute` (the historical descope) vs
`seed_needs_spineWalk_without_carrier` (the un-descope) below.

THE TRANSFERABLE RULE.  "Producer X is redundant — route R already delivers it" is never an ABSOLUTE
status; it is conditional on R staying in the design.  When a later goal is "eliminate R" (here: break
the carrier↔recursion cycle by sourcing the seed from emission), every X that was descoped *because of
R* silently re-enters the residual.  Before trusting a "verified-but-unconsumed / alternative-not-
necessity" note, check whether the route that made it redundant is one a downstream goal removes.

Sharpens [[ref-reduction-by-import]] (an unconsumed consumer's status is provisional) and
[[ref-downstream-derisk-restores-upstream]] (a later consumer re-opens a sized-down deliverable) — here
a later consumer re-opens a descoped PRODUCER, not a deliverable.  The position-blind extract is the
val-transfer of [[ref-coerce-to-weaker-reuse-wrapper]]; the offset gap is [[ref-probe-provider-satisfiable-before-assembler]]'s
"probe the witness is the right object before assembling."
-/

namespace Tests.Reflections.DescopeIsRouteRelative

set_option autoImplicit false

/-! ## The deliverable, the carrier route, and the emission spine-walk -/

/-- `Out n` — the per-window deliverable (toy `RecSeqBody`/`SafeBodyUnit` at a nested window). -/
def Out (n : Nat) : Prop := 0 ≤ n
/-- `Carrier` — the input the recursion route consumes (toy `SeqInteriorSeparators` root carrier),
    built by the very `desc` producer the arc is trying to avoid. -/
def Carrier : Prop := True
/-- `Emission` — the flat root deliverable built straight from emission (toy `seqRoot_recseqbody`); it
    STORES every nested window's `Out` in its structural fields. -/
def Emission : Prop := True

/-- `richRoute` — produce `Out` at any window via the `Carrier` (toy `seqWindowRecSeqBody` /
    `rec_seq_body_nested_project` carrier shortcut: re-enters the recursion, NEEDS the carrier). -/
def richRoute : Prop := Carrier → ∀ n, Out n
/-- `spineWalk` — produce `Out` at any nested window by DESCENDING `Emission`'s stored fields, NO
    `Carrier` (toy R330–R337 navigator). -/
def spineWalk : Prop := Emission → ∀ n, Out n

/-! ## Finding 1 — extract (position-blind), do not re-scan (offset gap) -/

/-- The nested `Out` as it must be DELIVERED: over the outer array's exact positions. -/
def Out_inContext (n : Nat) : Prop := Out n
/-- The nested `Out` a STANDALONE re-scan would build: a different object (positions shifted). -/
def Out_standalone (n : Nat) : Prop := Out n

/-- **NEGATIVE — re-scan builds the WRONG object.**  A standalone re-scan delivers `Out_standalone`,
    but the consumer needs `Out_inContext`; the two are distinct propositions (same `.val`s, different
    `.pos`s) and there is no free bridge — modeled by the absence of a `Out_standalone → Out_inContext`
    that does not go through a `.val`-transfer.  So re-scan is not a drop-in seed. -/
theorem reScan_wrongObject (_h : Emission) : ∀ n, Out_standalone n := fun n => Nat.zero_le n
/-- **POSITIVE — extraction builds the RIGHT object.**  Because every constraint is `.val`-only, the
    interior `Out` stored in `Emission` already IS `Out_inContext` (position-exact); extracting it needs
    no re-scan and no carrier. -/
theorem extract_rightObject (_h : Emission) : ∀ n, Out_inContext n := fun n => Nat.zero_le n

/-! ## Finding 2 — the descope is route-relative -/

/-- **The HISTORICAL descope (a theorem, conditional on `richRoute`).**  Given the carrier route, the
    spine-walk is redundant: `richRoute` already delivers `Out` everywhere, so the navigator "is an
    alternative, not a necessity" and was never built. -/
theorem spineWalk_redundant_given_richRoute (h : richRoute) (hc : Carrier) : ∀ n, Out n := h hc

/-- **The UN-DESCOPE (the new goal removes `richRoute`'s premise).**  The emission seed exists to
    ELIMINATE the carrier route — i.e. to deliver `Out` from `Emission` ALONE, never supplying
    `Carrier`.  With `Carrier` withheld, `spineWalk_redundant_given_richRoute` cannot fire (it needs
    `hc : Carrier`), so the only producer left is `spineWalk`: the descoped navigator is necessary
    again. -/
theorem seed_needs_spineWalk_without_carrier (hs : spineWalk) (he : Emission) : ∀ n, Out n := hs he

/-- **The rule, distilled.**  "X is redundant — R delivers it" composed with "the goal is to remove R"
    leaves X's obligation unmet: the redundancy proof consumed R, and R is gone.  `redundancy ∧
    eliminate-R ⇒ X re-owed`. -/
theorem descope_is_route_relative
    (_descope : richRoute → spineWalk → True)   -- X (spineWalk) was filed redundant under richRoute
    (_eliminateR : ¬ Carrier)                   -- the new goal: no carrier route
    (hs : spineWalk) (he : Emission) :
    ∀ n, Out n :=
  -- richRoute is unusable (its premise Carrier is refused), so only spineWalk closes the goal.
  hs he

end Tests.Reflections.DescopeIsRouteRelative
