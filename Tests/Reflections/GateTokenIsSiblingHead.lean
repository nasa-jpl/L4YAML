/-!
# Reflection 425 — the gate token of a shared GATED edge field IS the discriminating sibling's head

Self-contained (core Lean, no `L4YAML` import) toy of the R425 finding.  Threading the field-(ii)
`≠ .key`-gated head `∀ h0, block[0] ≠ .key → isFlowContentStart block[0]` through the TWO list-body
defs — `EmitListScansInFlowBlock` (SEQ) and `EmitPairListScansInFlowBlock` (MAP) — discharges the SAME
field in OPPOSITE ways:

* **SEQ.** A seq entry's block head is a value's content-start head, so `isFlowContentStart block[0]`
  is genuinely TRUE; the `≠ .key` gate is irrelevant and DISCARDED.  (Substantive discharge.)
* **MAP.** A map entry's block is `⟨_, .key, _⟩ :: …` — head literally `.key`, so the conclusion is
  FALSE.  The field survives ONLY because the gate premise `block[0] ≠ .key` is FALSE: it holds
  VACUOUSLY.  The gate token `.key` IS the map head; it gates out exactly the axis where the
  conclusion fails.  (Vacuous discharge.)

So the gate is LOAD-BEARING for the map axis (without it the field is false there) and FREE for the
seq axis.  The gate token is read off the DISCRIMINATING sibling's constructor — choosing it WRONG
(a token that is NOT the failing sibling's head) leaves the field FALSE for that sibling.

This is the multi-axis dual of `GuardedUniversalFoldRelocatesGuard` (the gated-out region is one
entire sibling AXIS) and complements `InvariantNeutralSiblingNeedsHead` (R424 also bifurcated a
single field's discharge by the head token, but by ADDING a hypothesis; here by REFUTING the gate).
-/

namespace Tests.Reflections.GateTokenIsSiblingHead

set_option autoImplicit false

/-- Toy tokens: a `content` start, the `key` marker (a map entry's leading token), and an `opener`. -/
inductive Tok | content | key | opener
  deriving DecidableEq

/-- The conclusion predicate (toy of `isFlowContentStart`): only `content` is a content start. -/
def isContent : Tok → Bool
  | .content => true
  | _ => false

/-- The shared GATED edge field, parameterised by the gate token `K`: a nonempty block's head is a
    content start UNLESS it is `K`.  (Toy of `∀ h0, block[0] ≠ K → isFlowContentStart block[0]`.) -/
def GatedHead (K : Tok) (block : List Tok) : Prop :=
  ∀ (h0 : 0 < block.length), (block[0]'h0) ≠ K → isContent (block[0]'h0) = true

/-! ## Two sibling axes build their head DIFFERENTLY. -/

/-- A SEQ entry block: head is `content` (a value's content-start head), then arbitrary tail. -/
def seqEntry (tail : List Tok) : List Tok := Tok.content :: tail

/-- A MAP entry block: head is literally `key` (the leading colon-key marker), then arbitrary tail. -/
def mapEntry (tail : List Tok) : List Tok := Tok.key :: tail

/-! ## With the gate token = the MAP head (`key`), BOTH siblings discharge — differently. -/

/-- **POSITIVE (seq, substantive)** — the seq head is `content`, so the conclusion holds and the gate
    `≠ key` is DISCARDED (we never use the premise). -/
theorem seq_field_holds (tail : List Tok) : GatedHead Tok.key (seqEntry tail) := by
  intro h0 _                     -- gate premise discarded
  rfl                            -- isContent content = true

/-- **POSITIVE (map, vacuous)** — the map head is `key`, so `isContent` would be FALSE; the field
    survives ONLY because the gate premise `head ≠ key` is FALSE.  The gate token `key` IS the map
    head — read off the constructor, not invented. -/
theorem map_field_holds_vacuously (tail : List Tok) : GatedHead Tok.key (mapEntry tail) := by
  intro h0 hne
  -- head of `mapEntry tail` is `key`, contradicting `hne : head ≠ key`
  exact absurd (by simp [mapEntry] : (mapEntry tail)[0]'h0 = Tok.key) hne

/-! ## Choosing the gate token WRONG (≠ opener) leaves the field FALSE for the map. -/

/-- **NEGATIVE** — gate on `≠ opener` instead of `≠ key`: the map entry `[key]` now has a TRUE gate
    premise (`key ≠ opener`) but a FALSE conclusion (`isContent key = false`), so the field is FALSE.
    The gate must be the discriminating sibling's HEAD (`key`), not an arbitrary token. -/
theorem wrong_gate_undergates : ¬ GatedHead Tok.opener (mapEntry []) := by
  intro h
  -- h forces isContent key = true, but it is false
  exact absurd (h (by simp [mapEntry]) (by decide)) (by decide)

#guard isContent Tok.content == true   -- seq head: conclusion TRUE  (gate discarded)
#guard isContent Tok.key == false      -- map head: conclusion FALSE (gate `≠ key` rescues vacuously)

end Tests.Reflections.GateTokenIsSiblingHead
