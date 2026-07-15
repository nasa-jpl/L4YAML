/-!
# Reflection 339 — a probe of a would-be COMPLEMENT provider REFUTES its necessity

Self-contained (core Lean, no `L4YAML` import) toy model of the decision behind
`seqEnclosed_of_seqTypedInterior`.

A navigator framing introduced a STRONG predicate `StrongPath` to restrict a provider's domain, and
the plan called for a SECOND ("complement") provider for the windows where `StrongPath` FAILS.  The
probe — run BEFORE authoring the complement — refutes its necessity by reading three things:

* **the PRODUCER is path-blind** — it threads only a WEAKER predicate `Enclosed`, never `StrongPath`,
  and its recursion STOPS at the severed-edge leaves (so the complement's windows are never reached);
* **`Enclosed` is PATH-INVARIANT** — here modelled as the *top* of a typed stack, `true` for every
  window's own opener regardless of the deeper path `StrongPath` tracks;
* **the consumer's GATE definitionally CONTAINS `Enclosed`** — `Gate.enc` IS the producer's `Enclosed`
  need, handed over free, identically for `StrongPath`-windows and `¬StrongPath`-windows.

So the complement provider is UNNECESSARY and `StrongPath` is VESTIGIAL: the bridge that plugs the
producer into the consumer is the one-line projection `enclosed_of_gate g := g.enc` (mirrors
`seqEnclosed_of_seqTypedInterior tokens a b h := h.2.1`).

`StrongPath` here is the whole stack all-`true`; `Enclosed` is just its HEAD — the same head the gate
already carries.  The `#guard`s exhibit a window where `StrongPath` FAILS (a `false` deeper in the
stack) yet `Gate` still HOLDS (its `enc` head is `true`) — the producer serves it through the gate,
no complement needed.
-/

namespace Tests.Reflections.ProbeRefutesComplementProvider

set_option autoImplicit false

/-- A window's typed enclosure stack (head = immediate frame; tail = deeper path to the root).
    `true` = a sequence `[` frame, `false` = a mapping `{` frame.  Mirrors the `btFold` typed stack. -/
abbrev Stack := List Bool

/-- The PRODUCER's only path-sensitive need: the immediate enclosing frame is a sequence (`true`).
    Reads ONLY the HEAD — PATH-INVARIANT (blind to the tail / deeper path).  Mirrors
    `SeqEnclosed tokens a := (btFold (some []) (take a)).bind (·.head?) = some true`. -/
def Enclosed (s : Stack) : Prop := s.head? = some true

/-- The STRONG navigator-domain predicate: the WHOLE stack is all-`true` (every frame to the root is a
    sequence — no `{` anywhere on the path).  Mirrors
    `SeqPathAllSeq tokens lo := ∃ s, … ∧ s.all (· == true)`.  STRICTLY stronger than `Enclosed`. -/
def StrongPath (s : Stack) : Prop := s ≠ [] ∧ s.all (· == true) = true

/-- The CONSUMER's gate the provider quantifies under.  Its `enc` field is *definitionally* the
    producer's `Enclosed` need.  Mirrors `SeqTypedInterior`, whose 2nd conjunct IS `SeqEnclosed`. -/
structure Gate (s : Stack) : Prop where
  /-- balance-style numeric conjunct (here a stand-in flag) -/
  bal : True
  /-- the enclosure conjunct — IDENTICAL to the producer's `Enclosed s` need -/
  enc : s.head? = some true
  /-- a floor-style conjunct (stand-in) -/
  floor : True

/-! ## THE BRIDGE — the gate definitionally supplies the producer's need, in ONE line

Mirrors `seqEnclosed_of_seqTypedInterior tokens a b (h) : SeqEnclosed tokens a := h.2.1`. -/

theorem enclosed_of_gate {s : Stack} (g : Gate s) : Enclosed s := g.enc

/-! ## `StrongPath` DOMINATES `Enclosed` (its head is `true`) — but is NOT needed for it

Mirrors `seqEnclosed_of_seqPathAllSeq`: the strong predicate also gives `Enclosed`, but the gate
already does, so the strong one is vestigial. -/

theorem enclosed_of_strongPath {s : Stack} (h : StrongPath s) : Enclosed s := by
  obtain ⟨h_ne, h_all⟩ := h
  cases s with
  | nil => exact absurd rfl h_ne
  | cons a t =>
    cases a with
    | true => rfl
    | false => simp at h_all

/-! ## THE PROBE — a `¬StrongPath` window the gate STILL serves

The window `[true, false]` (immediate frame a sequence, but the path dips through a `{` deeper down):
`StrongPath` FAILS, yet `Gate` HOLDS — so the producer serves it through `enclosed_of_gate`, with NO
complement provider.  This is the refutation: the partition's `¬StrongPath` side is covered by the
SAME producer via the gate's free conjunct. -/

/-- The witness stack: a seq frame on TOP, a map frame underneath. -/
def probeStack : Stack := [true, false]

-- `StrongPath` FAILS on the probe window (a `false` deeper in the stack)...
theorem probe_not_strongPath : ¬ StrongPath probeStack := by
  rintro ⟨_, h_all⟩; simp [probeStack] at h_all

-- ...yet the GATE HOLDS (its `enc` head is `true`)...
theorem probeGate : Gate probeStack := ⟨trivial, rfl, trivial⟩

-- ...so the producer's need `Enclosed` is supplied — for a window OUTSIDE `StrongPath`'s domain.
theorem probe_enclosed_via_gate : Enclosed probeStack := enclosed_of_gate probeGate

/-! ## Concrete witnesses -/

-- the probe window: NOT all-seq-path...
#guard probeStack.all (· == true) = false
-- ...but its immediate enclosure (the gate's `enc` head) IS a sequence:
#guard probeStack.head? = some true
-- an all-seq-path window for contrast — both StrongPath and the gate hold:
#guard ([true, true] : Stack).all (· == true) = true
#guard ([true, true] : Stack).head? = some true

/-- End-to-end: a window where `StrongPath` FAILS but the `Gate` still supplies `Enclosed` —
    the complement provider is unnecessary; one producer (consuming `Enclosed` from the gate) serves
    both sides of the would-be partition. -/
example : ¬ StrongPath probeStack ∧ Enclosed probeStack :=
  ⟨probe_not_strongPath, enclosed_of_gate probeGate⟩

end Tests.Reflections.ProbeRefutesComplementProvider
