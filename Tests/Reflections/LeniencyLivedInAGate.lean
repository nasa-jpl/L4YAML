/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 676 — an over-acceptance behind a gate is closed by deleting the gate

**The rule.**  When a family of invalid inputs is accepted although the
refusing CHECK exists and runs on the family's neighbours, look for the gate:
a conjunct that exempts exactly the accepted family, priced at some point as
"the spec requires the leniency" and never checked against the productions.
The closure then costs a DELETION per family — no new machinery, no new
invariant — and the discrimination against the sibling shape matters: item 48
needed new checks and new park fields because nothing recorded its facts;
item 50's three families each sat one conjunct away from a check their
neighbours already met.  Before building, grep the guard for exemptions and
read each against the grammar rule it claims to serve.

**The instance** (item 50).  Three flow-floor leniencies, three gates:
`]`/`}` were exempt from the under-indent guard (`[137]`/`[140]` sit inside
`s-l+flow-in-block(n)`'s `ns-flow-node(n+1)`, so the closers clear the same
floor — the exemption served nothing); the fold's §6.1 tab check was
`!inFlow`-gated (`[69] s-flow-line-prefix(n)` begins with `[63] s-indent(n)`,
spaces in either context); and the flow plain continuation had no floor read
at all — the one genuine addition, and it is the same `≤ currentIndent`
comparison its quoted neighbour had made since item 7.  All four §2 pins of
`ScannerIndexedFlowCompose` flip; matrix and eventscore are unmoved — no
valid input ever lived in a gate's shadow.

§1 the toy: a floor check with an exemption for the "closer".  §2 the
over-acceptance, witnessed through the gate; §3 the deletion refuses it and
every properly indented input still passes — the good set never met the
gate. -/

namespace L4YAML.Tests.Reflections.LeniencyLivedInAGate

/-- §1 a token at a column, closing or not. -/
structure Tok where
  col : Nat
  closer : Bool

/-- The gated check: closers are exempt from the floor. -/
def gatedOk (floor : Nat) (t : Tok) : Bool :=
  t.closer || floor < t.col

/-- The ungated check: everything clears the floor. -/
def strictOk (floor : Nat) (t : Tok) : Bool :=
  floor < t.col

/-- §2 the over-acceptance: an under-indented closer passes the gate… -/
theorem gate_accepts_the_invalid : gatedOk 2 ⟨0, true⟩ = true := rfl

/-- …and the strict check refuses it. -/
theorem strict_refuses_it : strictOk 2 ⟨0, true⟩ = false := rfl

/-- §3 nothing valid lived in the gate's shadow: on inputs that clear the
    floor the two checks agree, so deleting the gate moves only the
    invalid family. -/
theorem deletion_moves_only_the_shadow (floor : Nat) (t : Tok)
    (h : floor < t.col) : gatedOk floor t = strictOk floor t := by
  simp [gatedOk, strictOk, h]

/-- The gate's whole delta IS the shadow: the checks differ exactly on the
    exempted, under-floor inputs. -/
theorem gate_delta_is_the_shadow (floor : Nat) (t : Tok) :
    gatedOk floor t ≠ strictOk floor t ↔ (t.closer = true ∧ ¬floor < t.col) := by
  constructor
  · intro hne
    by_cases hc : t.closer = true
    · refine ⟨hc, fun hlt => hne ?_⟩
      simp [gatedOk, strictOk, hc, hlt]
    · exact absurd (by simp [gatedOk, strictOk, Bool.eq_false_iff.mpr hc]) hne
  · intro ⟨hc, hlt⟩
    simp [gatedOk, strictOk, hc, hlt]

end L4YAML.Tests.Reflections.LeniencyLivedInAGate

end Blanket
