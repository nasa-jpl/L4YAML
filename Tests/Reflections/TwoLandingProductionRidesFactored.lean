/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 677 — a two-landing production rides the pending as a FACTORED closure

**The rule.**  A production whose halves land on different steps — a key
line and a value line — cannot be served by close-then-reopen: the second
half has no production of its own to reopen INTO, so the entry must stay
open across the break.  The closure the park already carries is a
composition, `close = route ∘ completion`; PRE-composing it at the park is
what forecloses the later half, because the composition, once taken, is one
stream, while the factors are every stream the production still admits.
Keep the factors as fields (the route on the opener's pending, the derived
pack on the content park), and the later landing re-enters the production
at the exact point the first landing left it.  The cost is one optional
field per park kind on the chain — `∨ True` everywhere else — and the
producers that pay it already built both factors inline.

**The instance** (item 51).  A standalone `: - w` line is not in the YAML
language (`[189]`'s empty-key value slot is `s-l+block-node`), so
`? a⏎: - w` composes only as ONE `[188]` explicit entry: `question_open_map`
factors its `explicitEmpty` closure into the entry route (`h_expl`), the
key-content park derives the value pack from it (`h_vpack` — the landing's
comments complete the KEY's `s-l+block-indented` half), the landed `:` at
the key's own column parks the value slot (`h_vslot`), and the same-line
`-`/`?`/`:` fills `[185]`'s compact alternatives.  The runtime's share is
the `[197]` column discrimination — the `:` is the value line only AT
`explicitKeyCol` — which both refused two over-acceptances and un-refused a
valid input (`? earth: blue⏎  : x⏎: - w`).

§1 the two park shapes; §2 the factored park serves the two-landing entry;
§3 the pre-composed park cannot — its one field is one stream, shown by
instantiating the acceptor. -/

namespace L4YAML.Tests.Reflections.TwoLandingProductionRidesFactored

/-- §1 a token alphabet: the opener, the value indicator, and scalars. -/
inductive Tok : Type
  | q | colon | scalar (n : Nat)
deriving DecidableEq

/-- The production's KEY half: `? <scalar>`. -/
inductive KeyHalf : List Tok → Prop
  | mk (n : Nat) : KeyHalf [.q, .scalar n]

/-- The two-landing production: a key half alone, or extended by its value
    line — the second alternative has no standalone reading of its tail. -/
inductive Entry : List Tok → Prop
  | keyOnly {k : List Tok} : KeyHalf k → Entry k
  | full {k : List Tok} (n : Nat) :
      KeyHalf k → Entry (k ++ [.colon, .scalar n])

/-- The FACTORED park: the route and the key half, composition not taken. -/
structure FactoredPark (Accept : List Tok → Prop) (k : List Tok) : Prop where
  route : ∀ t, Entry t → Accept t
  keyHalf : KeyHalf k

/-- The PRE-COMPOSED park: the same two facts, already spent on the
    key-only reading.  One stream. -/
structure ComposedPark (Accept : List Tok → Prop) (k : List Tok) : Prop where
  closed : Accept k

/-- Every factored park could have pre-composed — the factoring is free. -/
theorem composed_of_factored {Accept : List Tok → Prop} {k : List Tok}
    (p : FactoredPark Accept k) : ComposedPark Accept k :=
  ⟨p.route k (Entry.keyOnly p.keyHalf)⟩

/-- §2 the later landing re-enters: the factored park serves the FULL
    entry when the value line arrives. -/
theorem factored_serves_full {Accept : List Tok → Prop} {k : List Tok}
    (p : FactoredPark Accept k) (n : Nat) :
    Accept (k ++ [.colon, .scalar n]) :=
  p.route _ (Entry.full n p.keyHalf)

/-- §3 the pre-composed park cannot: no consumer turns the key-only stream
    into the full one for an ARBITRARY acceptor.  Instantiating the
    acceptor at exactly the key-only word refutes the claim. -/
theorem composed_cannot_extend :
    ¬ (∀ (Accept : List Tok → Prop) (k : List Tok),
        ComposedPark Accept k → Accept (k ++ [.colon, .scalar 1])) := by
  intro h
  have := h (fun t => t = [.q, .scalar 0]) [.q, .scalar 0] ⟨rfl⟩
  simp at this

/-- …while the factored park extends at EVERY acceptor — the factors are
    every stream the production still admits. -/
theorem factored_extends_everywhere :
    ∀ (Accept : List Tok → Prop) (k : List Tok),
      FactoredPark Accept k → Accept (k ++ [.colon, .scalar 1]) :=
  fun _ _ p => factored_serves_full p 1

end L4YAML.Tests.Reflections.TwoLandingProductionRidesFactored

end Blanket
