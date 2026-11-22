module


@[expose] public section Blanket

/-!
# Reflection 611 — `cases` reorders the constructor telescope

`rename_i x₁ … xₙ` renames the **last `n` inaccessible hypotheses in context
order**, and `cases` does *not* introduce a constructor's fields in declaration
order: it floats binders that nothing depends on ahead of the ones that do.

So a `rename_i` list written by reading the constructor declaration binds the
wrong hypotheses. The failure does not look like a naming problem — the names
all exist — it surfaces downstream as *"application type mismatch"* against a
sibling field's type.

The toy below is the smallest faithful model of L4YAML's `SeqFrame.betweenHeld`:

```lean
| betweenHeld (sp sp_e sp_c sp') (h : Entries sp sp_e)
    (hcl : Closeable h) (hcomma : GLit ',' sp_e sp_c) (hsep : …) : SeqFrame .sep sp sp'
```

whose declared field order is `h, hcl, hcomma, hsep` but whose **context** order
after `cases` is `hcomma, h, hcl, hsep` — `hcomma` moves ahead of `h` because it
depends only on positions, while `hcl` depends on `h` and so must stay behind it.
Inlining `SeqFrame`/`MapFrame` (Reflection 610) broke 18 `rename_i` lines this
way at once.

`lake build Tests.Reflections.CasesReordersTelescope`
-/

namespace CasesReordersTelescope

/-- Stand-in for a surface position. -/
abbrev Pos := Nat

/-- The payload relation: "entries span `a` to `b`". -/
inductive Entries : Pos → Pos → Prop where
  | nil (a : Pos) : Entries a a
  | step (a b : Pos) (h : Entries a b) : Entries a (b + 1)

/-- A **dependent** side condition: it mentions the *proof* `h`, not merely its
    indices. This is what pins `hcl` behind `h` in the reordered context. -/
inductive Closeable : {a b : Pos} → Entries a b → Prop where
  | ofNil (a : Pos) : Closeable (.nil a)
  | ofStep (a b : Pos) (h : Entries a b) : Closeable (.step a b h)

/-- A separator witness — depends only on positions, on nothing else in the
    telescope. This is the binder that gets floated forward. -/
inductive Comma : Pos → Pos → Prop where
  | mk (a : Pos) : Comma a (a + 1)

/-- An optional trailing separator, likewise position-only. -/
inductive Sep : Pos → Pos → Prop where
  | none (a : Pos) : Sep a a
  | some (a : Pos) : Sep a (a + 1)

/-- The frame's tail class (the index that Reflection 610 introduced). -/
inductive Tail where
  | sep
  | value
  deriving DecidableEq, Repr

/-- The frame. `held` is the arm of interest: its declared field order is
    `b, c, h, hcl, hcomma, hsep`. -/
inductive Frame : Tail → Pos → Pos → Prop where
  | empty (a : Pos) : Frame .sep a a
  | held (a b c d : Pos) (h : Entries a b) (hcl : Closeable h)
      (hcomma : Comma b c) (hsep : Sep c d) : Frame .sep a d

/-! ## The probe — read the real order, do not derive it

This is the whole method: put `trace_state` in the arm, build once, and read
the context. The `#guard_msgs` below **pins** that order, so if a future Lean
release or a field reshuffle changes it, this file fails rather than some
consumer's `rename_i`.

Note what the trace shows: `hcomma✝ : Comma b✝ c✝` appears **before**
`h✝ : Entries a b✝`, inverting the declaration. The names Lean displays come
from the constructor, but they are *inaccessible* — you cannot refer to them,
which is why `rename_i` is needed at all, and why its positional semantics is
the only thing that decides what each new name means. -/

/--
trace: case held
a d b✝ c✝ : Pos
hcomma✝ : Comma b✝ c✝
h✝ : Entries a b✝
hcl✝ : Closeable h✝
hsep✝ : Sep c✝ d
⊢ True
-/
#guard_msgs in
theorem order_probe {a d : Pos} (h : Frame .sep a d) : True := by
  cases h
  · trivial
  · trace_state
    trivial

/-! ## Three ways to write the same arm -/

/-- **STABLE** — `cases h with | held …` binds by *constructor field order*, so
    it is unaffected by the reordering and survives field reshuffles. Prefer
    this in arms you expect to edit. -/
theorem via_cases_with {a d : Pos} (h : Frame .sep a d) :
    (∃ b, Entries a b) ∨ a = d := by
  cases h with
  | empty => exact .inr rfl
  | held a b c d hentries hcl hcomma hsep => exact .inl ⟨b, hentries⟩

/-- **CORRECT `rename_i`** — the name list is written in *context* order, the
    order the probe above reported. `hentries` really is the `Entries` proof. -/
theorem via_rename_i_context_order {a d : Pos} (h : Frame .sep a d) :
    (∃ b, Entries a b) ∨ a = d := by
  cases h
  · exact .inr rfl
  · rename_i b c hcomma hentries hcl hsep
    exact .inl ⟨b, hentries⟩

/-- **THE TRAP** — the same `rename_i` with the list read off the *declaration*
    (`hentries, hcl, hcomma, hsep`) still elaborates, but every name is bound to
    a different hypothesis: `hentries` is the comma, `hcl` is the entries proof,
    `hcomma` is the closeable. The proof term that type-checks is the one that
    reads as nonsense — which is exactly why the error surfaces as a type
    mismatch at the *use* site rather than as a naming complaint here. -/
theorem rename_i_declaration_order_binds_swapped {a d : Pos} (h : Frame .sep a d) :
    (∃ b, Entries a b) ∨ a = d := by
  cases h
  · exact .inr rfl
  · rename_i b c hentries hcl hcomma hsep
    -- `hcl`, not `hentries`, carries `Entries a b`:
    exact .inl ⟨b, hcl⟩

/-! ## Why the float happens, made checkable

`hcomma : Comma b c` mentions only positions; `hcl : Closeable h` mentions the
proof `h`. `cases` may hoist the former past the latter's dependency block, and
does. Below, a `Bool` model of the two orders makes the discrepancy a decidable
fact rather than a comment. -/

/-- The order as declared in the constructor. -/
def declaredOrder : List String := ["hentries", "hcl", "hcomma", "hsep"]

/-- The order `cases` actually produces, as pinned by `order_probe`. -/
def contextOrder : List String := ["hcomma", "hentries", "hcl", "hsep"]

#guard declaredOrder != contextOrder
#guard declaredOrder.length == contextOrder.length
#guard declaredOrder.all contextOrder.contains

/-- The two orders are permutations of one another — so *counting* fields never
    detects the problem, and a `rename_i` arity check never fires. Only the
    positions differ. -/
theorem same_names_different_order :
    declaredOrder ≠ contextOrder ∧
    declaredOrder.length = contextOrder.length ∧
    declaredOrder.all contextOrder.contains = true := by
  refine ⟨by decide, by decide, by decide⟩

/-- `hcl` stays *directly behind* `hentries` in both orders: a dependency block
    moves as a unit. That is the rule that predicts the permutation — the
    position-only binder floats, the dependent pair does not separate. -/
theorem dependency_block_stays_adjacent :
    (declaredOrder.idxOf "hcl" = declaredOrder.idxOf "hentries" + 1) ∧
    (contextOrder.idxOf "hcl" = contextOrder.idxOf "hentries" + 1) := by
  refine ⟨by decide, by decide⟩

/-! ## Index-determined fields never appear at all

`a` and `d` are the frame's own indices and `Tail` is fixed by the goal, so
`cases` substitutes them away. Counting the constructor's declared binders
(`a b c d h hcl hcomma hsep` — eight) to predict the `rename_i` arity (six)
overshoots for this reason too. -/

#guard (["a", "b", "c", "d", "hentries", "hcl", "hcomma", "hsep"] : List String).length == 8
#guard (["b", "c", "hcomma", "hentries", "hcl", "hsep"] : List String).length == 6

/-! ## Axiom audit -/

/-- info: 'CasesReordersTelescope.via_cases_with' does not depend on any axioms -/
#guard_msgs in
#print axioms via_cases_with

/-- info: 'CasesReordersTelescope.via_rename_i_context_order' does not depend on any axioms -/
#guard_msgs in
#print axioms via_rename_i_context_order

/--
info: 'CasesReordersTelescope.rename_i_declaration_order_binds_swapped' does not depend on any axioms
-/
#guard_msgs in
#print axioms rename_i_declaration_order_binds_swapped

end CasesReordersTelescope

end Blanket
