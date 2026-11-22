/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 675 — an escape that cites its inhabitant's rules is closed by wiring

**The rule.**  A deferral arm annotated with the RULE NUMBERS of its one
grammatical inhabitant is a closure whose cost is one application: if the
cited constructors elaborate against each other — the run as the key
alternative, the key under the entry, the entry through a route somebody
already carries — then no new surface constructor, no new invariant field
and no runtime edit is owed, and the item is a producer that composes what
exists.  Check the overlap the way Reflection 667 reads an empty product:
by TYPES, before writing the call.  Conversely, an escape whose comment can
only describe its inhabitant in prose is signalling a missing constructor —
the two annotations price differently and should not be confused.

**The instance** (item 49).  `pendingProps`' `:` arm had carried its ask in
its own docstring since item 42: `&a : b` is "`[154]`'s anchored empty key"
— `[161] ns-flow-node`'s props-only alternative under `[193]`'s implicit
key.  All three constructors existed (`SFlowNode.propsEmpty`,
`SImplicitKey.jsonKey`, `SBlockMapEntry.implicitKeyNode`), and the entry
route had been carried by `PropsKeyPack` since item 41 — so the closure is
`colon_open_map_props`, one producer applying them in order, zero new
grammar, zero runtime change, and the escape narrows to the pack-less parks.

§1 the toy: a run, a key with a run-reading arm, an entry, and a route that
consumes the entry — four EXISTING pieces.  §2 the wiring is one
definition, and the closed arm is a theorem.  §3 the discrimination:
without the run arm the same obligation is UNPROVABLE from the same pieces
(a run heads where no scalar does), so a prose-only escape names a
genuinely missing constructor, not an unapplied one.
-/

namespace L4YAML.Tests.Reflections.CitedRulesMeanTheClosureIsWiring

/-- §1 a fragment of surface grammar: a properties run over a span.  A run
    heads at an ODD position — a property indicator is not a content head. -/
inductive Run : Nat → Nat → Prop where
  | mk (a b : Nat) : a % 2 = 1 → a < b → Run a b

/-- The key alternatives: a content-headed scalar (EVEN head), or a run
    read whole — the two `[193]` arms of the toy. -/
inductive Key : Nat → Nat → Prop where
  | scalar (a b : Nat) : a % 2 = 0 → a < b → Key a b
  | ofRun (a b : Nat) : Run a b → Key a b

/-- The entry: a key, then a value span. -/
inductive Entry : Nat → Nat → Prop where
  | mk (a b c : Nat) : Key a b → b < c → Entry a c

/-- The route somebody already carries: entries close to a stream `S`. -/
def Route (S : Nat → Prop) (a : Nat) : Prop := ∀ c, Entry a c → S c

/-- §2 the wiring: the run as key as entry, one application deep — the
    producer item 49 writes, with nothing new on either side. -/
theorem run_entry_composes {a b c : Nat} (hr : Run a b) (hv : b < c) :
    Entry a c :=
  Entry.mk a b c (Key.ofRun a b hr) hv

/-- …so the arm that held the escape closes through the existing route. -/
theorem arm_closes {S : Nat → Prop} {a b c : Nat} (route : Route S a)
    (hr : Run a b) (hv : b < c) : S c :=
  route c (run_entry_composes hr hv)

/-- §3 the discrimination: in a grammar WITHOUT the run-as-key alternative
    the same pieces cannot produce the key — a run heads where no scalar
    does.  An escape citing THIS grammar's rules would be dishonest: the
    constructor is missing, and the closure's price is a grammar edit, not
    a producer. -/
inductive KeyNoRun : Nat → Nat → Prop where
  | scalar (a b : Nat) : a % 2 = 0 → a < b → KeyNoRun a b

theorem no_wiring_without_the_alternative :
    ¬ (∀ a b : Nat, Run a b → KeyNoRun a b) := by
  intro h
  rcases h 1 2 (Run.mk 1 2 rfl (by omega)) with ⟨heven, _⟩
  omega

end L4YAML.Tests.Reflections.CitedRulesMeanTheClosureIsWiring

end Blanket
