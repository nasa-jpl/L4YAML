/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # A wider closure argument is a lost invariant (Reflection 621)

A nested frame does not store its parent; it carries a closure that folds this
frame's eventual result into it.  That closure's argument type was
`SFlowNode` — `[161] ns-flow-node`, the widest thing a flow position can hold.
Widest looks like the safe choice.  It was the reason one case could not be
written at all.

The case is `[&a [b]]`: a `[96] c-ns-properties` run is being held when a nested
collection opens, so the properties DECORATE that collection — they have to wrap
the child's eventual node, not sit beside it.  Wrapping is
`SFlowNode.propsContent`, and `propsContent` takes `[158] ns-flow-content`,
because properties may not decorate an alias: `[104] c-ns-alias-node` is an
ALTERNATIVE to the properties-bearing form of `[161]`, never its content.  So the
closure had to promise its argument was content, and a closure taking a whole
node promises strictly less.

The tell was in the callers, and it was there from the beginning: **every** call
site already built `SFlowNode.content (…)` to reach the wide type.  The alias
constructor was in the argument's range and never in its image.  Narrowing the
argument cost each producer one wrapper — moved from the caller to the callee,
not added — and bought the case.

The general form: a closure argument wider than the values that actually flow
through it is not spare generality, it is a **discarded invariant**.  Every
caller applying the same injection to reach the type is the diagnostic.

L4YAML DOCS item 10 (β.3), 2026-08-08.
-/

namespace Tests.Reflections.WiderClosureArgumentLosesInvariant

/-! ## §0  The two grammar levels

`Content` is what a collection or a scalar produces.  `Node` is `Content` plus
the one thing properties cannot decorate — the alias. -/

inductive Content where
  | scalar | collection
  deriving DecidableEq, Repr, BEq

inductive Node where
  /-- The injection every caller was already applying. -/
  | content (c : Content)
  /-- `[104]`: a whole node, never the content of a properties-bearing one. -/
  | alias
  deriving DecidableEq, Repr, BEq

/-- Properties wrap CONTENT.  There is deliberately no `Node` constructor here:
    that absence is the invariant the wide argument threw away. -/
inductive Decorated where
  | bare (c : Content)
  | props (c : Content)
  deriving DecidableEq, Repr, BEq

/-- …and a decorated thing is again a node. -/
def Decorated.toNode : Decorated → Node
  | .bare c => .content c
  | .props c => .content c

/-! ## §1  The two closure types

`WideInject` is what the frame carried; `NarrowInject` is what it carries now.
The result type is the same — only the promise about the argument differs. -/

abbrev WideInject (R : Type) := Node → R
abbrev NarrowInject (R : Type) := Content → R

/-- Narrow ⇒ wide is FREE, and it is exactly the wrapper every caller was
    writing by hand. That direction always exists. -/
def NarrowInject.widen {R : Type} (f : NarrowInject R) : WideInject R :=
  fun n => match n with
    | .content c => f c
    | .alias => f .scalar   -- an arbitrary choice: the alias was never in range

/-- Wide ⇒ narrow is free too, and this is the direction the producers now take:
    one wrapper, moved from the caller into the callee. -/
def WideInject.narrow {R : Type} (f : WideInject R) : NarrowInject R :=
  fun c => f (.content c)

/-! ## §2  The case only the narrow closure can express

The consumer that holds a property run must build the child's result by WRAPPING
what the child produces. -/

/-- With the narrow closure the wrap is definable: the argument is content, and
    content is what `props` takes. -/
def wrapWithProps {R : Type} (f : Decorated → R) : NarrowInject R :=
  fun c => f (.props c)

/-- The wide closure cannot be fed the same way. Any total `Node → Decorated`
    must send `alias` somewhere, and every `Decorated` erases to a `.content`
    node — so no such function is a section: `alias` has no `Decorated` preimage.
    (Axiom-free; `decide` on the two `Decorated` shapes.) -/
theorem alias_has_no_decorated_preimage : ∀ d : Decorated, d.toNode ≠ Node.alias := by
  intro d; cases d <;> intro h <;> cases h

/-- Stated as the wide closure's failure: a `wrap : Node → Decorated` that agrees
    with `props` on content cannot round-trip `alias` — the wide argument admits
    a value the target has no room for. -/
theorem wide_wrap_cannot_round_trip (wrap : Node → Decorated) :
    (wrap Node.alias).toNode ≠ Node.alias :=
  alias_has_no_decorated_preimage _

/-! ## §3  …and the narrow one does round-trip, on everything it admits -/

theorem narrow_wrap_round_trips (c : Content) :
    (Decorated.props c).toNode = Node.content c := by cases c <;> rfl

/-- So the narrowing is not a restriction of what the closure can DO: on the
    values that actually flow, wide and narrow agree pointwise. -/
theorem narrow_agrees_on_content {R : Type} (f : WideInject R) (c : Content) :
    f.narrow c = f (.content c) := rfl

/-! ## §4  The diagnostic

The smell is not in the closure, it is in the CALLERS: each one applies the same
injection to reach the argument type.  Model a caller as the value it really
has, and read off which constructor is ever used. -/

/-- Every existing call site closed a collection and wrapped it. -/
def callSites : List Content := [.collection, .collection, .scalar]

/-- What those callers pass through the wide closure. -/
def wideArgs : List Node := callSites.map Node.content

-- The alias constructor is in the argument's RANGE and never in its IMAGE.
#guard wideArgs.all (fun n => n != Node.alias)

-- …so narrowing changes nothing the callers do: the two agree on every argument
-- that is actually passed.
#guard (wideArgs.map (fun n => match n with | .content c => c | .alias => Content.scalar))
  == callSites

/-! ## §5  Why the wide type looked safe

Widening the argument of a closure LOOKS like weakening a hypothesis (good), but
a closure argument is contravariant: widening it STRENGTHENS the obligation on
whoever supplies the closure, and it is the supplier who has the invariant. The
two directions below are both total, which is exactly why the mistake is easy —
nothing fails to typecheck, the new consumer just cannot be written. -/

theorem widen_narrow_id {R : Type} (f : NarrowInject R) (c : Content) :
    f.widen.narrow c = f c := rfl

/-- The information actually lost, made concrete: `widen` had to invent an answer
    for `alias`, and the invented answer is observably wrong for any `f` that
    separates the two contents. -/
theorem widen_invents_an_answer :
    (NarrowInject.widen (R := Content) id) Node.alias = Content.scalar := rfl

/-! ## §6  Axiom pins -/

/-- info: 'Tests.Reflections.WiderClosureArgumentLosesInvariant.alias_has_no_decorated_preimage' does not depend on any axioms -/
#guard_msgs in
#print axioms alias_has_no_decorated_preimage

/-- info: 'Tests.Reflections.WiderClosureArgumentLosesInvariant.wide_wrap_cannot_round_trip' does not depend on any axioms -/
#guard_msgs in
#print axioms wide_wrap_cannot_round_trip

/-- info: 'Tests.Reflections.WiderClosureArgumentLosesInvariant.narrow_wrap_round_trips' does not depend on any axioms -/
#guard_msgs in
#print axioms narrow_wrap_round_trips

end Tests.Reflections.WiderClosureArgumentLosesInvariant

end Blanket
