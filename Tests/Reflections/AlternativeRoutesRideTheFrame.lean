/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 680 — alternative routes ride the frame

**The rule.**  When a construct's ROLE is decided after it is built, the two
ends of its construction know different halves and neither can finish alone.
The site that OPENS it knows every frame the enclosing construct offers — the
node slot, the implicit-key entry, the explicit-key entry — but not which one
the thing will fill; the site that CLOSES it knows the characters but has lost
the enclosing frame, because the route it was handed ends in the FINISHED
object and a closure whose codomain has no occurrence of its argument cannot be
run backwards.  So the alternative routes must be carried on the frame from the
open, as optional fields, and the close spends whichever the next token names.
Carrying a route costs a field; recovering one is not merely hard — what the
frame has does not determine it (§4).

What the frame carries is a route and a HEAD BUILDER, not a head: the head is a
function of the content, which only the close has.  The pack is their join, and
each half alone is worth nothing (§5).

**The instance** (item 56).  A depth-0 `[`/`{` is opened over whatever block
construct is awaiting a node, and `[1]: b` — `[193] c-s-implicit-json-key` — is
decided by a `:` that arrives after the `]`.  The frame's `resume` ends in
`SLYamlStream`, so the closed collection cannot be recovered at the `]` to build
the key half; `FlowBaseRoutes` therefore carries three fields (`value`, `key`,
`vslot`), the five block-side open arms pay the routes their own pendings offer
(root, compact/nested entry, explicit `?`, props run, fresh document), and the
two base closes spend them through `flowKeyPack_of_close` /
`flowVPack_of_close`, with `FlowKeyLift.flowNode_toBlockKey` supplying the head.
Bundling the three in ONE field is what keeps the eighteen frame-extension sites
untouched: they forward the bundle by name.

The model below is data, not `Prop`: an equation between proofs is free, so a
`Prop`-valued `spend` would let §3 hold of a frame that carries nothing.

§1 the roles; §2 the frame; §3 the paid frame answers both, the value-only one
punts (by `rfl`, on data); §4 no uniform construction yields the missing route;
§5 the pack is a join. -/

namespace L4YAML.Tests.Reflections.AlternativeRoutesRideTheFrame

/-- §1 The role the built object turns out to play, named by the token that
    arrives AFTER it. -/
inductive Role where
  | value
  | key
deriving DecidableEq

/-- The object the frame hosts, and the entry it keys when that token is a
    `:`.  The entry is built FROM the object — which is why the close is the
    only site that can build it. -/
inductive Node where | mk
inductive Entry where | key (n : Node)

/-- §2 What a frame carries.  `value` is the reading the enclosing construct
    always has; `key` is the one it may not have (a document node hosts no
    mapping entry), so it is optional and says so. -/
structure Routes (S : Type) where
  value : Node → S
  key : Option (Entry → S)

/-- The value-only frame: what an enclosing construct with no entry to offer
    hands the open. -/
def Routes.ofValue {S : Type} (v : Node → S) : Routes S := ⟨v, none⟩

/-- §3 The close spends the route the token names — and can only punt when the
    open did not carry it. -/
def spend {S : Type} (r : Routes S) : Role → Node → Option S
  | .value, n => some (r.value n)
  | .key, n =>
    match r.key with
    | some route => some (route (Entry.key n))
    | none => none

/-- A PAID frame answers for either role. -/
theorem paid_answers_both {S : Type} (v : Node → S) (route : Entry → S)
    (role : Role) (n : Node) :
    spend ⟨v, some route⟩ role n ≠ none := by
  cases role <;> simp [spend]

/-- A value-only frame punts the key role, and the punt is not a proof gap: it
    is the frame's own content, decided by `rfl`. -/
theorem valueOnly_punts_key {S : Type} (v : Node → S) (n : Node) :
    spend (Routes.ofValue v) .key n = none := rfl

/-- …while still answering the role it was opened for: what is missing is the
    ROUTE, not the reading. -/
theorem valueOnly_answers_value {S : Type} (v : Node → S) (n : Node) :
    spend (Routes.ofValue v) .value n = some (v n) := rfl

/-- §4 The close cannot make up the difference: no uniform construction turns
    a value route into an entry route, because what the frame has does not
    determine it — the first is total exactly where the second is empty. -/
theorem no_uniform_key_route (f : ∀ (S N E : Type), (N → S) → (E → S)) : False :=
  (f Empty Empty Unit (fun e => e.elim) ()).elim

/-- §5 What the frame owes is a route and a head BUILDER; the pack is their
    join, taken at the close where the object exists. -/
def pack {S : Type} (route : Entry → S) (head : Node → Entry) (n : Node) : S :=
  route (head n)

/-- The route alone is worth nothing without the object the close supplies… -/
theorem route_alone_insufficient (f : ∀ (S E : Type), (E → S) → S) : False :=
  (f Empty Empty (fun e => e.elim)).elim

/-- …and the head alone is worth nothing without the route the open carried. -/
theorem head_alone_insufficient (f : ∀ (S N E : Type), (N → E) → N → S) : False :=
  (f Empty Unit Unit (fun _ => ()) ()).elim

end L4YAML.Tests.Reflections.AlternativeRoutesRideTheFrame

end Blanket
