/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 672 — the collapse keeps what the neighbors read

**The rule.**  An invariant threaded through a machine that over-accepts
needs a way out of an arm that can neither close (no derivation exists) nor
refute (the machine really accepts) — and the way out is to RENOUNCE the
rich reading, not to widen it.  Design the renounced state by reading the
OTHER conjuncts of the invariant: keep exactly the fields their steps consume
(here: depth, kinds and their size, a frame tail), give every promise-shaped
field its trivially-sound instance (an empty mask promises nothing and is
sound in every state), and give the one obligation that must eventually be
met a single absorbing closure.  The escape then CONCENTRATES: many textual
escape sites become one — the collapse's close — and the escape's domain
becomes exactly the renounce events, named at the point each lift fails.

**The instance** (item 46).  `FlowStackB.shape`: a flow stack whose grammar
reading at the carried index was given up mid-flight (a landing under-ran
`s-indent(n)`; a scalar token crossed a line).  It keeps depth (= the
scanner's `flowLevel`), kinds (= `flowStack`, with `ks.size = fl` — the one
fact the pop-to-zero arm reads), the frame tail, an empty promise mask
(`KmSound.empty` — the mask's consumers fire only on `true` bits), and
`close : ∀ sp_e sp_m, SSLComments sp_e sp_m → SLYamlStream …` — `scannerDrop`
spent at ONE place, `dropClose`.  Textual drop sites went 4 → 2 and the flow
share's domain shrank from "every indented flow" to the renounce events.

§1 the toy invariant: three conjuncts with three different collapse fates.
§2 the step that loses the reading, and the collapse threading where the
rich state is stuck.  §3 the concentration: both renounce events spend the
same close.

**The sequel** (item 126, Reflection 684 `EscapeWithNoEntrance`).  An escape
built this way is closed one birth site at a time by the repairs that refute
its events, and the last one closes silently: `FlowStackB.shape`'s producers
each ended up consuming a `shape`, so no reachable state carried one while
every transport arm went on compiling.  The lesson above is what got the
invariant through item 46; the sequel is how to notice the day it is over.
-/

namespace L4YAML.Tests.Reflections.CollapseKeepsWhatNeighborsRead

/-- The rich reading (toy grammar derivation): extendable while it has fuel,
    stuck when the machine accepts past what the grammar derives. -/
inductive Reading (n : Nat) : Type where
  | mk (fuel : Nat) : Reading n

/-- The invariant: a depth the pop arm reads, a mask whose consumers fire
    only on `true` bits, and the reading — or its renounced twin, which
    keeps the depth, empties the mask, and carries one absorbing close. -/
inductive Inv (n : Nat) : Nat → List Bool → Type where
  | rich (d : Nat) (mask : List Bool) (r : Reading n) (hd : mask.length = d) :
      Inv n d mask
  | shape (d : Nat) (hd : 1 ≤ d) (close : Unit → String) :
      Inv n d []

/-- §1 the mask's consumer: fires only on `true` bits — which is why the
    empty mask is sound everywhere, the way `KmSound.empty` is. -/
def maskConsumer : List Bool → Nat
  | [] => 0
  | true :: rest => 1 + maskConsumer rest
  | false :: rest => maskConsumer rest

example : maskConsumer [] = 0 := rfl

/-- §2 a step that must extend the reading — and cannot when the fuel is
    out.  The rich arm extends; the renounce event collapses, keeping the
    depth and spending nothing but the close; a collapsed state stays
    collapsed for free. -/
def step {n d : Nat} {mask : List Bool} (hd : 1 ≤ d) :
    Inv n d mask → (Inv n d mask) ⊕ (Inv n d [])
  | .rich _ _ (.mk (f + 1)) hdm => .inl (.rich _ _ (.mk f) hdm)
  | .rich _ _ (.mk 0) _ => .inr (.shape _ hd fun _ => "dropped")
  | .shape _ _ close => .inr (.shape _ hd close)

/-- §3 the concentration, executable: the renounce event and the collapsed
    passthrough land in the SAME constructor with the same close type — the
    drop has one home, and its domain is exactly the renounce events. -/
example (r : Reading 7) (h : r = .mk 0) :
    step (d := 1) (by omega) (.rich 1 [true] r rfl) =
      .inr (.shape 1 (by omega) fun _ => "dropped") := by subst h; rfl

example (close : Unit → String) :
    step (n := 7) (d := 3) (by omega) (.shape 3 (by omega) close) =
      .inr (.shape 3 (by omega) close) := rfl

/-- ... and a collapse at any depth threads the same invariant the rich
    state does — what the neighbors read is all still there. -/
example (close : Unit → String) : Inv 7 3 [] := .shape 3 (by omega) close

end L4YAML.Tests.Reflections.CollapseKeepsWhatNeighborsRead

end Blanket
