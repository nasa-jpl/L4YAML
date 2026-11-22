/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 670 — price a re-index by its signatures, not its occurrences

**The rule.**  When an invariant must trade a hard-coded index for a
parameter, the census that greps the literal misprices the edit in BOTH
directions, because Lean's inductive parameters are implicit in constructor
applications and invisible to `cases` patterns.  Every construction and every
elimination of the type compiles untouched; what pays is each SIGNATURE that
ascribes the type — and, in the other direction, any literal that hides in a
body's `show`/`have` ascription pays even though the occurrence census under a
different spelling missed it.  Count the declarations whose statements mention
the type, not the zeros.

**The instance.**  `FlowOpenStack`'s reading index (item 44): item 25's census
priced ≈86 literal `0`s across 31 declarations; the edit cost two inductive
headers, twenty-two signatures, and a handful of ascriptions where a literal
DEPTH shifted into the new parameter's slot — every one of the accumulation's
stack constructions and `cases` compiled verbatim, because the parameter never
appears in them.  Roughly three-to-one over-priced, and the un-greppable
residue (a literal inside a tactic block's ascription) is exactly what the
same census cannot see at all.

§1 the toy, pinned; §2 the parameter added — the operation's body is the SAME
TERM, and the pinned operation is the generic one instantiated (the type-level
face of [[CloserIsAParameterNotAPremise]]'s "the special case is the general
case with the parameter thrown away"); §3 the elimination side: one `match`,
written once, serves every index.
-/

namespace L4YAML.Tests.Reflections.ReindexPriceIsTheSignatures

/-- A "reading" whose meaning depends on the index (toy `s-indent(n)`). -/
def Reading (n : Nat) : Prop := n ≤ 3

/-- §1-§2 the toy stack: depth-indexed, every grammar slot reading at `n`.
    (The pinned original had `Reading 0` here; adding `(n : Nat)` is the WHOLE
    edit to the type — no constructor mentions it.) -/
inductive Tower (n : Nat) : Nat → Type where
  | base (r : Reading n) : Tower n 1
  | nest {d : Nat} (below : Tower n d) (r : Reading n) : Tower n (d + 1)

/-! ## §2  The operation's body survives the re-index verbatim -/

/-- The generic operation.  Its body names no index. -/
def Tower.grow {n d : Nat} (h : Tower n d) (r : Reading n) : Tower n (d + 1) :=
  .nest h r

/-- The pinned operation is the generic one INSTANTIATED — the signature is
    the only difference, which is why the signature is the price. -/
def Tower.grow0 {d : Nat} (h : Tower 0 d) (r : Reading 0) : Tower 0 (d + 1) :=
  Tower.grow h r

/-- ... and the instantiation is definitional: nothing moved. -/
example {d : Nat} (h : Tower 0 d) (r : Reading 0) :
    Tower.grow0 h r = Tower.grow h r := rfl

/-! ## §3  Eliminations never see the parameter

One `match`, written once with no index in any pattern, serves the pinned
index and every other — the `cases` side of the same fact.  A census grepping
`Reading 0` finds the OCCURRENCES inside old signatures; it cannot find this
function, and this function is what makes most of the edit free. -/

/-- The reading, recovered by elimination: the patterns bind no `n`. -/
theorem Tower.reading {n d : Nat} : Tower n d → Reading n
  | .base r => r
  | .nest _ r => r

example (h : Tower 0 5) : Reading 0 := h.reading
example (h : Tower 2 5) : Reading 2 := h.reading

/-- The machinery at a NONZERO index, from abstract evidence — the elaboration
    that the pinned type refused (item 44's guard file does this for the real
    stack). -/
example (r : Reading 2) : Tower 2 2 := (Tower.base r).grow r

end L4YAML.Tests.Reflections.ReindexPriceIsTheSignatures

end Blanket
