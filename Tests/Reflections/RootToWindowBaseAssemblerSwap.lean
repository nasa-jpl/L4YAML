/-!
# Reflection 446 — generalizing a ROOT-span producer to a WINDOW-parametric one is exactly ONE swap:
# replace the BASE-CASE assembler (the flat, root-only supplier) with its window-parametric sibling,
# LIFTING the base unit as a hypothesis.  The DESCENT/recursive route is already window-parametric, so
# it is untouched and the generalization carries ZERO new proof — the root version is recovered as the
# thin literal-span INSTANCE (`rfl`).  A measure corollary: even when the descent's enclosing window
# coincides with the whole window (the self-instantiation), the IH callee is strictly narrower, so a
# joint width induction covers it with no circular self-call.

Self-contained (core Lean, no `L4YAML` import) toy of the R446 finding — STEP D continued: the
SMALLEST-FIRST brick before the R447 carrier↔recursion co-construction.

Context.  `seqRoot_carrier_of_widthEnc` produced the seq carrier `SeqInteriorSeparators tokens 2 (size-2)`
at the ROOT span by driving its descent through `seqRoot_seqInteriorSeparators`, which bakes in BOTH the
literal span `lo = 2`, `hi = size - 2` AND the FLAT root `SafeBodyUnit` (`seqRoot_safeBodyUnit`, scanned
straight off emission, no recursion).  R446 needed the SAME carrier at an ARBITRARY seq window `[lo, hi)`
(the co-construction's local-carrier half).  The whole descent route the producer threads
(`seqEnclosingOpener_of_gate` → `h_widthEnc` → `seqEnclosed_succ_of_located_opener` →
`seqDescent_provider_of_located`) is ALREADY window-parametric — every lemma takes `lo`/`hi`/`a`/`b`/`p`
as arguments, none reads the literal `2`/`size - 2`.  So the ONLY root-specific ingredient is the flat
base-case assembler.

The generalization is therefore exactly ONE swap: replace the root assembler
`seqRoot_seqInteriorSeparators` (which supplies the flat base + pins the span) with the window-parametric
`seqInteriorSeparators_of_safebody_and_descent`, LIFTING the window's `SafeBodyUnit` as a hypothesis
`h_safe`, and re-base `h_widthEnc`'s bounds to `[lo, hi)`.  The proof body is otherwise term-for-term
unchanged, and `seqRoot_carrier_of_widthEnc` becomes the thin `lo := 2`, `hi := size - 2` instance fed
`seqRoot_safeBodyUnit` — a `rfl`-level delegation ([[ref-additive-parallel-type-over-shared-edit]]).

The reusable rule.  When you generalize a producer from a fixed (root) span to an arbitrary window, the
part to generalize is the BASE-CASE assembler alone: the recursive/descent route is usually already
parametric (it descends into windows it does not own).  So measure the generalization by what the base
case bakes in — span literals and the flat base supplier — and lift exactly those to arguments; the
descent stays put and the root version is recovered as a literal instance.

This toy models the two facts the brick rests on:

* `root_is_instance` — with the descent route exposed as a parameter, the root producer is DEFINITIONALLY
  the window producer at the literal span fed the flat base: the swap carries zero new proof (`rfl`).
* `joint_ih_covers_seqchild_callee` — the R447 measure: the descent's enclosing window `[p, hiE)` is
  CONTAINED in the whole window `[lo, hi)` (`lo ≤ p`, `hiE ≤ hi`), with EQUALITY allowed (the `[[1,2],9]`
  self-instantiation `p = lo`, `hiE = hi`).  Either way the `seqChild_safeBodyUnit` IH gate
  `hi' - lo' < hiE - p` entails the joint width-IH gate `hi' - lo' < hi - lo`, so a width induction over
  `[lo, hi)` covers every callee with no circular self-call.

All sorry-free, axiom-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.RootToWindowBaseAssemblerSwap

/-! ## The three abstract roles, modelling the seq carrier producer. -/

/-- The base-case unit, available FLAT at the root and (in the co-construction) from the recursion at a
    window.  Models `SafeBodyUnit ContentStartTok ((take hi).drop lo)`. -/
opaque BaseUnit : Nat → Nat → Prop
/-- The width supplier — enclosing facts + strictly-narrower IH.  Models `h_widthEnc`. -/
opaque WidthSupplier : Nat → Nat → Prop
/-- The deliverable carrier.  Models `SeqInteriorSeparators tokens lo hi`. -/
opaque Carrier : Nat → Nat → Prop

/-! ## The WINDOW-PARAMETRIC descent route — already takes the span as arguments, reads no literal.
    Models `seqInteriorSeparators_of_safebody_and_descent` composed with the located-descent chain.
    It is a PARAMETER here (the already-landed, window-parametric assembler). -/

/-- The window-parametric producer: just expose the descent route's parameters.  Models
    `seqLocalCarrier_of_widthEnc`. -/
def windowProduce
    (descRoute : ∀ lo hi, BaseUnit lo hi → WidthSupplier lo hi → Carrier lo hi)
    (lo hi : Nat) (base : BaseUnit lo hi) (w : WidthSupplier lo hi) : Carrier lo hi :=
  descRoute lo hi base w

/-- The ROOT producer: bake in the literal span `[2, size]` and the FLAT base `flatBase`.  Models the
    pre-R446 `seqRoot_carrier_of_widthEnc` (via `seqRoot_seqInteriorSeparators` + `seqRoot_safeBodyUnit`). -/
def rootProduce
    (descRoute : ∀ lo hi, BaseUnit lo hi → WidthSupplier lo hi → Carrier lo hi)
    (size : Nat) (flatBase : BaseUnit 2 size) (w : WidthSupplier 2 size) : Carrier 2 size :=
  descRoute 2 size flatBase w

/-- **THE GENERALIZATION IS A FREE `rfl`.**  Because the descent route was already window-parametric,
    the root producer is DEFINITIONALLY the window producer at the literal span fed the flat base — the
    only root-specific ingredients (the span `2`/`size` and `flatBase`) move from baked-in to arguments,
    and the swap proves nothing.  Post-R446, `seqRoot_carrier_of_widthEnc` IS this instance. -/
theorem root_is_instance
    (descRoute : ∀ lo hi, BaseUnit lo hi → WidthSupplier lo hi → Carrier lo hi)
    (size : Nat) (flatBase : BaseUnit 2 size) (w : WidthSupplier 2 size) :
    rootProduce descRoute size flatBase w = windowProduce descRoute 2 size flatBase w := rfl

/-! ## The R447 MEASURE corollary — the self-instantiation is sound. -/

/-- The descent's enclosing window `[p, hiE)` is CONTAINED in the whole window `[lo, hi)` — with
    EQUALITY allowed (the `[[1, 2], 9]` self-instantiation `p = lo`, `hiE = hi`).  Either way, the
    `seqChild_safeBodyUnit` IH gate `hi' - lo' < hiE - p` entails the joint width-IH gate
    `hi' - lo' < hi - lo`, so a width induction over `[lo, hi)` covers every callee the carrier-build
    consumes — no circular self-call. -/
theorem joint_ih_covers_seqchild_callee
    {lo hi p hiE childLo childHi : Nat}
    (h_p : lo ≤ p) (h_hiE : hiE ≤ hi)            -- enclosing ⊆ whole (≤; equality at self-instantiation)
    (h_gate : childHi - childLo < hiE - p) :     -- the seqChild_safeBodyUnit IH gate
    childHi - childLo < hi - lo := by omega       -- ⇒ joint width-IH gate; width induction applies

/-- The finding in one proposition: the generalization is a definitional instance (free) AND the measure
    is sound even at the self-instantiation `p = lo ∧ hiE = hi`. -/
theorem r446_finding
    (descRoute : ∀ lo hi, BaseUnit lo hi → WidthSupplier lo hi → Carrier lo hi)
    (size : Nat) (flatBase : BaseUnit 2 size) (w : WidthSupplier 2 size)
    {lo hi childLo childHi : Nat}
    (h_gate : childHi - childLo < hi - lo) :       -- the IH callee at the self-instantiation p=lo, hiE=hi
    (rootProduce descRoute size flatBase w = windowProduce descRoute 2 size flatBase w)
    ∧ childHi - childLo < hi - lo :=
  ⟨rfl, joint_ih_covers_seqchild_callee (lo := lo) (hi := hi) (p := lo) (hiE := hi)
        (Nat.le_refl lo) (Nat.le_refl hi) h_gate⟩

end Tests.Reflections.RootToWindowBaseAssemblerSwap
