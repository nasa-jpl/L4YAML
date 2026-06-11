/-!
# Reflection 363 — a seam's deferred "source it LATER by frame-transport" typed-fact obligation is often
ALREADY carried by the recursion's existing guard `G` and ALREADY transported by a SIBLING driver over that
same `G`; before authoring a new producer brick, READ the guard's fields and the sibling for the inline
transport — the de-risk is a READ, not a build.

Self-contained (core Lean, no `L4YAML` import) toy model of the move found while turning the
emission-spine-walk ADVANCE arm's threaded `WellTyped (e ++ [fe])` (R362) into a *produced* fact.

R362 threaded the typed fact and filed its production as a residual: "source it later by frame-transport
DOWN from a global `WellTyped`, guarded by a floor." That sounds like new infra. It was not. Two reads
resolved it:
1. **The guard.** The consuming recursion's guard `G` carries a balanced-window structure (`FlowBodyWindow`)
   whose `.wellTyped` field IS the WHOLE-window typed fact — so the "global `WellTyped` to transport down"
   is a *field of a guard the recursion already descends along*, not a fact to manufacture.
2. **The sibling.** A sibling driver over the SAME `G` (`seqWindowRecSeqBody`) had ALREADY written the exact
   transport at its own depth-`0` cut: `WellTyped_subrange … h_win.wellTyped … (h_win.dyck …)`. The new
   "supplier" brick is that four-line transport re-aimed at this seam's slice — same body, different cut.

This toy mirrors that faithfully. `typed` is a typed stack fold (it PUSHES which bracket type opened and POPs
only the matching type). `Win` is the guard (toy of `FlowBodyWindow`): it BUNDLES the whole-context typed
fact `wholeTyped` as a FIELD. `SubrangeTransporter` is the pre-existing transport primitive (toy of
`WellTyped_subrange`) — the demo MODELS it as given (a parameter), because the lesson is that it ALREADY
EXISTS and is re-used, not re-derived. `sibling` invokes it at one cut; `supplier` re-aims the SAME call at
the seam's cut `e ++ [fe]` — note the two proof bodies are token-identical modulo the aimed prefix. The
POSITIVE shows a concrete `Win` whose field holds (`by decide`) and whose seam-prefix is genuinely typed (so
the transport is non-vacuous). The NEGATIVE shows the guard field is LOAD-BEARING: on a mistyped window
(`{ [ } }`, R362's witness) `Win` cannot be built, so the typed fact must hold UPSTREAM — the supplier can
never manufacture it.

(The toy elides the Dyck-floor hypothesis the real `WellTyped_subrange` carries: here the transported region
is a PREFIX from the empty stack, so a successful typed fold cannot dip and the floor is automatic. The real
guard carries `.dyck` because it transports general non-prefix subranges.)
-/

namespace Tests.Reflections.DeferredTypedFactInGuard

set_option autoImplicit false

/-! ## The bracket alphabet + typed stack fold (shared vocabulary with `TypeBlindBridgeFalse`) -/

/-- `os`/`cs` = `[`/`]`; `om`/`cm` = `{`/`}`; `other` = a stack-neutral filler. -/
inductive Brak | os | cs | om | cm | other
  deriving DecidableEq, BEq, Repr

open Brak

/-- Type-blind balance delta (both openers `+1`). -/
def delta : Brak → Int
  | os => 1 | om => 1 | cs => -1 | cm => -1 | other => 0

/-- Cumulative balance. -/
def bal (l : List Brak) : Int := l.foldl (fun acc b => acc + delta b) 0

/-- Typed step: an opener PUSHES which type opened; a closer POPs only the matching type, else `none`. -/
def tstep (b : Brak) (s : List Bool) : Option (List Bool) :=
  match b with
  | os => some (true :: s)
  | om => some (false :: s)
  | cs => match s with | true :: s' => some s' | _ => none
  | cm => match s with | false :: s' => some s' | _ => none
  | other => some s

/-- Typed stack fold. -/
def tfold (s0 : Option (List Bool)) (l : List Brak) : Option (List Bool) :=
  l.foldl (fun acc b => acc.bind (tstep b)) s0

/-- **Typed-and-balanced** (toy of `WellTyped`): the typed fold from the empty stack returns to empty. -/
@[reducible] def typed (l : List Brak) : Prop := tfold (some []) l = some []

/-! ## The GUARD — bundles the WHOLE-context typed fact as a FIELD (toy of `FlowBodyWindow`) -/

/-- The recursion's guard.  Its `wholeTyped` field IS the whole-window typed fact — exactly as
    `FlowBodyWindow.wellTyped` bundles `WellTyped` of the whole window.  So the "global `WellTyped` to
    transport down" is a FIELD here, not a fact to be produced. -/
structure Win (whole : List Brak) : Prop where
  wholeTyped : typed whole

/-! ## The TRANSPORT PRIMITIVE — modeled as GIVEN (toy of `WellTyped_subrange`) -/

/-- The pre-existing balanced-prefix transporter (toy of `WellTyped_subrange`): from the WHOLE-context typed
    fact + a balanced cut, it yields the cut-PREFIX's typed fact.  The demo MODELS it as a parameter because
    the R363 lesson is that this primitive ALREADY EXISTS in the library and is RE-USED — not re-derived. -/
abbrev SubrangeTransporter : Prop :=
  ∀ (whole pre : List Brak), typed whole → (∃ suf, whole = pre ++ suf) → bal pre = 0 → typed pre

/-! ## The SIBLING and the SUPPLIER — SAME body, the transport re-aimed -/

/-- **The sibling driver** (toy of `seqWindowRecSeqBody`): at its own cut `pre`, it transports the guard's
    whole-typed fact DOWN to the prefix by CALLING the transporter on the guard field `w.wholeTyped`. -/
theorem sibling (subrange : SubrangeTransporter)
    (whole pre suf : List Brak) (w : Win whole)
    (h_split : whole = pre ++ suf) (h_bal : bal pre = 0) : typed pre :=
  subrange whole pre w.wholeTyped ⟨suf, h_split⟩ h_bal

/-- **The supplier** (toy of `nestedSeq_recseqentry_locate_advance_welltyped`): re-aims the SAME transporter
    call at the seam's cut `e ++ [fe]`.  Its body is token-identical to `sibling`'s — it is the sibling's
    transport re-aimed, NOT a new lemma: both just project the guard field `w.wholeTyped` into `subrange`. -/
theorem supplier (subrange : SubrangeTransporter)
    (whole e rest : List Brak) (fe : Brak) (w : Win whole)
    (h_split : whole = (e ++ [fe]) ++ rest) (h_bal : bal (e ++ [fe]) = 0) : typed (e ++ [fe]) :=
  subrange whole (e ++ [fe]) w.wholeTyped ⟨rest, h_split⟩ h_bal

/-! ## POSITIVE — a concrete window whose guard field holds and whose seam-prefix is genuinely typed -/

-- whole = `[ a ] , { a }` : `[os, other, cs, other, om, other, cm]`.
def wholePos : List Brak := [os, other, cs, other, om, other, cm]
def ePos : List Brak := [os, other, cs]      -- the head entry `[ a ]`
def fePos : Brak := other                     -- the depth-0 separator
def restPos : List Brak := [om, other, cm]    -- the tail `{ a }`

-- the guard field holds (the whole window is typed):
#guard tfold (some []) wholePos == some []
-- the seam-prefix `e ++ [fe]` is genuinely typed, so the supplier's conclusion is non-vacuous:
#guard tfold (some []) (ePos ++ [fePos]) == some []
-- and it is a depth-0 balanced cut, as the supplier's `h_bal` requires:
#guard bal (ePos ++ [fePos]) == 0
-- the split holds definitionally:
#guard (wholePos == (ePos ++ [fePos]) ++ restPos)

/-- The guard is constructible on the concrete window — its `wholeTyped` field is `by decide`. -/
example : Win wholePos := ⟨by decide⟩

/-- Given the pre-existing transporter, the supplier FIRES on the concrete window: same call, aimed at the
    seam's `e ++ [fe]`.  (`subrange` is the library primitive; here taken as a hypothesis.) -/
example (subrange : SubrangeTransporter) : typed (ePos ++ [fePos]) :=
  supplier subrange wholePos ePos restPos fePos ⟨by decide⟩ (by decide) (by decide)

/-! ## NEGATIVE — the guard field is LOAD-BEARING; a mistyped window cannot build `Win` -/

-- the mistyped map entry `{ [ } }` (R362's witness): balanced but NOT typed.
def mapEntry : List Brak := om :: ([os, cm] ++ [cm])

#guard bal mapEntry == 0                      -- passes a balance-only check…
#guard tfold (some []) mapEntry == none       -- …but the typed fold rejects it: `}` can't pop `[`.

/-- So `typed mapEntry` is false — and therefore the guard cannot be built on this window. -/
example : ¬ typed mapEntry := by decide

/-- The guard field is LOAD-BEARING: on a mistyped window `Win` is uninhabitable, so the supplier can never
    be set up there — the typed fact must hold UPSTREAM (the guard refuses mistyped windows), it is never
    manufactured by the transport. -/
example : ¬ Win mapEntry := fun w => absurd w.wholeTyped (by decide)

end Tests.Reflections.DeferredTypedFactInGuard
