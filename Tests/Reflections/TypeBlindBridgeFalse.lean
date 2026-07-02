/-!
# Reflection 362 — a balance-only invariant is TYPE-BLIND, so a "structure ⇒ typed-fact" bridge across a
type-blind constructor is FALSE; PROBE a minimal pair before authoring, and on refutation THREAD the typed
fact as a parametric-assembler hypothesis rather than inventing a stronger invariant.

Self-contained (core Lean, no `L4YAML` import) toy model of the move found while composing the emission-spine-
walk ADVANCE seam `nestedSeq_recseqentry_locate_advance_step`.

The seam's domain brick (`seqPathAllSeq_advance`) demanded the consumed segment be `WellTyped`. The plan
named a discharge: "the head entry is a `RecSeqEntry`, a balanced bracket pair ⇒ `WellTyped`". That bridge
is FALSE, and the toy shows exactly why: `WellBracketed` (the `pbalance` Dyck condition) is **type-blind** —
`flowBracketDelta` maps BOTH `[`/`{` to `+1` and BOTH `]`/`}` to `−1`, so it cannot distinguish bracket
TYPES. A structural inductive whose constructor gates only on this balance invariant (the real
`RecSeqEntry.map` stores only `WellBracketed interior`) ADMITS a balanced-but-MISTYPED witness `{ [ } }`
(balance returns to 0, but `}` cannot pop a `[`). So `structure ⇒ WellTyped` is refuted by ONE concrete
witness — far cheaper than a `∀`-survey. On refutation: do NOT strengthen the shared inductive, do NOT chase
a stronger local invariant (a type-blind invariant cannot CREATE a typed fact, only TRANSPORT one); THREAD
the typed fact as a parametric-assembler hypothesis and isolate its production as a later frame-transport.

This toy mirrors the structure faithfully: `bal` is the type-blind balance metric (`delta` maps both openers
to `+1`); `tfold`/`typed` is the typed stack fold (it PUSHES which bracket type opened and POPs only the
matching type); `Struct.wrap` is the type-blind constructor (gates only on `balOnly interior`). The `#guard`s
show the mistyped `{ [ } }` passes `balOnly` but FAILS `typed` — so `Struct ⇒ typed` is false (the `example`
builds it as a real `Struct` that is provably not `typed`). The `seam` then THREADS `typed` as a hypothesis
it cannot manufacture from `Struct` alone.
-/

namespace Tests.Reflections.TypeBlindBridgeFalse

set_option autoImplicit false

/-! ## The bracket alphabet — two DISTINCT bracket types (`[]` sequence, `{}` mapping) plus a filler -/

/-- `os`/`cs` = `[`/`]` (sequence brackets); `om`/`cm` = `{`/`}` (mapping brackets); `other` = a delta-`0`
    filler (a scalar). The two opener types are DISTINCT tokens but share the same balance delta. -/
inductive Brak | os | cs | om | cm | other
  deriving DecidableEq, BEq, Repr

open Brak

/-! ## The TYPE-BLIND balance metric (toy of `pbalance` / `WellBracketed`) -/

/-- **Type-blind delta** (toy of `flowBracketDelta`).  BOTH openers map to `+1`, BOTH closers to `−1` —
    so the metric cannot tell `[` from `{`.  THIS is the source of the false bridge. -/
def delta : Brak → Int
  | os => 1 | om => 1 | cs => -1 | cm => -1 | other => 0

/-- Cumulative balance (toy of `pbalance`). -/
def bal (l : List Brak) : Int := l.foldl (fun acc b => acc + delta b) 0

/-- **The type-blind gate** (toy of `WellBracketed`).  Here just balance-`0`; the real `WellBracketed` adds
    a prefix floor `∀ i, bal (l.take i) ≥ 0`, which is EQUALLY type-blind, so it changes nothing about the
    refutation below. -/
@[reducible] def balOnly (l : List Brak) : Prop := bal l = 0

/-! ## The TYPED stack fold (toy of `btFold` / `WellTyped`) — STRICTLY stronger: it tracks bracket TYPES -/

/-- **Typed step** (toy of `btStep`).  An opener PUSHES a bit marking WHICH type opened (`true` = seq,
    `false` = map); a closer POPs only the MATCHING type, else `none`.  This is what `balOnly` cannot see. -/
def tstep (b : Brak) (s : List Bool) : Option (List Bool) :=
  match b with
  | os => some (true :: s)
  | om => some (false :: s)
  | cs => match s with | true :: s' => some s' | _ => none
  | cm => match s with | false :: s' => some s' | _ => none
  | other => some s

/-- Typed stack fold (toy of `btFold`). -/
def tfold (s0 : Option (List Bool)) (l : List Brak) : Option (List Bool) :=
  l.foldl (fun acc b => acc.bind (tstep b)) s0

/-- **Typed-and-balanced** (toy of `WellTyped`): the typed fold from the empty stack returns to empty. -/
@[reducible] def typed (l : List Brak) : Prop := tfold (some []) l = some []

/-! ## The TYPE-BLIND constructor — gates only on the balance metric (toy of `RecSeqEntry.map`) -/

/-- A toy structural inductive.  The `wrap` constructor gates its interior ONLY on `balOnly` (the
    type-blind metric) — exactly as the real `RecSeqEntry.map` stores only `WellBracketed interior`.
    So `wrap` ADMITS a mistyped interior, and `Struct ⇒ typed` is FALSE. -/
inductive Struct : List Brak → Prop where
  | leaf (b : Brak) (h : delta b = 0) : Struct [b]
  | wrap (op cl : Brak) (interior : List Brak)
      (h_op : delta op = 1) (h_cl : delta cl = -1) (h_bal : balOnly interior) :
      Struct (op :: (interior ++ [cl]))

/-! ## The PROBE — one concrete minimal pair refutes the `Struct ⇒ typed` bridge -/

-- The mistyped map interior `[ }` : a sequence-opener followed by a mapping-closer.
def interior : List Brak := [os, cm]
-- The whole map entry `{ [ } }` = `om :: (interior ++ [cm])`.
def mapEntry : List Brak := om :: (interior ++ [cm])

-- (1) the interior is balance-`0`, so it PASSES the type-blind `wrap` gate:
#guard bal interior == 0
-- the whole entry is balance-`0` too (a balance-only check would accept it):
#guard bal mapEntry == 0
-- (2) BUT the entry is NOT `typed`: the `}` cannot pop the `[`, so the typed fold returns `none`:
#guard tfold (some []) mapEntry == none
-- ⇒ `Struct mapEntry` holds yet `typed mapEntry` is false: the bridge `Struct ⇒ typed` is REFUTED.

/-- The witness IS a real `Struct` (the type-blind `wrap` constructor accepts it). -/
example : Struct mapEntry := by
  show Struct (om :: ([os, cm] ++ [cm]))
  exact Struct.wrap om cm [os, cm] (by decide) (by decide) (by decide)

/-- …yet it is NOT `typed` — so no bridge `∀ l, Struct l → typed l` can exist. -/
example : ¬ typed mapEntry := by decide

/-! ## The MOVE on refutation — THREAD the typed fact; the seam cannot manufacture it from `Struct` -/

/-- **The ADVANCE seam analogue.**  It needs `typed (e ++ [fe])` for its domain step, but the probe proved
    that fact is NOT a projection of `Struct e` (the `wrap` constructor is type-blind).  So the seam THREADS
    `typed (e ++ [fe])` as a parametric-assembler HYPOTHESIS (toy of
    `nestedSeq_recseqentry_locate_advance_step`'s `h_wt_seg`) — it consumes the typed fact, never derives it.
    The genuine residual (PRODUCING `typed (e ++ [fe])`) is isolated for a later frame-transport. -/
theorem seam (e : List Brak) (fe : Brak) (_h_e : Struct e) (_h_fe : delta fe = 0)
    (h_typed : typed (e ++ [fe])) : typed (e ++ [fe]) :=
  h_typed

/-! ## A POSITIVE — a CORRECTLY-typed entry is both `Struct` and `typed`; the seam fires on it -/

-- a well-typed sequence entry `[ a ]` = `[os, other, cs]`:
def goodEntry : List Brak := os :: ([other] ++ [cs])
-- the separator `fe` (a delta-`0` filler):
def feTok : Brak := other

-- the good entry is `typed`, and so is `goodEntry ++ [fe]` (the separator is stack-neutral):
#guard tfold (some []) goodEntry == some []
#guard tfold (some []) (goodEntry ++ [feTok]) == some []

example : Struct goodEntry :=
  Struct.wrap os cs [other] (by decide) (by decide) (by decide)

-- the seam fires once the threaded typed fact is supplied (here it genuinely holds):
example : typed (goodEntry ++ [feTok]) :=
  seam goodEntry feTok (Struct.wrap os cs [other] (by decide) (by decide) (by decide))
    (by decide) (by decide)

end Tests.Reflections.TypeBlindBridgeFalse
