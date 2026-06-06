/-!
# Reflection 321 — push-overwrite vs frame-preserve: an accumulator-guard's two recursion edges have OPPOSITE parent-dependence

Self-contained (core Lean) toy of the `SeqEnclosed` guard (the `lo`-keyed enclosing btFold-top fact)
and its two preservation edges `seqEnclosed_descend` / `seqEnclosed_advance`.

The real situation: the seq `windowWidth_strongRecOn` producer threads a guard that reads the TOP of the
typed bracket stack — `SeqEnclosed tokens lo := (btFold (some []) (take lo)).bind (·.head?) = some true`
(the window sits immediately inside a flow sequence `[`, not a mapping `{`).  Threading it down the
recursion needs two edges, and they depend on the parent's tracked TOP in OPPOSITE ways:

* **DESCEND = PUSH.**  Entering a nested bracket PREPENDS a new top (`true` for `[`), OVERWRITING
  whatever the parent's top was.  The edge is parent-value-BLIND: it needs only that the parent
  accumulator is DEFINED (`some _`), never that the parent's top is `true`.  It would even hold where
  the parent is NOT seq-enclosed (a `[` inside a `{` still encloses-as-seq).

* **ADVANCE = FRAME.**  Moving past a sibling across a balanced / `WellTyped` segment returns the
  accumulator to the SAME state, so the top is PRESERVED.  The edge is parent-value-DEPENDENT: it
  carries the parent's top forward and CANNOT manufacture enclosure where there was none.

This file proves the two edge theorems (the transferable nugget) and EXHIBITS the asymmetry
computationally: over the SAME non-enclosed parent, the PUSH edge produces enclosure while the FRAME
edge does not.

Distinct from `ConverseForwardAsymmetry` (R-converse contrasts a property vs its CONVERSE); this
contrasts ONE guard's two recursion EDGES.  The accumulator-guard analogue of `GuardEdgeFloorAsymmetry`
(R288), where the balance guard's two edges need different FLOORS — here the split is whether the
parent's value is read at all.
-/

namespace Tests.Reflections.PushBlindFramePreserveDependent

set_option autoImplicit false

-- ════════════════════ The toy accumulator — a typed bracket stack ════════════════════
-- `true` = a sequence frame `[`, `false` = a mapping frame `{`, `none` = malformed (underflow/mismatch).
abbrev Acc := Option (List Bool)

/-- The guard: the TOP of the stack is `true` (immediately inside a sequence). Toy of `SeqEnclosed`. -/
def Enclosed (s : Acc) : Prop := s.bind (·.head?) = some true

/-- DESCEND = PUSH a new frame `b`. Toy of `btStep` on an opener: prepend, overwriting the old top. -/
def push (b : Bool) (s : Acc) : Acc := s.map (b :: ·)

/-- ADVANCE = FRAME a balanced segment: it returns the accumulator UNCHANGED. Toy of `WellTyped_frame`
    (a `WellTyped` segment opens and closes everything it touches, returning to the same stack). -/
def frame (s : Acc) : Acc := s

-- ════════════════════ The PROVEN nugget — the two edges, with OPPOSITE hypotheses ════════════════════

/-- **DESCEND edge (PUSH `true`).**  Toy of `seqEnclosed_descend`.  Parent-value-BLIND: the hypothesis
    is only that the parent is DEFINED (`∃ l, s = some l`), NOT that the parent is `Enclosed`.  Pushing
    `true` overwrites the top, so enclosure follows regardless of the parent's top. -/
theorem descend_push {s : Acc} (h_def : ∃ l, s = some l) : Enclosed (push true s) := by
  obtain ⟨l, rfl⟩ := h_def
  rfl

/-- **ADVANCE edge (FRAME).**  Toy of `seqEnclosed_advance`.  Parent-value-DEPENDENT: the hypothesis is
    the parent `Enclosed`; the frame preserves the top, so enclosure is carried forward.  (It cannot be
    manufactured — see the negative below.) -/
theorem advance_frame {s : Acc} (h : Enclosed s) : Enclosed (frame s) := h

-- ════════════════════ The asymmetry, computationally ════════════════════
/-- Boolean form of `Enclosed`, for `#guard`. -/
def isEnclosed (s : Acc) : Bool := s.bind (·.head?) == some true

-- DESCEND is parent-value-BLIND — over a NON-enclosed parent (top `false`), the push STILL encloses:
#guard isEnclosed (some [false]) == false             -- parent NOT enclosed (top is a mapping frame)
#guard isEnclosed (push true (some [false])) == true   -- ...yet DESCEND encloses — blind to the parent

-- DESCEND needs only DEFINEDNESS — over `none` (malformed parent) it cannot:
#guard isEnclosed (push true none) == false

-- ADVANCE is parent-value-DEPENDENT — it PRESERVES, so it cannot manufacture enclosure:
#guard isEnclosed (frame (some [true]))  == true      -- enclosed parent → enclosed (carried forward)
#guard isEnclosed (frame (some [false])) == false     -- non-enclosed parent → STILL not enclosed

-- THE ASYMMETRY IN ONE LINE: the SAME non-enclosed parent, OPPOSITE results across the two edges.
#guard isEnclosed (push true (some [false])) != isEnclosed (frame (some [false]))

end Tests.Reflections.PushBlindFramePreserveDependent
