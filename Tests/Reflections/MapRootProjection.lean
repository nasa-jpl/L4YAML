/-! # Reflection 515 — the map root projection: carrier ⊕ gate bridge ⇒ the grammar facts

R513 landed the map separator carrier `MapInteriorSeparators` (a GUARDED universal
`∀ a b, lo' ≤ a → a ≤ b → b ≤ hi' → MapTypedInterior .. → MapGrammarFacts ..`).  R514 landed the gate
bridge `mapTypedInterior_of_opener` (reconstructing the gate's enclosing-`{` conjunct in place from the
window opener).  R515 COMPOSES them into the map root projection `mapGrammarFacts_of_mapRoot`: the map
twin of the seq root projection, the step that turns the abstract carrier into the concrete six grammar
facts the final consumer `flowSubrangesOk_of_window_producers` wants.

The crux the brick pins, modelled below over a toy bracket alphabet:

* **The projection is a ONE-STEP composition, not new induction.**  A guarded-universal carrier yields its
  body by INSTANTIATION: pick the window `[q+1, hi)`, supply the gate, read off the facts.  The gate
  bridge supplies the gate; the carrier supplies the facts.  Nothing recurses — the carrier already did
  the universal work ([[ref-guarded-universal-fold-relocates-guard]]: proving/consuming the carrier
  CONSUMES the guard, it never re-produces it).

* **The gate's two non-premise inputs are FOLDED as hypotheses — naming the producer's contract.**  The
  gate `MapTypedInterior` has three conjuncts.  Two are the consumer's OWN premises (the body balance, and
  the `.flowMappingStart` opener that drives the bridge).  The other two — the pre-opener PREFIX witness
  `btFold (some []) (take q) = some s` and the body FLOOR — are not carried by the consumer's six grammar
  premises, so the projection takes them as hypotheses ([[ref-fold-consumer-chain-to-producer-contract]]).
  At the real consume site they come from `WellTyped_prefix_some` and a `flowBracketBalance_interior_dyck`
  re-base — the SAME two sources the seq path uses.  Folding them here makes the residual a precise
  two-item owed list, not a vague "establish the gate".

* **The prefix witness is genuinely a PREFIX fact, not an interior projection.**  It is about `[0, q]`,
  outside the window `[q+1, hi)` the carrier and facts both live in — so no interior predicate projects it
  ([[ref-prefix-gate-reconstructed-from-boundary]]).  That is exactly why it must be a folded hypothesis
  (reconstructed at the boundary), not derived from the carrier.

This demo (self-contained core Lean, no imports) models all three over a tiny `Tok` alphabet: the gate
bridge from R514, a toy guarded-universal carrier, and the one-step projection `facts_of_root` that
composes them — with the prefix witness and floor folded as hypotheses.  `demo` carries `[propext,
Quot.sound]` (the `Quot.sound` via `List.foldl_append`), faithfully matching the real lemma's profile.
-/

namespace MapRootProjection

/-- Toy bracket token: `[` (seq open), `{` (map open), and everything else. -/
inductive Tok | lbrack | lbrace | other
deriving DecidableEq

/-- One step of the typed bracket stack (toy of `btStep`): `[` pushes `true`, `{` pushes `false`. -/
def btStep (t : Tok) (s : List Bool) : Option (List Bool) :=
  match t with
  | .lbrack => some (true :: s)
  | .lbrace => some (false :: s)
  | .other  => some s

/-- Fold the typed stack across a token list (toy of `btFold`). -/
def btFold (s0 : Option (List Bool)) (l : List Tok) : Option (List Bool) :=
  l.foldl (fun acc t => acc.bind (btStep t)) s0

theorem btFold_append (s0 : Option (List Bool)) (l1 l2 : List Tok) :
    btFold s0 (l1 ++ l2) = btFold (btFold s0 l1) l2 := by
  simp only [btFold, List.foldl_append]

/-- R514's gate-bridge conjunct (toy `enclosingMark_false_of_opener`): a `{` opener after a typed-prefix
    witness gives stack-top `some false` — reconstructed at the boundary, never projected. -/
theorem enclosingMark_false_of_opener (pre : List Tok) (s : List Bool)
    (h_pre : btFold (some []) pre = some s) :
    (btFold (some []) (pre ++ [Tok.lbrace])).bind (·.head?) = some false := by
  rw [btFold_append, h_pre]; rfl

/-- Toy map-typed gate (mirror of `MapTypedInterior`): balance-zero ∧ enclosing-`{` ∧ floored. -/
structure MapTypedInterior (pre : List Tok) (bal : Int) (floored : Prop) : Prop where
  balanced : bal = 0
  isMap : (btFold (some []) (pre ++ [Tok.lbrace])).bind (·.head?) = some false
  floor : floored

/-- R514's gate bridge (toy `mapTypedInterior_of_opener`): bundle balance + reconstructed conjunct + floor. -/
theorem mapTypedInterior_of_opener (pre : List Tok) (s : List Bool) (floored : Prop)
    (h_pre : btFold (some []) pre = some s) (h_bal : (0 : Int) = 0) (h_floor : floored) :
    MapTypedInterior pre 0 floored :=
  ⟨h_bal, enclosingMark_false_of_opener pre s h_pre, h_floor⟩

/-- Toy grammar-facts bundle (mirror of `MapGrammarFacts`): two adjacency facts keyed on the window. -/
structure MapGrammarFacts (lo hi : Nat) : Prop where
  keyContent : lo ≤ hi
  valueContent : lo ≤ hi + 1

/-- Toy guarded-universal carrier (mirror of `MapInteriorSeparators`): every gated sub-window's facts.
    The gate is the typed-interior case (balance fixed at `0`), keyed on the window's pre-opener prefix
    `preOf a` and the body floor `floorOf a b`. -/
def MapInteriorSeparators (lo' hi' : Nat)
    (preOf : Nat → List Tok) (floorOf : Nat → Nat → Prop) : Prop :=
  ∀ a b, lo' ≤ a → a ≤ b → b ≤ hi' →
    MapTypedInterior (preOf a) 0 (floorOf a b) → MapGrammarFacts a b

/-- **The map root projection** (toy of `mapGrammarFacts_of_mapRoot`): from the carrier and the window
    opener, the grammar facts — a ONE-STEP composition.  The gate bridge supplies the carrier's gate
    premise; the carrier delivers the facts.  The prefix witness `h_pre` and floor `floorOf a b` are
    FOLDED as hypotheses (the producer's remaining contract), exactly as the real lemma folds them. -/
theorem facts_of_root (lo' hi' a b : Nat)
    (preOf : Nat → List Tok) (floorOf : Nat → Nat → Prop)
    (h_carrier : MapInteriorSeparators lo' hi' preOf floorOf)
    (h_lo' : lo' ≤ a) (h_ab : a ≤ b) (h_hi' : b ≤ hi')
    (s : List Bool)
    (h_pre : btFold (some []) (preOf a) = some s)                    -- folded prefix witness
    (h_floor : floorOf a b) :                                        -- folded body floor
    MapGrammarFacts a b :=
  h_carrier a b h_lo' h_ab h_hi'
    (mapTypedInterior_of_opener (preOf a) s (floorOf a b) h_pre rfl h_floor)

/-- A concrete carrier: facts hold at every window (toy), gate keyed on a prefix folding to `some []`. -/
def samplePre : Nat → List Tok := fun _ => [Tok.other]
def sampleFloor : Nat → Nat → Prop := fun _ _ => True
theorem sampleCarrier : MapInteriorSeparators 0 10 samplePre sampleFloor :=
  fun _a b _ hab _ _ => ⟨hab, Nat.le_trans hab (Nat.le_succ b)⟩
theorem sample_pre : btFold (some []) (samplePre 2) = some [] := rfl

/-- The demo deliverable: the root projection fires — the facts at `[2,5)` follow from the carrier, the
    folded prefix witness, and the folded floor, with the gate discharged in place by the bridge. -/
theorem demo : MapGrammarFacts 2 5 :=
  facts_of_root 0 10 2 5 samplePre sampleFloor sampleCarrier
    (by decide) (by decide) (by decide) [] rfl trivial

end MapRootProjection

-- Axiom audit (machine-checked: `#guard_msgs` pins the profile and fails the build if it ever drifts;
-- it also CONSUMES the info output, so the audit no longer pollutes the build log).
-- `[propext, Quot.sound]`, faithfully matching the real lemma (`Quot.sound` via `List.foldl_append`,
-- inherited through the R514 gate bridge).
/-- info: 'MapRootProjection.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MapRootProjection.demo
