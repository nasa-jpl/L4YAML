/-! # Reflection 514 — the map gate's enclosing-opener conjunct, reconstructed in place

R513 landed the map separator carrier `MapInteriorSeparators` (the `some false` dual of the seq
carrier), whose body is GUARDED by the gate `MapTypedInterior`.  Its eventual consumer
(`mapGrammarFacts_of_mapRoot`, the map twin of the seq root projection) instantiates the carrier at
`a := lo, b := hi` and must therefore SUPPLY that gate.  R514 lands the genuine "real work" that supply
needs: the gate's enclosing-opener conjunct
`(btFold (some []) (tokens.toList.take a)).bind (·.head?) = some false`.

The crux the brick pins, modelled below over a toy bracket alphabet:

* **The conjunct is about the PREFIX `[0,a)`, not the window interior `[a,b)`** — so it is NOT a
  projection of any interior predicate (`FlowBodyWindow.wellTyped` only sees the interior).  It must be
  RECONSTRUCTED at the window from its boundary opener
  ([[ref-reconstruct-in-place-over-relocate]] / [[ref-prefix-gate-reconstructed-from-boundary]]): split
  the prefix `take (q+1) = take q ++ [opener]`, fold the typed-prefix witness `btFold .. (take q) = some
  s` through the single opener step, read the new stack top.

* **The seq/map mirror is a pure TWO-SYMBOL TEXT-SWAP resting on ONE `btStep` fact.**  The typed
  bracket stack pushes `true` for `[` and `false` for `{` (`WellBracketed.lean:1540-1541`).  That single
  asymmetry is the WHOLE difference between the seq lemma `enclosingMark_true_of_opener` and its map
  dual `enclosingMark_false_of_opener`: swap `.flowSequenceStart → .flowMappingStart` and
  `some true → some false`, and the proof is byte-identical (same `take_add_one` split, same
  `btFold_append`, same `getElem!` bridge).  The mirror SHEDS NO machinery
  ([[ref-near-leaf-mirror-sheds-machinery]] in its degenerate form: nothing to drop, nothing to add) —
  it is a [[ref-mirror-cost-delta-alphabet]] of cost exactly `{push-symbol swap}`.  The real map lemma
  carries axioms `[propext, Quot.sound]`, identical to the seq lemma.

* **The full gate bundles the reconstructed conjunct with the two interior facts it already has.**  The
  consume-site corollary `mapTypedInterior_of_opener` packages balance-zero + the reconstructed
  enclosing-`{` + the body floor into `MapTypedInterior` — exactly the three fields the gate needs, no
  second guard threaded.

This demo (self-contained core Lean, no imports) models all three over a tiny `Tok` alphabet
(`lbrack` = `[`, `lbrace` = `{`, `other`): the `btStep` push-dual, the prefix-split reconstruction in
BOTH directions (`false` for map, `true` for seq — proving the swap is the only difference), and the
bundled gate.  `demo` carries `[propext, Quot.sound]` — the `Quot.sound` from `List.foldl_append`,
faithfully matching the real lemmas' profile.
-/

namespace MapGateBridge

/-- Toy bracket token: `[` (seq open), `{` (map open), and everything else. -/
inductive Tok | lbrack | lbrace | other
deriving DecidableEq

/-- One step of the typed bracket stack (toy of the real `btStep`, `WellBracketed.lean:1538`): `[`
    pushes `true`, `{` pushes `false`.  THIS push-dual is the entire seq/map asymmetry. -/
def btStep (t : Tok) (s : List Bool) : Option (List Bool) :=
  match t with
  | .lbrack => some (true :: s)
  | .lbrace => some (false :: s)
  | .other  => some s

/-- Fold the typed stack across a token list (toy of `btFold`). -/
def btFold (s0 : Option (List Bool)) (l : List Tok) : Option (List Bool) :=
  l.foldl (fun acc t => acc.bind (btStep t)) s0

/-- `btFold` splits across `++` — the lemma that lets a prefix `take (q+1) = take q ++ [opener]` fold
    its already-known `take q` witness through just the final opener step. -/
theorem btFold_append (s0 : Option (List Bool)) (l1 l2 : List Tok) :
    btFold s0 (l1 ++ l2) = btFold (btFold s0 l1) l2 := by
  simp only [btFold, List.foldl_append]

/-- **The MAP reconstruction** (toy of `enclosingMark_false_of_opener`): a `{` opener after a
    typed-prefix witness `btFold .. pre = some s` gives stack-top `some false` — the gate's enclosing-`{`
    conjunct, rebuilt at the boundary, never projected from the interior. -/
theorem enclosingMark_false_of_opener (pre : List Tok) (s : List Bool)
    (h_pre : btFold (some []) pre = some s) :
    (btFold (some []) (pre ++ [Tok.lbrace])).bind (·.head?) = some false := by
  rw [btFold_append, h_pre]; rfl

/-- **The SEQ reconstruction**, the DUAL (toy of `enclosingMark_true_of_opener`): a `[` opener gives
    stack-top `some true`.  IDENTICAL proof — only `lbrace → lbrack` and `false → true` change.  Placing
    the two side by side is the point: the mirror is a pure two-symbol swap. -/
theorem enclosingMark_true_of_opener (pre : List Tok) (s : List Bool)
    (h_pre : btFold (some []) pre = some s) :
    (btFold (some []) (pre ++ [Tok.lbrack])).bind (·.head?) = some true := by
  rw [btFold_append, h_pre]; rfl

/-- Toy map-typed gate (mirror of `MapTypedInterior`): balance-zero ∧ enclosing-`{` ∧ floored. -/
structure MapTypedInterior (pre : List Tok) (bal : Int) (floored : Prop) : Prop where
  balanced : bal = 0
  isMap : (btFold (some []) (pre ++ [Tok.lbrace])).bind (·.head?) = some false
  floor : floored

/-- **The full gate, discharged from the opener** (mirror of `mapTypedInterior_of_opener`): bundle the
    balance, the reconstructed enclosing conjunct, and the floor — the three gate fields, no second
    guard. -/
theorem mapTypedInterior_of_opener (pre : List Tok) (s : List Bool) (floored : Prop)
    (h_pre : btFold (some []) pre = some s) (h_bal : (0 : Int) = 0) (h_floor : floored) :
    MapTypedInterior pre 0 floored :=
  ⟨h_bal, enclosingMark_false_of_opener pre s h_pre, h_floor⟩

/-- A concrete `{`-enclosed prefix: `[ {, other ]` folds to the typed stack `[false]`. -/
def sample : List Tok := [Tok.lbrace, Tok.other]
theorem sample_pre : btFold (some []) sample = some [false] := rfl

/-- The demo deliverable: the map reconstruction AND its seq dual both fire from the same prefix
    witness (the swap is the only difference), and the bundled map gate holds. -/
theorem demo :
    (btFold (some []) (sample ++ [Tok.lbrace])).bind (·.head?) = some false
    ∧ (btFold (some []) (sample ++ [Tok.lbrack])).bind (·.head?) = some true
    ∧ MapTypedInterior sample 0 True :=
  ⟨enclosingMark_false_of_opener sample [false] sample_pre,
   enclosingMark_true_of_opener sample [false] sample_pre,
   mapTypedInterior_of_opener sample [false] True sample_pre rfl trivial⟩

end MapGateBridge

-- Axiom audit: `[propext, Quot.sound]`, faithfully matching the real lemmas (`Quot.sound` via
-- `List.foldl_append`).
#print axioms MapGateBridge.demo
