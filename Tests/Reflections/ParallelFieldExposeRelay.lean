/-!
# Reflection 427 — a parallel carrier field's STRUCTURE-EXPOSE carries zero new index reasoning:
  it rides the sibling field's pre-built `_array` bridge as a token-keyed one-liner

Self-contained (core Lean, no `L4YAML` import) toy of the R427 finding.

A list-predicate carrier field `P block` (here a toy adjacency field) reaches the whole-structure
conclusion by a RELAY of slice re-basings:

* producer → body characterization  (re-base `block` to `drop old_sz` via a `drop`-identity), and
* body characterization → structure lemma  (re-base the `drop lo` SLICE to the array `getElem!`
  index space via the `_array` projection lemma + the per-lemma `tokens[k]! = slice[k]` helper).

ALL the index reasoning — the `k - lo` offset, the slice↔array element identity — is concentrated
in the `_array` projection lemma (`SepAdj_array`, `OpenerAdj_array`).  Once that ONE lemma exists for
a field, the structure-EXPOSE `have h_body_X` block is a CHARACTER-FOR-CHARACTER clone of the sibling
field's, swapping only the trigger token, the gate, and the `_array` lemma name.  So when you budget a
NEW parallel field, the cost is FRONT-LOADED at the token-concrete combinator + `_array` layer (R421:
the relocated content-start obligation); the structure-expose is mechanical plumbing — the COMPLEMENT
of R421 (where the mirror costs) is R427 (where the mirror is free).

The toy below models exactly that:

* `AdjA` / `AdjB` — two sibling all-depth adjacency fields differing only in trigger/target token
  (toys of `OpenerAdj` (trigger `.flowSequenceStart`) and `SepAdj` (trigger `.flowEntry`)).
* `AdjA_array` / `AdjB_array` — the `_array` projection bridges; their bodies are IDENTICAL up to the
  token swap, and they carry ALL the `k - lo` offset arithmetic (paid once per field).
* POSITIVE `exposeA_is_oneliner` / `exposeB_is_oneliner` — the structure-EXPOSE for each field is the
  single term `Adj_array arr lo h`: no inline index reasoning at the expose site.
* NEGATIVE `#guard`s — the `k - lo` offset INSIDE the bridge is load-bearing, not identity: consulting
  the slice at the GLOBAL index reads the wrong element, so the bridge carries real content (which is
  precisely why exposing a SECOND field that reuses an already-built bridge costs nothing new).
-/

namespace Tests.Reflections.ParallelFieldExposeRelay

set_option autoImplicit false

/-- Sibling field A (toy of `OpenerAdj`): every `1` is immediately followed by a `9`. -/
def AdjA (l : List Nat) : Prop :=
  ∀ (k : Nat) (h : k + 1 < l.length), l[k]'(Nat.lt_of_succ_lt h) = 1 → l[k+1]'h = 9

/-- Sibling field B (toy of `SepAdj`): every `2` is immediately followed by an `8`.  The same SHAPE
    as `AdjA`, differing only in the trigger/target token. -/
def AdjB (l : List Nat) : Prop :=
  ∀ (k : Nat) (h : k + 1 < l.length), l[k]'(Nat.lt_of_succ_lt h) = 2 → l[k+1]'h = 8

/-- The `_array` projection bridge for field A (toy of `OpenerAdj_array`).  Re-bases the `drop lo`
    slice to the array `getElem!` index space.  ALL the index reasoning — the `k - lo` offset, the
    slice↔array element identity — lives HERE, proved once for field A. -/
theorem AdjA_array (arr : Array Nat) (lo : Nat) (h : AdjA (arr.toList.drop lo)) :
    ∀ (k : Nat), lo ≤ k → k + 1 < arr.size → arr[k]! = 1 → arr[k+1]! = 9 := by
  intro k h_lo hk1 htrig
  have hk0 : k < arr.size := by omega
  have h_len : (arr.toList.drop lo).length = arr.size - lo := by
    rw [List.length_drop, Array.length_toList]
  have hj1 : (k - lo) + 1 < (arr.toList.drop lo).length := by rw [h_len]; omega
  have hj0 : k - lo < (arr.toList.drop lo).length := by omega
  have e_k : (arr.toList.drop lo)[k - lo]'hj0 = arr[k]! := by
    rw [getElem!_pos arr k hk0, List.getElem_drop, Array.getElem_toList (by omega)]; congr 1; omega
  have e_k1 : (arr.toList.drop lo)[(k - lo) + 1]'hj1 = arr[k+1]! := by
    rw [getElem!_pos arr (k+1) hk1, List.getElem_drop, Array.getElem_toList (by omega)]; congr 1; omega
  have key := h (k - lo) hj1 (by rw [e_k]; exact htrig)
  rw [e_k1] at key; exact key

/-- The `_array` bridge for field B (toy of `SepAdj_array`) — a VERBATIM clone of `AdjA_array` with
    the token swap `1 → 2` / `9 → 8`.  Same `k - lo` offset reasoning, character-for-character. -/
theorem AdjB_array (arr : Array Nat) (lo : Nat) (h : AdjB (arr.toList.drop lo)) :
    ∀ (k : Nat), lo ≤ k → k + 1 < arr.size → arr[k]! = 2 → arr[k+1]! = 8 := by
  intro k h_lo hk1 htrig
  have hk0 : k < arr.size := by omega
  have h_len : (arr.toList.drop lo).length = arr.size - lo := by
    rw [List.length_drop, Array.length_toList]
  have hj1 : (k - lo) + 1 < (arr.toList.drop lo).length := by rw [h_len]; omega
  have hj0 : k - lo < (arr.toList.drop lo).length := by omega
  have e_k : (arr.toList.drop lo)[k - lo]'hj0 = arr[k]! := by
    rw [getElem!_pos arr k hk0, List.getElem_drop, Array.getElem_toList (by omega)]; congr 1; omega
  have e_k1 : (arr.toList.drop lo)[(k - lo) + 1]'hj1 = arr[k+1]! := by
    rw [getElem!_pos arr (k+1) hk1, List.getElem_drop, Array.getElem_toList (by omega)]; congr 1; omega
  have key := h (k - lo) hj1 (by rw [e_k]; exact htrig)
  rw [e_k1] at key; exact key

/-! ## The structure-EXPOSE is a one-liner — it rides the pre-built bridge. -/

/-- **POSITIVE** — exposing field A at the array boundary, given the producer's `drop lo` slice
    output, is the single term `AdjA_array arr lo h`: NO inline index arithmetic at the expose site.
    (Mirror of the `have h_body_opener := … OpenerAdj_array …` block in the structure lemma.) -/
theorem exposeA_is_oneliner (arr : Array Nat) (lo : Nat) (h : AdjA (arr.toList.drop lo)) :
    ∀ (k : Nat), lo ≤ k → k + 1 < arr.size → arr[k]! = 1 → arr[k+1]! = 9 :=
  AdjA_array arr lo h

/-- **POSITIVE** — exposing the SECOND field B is the SAME one-liner with the token-keyed bridge
    swapped (`AdjB_array`).  The expose paid nothing new; the cost was the bridge, built once.
    (Mirror of `have h_body_separator := … SepAdj_array …`, the R427 brick.) -/
theorem exposeB_is_oneliner (arr : Array Nat) (lo : Nat) (h : AdjB (arr.toList.drop lo)) :
    ∀ (k : Nat), lo ≤ k → k + 1 < arr.size → arr[k]! = 2 → arr[k+1]! = 8 :=
  AdjB_array arr lo h

/-! ## Why the bridge is load-bearing — the `k - lo` offset is NOT identity. -/

-- For `arr = #[5, 1, 9]`, `lo = 1`, the slice `drop 1 = [1, 9]`.  The slice's LOCAL index 1 is `9`,
-- but the array's GLOBAL index 1 is `1` — different elements.  An expose that skipped the `k - lo`
-- offset (consulting the slice at the global `k`) would read the WRONG element; the bridge's offset
-- carries real content.  This is exactly why a SECOND field reusing the built bridge costs nothing:
-- the hard part (the offset) was already discharged once.
#guard ((#[5, 1, 9] : Array Nat).toList.drop 1)[1]! == 9      -- slice at LOCAL index 1
#guard (#[5, 1, 9] : Array Nat)[1]! == 1                       -- array at GLOBAL index 1
#guard (((#[5, 1, 9] : Array Nat).toList.drop 1)[1]! ==
        (#[5, 1, 9] : Array Nat)[1]!) == false                -- the index spaces genuinely differ

end Tests.Reflections.ParallelFieldExposeRelay
