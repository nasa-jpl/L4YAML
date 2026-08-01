/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Spec.Types
import L4YAML.Token.Token

/-!
# The value-determined token run of an emission

`emitTokVals v` is the exact `.val`-run (filtered token list, without the stream framing
`streamStart`/`streamEnd`) that `Scanner.scanFiltered (emit v)` produces — as a pure function of
the VALUE, independent of where in a larger emission the item sits.  This is the content pin the
general Bridge needs: the deep chain producers (`EmitScansInFlowRecEntryDeep`) already quantify
over arbitrary admissible scanner states, so once the produced `block` is pinned to
`emitTokVals v`, the in-stream window and the standalone window of the same item are equal
`.val`-runs by transitivity — no scanner translation-invariance lemma required.

Shape (mirrors `emit`):
* scalar `s`   ↦ `[.scalar s.content .doubleQuoted]` (the emitter always double-quotes);
* alias `n`    ↦ `[.scalar ("*" ++ n) .doubleQuoted]` (the emitter quotes aliases as scalars);
* sequence     ↦ `[` ++ body ++ `]` with `.flowEntry`-separated item runs;
* mapping      ↦ `{` ++ body ++ `}` with per-pair `.key ⟨key run⟩ .value ⟨value run⟩` and
  `.flowEntry` separators (the scanner materialises the `.key`/`.value` markers for every flow
  pair, scalar-keyed or not — pinned by the `TokValsPin` producer).

`FlowCleanTok` is the window gate of the value-locality joint (`ValueLocality.lean`): the token
kinds the parser dispatches on purely by `.val` with no cross-window reads.  Everything
`emitTokVals` produces is flow-clean (`emitTokVals_flowClean`), which is what lets the joint
drop anchors/tagHandles hypotheses entirely at the emission call sites.
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML

/-- The expected filtered `.val`-run of `emit v` (without stream framing). -/
def emitTokVals : YamlValue → List YamlToken
  | .scalar s => [.scalar s.content .doubleQuoted]
  | .sequence _ items .. => .flowSequenceStart :: (seqTokVals items.toList ++ [.flowSequenceEnd])
  | .mapping _ pairs .. => .flowMappingStart :: (mapTokVals pairs.toList ++ [.flowMappingEnd])
  | .alias name => [.scalar ("*" ++ name) .doubleQuoted]
where
  /-- Body run of a flow sequence: `.flowEntry`-separated item runs. -/
  seqTokVals : List YamlValue → List YamlToken
    | [] => []
    | [v] => emitTokVals v
    | v :: vs => emitTokVals v ++ (.flowEntry :: seqTokVals vs)
  /-- Body run of a flow mapping: `.flowEntry`-separated `.key k .value v` pair runs. -/
  mapTokVals : List (YamlValue × YamlValue) → List YamlToken
    | [] => []
    | [(k, v)] => .key :: (emitTokVals k ++ (.value :: emitTokVals v))
    | (k, v) :: rest =>
        (.key :: (emitTokVals k ++ (.value :: emitTokVals v))) ++ (.flowEntry :: mapTokVals rest)

/-- The window gate of the value-locality joint: token kinds the parser consumes by `.val` alone
    on its success paths (no `tagHandles` read, no anchor registration, no alias lookup, no
    pre-window `isSeqEntry` read — those need `.tag`/`.anchor`/`.alias`/`.blockEntry` heads,
    all excluded here). -/
def FlowCleanTok : YamlToken → Bool
  | .scalar _ _ => true
  | .flowSequenceStart => true
  | .flowSequenceEnd => true
  | .flowMappingStart => true
  | .flowMappingEnd => true
  | .flowEntry => true
  | .key => true
  | .value => true
  | _ => false

/-! ## Unfolding equations (definitional) -/

@[simp] lemma seqTokVals_nil : emitTokVals.seqTokVals [] = [] := rfl

lemma seqTokVals_singleton (v : YamlValue) :
    emitTokVals.seqTokVals [v] = emitTokVals v := rfl

lemma seqTokVals_cons_cons (v w : YamlValue) (vs : List YamlValue) :
    emitTokVals.seqTokVals (v :: w :: vs)
      = emitTokVals v ++ (.flowEntry :: emitTokVals.seqTokVals (w :: vs)) := rfl

@[simp] lemma mapTokVals_nil : emitTokVals.mapTokVals [] = [] := rfl

lemma mapTokVals_singleton (k v : YamlValue) :
    emitTokVals.mapTokVals [(k, v)]
      = .key :: (emitTokVals k ++ (.value :: emitTokVals v)) := rfl

lemma mapTokVals_cons_cons (k v : YamlValue) (p : YamlValue × YamlValue)
    (rest : List (YamlValue × YamlValue)) :
    emitTokVals.mapTokVals ((k, v) :: p :: rest)
      = (.key :: (emitTokVals k ++ (.value :: emitTokVals v)))
          ++ (.flowEntry :: emitTokVals.mapTokVals (p :: rest)) := rfl

/-! ## Structure lemmas -/

/-- Every emission's token run is non-empty. -/
lemma emitTokVals_ne_nil (v : YamlValue) : emitTokVals v ≠ [] := by
  cases v <;> simp [emitTokVals]

lemma emitTokVals_length_pos (v : YamlValue) : 0 < (emitTokVals v).length :=
  List.length_pos_iff.mpr (emitTokVals_ne_nil v)

/-- The head of an emission's run is a content-start token: a scalar or a flow opener.
    (Feeds the loop walks: element heads are never `.flowSequenceEnd`/`.key`/`.flowEntry`.) -/
lemma emitTokVals_head (v : YamlValue) :
    (∃ c st, (emitTokVals v).head? = some (.scalar c st))
    ∨ (emitTokVals v).head? = some .flowSequenceStart
    ∨ (emitTokVals v).head? = some .flowMappingStart := by
  cases v with
  | scalar s => exact Or.inl ⟨s.content, .doubleQuoted, rfl⟩
  | sequence style items tag anchor => exact Or.inr (Or.inl rfl)
  | mapping style pairs tag anchor => exact Or.inr (Or.inr rfl)
  | alias name => exact Or.inl ⟨"*" ++ name, .doubleQuoted, rfl⟩

/-- Item count is bounded by the body-run length (each item contributes ≥ 1 token). -/
lemma seqTokVals_length_ge (items : List YamlValue) :
    items.length ≤ (emitTokVals.seqTokVals items).length := by
  match items with
  | [] => simp
  | [v] =>
    rw [seqTokVals_singleton]
    exact emitTokVals_length_pos v
  | v :: w :: vs =>
    rw [seqTokVals_cons_cons]
    have h1 := emitTokVals_length_pos v
    have h2 := seqTokVals_length_ge (w :: vs)
    simp only [List.length_append, List.length_cons] at h2 ⊢
    omega

/-- Pair count is bounded by the body-run length. -/
lemma mapTokVals_length_ge (pairs : List (YamlValue × YamlValue)) :
    pairs.length ≤ (emitTokVals.mapTokVals pairs).length := by
  match pairs with
  | [] => simp
  | [(k, v)] =>
    rw [mapTokVals_singleton]
    simp
  | (k, v) :: p :: rest =>
    rw [mapTokVals_cons_cons]
    have h2 := mapTokVals_length_ge (p :: rest)
    simp only [List.length_append, List.length_cons] at h2 ⊢
    omega

mutual

/-- Every token an emission produces is flow-clean. -/
lemma emitTokVals_flowClean (v : YamlValue) :
    ∀ t ∈ emitTokVals v, FlowCleanTok t = true := by
  match v with
  | .scalar s => intro t ht; simp [emitTokVals] at ht; simp [ht, FlowCleanTok]
  | .alias name => intro t ht; simp [emitTokVals] at ht; simp [ht, FlowCleanTok]
  | .sequence _ items _ _ =>
    intro t ht
    simp only [emitTokVals, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | ht | rfl
    · rfl
    · exact seqTokVals_flowClean items.toList t ht
    · rfl
  | .mapping _ pairs _ _ =>
    intro t ht
    simp only [emitTokVals, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | ht | rfl
    · rfl
    · exact mapTokVals_flowClean pairs.toList t ht
    · rfl

lemma seqTokVals_flowClean (l : List YamlValue) :
    ∀ t ∈ emitTokVals.seqTokVals l, FlowCleanTok t = true := by
  match l with
  | [] => intro t ht; simp at ht
  | [v] => exact fun t ht => emitTokVals_flowClean v t ht
  | v :: w :: vs =>
    intro t ht
    rw [seqTokVals_cons_cons] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact emitTokVals_flowClean v t ht
    · rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact seqTokVals_flowClean (w :: vs) t ht

lemma mapTokVals_flowClean (l : List (YamlValue × YamlValue)) :
    ∀ t ∈ emitTokVals.mapTokVals l, FlowCleanTok t = true := by
  match l with
  | [] => intro t ht; simp at ht
  | [(k, v)] =>
    intro t ht
    rw [mapTokVals_singleton] at ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · rcases List.mem_append.mp ht with ht | ht
      · exact emitTokVals_flowClean k t ht
      · rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · exact emitTokVals_flowClean v t ht
  | (k, v) :: p :: rest =>
    intro t ht
    rw [mapTokVals_cons_cons] at ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · rcases List.mem_append.mp ht with ht | ht
        · exact emitTokVals_flowClean k t ht
        · rcases List.mem_cons.mp ht with rfl | ht
          · rfl
          · exact emitTokVals_flowClean v t ht
    · rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact mapTokVals_flowClean (p :: rest) t ht

end

end L4YAML.Proofs.EmitterScannability
