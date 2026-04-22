import L4YAML.Spec.Grammar
import L4YAML.Parser.Composition
import L4YAML.Proofs.ScannerPlainScalarValid
import L4YAML.Proofs.ParserGrammableBase
import L4YAML.Proofs.ParserNodeProofs
import L4YAML.Proofs.ValueAlgebra
import L4YAML.Proofs.ParserWfaProofs

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace L4YAML.Proofs.ParserGrammable

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.Composition

/-- C2b: Every document's aliases resolve through its anchor map.

    ### Proof Architecture

    With the parser-level §7.1 validation check in `parseNode`, every
    `YamlValue.alias name` in the output tree was created only after
    confirming `ps.anchors.any (fun (n, _) => n == name) = true`.

    The proof chains three properties:

    1. **Bridge**: `Array.any ... = true` implies
       `(Array.findSome? ...).isSome` (matching `AllAliasesResolve.alias`).

    2. **Monotonicity**: `AllAliasesResolve val anchors` is preserved
       when `anchors` grows (since `findSome?` on a larger array still finds
       entries present in any prefix).

    3. **Parser invariant**: By structural induction on fuel, `parseNode`
       produces values satisfying `AllAliasesResolve` against the output
       state's `anchors` (which includes all anchors accumulated during parsing).

    The `parseStream_doc_from_parseDocument` decomposition lifts this to
    `parseStream`. -/

-- Bridge: `Array.any (fun (n, _) => n == name) = true` →
--         `(Array.findSome? (fun (n, _) => if n == name then some () else none)).isSome`
-- General bridge: if `any f` and `f x → (g x).isSome`, then `findSome? g .isSome`
theorem Array.any_true_findSome_isSome
    {α β : Type} (xs : Array α) (f : α → Bool) (g : α → Option β)
    (h_fg : ∀ x, f x = true → (g x).isSome = true)
    (h : xs.any f = true) :
    (xs.findSome? g).isSome = true := by
  rw [Array.findSome?_isSome_iff]
  rw [Array.any_eq_true] at h
  obtain ⟨i, hi, hp⟩ := h
  exact ⟨xs[i], Array.getElem_mem hi, h_fg _ hp⟩

-- Specialized bridge for the alias resolution check
theorem any_name_implies_findSome_isSome
    (anchors : Array (String × YamlValue)) (name : String)
    (h : anchors.any (fun (n, _) => n == name) = true) :
    (anchors.findSome? (fun (n, _) => if n == name then some () else none)).isSome = true :=
  Array.any_true_findSome_isSome anchors _ _ (fun ⟨n, _⟩ hp => by simp [hp]) h

-- Monotonicity: AllAliasesResolve is preserved under anchor growth (push).
theorem AllAliasesResolve.push (val : YamlValue)
    (anchors : Array (String × YamlValue)) (entry : String × YamlValue)
    (h : AllAliasesResolve val anchors) :
    AllAliasesResolve val (anchors.push entry) := by
  induction h with
  | scalar s _ => exact .scalar s _
  | alias name anchors h_find =>
    apply AllAliasesResolve.alias
    rw [Array.findSome?_isSome_iff] at h_find ⊢
    obtain ⟨x, hx, hfx⟩ := h_find
    exact ⟨x, Array.mem_push.mpr (.inl hx), hfx⟩
  | sequence style items tag anchor anchors h_items ih_items =>
    exact .sequence style items tag anchor _ (fun i => ih_items i)
  | mapping style pairs tag anchor anchors hk hv ihk ihv =>
    exact .mapping style pairs tag anchor _ (fun i => ihk i) (fun i => ihv i)

-- Monotonicity generalized: prefix ⊆ suffix via repeated push
theorem AllAliasesResolve.mono (val : YamlValue)
    (anchors1 anchors2 : Array (String × YamlValue))
    (h_prefix : ∀ i : Fin anchors1.size, ∃ j : Fin anchors2.size,
        anchors2[j] = anchors1[i])
    (h : AllAliasesResolve val anchors1) :
    AllAliasesResolve val anchors2 := by
  induction h with
  | scalar s _ => exact .scalar s _
  | alias name anchors h_find =>
    apply AllAliasesResolve.alias
    rw [Array.findSome?_isSome_iff] at h_find ⊢
    obtain ⟨x, hx, hfx⟩ := h_find
    rw [Array.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj⟩ := h_prefix ⟨i, hi⟩
    exact ⟨anchors2[j], Array.getElem_mem j.isLt, hj ▸ hfx⟩
  | sequence style items tag anchor anchors h_items ih_items =>
    exact .sequence style items tag anchor _ (fun i => ih_items i h_prefix)
  | mapping style pairs tag anchor anchors hk hv ihk ihv =>
    exact .mapping style pairs tag anchor _
      (fun i => ihk i h_prefix) (fun i => ihv i h_prefix)

-- Anchors only grow within parseNode: ps'.anchors is a suffix extension of ps.anchors.
-- (This is the key monotonicity property of the parser.)
theorem parseNode_anchors_grow (ps : ParseState) (fuel : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNode ps fuel = .ok (val, ps')) :
    ∀ i : Fin ps.anchors.size, ∃ j : Fin ps'.anchors.size,
        ps'.anchors[j] = ps.anchors[i] :=
  ParserNodeProofs.parseNode_anchors_grow ps fuel val ps' h_ok

-- Core lemma: parseNode produces AllAliasesResolve-satisfying output.
theorem parseNode_aliases_resolve (ps : ParseState) (fuel : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNode ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors :=
  ParserNodeProofs.parseNode_aliases_resolve' ps fuel val ps' h_ok

-- Lift to parseDocument level
theorem parseDocument_aliases_resolve (ps : ParseState)
    (doc : YamlDocument) (ps' : ParseState)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    AllAliasesResolve doc.value doc.anchors := by
  unfold parseDocument at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Split on prepareDocumentState result
  split at h_ok
  · contradiction
  · rename_i v_prep h_prep
    -- The rest: let fuel := ...; let (val, ps) ← match peek? ...; .ok (doc, ps)
    -- After bind simplification, split on the match ps.peek?
    split at h_ok
    · -- documentEnd → empty doc
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, _⟩ := Prod.mk.inj h_ok
      exact .scalar _ _
    · -- streamEnd → empty doc
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, _⟩ := Prod.mk.inj h_ok
      exact .scalar _ _
    · -- none → empty doc
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨rfl, _⟩ := Prod.mk.inj h_ok
      exact .scalar _ _
    · -- non-empty: parseNode was called
      -- Split on parseNode result
      split at h_ok
      · contradiction
      · rename_i v_node h_node
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨rfl, _⟩ := Prod.mk.inj h_ok
        obtain ⟨val_n, ps_n⟩ := v_node
        exact parseNode_aliases_resolve _ _ _ _ h_node

-- Loop-level lemma: parseStreamLoop preserves AllAliasesResolve for accumulated docs
theorem parseStreamLoop_aliases_resolve
    (ps : ParseState) (docs : Array YamlDocument)
    (streamState : StreamState) (fuel : Nat)
    (result : Array YamlDocument)
    (h_acc : ∀ doc ∈ docs.toList, AllAliasesResolve doc.value doc.anchors)
    (h_ok : parseStreamLoop ps docs streamState fuel = .ok result) :
    ∀ doc ∈ result.toList, AllAliasesResolve doc.value doc.anchors := by
  induction fuel generalizing ps docs streamState with
  | zero =>
    simp only [parseStreamLoop] at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
  | succ fuel ih =>
    unfold parseStreamLoop at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
    · -- some tok → validation + parseDocument + recurse
      split at h_ok
      · simp at h_ok
      · dsimp only [] at h_ok
        generalize h_pd : parseDocument ps = pd_result at h_ok
        cases pd_result with
        | error e => simp at h_ok
        | ok val =>
          obtain ⟨doc_new, ps'⟩ := val
          dsimp only [] at h_ok
          have h_acc' : ∀ doc ∈ (docs.push doc_new).toList,
              AllAliasesResolve doc.value doc.anchors := by
            intro d hd
            rw [Array.toList_push] at hd
            simp only [List.mem_append, List.mem_singleton] at hd
            rcases hd with hd_old | rfl
            · exact h_acc d hd_old
            · exact parseDocument_aliases_resolve _ _ _ h_pd
          split at h_ok
          · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc'
          · exact ih _ _ _ h_acc' h_ok

theorem parseStream_output_aliases_resolve
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, AllAliasesResolve doc.value doc.anchors := by
  -- Decompose: each doc came from a parseDocument call
  intro doc hdoc
  -- We need FlowAwarePSV and FlowBracketsMatched for the decomposition lemma,
  -- but AllAliasesResolve doesn't actually depend on these scanner properties.
  -- Use the direct approach: unfold parseStream and trace through parseStreamLoop.
  unfold parseStream at h_parse
  simp only [bind, Except.bind] at h_parse
  split at h_parse
  · contradiction
  · rename_i ps_start h_expect
    -- Now trace through parseStreamLoop
    exact parseStreamLoop_aliases_resolve ps_start #[] .initial tokens.size docs
      (by intro d hd; simp at hd) h_parse doc hdoc

-- C2c: Anchor values in parser output are well-formed.
-- parseStream_output_anchors_wellformed is now in ParserWfaProofs.lean
-- (with updated signature: FlowAwarePSV + FlowBracketsMatched)

end L4YAML.Proofs.ParserGrammable
