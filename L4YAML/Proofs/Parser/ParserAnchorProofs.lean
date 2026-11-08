/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Spec.Grammar
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Production.ScannerPlainScalarValid
public import L4YAML.Proofs.Parser.ParserGrammableBase
public import L4YAML.Proofs.Parser.ParserNodeProofs
public import L4YAML.Algebra.Value
public import L4YAML.Proofs.Parser.ParserWfaProofs

@[expose] public section Blanket

/-!
# Anchor/alias resolution lifted to documents and streams

Public wrappers and doc/stream-level lifts of the `ParserNodeProofs`
scaffolding: capstones 3.5 `parseNode_aliases_declared`, 3.6
`parseDocument_aliases_resolve`, and 3.7
`parseStream_output_aliases_resolve`.

## The obligation has two readings and this file carries both

§7.1 forbids an alias whose anchor has not previously **occurred**; §3.2.2.2
says what an alias resolves **to**.  Per node only the first is available: an
anchor occurs at the `&` property, which is the node's start event, while its
entry in the resolution table stores a *value* and so cannot exist until the
node it decorates is complete.  `&x [*x]` is exactly that gap — a legal
document whose inner alias names an anchor that has occurred and is not yet
resolvable — so capstone 3.5 is indexed on the DECLARATION set
(`AllAliasesDeclared`).

At a document boundary the two readings coincide, because every anchor the
document declared has been finalized by the time its node returns.  Capstones
3.6 and 3.7 are therefore stated on the resolution table, unchanged.
`AllAliasesResolve.of_declared` is the step between the readings and
`AG.declsBound` is what discharges its premise; `DeclarationsBound` is the
document-entry condition, which the stream's initial state and
`parseStreamLoop`'s per-document reset both supply.
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace L4YAML.Proofs.ParserAnchorProofs

open L4YAML
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ParserWfaProofs
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.Composition

/-- The document-entry condition the resolution reading needs: every name that
    has OCCURRED is already BOUND.

    False inside a node, which is the whole of row 20, and true wherever a
    document starts — the stream's initial state has both registers empty and
    `parseStreamLoop` clears both after each document (§3.2.2.2: anchor scope is
    per document). -/
def DeclarationsBound (ps : ParseState) : Prop :=
  ∀ nm, nm ∈ ps.declaredAnchors → AnchorBound ps.anchors nm

/-- A state that has declared nothing satisfies it vacuously. -/
lemma DeclarationsBound.of_empty {ps : ParseState}
    (h : ps.declaredAnchors = #[]) : DeclarationsBound ps := by
  intro nm hm; rw [h] at hm; simp at hm

/-- …and the condition reads only the two registers, so it travels with them. -/
lemma DeclarationsBound.of_registers {ps ps' : ParseState}
    (h_a : ps'.anchors = ps.anchors) (h_d : ps'.declaredAnchors = ps.declaredAnchors)
    (h : DeclarationsBound ps) : DeclarationsBound ps' := by
  intro nm hm; rw [h_d] at hm; rw [h_a]; exact h nm hm

-- Anchors only grow within parseNode: ps'.anchors is a suffix extension of ps.anchors.
-- (This is the key monotonicity property of the parser.)
lemma parseNode_anchors_grow (ps : ParseState) (fuel : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNode ps fuel = .ok (val, ps')) :
    ∀ i : Fin ps.anchors.size, ∃ j : Fin ps'.anchors.size,
        ps'.anchors[j] = ps.anchors[i] :=
  L4YAML.Proofs.ParserNodeProofs.parseNode_anchors_grow ps fuel val ps' h_ok

/-- **Capstone 3.5, the §7.1 reading**: every alias node in `parseNode`'s
    output names an anchor that has previously occurred.

    Unconditional, and the strongest statement that is true of a single node:
    the resolution reading fails here for `&x [*x]`, whose inner alias is
    admitted while the collection's own value is still being built. -/
lemma parseNode_aliases_declared (ps : ParseState) (fuel : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNode ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors :=
  L4YAML.Proofs.ParserNodeProofs.parseNode_aliases_declared' ps fuel val ps' h_ok

/-- The step from 3.5 to the resolution reading, for one `parseNode` call: a
    call that starts where the registers agree ends with every name it admitted
    as an alias bound in its own table. -/
lemma parseNode_aliases_resolve (ps : ParseState) (fuel : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_decl : DeclarationsBound ps)
    (h_ok : parseNode ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  have h_ag := L4YAML.Proofs.ParserNodeProofs.parseNode_ag_all fuel ps fuel val ps'
    Nat.le.refl h_ok
  refine AllAliasesResolve.of_declared (fun nm hnm => ?_)
    (parseNode_aliases_declared ps fuel val ps' h_ok)
  rcases h_ag.declsBound nm hnm with h_old | h_bound
  · exact AnchorBound.mono h_ag.anchorsGrow (h_decl nm h_old)
  · exact h_bound

/-- **Capstone 3.6**: every alias in a document's output resolves through that
    document's anchor table.  The resolution reading, at the boundary where it
    is true. -/
lemma parseDocument_aliases_resolve (ps : ParseState)
    (doc : YamlDocument) (ps' : ParseState)
    (h_decl : DeclarationsBound ps)
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
        -- The directive prefix writes neither register, so the document's
        -- entry state inherits the stream's agreement between them.
        refine parseNode_aliases_resolve _ _ _ _ (fun nm hnm => ?_) h_node
        rw [L4YAML.Proofs.ParserWfaProofs.prepareDocumentState_decls_eq
          ps v_prep.1 v_prep.2 (by rw [← Prod.eta v_prep]; exact h_prep)] at hnm
        rw [L4YAML.Proofs.ParserWfaProofs.prepareDocumentState_anchors_eq
          ps v_prep.1 v_prep.2 (by rw [← Prod.eta v_prep]; exact h_prep)]
        exact h_decl nm hnm

-- Loop-level lemma: parseStreamLoop preserves AllAliasesResolve for accumulated docs
lemma parseStreamLoop_aliases_resolve
    (ps : ParseState) (docs : Array YamlDocument)
    (streamState : StreamState) (fuel : Nat)
    (result : Array YamlDocument)
    (h_decl : DeclarationsBound ps)
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
    · -- documentEnd (bare `...` suffix) → skip it, recurse with same accumulator
      refine ih _ _ _ ?_ h_acc h_ok
      exact h_decl.of_registers (by split <;> (try split) <;> rfl)
        (by split <;> (try split) <;> rfl)
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
            · exact parseDocument_aliases_resolve _ _ _ h_decl h_pd
          split at h_ok
          · simp at h_ok  -- no progress → error, contradiction
          · -- §3.2.2.2: anchor scope is per document, so the reset restores
            -- the agreement between the registers for the next one.
            refine ih _ _ _ ?_ h_acc' h_ok
            exact DeclarationsBound.of_empty (by simp)

lemma parseStream_output_aliases_resolve
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
    refine parseStreamLoop_aliases_resolve ps_start #[] .initial tokens.size docs
      ?_ (by intro d hd; simp at hd) h_parse doc hdoc
    -- A stream's initial state has declared nothing, so the two readings agree
    -- at the first document too.
    refine DeclarationsBound.of_empty ?_
    unfold ParseState.expect at h_expect
    split at h_expect
    · split at h_expect
      · simp only [Except.ok.injEq] at h_expect; subst h_expect; rfl
      · simp at h_expect
    · simp at h_expect

-- C2c: Anchor values in parser output are well-formed.
-- parseStream_output_anchors_wellformed is now in ParserWfaProofs.lean
-- (with updated signature: FlowAwarePSV + FlowBracketsMatched)

end L4YAML.Proofs.ParserAnchorProofs

end Blanket
