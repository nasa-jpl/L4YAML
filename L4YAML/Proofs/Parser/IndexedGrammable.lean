/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Spec.Grammar
public import L4YAML.Parser.Composition
public import L4YAML.Parser.TokenParserIx
public import L4YAML.Proofs.Composition
public import L4YAML.Proofs.Parser.ParserSoundness
public import L4YAML.Proofs.Parser.ParserGrammableBase
public import L4YAML.Proofs.Parser.ParserScannableBase
public import L4YAML.Proofs.Parser.IndexedNodeProofs
public import L4YAML.Proofs.Parser.IndexedWellBehaved
public import L4YAML.Proofs.Parser.IndexedWfa
public import L4YAML.Proofs.Parser.IndexedComposition
public import L4YAML.Proofs.Scanner.IndexedScannerCorrectness

@[expose] public section Blanket

/-! # `IndexedGrammable` — Phase 3 Step 6d.3 indexed grammability

## Role

Indexed twin of `L4YAML/Proofs/Parser/ParserGrammable.lean`: the
composition layer that discharges the `h_grammable` obligation by
chaining the indexed scannability (`parseStreamIx_output_scannable`),
alias-resolution, and well-formed-anchors substrates.

Legacy `ParserAnchorProofs` is folded into this file: the indexed
twin needs only the top-level `parseStreamIx_output_aliases_resolve`,
which is short enough to inline here rather than spawn a separate
`IndexedAnchorProofs.lean`.

## Phase 3 Step 6f cutover

At cutover, this file is renamed to `Proofs/Parser/ParserGrammable.lean`
(overwriting the legacy file) and the namespace
`L4YAML.Proofs.Indexed.Grammable` reverts to
`L4YAML.Proofs.ParserGrammable`.

# Phase C: Discharge `h_grammable` (IndexedGrammable)

This file combines the component proofs to produce the final
`parseStreamIx_output_grammable` theorem (the indexed twin of
`parseStream_output_grammable`).

**Component files:**
- `ParserGrammableBase`: Composition layer (§1–§4) — reused as-is
- `IndexedWellBehaved`: Parser output is `Scannable` (§5, C2 indexed)
- `IndexedWfa`: WellFormedAnchors preservation (C2c indexed)
- `IndexedNodeProofs`: `parseNode` produces `AllAliasesResolve` (C2b indexed)

## §6  Final Theorem (C3)

Combines C1 (compose_grammable / compose_scannable from base) and the indexed
C2 substrate to discharge `h_grammable` on the indexed `parseStreamIx`
pipeline.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.Grammable

open L4YAML
open L4YAML.Grammar
open L4YAML.Indexed
open L4YAML.TokenParser.Indexed
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.Composition
open L4YAML.Proofs.Indexed.WellBehaved
open L4YAML.Proofs.Indexed.NodeProofs
open L4YAML.Proofs.Indexed.WfaProofs
open L4YAML.Proofs.Indexed.Composition
open L4YAML.Proofs.Indexed.ScannerCorrectness
open L4YAML.Scanner.Indexed.ScannerStateIx

variable {input : String}

/-! ## §C2b  AllAliasesResolve lifting — Indexed

Lifts `parseNode_aliases_declared'` (parseNode-level, from
`IndexedNodeProofs`) up through `parseDocument` and `parseStreamLoop`
to obtain `parseStreamIx_output_aliases_resolve`.

The per-node statement is §7.1's — every alias names an anchor that has
*occurred* — because that is the reading that holds of a single node; the
resolution reading is recovered here, at the document boundary, where every
anchor the document declared has been finalized.  `DeclarationsBound` is that
boundary condition and `AllAliasesResolve.of_declared` the step.  See
`ParserAnchorProofs` for the argument in full.

Legacy structure: see `ParserAnchorProofs.lean` §`parseDocument_aliases_resolve`,
`parseStreamLoop_aliases_resolve`, `parseStream_output_aliases_resolve`.
The indexed version is a 1:1 transfer with `parseStream` →
`parseStreamIx`, `Array (Positioned YamlToken)` →
`Indexed.TokenStream input`, and `parseStreamLoop` references repointed
at the indexed variant. -/

/-- The document-entry condition: every name that has OCCURRED is already
    BOUND.  False inside a node (row 20), true wherever a document starts. -/
def DeclarationsBound (ps : ParseStateIx input) : Prop :=
  ∀ nm, nm ∈ ps.declaredAnchors → AnchorBound ps.anchors nm

lemma DeclarationsBound.of_empty {ps : ParseStateIx input}
    (h : ps.declaredAnchors = #[]) : DeclarationsBound ps := by
  intro nm hm; rw [h] at hm; simp at hm

lemma DeclarationsBound.of_registers {ps ps' : ParseStateIx input}
    (h_a : ps'.anchors = ps.anchors) (h_d : ps'.declaredAnchors = ps.declaredAnchors)
    (h : DeclarationsBound ps) : DeclarationsBound ps' := by
  intro nm hm; rw [h_d] at hm; rw [h_a]; exact h nm hm

/-- **Capstone 3.5 (indexed), the §7.1 reading**: every alias node in
    `parseNode`'s output names an anchor that has previously occurred. -/
lemma parseNode_aliases_declared_ix
    (ps : ParseStateIx input) (fuel : Nat) (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseNode ps fuel = .ok (val, ps')) :
    AllAliasesDeclared val ps'.declaredAnchors :=
  parseNode_aliases_declared' ps fuel val ps' h_ok

/-- The step to the resolution reading for one `parseNode` call. -/
lemma parseNode_aliases_resolve_ix
    (ps : ParseStateIx input) (fuel : Nat) (val : YamlValue) (ps' : ParseStateIx input)
    (h_decl : DeclarationsBound ps)
    (h_ok : parseNode ps fuel = .ok (val, ps')) :
    AllAliasesResolve val ps'.anchors := by
  have h_ag := parseNode_ag_all fuel ps fuel val ps' Nat.le.refl h_ok
  refine AllAliasesResolve.of_declared (fun nm hnm => ?_)
    (parseNode_aliases_declared_ix ps fuel val ps' h_ok)
  rcases h_ag.declsBound nm hnm with h_old | h_bound
  · exact AnchorBound.mono h_ag.anchorsGrow (h_decl nm h_old)
  · exact h_bound

-- parseDocument-level lift.
lemma parseDocument_aliases_resolve_ix
    (ps : ParseStateIx input) (doc : YamlDocument) (ps' : ParseStateIx input)
    (h_decl : DeclarationsBound ps)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    AllAliasesResolve doc.value doc.anchors := by
  unfold parseDocument at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Split on prepareDocumentState result
  split at h_ok
  · contradiction
  · rename_i v_prep h_prep
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
      split at h_ok
      · contradiction
      · rename_i v_node h_node
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨rfl, _⟩ := Prod.mk.inj h_ok
        obtain ⟨val_n, ps_n⟩ := v_node
        -- The directive prefix writes neither register.
        refine parseNode_aliases_resolve_ix _ _ _ _ (fun nm hnm => ?_) h_node
        rw [prepareDocumentState_decls_eq_ix ps v_prep.1 v_prep.2
          (by rw [← Prod.eta v_prep]; exact h_prep)] at hnm
        rw [prepareDocumentState_anchors_eq_ix ps v_prep.1 v_prep.2
          (by rw [← Prod.eta v_prep]; exact h_prep)]
        exact h_decl nm hnm

-- parseStreamLoop-level lift (induction on fuel).
lemma parseStreamLoop_aliases_resolve_ix
    (ps : ParseStateIx input) (docs : Array YamlDocument)
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
    · -- documentEnd (bare `...` suffix, C1) → skip it, recurse with same accumulator
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
            · exact parseDocument_aliases_resolve_ix _ _ _ h_decl h_pd
          split at h_ok
          · simp at h_ok  -- no progress → error, contradiction
          · -- §3.2.2.2: anchor scope is per document, and the reset restores
            -- the agreement between the registers for the next one.
            refine ih _ _ _ ?_ h_acc' h_ok
            exact DeclarationsBound.of_empty (by simp)

-- parseStreamIx-level lift (the C2b indexed final).
lemma parseStreamIx_output_aliases_resolve
    (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (h_parse : parseStreamIx tokens = .ok docs) :
    ∀ doc ∈ docs.toList, AllAliasesResolve doc.value doc.anchors := by
  intro doc hdoc
  unfold parseStreamIx at h_parse
  simp only [bind, Except.bind] at h_parse
  split at h_parse
  · contradiction
  · rename_i ps_start h_expect
    refine parseStreamLoop_aliases_resolve_ix ps_start #[] .initial tokens.size docs
      ?_ (by intro d hd; simp at hd) h_parse doc hdoc
    -- A stream's initial state has declared nothing.
    refine DeclarationsBound.of_empty ?_
    unfold ParseStateIx.expect at h_expect
    split at h_expect
    · split at h_expect
      · simp only [Except.ok.injEq] at h_expect; subst h_expect; rfl
      · simp at h_expect
    · simp at h_expect

/-! ## §6  Final Theorem (C3 indexed) -/

/-- **C3 (indexed)**: Every document produced by `parseStreamIx` (with
    scanner-quality token-stream hypotheses) is `Grammable` after
    composition.

    This theorem eliminates the `h_grammable` hypothesis from
    `parseStreamIx_respects_grammar` in `IndexedCorrectness.lean`.

    **Architecture**: Chains `parseStream_output_scannable_ix`
    (IndexedWellBehaved) into `compose_grammable` (ParserGrammableBase).

    **Precondition on the input**: `AliasFree`.  An alias with no preceding
    definition survives composition — §3.2.2.2 resolves against the most
    recent preceding event and a collection's anchor binds only after its
    items, so a node that has itself as a descendant via an alias (§3.2.1.3)
    keeps its `.alias`, which `Grammable` has no constructor for.  The
    hypothesis-free form is `parseStreamIx_output_scannable_composed`. -/
lemma parseStreamIx_output_grammable
    (tokens : Indexed.TokenStream input)
    (raw_docs : Array YamlDocument)
    (h_fpsv : FlowAwarePSVIx tokens)
    (h_matched : FlowBracketsMatchedIx tokens)
    (h_parse : parseStreamIx tokens = .ok raw_docs)
    (h_af : ∀ doc ∈ raw_docs.toList, AliasFree doc.value) :
    ∀ doc ∈ raw_docs.toList, Grammable doc.compose.value false := by
  intro doc hdoc
  have h_scannable :=
    parseStream_output_scannable_ix tokens raw_docs h_fpsv h_matched h_parse doc hdoc
  exact compose_grammable doc h_scannable (h_af doc hdoc)

/-- **Unconditional scannability of the composed value (indexed).**

    The `Scannable` twin of `parseStreamIx_output_grammable`, carrying no
    hypothesis on the input: `Scannable` admits the alias node that survives
    composition, so this is the form the unconditional capstone needs. -/
lemma parseStreamIx_output_scannable_composed
    (tokens : Indexed.TokenStream input)
    (raw_docs : Array YamlDocument)
    (h_fpsv : FlowAwarePSVIx tokens)
    (h_matched : FlowBracketsMatchedIx tokens)
    (h_parse : parseStreamIx tokens = .ok raw_docs) :
    ∀ doc ∈ raw_docs.toList, Scannable doc.compose.value false := by
  intro doc hdoc
  have h_scannable :=
    parseStream_output_scannable_ix tokens raw_docs h_fpsv h_matched h_parse doc hdoc
  exact compose_scannable doc h_scannable

/-- **Unconditional correctness (indexed, parseStreamIx-level)**: every
    document produced by `parseStreamIx` from scanner-quality tokens has
    a `ValidNode` witness whose stripped canonical form matches the
    composed value.

    Indexed twin of `parseYaml_produces_valid_nodes`, repointed at
    `parseStreamIx` (the full `parseYaml`-pipeline twin is deferred to
    the Step 6f cutover, where `parseYaml` is rebound to use the indexed
    pipeline). -/
lemma parseStreamIx_produces_valid_nodes
    (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (h_fpsv : FlowAwarePSVIx tokens)
    (h_matched : FlowBracketsMatchedIx tokens)
    (h_parse : parseStreamIx tokens = .ok docs) :
    ∀ doc ∈ docs.toList, ∃ node : ValidNode,
      stripAnnotations (toYamlValue node) = stripAnnotations doc.compose.value := by
  intro doc hdoc
  have h_g :=
    parseStreamIx_output_scannable_composed tokens docs h_fpsv h_matched h_parse doc hdoc
  exact ParserSoundness.scannableValue_has_witness doc.compose.value false h_g

/-- **Unconditional correctness (indexed, parseStreamIx-level, no
    hypotheses)**: given that `tokens` came from `scanFilteredIx`,
    every document produced by `parseStreamIx` has a `ValidNode`
    witness. The `FlowAwarePSVIx` / `FlowBracketsMatchedIx`
    hypotheses are discharged via
    `scanFilteredIx_FlowAwarePSVIx` /
    `scanFilteredIx_FlowBracketsMatchedIx`. -/
lemma parseStreamIx_produces_valid_nodes_unconditional
    {input : String} (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (h_scan : scanFilteredIx input = .ok tokens)
    (h_parse : parseStreamIx tokens = .ok docs) :
    ∀ doc ∈ docs.toList, ∃ node : ValidNode,
      stripAnnotations (toYamlValue node) = stripAnnotations doc.compose.value := by
  have h_fpsv := scanFilteredIx_FlowAwarePSVIx input tokens h_scan
  have h_matched := scanFilteredIx_FlowBracketsMatchedIx input tokens h_scan
  exact parseStreamIx_produces_valid_nodes tokens docs h_fpsv h_matched h_parse

/-- **Unconditional correctness (indexed, parseYamlIx-level)**: the
    full `parseYamlIx` pipeline (scan → parse → compose) produces
    documents whose values have `ValidNode` witnesses. Indexed twin
    of `parseYaml_produces_valid_nodes` in
    `Proofs/Parser/ParserGrammable.lean`. -/
lemma parseYamlIx_produces_valid_nodes
    (input : String) (docs : Array YamlDocument)
    (h : parseYamlIx input = .ok docs) :
    ∀ doc ∈ docs.toList, ∃ node : ValidNode,
      stripAnnotations (toYamlValue node) = stripAnnotations doc.value := by
  rw [parseYamlIx_ok_iff] at h
  obtain ⟨raw_docs, h_raw, h_eq⟩ := h
  obtain ⟨tokens, h_scan, h_parse⟩ := parseYamlRawIx_ok_decompose input raw_docs h_raw
  intro doc hdoc
  rw [h_eq, Array.toList_map] at hdoc
  obtain ⟨raw_doc, h_raw_mem, h_compose_eq⟩ := List.mem_map.mp hdoc
  subst h_compose_eq
  exact parseStreamIx_produces_valid_nodes_unconditional tokens raw_docs h_scan h_parse
    raw_doc h_raw_mem

/-- **Indexed twin** of legacy `parseYaml_implies_valid_token_stream`
    (`Proofs/EndToEndCorrectness.lean:302`): successful `parseYamlIx`
    implies the underlying *unfiltered* `scanIx` token stream satisfies
    `ValidTokenStreamPropIx`.

    Mirrors the legacy chain: decompose `parseYamlIx` → `scanFilteredIx`,
    unfold `scanFilteredIx` to recover the unfiltered `scanIx` witness,
    then apply `scanIx_valid_token_stream` (Step 6f.3b3.primitives.tractable
    composed theorem replacing the prior 6f.3b2.consume monolithic
    staging axiom — see Reflection 108). -/
lemma parseYamlIx_implies_valid_token_stream
    (input : String) (docs : Array YamlDocument)
    (h : parseYamlIx input = .ok docs) :
    ∃ (tokens : Indexed.TokenStream input),
      scanIx input = .ok tokens ∧
      ValidTokenStreamPropIx tokens := by
  rw [parseYamlIx_ok_iff] at h
  obtain ⟨raw_docs, h_raw, _⟩ := h
  obtain ⟨_, h_scanf, _⟩ := parseYamlRawIx_ok_decompose input raw_docs h_raw
  unfold scanFilteredIx at h_scanf
  split at h_scanf
  · rename_i all_tokens h_scan_raw
    exact ⟨all_tokens, h_scan_raw,
      scanIx_valid_token_stream all_tokens h_scan_raw⟩
  · contradiction

end L4YAML.Proofs.Indexed.Grammable

end Blanket
