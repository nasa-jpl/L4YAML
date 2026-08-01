/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Token.Token

/-! # Token Discriminator Algebra  (Algebra Item 17)

`YamlToken.isVirtual`, `YamlToken.canStartNode`, and
`YamlToken.isFlowIndicator` (in `Token/Token.lean:241–270`) are the
three boolean classifiers the scanner and parser use to dispatch on
token kind. This file names the equational laws they satisfy:

- Per-constructor evaluation: every constructor reduces each
  discriminator to a concrete boolean via `rfl`, so case-split
  reasoning collapses to `simp`.
- Cross-discriminator exclusion: flow indicators are never virtual.
- Non-emptiness witnesses: each discriminator has at least one
  constructor evaluating to `true`, so `decide` and exhaustiveness
  tactics have an inhabitant to work with.

## Phase-1 inventory caveat — these are *classifiers*, not a *partition*

The Phase 1 wording said "partition tokens into disjoint classes".
After implementation, the three classifiers are *not* mutually
disjoint:

- `isVirtual ∩ canStartNode = {.blockSequenceStart, .blockMappingStart}`
- `canStartNode ∩ isFlowIndicator = {.flowSequenceStart, .flowMappingStart}`
- `isVirtual ∩ isFlowIndicator = ∅` (proved below as `not_virtual_of_flow`)

So they are *classifiers* (decidable predicates) that overlap in
controlled places, not a partition. The disjointness that actually
holds — flow vs. virtual — is the only one this file proves; the
others are not claims but observed overlaps documented in the
constructor evaluation simp set. This refines the Phase 1 wording
(parallel to the Item 7 refinement: "ordered monoid on
componentwise position", not on `ScannerState.advance`).

## Closure (Guardrail 2)

Every theorem here is either a per-constructor `rfl` for one of
the three discriminators or a Bool-level case-split over those
`rfl` facts. No new algebraic content beyond Item 17.

## Provenance

New content (no migration). The blueprint estimate of ~100 LOC
holds.
-/

set_option autoImplicit false

namespace L4YAML.Algebra.Token

open L4YAML

/-! ## Item 17(a) — `isVirtual` per-constructor evaluation

    Each constructor either is a virtual token (no input bytes
    consumed: stream/document/block-structure scaffolding) or is a
    concrete token (consumes characters from the input). The simp
    set below lets `simp [...]` discharge any case-split on
    `YamlToken.isVirtual t` over an applied constructor. -/

namespace YamlToken

@[simp] lemma isVirtual_streamStart :
    (YamlToken.streamStart).isVirtual = true := rfl

@[simp] lemma isVirtual_streamEnd :
    (YamlToken.streamEnd).isVirtual = true := rfl

@[simp] lemma isVirtual_placeholder :
    (YamlToken.placeholder).isVirtual = true := rfl

@[simp] lemma isVirtual_blockSequenceStart :
    (YamlToken.blockSequenceStart).isVirtual = true := rfl

@[simp] lemma isVirtual_blockMappingStart :
    (YamlToken.blockMappingStart).isVirtual = true := rfl

@[simp] lemma isVirtual_blockEnd :
    (YamlToken.blockEnd).isVirtual = true := rfl

@[simp] lemma isVirtual_documentStart :
    (YamlToken.documentStart).isVirtual = false := rfl

@[simp] lemma isVirtual_documentEnd :
    (YamlToken.documentEnd).isVirtual = false := rfl

@[simp] lemma isVirtual_blockEntry :
    (YamlToken.blockEntry).isVirtual = false := rfl

@[simp] lemma isVirtual_key :
    (YamlToken.key).isVirtual = false := rfl

@[simp] lemma isVirtual_value :
    (YamlToken.value).isVirtual = false := rfl

@[simp] lemma isVirtual_flowSequenceStart :
    (YamlToken.flowSequenceStart).isVirtual = false := rfl

@[simp] lemma isVirtual_flowSequenceEnd :
    (YamlToken.flowSequenceEnd).isVirtual = false := rfl

@[simp] lemma isVirtual_flowMappingStart :
    (YamlToken.flowMappingStart).isVirtual = false := rfl

@[simp] lemma isVirtual_flowMappingEnd :
    (YamlToken.flowMappingEnd).isVirtual = false := rfl

@[simp] lemma isVirtual_flowEntry :
    (YamlToken.flowEntry).isVirtual = false := rfl

@[simp] lemma isVirtual_scalar (v : String) (s : ScalarStyle) :
    (YamlToken.scalar v s).isVirtual = false := rfl

@[simp] lemma isVirtual_alias (n : String) :
    (YamlToken.alias n).isVirtual = false := rfl

@[simp] lemma isVirtual_anchor (n : String) :
    (YamlToken.anchor n).isVirtual = false := rfl

@[simp] lemma isVirtual_tag (h s : String) :
    (YamlToken.tag h s).isVirtual = false := rfl

@[simp] lemma isVirtual_versionDirective (M m : Nat) :
    (YamlToken.versionDirective M m).isVirtual = false := rfl

@[simp] lemma isVirtual_tagDirective (h p : String) :
    (YamlToken.tagDirective h p).isVirtual = false := rfl

@[simp] lemma isVirtual_comment (t : String) :
    (YamlToken.comment t).isVirtual = false := rfl

/-! ## Item 17(b) — `canStartNode` per-constructor evaluation -/

@[simp] lemma canStartNode_scalar (v : String) (s : ScalarStyle) :
    (YamlToken.scalar v s).canStartNode = true := rfl

@[simp] lemma canStartNode_alias (n : String) :
    (YamlToken.alias n).canStartNode = true := rfl

@[simp] lemma canStartNode_anchor (n : String) :
    (YamlToken.anchor n).canStartNode = true := rfl

@[simp] lemma canStartNode_tag (h s : String) :
    (YamlToken.tag h s).canStartNode = true := rfl

@[simp] lemma canStartNode_flowSequenceStart :
    (YamlToken.flowSequenceStart).canStartNode = true := rfl

@[simp] lemma canStartNode_flowMappingStart :
    (YamlToken.flowMappingStart).canStartNode = true := rfl

@[simp] lemma canStartNode_blockSequenceStart :
    (YamlToken.blockSequenceStart).canStartNode = true := rfl

@[simp] lemma canStartNode_blockMappingStart :
    (YamlToken.blockMappingStart).canStartNode = true := rfl

@[simp] lemma canStartNode_streamStart :
    (YamlToken.streamStart).canStartNode = false := rfl

@[simp] lemma canStartNode_streamEnd :
    (YamlToken.streamEnd).canStartNode = false := rfl

@[simp] lemma canStartNode_placeholder :
    (YamlToken.placeholder).canStartNode = false := rfl

@[simp] lemma canStartNode_blockEnd :
    (YamlToken.blockEnd).canStartNode = false := rfl

@[simp] lemma canStartNode_documentStart :
    (YamlToken.documentStart).canStartNode = false := rfl

@[simp] lemma canStartNode_documentEnd :
    (YamlToken.documentEnd).canStartNode = false := rfl

@[simp] lemma canStartNode_blockEntry :
    (YamlToken.blockEntry).canStartNode = false := rfl

@[simp] lemma canStartNode_key :
    (YamlToken.key).canStartNode = false := rfl

@[simp] lemma canStartNode_value :
    (YamlToken.value).canStartNode = false := rfl

@[simp] lemma canStartNode_flowSequenceEnd :
    (YamlToken.flowSequenceEnd).canStartNode = false := rfl

@[simp] lemma canStartNode_flowMappingEnd :
    (YamlToken.flowMappingEnd).canStartNode = false := rfl

@[simp] lemma canStartNode_flowEntry :
    (YamlToken.flowEntry).canStartNode = false := rfl

@[simp] lemma canStartNode_versionDirective (M m : Nat) :
    (YamlToken.versionDirective M m).canStartNode = false := rfl

@[simp] lemma canStartNode_tagDirective (h p : String) :
    (YamlToken.tagDirective h p).canStartNode = false := rfl

@[simp] lemma canStartNode_comment (t : String) :
    (YamlToken.comment t).canStartNode = false := rfl

/-! ## Item 17(c) — `isFlowIndicator` per-constructor evaluation -/

@[simp] lemma isFlowIndicator_flowSequenceStart :
    (YamlToken.flowSequenceStart).isFlowIndicator = true := rfl

@[simp] lemma isFlowIndicator_flowSequenceEnd :
    (YamlToken.flowSequenceEnd).isFlowIndicator = true := rfl

@[simp] lemma isFlowIndicator_flowMappingStart :
    (YamlToken.flowMappingStart).isFlowIndicator = true := rfl

@[simp] lemma isFlowIndicator_flowMappingEnd :
    (YamlToken.flowMappingEnd).isFlowIndicator = true := rfl

@[simp] lemma isFlowIndicator_flowEntry :
    (YamlToken.flowEntry).isFlowIndicator = true := rfl

@[simp] lemma isFlowIndicator_streamStart :
    (YamlToken.streamStart).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_streamEnd :
    (YamlToken.streamEnd).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_placeholder :
    (YamlToken.placeholder).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_blockSequenceStart :
    (YamlToken.blockSequenceStart).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_blockMappingStart :
    (YamlToken.blockMappingStart).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_blockEnd :
    (YamlToken.blockEnd).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_documentStart :
    (YamlToken.documentStart).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_documentEnd :
    (YamlToken.documentEnd).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_blockEntry :
    (YamlToken.blockEntry).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_key :
    (YamlToken.key).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_value :
    (YamlToken.value).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_scalar (v : String) (s : ScalarStyle) :
    (YamlToken.scalar v s).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_alias (n : String) :
    (YamlToken.alias n).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_anchor (n : String) :
    (YamlToken.anchor n).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_tag (h s : String) :
    (YamlToken.tag h s).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_versionDirective (M m : Nat) :
    (YamlToken.versionDirective M m).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_tagDirective (h p : String) :
    (YamlToken.tagDirective h p).isFlowIndicator = false := rfl

@[simp] lemma isFlowIndicator_comment (t : String) :
    (YamlToken.comment t).isFlowIndicator = false := rfl

/-! ## Item 17(d) — cross-discriminator exclusion

    The single class disjointness that holds across all constructors:
    flow indicators are never virtual. Verified by case analysis on
    `t`; the simp set above discharges every branch by `rfl`. -/

lemma not_virtual_of_flow (t : YamlToken) :
    t.isFlowIndicator = true → t.isVirtual = false := by
  cases t <;> simp

lemma not_flow_of_virtual (t : YamlToken) :
    t.isVirtual = true → t.isFlowIndicator = false := by
  cases t <;> simp

/-! ## Item 17(e) — non-emptiness witnesses

    Each discriminator has at least one constructor returning
    `true`. Useful as a sanity check (no classifier is constantly
    false) and as a starting point for exhaustiveness-style
    arguments that need an inhabited witness. -/

lemma exists_virtual : ∃ t : YamlToken, t.isVirtual = true :=
  ⟨YamlToken.streamStart, rfl⟩

lemma exists_canStartNode : ∃ t : YamlToken, t.canStartNode = true :=
  ⟨YamlToken.scalar "" ScalarStyle.plain, rfl⟩

lemma exists_isFlowIndicator : ∃ t : YamlToken, t.isFlowIndicator = true :=
  ⟨YamlToken.flowEntry, rfl⟩

end YamlToken

end L4YAML.Algebra.Token
