module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Serialization.TraceOf.UniqueFlow
public import L4YAML.Proofs.Foundation.SurfaceSpanSupply
public meta import L4YAML.Proofs.Serialization.TraceOf.Document
public meta import L4YAML.Proofs.Serialization.TraceOf.UniqueFlow
public meta import L4YAML.Proofs.Foundation.SurfaceSpanSupply

/-! # Experimental after-case for the block/document trace

The frozen before-case is `experiment/metagraph-problem` at
`aeacc60258b89fc1c5bb34b6f0ba9a5286801c02`. It kernel-checks three
two-bare-document readings through the old `TLYamlStream.implicitContinue`
and `traceWellFormed_refuted`. They are deliberately not restated as lemmas
on this after-branch: the continuation now accepts only an explicit document.

The scanner's positive trace is retained below. The negative guards prove
that `*x` and `&x` cannot start an explicit document, then use the existing
source-span lemmas to exclude every eventful block/document alternative at
the initial `a`. The resulting full fixed-input theorem is
`traceWellFormed_fixed : TraceWellFormed "a\n*x"`; it is NOT a proof of
general trace uniqueness, source/grammar correspondence, or capstone Group 7.7.
Priority 68 of `Tests/AdversarialInstantiation.lean` supplies the prior
adversarial predictions. The frozen `EXPERIMENT.md` retains the before-case
as the experiment's baseline; the PR description records the after verdict.
-/

namespace L4YAML.Tests.Guards.TraceOfBlockAmbiguity

open L4YAML L4YAML.Surface L4YAML.CharPredicates
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.SurfaceSpan

private lemma nsc_a : isNsChar 'a' := by unfold isNsChar; decide
private lemma nsc_star : isNsChar '*' := by unfold isNsChar; decide
private lemma nsc_x : isNsChar 'x' := by unfold isNsChar; decide
private lemma notInd_a : ¬ isIndicatorProp 'a' := by unfold isIndicatorProp; decide

private lemma eofComments (col : Nat) : SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  .withComment _ _ _ (.noSep _ _ (.eof col)) (.nil _)

abbrev w0 : SurfPos := ⟨['a', '\n', '*', 'x'], 0⟩
abbrev w1 : SurfPos := ⟨['\n', '*', 'x'], 1⟩
abbrev w2 : SurfPos := ⟨['*', 'x'], 0⟩
abbrev w3 : SurfPos := ⟨['x'], 1⟩
abbrev w4 : SurfPos := ⟨[], 2⟩

/-- The positive scanner-compatible reading survives the narrower stream. -/
lemma readPlainStar : TLYamlStream w0 w4 [] :=
  .single w0 w0 w4 w4 [] [] (.nil _)
    (.some _ _ _ (.bare _ _ _ (.mk _ _ _
      (.flowInBlock 0 .blockIn w0 w0 w4 w4 []
        (.inline 0 _ _ (.startOfLine _))
        (.content 0 .flowOut w0 w4 [] (.plain 0 .flowOut w0 w4
          (SNsPlainMultiLine.mk 0 .flowOut w0 w1 w4
            (SNsPlainOneLine.mk .flowOut w0 w1 w1
              (SNsPlainFirst.nonIndicator .flowOut 'a' _ 0 nsc_a notInd_a) (.nil _))
            (.cons w1 w4 w4
              (SSNsPlainNextLine.mk 0 .flowOut w1 w1 w2 w2 w2 w3 w4
                (.nil _) (SBBreak.lf _ 1) (.nil _)
                (SFlowLinePrefix.mk 0 w2 w2 w2 (.zero _) (.none _))
                (SNsPlainChar.safe .flowOut '*' _ 0 nsc_star (by decide) (by decide))
                (.cons w3 w4 w4
                  (SNbNsPlainInLineEntry.mk .flowOut w3 w3 w4 (.nil _)
                    (SNsPlainChar.safe .flowOut 'x' _ 1 nsc_x (by decide) (by decide)))
                  (.nil _)))
              (.nil _)))))
        (eofComments 2)))))
    (.nil _)

lemma traceOf_plainStar : TraceOf "a\n*x" [] := ⟨2, readPlainStar⟩

lemma scannerTrace_wf : SerializationWellFormed ([] : List Event) := by
  rw [serializationWellFormed_iff_check]; decide

/-- No explicit document, with ANY event trace or endpoint, can start at `*x`. -/
lemma no_unmarked_alias_document :
    ∀ (s' : SurfPos) (ev : List Event), ¬ TLExplicitDocument w2 s' ev := by
  intro s' ev h
  cases h with
  | withContent _ _ _ _ hStart _ => cases hStart

/-- Likewise for the `&x` continuation, independently of its event trace. -/
lemma no_unmarked_anchor_document :
    ∀ (s' : SurfPos) (ev : List Event),
      ¬ TLExplicitDocument ⟨['&', 'x'], 0⟩ s' ev := by
  intro s' ev h
  cases h with
  | withContent _ _ _ _ hStart _ => cases hStart

/-- Prefixes cannot advance past `*x`, even through repeated empty comment-prefixes. -/
private lemma no_alias_line_comment (s' : SurfPos) : ¬ SLComment w2 s' := by
  intro h
  cases h with
  | mk _ _ _ hSep hText hBreak =>
    cases hSep with
    | whites _ _ hWhite => cases hWhite with
      | mk _ _ hHead _ => cases hHead
    | startOfLine _ =>
      cases hText with
      | none => cases hBreak with
        | «break» _ _ hBr => cases hBr
      | some _ hHash => cases hHash

private lemma alias_prefix_static (s' : SurfPos) (h : SLDocumentPrefix w2 s') : s' = w2 := by
  cases h with
  | comments _ _ hComments =>
    cases hComments with
    | nil _ => rfl
    | cons _ _ _ hFirst _ => exact False.elim (no_alias_line_comment _ hFirst)

private lemma alias_prefixes_static_aux {s s' : SurfPos}
    (h : GStar SLDocumentPrefix s s') (hs : s = w2) : s' = w2 := by
  induction h with
  | nil _ => exact hs
  | cons _ _ _ hFirst _ ih =>
    cases hs
    exact ih (alias_prefix_static _ hFirst)

lemma alias_prefixes_static (s' : SurfPos) (h : GStar SLDocumentPrefix w2 s') :
    s' = w2 := alias_prefixes_static_aux h rfl

/-- Even with arbitrary document-prefix repetitions, the narrowed implicit arm
    cannot emit an alias (or any events) when begun at the unmarked `*x`. -/
lemma alias_implicit_body_empty
    (s₁ s₂ : SurfPos) (ev : List Event)
    (hPrefix : GStar SLDocumentPrefix w2 s₁)
    (hBody : TOpt TLExplicitDocument s₁ s₂ ev) :
    s₂ = w2 ∧ ev = [] := by
  have hStart := alias_prefixes_static _ hPrefix
  subst s₁
  cases hBody with
  | none => exact ⟨rfl, rfl⟩
  | some _ _ _ hExplicit => exact False.elim (no_unmarked_alias_document _ _ hExplicit)

/-- A document-end marker also cannot begin at the unmarked alias line. -/
lemma alias_suffixes_empty (s' : SurfPos) (ev : List Event)
    (h : TStar TLDocumentSuffix w2 s' ev) : s' = w2 ∧ ev = [] := by
  cases h with
  | nil _ => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ hSuffix _ =>
    cases hSuffix with
    | mk _ _ _ hEnd _ => cases hEnd

/-- The WHOLE after-grammar continuation arm at `*x` is event-empty and stationary:
    prefixes, optional explicit document, and any document suffixes. -/
lemma alias_implicit_tail_empty
    (s₁ s₂ s' : SurfPos) (body tail : List Event)
    (hPrefix : GStar SLDocumentPrefix w2 s₁)
    (hBody : TOpt TLExplicitDocument s₁ s₂ body)
    (hTail : TStar TLDocumentSuffix s₂ s' tail) :
    s' = w2 ∧ body ++ tail = [] := by
  obtain ⟨hs, he⟩ := alias_implicit_body_empty _ _ _ hPrefix hBody
  subst s₂
  obtain ⟨hs', he'⟩ := alias_suffixes_empty _ _ hTail
  exact ⟨hs', by simp [he, he']⟩

/-- The narrowed continuation still accepts an actual explicit document.
    This is conditional on the document relation, not a membership oracle. -/
lemma marked_continuation_retained
    (s s₁ s₂ s₃ s' : SurfPos) (e₀ e₁ e₂ : List Event)
    (hStream : TLYamlStream s s₁ e₀)
    (hPrefix : GStar SLDocumentPrefix s₁ s₂)
    (hExplicit : TLExplicitDocument s₂ s₃ e₁)
    (hSuffix : TStar TLDocumentSuffix s₃ s' e₂) :
    TLYamlStream s s' (e₀ ++ e₁ ++ e₂) :=
  .implicitContinue s s₁ s₂ s₃ s' e₀ e₁ e₂
    hStream hPrefix (.some _ _ _ hExplicit) hSuffix

/-- The first `a` cannot be an alias or start an event-bearing property. -/
private lemma no_props_at_a (c : YamlContext) (s' : SurfPos) (ev : List Event) :
    ¬ TCNsProperties 0 c w0 s' ev := by
  intro h
  cases h with
  | tagFirst _ _ _ _ _ hTag _ => cases hTag.1
  | anchorFirst _ _ _ _ _ hAnchor _ => cases hAnchor.1

/-- The source beginning with `a` has an event-free flow-node reading. -/
lemma flow_at_a_events_empty (s' : SurfPos) (ev : List Event)
    (h : TFlowNode 0 .flowOut w0 s' ev) : ev = [] := by
  cases h with
  | alias =>
    have ha : TCNsAliasNode w0 s' ev := by assumption
    cases ha.1
  | content =>
    have hc : TFlowContent 0 .flowOut w0 s' ev := by assumption
    cases hc with
    | plain => rfl
    | flowSeq =>
      have hs : TFlowSequence 0 .flowOut w0 s' ev := by assumption
      cases hs <;> (
        have hx : ∃ t, GLit '[' w0 t := ⟨_, by assumption⟩
        rcases hx with ⟨_, ho⟩
        cases ho)
    | flowMap =>
      have hs : TFlowMapping 0 .flowOut w0 s' ev := by assumption
      cases hs <;> (
        have hx : ∃ t, GLit '{' w0 t := ⟨_, by assumption⟩
        rcases hx with ⟨_, ho⟩
        cases ho)
    | singleQ => rfl
    | doubleQ => rfl
  | propsContent => exact False.elim (no_props_at_a .flowOut _ _ (by assumption))
  | propsEmpty => exact False.elim (no_props_at_a .flowOut _ _ (by assumption))

/-- Discriminating control: the same grammar CAN emit the alias at source `*x`.
    The preceding impossibility is about the `a` source, not alias support. -/
lemma flow_at_star_uses_alias : TFlowNode 0 .flowOut w2 w4 [.useAlias "x"] :=
  .alias 0 .flowOut w2 w4 _
    (And.intro
      (SCNsAliasNode.mk _ 0 w4
        (GPlus.mk _ _ _ (GChar.mk 'x' _ 1 (by unfold isNsAnchorChar isNsChar; decide))
          (.nil _))
        (fun _ hg => by cases hg))
      (by decide))

private lemma inline_at_a_static (s' : SurfPos) (h : SSeparateInLine w0 s') : s' = w0 := by
  cases h with
  | whites _ _ hWhite => cases hWhite with
    | mk _ _ hHead _ => cases hHead
  | startOfLine _ => rfl

private lemma no_a_line_comment (s' : SurfPos) : ¬ SLComment w0 s' := by
  intro h
  cases h with
  | mk _ _ _ hSep hText hBreak =>
    cases hSep with
    | whites _ _ hWhite => cases hWhite with
      | mk _ _ hHead _ => cases hHead
    | startOfLine _ =>
      cases hText with
      | none => cases hBreak with
        | «break» _ _ hBr => cases hBr
      | some _ hHash => cases hHash

private lemma no_a_sb_comment (s' : SurfPos) : ¬ SSBComment w0 s' := by
  intro h
  cases h with
  | noSep _ hBreak => cases hBreak with
    | «break» _ _ hBr => cases hBr
  | withSep _ _ _ hSep hOpt hBreak =>
    have hs := inline_at_a_static _ hSep
    subst hs
    cases hOpt with
    | none => cases hBreak with
      | «break» _ _ hBr => cases hBr
    | some _ hHash => cases hHash

private lemma comments_at_a_static (s' : SurfPos) (h : SSLComments w0 s') : s' = w0 := by
  cases h with
  | withComment _ _ _ hComment _ => exact False.elim (no_a_sb_comment _ hComment)
  | startOfLine _ _ hComments =>
    cases hComments with
    | nil _ => rfl
    | cons _ _ _ hFirst _ => exact False.elim (no_a_line_comment _ hFirst)

private lemma flow_prefix_at_a_static (s' : SurfPos) (h : SFlowLinePrefix 0 w0 s') :
    s' = w0 := by
  cases h with
  | mk _ _ hIndent hOpt =>
    cases hIndent
    cases hOpt with
    | none => rfl
    | some _ hSep => exact inline_at_a_static _ hSep

lemma separate_at_a_static (s' : SurfPos) (h : SSeparate 0 .flowOut w0 s') :
    s' = w0 := by
  change SSeparateLines 0 w0 s' at h
  cases h with
  | commented _ _ hComments hPrefix =>
    have hs := comments_at_a_static _ hComments
    subst hs
    exact flow_prefix_at_a_static _ hPrefix
  | inline _ hInline => exact inline_at_a_static _ hInline

/-- The `flowInBlock` arm of a bare document beginning with `a` is event-free:
    separation cannot move past `a`, and the flow-node itself has no events. -/
lemma block_flow_at_a_events_empty
    (s₁ s₂ s' : SurfPos) (ev : List Event)
    (hSep : SSeparate 0 .flowOut w0 s₁)
    (hFlow : TFlowNode 0 .flowOut s₁ s₂ ev)
    (_hComments : SSLComments s₂ s') : ev = [] := by
  have hStart := separate_at_a_static _ hSep
  subst s₁
  exact flow_at_a_events_empty _ _ hFlow

/-- A block literal cannot begin with the initial plain-scalar `a`.
    The literal indicator `|` is a constructor-level source requirement. -/
private lemma no_literal_at_a (s' : SurfPos) : ¬ SCLLiteral 0 w0 s' := by
  intro h
  cases h

/-- Likewise, a folded scalar requires `>` rather than the initial `a`. -/
private lemma no_folded_at_a (s' : SurfPos) : ¬ SCLFolded 0 w0 s' := by
  intro h
  cases h

/-- On the initial `a`, the optional scalar properties cannot move the source:
    both block scalar productions therefore face the wrong indicator. -/
private lemma block_scalar_prefix_at_a_static
    (s₁ s₂ : SurfPos) (ev : List Event)
    (hSep : SSeparate 0 .blockIn w0 s₁)
    (hProps : TOpt (TSeq (TCNsProperties 0 .blockIn)
      (Lift (SSeparate 0 .blockIn))) s₁ s₂ ev) :
    s₂ = w0 ∧ ev = [] := by
  have hs : s₁ = w0 := separate_at_a_static _ hSep
  subst s₁
  cases hProps with
  | none => exact ⟨rfl, rfl⟩
  | some _ _ _ hSeq =>
    cases hSeq with
    | mk _ _ _ _ _ hProperty _ =>
      exact False.elim (no_props_at_a .blockIn _ _ hProperty)

lemma no_block_literal_at_a
    (s₁ s₂ s' : SurfPos) (ev : List Event)
    (hSep : SSeparate 0 .blockIn w0 s₁)
    (hProps : TOpt (TSeq (TCNsProperties 0 .blockIn)
      (Lift (SSeparate 0 .blockIn))) s₁ s₂ ev)
    (hScalar : SCLLiteral 0 s₂ s') : False := by
  obtain ⟨hs, _⟩ := block_scalar_prefix_at_a_static _ _ _ hSep hProps
  subst s₂
  exact no_literal_at_a _ hScalar

lemma no_block_folded_at_a
    (s₁ s₂ s' : SurfPos) (ev : List Event)
    (hSep : SSeparate 0 .blockIn w0 s₁)
    (hProps : TOpt (TSeq (TCNsProperties 0 .blockIn)
      (Lift (SSeparate 0 .blockIn))) s₁ s₂ ev)
    (hScalar : SCLFolded 0 s₂ s') : False := by
  obtain ⟨hs, _⟩ := block_scalar_prefix_at_a_static _ _ _ hSep hProps
  subst s₂
  exact no_folded_at_a _ hScalar

/-- Optional block-collection properties cannot consume anything at initial `a`. -/
private lemma block_collection_prefix_at_a_static
    (s₁ : SurfPos) (ev : List Event)
    (h : TOpt (TSeq (Lift (SSeparate 0 .blockIn))
      (TCNsProperties 0 .blockIn)) w0 s₁ ev) : s₁ = w0 ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl, rfl⟩
  | some _ _ _ hSeq =>
    cases hSeq with
    | mk _ _ _ _ _ hSep hProps =>
      have hs : _ = w0 := separate_at_a_static _ hSep.1
      subst hs
      exact False.elim (no_props_at_a .blockIn _ _ hProps)

private lemma indent_at_a_static (n : Nat) (s' : SurfPos)
    (h : SIndent n w0 s') : s' = w0 := by
  cases h with
  | zero => rfl

/-- Regardless of indentation parameter, a block sequence needs `-`, not `a`. -/
private lemma no_seq_entries_at_a (n : Nat) (s' : SurfPos) (ev : List Event)
    (h : TBlockSeqEntries n w0 s' ev) : False := by
  cases h with
  | single _ _ _ _ _ _ _ hIndent hDash _ _ =>
    have hs := indent_at_a_static _ _ hIndent
    subst hs
    cases hDash
  | cons _ _ _ _ _ _ _ _ hIndent hDash _ _ _ =>
    have hs := indent_at_a_static _ _ hIndent
    subst hs
    cases hDash

lemma no_block_sequence_at_a (m : Nat)
    (s₁ s₂ s' : SurfPos) (ev₁ ev₂ : List Event)
    (hProps : TOpt (TSeq (Lift (SSeparate 0 .blockIn))
      (TCNsProperties 0 .blockIn)) w0 s₁ ev₁)
    (hComments : SSLComments s₁ s₂)
    (hEntries : TBlockSeqEntries (seqSpaces 0 .blockIn + m) s₂ s' ev₂) : False := by
  obtain ⟨hs, _⟩ := block_collection_prefix_at_a_static _ _ hProps
  subst s₁
  have hs₂ := comments_at_a_static _ hComments
  subst s₂
  exact no_seq_entries_at_a _ _ _ hEntries

/-- All five non-mapping block-node arms at the initial `a` are event-empty
    or impossible. A nonempty trace must therefore originate in block mapping. -/
lemma block_at_a_only_mapping_can_emit
    (s' : SurfPos) (ev : List Event)
    (h : TBlockNode 0 .blockIn w0 s' ev) :
    ev = [] ∨ ∃ m : Nat, TBlockMapEntries m w0 s' ev := by
  cases h with
  | blockLiteral _ _ _ _ _ _ _ hSep hProps hScalar =>
    exact False.elim (no_block_literal_at_a _ _ _ _ hSep hProps hScalar)
  | blockFolded _ _ _ _ _ _ _ hSep hProps hScalar =>
    exact False.elim (no_block_folded_at_a _ _ _ _ hSep hProps hScalar)
  | blockSeq _ _ m _ _ _ _ _ _ hProps hComments hEntries =>
    exact False.elim (no_block_sequence_at_a m _ _ _ _ _ hProps hComments hEntries)
  | blockMap _ _ m _ _ _ _ _ _ hProps hComments hEntries =>
    obtain ⟨hs, he⟩ := block_collection_prefix_at_a_static _ _ hProps
    subst hs
    have hs₂ := comments_at_a_static _ hComments
    subst hs₂
    right
    refine ⟨m, ?_⟩
    simpa [he] using hEntries
  | flowInBlock _ _ _ _ _ _ _ hSep hFlow hComments =>
    left
    exact block_flow_at_a_events_empty _ _ _ _ hSep hFlow hComments
  | emptyNode => exact Or.inl rfl

/-- Reuse the general source-span invariant: an implicit key cannot invent a
    colon at its endpoint when no colon occurs in the original source. -/
private lemma no_colon_after_key_at_a
    (s₁ s₂ : SurfPos) (ev : List Event)
    (hKey : TImplicitKey w0 s₁ ev)
    (hColon : GLit ':' s₁ s₂) : False := by
  have hsuf : s₁.chars <:+ w0.chars := by
    cases hKey with
    | jsonKey _ _ _ _ hFlow hSep =>
      exact (gopt_suffix (fun _ _ h => sSeparateInLine_suffix h) hSep).trans
        (tFlowNode_suffix hFlow)
    | yamlKey _ _ _ hPlain hSep =>
      exact (gopt_suffix (fun _ _ h => sSeparateInLine_suffix h) hSep).trans
        (snsPlain_suffix hPlain)
  have hmem : ':' ∈ s₁.chars := by
    cases hColon with
    | mk _ _ => simp
  have hnone : ':' ∉ w0.chars := by decide
  exact hnone (List.Sublist.mem hmem hsuf.sublist)

private lemma no_map_entry_at_a
    (n : Nat) (s' : SurfPos) (ev : List Event)
    (h : TBlockMapEntry n w0 s' ev) : False := by
  cases h with
  | explicit _ _ _ _ _ _ _ _ _ hQuestion _ _ _ _ => cases hQuestion
  | explicitEmpty _ _ _ _ _ hQuestion _ => cases hQuestion
  | implicitKeyNode _ _ _ _ _ _ _ hKey hColon _ =>
    exact no_colon_after_key_at_a _ _ _ hKey hColon
  | implicitKeyEmpty _ _ _ _ _ _ hKey hColon _ =>
    exact no_colon_after_key_at_a _ _ _ hKey hColon
  | emptyKeyNode _ _ _ _ _ hColon _ => cases hColon
  | emptyKeyEmpty _ _ _ _ hColon _ => cases hColon

lemma no_block_mapping_at_a (n : Nat) (s' : SurfPos) (ev : List Event)
    (h : TBlockMapEntries n w0 s' ev) : False := by
  cases h with
  | single _ _ _ _ _ hIndent hEntry =>
    have hs := indent_at_a_static _ _ hIndent
    subst hs
    exact no_map_entry_at_a _ _ _ hEntry
  | cons _ _ _ _ _ _ _ hIndent hEntry _ =>
    have hs := indent_at_a_static _ _ hIndent
    subst hs
    exact no_map_entry_at_a _ _ _ hEntry

/-- All initial block-node derivations of `a\n*x`, whatever their endpoint,
    emit no events. This closes the last eventful first-node alternative. -/
lemma block_at_a_events_empty (s' : SurfPos) (ev : List Event)
    (h : TBlockNode 0 .blockIn w0 s' ev) : ev = [] := by
  cases block_at_a_only_mapping_can_emit _ _ h with
  | inl he => exact he
  | inr hm =>
    obtain ⟨n, hEntries⟩ := hm
    exact False.elim (no_block_mapping_at_a _ _ _ hEntries)

/-- The first block node cannot synthesize a source endpoint: the only
    surviving arms are the flow reading and empty comments. -/
lemma block_at_a_suffix (s' : SurfPos) (ev : List Event)
    (h : TBlockNode 0 .blockIn w0 s' ev) : s'.chars <:+ w0.chars := by
  cases h with
  | blockLiteral _ _ _ _ _ _ _ hSep hProps hScalar =>
    exact False.elim (no_block_literal_at_a _ _ _ _ hSep hProps hScalar)
  | blockFolded _ _ _ _ _ _ _ hSep hProps hScalar =>
    exact False.elim (no_block_folded_at_a _ _ _ _ hSep hProps hScalar)
  | blockSeq _ _ m _ _ _ _ _ _ hProps hComments hEntries =>
    exact False.elim (no_block_sequence_at_a m _ _ _ _ _ hProps hComments hEntries)
  | blockMap _ _ m _ _ _ _ _ _ hProps hComments hEntries =>
    obtain ⟨hs, _⟩ := block_collection_prefix_at_a_static _ _ hProps
    subst hs
    have hs₂ := comments_at_a_static _ hComments
    subst hs₂
    exact False.elim (no_block_mapping_at_a _ _ _ hEntries)
  | flowInBlock _ _ _ _ _ _ _ hSep hFlow hComments =>
    exact (sslComments_suffix hComments).trans
      ((tFlowNode_suffix hFlow).trans (sSeparate_suffix hSep))
  | emptyNode => exact sslComments_suffix (by assumption)

private lemma char_absent_from_suffix (ch : Char) (hAbsent : ch ∉ w0.chars)
    (s : SurfPos) (hSuffix : s.chars <:+ w0.chars) : ch ∉ s.chars := by
  intro hMem
  exact hAbsent (List.Sublist.mem hMem hSuffix.sublist)

private lemma no_explicit_from_source_suffix (s s' : SurfPos)
    (ev : List Event) (hs : s.chars <:+ w0.chars) :
    ¬ TLExplicitDocument s s' ev := by
  intro h
  cases h with
  | withContent _ _ _ _ hMarker _ =>
    cases hMarker with
    | mk rest =>
      exact (char_absent_from_suffix '-' (by decide) _ hs) (by simp)

private lemma no_directive_from_source_suffix (s s' : SurfPos)
    (ev : List Event) (hs : s.chars <:+ w0.chars) :
    ¬ TLDirective s s' ev := by
  intro h
  obtain ⟨hDirective, _⟩ := h
  cases hDirective with
  | yaml => exact (char_absent_from_suffix '%' (by decide) _ hs) (by simp)
  | tag => exact (char_absent_from_suffix '%' (by decide) _ hs) (by simp)
  | reserved => exact (char_absent_from_suffix '%' (by decide) _ hs) (by simp)

private lemma no_suffix_from_source_suffix (s s' : SurfPos)
    (ev : List Event) (hs : s.chars <:+ w0.chars) :
    ¬ TLDocumentSuffix s s' ev := by
  intro h
  cases h with
  | mk _ _ _ hMarker _ =>
    cases hMarker with
    | mk rest =>
      exact (char_absent_from_suffix '.' (by decide) _ hs) (by simp)

private lemma suffix_star_empty (s s' : SurfPos) (ev : List Event)
    (hs : s.chars <:+ w0.chars)
    (h : TStar TLDocumentSuffix s s' ev) : s' = s ∧ ev = [] := by
  cases h with
  | nil _ => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ hFirst _ =>
    exact False.elim (no_suffix_from_source_suffix _ _ _ hs hFirst)

private lemma suffix_plus_impossible (s s' : SurfPos) (ev : List Event)
    (hs : s.chars <:+ w0.chars)
    (h : TPlus TLDocumentSuffix s s' ev) : False := by
  cases h with
  | mk _ _ _ _ _ hFirst _ =>
    exact no_suffix_from_source_suffix _ _ _ hs hFirst

private lemma explicit_optional_empty (s s' : SurfPos) (ev : List Event)
    (hs : s.chars <:+ w0.chars)
    (h : TOpt TLExplicitDocument s s' ev) : s' = s ∧ ev = [] := by
  cases h with
  | none => exact ⟨rfl, rfl⟩
  | some _ _ _ hExplicit =>
    exact False.elim (no_explicit_from_source_suffix _ _ _ hs hExplicit)

private lemma a_prefix_static (s' : SurfPos) (h : SLDocumentPrefix w0 s') :
    s' = w0 := by
  cases h with
  | comments _ _ hComments =>
    cases hComments with
    | nil _ => rfl
    | cons _ _ _ hFirst _ => exact False.elim (no_a_line_comment _ hFirst)

private lemma a_prefixes_static_aux {s s' : SurfPos}
    (h : GStar SLDocumentPrefix s s') (hs : s = w0) : s' = w0 := by
  induction h with
  | nil _ => exact hs
  | cons _ _ _ hFirst _ ih =>
    cases hs
    exact ih (a_prefix_static _ hFirst)

private lemma a_prefixes_static (s' : SurfPos)
    (h : GStar SLDocumentPrefix w0 s') : s' = w0 :=
  a_prefixes_static_aux h rfl

private lemma no_any_directive_at_a (s' : SurfPos) (ev : List Event)
    (h : TLDirectiveDocument w0 s' ev) : False := by
  cases h with
  | mk _ _ _ _ _ _ hDirs _ _ =>
    cases hDirs with
    | mk _ _ _ _ _ hDirective _ =>
      exact no_directive_from_source_suffix _ _ _ (List.suffix_refl _) hDirective

/-- At the source beginning with `a`, any optional first document is either
    absent or a bare block node. In either case it has no events and its
    endpoint remains a suffix of the actual input. -/
lemma first_document_events_empty (s' : SurfPos) (ev : List Event)
    (h : TOpt TLAnyDocument w0 s' ev) :
    ev = [] ∧ s'.chars <:+ w0.chars := by
  cases h with
  | none => exact ⟨rfl, List.suffix_refl _⟩
  | some _ _ _ hDocument =>
    cases hDocument with
    | directive _ _ _ hDirective =>
      exact False.elim (no_any_directive_at_a _ _ hDirective)
    | explicit _ _ _ hExplicit =>
      exact False.elim
        (no_explicit_from_source_suffix _ _ _ (List.suffix_refl _) hExplicit)
    | bare _ _ _ hBare =>
      cases hBare with
      | mk _ _ _ hBlock =>
        exact ⟨block_at_a_events_empty _ _ hBlock,
          block_at_a_suffix _ _ hBlock⟩

/-- The full annotated stream for this fixed source has no event-bearing
    derivation. All continuation arms would require a source marker that
    cannot occur in a suffix of these four characters. -/
private lemma stream_at_a_aux (s s' : SurfPos) (ev : List Event)
    (h : TLYamlStream s s' ev) :
    s = w0 → ev = [] ∧ s'.chars <:+ w0.chars := by
  induction h with
  | single _ _ _ _ _ _ hPrefixes hDocument hSuffix =>
    intro hStart
    subst hStart
    have hs₁ := a_prefixes_static _ hPrefixes
    subst hs₁
    obtain ⟨he₁, hs₂⟩ := first_document_events_empty _ _ hDocument
    obtain ⟨hs', he₂⟩ := suffix_star_empty _ _ _ hs₂ hSuffix
    subst hs'
    exact ⟨by simp [he₁, he₂], hs₂⟩
  | suffixContinue _ _ _ _ _ _ _ _ _ _ hPrev hSuffixes _ _ _ ih =>
    intro hStart
    obtain ⟨_, hs₁⟩ := ih hStart
    exact False.elim (suffix_plus_impossible _ _ _ hs₁ hSuffixes)
  | implicitContinue _ _ _ _ _ _ _ _ hPrev hPrefixes hBody hSuffix ih =>
    intro hStart
    obtain ⟨he₀, hs₁⟩ := ih hStart
    have hs₂ : _ := (gstar_suffix (fun _ _ h => slDocumentPrefix_suffix h) hPrefixes).trans hs₁
    obtain ⟨hs₃, he₁⟩ := explicit_optional_empty _ _ _ hs₂ hBody
    subst hs₃
    obtain ⟨hs', he₂⟩ := suffix_star_empty _ _ _ hs₂ hSuffix
    subst hs'
    exact ⟨by simp [he₀, he₁, he₂], hs₂⟩

lemma stream_at_a_events_empty (s' : SurfPos) (ev : List Event)
    (h : TLYamlStream w0 s' ev) : ev = [] ∧ s'.chars <:+ w0.chars :=
  stream_at_a_aux _ _ _ h rfl

/-- Exact negative witness in the after grammar: no spurious alias trace
    exists at any ending column. -/
lemma traceOf_only_plain (ev : List Event)
    (h : TraceOf "a\n*x" ev) : ev = [] := by
  obtain ⟨col, hStream⟩ := h
  exact (stream_at_a_events_empty ⟨[], col⟩ ev hStream).1

lemma no_alias_trace : ¬ TraceOf "a\n*x" [.useAlias "x"] := by
  intro h
  have he := traceOf_only_plain _ h
  cases he

/-- The intended full well-formedness flips from false on the frozen problem
    branch to true on this local after grammar, for this exact source. -/
lemma traceWellFormed_fixed : TraceWellFormed "a\n*x" := by
  intro ev h
  have he := traceOf_only_plain ev h
  subst ev
  exact scannerTrace_wf

#print axioms no_unmarked_alias_document
#print axioms no_unmarked_anchor_document
#print axioms alias_prefixes_static
#print axioms alias_implicit_body_empty
#print axioms alias_implicit_tail_empty
#print axioms flow_at_a_events_empty
#print axioms flow_at_star_uses_alias
#print axioms separate_at_a_static
#print axioms block_flow_at_a_events_empty
#print axioms no_block_literal_at_a
#print axioms no_block_folded_at_a
#print axioms no_block_sequence_at_a
#print axioms block_at_a_only_mapping_can_emit
#print axioms no_block_mapping_at_a
#print axioms block_at_a_events_empty
#print axioms stream_at_a_events_empty
#print axioms traceOf_only_plain
#print axioms no_alias_trace
#print axioms traceWellFormed_fixed
#print axioms marked_continuation_retained

end L4YAML.Tests.Guards.TraceOfBlockAmbiguity
