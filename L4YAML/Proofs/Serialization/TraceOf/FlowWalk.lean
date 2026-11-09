/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Serialization.TraceOf.Node
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Production.StreamAccum
/-!
# S3 slice (3), PR 2a — the flow frame algebra over `TraceOf`
(EVENTSOF §10, capstone 7.7 `parse_iff_grammar`; item 466)

`TraceOf` siblings of `NodeProduction`'s flow-entry algebra and of `StreamAccum`'s
`SeqFrame` / `MapFrame`, each with one more index: the frame's trace (the `goOut`
trace of its token segment, coupled to the scanner in 2c).  Every S-side shape has
exactly one T-side twin — `TFlowSeqEntriesCloseable` / `TPartialFlowSeq` /
`TFlowSeqPrefix` / `TSeqFrame` and the mapping four — and every step of the frame
walk (`,`, `]` / `}`) preserves the trace: `TSeqFrame.closeWithSep` lands every one
of the 10 shapes on `TFlowSequence … ev`, `TSeqFrame.holdComma` on `TSeqFrame … .sep … ev`.
No scanner step here (2b re-walks `accum_step_flow` onto these), no `StreamAccum` edit.
Rule 2 first: Priority 104 (`Tests/AdversarialInstantiation.lean`).
-/
namespace L4YAML.Proofs.Serialization.TraceOf.FlowWalk
@[expose] public section
open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.PreprocessProduction (GOpt_SSeparate_extend)
open L4YAML.Proofs.StreamAccum (FrameTail FlowStackK)

/-! ## §1 Closeable entries, partial collections, prefixes (T twins of `NodeProduction` §4) -/

/-- `FlowSeqEntriesCloseable` over a traced derivation: no trailing `,` (`consEnd` excluded;
    `TPartialFlowSeq.held` carries that case). -/
inductive TFlowSeqEntriesCloseable :
    {n : Nat} → {c : YamlContext} → {s s' : SurfPos} → {ev : List Event} →
    TFlowSeqEntries n c s s' ev → Prop where
  | single {n : Nat} {c : YamlContext} {s s₁ s' : SurfPos} {ev : List Event}
      (he : TFlowSeqEntry n c s s₁ ev) (hsep : GOpt (SSeparate n c) s₁ s') :
      TFlowSeqEntriesCloseable (TFlowSeqEntries.single n c s s₁ s' ev he hsep)
  | consMore {n : Nat} {c : YamlContext} {s s₁ s₂ s₃ s₄ s' : SurfPos} {ev1 ev2 : List Event}
      (he : TFlowSeqEntry n c s s₁ ev1) (hsep : GOpt (SSeparate n c) s₁ s₂)
      (hcomma : GLit ',' s₂ s₃) (hsep' : GOpt (SSeparate n c) s₃ s₄)
      (tail : TFlowSeqEntries n c s₄ s' ev2) :
      TFlowSeqEntriesCloseable tail →
      TFlowSeqEntriesCloseable
        (TFlowSeqEntries.consMore n c s s₁ s₂ s₃ s₄ s' ev1 ev2 he hsep hcomma hsep' tail)

/-- `FlowMapEntriesCloseable` over a traced derivation. -/
inductive TFlowMapEntriesCloseable :
    {n : Nat} → {c : YamlContext} → {s s' : SurfPos} → {ev : List Event} →
    TFlowMapEntries n c s s' ev → Prop where
  | single {n : Nat} {c : YamlContext} {s s₁ s' : SurfPos} {ev : List Event}
      (he : TFlowMapEntry n c s s₁ ev) (hsep : GOpt (SSeparate n c) s₁ s') :
      TFlowMapEntriesCloseable (TFlowMapEntries.single n c s s₁ s' ev he hsep)
  | consMore {n : Nat} {c : YamlContext} {s s₁ s₂ s₃ s₄ s' : SurfPos} {ev1 ev2 : List Event}
      (he : TFlowMapEntry n c s s₁ ev1) (hsep : GOpt (SSeparate n c) s₁ s₂)
      (hcomma : GLit ',' s₂ s₃) (hsep' : GOpt (SSeparate n c) s₃ s₄)
      (tail : TFlowMapEntries n c s₄ s' ev2) :
      TFlowMapEntriesCloseable tail →
      TFlowMapEntriesCloseable
        (TFlowMapEntries.consMore n c s s₁ s₂ s₃ s₄ s' ev1 ev2 he hsep hcomma hsep' tail)

/-- `PartialFlowSeq` with the trace: nothing yet (`[]`), closeable entries, or entries plus a
    trailing `,`. -/
inductive TPartialFlowSeq (n : Nat) (c : YamlContext) : SurfPos → SurfPos → List Event → Prop where
  | empty (sp : SurfPos) : TPartialFlowSeq n c sp sp []
  | entries (sp sp' : SurfPos) (ev : List Event) (h : TFlowSeqEntries n c sp sp' ev)
      (hcl : TFlowSeqEntriesCloseable h) : TPartialFlowSeq n c sp sp' ev
  | held (sp sp_e sp_c sp' : SurfPos) (ev : List Event) (h : TFlowSeqEntries n c sp sp_e ev)
      (hcl : TFlowSeqEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : TPartialFlowSeq n c sp sp' ev

/-- `PartialFlowMap` with the trace. -/
inductive TPartialFlowMap (n : Nat) (c : YamlContext) : SurfPos → SurfPos → List Event → Prop where
  | empty (sp : SurfPos) : TPartialFlowMap n c sp sp []
  | entries (sp sp' : SurfPos) (ev : List Event) (h : TFlowMapEntries n c sp sp' ev)
      (hcl : TFlowMapEntriesCloseable h) : TPartialFlowMap n c sp sp' ev
  | held (sp sp_e sp_c sp' : SurfPos) (ev : List Event) (h : TFlowMapEntries n c sp sp_e ev)
      (hcl : TFlowMapEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : TPartialFlowMap n c sp sp' ev

/-- `FlowSeqPrefix` with the trace: the committed entries a fresh entry extends. -/
inductive TFlowSeqPrefix (n : Nat) (c : YamlContext) : SurfPos → SurfPos → List Event → Prop where
  | init (sp : SurfPos) : TFlowSeqPrefix n c sp sp []
  | cons (sp sp_e sp_c sp' : SurfPos) (ev : List Event) (h : TFlowSeqEntries n c sp sp_e ev)
      (hcl : TFlowSeqEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : TFlowSeqPrefix n c sp sp' ev

/-- `FlowMapPrefix` with the trace. -/
inductive TFlowMapPrefix (n : Nat) (c : YamlContext) : SurfPos → SurfPos → List Event → Prop where
  | init (sp : SurfPos) : TFlowMapPrefix n c sp sp []
  | cons (sp sp_e sp_c sp' : SurfPos) (ev : List Event) (h : TFlowMapEntries n c sp sp_e ev)
      (hcl : TFlowMapEntriesCloseable h) (hcomma : GLit ',' sp_e sp_c)
      (hsep : GOpt (SSeparate n c) sp_c sp') : TFlowMapPrefix n c sp sp' ev

/-! ## §2 The frames (T twins of `StreamAccum`'s `SeqFrame` / `MapFrame`, 10 + 10 shapes)

The `kj` side condition is stated over the SAME trace as the node: a trace is determined by
the token run, so a producer that reads a JSON-like key proves `TFlowNode` and `TCFlowJsonNode`
off one run with one `ev`. -/

/-- The state of one open flow SEQUENCE frame, with its trace. -/
inductive TSeqFrame (n : Nat) (c : YamlContext) :
    FrameTail → SurfPos → SurfPos → List Event → Prop where
  | betweenEmpty (sp : SurfPos) : TSeqFrame n c .sep sp sp []
  | betweenEntries (kj : Bool) (sp sp' : SurfPos) (ev : List Event)
      (h : TFlowSeqEntries n c sp sp' ev) (hcl : TFlowSeqEntriesCloseable h) :
      TSeqFrame n c (.value kj) sp sp' ev
  | betweenHeld (sp sp_e sp_c sp' : SurfPos) (ev : List Event)
      (h : TFlowSeqEntries n c sp sp_e ev) (hcl : TFlowSeqEntriesCloseable h)
      (hcomma : GLit ',' sp_e sp_c) (hsep : GOpt (SSeparate n c) sp_c sp') :
      TSeqFrame n c .sep sp sp' ev
  | midNode (kj : Bool) (sp sp_d sp' : SurfPos) (ev_p ev_n : List Event)
      (pre : TFlowSeqPrefix n c sp sp_d ev_p)
      (hnode : TFlowNode n c sp_d sp' ev_n) (hjson : kj = true → TCFlowJsonNode n c sp_d sp' ev_n) :
      TSeqFrame n c (.value kj) sp sp' (ev_p ++ ev_n)
  | midColon (kj : Bool) (sp sp_d sp_k sp_s sp' : SurfPos) (ev_p ev_n : List Event)
      (pre : TFlowSeqPrefix n c sp sp_d ev_p)
      (hkey : TFlowNode n c sp_d sp_k ev_n) (hjson : kj = true → TCFlowJsonNode n c sp_d sp_k ev_n)
      (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
      TSeqFrame n c (.colon kj) sp sp' (ev_p ++ ev_n)
  | midExplicitKey (kj : Bool) (sp sp_q sp_qe sp_k0 sp' : SurfPos) (ev_p ev_n : List Event)
      (pre : TFlowSeqPrefix n c sp sp_q ev_p)
      (hq : GLit '?' sp_q sp_qe) (hqsep : SSeparate n c sp_qe sp_k0)
      (hkey : TFlowNode n c sp_k0 sp' ev_n) (hjson : kj = true → TCFlowJsonNode n c sp_k0 sp' ev_n) :
      TSeqFrame n c (.value kj) sp sp' (ev_p ++ ev_n)
  | midExplicitColon (kj : Bool) (sp sp_q sp_qe sp_k0 sp_k sp_s sp' : SurfPos) (ev_p ev_n : List Event)
      (pre : TFlowSeqPrefix n c sp sp_q ev_p) (hq : GLit '?' sp_q sp_qe)
      (hqsep : SSeparate n c sp_qe sp_k0) (hkey : TFlowNode n c sp_k0 sp_k ev_n)
      (hjson : kj = true → TCFlowJsonNode n c sp_k0 sp_k ev_n)
      (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
      TSeqFrame n c (.colon kj) sp sp' (ev_p ++ ev_n)
  | midEmptyColon (sp sp_s sp' : SurfPos) (ev_p : List Event)
      (pre : TFlowSeqPrefix n c sp sp_s ev_p) (hcolon : GLit ':' sp_s sp') :
      TSeqFrame n c (.colon false) sp sp' ev_p
  | midQuestion (sp sp_q sp' : SurfPos) (ev_p : List Event)
      (pre : TFlowSeqPrefix n c sp sp_q ev_p) (hq : GLit '?' sp_q sp') :
      TSeqFrame n c .question sp sp' ev_p
  | midQuestionEmptyColon (sp sp_q sp_qe sp_s sp' : SurfPos) (ev_p : List Event)
      (pre : TFlowSeqPrefix n c sp sp_q ev_p) (hq : GLit '?' sp_q sp_qe)
      (hqsep : SSeparate n c sp_qe sp_s) (hcolon : GLit ':' sp_s sp') :
      TSeqFrame n c (.colon false) sp sp' ev_p

/-- The state of one open flow MAPPING frame, with its trace. -/
inductive TMapFrame (n : Nat) (c : YamlContext) :
    FrameTail → SurfPos → SurfPos → List Event → Prop where
  | betweenEmpty (sp : SurfPos) : TMapFrame n c .sep sp sp []
  | betweenEntries (kj : Bool) (sp sp' : SurfPos) (ev : List Event)
      (h : TFlowMapEntries n c sp sp' ev) (hcl : TFlowMapEntriesCloseable h) :
      TMapFrame n c (.value kj) sp sp' ev
  | betweenHeld (sp sp_e sp_c sp' : SurfPos) (ev : List Event)
      (h : TFlowMapEntries n c sp sp_e ev) (hcl : TFlowMapEntriesCloseable h)
      (hcomma : GLit ',' sp_e sp_c) (hsep : GOpt (SSeparate n c) sp_c sp') :
      TMapFrame n c .sep sp sp' ev
  | midKey (kj : Bool) (sp sp_d sp' : SurfPos) (ev_p ev_n : List Event)
      (pre : TFlowMapPrefix n c sp sp_d ev_p)
      (hkey : TFlowNode n c sp_d sp' ev_n) (hjson : kj = true → TCFlowJsonNode n c sp_d sp' ev_n) :
      TMapFrame n c (.value kj) sp sp' (ev_p ++ ev_n)
  | midColon (kj : Bool) (sp sp_d sp_k sp_s sp' : SurfPos) (ev_p ev_n : List Event)
      (pre : TFlowMapPrefix n c sp sp_d ev_p)
      (hkey : TFlowNode n c sp_d sp_k ev_n) (hjson : kj = true → TCFlowJsonNode n c sp_d sp_k ev_n)
      (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
      TMapFrame n c (.colon kj) sp sp' (ev_p ++ ev_n)
  | midExplicitKey (kj : Bool) (sp sp_q sp_qe sp_k0 sp' : SurfPos) (ev_p ev_n : List Event)
      (pre : TFlowMapPrefix n c sp sp_q ev_p)
      (hq : GLit '?' sp_q sp_qe) (hqsep : SSeparate n c sp_qe sp_k0)
      (hkey : TFlowNode n c sp_k0 sp' ev_n) (hjson : kj = true → TCFlowJsonNode n c sp_k0 sp' ev_n) :
      TMapFrame n c (.value kj) sp sp' (ev_p ++ ev_n)
  | midExplicitColon (kj : Bool) (sp sp_q sp_qe sp_k0 sp_k sp_s sp' : SurfPos) (ev_p ev_n : List Event)
      (pre : TFlowMapPrefix n c sp sp_q ev_p) (hq : GLit '?' sp_q sp_qe)
      (hqsep : SSeparate n c sp_qe sp_k0) (hkey : TFlowNode n c sp_k0 sp_k ev_n)
      (hjson : kj = true → TCFlowJsonNode n c sp_k0 sp_k ev_n)
      (hsep : GOpt (SSeparate n c) sp_k sp_s) (hcolon : GLit ':' sp_s sp') :
      TMapFrame n c (.colon kj) sp sp' (ev_p ++ ev_n)
  | midEmptyColon (sp sp_s sp' : SurfPos) (ev_p : List Event)
      (pre : TFlowMapPrefix n c sp sp_s ev_p) (hcolon : GLit ':' sp_s sp') :
      TMapFrame n c (.colon false) sp sp' ev_p
  | midQuestion (sp sp_q sp' : SurfPos) (ev_p : List Event)
      (pre : TFlowMapPrefix n c sp sp_q ev_p) (hq : GLit '?' sp_q sp') :
      TMapFrame n c .question sp sp' ev_p
  | midQuestionEmptyColon (sp sp_q sp_qe sp_s sp' : SurfPos) (ev_p : List Event)
      (pre : TFlowMapPrefix n c sp sp_q ev_p) (hq : GLit '?' sp_q sp_qe)
      (hqsep : SSeparate n c sp_qe sp_s) (hcolon : GLit ':' sp_s sp') :
      TMapFrame n c (.colon false) sp sp' ev_p

/-! ## §3 The open-frame stack and the `FlowStackK` sibling

`TFlowOpenStack n fl ks tl sp_before sp_cur ev`: `fl` open frames (`ks` their kinds,
`true` = sequence, as in `FlowOpenStack`), the innermost's tail `tl`, the outer boundary
`sp_before` (decoupled from the outermost `[` / `{` at `sp_br`, as in `FlowOpenStack.seqBase`:
the gap is the enclosing context's), the innermost's end at `sp_cur`, and `ev` the trace of the
open frames: each parent's trace so far (at whatever tail it held when the child opened —
`.sep` for `[[`, `.colon false` for `{a: [`) followed by the innermost frame's.  `FlowOpenStack`'s scanner-side
payloads (`resume`, `promise`, `inject`) are not mirrored: 2c couples them. -/
inductive TFlowOpenStack (n : Nat) :
    Nat → Array Bool → FrameTail → SurfPos → SurfPos → List Event → Prop where
  | seqBase (sp_before sp_br sp_open sp_es sp_cur : SurfPos) (tl : FrameTail) (ev : List Event)
      (h_open : GLit '[' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowOut) sp_open sp_es)
      (st : TSeqFrame n (inFlowCtx .flowOut) tl sp_es sp_cur ev) :
      TFlowOpenStack n 1 #[true] tl sp_before sp_cur ev
  | mapBase (sp_before sp_br sp_open sp_es sp_cur : SurfPos) (tl : FrameTail) (ev : List Event)
      (h_open : GLit '{' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowOut) sp_open sp_es)
      (st : TMapFrame n (inFlowCtx .flowOut) tl sp_es sp_cur ev) :
      TFlowOpenStack n 1 #[false] tl sp_before sp_cur ev
  | seqNest (d : Nat) (ks : Array Bool) (tl_par tl : FrameTail)
      (sp_before sp_par sp_br sp_open sp_es sp_cur : SurfPos) (ev_par ev : List Event)
      (parent : TFlowOpenStack n d ks tl_par sp_before sp_par ev_par)
      (h_tail : ∀ kj, tl_par ≠ .value kj)
      (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
      (h_open : GLit '[' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
      (st : TSeqFrame n .flowIn tl sp_es sp_cur ev) :
      TFlowOpenStack n (d + 1) (ks.push true) tl sp_before sp_cur (ev_par ++ ev)
  | mapNest (d : Nat) (ks : Array Bool) (tl_par tl : FrameTail)
      (sp_before sp_par sp_br sp_open sp_es sp_cur : SurfPos) (ev_par ev : List Event)
      (parent : TFlowOpenStack n d ks tl_par sp_before sp_par ev_par)
      (h_tail : ∀ kj, tl_par ≠ .value kj)
      (h_lead : SSeparateLines n sp_par sp_br ∨ (sp_br = sp_par ∧ tl_par.leadFree))
      (h_open : GLit '{' sp_br sp_open)
      (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
      (st : TMapFrame n .flowIn tl sp_es sp_cur ev) :
      TFlowOpenStack n (d + 1) (ks.push false) tl sp_before sp_cur (ev_par ++ ev)

/-- The `FlowStackB` sibling: no flow open (`nil`, depth 0, any tail, trace `[]`) or an open
    stack.  `nil` is what the re-walk starts from and returns to after a base close. -/
inductive TFlowStackB (n : Nat) :
    Nat → Array Bool → FrameTail → SurfPos → SurfPos → List Event → Prop where
  | nil (sp : SurfPos) (tl : FrameTail) : TFlowStackB n 0 #[] tl sp sp []
  | «open» (d : Nat) (ks : Array Bool) (tl : FrameTail) (sp_block sp_cur : SurfPos) (ev : List Event)
      (h : TFlowOpenStack n d ks tl sp_block sp_cur ev) :
      TFlowStackB n d ks tl sp_block sp_cur ev

/-- The `FlowStackK` sibling: the scanner-coupled S stack as it stands, and a `TraceOf` stack
    over the same frame indices with trace `ev`.  The S frame and the T frame sit side by side
    (no `TFlow* → SFlow*` erasure is spent); 2c couples `ev` to `goOut` of the token segment
    since `sp_block` over `scanLoop`. -/
def TFlowStackK (sp_start : SurfPos) (sc : L4YAML.Scanner.ScannerState) (fl : Nat) (ks : Array Bool)
    (tl : FrameTail) (sp_block sp_flow : SurfPos) (ev : List Event) : Prop :=
  FlowStackK sp_start sc fl ks tl sp_block sp_flow ∧
    ∃ n, TFlowStackB n fl ks tl sp_block sp_flow ev

/-! ## §4 The entries algebra (T twins of `NodeProduction` §4 / `PreprocessProduction`) -/

lemma TFlowSeqEntries_extendSep {n : Nat} {c : YamlContext} {s s_e s' : SurfPos} {ev : List Event}
    {h : TFlowSeqEntries n c s s_e ev} (hcl : TFlowSeqEntriesCloseable h)
    (hsep : SSeparate n c s_e s') :
    ∃ h' : TFlowSeqEntries n c s s' ev, TFlowSeqEntriesCloseable h' := by
  revert hsep
  induction hcl with
  | single he hs => intro hsep; exact ⟨.single _ _ _ _ _ _ he (GOpt_SSeparate_extend hs hsep), .single he (GOpt_SSeparate_extend hs hsep)⟩
  | consMore he hs hc hs' tail _ ih =>
    intro hsep
    obtain ⟨t', ht'⟩ := ih hsep
    exact ⟨.consMore _ _ _ _ _ _ _ _ _ _ he hs hc hs' t', .consMore he hs hc hs' t' ht'⟩

lemma TFlowMapEntries_extendSep {n : Nat} {c : YamlContext} {s s_e s' : SurfPos} {ev : List Event}
    {h : TFlowMapEntries n c s s_e ev} (hcl : TFlowMapEntriesCloseable h)
    (hsep : SSeparate n c s_e s') :
    ∃ h' : TFlowMapEntries n c s s' ev, TFlowMapEntriesCloseable h' := by
  revert hsep
  induction hcl with
  | single he hs => intro hsep; exact ⟨.single _ _ _ _ _ _ he (GOpt_SSeparate_extend hs hsep), .single he (GOpt_SSeparate_extend hs hsep)⟩
  | consMore he hs hc hs' tail _ ih =>
    intro hsep
    obtain ⟨t', ht'⟩ := ih hsep
    exact ⟨.consMore _ _ _ _ _ _ _ _ _ _ he hs hc hs' t', .consMore he hs hc hs' t' ht'⟩

/-- Closeable entries plus a trailing `,` are entries (`consEnd` at the last entry). -/
lemma TFlowSeqEntries_addTrailingComma {n : Nat} {c : YamlContext} {s s_e s_c s' : SurfPos}
    {ev : List Event} {h : TFlowSeqEntries n c s s_e ev} (hcl : TFlowSeqEntriesCloseable h)
    (hcomma : GLit ',' s_e s_c) (hsep : GOpt (SSeparate n c) s_c s') :
    TFlowSeqEntries n c s s' ev := by
  revert hcomma hsep
  induction hcl with
  | single he hs => intro hcomma hsep; exact .consEnd _ _ _ _ _ _ _ _ he hs hcomma hsep
  | consMore he hs hc hs' _ _ ih =>
    intro hcomma hsep
    exact .consMore _ _ _ _ _ _ _ _ _ _ he hs hc hs' (ih hcomma hsep)

lemma TFlowMapEntries_addTrailingComma {n : Nat} {c : YamlContext} {s s_e s_c s' : SurfPos}
    {ev : List Event} {h : TFlowMapEntries n c s s_e ev} (hcl : TFlowMapEntriesCloseable h)
    (hcomma : GLit ',' s_e s_c) (hsep : GOpt (SSeparate n c) s_c s') :
    TFlowMapEntries n c s s' ev := by
  revert hcomma hsep
  induction hcl with
  | single he hs => intro hcomma hsep; exact .consEnd _ _ _ _ _ _ _ _ he hs hcomma hsep
  | consMore he hs hc hs' _ _ ih =>
    intro hcomma hsep
    exact .consMore _ _ _ _ _ _ _ _ _ _ he hs hc hs' (ih hcomma hsep)

/-- Snoc a finished entry onto held entries: the trace grows by the entry's. -/
lemma TFlowSeqEntries_snoc {n : Nat} {c : YamlContext} {s s_e s_c s_d s_x s' : SurfPos}
    {ev ev_e : List Event} {h : TFlowSeqEntries n c s s_e ev} (hcl : TFlowSeqEntriesCloseable h)
    (hcomma : GLit ',' s_e s_c) (hsep : GOpt (SSeparate n c) s_c s_d)
    (h_entry : TFlowSeqEntry n c s_d s_x ev_e) (h_sep : GOpt (SSeparate n c) s_x s') :
    ∃ h' : TFlowSeqEntries n c s s' (ev ++ ev_e), TFlowSeqEntriesCloseable h' := by
  revert hcomma hsep h_entry h_sep
  induction hcl with
  | single he hs =>
    intro hcomma hsep h_entry h_sep
    exact ⟨.consMore _ _ _ _ _ _ _ _ _ _ he hs hcomma hsep (.single _ _ _ _ _ _ h_entry h_sep),
      .consMore he hs hcomma hsep _ (.single h_entry h_sep)⟩
  | consMore he hs hc hs' _ _ ih =>
    intro hcomma hsep h_entry h_sep
    obtain ⟨t', ht'⟩ := ih hcomma hsep h_entry h_sep
    rw [List.append_assoc]
    exact ⟨.consMore _ _ _ _ _ _ _ _ _ _ he hs hc hs' t', .consMore he hs hc hs' t' ht'⟩

lemma TFlowMapEntries_snoc {n : Nat} {c : YamlContext} {s s_e s_c s_d s_x s' : SurfPos}
    {ev ev_e : List Event} {h : TFlowMapEntries n c s s_e ev} (hcl : TFlowMapEntriesCloseable h)
    (hcomma : GLit ',' s_e s_c) (hsep : GOpt (SSeparate n c) s_c s_d)
    (h_entry : TFlowMapEntry n c s_d s_x ev_e) (h_sep : GOpt (SSeparate n c) s_x s') :
    ∃ h' : TFlowMapEntries n c s s' (ev ++ ev_e), TFlowMapEntriesCloseable h' := by
  revert hcomma hsep h_entry h_sep
  induction hcl with
  | single he hs =>
    intro hcomma hsep h_entry h_sep
    exact ⟨.consMore _ _ _ _ _ _ _ _ _ _ he hs hcomma hsep (.single _ _ _ _ _ _ h_entry h_sep),
      .consMore he hs hcomma hsep _ (.single h_entry h_sep)⟩
  | consMore he hs hc hs' _ _ ih =>
    intro hcomma hsep h_entry h_sep
    obtain ⟨t', ht'⟩ := ih hcomma hsep h_entry h_sep
    rw [List.append_assoc]
    exact ⟨.consMore _ _ _ _ _ _ _ _ _ _ he hs hc hs' t', .consMore he hs hc hs' t' ht'⟩

/-- A prefix plus a finished entry is closeable entries (`FlowSeqPrefix.appendEntry`'s content). -/
lemma TFlowSeqPrefix.snocEntry {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    {ev_p ev_e : List Event} (pre : TFlowSeqPrefix n c sp sp_d ev_p)
    (h_entry : TFlowSeqEntry n c sp_d sp_e ev_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    ∃ h' : TFlowSeqEntries n c sp sp' (ev_p ++ ev_e), TFlowSeqEntriesCloseable h' := by
  cases pre with
  | init =>
    rw [List.nil_append]
    exact ⟨.single _ _ _ _ _ _ h_entry h_sep, .single h_entry h_sep⟩
  | cons _ _ _ _ _ hcl hcomma hsep => exact TFlowSeqEntries_snoc hcl hcomma hsep h_entry h_sep

lemma TFlowMapPrefix.snocEntry {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    {ev_p ev_e : List Event} (pre : TFlowMapPrefix n c sp sp_d ev_p)
    (h_entry : TFlowMapEntry n c sp_d sp_e ev_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    ∃ h' : TFlowMapEntries n c sp sp' (ev_p ++ ev_e), TFlowMapEntriesCloseable h' := by
  cases pre with
  | init =>
    rw [List.nil_append]
    exact ⟨.single _ _ _ _ _ _ h_entry h_sep, .single h_entry h_sep⟩
  | cons _ _ _ _ _ hcl hcomma hsep => exact TFlowMapEntries_snoc hcl hcomma hsep h_entry h_sep

lemma TFlowSeqPrefix.appendEntry {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    {ev_p ev_e : List Event} (pre : TFlowSeqPrefix n c sp sp_d ev_p)
    (h_entry : TFlowSeqEntry n c sp_d sp_e ev_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    TPartialFlowSeq n c sp sp' (ev_p ++ ev_e) :=
  let ⟨h', hcl'⟩ := pre.snocEntry h_entry h_sep
  .entries _ _ _ h' hcl'

lemma TFlowMapPrefix.appendEntry {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    {ev_p ev_e : List Event} (pre : TFlowMapPrefix n c sp sp_d ev_p)
    (h_entry : TFlowMapEntry n c sp_d sp_e ev_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    TPartialFlowMap n c sp sp' (ev_p ++ ev_e) :=
  let ⟨h', hcl'⟩ := pre.snocEntry h_entry h_sep
  .entries _ _ _ h' hcl'

/-- A prefix plus a finished entry plus `,`: the held frame (`appendSeqEntryHeldFrame`). -/
lemma TFlowSeqPrefix.appendEntryHeld {n : Nat} {c : YamlContext} {sp sp_d sp_e sp_x sp_c sp' : SurfPos}
    {ev_p ev_e : List Event} (pre : TFlowSeqPrefix n c sp sp_d ev_p)
    (h_entry : TFlowSeqEntry n c sp_d sp_e ev_e) (h_sep_tr : GOpt (SSeparate n c) sp_e sp_x)
    (hcomma : GLit ',' sp_x sp_c) (h_sep_post : GOpt (SSeparate n c) sp_c sp') :
    TSeqFrame n c .sep sp sp' (ev_p ++ ev_e) :=
  let ⟨h', hcl'⟩ := pre.snocEntry h_entry h_sep_tr
  .betweenHeld _ _ _ _ _ h' hcl' hcomma h_sep_post

lemma TFlowMapPrefix.appendEntryHeld {n : Nat} {c : YamlContext} {sp sp_d sp_e sp_x sp_c sp' : SurfPos}
    {ev_p ev_e : List Event} (pre : TFlowMapPrefix n c sp sp_d ev_p)
    (h_entry : TFlowMapEntry n c sp_d sp_e ev_e) (h_sep_tr : GOpt (SSeparate n c) sp_e sp_x)
    (hcomma : GLit ',' sp_x sp_c) (h_sep_post : GOpt (SSeparate n c) sp_c sp') :
    TMapFrame n c .sep sp sp' (ev_p ++ ev_e) :=
  let ⟨h', hcl'⟩ := pre.snocEntry h_entry h_sep_tr
  .betweenHeld _ _ _ _ _ h' hcl' hcomma h_sep_post

/-- Finalize a partial flow sequence (`PartialFlowSeq.closeSeq`), trace kept. -/
lemma TPartialFlowSeq.closeSeq {n : Nat} {c_out : YamlContext} {sp_before sp_open sp_es sp_cur sp' : SurfPos}
    {ev : List Event} (h_open : GLit '[' sp_before sp_open)
    (h_sep : GOpt (SSeparate n c_out) sp_open sp_es)
    (p : TPartialFlowSeq n (inFlowCtx c_out) sp_es sp_cur ev) (h_close : GLit ']' sp_cur sp') :
    TFlowSequence n c_out sp_before sp' ev := by
  cases p with
  | empty => exact .empty _ _ _ _ _ _ h_open h_sep h_close
  | entries _ _ h _ => exact .nonempty _ _ _ _ _ _ _ _ h_open h_sep h h_close
  | held _ _ _ _ _ hcl hcomma hsep =>
    exact .nonempty _ _ _ _ _ _ _ _ h_open h_sep (TFlowSeqEntries_addTrailingComma hcl hcomma hsep) h_close

lemma TPartialFlowMap.closeMap {n : Nat} {c_out : YamlContext} {sp_before sp_open sp_es sp_cur sp' : SurfPos}
    {ev : List Event} (h_open : GLit '{' sp_before sp_open)
    (h_sep : GOpt (SSeparate n c_out) sp_open sp_es)
    (p : TPartialFlowMap n (inFlowCtx c_out) sp_es sp_cur ev) (h_close : GLit '}' sp_cur sp') :
    TFlowMapping n c_out sp_before sp' ev := by
  cases p with
  | empty => exact .empty _ _ _ _ _ _ h_open h_sep h_close
  | entries _ _ h _ => exact .nonempty _ _ _ _ _ _ _ _ h_open h_sep h h_close
  | held _ _ _ _ _ hcl hcomma hsep =>
    exact .nonempty _ _ _ _ _ _ _ _ h_open h_sep (TFlowMapEntries_addTrailingComma hcl hcomma hsep) h_close

/-! ## §5 The frame steps: `]` / `}` and `,` on every shape, trace preserved -/

/-- Every sequence shape closes at `]` after a separation lead (`SeqFrame.closeWithSep`). -/
lemma TSeqFrame.closeWithSep {n : Nat} {c_out : YamlContext} {tl : FrameTail}
    {sp_br sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_open : GLit '[' sp_br sp_open)
    (h_sep : GOpt (SSeparate n c_out) sp_open sp_es)
    (st : TSeqFrame n (inFlowCtx c_out) tl sp_es sp_flow ev)
    (h_lead_out : SSeparate n c_out sp_flow sp_prep)
    (h_lead_in : SSeparate n (inFlowCtx c_out) sp_flow sp_prep)
    (h_close : GLit ']' sp_prep sp_tok) :
    TFlowSequence n c_out sp_br sp_tok ev := by
  cases st with
  | betweenEmpty =>
    exact TPartialFlowSeq.closeSeq h_open (GOpt_SSeparate_extend h_sep h_lead_out) (.empty sp_prep) h_close
  | betweenEntries _ _ _ _ _ hcl =>
    obtain ⟨h', hcl'⟩ := TFlowSeqEntries_extendSep hcl h_lead_in
    exact TPartialFlowSeq.closeSeq h_open h_sep (.entries _ _ _ h' hcl') h_close
  | betweenHeld _ _ _ _ _ h hcl hcomma hsep =>
    exact TPartialFlowSeq.closeSeq h_open h_sep
      (.held _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend hsep h_lead_in)) h_close
  | midNode _ _ _ _ _ _ pre hnode _ =>
    exact TPartialFlowSeq.closeSeq h_open h_sep
      (pre.appendEntry (.node _ _ _ _ _ hnode) (.some _ _ h_lead_in)) h_close
  | midColon _ _ _ _ _ _ _ _ pre hkey _ hsep hcolon =>
    exact TPartialFlowSeq.closeSeq h_open h_sep
      (pre.appendEntry (.pairEmpty _ _ _ _ _ _ _ hkey hsep hcolon) (.some _ _ h_lead_in)) h_close
  | midExplicitKey _ _ _ _ _ _ _ _ pre hq hqsep hkey _ =>
    exact TPartialFlowSeq.closeSeq h_open h_sep
      (pre.appendEntry (.explicitPairKeyOnly _ _ _ _ _ _ _ hq hqsep hkey) (.some _ _ h_lead_in)) h_close
  | midExplicitColon _ _ _ _ _ _ _ _ _ _ pre hq hqsep hkey _ hsep hcolon =>
    exact TPartialFlowSeq.closeSeq h_open h_sep
      (pre.appendEntry (.explicitPairEmpty _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon)
        (.some _ _ h_lead_in)) h_close
  | midEmptyColon _ _ _ _ pre hcolon =>
    simpa using TPartialFlowSeq.closeSeq h_open h_sep
      (pre.appendEntry (.emptyKeyEmpty _ _ _ _ hcolon) (.some _ _ h_lead_in)) h_close
  | midQuestion _ _ _ _ pre hq =>
    simpa using TPartialFlowSeq.closeSeq h_open h_sep
      (pre.appendEntry (.explicitPairEmptyNodes _ _ _ _ _ hq h_lead_in) (GOpt.none sp_prep)) h_close
  | midQuestionEmptyColon _ _ _ _ _ _ pre hq hqsep hcolon =>
    simpa using TPartialFlowSeq.closeSeq h_open h_sep
      (pre.appendEntry (.explicitEmptyKeyEmpty _ _ _ _ _ _ hq hqsep hcolon) (.some _ _ h_lead_in)) h_close

/-- Every mapping shape closes at `}` after a separation lead (`MapFrame.closeWithSep`). -/
lemma TMapFrame.closeWithSep {n : Nat} {c_out : YamlContext} {tl : FrameTail}
    {sp_br sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_open : GLit '{' sp_br sp_open)
    (h_sep : GOpt (SSeparate n c_out) sp_open sp_es)
    (st : TMapFrame n (inFlowCtx c_out) tl sp_es sp_flow ev)
    (h_lead_out : SSeparate n c_out sp_flow sp_prep)
    (h_lead_in : SSeparate n (inFlowCtx c_out) sp_flow sp_prep)
    (h_close : GLit '}' sp_prep sp_tok) :
    TFlowMapping n c_out sp_br sp_tok ev := by
  cases st with
  | betweenEmpty =>
    exact TPartialFlowMap.closeMap h_open (GOpt_SSeparate_extend h_sep h_lead_out) (.empty sp_prep) h_close
  | betweenEntries _ _ _ _ _ hcl =>
    obtain ⟨h', hcl'⟩ := TFlowMapEntries_extendSep hcl h_lead_in
    exact TPartialFlowMap.closeMap h_open h_sep (.entries _ _ _ h' hcl') h_close
  | betweenHeld _ _ _ _ _ h hcl hcomma hsep =>
    exact TPartialFlowMap.closeMap h_open h_sep
      (.held _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend hsep h_lead_in)) h_close
  | midKey _ _ _ _ _ _ pre hkey _ =>
    exact TPartialFlowMap.closeMap h_open h_sep
      (pre.appendEntry (.bareKey _ _ _ _ _ hkey) (.some _ _ h_lead_in)) h_close
  | midColon _ _ _ _ _ _ _ _ pre hkey _ hsep hcolon =>
    exact TPartialFlowMap.closeMap h_open h_sep
      (pre.appendEntry (.implicitEmpty _ _ _ _ _ _ _ hkey hsep hcolon) (.some _ _ h_lead_in)) h_close
  | midExplicitKey _ _ _ _ _ _ _ _ pre hq hqsep hkey _ =>
    exact TPartialFlowMap.closeMap h_open h_sep
      (pre.appendEntry (.explicitKeyOnly _ _ _ _ _ _ _ hq hqsep hkey) (.some _ _ h_lead_in)) h_close
  | midExplicitColon _ _ _ _ _ _ _ _ _ _ pre hq hqsep hkey _ hsep hcolon =>
    exact TPartialFlowMap.closeMap h_open h_sep
      (pre.appendEntry (.explicitEmpty _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon)
        (.some _ _ h_lead_in)) h_close
  | midEmptyColon _ _ _ _ pre hcolon =>
    simpa using TPartialFlowMap.closeMap h_open h_sep
      (pre.appendEntry (.emptyKeyEmpty _ _ _ _ hcolon) (.some _ _ h_lead_in)) h_close
  | midQuestion _ _ _ _ pre hq =>
    simpa using TPartialFlowMap.closeMap h_open h_sep
      (pre.appendEntry (.explicitEmptyNodes _ _ _ _ _ hq h_lead_in) (GOpt.none sp_prep)) h_close
  | midQuestionEmptyColon _ _ _ _ _ _ pre hq hqsep hcolon =>
    simpa using TPartialFlowMap.closeMap h_open h_sep
      (pre.appendEntry (.explicitEmptyKeyEmpty _ _ _ _ _ _ hq hqsep hcolon) (.some _ _ h_lead_in)) h_close

/-- `closeWithSep` with the lead optional: a `closeFree` tail may sit glued to the `]`
    (`SeqFrame.closeLead`); after `?` the `[143]` separator is mandatory. -/
lemma TSeqFrame.closeLead {n : Nat} {c_out : YamlContext} {tl : FrameTail}
    {sp_br sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_open : GLit '[' sp_br sp_open)
    (h_sep : GOpt (SSeparate n c_out) sp_open sp_es)
    (st : TSeqFrame n (inFlowCtx c_out) tl sp_es sp_flow ev)
    (h_lead : (SSeparate n c_out sp_flow sp_prep ∧ SSeparate n (inFlowCtx c_out) sp_flow sp_prep) ∨
      (sp_prep = sp_flow ∧ tl.closeFree = true))
    (h_close : GLit ']' sp_prep sp_tok) :
    TFlowSequence n c_out sp_br sp_tok ev := by
  rcases h_lead with ⟨ho, hi⟩ | ⟨rfl, hfree⟩
  · exact TSeqFrame.closeWithSep h_open h_sep st ho hi h_close
  · cases st with
    | betweenEmpty => exact TPartialFlowSeq.closeSeq h_open h_sep (.empty _) h_close
    | betweenEntries _ _ _ _ h hcl => exact TPartialFlowSeq.closeSeq h_open h_sep (.entries _ _ _ h hcl) h_close
    | betweenHeld _ _ _ _ _ h hcl hcomma hsep =>
      exact TPartialFlowSeq.closeSeq h_open h_sep (.held _ _ _ _ _ h hcl hcomma hsep) h_close
    | midNode _ _ _ _ _ _ pre hnode _ =>
      exact TPartialFlowSeq.closeSeq h_open h_sep (pre.appendEntry (.node _ _ _ _ _ hnode) (GOpt.none _)) h_close
    | midColon _ _ _ _ _ _ _ _ pre hkey _ hsep hcolon =>
      exact TPartialFlowSeq.closeSeq h_open h_sep
        (pre.appendEntry (.pairEmpty _ _ _ _ _ _ _ hkey hsep hcolon) (GOpt.none _)) h_close
    | midExplicitKey _ _ _ _ _ _ _ _ pre hq hqsep hkey _ =>
      exact TPartialFlowSeq.closeSeq h_open h_sep
        (pre.appendEntry (.explicitPairKeyOnly _ _ _ _ _ _ _ hq hqsep hkey) (GOpt.none _)) h_close
    | midExplicitColon _ _ _ _ _ _ _ _ _ _ pre hq hqsep hkey _ hsep hcolon =>
      exact TPartialFlowSeq.closeSeq h_open h_sep
        (pre.appendEntry (.explicitPairEmpty _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon) (GOpt.none _)) h_close
    | midEmptyColon _ _ _ _ pre hcolon =>
      simpa using TPartialFlowSeq.closeSeq h_open h_sep
        (pre.appendEntry (.emptyKeyEmpty _ _ _ _ hcolon) (GOpt.none _)) h_close
    | midQuestion => simp [FrameTail.closeFree] at hfree
    | midQuestionEmptyColon _ _ _ _ _ _ pre hq hqsep hcolon =>
      simpa using TPartialFlowSeq.closeSeq h_open h_sep
        (pre.appendEntry (.explicitEmptyKeyEmpty _ _ _ _ _ _ hq hqsep hcolon) (GOpt.none _)) h_close

lemma TMapFrame.closeLead {n : Nat} {c_out : YamlContext} {tl : FrameTail}
    {sp_br sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_open : GLit '{' sp_br sp_open)
    (h_sep : GOpt (SSeparate n c_out) sp_open sp_es)
    (st : TMapFrame n (inFlowCtx c_out) tl sp_es sp_flow ev)
    (h_lead : (SSeparate n c_out sp_flow sp_prep ∧ SSeparate n (inFlowCtx c_out) sp_flow sp_prep) ∨
      (sp_prep = sp_flow ∧ tl.closeFree = true))
    (h_close : GLit '}' sp_prep sp_tok) :
    TFlowMapping n c_out sp_br sp_tok ev := by
  rcases h_lead with ⟨ho, hi⟩ | ⟨rfl, hfree⟩
  · exact TMapFrame.closeWithSep h_open h_sep st ho hi h_close
  · cases st with
    | betweenEmpty => exact TPartialFlowMap.closeMap h_open h_sep (.empty _) h_close
    | betweenEntries _ _ _ _ h hcl => exact TPartialFlowMap.closeMap h_open h_sep (.entries _ _ _ h hcl) h_close
    | betweenHeld _ _ _ _ _ h hcl hcomma hsep =>
      exact TPartialFlowMap.closeMap h_open h_sep (.held _ _ _ _ _ h hcl hcomma hsep) h_close
    | midKey _ _ _ _ _ _ pre hkey _ =>
      exact TPartialFlowMap.closeMap h_open h_sep (pre.appendEntry (.bareKey _ _ _ _ _ hkey) (GOpt.none _)) h_close
    | midColon _ _ _ _ _ _ _ _ pre hkey _ hsep hcolon =>
      exact TPartialFlowMap.closeMap h_open h_sep
        (pre.appendEntry (.implicitEmpty _ _ _ _ _ _ _ hkey hsep hcolon) (GOpt.none _)) h_close
    | midExplicitKey _ _ _ _ _ _ _ _ pre hq hqsep hkey _ =>
      exact TPartialFlowMap.closeMap h_open h_sep
        (pre.appendEntry (.explicitKeyOnly _ _ _ _ _ _ _ hq hqsep hkey) (GOpt.none _)) h_close
    | midExplicitColon _ _ _ _ _ _ _ _ _ _ pre hq hqsep hkey _ hsep hcolon =>
      exact TPartialFlowMap.closeMap h_open h_sep
        (pre.appendEntry (.explicitEmpty _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon) (GOpt.none _)) h_close
    | midEmptyColon _ _ _ _ pre hcolon =>
      simpa using TPartialFlowMap.closeMap h_open h_sep
        (pre.appendEntry (.emptyKeyEmpty _ _ _ _ hcolon) (GOpt.none _)) h_close
    | midQuestion => simp [FrameTail.closeFree] at hfree
    | midQuestionEmptyColon _ _ _ _ _ _ pre hq hqsep hcolon =>
      simpa using TPartialFlowMap.closeMap h_open h_sep
        (pre.appendEntry (.explicitEmptyKeyEmpty _ _ _ _ _ _ hq hqsep hcolon) (GOpt.none _)) h_close

/-- `,` on a non-`sep` sequence tail commits the open entry; the trace is unchanged
    (`SeqFrame.holdComma`). -/
lemma TSeqFrame.holdComma {n : Nat} {c : YamlContext} {tl : FrameTail}
    {sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (st : TSeqFrame n c tl sp_es sp_flow ev) (h_tail : tl ≠ .sep)
    (h_lead : SSeparate n c sp_flow sp_prep) (hcomma : GLit ',' sp_prep sp_tok) :
    TSeqFrame n c .sep sp_es sp_tok ev := by
  cases st with
  | betweenEmpty => exact absurd rfl h_tail
  | betweenEntries _ _ _ _ _ hcl =>
    obtain ⟨h', hcl'⟩ := TFlowSeqEntries_extendSep hcl h_lead
    exact .betweenHeld _ _ _ _ _ h' hcl' hcomma (GOpt.none sp_tok)
  | betweenHeld => exact absurd rfl h_tail
  | midNode _ _ _ _ _ _ pre hnode _ =>
    exact pre.appendEntryHeld (.node _ _ _ _ _ hnode) (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  | midColon _ _ _ _ _ _ _ _ pre hkey _ hsep hcolon =>
    exact pre.appendEntryHeld (.pairEmpty _ _ _ _ _ _ _ hkey hsep hcolon) (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  | midExplicitKey _ _ _ _ _ _ _ _ pre hq hqsep hkey _ =>
    exact pre.appendEntryHeld (.explicitPairKeyOnly _ _ _ _ _ _ _ hq hqsep hkey) (.some _ _ h_lead) hcomma
      (GOpt.none sp_tok)
  | midExplicitColon _ _ _ _ _ _ _ _ _ _ pre hq hqsep hkey _ hsep hcolon =>
    exact pre.appendEntryHeld (.explicitPairEmpty _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  | midEmptyColon _ _ _ _ pre hcolon =>
    simpa using pre.appendEntryHeld (.emptyKeyEmpty _ _ _ _ hcolon) (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  | midQuestion _ _ _ _ pre hq =>
    simpa using pre.appendEntryHeld (.explicitPairEmptyNodes _ _ _ _ _ hq h_lead) (GOpt.none sp_prep) hcomma
      (GOpt.none sp_tok)
  | midQuestionEmptyColon _ _ _ _ _ _ pre hq hqsep hcolon =>
    simpa using pre.appendEntryHeld (.explicitEmptyKeyEmpty _ _ _ _ _ _ hq hqsep hcolon) (.some _ _ h_lead)
      hcomma (GOpt.none sp_tok)

lemma TMapFrame.holdComma {n : Nat} {c : YamlContext} {tl : FrameTail}
    {sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (st : TMapFrame n c tl sp_es sp_flow ev) (h_tail : tl ≠ .sep)
    (h_lead : SSeparate n c sp_flow sp_prep) (hcomma : GLit ',' sp_prep sp_tok) :
    TMapFrame n c .sep sp_es sp_tok ev := by
  cases st with
  | betweenEmpty => exact absurd rfl h_tail
  | betweenEntries _ _ _ _ _ hcl =>
    obtain ⟨h', hcl'⟩ := TFlowMapEntries_extendSep hcl h_lead
    exact .betweenHeld _ _ _ _ _ h' hcl' hcomma (GOpt.none sp_tok)
  | betweenHeld => exact absurd rfl h_tail
  | midKey _ _ _ _ _ _ pre hkey _ =>
    exact pre.appendEntryHeld (.bareKey _ _ _ _ _ hkey) (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  | midColon _ _ _ _ _ _ _ _ pre hkey _ hsep hcolon =>
    exact pre.appendEntryHeld (.implicitEmpty _ _ _ _ _ _ _ hkey hsep hcolon) (.some _ _ h_lead) hcomma
      (GOpt.none sp_tok)
  | midExplicitKey _ _ _ _ _ _ _ _ pre hq hqsep hkey _ =>
    exact pre.appendEntryHeld (.explicitKeyOnly _ _ _ _ _ _ _ hq hqsep hkey) (.some _ _ h_lead) hcomma
      (GOpt.none sp_tok)
  | midExplicitColon _ _ _ _ _ _ _ _ _ _ pre hq hqsep hkey _ hsep hcolon =>
    exact pre.appendEntryHeld (.explicitEmpty _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon)
      (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  | midEmptyColon _ _ _ _ pre hcolon =>
    simpa using pre.appendEntryHeld (.emptyKeyEmpty _ _ _ _ hcolon) (.some _ _ h_lead) hcomma (GOpt.none sp_tok)
  | midQuestion _ _ _ _ pre hq =>
    simpa using pre.appendEntryHeld (.explicitEmptyNodes _ _ _ _ _ hq h_lead) (GOpt.none sp_prep) hcomma
      (GOpt.none sp_tok)
  | midQuestionEmptyColon _ _ _ _ _ _ pre hq hqsep hcolon =>
    simpa using pre.appendEntryHeld (.explicitEmptyKeyEmpty _ _ _ _ _ _ hq hqsep hcolon) (.some _ _ h_lead)
      hcomma (GOpt.none sp_tok)

/-- `holdComma` with the lead optional: a `closeFree` tail may sit glued to the `,`
    (`SeqFrame.holdCommaLead`). -/
lemma TSeqFrame.holdCommaLead {n : Nat} {c : YamlContext} {tl : FrameTail}
    {sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (st : TSeqFrame n c tl sp_es sp_flow ev) (h_tail : tl ≠ .sep)
    (h_lead : SSeparate n c sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.closeFree = true))
    (hcomma : GLit ',' sp_prep sp_tok) :
    TSeqFrame n c .sep sp_es sp_tok ev := by
  rcases h_lead with h | ⟨rfl, hfree⟩
  · exact st.holdComma h_tail h hcomma
  · cases st with
    | betweenEmpty => exact absurd rfl h_tail
    | betweenEntries _ _ _ _ h hcl => exact .betweenHeld _ _ _ _ _ h hcl hcomma (GOpt.none sp_tok)
    | betweenHeld => exact absurd rfl h_tail
    | midNode _ _ _ _ _ _ pre hnode _ =>
      exact pre.appendEntryHeld (.node _ _ _ _ _ hnode) (GOpt.none _) hcomma (GOpt.none sp_tok)
    | midColon _ _ _ _ _ _ _ _ pre hkey _ hsep hcolon =>
      exact pre.appendEntryHeld (.pairEmpty _ _ _ _ _ _ _ hkey hsep hcolon) (GOpt.none _) hcomma (GOpt.none sp_tok)
    | midExplicitKey _ _ _ _ _ _ _ _ pre hq hqsep hkey _ =>
      exact pre.appendEntryHeld (.explicitPairKeyOnly _ _ _ _ _ _ _ hq hqsep hkey) (GOpt.none _) hcomma
        (GOpt.none sp_tok)
    | midExplicitColon _ _ _ _ _ _ _ _ _ _ pre hq hqsep hkey _ hsep hcolon =>
      exact pre.appendEntryHeld (.explicitPairEmpty _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon)
        (GOpt.none _) hcomma (GOpt.none sp_tok)
    | midEmptyColon _ _ _ _ pre hcolon =>
      simpa using pre.appendEntryHeld (.emptyKeyEmpty _ _ _ _ hcolon) (GOpt.none _) hcomma (GOpt.none sp_tok)
    | midQuestion => simp [FrameTail.closeFree] at hfree
    | midQuestionEmptyColon _ _ _ _ _ _ pre hq hqsep hcolon =>
      simpa using pre.appendEntryHeld (.explicitEmptyKeyEmpty _ _ _ _ _ _ hq hqsep hcolon) (GOpt.none _)
        hcomma (GOpt.none sp_tok)

lemma TMapFrame.holdCommaLead {n : Nat} {c : YamlContext} {tl : FrameTail}
    {sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (st : TMapFrame n c tl sp_es sp_flow ev) (h_tail : tl ≠ .sep)
    (h_lead : SSeparate n c sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.closeFree = true))
    (hcomma : GLit ',' sp_prep sp_tok) :
    TMapFrame n c .sep sp_es sp_tok ev := by
  rcases h_lead with h | ⟨rfl, hfree⟩
  · exact st.holdComma h_tail h hcomma
  · cases st with
    | betweenEmpty => exact absurd rfl h_tail
    | betweenEntries _ _ _ _ h hcl => exact .betweenHeld _ _ _ _ _ h hcl hcomma (GOpt.none sp_tok)
    | betweenHeld => exact absurd rfl h_tail
    | midKey _ _ _ _ _ _ pre hkey _ =>
      exact pre.appendEntryHeld (.bareKey _ _ _ _ _ hkey) (GOpt.none _) hcomma (GOpt.none sp_tok)
    | midColon _ _ _ _ _ _ _ _ pre hkey _ hsep hcolon =>
      exact pre.appendEntryHeld (.implicitEmpty _ _ _ _ _ _ _ hkey hsep hcolon) (GOpt.none _) hcomma
        (GOpt.none sp_tok)
    | midExplicitKey _ _ _ _ _ _ _ _ pre hq hqsep hkey _ =>
      exact pre.appendEntryHeld (.explicitKeyOnly _ _ _ _ _ _ _ hq hqsep hkey) (GOpt.none _) hcomma
        (GOpt.none sp_tok)
    | midExplicitColon _ _ _ _ _ _ _ _ _ _ pre hq hqsep hkey _ hsep hcolon =>
      exact pre.appendEntryHeld (.explicitEmpty _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon)
        (GOpt.none _) hcomma (GOpt.none sp_tok)
    | midEmptyColon _ _ _ _ pre hcolon =>
      simpa using pre.appendEntryHeld (.emptyKeyEmpty _ _ _ _ hcolon) (GOpt.none _) hcomma (GOpt.none sp_tok)
    | midQuestion => simp [FrameTail.closeFree] at hfree
    | midQuestionEmptyColon _ _ _ _ _ _ pre hq hqsep hcolon =>
      simpa using pre.appendEntryHeld (.explicitEmptyKeyEmpty _ _ _ _ _ _ hq hqsep hcolon) (GOpt.none _)
        hcomma (GOpt.none sp_tok)


/-! ## §6 The receive steps: a node / `?` / `:` into the top frame (PR 2b-i)

    T twins of `FlowOpenStack.receive*` (`StreamAccum` §1c''): the frame moves `between → mid`
    (the node is a new entry / key), `mid …Colon → between` (the node is the awaited value),
    `between → midQuestion` / `midEmptyColon`, `midNode → midColon`, …, and the stack's trace
    grows by EXACTLY the node's events (`ev ++ ev_n`); `?` and `:` add nothing.  Each step is a
    frame lemma (one per frame kind, the 10-way shape split, context-generic) lifted to the
    stack by `TFlowOpenStack.liftTop`.  The frame lemmas return the opener's separation
    re-read: on `betweenEmpty` the lead is absorbed into the `[`/`{`'s trailing `s-separate?`
    (`GOpt_SSeparate_extend_free`), elsewhere it rides inside the frame. -/

open L4YAML.Proofs.StreamAccum (GOpt_SSeparate_extend_free lead_of_not_free GOpt_of_lead)

lemma TSeqFrame.retrace {n : Nat} {c : YamlContext} {tl : FrameTail} {a b : SurfPos}
    {ev ev' : List Event} (h : ev = ev') (st : TSeqFrame n c tl a b ev) : TSeqFrame n c tl a b ev' :=
  h ▸ st

lemma TMapFrame.retrace {n : Nat} {c : YamlContext} {tl : FrameTail} {a b : SurfPos}
    {ev ev' : List Event} (h : ev = ev') (st : TMapFrame n c tl a b ev) : TMapFrame n c tl a b ev' :=
  h ▸ st

lemma TFlowOpenStack.retrace {n D : Nat} {ks : Array Bool} {tl : FrameTail} {a b : SurfPos}
    {ev ev' : List Event} (h : ev = ev') (st : TFlowOpenStack n D ks tl a b ev) :
    TFlowOpenStack n D ks tl a b ev' :=
  h ▸ st

/-- A prefix plus a finished entry: the `.value`-tailed `betweenEntries` frame
    (`appendSeqEntryFrame`), trace `ev_p ++ ev_e`. -/
lemma TFlowSeqPrefix.appendEntryFrame {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    {ev_p ev_e : List Event} {kj : Bool} (pre : TFlowSeqPrefix n c sp sp_d ev_p)
    (h_entry : TFlowSeqEntry n c sp_d sp_e ev_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    TSeqFrame n c (.value kj) sp sp' (ev_p ++ ev_e) :=
  let ⟨h', hcl'⟩ := pre.snocEntry h_entry h_sep
  .betweenEntries kj _ _ _ h' hcl'

lemma TFlowMapPrefix.appendEntryFrame {n : Nat} {c : YamlContext} {sp sp_d sp_e sp' : SurfPos}
    {ev_p ev_e : List Event} {kj : Bool} (pre : TFlowMapPrefix n c sp sp_d ev_p)
    (h_entry : TFlowMapEntry n c sp_d sp_e ev_e) (h_sep : GOpt (SSeparate n c) sp_e sp') :
    TMapFrame n c (.value kj) sp sp' (ev_p ++ ev_e) :=
  let ⟨h', hcl'⟩ := pre.snocEntry h_entry h_sep
  .betweenEntries kj _ _ _ h' hcl'

/-! ### §6a The frame steps (`SeqFrame` / `MapFrame` side of each receive) -/

/-- A node into a sequence frame that is not `.value`-tailed (`receiveNode`'s frame half):
    `between* → midNode`, `midQuestion → midExplicitKey`, `mid*Colon → betweenEntries`. -/
lemma TSeqFrame.receiveNode {n : Nat} {tl : FrameTail}
    {sp_open sp_es sp_flow sp_prep sp_ne : SurfPos} {ev ev_n : List Event} {kj : Bool}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn tl sp_es sp_flow ev) (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (h_node : TFlowNode n .flowIn sp_prep sp_ne ev_n)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_prep sp_ne ev_n) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
      TSeqFrame n .flowIn (.value kj) sp_es' sp_ne (ev ++ ev_n) := by
  cases st with
  | betweenEmpty sp => exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midNode kj _ _ _ _ _ (.init sp_prep) h_node hjson⟩
  | betweenEntries _ _ _ _ _ _ => exact absurd rfl (h_tail _)
  | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
    exact ⟨_, h_sep, .midNode kj _ _ _ _ _
      (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead)) h_node hjson⟩
  | midNode _ _ _ _ _ _ _ _ _ => exact absurd rfl (h_tail _)
  | midColon kj' sp sp_d sp_k sp_s sp' ev_p ev_k pre hkey hjson' hsep hcolon =>
    rcases h_lead with h_lead | ⟨rfl, hkj⟩
    · exact ⟨_, h_sep, by rw [List.append_assoc]; exact
        (pre.appendEntryFrame (.pairValue _ _ _ _ _ _ _ _ _ _ hkey hsep hcolon h_lead h_node) (GOpt.none _))⟩
    · exact ⟨_, h_sep, by rw [List.append_assoc]; exact
        (pre.appendEntryFrame
          (.pairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ (hjson' hkj) hsep hcolon (GOpt.none _) h_node)
          (GOpt.none _))⟩
  | midExplicitKey _ _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (h_tail _)
  | midExplicitColon kj' sp sp_q sp_qe sp_k0 sp_k sp_s sp' ev_p ev_k pre hq hqsep hkey hjson' hsep hcolon =>
    rcases h_lead with h_lead | ⟨rfl, hkj⟩
    · exact ⟨_, h_sep, by rw [List.append_assoc]; exact
        (pre.appendEntryFrame
          (.explicitPairValue _ _ _ _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon h_lead h_node) (GOpt.none _))⟩
    · exact ⟨_, h_sep, by rw [List.append_assoc]; exact
        (pre.appendEntryFrame
          (.explicitPairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ _ _ hq hqsep (hjson' hkj) hsep hcolon
            (GOpt.none _) h_node)
          (GOpt.none _))⟩
  | midEmptyColon sp sp_s sp' ev_p pre hcolon =>
    exact ⟨_, h_sep, pre.appendEntryFrame
      (.emptyKeyValue _ _ _ _ _ _ _ hcolon (lead_of_not_free h_lead Bool.false_ne_true) h_node)
      (GOpt.none _)⟩
  | midQuestion sp sp_q sp' ev_p pre hq =>
    exact ⟨_, h_sep, .midExplicitKey kj _ _ _ _ _ _ _ pre hq
      (lead_of_not_free h_lead Bool.false_ne_true) h_node hjson⟩
  | midQuestionEmptyColon sp sp_q sp_qe sp_s sp' ev_p pre hq hqsep hcolon =>
    exact ⟨_, h_sep, pre.appendEntryFrame
      (.explicitEmptyKeyValue _ _ _ _ _ _ _ _ _ hq hqsep hcolon
        (lead_of_not_free h_lead Bool.false_ne_true) h_node)
      (GOpt.none _)⟩

lemma TMapFrame.receiveNode {n : Nat} {tl : FrameTail}
    {sp_open sp_es sp_flow sp_prep sp_ne : SurfPos} {ev ev_n : List Event} {kj : Bool}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn tl sp_es sp_flow ev) (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (h_node : TFlowNode n .flowIn sp_prep sp_ne ev_n)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_prep sp_ne ev_n) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
      TMapFrame n .flowIn (.value kj) sp_es' sp_ne (ev ++ ev_n) := by
  cases st with
  | betweenEmpty sp => exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midKey kj _ _ _ _ _ (.init sp_prep) h_node hjson⟩
  | betweenEntries _ _ _ _ _ _ => exact absurd rfl (h_tail _)
  | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
    exact ⟨_, h_sep, .midKey kj _ _ _ _ _
      (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead)) h_node hjson⟩
  | midKey _ _ _ _ _ _ _ _ _ => exact absurd rfl (h_tail _)
  | midColon kj' sp sp_d sp_k sp_s sp' ev_p ev_k pre hkey hjson' hsep hcolon =>
    rcases h_lead with h_lead | ⟨rfl, hkj⟩
    · exact ⟨_, h_sep, by rw [List.append_assoc]; exact
        (pre.appendEntryFrame (.implicitValue _ _ _ _ _ _ _ _ _ _ hkey hsep hcolon h_lead h_node) (GOpt.none _))⟩
    · exact ⟨_, h_sep, by rw [List.append_assoc]; exact
        (pre.appendEntryFrame
          (.jsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ (hjson' hkj) hsep hcolon (GOpt.none _) h_node)
          (GOpt.none _))⟩
  | midExplicitKey _ _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd rfl (h_tail _)
  | midExplicitColon kj' sp sp_q sp_qe sp_k0 sp_k sp_s sp' ev_p ev_k pre hq hqsep hkey hjson' hsep hcolon =>
    rcases h_lead with h_lead | ⟨rfl, hkj⟩
    · exact ⟨_, h_sep, by rw [List.append_assoc]; exact
        (pre.appendEntryFrame
          (.explicitValue _ _ _ _ _ _ _ _ _ _ _ _ hq hqsep hkey hsep hcolon h_lead h_node) (GOpt.none _))⟩
    · exact ⟨_, h_sep, by rw [List.append_assoc]; exact
        (pre.appendEntryFrame
          (.explicitJsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ _ _ hq hqsep (hjson' hkj) hsep hcolon
            (GOpt.none _) h_node)
          (GOpt.none _))⟩
  | midEmptyColon sp sp_s sp' ev_p pre hcolon =>
    exact ⟨_, h_sep, pre.appendEntryFrame
      (.emptyKeyValue _ _ _ _ _ _ _ hcolon (lead_of_not_free h_lead Bool.false_ne_true) h_node)
      (GOpt.none _)⟩
  | midQuestion sp sp_q sp' ev_p pre hq =>
    exact ⟨_, h_sep, .midExplicitKey kj _ _ _ _ _ _ _ pre hq
      (lead_of_not_free h_lead Bool.false_ne_true) h_node hjson⟩
  | midQuestionEmptyColon sp sp_q sp_qe sp_s sp' ev_p pre hq hqsep hcolon =>
    exact ⟨_, h_sep, pre.appendEntryFrame
      (.explicitEmptyKeyValue _ _ _ _ _ _ _ _ _ hq hqsep hcolon
        (lead_of_not_free h_lead Bool.false_ne_true) h_node)
      (GOpt.none _)⟩

/-- `?` into a `.sep`-tailed frame (`receiveQuestion`): `between* → midQuestion`, trace kept. -/
lemma TSeqFrame.receiveQuestion {n : Nat} 
    {sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn .sep sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ FrameTail.leadFree .sep))
    (hq : GLit '?' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧ TSeqFrame n .flowIn .question sp_es' sp_tok ev := by
  cases st with
  | betweenEmpty sp => exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midQuestion _ _ _ _ (.init sp_prep) hq⟩
  | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
    exact ⟨_, h_sep, .midQuestion _ _ _ _
      (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead)) hq⟩

lemma TMapFrame.receiveQuestion {n : Nat} 
    {sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn .sep sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ FrameTail.leadFree .sep))
    (hq : GLit '?' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧ TMapFrame n .flowIn .question sp_es' sp_tok ev := by
  cases st with
  | betweenEmpty sp => exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midQuestion _ _ _ _ (.init sp_prep) hq⟩
  | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
    exact ⟨_, h_sep, .midQuestion _ _ _ _
      (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead)) hq⟩

/-- `:` into a `.sep`-tailed frame (`receiveColonSep`, `[146]`'s empty key): `between* →
    midEmptyColon`, trace kept. -/
lemma TSeqFrame.receiveColonSep {n : Nat} 
    {sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn .sep sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ FrameTail.leadFree .sep))
    (hcolon : GLit ':' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧ TSeqFrame n .flowIn (.colon false) sp_es' sp_tok ev := by
  cases st with
  | betweenEmpty sp => exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midEmptyColon _ _ _ _ (.init sp_prep) hcolon⟩
  | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
    exact ⟨_, h_sep, .midEmptyColon _ _ _ _
      (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead)) hcolon⟩

lemma TMapFrame.receiveColonSep {n : Nat} 
    {sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn .sep sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ FrameTail.leadFree .sep))
    (hcolon : GLit ':' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧ TMapFrame n .flowIn (.colon false) sp_es' sp_tok ev := by
  cases st with
  | betweenEmpty sp => exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midEmptyColon _ _ _ _ (.init sp_prep) hcolon⟩
  | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
    exact ⟨_, h_sep, .midEmptyColon _ _ _ _
      (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead)) hcolon⟩

/-- `:` into a `.question`-tailed frame (`receiveColonQuestion`, `[? :`): `midQuestion →
    midQuestionEmptyColon`; the `?`'s mandatory separation is this step's lead. -/
lemma TSeqFrame.receiveColonQuestion {n : Nat} 
    {sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn .question sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ FrameTail.leadFree .question))
    (hcolon : GLit ':' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧ TSeqFrame n .flowIn (.colon false) sp_es' sp_tok ev := by
  cases st with
  | midQuestion sp sp_q sp' ev_p pre hq =>
    exact ⟨_, h_sep, .midQuestionEmptyColon _ _ _ _ _ _ pre hq
      (lead_of_not_free h_lead Bool.false_ne_true) hcolon⟩

lemma TMapFrame.receiveColonQuestion {n : Nat} 
    {sp_open sp_es sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn .question sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ FrameTail.leadFree .question))
    (hcolon : GLit ':' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧ TMapFrame n .flowIn (.colon false) sp_es' sp_tok ev := by
  cases st with
  | midQuestion sp sp_q sp' ev_p pre hq =>
    exact ⟨_, h_sep, .midQuestionEmptyColon _ _ _ _ _ _ pre hq
      (lead_of_not_free h_lead Bool.false_ne_true) hcolon⟩

/-- A held property run then `:` on a `.sep` tail (`receiveColonPropsSep`, `[&a : b]`): the run
    is the KEY (`[96]` + `e-scalar`), `between* → midColon`, trace grown by the run's. -/
lemma TSeqFrame.receiveColonPropsSep {n : Nat} 
    {sp_open sp_es sp_flow sp_p sp_end sp_prep sp_tok : SurfPos} {ev ev_p : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn .sep sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_p ∨ (sp_p = sp_flow ∧ FrameTail.leadFree .sep))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_gap : GOpt (SSeparate n .flowIn) sp_end sp_prep) (hcolon : GLit ':' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
      TSeqFrame n .flowIn (.colon false) sp_es' sp_tok (ev ++ ev_p) := by
  cases st with
  | betweenEmpty sp =>
    exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midColon false _ _ _ _ _ _ _ (.init sp_p) (.propsEmpty _ _ _ _ _ h_props)
      (fun h => nomatch h) h_gap hcolon⟩
  | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
    exact ⟨_, h_sep, .midColon false _ _ _ _ _ _ _
      (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead))
      (.propsEmpty _ _ _ _ _ h_props) (fun h => nomatch h) h_gap hcolon⟩

lemma TMapFrame.receiveColonPropsSep {n : Nat} 
    {sp_open sp_es sp_flow sp_p sp_end sp_prep sp_tok : SurfPos} {ev ev_p : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn .sep sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_p ∨ (sp_p = sp_flow ∧ FrameTail.leadFree .sep))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_gap : GOpt (SSeparate n .flowIn) sp_end sp_prep) (hcolon : GLit ':' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
      TMapFrame n .flowIn (.colon false) sp_es' sp_tok (ev ++ ev_p) := by
  cases st with
  | betweenEmpty sp =>
    exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midColon false _ _ _ _ _ _ _ (.init sp_p) (.propsEmpty _ _ _ _ _ h_props)
      (fun h => nomatch h) h_gap hcolon⟩
  | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
    exact ⟨_, h_sep, .midColon false _ _ _ _ _ _ _
      (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead))
      (.propsEmpty _ _ _ _ _ h_props) (fun h => nomatch h) h_gap hcolon⟩

/-- A held run then `:` on a `.question` tail (`receiveColonPropsQuestion`, `[? &a : b]`): the
    run is the explicit key, `midQuestion → midExplicitColon`. -/
lemma TSeqFrame.receiveColonPropsQuestion {n : Nat} 
    {sp_open sp_es sp_flow sp_p sp_end sp_prep sp_tok : SurfPos} {ev ev_p : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn .question sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_p ∨ (sp_p = sp_flow ∧ FrameTail.leadFree .question))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_gap : GOpt (SSeparate n .flowIn) sp_end sp_prep) (hcolon : GLit ':' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
      TSeqFrame n .flowIn (.colon false) sp_es' sp_tok (ev ++ ev_p) := by
  cases st with
  | midQuestion sp sp_q sp' ev_q pre hq =>
    exact ⟨_, h_sep, .midExplicitColon false _ _ _ _ _ _ _ _ _ pre hq
      (lead_of_not_free h_lead Bool.false_ne_true) (.propsEmpty _ _ _ _ _ h_props)
      (fun h => nomatch h) h_gap hcolon⟩

lemma TMapFrame.receiveColonPropsQuestion {n : Nat} 
    {sp_open sp_es sp_flow sp_p sp_end sp_prep sp_tok : SurfPos} {ev ev_p : List Event}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn .question sp_es sp_flow ev)
    (h_lead : SSeparate n .flowIn sp_flow sp_p ∨ (sp_p = sp_flow ∧ FrameTail.leadFree .question))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_gap : GOpt (SSeparate n .flowIn) sp_end sp_prep) (hcolon : GLit ':' sp_prep sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
      TMapFrame n .flowIn (.colon false) sp_es' sp_tok (ev ++ ev_p) := by
  cases st with
  | midQuestion sp sp_q sp' ev_q pre hq =>
    exact ⟨_, h_sep, .midExplicitColon false _ _ _ _ _ _ _ _ _ pre hq
      (lead_of_not_free h_lead Bool.false_ne_true) (.propsEmpty _ _ _ _ _ h_props)
      (fun h => nomatch h) h_gap hcolon⟩

/-- A node AND its `:` in one step (`receiveNodeColon`, item 10's `receiveColonValue`): on a
    `.sep` tail `between* → midColon`, on `.question` `midQuestion → midExplicitColon`; trace
    grown by the key's. -/
lemma TSeqFrame.receiveNodeColon {n : Nat} {tl : FrameTail}
    {sp_open sp_es sp_flow sp_prep sp_ne sp_prep₂ sp_tok : SurfPos} {ev ev_n : List Event} {kj : Bool}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TSeqFrame n .flowIn tl sp_es sp_flow ev) (h_tail : tl = .sep ∨ tl = .question)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (h_node : TFlowNode n .flowIn sp_prep sp_ne ev_n)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_prep sp_ne ev_n)
    (h_lead₂ : SSeparate n .flowIn sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne)
    (hcolon : GLit ':' sp_prep₂ sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
      TSeqFrame n .flowIn (.colon kj) sp_es' sp_tok (ev ++ ev_n) := by
  have h_gap : GOpt (SSeparate n .flowIn) sp_ne sp_prep₂ :=
    GOpt_of_lead (Q := True) (h_lead₂.imp id (fun h => ⟨h, trivial⟩))
  rcases h_tail with rfl | rfl
  · cases st with
    | betweenEmpty sp =>
      exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midColon kj _ _ _ _ _ _ _ (.init sp_prep) h_node hjson h_gap hcolon⟩
    | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
      exact ⟨_, h_sep, .midColon kj _ _ _ _ _ _ _
        (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead)) h_node hjson h_gap hcolon⟩
  · cases st with
    | midQuestion sp sp_q sp' ev_p pre hq =>
      exact ⟨_, h_sep, .midExplicitColon kj _ _ _ _ _ _ _ _ _ pre hq
        (lead_of_not_free h_lead Bool.false_ne_true) h_node hjson h_gap hcolon⟩

lemma TMapFrame.receiveNodeColon {n : Nat} {tl : FrameTail}
    {sp_open sp_es sp_flow sp_prep sp_ne sp_prep₂ sp_tok : SurfPos} {ev ev_n : List Event} {kj : Bool}
    (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
    (st : TMapFrame n .flowIn tl sp_es sp_flow ev) (h_tail : tl = .sep ∨ tl = .question)
    (h_lead : SSeparate n .flowIn sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (h_node : TFlowNode n .flowIn sp_prep sp_ne ev_n)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_prep sp_ne ev_n)
    (h_lead₂ : SSeparate n .flowIn sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne)
    (hcolon : GLit ':' sp_prep₂ sp_tok) :
    ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
      TMapFrame n .flowIn (.colon kj) sp_es' sp_tok (ev ++ ev_n) := by
  have h_gap : GOpt (SSeparate n .flowIn) sp_ne sp_prep₂ :=
    GOpt_of_lead (Q := True) (h_lead₂.imp id (fun h => ⟨h, trivial⟩))
  rcases h_tail with rfl | rfl
  · cases st with
    | betweenEmpty sp =>
      exact ⟨_, GOpt_SSeparate_extend_free h_sep h_lead, .midColon kj _ _ _ _ _ _ _ (.init sp_prep) h_node hjson h_gap hcolon⟩
    | betweenHeld sp sp_e sp_c sp' ev h hcl hcomma hsep =>
      exact ⟨_, h_sep, .midColon kj _ _ _ _ _ _ _
        (.cons _ _ _ _ _ h hcl hcomma (GOpt_SSeparate_extend_free hsep h_lead)) h_node hjson h_gap hcolon⟩
  · cases st with
    | midQuestion sp sp_q sp' ev_p pre hq =>
      exact ⟨_, h_sep, .midExplicitColon kj _ _ _ _ _ _ _ _ _ pre hq
        (lead_of_not_free h_lead Bool.false_ne_true) h_node hjson h_gap hcolon⟩

/-! ### §6b The stack: lift a top-frame step through `TFlowOpenStack` -/

/-- Lift a step of the TOP frame (given as the two frame-kind halves, each re-reading the
    opener's separation) through the open stack.  The base frames sit at `inFlowCtx .flowOut`
    and the nests at `.flowIn`, both `.flowIn` definitionally, and both openers' separations
    are `s-separate-lines`, so one `.flowIn`-typed step serves all four constructors; a nest's
    parent and its trace prefix ride unchanged. -/
lemma TFlowOpenStack.liftTop {n D : Nat} {ks : Array Bool} {tl tl' : FrameTail}
    {sp_block sp_flow sp_new : SurfPos} {ev delta : List Event}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (fs : ∀ {sp_open sp_es : SurfPos} {ev_f : List Event},
      GOpt (SSeparate n .flowIn) sp_open sp_es → TSeqFrame n .flowIn tl sp_es sp_flow ev_f →
      ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
        TSeqFrame n .flowIn tl' sp_es' sp_new (ev_f ++ delta))
    (fm : ∀ {sp_open sp_es : SurfPos} {ev_f : List Event},
      GOpt (SSeparate n .flowIn) sp_open sp_es → TMapFrame n .flowIn tl sp_es sp_flow ev_f →
      ∃ sp_es', GOpt (SSeparate n .flowIn) sp_open sp_es' ∧
        TMapFrame n .flowIn tl' sp_es' sp_new (ev_f ++ delta)) :
    TFlowOpenStack n D ks tl' sp_block sp_new (ev ++ delta) := by
  cases h with
  | seqBase sp_before sp_br sp_open sp_es sp_cur tl ev h_open h_sep st =>
    obtain ⟨sp_es', h_sep', st'⟩ := fs h_sep st
    exact .seqBase _ _ _ _ _ _ _ h_open h_sep' st'
  | mapBase sp_before sp_br sp_open sp_es sp_cur tl ev h_open h_sep st =>
    obtain ⟨sp_es', h_sep', st'⟩ := fm h_sep st
    exact .mapBase _ _ _ _ _ _ _ h_open h_sep' st'
  | seqNest d ks tl_par tl sp_before sp_par sp_br sp_open sp_es sp_cur ev_par ev parent h_tail h_lead h_open h_sep st =>
    obtain ⟨sp_es', h_sep', st'⟩ := fs h_sep st
    exact TFlowOpenStack.retrace (List.append_assoc _ _ _).symm
      (.seqNest _ _ _ _ _ _ _ _ _ _ _ _ parent h_tail h_lead h_open h_sep' st')
  | mapNest d ks tl_par tl sp_before sp_par sp_br sp_open sp_es sp_cur ev_par ev parent h_tail h_lead h_open h_sep st =>
    obtain ⟨sp_es', h_sep', st'⟩ := fm h_sep st
    exact TFlowOpenStack.retrace (List.append_assoc _ _ _).symm
      (.mapNest _ _ _ _ _ _ _ _ _ _ _ _ parent h_tail h_lead h_open h_sep' st')

/-- `FlowOpenStack.receiveNode`: a completed `.flowIn` node into the top frame, which is not
    `.value`-tailed (`h_tail` = the scanner's adjacency guard); the tail becomes `.value kj`
    and the trace grows by the node's. -/
lemma TFlowOpenStack.receiveNode {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_ne : SurfPos} {ev ev_n : List Event} {kj : Bool}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (h_node : TFlowNode n .flowIn sp_prep sp_ne ev_n)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_prep sp_ne ev_n) :
    TFlowOpenStack n D ks (.value kj) sp_block sp_ne (ev ++ ev_n) :=
  h.liftTop
    (fun h_sep st => st.receiveNode h_sep h_tail h_lead h_node hjson)
    (fun h_sep st => st.receiveNode h_sep h_tail h_lead h_node hjson)

/-- `FlowOpenStack.receivePropsEmpty`: a held `[96]` run decides EMPTY content (`[&a]`,
    `[&a, b]`), the node is `propsEmpty`, the trace grows by the run's. -/
lemma TFlowOpenStack.receivePropsEmpty {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end : SurfPos} {ev ev_p : List Event}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p) :
    TFlowOpenStack n D ks (.value false) sp_block sp_end (ev ++ ev_p) :=
  h.receiveNode h_tail h_lead (.propsEmpty _ _ _ _ _ h_props) (fun h => nomatch h)

/-- `FlowOpenStack.receivePropsContent`: a held run decorates the content that follows
    (`[&a b]`, `[&a [b]]`); trace = run's ++ content's. -/
lemma TFlowOpenStack.receivePropsContent {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_ne : SurfPos} {ev ev_p ev_c : List Event} {kj : Bool}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_sep : SSeparate n .flowIn sp_end sp_prep)
    (h_content : TFlowContent n .flowIn sp_prep sp_ne ev_c)
    (hjson : kj = true → TCFlowJsonContent n .flowIn sp_prep sp_ne ev_c) :
    TFlowOpenStack n D ks (.value kj) sp_block sp_ne (ev ++ (ev_p ++ ev_c)) :=
  h.receiveNode h_tail h_lead (.propsContent _ _ _ _ _ _ _ _ h_props h_sep h_content)
    (fun hk => .propsContent _ _ _ _ _ _ _ _ h_props h_sep (hjson hk))

/-- `FlowOpenStack.receiveQuestion`: `?` on a `.sep` tail; the tail becomes `.question`, the
    trace is kept (indicators are silent). -/
lemma TFlowOpenStack.receiveQuestion {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : tl = .sep)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (hq : GLit '?' sp_prep sp_tok) :
    TFlowOpenStack n D ks .question sp_block sp_tok ev := by
  subst h_tail
  exact TFlowOpenStack.retrace (List.append_nil _) (h.liftTop (delta := [])
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveQuestion h_sep h_lead hq
      exact ⟨a, b, TSeqFrame.retrace (List.append_nil _).symm c⟩)
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveQuestion h_sep h_lead hq
      exact ⟨a, b, TMapFrame.retrace (List.append_nil _).symm c⟩))

/-- `FlowOpenStack.receiveColonSep`: `:` on a `.sep` tail (`[146]`'s empty key). -/
lemma TFlowOpenStack.receiveColonSep {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : tl = .sep)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (hcolon : GLit ':' sp_prep sp_tok) :
    TFlowOpenStack n D ks (.colon false) sp_block sp_tok ev := by
  subst h_tail
  exact TFlowOpenStack.retrace (List.append_nil _) (h.liftTop (delta := [])
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveColonSep h_sep h_lead hcolon
      exact ⟨a, b, TSeqFrame.retrace (List.append_nil _).symm c⟩)
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveColonSep h_sep h_lead hcolon
      exact ⟨a, b, TMapFrame.retrace (List.append_nil _).symm c⟩))

/-- `FlowOpenStack.receiveColonQuestion`: `:` on a `.question` tail (`[? :`). -/
lemma TFlowOpenStack.receiveColonQuestion {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_tok : SurfPos} {ev : List Event}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : tl = .question)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (hcolon : GLit ':' sp_prep sp_tok) :
    TFlowOpenStack n D ks (.colon false) sp_block sp_tok ev := by
  subst h_tail
  exact TFlowOpenStack.retrace (List.append_nil _) (h.liftTop (delta := [])
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveColonQuestion h_sep h_lead hcolon
      exact ⟨a, b, TSeqFrame.retrace (List.append_nil _).symm c⟩)
    (fun h_sep st => by
      obtain ⟨a, b, c⟩ := st.receiveColonQuestion h_sep h_lead hcolon
      exact ⟨a, b, TMapFrame.retrace (List.append_nil _).symm c⟩))

/-- `FlowOpenStack.receiveColonPropsSep`: a held run then `:` on a `.sep` tail (`[&a : b]`); the
    run is the key, the trace grows by the run's. -/
lemma TFlowOpenStack.receiveColonPropsSep {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_tok : SurfPos} {ev ev_p : List Event}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : tl = .sep)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_gap : GOpt (SSeparate n .flowIn) sp_end sp_prep)
    (hcolon : GLit ':' sp_prep sp_tok) :
    TFlowOpenStack n D ks (.colon false) sp_block sp_tok (ev ++ ev_p) := by
  subst h_tail
  exact h.liftTop
    (fun h_sep st => st.receiveColonPropsSep h_sep h_lead h_props h_gap hcolon)
    (fun h_sep st => st.receiveColonPropsSep h_sep h_lead h_props h_gap hcolon)

/-- `FlowOpenStack.receiveColonPropsQuestion`: a held run then `:` on a `.question` tail
    (`[? &a : b]`); the run is the explicit key. -/
lemma TFlowOpenStack.receiveColonPropsQuestion {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_tok : SurfPos} {ev ev_p : List Event}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : tl = .question)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_gap : GOpt (SSeparate n .flowIn) sp_end sp_prep)
    (hcolon : GLit ':' sp_prep sp_tok) :
    TFlowOpenStack n D ks (.colon false) sp_block sp_tok (ev ++ ev_p) := by
  subst h_tail
  exact h.liftTop
    (fun h_sep st => st.receiveColonPropsQuestion h_sep h_lead h_props h_gap hcolon)
    (fun h_sep st => st.receiveColonPropsQuestion h_sep h_lead h_props h_gap hcolon)

/-- `FlowOpenStack.receiveNodeColon`: a node and its `:` in one step on a `.sep` / `.question`
    tail; the tail becomes `.colon kj`, the trace grows by the key's. -/
lemma TFlowOpenStack.receiveNodeColon {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_ne sp_prep₂ sp_tok : SurfPos} {ev ev_n : List Event} {kj : Bool}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : tl = .sep ∨ tl = .question)
    (h_lead : SSeparateLines n sp_flow sp_prep ∨ (sp_prep = sp_flow ∧ tl.leadFree))
    (h_node : TFlowNode n .flowIn sp_prep sp_ne ev_n)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_prep sp_ne ev_n)
    (h_lead₂ : SSeparateLines n sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne)
    (hcolon : GLit ':' sp_prep₂ sp_tok) :
    TFlowOpenStack n D ks (.colon kj) sp_block sp_tok (ev ++ ev_n) :=
  h.liftTop
    (fun h_sep st => st.receiveNodeColon h_sep h_tail h_lead
      h_node hjson h_lead₂ hcolon)
    (fun h_sep st => st.receiveNodeColon h_sep h_tail h_lead
      h_node hjson h_lead₂ hcolon)

/-- `FlowOpenStack.receivePropsNodeColon`: the held run decorates the key (`[a, &x b : c]`). -/
lemma TFlowOpenStack.receivePropsNodeColon {n D : Nat} {ks : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_ne sp_prep₂ sp_tok : SurfPos}
    {ev ev_p ev_c : List Event} {kj : Bool}
    (h : TFlowOpenStack n D ks tl sp_block sp_flow ev)
    (h_tail : tl = .sep ∨ tl = .question)
    (h_lead : SSeparateLines n sp_flow sp_p ∨ (sp_p = sp_flow ∧ tl.leadFree))
    (h_props : TCNsProperties n .flowIn sp_p sp_end ev_p)
    (h_sep : SSeparate n .flowIn sp_end sp_prep)
    (h_content : TFlowContent n .flowIn sp_prep sp_ne ev_c)
    (hjson : kj = true → TCFlowJsonNode n .flowIn sp_p sp_ne (ev_p ++ ev_c))
    (h_lead₂ : SSeparateLines n sp_ne sp_prep₂ ∨ sp_prep₂ = sp_ne)
    (hcolon : GLit ':' sp_prep₂ sp_tok) :
    TFlowOpenStack n D ks (.colon kj) sp_block sp_tok (ev ++ (ev_p ++ ev_c)) :=
  h.receiveNodeColon h_tail h_lead (.propsContent _ _ _ _ _ _ _ _ h_props h_sep h_content) hjson
    h_lead₂ hcolon

/-! ### §6c The depth-0 opens (`FlowStackB.openSeqBase` / `openMapBase`), trace `[]` -/

lemma TFlowStackB.openSeqBase {n : Nat} {sp_before sp_br sp_open sp_es : SurfPos}
    (h_open : GLit '[' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowOut) sp_open sp_es) :
    TFlowStackB n 1 #[true] .sep sp_before sp_es [] :=
  .open _ _ _ _ _ _ (.seqBase _ _ _ _ _ _ _ h_open h_sep (.betweenEmpty sp_es))

lemma TFlowStackB.openMapBase {n : Nat} {sp_before sp_br sp_open sp_es : SurfPos}
    (h_open : GLit '{' sp_br sp_open) (h_sep : GOpt (SSeparate n .flowOut) sp_open sp_es) :
    TFlowStackB n 1 #[false] .sep sp_before sp_es [] :=
  .open _ _ _ _ _ _ (.mapBase _ _ _ _ _ _ _ h_open h_sep (.betweenEmpty sp_es))

end

end L4YAML.Proofs.Serialization.TraceOf.FlowWalk
