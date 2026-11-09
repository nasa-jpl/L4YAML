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
      (sp_before sp_par sp_open sp_es sp_cur : SurfPos) (ev_par ev : List Event)
      (parent : TFlowOpenStack n d ks tl_par sp_before sp_par ev_par)
      (h_open : GLit '[' sp_par sp_open)
      (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
      (st : TSeqFrame n .flowIn tl sp_es sp_cur ev) :
      TFlowOpenStack n (d + 1) (ks.push true) tl sp_before sp_cur (ev_par ++ ev)
  | mapNest (d : Nat) (ks : Array Bool) (tl_par tl : FrameTail)
      (sp_before sp_par sp_open sp_es sp_cur : SurfPos) (ev_par ev : List Event)
      (parent : TFlowOpenStack n d ks tl_par sp_before sp_par ev_par)
      (h_open : GLit '{' sp_par sp_open)
      (h_sep : GOpt (SSeparate n .flowIn) sp_open sp_es)
      (st : TMapFrame n .flowIn tl sp_es sp_cur ev) :
      TFlowOpenStack n (d + 1) (ks.push false) tl sp_before sp_cur (ev_par ++ ev)

/-- The `FlowStackK` sibling: the scanner-coupled S stack as it stands, and a `TraceOf` stack
    over the same frame indices with trace `ev`.  The S frame and the T frame sit side by side
    (no `TFlow* → SFlow*` erasure is spent); 2c couples `ev` to `goOut` of the token segment
    since `sp_block` over `scanLoop`. -/
def TFlowStackK (sp_start : SurfPos) (sc : L4YAML.Scanner.ScannerState) (fl : Nat) (ks : Array Bool)
    (tl : FrameTail) (sp_block sp_flow : SurfPos) (ev : List Event) : Prop :=
  FlowStackK sp_start sc fl ks tl sp_block sp_flow ∧
    ∃ n, TFlowOpenStack n fl ks tl sp_block sp_flow ev

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

end
end L4YAML.Proofs.Serialization.TraceOf.FlowWalk
