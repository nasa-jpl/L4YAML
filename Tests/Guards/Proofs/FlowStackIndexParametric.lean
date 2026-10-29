module

public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flow stack's grammar slots read at a parameter, not at 0 (DOCS item 44)

Item 44 re-indexed `FlowOpenStack`/`FlowStackB` by a reading index `n`: every
grammar slot inside the stack — the frames, the interior separators, the nest
closures, the base `resume` — is stated at that one parameter, and the ≈86
literal `0`s item 25 priced now live in exactly ONE place, `FlowStackK`'s
instantiation.  Nothing behaves differently yet (every producer still runs the
stack at 0); what changed is what the TYPE admits.

This file is the compile-time witness of that admission: each `example` below
instantiates a piece of the machinery at the index `2` from abstract
hypotheses.  Before item 44 none of these elaborated — the `2` had to be `0`.
They are `example`s over hypotheses rather than `#guard`s over inputs because
the claim is about the types: no scanner run can reach a nonzero index until
item 46 threads it, so the only thing to pin today is that the machinery no
longer refuses one.
-/

namespace L4YAML.Tests.Guards.FlowStackIndexParametric

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  The base frame opens at a nonzero index -/

/-- `FlowStackB.openSeqBase` at `n = 2`: the resume's content argument and the
    post-bracket separator both read at 2.  (Item 56 bundled the frame's
    closures, so the witness opens through `FlowBaseRoutes.ofValue` — the
    value-only frame an enclosing construct with no entry to offer hands it.) -/
example {s0 : ScannerState} {sp_start sp_before sp_br sp_open : SurfPos}
    (resume : ∀ sp_ne sp_m, SFlowContent 2 .flowOut sp_br sp_ne →
              SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m)
    (h_open : GLit '[' sp_br sp_open) :
    FlowStackB sp_start 2 3 none s0 1 #[true] #[false] .sep sp_before sp_open :=
  FlowStackB.openSeqBase false (.ofValue (fun _ => resume)) h_open (GOpt.none sp_open)

/-- ... and the mapping twin at `n = 2`. -/
example {s0 : ScannerState} {sp_start sp_before sp_br sp_open : SurfPos}
    (resume : ∀ sp_ne sp_m, SFlowContent 2 .flowOut sp_br sp_ne →
              SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m)
    (h_open : GLit '{' sp_br sp_open) :
    FlowStackB sp_start 2 3 none s0 1 #[false] #[false] .sep sp_before sp_open :=
  FlowStackB.openMapBase false (.ofValue (fun _ => resume)) h_open (GOpt.none sp_open)

/-! ## §2  The interior receivers thread the index -/

/-- `receiveNode` at `n = 2`: the leading separation and the received node both
    read at the stack's index. -/
example {s0 : ScannerState} {sp_start : SurfPos} {D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_prep sp_ne : SurfPos}
    (h_fos : FlowOpenStack sp_start 2 3 none s0 D ks km tl sp_block sp_flow)
    (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparateLines 2 sp_flow sp_prep)
    (h_node : SFlowNode 2 .flowIn sp_prep sp_ne) :
    FlowOpenStack sp_start 2 3 none s0 D ks km (.value false) sp_block sp_ne :=
  h_fos.receiveNode h_tail (Or.inl h_lead) sp_ne false h_node (fun h => nomatch h)

/-- The property-run receiver at `n = 2` (`  - &a [&b c]`'s interior shape):
    the run, its separator, and the content all read at the index item 24
    could not reach. -/
example {s0 : ScannerState} {sp_start : SurfPos} {D : Nat} {ks km : Array Bool} {tl : FrameTail}
    {sp_block sp_flow sp_p sp_end sp_prep sp_ne : SurfPos} {ha ht : Bool}
    (h_fos : FlowOpenStack sp_start 2 3 none s0 D ks km tl sp_block sp_flow)
    (h_tail : ∀ kj, tl ≠ .value kj)
    (h_lead : SSeparateLines 2 sp_flow sp_p)
    (h_run : PropsRun 2 (inFlowCtx .flowOut) ha ht sp_p sp_end)
    (h_sep : SSeparate 2 (inFlowCtx .flowOut) sp_end sp_prep)
    (h_content : SFlowContent 2 (inFlowCtx .flowOut) sp_prep sp_ne) :
    FlowOpenStack sp_start 2 3 none s0 D ks km (.value false) sp_block sp_ne :=
  h_fos.receivePropsContent h_tail (Or.inl h_lead) h_run h_sep h_content (kj := false)
    (fun h => nomatch h)

/-! ## §3  The close hands the collection back at the index -/

/-- `SeqFrame.closeWithSep` at `n = 2`: the closed collection is
    `SFlowSequence 2`, which is what `[137] c-flow-sequence(n,c)` needs from a
    flow value inside an entry at index 2 — the consumer item 46 wires up. -/
example {c_out : YamlContext} {tl : FrameTail}
    {sp_br sp_open sp_es sp_flow sp_prep sp_tok : SurfPos}
    (h_open : GLit '[' sp_br sp_open)
    (h_sep : GOpt (SSeparate 2 c_out) sp_open sp_es)
    (st : SeqFrame 2 (inFlowCtx c_out) tl sp_es sp_flow)
    (h_lead_out : SSeparate 2 c_out sp_flow sp_prep)
    (h_lead_in : SSeparate 2 (inFlowCtx c_out) sp_flow sp_prep)
    (h_close : GLit ']' sp_prep sp_tok) :
    SFlowSequence 2 c_out sp_br sp_tok :=
  SeqFrame.closeWithSep h_open h_sep st h_lead_out h_lead_in h_close

/-- ... and the mapping twin. -/
example {c_out : YamlContext} {tl : FrameTail}
    {sp_br sp_open sp_es sp_flow sp_prep sp_tok : SurfPos}
    (h_open : GLit '{' sp_br sp_open)
    (h_sep : GOpt (SSeparate 2 c_out) sp_open sp_es)
    (st : MapFrame 2 (inFlowCtx c_out) tl sp_es sp_flow)
    (h_lead_out : SSeparate 2 c_out sp_flow sp_prep)
    (h_lead_in : SSeparate 2 (inFlowCtx c_out) sp_flow sp_prep)
    (h_close : GLit '}' sp_prep sp_tok) :
    SFlowMapping 2 c_out sp_br sp_tok :=
  MapFrame.closeWithSep h_open h_sep st h_lead_out h_lead_in h_close

/-! ## §4  One index serves a nested stack

The nest constructors take their closures at the SAME `n` as the parent — the
flow productions propagate the index unchanged — so a depth-2 stack at index 2
needs no second index.  This is the design fact §0c's docstring states, pinned
here by building the nested frame from abstract closures at one `n`. -/

example {s0 : ScannerState} {sp_start : SurfPos} {ks km : Array Bool}
    {sp_before0 sp_par sp_open : SurfPos}
    (inject : ∀ sp_ne, SCFlowJsonContent 2 .flowIn sp_par sp_ne →
              FlowOpenStack sp_start 2 3 none s0 1 ks km (.value true) sp_before0 sp_ne)
    (h_open : GLit '[' sp_par sp_open) :
    FlowOpenStack sp_start 2 3 none s0 2 (ks.push true) (km.push true) .sep sp_before0 sp_open :=
  .seqNest 1 ks km true .sep sp_before0 sp_par sp_open sp_open sp_open
    (fun h => absurd h (by simp)) inject h_open (GOpt.none sp_open)
    (.betweenEmpty sp_open)

/-! ## §5  The base-key column is a second, independent parameter (item 75)

`kc` records the column of the key the OPEN stacks, so that the matching close
can hand its park a pack whose entry index is measured rather than punted.  It
is a parameter of the same shape as `n` and independent of it — the witnesses
above all run at `n = 2`, `kc = 3` — and only the BASE constructors read it, in
`FlowBaseRoutes.key`'s last conjunct.

The pair below is the whole of what item 75 threads: an open that can measure
its stacked key hands the frame `kc = k`, and the close spends it against the
mask's base slot.  Item 78 removed the first half's option — `FlowBaseRoutes.key`
now carries the equation itself, because every park says what preprocessing
saved — so the `rfl`s below are the field's own type rather than one arm of it,
and what the close still decides per input is the MASK's promise (`h_kc`). -/

/-- A base frame whose entry route is measured AT the stacked key's column. -/
example {s0 : ScannerState} {sp_start sp_before sp_br sp_open sp_key : SurfPos}
    (value : ∀ sp_ne sp_m, SFlowContent 2 .flowOut sp_br sp_ne →
              SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m)
    (route : ∀ sp_v, SBlockMapEntry 3 sp_key sp_v → SLYamlStream sp_start sp_v)
    (h_open : GLit '[' sp_br sp_open) :
    FlowStackB sp_start 2 3 none s0 1 #[true] #[false] .sep sp_before sp_open :=
  FlowStackB.openSeqBase false
    ⟨fun _ _ => Or.inr trivial, fun _ => value, Or.inl ⟨3, sp_key, route, fun _ _ => Or.inr trivial, rfl, Or.inr trivial,
      Or.inr trivial, Or.inr trivial⟩,
     Or.inr trivial⟩
    h_open (GOpt.none sp_open)

/-- …and the close spends it: a one-bit mask carries the base slot's column
    (item 79 made that promise conditional on the mask rather than optional), so
    the frame becomes a pack whose column conjunct is DERIVED — the column is
    an equation and neither arm of the pack can punt on a measurement.  Beside
    it rides the open's stamp reading (item 103), which is optional because it
    is a fact about the INPUT rather than a measurement of the mask. -/
-- Item 311: the flow frame's alternative is the gate's (`PackAltG g`); these probes name an ungated frame.
example {sc : ScannerState} {sp_start sp_br sp_tok sp_key : SurfPos}
    (route : ∀ sp_v, SBlockMapEntry 3 sp_key sp_v → SLYamlStream sp_start sp_v)
    (head : ∀ sp_end, SFlowContent 2 .flowOut sp_br sp_end →
      ImplicitKeyHead sp_key sp_end ∨ True)
    (h_kc : sc.simpleKey.pos.col = 3)
    (h_park : StalePark sc)
    (h_content : SFlowContent 2 .flowOut sp_br sp_tok) :
    sc.simpleKey.possible = true → sc.simpleKey.pos.line = sc.line →
      ImplicitKeyPack sc sp_start sp_tok ∨ KeyPackPunt sc :=
  flowKeyPack_of_close (g := none) (kc := 3)
    (Or.inl ⟨3, sp_key, route, head, rfl, Or.inr trivial, Or.inr trivial,
      Or.inr trivial⟩)
    -- Item 300: the base slot's third reading, the marker's line, declined here.
    ⟨h_kc, Or.inr trivial, Or.inr trivial⟩ h_park h_content

end L4YAML.Tests.Guards.FlowStackIndexParametric

end Blanket
