module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flow tower, indexed by the gate its base frame's route is stated
    against (DOCS item 163)

Item 162 built the carrier — `ParkAnchor`, the five shapes a scanner step can
take, and the spend the base close makes — and priced the installation with the
compiler.  This file is the installation's first half: the gate `g` is now a
PARAMETER of `FlowBaseRoutes`, `FlowOpenStack` and `FlowStackB`, `FlowStackK`
quantifies it existentially, and the frame's own construction is polymorphic in
it.  Reflection 670's rule held exactly: the price was the **46** signatures
that ascribe the three types, and every constructor application and every
`cases` compiled verbatim.

**What the parameter buys.**  Which verdict a depth-0 frame's node reading is
stated against is the OPENING ARM's to choose.  A landing that owes an
unconditional reading opens at `none`, and `GateOf none` is `True` by
definition — so six of the ten `FlowBaseRoutes.value` sites item 161 priced pay
nothing at all, by construction rather than by argument.  A park that owes one
only when its own `[96]` run is spent opens at `some`.  Until the routes
themselves are gated the choice is uniform (`none` everywhere), which is why
the tower here is a re-index and not yet a narrowing.

**The transport kit, completed** (§3).  Every step a flow dispatch can take now
names its own shape once, against the SCANNER's function rather than an
abstract push: `dispatchBase` for the two silent writers each dispatch crosses,
`seqStart`/`mapStart` for the two opens, `seqEnd`/`mapEnd` (and their
positive-depth twins) for the two closes, `flowEntry` for `,`, `flowKey` for
`?`, and `content` for the WHOLE content lane — item 158's
`dispatchContent_tokens_push_node` says a content dispatch pushes exactly one
node token, and no node token is a bracket, so the six content arms need no
case on the character.

**What the conjunct still waits on, MEASURED** (§4).  `FlowStackK` does not yet
carry the anchor, and the obstacle is the fifth shape.  Inside a flow the `:`
resolves a simple key by REWRITING the slot at `simpleKey.tokenIndex + 1`, and
the anchor survives that only if the slot is not the base open's own.  That is
true — the walk below shows it — but it is not a carried proposition: item 10's
`KmSound` docstring states it as a parenthetical ("token writes only target
reservation slots at or above the CURRENT pending key's index, which sits above
every stacked entry") and nothing proves it.  It cannot be an arm-local
discharge either, because a flow CLOSE restores the pending key from
`simpleKeyStack` — so the floor is a statement about the whole stack, and it is
DEPTH-RELATIVE: §4's walk shows the base close restoring a key that sits BELOW
the base open, which is sound only because a closed frame owes no anchor.
-/

namespace L4YAML.Tests.Guards.FlowGateGeneration

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  The tower takes the gate, and every level forwards it

A base open built at `g` yields a stack at `g`; a nest neither reads it nor
changes it, which is why the re-index cost signatures and not occurrences. -/

example {s0 : ScannerState} {sp_start sp_before sp_br sp_open sp_es : SurfPos} {n kc : Nat}
    {g : Option ScannerState} (b : Bool)
    (resume : FlowBaseRoutes sp_start n sp_br kc g s0)
    (h_open : GLit '[' sp_br sp_open)
    (h_sep : GOpt (SSeparate n .flowOut) sp_open sp_es) :
    FlowStackB sp_start n kc g s0 1 #[true] #[b] .sep sp_before sp_es :=
  FlowStackB.openSeqBase b resume h_open h_sep

example {s0 : ScannerState} {sp_start sp_before sp_br sp_open sp_es : SurfPos} {n kc : Nat}
    {g : Option ScannerState} (b : Bool)
    (resume : FlowBaseRoutes sp_start n sp_br kc g s0)
    (h_open : GLit '{' sp_br sp_open)
    (h_sep : GOpt (SSeparate n .flowOut) sp_open sp_es) :
    FlowStackB sp_start n kc g s0 1 #[false] #[b] .sep sp_before sp_es :=
  FlowStackB.openMapBase b resume h_open h_sep

/-- A closed stack names a gate too, and `none` is the one it names: with no
    frame there is no park to be anchored to.  This is the shape all 32 of the
    depth-0 accum-step conclusions took. -/
example {s0 : ScannerState} {sp_start sp : SurfPos} {tl : FrameTail} :
    FlowStackB sp_start 0 0 none s0 0 #[] #[] tl sp sp :=
  FlowStackB.nil sp tl

/-! ## §2  What `none` is worth

`GateOf none` is `True` BY DEFINITION — not by a lemma — which is what makes an
ungated frame's route free once `FlowBaseRoutes.value` takes the gate. -/

example : GateOf none := trivial
example {sc0 : ScannerState} (h : danglingNodePos? sc0 = none)
    (hska : sc0.simpleKeyAllowed = false) : GateOf (some sc0) := ⟨h, hska⟩
example {s : ScannerState} {d : Nat} : FlowBaseAnchor none s d := trivial

/-! ## §3  The transport kit, against the scanner's own steps

Each of these is the shape ONE dispatch arm takes.  They are stated against
`scanFlowSequenceStart` and friends rather than against `Array.push` so that an
arm spends a lemma instead of re-deriving a token shape. -/

/-- **The genesis**: the base open is where the anchor is made, and `ofOpen`
    reads it off the bracket the scanner actually pushes. -/
example {sc0 : ScannerState} (hflow : sc0.inFlow = false)
    (hprop : ∃ k, prevRealIdx? sc0.tokens sc0.tokens.size = some k ∧
      sc0.tokens[k]!.val.isNodeProperty = true)
    (hska : sc0.simpleKeyAllowed = false) :
    ParkAnchor sc0 (scanFlowSequenceStart sc0) 0 :=
  ParkAnchor.ofOpen (scanFlowSequenceStart_tokens sc0) rfl
    (L4YAML.Proofs.EmitterScannability.scanFlowSequenceStart_preserves_indents sc0)
    hflow hprop hska

example {sc0 : ScannerState} (hflow : sc0.inFlow = false)
    (hprop : ∃ k, prevRealIdx? sc0.tokens sc0.tokens.size = some k ∧
      sc0.tokens[k]!.val.isNodeProperty = true)
    (hska : sc0.simpleKeyAllowed = false) :
    ParkAnchor sc0 (scanFlowMappingStart sc0) 0 :=
  ParkAnchor.ofOpen (scanFlowMappingStart_tokens sc0) rfl
    (L4YAML.Proofs.EmitterScannability.scanFlowMappingStart_preserves_indents sc0)
    hflow hprop hska

/-- The two silent writers, bundled: preprocessing's save and the
    `allowDirectives` update, which every flow dispatch crosses before its own
    indicator. -/
example {g : Option ScannerState} {sc s_prep : ScannerState} {c : Char} {d : Nat}
    (h : FlowBaseAnchor g sc d) (h_flow : sc.inFlow = true)
    (hpre : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    FlowBaseAnchor g (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep) d :=
  h.dispatchBase h_flow hpre

/-- The two opens deepen the hold. -/
example {g : Option ScannerState} {s : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s d) : FlowBaseAnchor g (scanFlowSequenceStart s) (d + 1) :=
  h.seqStart

example {g : Option ScannerState} {s : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s d) : FlowBaseAnchor g (scanFlowMappingStart s) (d + 1) :=
  h.mapStart

/-- The two closes shallow it — and a nested-close arm knows its depth only to
    be POSITIVE, which is the form `seqEndPos`/`mapEndPos` take. -/
example {g : Option ScannerState} {s : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s (d + 1)) : FlowBaseAnchor g (scanFlowSequenceEnd s) d :=
  h.seqEnd

example {g : Option ScannerState} {s : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s d) (hd : 0 < d) :
    FlowBaseAnchor g (scanFlowMappingEnd s) (d - 1) :=
  h.mapEndPos hd

/-- `,` and `?` each write one token that is neither bracket. -/
example {g : Option ScannerState} {s s' : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s d) (hstep : scanFlowEntry s = .ok s') :
    FlowBaseAnchor g s' d :=
  h.flowEntry hstep

example {g : Option ScannerState} {s s' : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s d) (h_flow : s.inFlow = true) (hstep : scanKey s = .ok s') :
    FlowBaseAnchor g s' d :=
  h.flowKey h_flow hstep

/-- **The whole content lane in one shape.**  No case on the character: item
    158 already proved every content dispatch pushes exactly one node token,
    and neither a node body nor a `[96]` property is a bracket. -/
example {g : Option ScannerState} {s s' : ScannerState} {c : Char} {d : Nat}
    (h : FlowBaseAnchor g s d) (h_flow : s.inFlow = true)
    (hstep : scanNextToken_dispatchContent s c = .ok s') :
    FlowBaseAnchor g s' d :=
  h.content h_flow hstep

/-! ## §4  The fifth shape's missing precondition, measured

The rows below are the scanner's own token array at each step, `ph` a
`saveSimpleKey` reservation and `K` the `[187] c-l-block-map-implicit-key` the
`:` resolves it into.  `sk=p/i` is the pending key: whether it is armed, and
the slot it reserved. -/

private def stepTo (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | k + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepTo s' k
    | _ => none

private def start (input : String) : ScannerState :=
  (ScannerState.mk' input).emit .streamStart

private def kinds (s : ScannerState) : String :=
  String.intercalate "," ((List.range s.tokens.size).map (fun j =>
    match s.tokens[j]!.val with
    | .placeholder => "ph" | .key => "K" | .value => "V"
    | .flowSequenceStart => "[" | .flowSequenceEnd => "]"
    | .flowMappingStart => "{" | .flowMappingEnd => "}"
    | .flowEntry => "," | .streamStart => "S" | .blockMappingStart => "BM"
    | .scalar _ _ => "s" | .anchor _ => "&" | _ => "?"))

private def row (s : ScannerState) : String :=
  s!"sk={s.simpleKey.possible}/{s.simpleKey.tokenIndex} [{kinds s}]"

private def walk (input : String) (n : Nat) : String :=
  let rec go (s : ScannerState) (k : Nat) (acc : List String) : List String :=
    match k with
    | 0 => acc.reverse
    | k + 1 =>
      match scanNextToken s with
      | .ok (some s') => go s' k (row s' :: acc)
      | _ => acc.reverse
  String.intercalate " ; " (go (start input) n [])

/-! **The rewrite, and the slot it lands on.**  In `&p [a: b]` the base open is
at index **4**.  The save made while scanning `a` reserves slots 5 and 6, and
the `:` rewrites slot **6** — `simpleKey.tokenIndex + 1` — from `ph` to `K`
while pushing its own `V`.  `6 > 4`, so the anchor's `below` conjunct survives
and the array at the open is untouched; that is the fact the carrier needs and
no conjunct states. -/

#guard walk "&p [a: b]\n" 6
  == "sk=true/1 [S,ph,ph,&] ; sk=false/0 [S,ph,ph,&,[] ; \
sk=true/5 [S,ph,ph,&,[,ph,ph,s] ; sk=false/0 [S,ph,ph,&,[,ph,K,s,V] ; \
sk=true/9 [S,ph,ph,&,[,ph,K,s,V,ph,ph,s] ; \
sk=true/1 [S,ph,ph,&,[,ph,K,s,V,ph,ph,s,]]"

/-! **Why it is not an arm-local fact.**  The last row above is the BASE close,
and it restores `sk=true/1` — a reservation at index **1**, BELOW the base open
at 4.  A floor on the pending key alone is therefore FALSE the moment the frame
closes.  It is sound only because a closed stack owes no anchor (`FlowStackK`'s
conjunct would ride under `0 < fl`), which makes the floor DEPTH-RELATIVE: a
property of the stack, restored by each close, not of any one state. -/

/-! **A NESTED close restores a key that is above the base open**, which is the
half that has to hold.  In `&p [a, [b: c], d]` the base open is at **4** and the
nest at **12**; the nested `:` rewrites slot **13**, and the nested `]` restores
`sk=true/9` — the key the nest stacked, and `9 > 4`. -/

#guard walk "&p [a, [b: c], d]\n" 12
  == "sk=true/1 [S,ph,ph,&] ; sk=false/0 [S,ph,ph,&,[] ; \
sk=true/5 [S,ph,ph,&,[,ph,ph,s] ; sk=false/0 [S,ph,ph,&,[,ph,ph,s,,] ; \
sk=false/0 [S,ph,ph,&,[,ph,ph,s,,,ph,ph,[] ; \
sk=true/12 [S,ph,ph,&,[,ph,ph,s,,,ph,ph,[,ph,ph,s] ; \
sk=false/0 [S,ph,ph,&,[,ph,ph,s,,,ph,ph,[,ph,K,s,V] ; \
sk=true/16 [S,ph,ph,&,[,ph,ph,s,,,ph,ph,[,ph,K,s,V,ph,ph,s] ; \
sk=true/9 [S,ph,ph,&,[,ph,ph,s,,,ph,ph,[,ph,K,s,V,ph,ph,s,]] ; \
sk=false/0 [S,ph,ph,&,[,ph,ph,s,,,ph,ph,[,ph,K,s,V,ph,ph,s,],,] ; \
sk=true/21 [S,ph,ph,&,[,ph,ph,s,,,ph,ph,[,ph,K,s,V,ph,ph,s,],,,ph,ph,s] ; \
sk=true/1 [S,ph,ph,&,[,ph,ph,s,,,ph,ph,[,ph,K,s,V,ph,ph,s,],,,ph,ph,s,]]"

end L4YAML.Tests.Guards.FlowGateGeneration

end Blanket
