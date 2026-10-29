module

public import L4YAML.Proofs.Production.StreamAccum

public meta import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The reservation floor, and the gate it lets the close pay (DOCS item 164)

Item 163 installed the gate parameter and completed the transport kit, then
measured why the anchor conjunct could not land: item 162's fifth step shape —
the `:`'s REWRITE — needs a precondition nothing carried.  Inside a flow,
`scanValuePrepare` resolves a pending simple key by writing the slot at
`simpleKey.tokenIndex + 1`.  A park anchored over the frame survives that write
only if the slot is neither below the base open (which would break the prefix
the anchor reads) nor a bracket (which would move the forward stack the anchor
is stated against).

This file is that precondition, carried — and the conjunct it unblocks, spent.

**One predicate.**  `KeyFloor ts o k` says an ARMED key's reservation sits above
`o`, in bounds, and holds no bracket; an unarmed key promises nothing, which is
what makes every clearing step free.  `ParkFloor sc0 s d` carries it for the
pending key and for the top `d` stack entries.

**The range is DEPTH-RELATIVE, and §4 is why.**  A flow close RESTORES the
pending key from `simpleKeyStack`, so a floor on the pending alone is false the
moment a frame closes: the walk shows `&p [a: b]`'s base close restoring a
reservation at index 1 against an open at 4.  That is sound because a closed
frame owes no anchor — the conjunct rides under `0 < fl` — so what the floor
covers is the pending key and the entries ABOVE the base slot.  `Nat`'s
truncating subtraction slides the range exactly right: an open takes
`(size, d)` to `(size + 1, d + 1)` and a close takes `(size, d + 1)` to
`(size - 1, d)`, and `size - d` is invariant under both.

**What it buys.**  `FlowStackK` now carries `FlowBaseAnchor g sc (fl - 1)`, all
twenty positive-depth arms discharge it — the five `:` arms included — and
`FlowBaseRoutes.value` takes `GateOf g`, paid at the two base closes off the
anchor the open recorded.  Item 161 priced that at ten sites; the six with an
unconditional route pay nothing, because `GateOf none` is `True` by definition.
The one site still choosing `none` where it could choose `some` is the props
arm, whose park is the one the whole carrier exists for.
-/

namespace L4YAML.Tests.Guards.FlowReservationFloor

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  The predicate, and what an unarmed key owes

Nothing.  Every step that clears the pending key — `:`, `?`, `,`, the block
scalars, both opens — discharges its half of the floor by construction. -/

example {ts : Array (Positioned YamlToken)} {o : Nat} {k : SimpleKeyState}
    (h : k.possible = false) : KeyFloor ts o k :=
  KeyFloor.cleared h

/-- …and an armed one owes exactly two readings: above the open, and no bracket
    in the slot its save reserved. -/
example {ts : Array (Positioned YamlToken)} {o : Nat} {k : SimpleKeyState}
    (h : KeyFloor ts o k) (hp : k.possible = true) :
    o < k.tokenIndex ∧ ts[k.tokenIndex + 1]!.val.isFlowOpen = false :=
  ⟨(h hp).1, (h hp).2.2.1⟩

/-! ## §2  The five maintenance shapes, against the scanner's own steps

The SAVE is the only step that opens a reservation, and it is preprocessing's;
the two opens stack the pending key and clear it; the two closes pop it back;
the `:` rewrites the slot.  Everything else is inert. -/

/-- **The save**, spelled inside the wrapper the arms already spend: the index
    a fresh reservation records is the incoming array's end, which is above the
    base open because a held open is an index INTO that array. -/
example {g : Option ScannerState} {sc s_prep : ScannerState} {c : Char} {d : Nat}
    (h : FlowBaseAnchor g sc d) (h_flow : sc.inFlow = true)
    (hpre : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    FlowBaseAnchor g s_prep d :=
  h.preprocess h_flow hpre

/-- The two opens stack the pending key, so the floor it carried becomes the
    new top entry's. -/
example {g : Option ScannerState} {s : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s d) : FlowBaseAnchor g (scanFlowSequenceStart s) (d + 1) :=
  h.seqStart

example {g : Option ScannerState} {s : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s d) : FlowBaseAnchor g (scanFlowMappingStart s) (d + 1) :=
  h.mapStart

/-- The two closes pop it back into the pending slot. -/
example {g : Option ScannerState} {s : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s (d + 1)) : FlowBaseAnchor g (scanFlowMappingEnd s) d :=
  h.mapEnd

/-- **The fifth shape, at last.**  `scanValue` in flow rewrites the slot at
    `simpleKey.tokenIndex + 1` and pushes its own `.value`; the floor says the
    slot is above the base open and holds no bracket, which is exactly what the
    park's prefix and the forward stack each need. -/
example {g : Option ScannerState} {s s' : ScannerState} {d : Nat}
    (h : FlowBaseAnchor g s d) (h_flow : s.inFlow = true)
    (hstep : scanValue s = .ok s') : FlowBaseAnchor g s' d :=
  h.flowValue h_flow hstep

/-- The step shape that makes it possible, read off the scanner: in flow the
    `:` writes ONE slot, and the block arms — the mapping-indent push and the
    `blockMappingStart` pair — are both off `inFlow`. -/
example {s s' : ScannerState} (h_flow : s.inFlow = true) (hok : scanValue s = .ok s') :
    (∃ q : Positioned YamlToken, q.val = .value ∧ s'.tokens = s.tokens.push q) ∨
    (s.simpleKey.possible = true ∧ ∃ v q : Positioned YamlToken,
      v.val = .key ∧ q.val = .value ∧
      s'.tokens = (s.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1) v).push q) :=
  scanValue_inFlow_tokens_shape h_flow hok

/-- The content lane's reading of the pending key, in one shape: a content
    dispatch keeps the reservation where it was — the quoted scalars move only
    `endLine` — or clears it.  No content scan OPENS one. -/
example {s s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchContent s c = .ok s') :
    (s'.simpleKey.possible = s.simpleKey.possible ∧
      s'.simpleKey.tokenIndex = s.simpleKey.tokenIndex) ∨ s'.simpleKey.possible = false :=
  dispatchContent_pending_cases h

/-! ## §3  The conjunct, carried by the invariant

`FlowStackK` names the anchor at `fl - 1` — the nesting ABOVE the base — so a
depth-1 stack reads it at 0, where the close spends it.  A closed stack owes
nothing. -/

example {sp_start : SurfPos} {sc : ScannerState} {fl : Nat} {ks : Array Bool}
    {tl : FrameTail} {a b : SurfPos}
    (h : FlowStackK sp_start sc fl ks tl a b) (hfl : 0 < fl) :
    ∃ g, FlowBaseAnchor g sc (fl - 1) := by
  obtain ⟨n, kc, km, g, _, -, -, -, -, h_prom⟩ := h
  exact ⟨g, (h_prom hfl).2.1⟩

/-! ## §4  The gate, now paid

`FlowBaseRoutes.value` takes `GateOf g`.  Six of item 161's ten sites pay
nothing — `GateOf none` reduces to `True` — and the two base closes pay with the
anchor the invariant carries. -/

/-- An ungated frame's node route is free. -/
example {s0 : ScannerState} {sp_start sp_br sp_ne sp_mid : SurfPos} {n kc : Nat}
    (r : FlowBaseRoutes sp_start n sp_br kc none s0)
    (h : SFlowContent n .flowOut sp_br sp_ne) (hs : SSLComments sp_ne sp_mid) :
    SLYamlStream sp_start sp_mid :=
  r.value trivial sp_ne sp_mid h hs

/-- **The spend.**  The depth-0 close writes its bracket at the array's end, so
    the anchor's four readings are the push's own; the only thing the arm
    supplies is §9.2's verdict on the state it just made — which is precisely
    the premise `pendingContent.h_closable` already hands it. -/
example {g : Option ScannerState} {s_bc : ScannerState}
    (h : FlowBaseAnchor g s_bc 0)
    (hflow : (scanFlowSequenceEnd s_bc).inFlow = false)
    (hnd : danglingNodePos? (scanFlowSequenceEnd s_bc) = none)
    (hui : underIndentedFlowValuePos? (scanFlowSequenceEnd s_bc) = none) : GateOf g :=
  h.gate_of_close (scanFlowSequenceEnd_tokens s_bc) rfl
    (L4YAML.Proofs.EmitterScannability.scanFlowSequenceEnd_preserves_indents s_bc) hflow hnd hui

example {g : Option ScannerState} {s_bc : ScannerState}
    (h : FlowBaseAnchor g s_bc 0)
    (hflow : (scanFlowMappingEnd s_bc).inFlow = false)
    (hnd : danglingNodePos? (scanFlowMappingEnd s_bc) = none)
    (hui : underIndentedFlowValuePos? (scanFlowMappingEnd s_bc) = none) : GateOf g :=
  h.gate_of_close (scanFlowMappingEnd_tokens s_bc) rfl
    (L4YAML.Proofs.EmitterScannability.scanFlowMappingEnd_preserves_indents s_bc) hflow hnd hui

/-! ## §5  The floor, measured

`o` is the BASE open — the outermost index the forward bracket stack still
holds — `sk` the pending key's reservation, and `slot` the token kind at
`sk + 1`, the slot a `:` would rewrite.  The floor's two halves are exactly the
two columns: `sk > o`, and `slot` is no bracket. -/

private def start (input : String) : ScannerState :=
  (ScannerState.mk' input).emit .streamStart

private def kindAt (s : ScannerState) (j : Nat) : String :=
  if j < s.tokens.size then
    match s.tokens[j]!.val with
    | .placeholder => "ph" | .key => "K" | .value => "V"
    | .flowSequenceStart => "[" | .flowSequenceEnd => "]"
    | .flowMappingStart => "{" | .flowMappingEnd => "}"
    | .flowEntry => "," | .streamStart => "S" | .blockMappingStart => "BM"
    | .scalar _ _ => "s" | .anchor _ => "&" | _ => "?"
  else "-"

private def floorRow (s : ScannerState) : String :=
  let stk := flowOpenIdxStack s.tokens s.tokens.size
  let o := match stk.getLast? with | some o => toString o | none => "-"
  let k := s.simpleKey
  if k.possible then
    s!"o={o} sk={k.tokenIndex} slot={kindAt s (k.tokenIndex + 1)}"
  else s!"o={o} sk=- slot=-"

private def floorWalk (input : String) (n : Nat) : String :=
  let rec go (s : ScannerState) (k : Nat) (acc : List String) : List String :=
    match k with
    | 0 => acc.reverse
    | k + 1 =>
      match scanNextToken s with
      | .ok (some s') => go s' k (floorRow s' :: acc)
      | _ => acc.reverse
  String.intercalate " ; " (go (start input) n [])

/-! **The base case.**  `&p [a: b]` opens at 4; the save made while scanning `a`
reserves 5 and 6, so the `:` rewrites slot 6 — above the open, and a `ph`.  The
FIRST row is the park's own key, armed at 1 before any frame exists, and the
LAST is the same key restored by the base close: `1 < 4`, which is why the floor
covers the top `d` entries and not the base slot. -/

#guard floorWalk "&p [a: b]\n" 6
  == "o=- sk=1 slot=ph ; o=4 sk=- slot=- ; o=4 sk=5 slot=ph ; \
o=4 sk=- slot=- ; o=4 sk=9 slot=ph ; o=- sk=1 slot=ph"

/-! **A nested close restores a key that is ABOVE the base open** — the half
that has to hold.  In `&p [a, [b: c], d]` the nest's own key is at 12 and the
nested `]` restores 9; both clear 4. -/

#guard floorWalk "&p [a, [b: c], d]\n" 12
  == "o=- sk=1 slot=ph ; o=4 sk=- slot=- ; o=4 sk=5 slot=ph ; \
o=4 sk=- slot=- ; o=4 sk=- slot=- ; o=4 sk=12 slot=ph ; o=4 sk=- slot=- ; \
o=4 sk=16 slot=ph ; o=4 sk=9 slot=ph ; o=4 sk=- slot=- ; o=4 sk=21 slot=ph ; \
o=- sk=1 slot=ph"

/-! …and the mapping base with a sequence nested inside it, so both bracket
kinds carry the same floor. -/

#guard floorWalk "&p {a: [b: c]}\n" 10
  == "o=- sk=1 slot=ph ; o=4 sk=- slot=- ; o=4 sk=5 slot=ph ; \
o=4 sk=- slot=- ; o=4 sk=- slot=- ; o=4 sk=12 slot=ph ; o=4 sk=- slot=- ; \
o=4 sk=16 slot=ph ; o=4 sk=9 slot=ph ; o=- sk=1 slot=ph"

end L4YAML.Tests.Guards.FlowReservationFloor

end Blanket
