module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flow frame's resume rider (DOCS item 120)

Item 111 gave `PropsKeyPack` the two resume twins (items 99/108's entry-level
faces) and named the ONE boundary that still dropped them: the flow open's
props arm, where `FlowBaseRoutes.key` carried the value-line pair only — so a
props-headed flow KEY at a RESUMED landing lost its context's holdings across
the collection, and the park the landed `:` opened had punts where the
enclosing levels' faces belonged.

**The rider**: `FlowBaseRoutes.key` gains the two twins beside the pair
(stated at the key's own entry, exactly `ImplicitKeyPack`'s shapes), the
props arm passes its pack's own through — the pack's domain `(k, sp_p)` IS
the frame's `(k, sp_key)`, so the hand-off is verbatim — and
`flowKeyPack_of_close` hands them into the pack it builds, replacing the two
`Or.inr trivial`s items 99/108 had left there.  `flowKeyRoute_of_root` /
`flowKeyRoute_of_open` punt the new conjuncts: their routes end in the CLOSED
stream, and the bare flow key at an open level's own column is §8.1-refused
(`flow content under-indented`, §1's boundary pins) — the props head is what
makes the family reachable, which is why the props arm is the one payment.

**This is the 67b piece that was committable.**  The DELETION proper —
`pendingFlow`, `scannerDrop`, `dropClose`, `close_with_ssl`'s arm,
`block_dispatch_deferred`'s three sites — stays blocked: the two
inline-residue defer sites still PRODUCE the pending whenever the key packs
punt, and the punts that remain are `KeyPackPunt.dedent` (R4's landing pad,
by design) and `noKeyContext`, which has no named input (items 101/104/105's
measured chain).  §4 pins the counts so the blockage is measured, not
assumed.  (Three names have since left this list: `noFrame` with item 125,
`FlowStackB.shape` with item 126, which measured the collapse unreachable, and
`dedent` with item 297, whose exits key a fresh document.) -/

namespace L4YAML.Tests.Guards.FlowFrameResumeRider

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover (FrameLevel)

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The family at the runtime.  The props-headed flow key at a resumed
-- landing (the props run clears §8.1 — the bracket sits past the level):
#guard emits "k:\n  m:\n    - a\n  &p [1]: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ",
   "=VAL :a", "-SEQ", "+SEQ [] &p", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-MAP", "-DOC", "-STR"]
-- …whose ENTRY may open deeper structure that must pop back to the resumed
-- level — the 99-twin's spend:
#guard emits "k:\n  m:\n    - a\n  &p [1]:\n    x: 1\n  n: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ",
   "=VAL :a", "-SEQ", "+SEQ [] &p", "=VAL :1", "-SEQ", "+MAP",
   "=VAL :x", "=VAL :1", "-MAP", "=VAL :n", "=VAL :2", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- …and the sibling AFTER the flow-keyed entry conses on the same chain:
#guard emits "k:\n  m:\n    - a\n  &p [1]: b\n  n: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ",
   "=VAL :a", "-SEQ", "+SEQ [] &p", "=VAL :1", "-SEQ", "=VAL :b",
   "=VAL :n", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
-- The 108 twin's frame: the props-headed flow key inside an open `?` entry.
#guard emits "?\n  &p [1]: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "+SEQ [] &p", "=VAL :1", "-SEQ",
   "=VAL :b", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The props head is NOT load-bearing (item 172): §8.1's floor is read at
-- the close, so the BARE flow key at an open level's own column is the
-- same sibling entry, the anchor's two columns now spelling only the anchor.
#guard emits "k:\n  m:\n    - a\n  [1]: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ",
   "=VAL :a", "-SEQ", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n[1]: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "+SEQ []", "=VAL :1",
   "-SEQ", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - a\n[1]: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "-SEQ",
   "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP", "-DOC", "-STR"]

-- §2 The rider at its types: the frame's key carries the twins and the close
-- hands them through into the pack — the two slots items 99/108 had left as
-- `Or.inr trivial` in `flowKeyPack_of_close` are the frame's own now.
example {sc : ScannerState} {kc : Nat} {sp_start sp_br sp_tok sp_key : SurfPos}
    (route : ∀ sp_v, SBlockMapEntry kc sp_key sp_v → SLYamlStream sp_start sp_v)
    (head : ∀ sp_end, SFlowContent 0 .flowOut sp_br sp_end →
      ImplicitKeyHead sp_key sp_end ∨ True)
    (tw99 : ∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < kc) ∧
      ∀ sp_v : SurfPos, SBlockMapEntry kc sp_key sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail kc sp_v sp_e →
      ResumeFrames (SLYamlStream sp_start) ks sp_e)
    (tw108 : ∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width < kc) ∧
      ∀ sp_v : SurfPos, SBlockMapEntry kc sp_key sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail kc sp_v sp_e →
      KeyFrames (ExplValueLine sp_start nv) ks sp_e)
    (h_kc : sc.simpleKey.pos.col = kc)
    (h_park : StalePark sc)
    (h_content : SFlowContent 0 .flowOut sp_br sp_tok) :
    sc.simpleKey.possible = true → sc.simpleKey.pos.line = sc.line →
      ImplicitKeyPack sc sp_start sp_tok ∨ KeyPackPunt sc :=
  -- Item 311: the frame's alternative is the gate's (`PackAltG g`); an ungated frame here.
  flowKeyPack_of_close (g := none)
    (Or.inl ⟨kc, sp_key, route, head, rfl, Or.inr trivial,
      Or.inl tw99, Or.inl tw108⟩)
    -- Item 300: the base slot's third reading, the marker's line, declined here.
    ⟨h_kc, Or.inr trivial, Or.inr trivial⟩ h_park h_content

-- §3 …and the frame type itself admits the paid key (the structure's field
-- accepts what the props arm now builds), spent through `ofValue`'s twin
-- shape: a fully-paid key is a valid `FlowBaseRoutes`.
example {sp_start sp_br sp_key : SurfPos} {kc : Nat}
    (value : ∀ sp_ne sp_mid, SFlowContent 0 .flowOut sp_br sp_ne →
      SSLComments sp_ne sp_mid → SLYamlStream sp_start sp_mid)
    (route : ∀ sp_v, SBlockMapEntry kc sp_key sp_v → SLYamlStream sp_start sp_v)
    (head : ∀ sp_end, SFlowContent 0 .flowOut sp_br sp_end →
      ImplicitKeyHead sp_key sp_end ∨ True)
    (tw99 : ∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < kc) ∧
      ∀ sp_v : SurfPos, SBlockMapEntry kc sp_key sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail kc sp_v sp_e →
      ResumeFrames (SLYamlStream sp_start) ks sp_e)
    (tw108 : ∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width < kc) ∧
      ∀ sp_v : SurfPos, SBlockMapEntry kc sp_key sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail kc sp_v sp_e →
      KeyFrames (ExplValueLine sp_start nv) ks sp_e) :
    FlowBaseRoutes sp_start 0 sp_br kc none :=
  ⟨fun _ _ => Or.inr trivial, fun _ => value,
   Or.inl ⟨kc, sp_key, route, head, rfl, Or.inr trivial,
     Or.inl tw99, Or.inl tw108⟩,
   Or.inr trivial⟩

/-! ## §4  The deletion proper, measured blocked

The escape's three `block_dispatch_deferred` applications and the one
`dropClose` use stand exactly where items 116–118 left them (the counts are
re-measured in DOCS item 120); the two inline-residue sites still produce
`pendingFlow` off `KeyPackPunt`'s surviving reasons.  `dedent` is R4's
landing pad by design; `noKeyContext` has NO named input (item 104) and its
constructor's deletion is the under-indent invariant's spend — `noFrame`'s
was paid at item 125.  So the rest of 67b — the constructor, `scannerDrop`,
`dropClose`, `close_with_ssl`'s arm — waits on that item, not on this one.
(`FlowStackB.shape` left the list at item 126, unreachable and deleted.) -/

end L4YAML.Tests.Guards.FlowFrameResumeRider

end Blanket
