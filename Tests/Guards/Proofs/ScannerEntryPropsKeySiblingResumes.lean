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

/-! # An entry-parked props key keeps its context's frames (DOCS item 115)

Item 111 gave `PropsKeyPack` the two resume twins and paid them at the
LANDING producer (`h_props_key`); the ENTRY producer —
`entryPropsKeyPack_of_dispatch`, the pack a parked block entry hands the run
it just scanned — still punted both, and had no dedent branch at all.  So
inside a still-open construct the props-headed key dropped its levels at the
`:`: `?⏎  &p a: b⏎  c: d⏎: - w`'s `c` could be given only as a fresh `[187]`
under a second bare document, and `k:⏎  a:⏎&p b: 2` deferred where its
implicit twin (item 99) had popped for two items already.

**The build is `entryKeyPack_of_dispatch`'s four threaded premises (items
99/108), transposed verbatim.**  The lemma gains `h_nodeF`/`h_dframes` (the
stream-bottomed pair) and `h_nodeFV`/`h_dframesV` (the value-line-bottomed
pair, item 108's); the LANDED branch pays the pack's twins from the
node-domain pair whenever the landing is strictly deeper (`n < w` — at
`w = n` the sibling belongs to the level itself); the DEDENT branch pops the
comment-domain pair exactly as the implicit twin's does.  The six callers pay
what their parks hold: the mapping-value producers hand their own
`h_closeF99`/`h_frames99`/`h_closeFV*`/`h_framesV*`, the indented sequence
producer folds its entry into `h_closeF_old` with a nil tail, and the root
sequence producers punt all four as refusals.  No consumer changes:
`colon_open_map_props` has spent whatever rides since item 111.

§1 is the family at the runtime; §2–§3 are the payment and the pop at their
types; §4 is what this item does not close. -/

namespace L4YAML.Tests.Guards.ScannerEntryPropsKeySiblingResumes

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
  L4YAML.Proofs.NodeProduction
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

-- §1 The family.  **The exemplar**: the props-headed key lands strictly
-- deeper inside an open `?`, its sibling conses at the same width, and the
-- frame's own value line still closes — ONE document, where the punted twins
-- could offer the `c` only as a second bare document.
#guard emits "?\n  &p a: b\n  c: d\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL &p :a", "=VAL :b", "=VAL :c",
   "=VAL :d", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The tag head takes the same route.
#guard emits "?\n  !!str a: b\n  c: d\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL <tag:yaml.org,2002:str> :a",
   "=VAL :b", "=VAL :c", "=VAL :d", "-MAP", "+SEQ", "=VAL :w", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- …and without the explicit value line, the `?`'s value is null.
#guard emits "?\n  &p a: b\n  c: d\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL &p :a", "=VAL :b", "=VAL :c",
   "=VAL :d", "-MAP", "=VAL :", "-MAP", "-DOC", "-STR"]
-- Item 106's baseline, unchanged: no sibling, the value line alone.
#guard emits "?\n  &p a: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL &p :a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- **The full nested thread**: land deeper, cons the sibling, then pop to the
-- enclosing level — the twins carry the levels through the props-headed key.
#guard emits "k:\n  a:\n    &p b: c\n    d: e\n  f: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP",
   "=VAL &p :b", "=VAL :c", "=VAL :d", "=VAL :e", "-MAP", "=VAL :f",
   "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
-- …and without the pop, the resumed level just closes.
#guard emits "k:\n  a:\n    &p b: c\n    d: e\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP",
   "=VAL &p :b", "=VAL :c", "=VAL :d", "=VAL :e", "-MAP", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- **The dedent, at the sequence entry**: the awaited `-` closes null, the
-- landing pops to the root, and the props-headed key conses there.
#guard emits "k:\n  -\n&p b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :", "-SEQ",
   "=VAL &p :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- **The dedent, at the mapping value**: `a`'s value closes null, `b` is
-- `k`'s sibling with the anchor on it — ONE outer mapping.
#guard emits "k:\n  a:\n&p b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :", "-MAP",
   "=VAL &p :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The tag twin of the dedent.
#guard emits "k:\n  a:\n!!str b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :", "-MAP",
   "=VAL <tag:yaml.org,2002:str> :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- **The value-line stack pops independently** (item 108's shape, at the
-- run): a dedent sibling INSIDE an explicit key keeps the `?` open.
#guard emits "?\n  a:\n    b:\n  &p c: 2\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :",
   "-MAP", "=VAL &p :c", "=VAL :2", "-MAP", "+SEQ", "=VAL :w", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- The equal-width landing (`w = n`): the sibling belongs to the level
-- itself, which is why the twins pay only strictly deeper.
#guard emits "?\n  a:\n  &p b: 2\n: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :", "=VAL &p :b",
   "=VAL :2", "-MAP", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- The indented sequence entry's landed nesting…
#guard emits "k:\n  -\n    &p b: c\n    d: e\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL &p :b",
   "=VAL :c", "=VAL :d", "=VAL :e", "-MAP", "-SEQ", "-MAP", "-DOC", "-STR"]
-- …and the sequence sibling after it (a `-` landing is not a key, so it
-- rides the entry chain, not the pack — §4).
#guard emits "k:\n  -\n    &p b: c\n  - y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL &p :b",
   "=VAL :c", "-MAP", "=VAL :y", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The nested landing inside a `?`, closed by the frame's value line.
#guard emits "?\n  a:\n    &p b: c\n    d: e\n: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "+MAP", "=VAL &p :b",
   "=VAL :c", "=VAL :d", "=VAL :e", "-MAP", "-MAP", "=VAL :v", "-MAP",
   "-DOC", "-STR"]

-- The boundaries.  A landing width naming no open level is refused upstream,
-- so the dedent's non-member deferral has no input.
#guard refuses "k:\n  a:\n &p b: 2\n"
-- A map key at the `-`'s own column after an empty entry is refused — the
-- sequence producers' punts are refusal-backed.
#guard refuses "k:\n  -\n  &p b: 2\n"
-- …as is the root sequence's (`- x⏎&p b: 2`'s shape at the empty entry).
#guard refuses "-\n&p b: 2\n"

/-! ## §2 The landed payment: the nested mapping chains onto the frames

Items 99/108's terms verbatim — the run-headed entry and its tail close the
mapping the caller's node awaits (`nestedBlockMap` over the compact tail),
and the caller's frames carry on below it.  The strictly-deeper landing
re-bounds the stack under `w`, which is the pack's own side condition. -/

example {sp_start sp_scan sp_mid sp_prep : SurfPos} {n w : Nat} {ks : List FrameLevel}
    (hnw : n ≤ w) (hlt : n < w)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_ind : SIndent w sp_mid sp_prep)
    (h_le : ∀ fr ∈ ks, fr.width ≤ n)
    (nodeF : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_scan sp_m →
      ResumeFrames (SLYamlStream sp_start) ks sp_m) :
    (∀ fr ∈ ks, fr.width < w) ∧
    (∀ sp_v : SurfPos, SBlockMapEntry w sp_prep sp_v →
     ∀ sp_e : SurfPos, SCompactMapTail w sp_v sp_e →
     ResumeFrames (SLYamlStream sp_start) ks sp_e) :=
  ⟨fun k' hk' => Nat.lt_of_le_of_lt (h_le k' hk') hlt,
   fun _sp_v h_entry sp_e h_tail =>
     nodeF sp_e (nestedBlockMap hnw h_ssl
       (SBlockMapEntries_of_compactTail h_ind h_entry h_tail))⟩

/-! ## §3 The dedent pop: one polymorphic spend serves both stacks

Item 108's parameterized bottom is what makes the transposition one term:
the pop below is stated over any `P`, so instantiating it at
`SLYamlStream sp_start` gives the pack's route and stream twin, and at
`ExplValueLine sp_start nv` its value-line twin — the two `match`es in the
lemma's dedent branch are this example twice. -/

-- 2026-11-10 (item 473, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {P : SurfPos → Prop} {sp_scan sp_mid sp_prep : SurfPos}
    {w : Nat} {ks : List FrameLevel}
    (hmem : FrameLevel.map w ∈ ks)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_ind : SIndent w sp_mid sp_prep)
    (dframes : ∀ sp_m : SurfPos, SSLComments sp_scan sp_m →
      ResumeFrames P ks sp_m) :
    (∀ sp_v, SBlockMapEntry w sp_prep sp_v → P sp_v) ∧
    ∃ ks' : List FrameLevel, (∀ fr ∈ ks', fr.width ≤ w) ∧
      ∀ sp_v : SurfPos, SBlockMapEntry w sp_prep sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail w sp_v sp_e →
      ResumeFrames P ks' sp_e := by
  obtain ⟨ks', h_w', cont'⟩ := (dframes sp_mid h_ssl).resumeAt hmem
  exact ⟨fun sp_v h_entry =>
    (cont' sp_v (SCompactMapTail.cons w sp_mid sp_prep sp_v sp_v
      h_ind h_entry (SCompactMapTail.nil w sp_v))).close,
    ks', h_w'.le, fun sp_v h_entry sp_e h_tail =>
      cont' sp_e (SCompactMapTail.cons w sp_mid sp_prep sp_v sp_e
        h_ind h_entry h_tail)⟩

/-! ## §4 What this item does NOT close

* The COMPACT branch's twins — item 99's residue, shared with
  `entryKeyPack_of_dispatch`'s compact branch on both packs: the frame's
  levels are fused into the enclosing entry's closure, so
  `? - &p a: b⏎...`'s compact key still hands `Or.inr trivial` twice.
* The sequence SIBLING after a landed nesting (`k:⏎  -⏎    &p b: c⏎  - y`,
  §1's runtime pin): a `-` landing is not a key, so it is outside the pack —
  the entry chain serves it or defers, identically on the implicit side.
* The root sequence producers punt all four faces on BOTH packs (a root `- `
  holds no frames); their dedent inputs are `trailingContent`, pinned in §1.
* The flow frame's rider (`FlowBaseRoutes.key` carries the value-line pair
  only — 67b's carrier) and the "no document started" carrier — items 111's
  and 110's residues, untouched here.  (The latter CLOSED by item 116 —
  `noPending.h_nodoc`.) -/

end L4YAML.Tests.Guards.ScannerEntryPropsKeySiblingResumes

end Blanket
