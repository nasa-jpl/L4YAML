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

/-! # A landing after a block ENTRY's completed content resumes its level (DOCS item 110)

Item 109 gave `accum_content_pending`'s landing skeleton the frames and paid
them for `pendingContent`, the park a completed MAPPING VALUE leaves.  The
sibling park — `pendingBlockContent`, a `[184]` sequence entry whose own node is
complete (`- a`, `- [1]`, `- "p⏎  q"`) — kept punting, so a landing after it
still closed the collection and re-opened at the root under `[211]`'s
`implicitContinue`.  `k:⏎  - a⏎b: 2` is ONE root mapping with two entries; the
root context could only give its `b` a second bare document.

**No new field.**  Item 99 sized `pendingBlockContent.h_closeF` at the ENTRY
level — the landing's `[79] s-l-comments` closes this entry, `[183]`'s remaining
tail rides, and the levels BELOW the sequence stand ready — and then left every
producer punting it.  So this item is two payments and a spend: the two indexed
producers already hold `pendingBlock.h_closeF` and transport it for the pack's
resume twin, and the landing arm reads the field with a `nil` tail.

**The ROOT producer keeps punting, and that is a refusal rather than a gap**:
after a root `-` there is no enclosing level for a landing to resume, and the
scanner says so — `- a⏎b: 2` is `trailingContent`.  §1 pins it.

§1 is the family at the runtime; §2–§5 are the payment and the spend at their
types; §6 is what this item does not close.

*Correcting item 109's own note*: its §7 named `- a: b⏎  c: d` as
`pendingBlockContent`'s input.  That input parks `pendingContent` — the `b` is a
completed mapping value, and `[195]`'s compact mapping is what its `c: d`
continues.  `pendingBlockContent`'s family is the one below. -/

namespace L4YAML.Tests.Guards.ScannerEntryContentSiblingResumes

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.CouplingBridge

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The family.  The entry's content is complete and the landing dedents to a
-- level the sequence stands inside: ONE `+DOC`, and `b` is `k`'s sibling.
#guard emits "k:\n  - a\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "-SEQ", "=VAL :b",
   "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The collection takes its own siblings first; the resumed level is reached
-- only when the width drops out of it.
#guard emits "k:\n  - a\n  - b\nc: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ",
   "=VAL :c", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The two paying arms are `indentedValue_reads_at_any_indent`'s flow/plain one …
#guard emits "k:\n  - [1]\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ",
   "-SEQ", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- … and its MULTI-LINE value one (items 53/54's arm), whose node is read at the
-- entry's own index and folded in identically.
#guard emits "k:\n  - \"p\n    q\"\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"p q", "-SEQ", "=VAL :b",
   "=VAL :2", "-MAP", "-DOC", "-STR"]
-- **The stack is a stack.**  Two open mapping levels below the sequence, and
-- the landing resumes the INNER one — `n` is `m`'s sibling, not `k`'s, and
-- there is still exactly one document.
#guard emits "k:\n  m:\n    - a\n  n: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ", "=VAL :a",
   "-SEQ", "=VAL :n", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]

-- The boundaries, both refusals.  A ROOT `-` has no enclosing level, which is
-- why that producer's punt costs nothing: the input it would serve does not
-- exist.
#guard refuses "- a\nb: 2\n"
-- And a landing width that names no resumable level is `trailingContent` too —
-- the case `ResumeFrames.resumeAt`'s membership test defers rather than
-- assumes, here at the entry-parked face.  The stack holds MAPPING levels
-- (`SCompactMapTail k`), so it is `{0}` below the first sequence and `{0, 2}`
-- below the second; a landing at width 1 names neither.
#guard refuses "k:\n  - a\n b: 2\n"
#guard refuses "k:\n  m:\n    - a\n n: 2\n"

/-! ## §2 The producer's payment: the entry node that `h_close_entry_old` folds

`pendingBlock.h_closeF` takes the entry's `[185] s-l+block-indented` slot and
`[183]`'s remaining tail; `pendingBlockContent.h_closeF` takes the landing's
`[79] s-l-comments` and the same tail.  The step between them is the node this
content scan just completed — the SAME wrap the park's `h_closable_entry`
already makes, so the field is free wherever that closure is. -/

example {sp_start sp_scan sp_park : SurfPos} {n : Nat} {ks : List FrameLevel}
    -- Item 179: the completed node reads at the SHIFTED index; the entry
    -- slot and the tail stay at the raw column.
    (build : ∀ sp_mid, SSLComments sp_park sp_mid → SBlockNode (n + 1) .blockIn sp_scan sp_mid)
    (closeF : ∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid →
      ∀ sp_end, SCompactSeqTail n sp_mid sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    ∀ sp_mid, SSLComments sp_park sp_mid →
    ∀ sp_end, SCompactSeqTail n sp_mid sp_end →
    ResumeFrames (SLYamlStream sp_start) ks sp_end :=
  fun sp_mid h_ssl =>
    closeF sp_mid (SBlockIndented.node n .blockIn sp_scan sp_mid (build sp_mid h_ssl))

/-! ## §3 The landing's spend: the entry-level face at an EMPTY tail

The landing ended the collection, so `[183]`'s remaining tail is `nil` and what
is left standing is exactly the skeleton's `h_fS` — the shape item 109 gave
`h_defer_split`.  This is the whole reason the field did not have to be
re-sized: an entry-level face is a landing-level face at the empty tail. -/

example {sp_start sp_park : SurfPos} {n : Nat} {ks : List FrameLevel}
    (closeF : ∀ sp_mid, SSLComments sp_park sp_mid →
      ∀ sp_end, SCompactSeqTail n sp_mid sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    ∀ sp_m, SSLComments sp_park sp_m → ResumeFrames (SLYamlStream sp_start) ks sp_m :=
  fun sp_m h_ssl => closeF sp_m h_ssl sp_m (SCompactSeqTail.nil n sp_m)

/-! ## §4 Nothing the park already said gets weaker

`h_closable_entry` is `h_closeF`'s `ResumeFrames.close`, exactly as
`pendingContent`'s `h_closable` is its stream face's (item 109 §3).  A producer
that pays the frames owes nothing new, and the two that still punt lose
nothing. -/

example {sp_start sp_park : SurfPos} {n : Nat} {ks : List FrameLevel}
    (closeF : ∀ sp_mid, SSLComments sp_park sp_mid →
      ∀ sp_end, SCompactSeqTail n sp_mid sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    ∀ sp_mid, SSLComments sp_park sp_mid →
    ∀ sp_end, SCompactSeqTail n sp_mid sp_end → SLYamlStream sp_start sp_end :=
  fun sp_mid h_ssl sp_end h_tail => (closeF sp_mid h_ssl sp_end h_tail).close

/-! ## §5 …and it reaches item 109's context lemma unchanged

`resumectx_of_landing` is polymorphic in nothing — it takes the two faces the
skeleton passes — so the entry-parked park reaches it with the same argument the
value-parked one does.  That the informative disjunct is REACHABLE is what a
`∨ True` lets a guard check; which branch a given input takes is not observable
(proof irrelevance, CLAUDE.md §7). -/

example {sc s_prep : ScannerState} {c : Char}
    {sp_start sp_park sp_mid sp_prep : SurfPos} {n : Nat} {ks : List FrameLevel}
    (hcol_mid : sp_mid.col = 0)
    (h_ws : GStar SSWhite sp_mid sp_prep)
    (h_ssl : SSLComments sp_park sp_mid)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (closeF : ∀ sp_m, SSLComments sp_park sp_m →
      ∀ sp_end, SCompactSeqTail n sp_m sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) 
    (h_alt : PackAlt sc)
    -- Item 374: the sentinel base, for the sequence-top face the declined resume now carries.
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    ResumeKeyCtx s_prep sp_start sp_prep :=
  -- Item 151: the entry-parked face carries no cover (`pendingBlock.h_closeF`
  -- is the widths alone), so the slot and the payer both take the punt — which
  -- is the argument this park actually passes at the relay.
  resumectx_of_landing (h_base := h_base) hcol_mid h_ws h_ssl h_preprocess hcorr_prep
    (Or.inl ⟨ks, Or.inr trivial,
      fun sp_m h => closeF sp_m h sp_m (SCompactSeqTail.nil n sp_m)⟩)
    (Or.inr h_alt)
    (fun _ _ _ _ _ _ _ => Or.inr trivial)
    -- Item 168: the sequence face punts here — this park's own collection is
    -- item 167's entry-level field, not a mapping level's.
    (Or.inr trivial)

/-! ## §6 What this item does NOT close

* The park's VALUE face.  A `[184]` entry's explicit frame is `h_kslot` — a
  single `[190]` value line, not a `ResumeFrames` — so there is no
  `ExplValueLine`-bottomed stack to hand the skeleton, and `h_fV` stays
  `Or.inr trivial` here (item 108's note at the producers).
* The ROOT producer, whose punt §1 shows to be a refusal.
* The PROPS landing.  `content_dispatch_routed`'s `h_props_key` still reads only
  the root key context; `PropsKeyPack` carries no resume twin to spend.  (CLOSED
  by item 111 — its family is `k:⏎  - a⏎&p b: 2`, the run at the LANDING.
  ~~`k:⏎  - &p a⏎b: 2`~~ was the wrong input to name here: its landing head is
  plain `b`, and what stays root-parked in it is the props-decorated VALUE
  completion's `pendingContent` faces, one of item 109's punting producers.)
* The block-scalar value arms of the two `accum_content_on_pendingMapValue`
  (one lemma since item 179)
  lemmas (CLOSED by item 112 — the node re-read to the landing), and the BLOCK
  dispatch's own `pendingBlockContent` arm
  (`accum_block_on_pendingBlockContent`) — this item, like item 109, is the
  CONTENT dispatch's landing skeleton only.
* The construction sites.  `SLYamlStream.implicitContinue` still takes
  `GOpt SLAnyDocument`; tightening it breaks 16 sites in `StreamAccum`, measured
  2026-09-07, and the fallback two of them are (`rootMapRoute`/`rootMapRouteF`)
  is what every punting park still uses. -/

end L4YAML.Tests.Guards.ScannerEntryContentSiblingResumes

end Blanket
