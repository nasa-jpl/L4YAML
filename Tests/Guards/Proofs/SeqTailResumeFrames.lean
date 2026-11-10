module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The collection's tail behind still-open mapping levels
    (DOCS item 169)

Item 168 read the corpus's 76 dedenting landings by DROP DEPTH — 68 stand on
one open mapping level, 8 on two — and paid the ONE branch that depth named:
the compact key on the `-`'s own line, one level deep.  What that census did
not read is the ENTRY HEAD, and the two are independent.  §2's census reads
both at once and re-sizes the item: the fused face reached **67** of the 76,
not 68 — one of the one-level landings closes an entry whose `-` stands ALONE
on its line, so its key LANDS (`[185]` reaches the mapping through
`s-l+block-node`) and the compact branch that carried item 168's face never
runs.

Framing the lane pays the landed head and the two-level family with one move:
the face becomes `ResumeFrames (SeqEntryTail sp_start ke)` — item 108's bottom
parameter on a THIRD lane, beside the stream and the explicit value line — and
`ks` lists the still-open mapping levels between the innermost one and the
collection.  No cover rides here, unlike item 148's: the only consumer of this
list is a `-` landing back at the collection's own width, and that landing
closes every level (`ResumeFrames.close`) — no width is ever tested for
membership.

§1 pins the three newly-reached families at the runtime, §2 records the
censuses, §3 states the hops at the types the proof composes them at and then
the two-level family end to end, §4 says what is paid and what is not. -/

namespace L4YAML.Tests.Guards.SeqTailResumeFrames

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.NodeProduction

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

private def stk (a : Array IndentEntry) : String :=
  String.intercalate "," (a.toList.map (fun e =>
    s!"{e.column}{if e.isSequence then "S" else "M"}"))

/-- The landing `n` steps in, read as the dedent arms read it (item 167's
    gotcha: the park's stack, BEFORE preprocessing unwinds it). -/
private def dropAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match scanNextToken_preprocess s with
    | .ok (some (s1, c)) =>
      let sd := if s1.allowDirectives then
          { s1 with allowDirectives := false, documentEverStarted := true }
        else s1
      let k : Int := (sd.col : Int)
      let dropped := s.indents.filter (fun e => e.column > k)
      s!"c={c} k={k} park=[{stk s.indents}] drop=[{stk dropped}]"
    | .ok none => "EOF"
    | _ => "no-landing"

/-- The parser's own reading, which is the statement the route has to match. -/
private def ev (input : String) : String :=
  match Events.streamToEvents input with
  | .ok es => String.intercalate " " ((es.splitOn "\n").filter (· ≠ ""))
  | .error e => s!"ERR {repr e}"

/-! ## §1  The families item 168 could not reach, measured

Each landing's park stack beside the levels its unwind drops, and the events
beside both.  Every one emits ONE document whose sequence takes the landing as
its next ENTRY. -/

-- The LANDED head, one level (`examples/2/example-2.4.yaml`'s shape): the `-`
-- stands alone, so its mapping arrives through `[185] s-l+block-node` and the
-- key crosses a break.  ONE of the corpus's 76 — and the one that shows depth
-- and head are independent readings.
#guard dropAt "-\n  a: 1\n  b: 2\n-\n  c: 3\n" 7 == "c=- k=0 park=[-1M,0S,2M] drop=[2M]"
#guard ev "-\n  a: 1\n  b: 2\n-\n  c: 3\n"
  == "+STR +DOC +SEQ +MAP =VAL :a =VAL :1 =VAL :b =VAL :2 -MAP +MAP =VAL :c =VAL :3 -MAP \
      -SEQ -DOC -STR"

-- TWO open levels under a COMPACT head (`examples/other/anchors-aliases.yaml`'s
-- shape, `- step:⏎    instrument: x`): the compact key's VALUE is itself a
-- mapping, so the landing crosses `4M` and then `2M`.  Three of the eight.
#guard dropAt "- a:\n    b: 1\n    c: 2\n- d: 3\n" 9
  == "c=- k=0 park=[-1M,0S,2M,4M] drop=[2M,4M]"
#guard ev "- a:\n    b: 1\n    c: 2\n- d: 3\n"
  == "+STR +DOC +SEQ +MAP =VAL :a +MAP =VAL :b =VAL :1 =VAL :c =VAL :2 -MAP -MAP +MAP \
      =VAL :d =VAL :3 -MAP -SEQ -DOC -STR"

-- TWO open levels under a LANDED head (`…/anchors-aliases2.yaml`'s shape): both
-- moves at once.  The other five of the eight.
#guard dropAt "-\n  a:\n    b: 1\n-\n  a:\n    b: 2\n" 6
  == "c=- k=0 park=[-1M,0S,2M,4M] drop=[2M,4M]"
#guard ev "-\n  a:\n    b: 1\n-\n  a:\n    b: 2\n"
  == "+STR +DOC +SEQ +MAP =VAL :a +MAP =VAL :b =VAL :1 -MAP -MAP +MAP =VAL :a +MAP \
      =VAL :b =VAL :2 -MAP -MAP -SEQ -DOC -STR"

/-! ## §2  The corpus

`Scratch/CensusEntryHead.lean` (gitignored) re-reads item 166's dedenting
landings with BOTH axes at once — drop depth × how the entry's `-` opened:

    d1compact=67  d1alone=1  d1unk=0
    d2compact=3   d2alone=5  d2unk=0

Item 168's face lived on the compact branch at one width, so it reached
`d1compact` alone: **67 of 76**, where its own drop-depth census read 68.  The
other nine are this item: the one landed head at depth one
(`examples/2/example-2.4.yaml` L5), and all eight two-level landings.

`Scratch/CensusDrop2.lean` lists the eight: every one is
`drop=[2M,4M] at=[0S] pen=value` in `examples/other/anchors-aliases.yaml` (3,
compact) and `…/anchors-aliases2.yaml` (5, landed) — a mapping two deep inside
a sequence entry, the park a value's content both times.
`Scratch/CensusAloneList.lean` names the six landed heads: example-2.4's one,
and anchors-aliases2's five. -/

/-! ## §3  The route

The hops item 168 did not have, at the types the proof composes them at, and
then the two-level family whole. -/

-- Ⓐ **The landed head is the entry closure read through `[185]`'s node
-- alternative** — `accum_content_on_pendingBlock{,_indented}`'s payment of
-- `entryKeyPack_of_dispatch.h_nodeSF`.  The frames bottom out at once: the
-- entry's own level is the first mapping level there is.
example {sp_start sp_scan : SurfPos} {n : Nat}
    (h : ∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid →
      SeqEntryTail sp_start n sp_mid) :
    -- Item 179: the entry's node reads at the SHIFTED index.
    ∀ sp_m, SBlockNode (n + 1) .blockIn sp_scan sp_m →
      ResumeFrames (SeqEntryTail sp_start n) [] sp_m :=
  fun sp_m h_bn =>
    ResumeFrames.bottom sp_m (h sp_m (SBlockIndented.node n .blockIn sp_scan sp_m h_bn))

-- Ⓑ **A `pendingMapValue` conses its own level on** — the payment at
-- `accum_content_on_pendingMapValue_indented`'s dispatch sites: the awaited
-- node is this entry's value, behind it the entry's `[187]` level at `n` stays
-- tail-open, and below that stands whatever the park already carries.
-- 2026-11-10 (item 471, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {sp_start sp_scan : SurfPos} {n ke : Nat} {ks : List FrameLevel}
    (h_lt : ∀ fr ∈ ks, fr.width ≤ n)
    (seqF : ∀ sp_mid, SBlockNode n .blockIn sp_scan sp_mid →
      ∀ sp_e, SCompactMapTail n sp_mid sp_e →
      ResumeFrames (SeqEntryTail sp_start ke) ks sp_e) :
    ∀ sp_m, SBlockNode n .blockIn sp_scan sp_m →
      ResumeFrames (SeqEntryTail sp_start ke) (FrameLevel.map n :: ks) sp_m :=
  fun sp_m h_bn =>
    ResumeFrames.level n ks sp_m h_lt (fun sp_end h_tail => seqF sp_m h_bn sp_end h_tail)

-- Ⓒ **The landed key closes the awaited node under the frames** —
-- `entryKeyPack_of_dispatch`'s landed-branch spend of `h_nodeSF`, the same
-- `nestedBlockMap` composition as item 99's `h_nodeF`, at the framed codomain.
example {sp_start sp_scan sp_land sp_key : SurfPos} {n w ke : Nat} {ks : List FrameLevel}
    (hnw : n ≤ w)
    (h_ssl : SSLComments sp_scan sp_land)
    (h_ind' : SIndent w sp_land sp_key)
    (nodeSF : ∀ sp_m, SBlockNode n .blockIn sp_scan sp_m →
      ResumeFrames (SeqEntryTail sp_start ke) ks sp_m) :
    ∀ sp_v, SBlockMapEntry w sp_key sp_v →
    ∀ sp_e, SCompactMapTail w sp_v sp_e →
      ResumeFrames (SeqEntryTail sp_start ke) ks sp_e :=
  fun _sp_v h_entry sp_e h_tail =>
    nodeSF sp_e (nestedBlockMap hnw h_ssl
      (SBlockMapEntries_of_compactTail h_ind' h_entry h_tail))

-- Ⓓ **The sibling landing conses at the frames** — `resumeMapRouteF` at the
-- `SeqEntryTail` bottom, the THIRD instantiation of item 108's parameter.
-- This is where item 168's `seqEntryTail_mapCons` went: the lane stopped
-- needing a lemma of its own.
example {sp_start sp_land sp_key : SurfPos} {k ke : Nat} {ks : List FrameLevel}
    (h_ind : SIndent k sp_land sp_key)
    (h_seq : ∀ sp_end, SCompactMapTail k sp_land sp_end →
      ResumeFrames (SeqEntryTail sp_start ke) ks sp_end) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e →
      ResumeFrames (SeqEntryTail sp_start ke) ks sp_e :=
  resumeMapRouteF h_ind h_seq

-- Ⓔ **The dedenting `-` closes every frame and conses** — the landing reads
-- the park's face at the innermost level's empty tail, `ResumeFrames.close`
-- ends each listed level the same way, and what is left is item 167's
-- `seqEntryTail_cons`.  No membership test anywhere: this consumer closes the
-- list whole, which is why the lane carries no cover.
example {sp_start sp_scan sp_mid sp_sc sp_scan' : SurfPos} {ke kk : Nat} {ks : List FrameLevel}
    (seqF : ∀ sp_m, SSLComments sp_scan sp_m →
      ∀ sp_e, SCompactMapTail kk sp_m sp_e →
      ResumeFrames (SeqEntryTail sp_start ke) ks sp_e)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_ind : SIndent ke sp_mid sp_sc) (h_dash : GLit '-' sp_sc sp_scan')
    (h_gnot : GNot SNsChar sp_scan') :
    ∀ sp_final, SBlockIndented ke .blockIn sp_scan' sp_final →
      ∀ sp_end, SCompactSeqTail ke sp_final sp_end → SLYamlStream sp_start sp_end :=
  seqEntryTail_cons
    ((seqF sp_mid h_ssl sp_mid (SCompactMapTail.nil kk sp_mid)).close)
    h_ind h_dash h_gnot

/-- **The whole of `- a:⏎    b: 1⏎- c`**, composed from the faces the parks
    carry and nothing else.  The fields are optional (`∨ True`) at every hop,
    so a green build does not witness the wiring — this term does: the compact
    key's value is ITSELF a mapping, its key `b` lands one level deeper, and
    the dedenting `-` comes back through BOTH open levels to the collection.
    Item 168's face could not state this route at any instantiation. -/
example {sp_start sp_scan sp_key sp_ws sp_val sp_land sp_key2 sp_ws2 sp_val2
         sp_park2 sp_mid sp_sc sp_scan' : SurfPos} {n w w2 : Nat}
    -- the park the first `-` opened — `pendingBlock n`'s own entry closure
    (h_close_entry : ∀ sp, SBlockIndented n .blockIn sp_scan sp →
      ∀ sp_end, SCompactSeqTail n sp sp_end → SLYamlStream sp_start sp_end)
    -- `a:` on the indicator's own line, its value awaited
    (h_ind : SIndent w sp_scan sp_key)
    (h_ik : SImplicitKey sp_key sp_ws) (h_lit : GLit ':' sp_ws sp_val)
    -- `b: 1` — the inner mapping the value turns out to be, one level deeper
    -- (item 179: STRICTLY deeper than the compact entry's column)
    (hn1w2 : n + 1 + w + 1 ≤ w2)
    (h_ssl : SSLComments sp_val sp_land)
    (h_ind2 : SIndent w2 sp_land sp_key2)
    (h_ik2 : SImplicitKey sp_key2 sp_ws2) (h_lit2 : GLit ':' sp_ws2 sp_val2)
    (h_node2 : ∀ sp_m, SSLComments sp_park2 sp_m → SBlockNode (w2 + 1) .blockIn sp_val2 sp_m)
    -- `- c` — the dedent, back at the collection's own width, TWO levels down
    (h_ssl2 : SSLComments sp_park2 sp_mid)
    (h_ind3 : SIndent n sp_mid sp_sc) (h_dash : GLit '-' sp_sc sp_scan')
    (h_gnot : GNot SNsChar sp_scan') :
    ∀ sp_final, SBlockIndented n .blockIn sp_scan' sp_final →
      ∀ sp_end, SCompactSeqTail n sp_final sp_end → SLYamlStream sp_start sp_end := by
  -- ① the head is free: the entry closure IS the tail at the park's width
  have f1 : ∀ sp, SBlockIndented n .blockIn sp_scan sp → SeqEntryTail sp_start n sp :=
    h_close_entry
  -- ② the compact `:` wraps into `[195]`, frames empty
  have f2 : ∀ sp_v, SBlockMapEntry (n+1+w) sp_key sp_v →
      ∀ sp_e, SCompactMapTail (n+1+w) sp_v sp_e →
      ResumeFrames (SeqEntryTail sp_start n) [] sp_e :=
    fun sp_v h_entry sp_e h_tail =>
      ResumeFrames.bottom sp_e
        (f1 sp_e (SBlockIndented.compactMap n .blockIn w sp_scan sp_key sp_e h_ind
          (SCompactMap.mk (n+1+w) sp_key sp_v sp_e h_entry h_tail)))
  -- ③ the `:` parks the value — `pendingMapValue (n+1+w)`'s `h_seqF`
  have f3 : ∀ sp_m, SBlockNode (n+1+w+1) .blockIn sp_val sp_m →
      ∀ sp_e, SCompactMapTail (n+1+w) sp_m sp_e →
      ResumeFrames (SeqEntryTail sp_start n) [] sp_e :=
    fun sp_m h_nd sp_e h_tail =>
      f2 sp_m (SBlockMapEntry.implicitKeyNode (n+1+w) sp_key sp_ws sp_val sp_m h_ik h_lit
        (SBlockNode_blockIn_to_blockOut h_nd)) sp_e h_tail
  -- ④ hop Ⓑ: the park conses its own level onto the frames
  have f4 : ∀ sp_m, SBlockNode (n+1+w+1) .blockIn sp_val sp_m →
      ResumeFrames (SeqEntryTail sp_start n) [FrameLevel.map (n+1+w)] sp_m :=
    fun sp_m h_bn =>
      ResumeFrames.level (n+1+w) [] sp_m (by simp)
        (fun sp_end h_tail => f3 sp_m h_bn sp_end h_tail)
  -- ⑤ hop Ⓒ: `b` lands one level deeper and closes the awaited node
  have f5 : ∀ sp_v, SBlockMapEntry w2 sp_key2 sp_v →
      ∀ sp_e, SCompactMapTail w2 sp_v sp_e →
      ResumeFrames (SeqEntryTail sp_start n) [FrameLevel.map (n+1+w)] sp_e :=
    fun sp_v h_entry sp_e h_tail =>
      f4 sp_e (nestedBlockMap hn1w2 h_ssl
        (SBlockMapEntries_of_compactTail h_ind2 h_entry h_tail))
  -- ⑥ `b:` parks ITS value in turn — the inner `pendingMapValue`'s `h_seqF`
  have f6 : ∀ sp_m, SBlockNode (w2 + 1) .blockIn sp_val2 sp_m →
      ∀ sp_e, SCompactMapTail w2 sp_m sp_e →
      ResumeFrames (SeqEntryTail sp_start n) [FrameLevel.map (n+1+w)] sp_e :=
    fun sp_m h_nd sp_e h_tail =>
      f5 sp_m (SBlockMapEntry.implicitKeyNode w2 sp_key2 sp_ws2 sp_val2 sp_m h_ik2 h_lit2
        (SBlockNode_blockIn_to_blockOut h_nd)) sp_e h_tail
  -- ⑦ `1` completes the value — `pendingContent.h_seqF`'s reading
  have f7 : ∀ sp_m, SSLComments sp_park2 sp_m →
      ∀ sp_e, SCompactMapTail w2 sp_m sp_e →
      ResumeFrames (SeqEntryTail sp_start n) [FrameLevel.map (n+1+w)] sp_e :=
    fun sp_m h_c sp_e h_tail => f6 sp_m (h_node2 sp_m h_c) sp_e h_tail
  -- ⑧ hop Ⓔ: the `-` closes the inner level, the listed one, and conses
  exact seqEntryTail_cons
    ((f7 sp_mid h_ssl2 sp_mid (SCompactMapTail.nil w2 sp_mid)).close)
    h_ind3 h_dash h_gnot

/-! ## §4  What is paid, and what is not

The framed face replaces the fused one on every carrier item 168 built —
`ImplicitKeyPack`'s fourth twin, `pendingMapValue.h_seqF`,
`pendingContent.h_seqF`, `ResumeKeyCtx`, `content_dispatch_routed`'s resuming
context, the block-landing dispatcher — so the one-width readings survive as
the `ks = []` instance and no producer got weaker.

New payments.  `entryKeyPack_of_dispatch` gains `h_nodeSF` (the LANDED key's
sequence face, hop Ⓐ's shape at `≤ n` because the list may include `n`
itself), spent at its landed branch (hop Ⓒ); the two `pendingBlock` dispatch
arms and the root site pay it from `h_close_entry_old` through
`SBlockIndented.node` with the frames bottomed — the landed head's whole
difference from the compact one.  `accum_content_on_pendingMapValue_indented`
pays it with its own level consed on (hop Ⓑ), which is what reaches a mapping
two levels inside the entry.  The ROOT `pendingMapValue` arm punts: a value at
index 0 is the root mapping's, and no sequence entry encloses it.

`seqEntryTail_mapCons` is DELETED — the sibling cons is `resumeMapRouteF` at
the third instantiation of item 108's bottom parameter (hop Ⓓ).

No cover rides this lane, and that is a difference in KIND from item 148's
frames: `resumeAt` funds a membership test, and this lane's only consumer
closes every level (`ResumeFrames.close`, hop Ⓔ) — no width is compared, so
there is nothing for a cover to pay for.

What is punted, in the corpus's own numbers: nothing the corpus contains —
67 + 1 + 8 = 76 of 76 dedenting landings now have their producer path.  Still
open from item 167: the sequence-crossing dedent (`dropSeq = 0`, no input),
and — outside this lane entirely — the `[210]` flip's same five construction
sites. -/

end L4YAML.Tests.Guards.SeqTailResumeFrames

end Blanket
