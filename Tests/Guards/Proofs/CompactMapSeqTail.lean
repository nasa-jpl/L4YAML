module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The compact mapping that fills a sequence entry, and the tail it owes
    (DOCS item 168)

Item 167 built `SeqEntryTail` and paid it on the two ENTRY parks, then measured
that the corpus puts nothing there: over 490 files not one dedenting `-` crosses
an open block SEQUENCE.  What the corpus HAS is the other half — **76** landings
whose unwind drops block MAPPING levels — and **75 of the 76 park after a mapping
VALUE**, which is `pendingContent`, a park item 167's field never reaches.  This
file measures that family and carries the route to it.

**The cascade is three hops and a loop.**  The collection's tail leaves the entry
park at the compact `:` (`ImplicitKeyPack`'s own sequence face), arrives on
`pendingMapValue`, comes back out on `pendingContent` with the value — and then
has to survive every SIBLING key inside the same mapping before the dedenting `-`
arrives.  §2 measures how much of that is load-bearing: **62 of the 68** reachable
landings dedent out of a MULTI-line entry, so the sibling hop is the item rather
than a refinement of it.

**One width, not a stack** — item 167's choice, made again and measured again.
The face names the innermost open mapping level and fuses everything below it, so
it serves the **68** landings that stand on exactly one open level and punts the
**8** that stand on two.  A stack here is `ResumeFrames (SeqEntryTail sp_start ke)`
— item 108's parameter on a third bottom — and those eight are what it would buy.
(Item 169 built that stack, and reading the entry HEAD showed it buys more than
the eight — see `SeqTailResumeFrames.lean`; this file's fused readings survive as
the `ks = []` instance.)

§1 pins the family at the runtime, §2 records the censuses, §3 composes the route
hop by hop and then end to end, §4 says what is paid and what is not. -/

namespace L4YAML.Tests.Guards.CompactMapSeqTail

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
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

/-- The landing `n` steps in, read as the dedent arms read it: the PARK's own
    indent stack (before preprocessing unwinds it — item 167's gotcha), the
    landing's column, and the levels the unwind drops between the two. -/
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

/-! ## §1  The family, measured

Each landing's park stack beside the levels its unwind drops, and the events
beside both.  Every one of these emits ONE document whose sequence takes the
landing as its next ENTRY — which is what says the second `-` is not a second
bare document. -/

-- The ONE-LINE entry: the `:` alone carries the collection across.  Six of the
-- corpus's 68 look like this.
#guard dropAt "- a: 1\n- b: 2\n" 4 == "c=- k=0 park=[-1M,0S,2M] drop=[2M]"
#guard ev "- a: 1\n- b: 2\n"
  == "+STR +DOC +SEQ +MAP =VAL :a =VAL :1 -MAP +MAP =VAL :b =VAL :2 -MAP -SEQ -DOC -STR"

-- The MULTI-LINE entry — the other 62.  The park the `-` meets is reached
-- through a SIBLING landing (`b` at width 2), so the face has to survive a hop
-- that closes nothing.
#guard dropAt "- a: 1\n  b: 2\n- c: 3\n" 7 == "c=- k=0 park=[-1M,0S,2M] drop=[2M]"
#guard ev "- a: 1\n  b: 2\n- c: 3\n"
  == "+STR +DOC +SEQ +MAP =VAL :a =VAL :1 =VAL :b =VAL :2 -MAP +MAP =VAL :c =VAL :3 -MAP \
      -SEQ -DOC -STR"

-- §8.2.1's `m = 0`: the sequence sits at its parent MAPPING's own column, so it
-- is NOT on the indent stack and the level at `k` reads `M`.  Two of the 76 are
-- this shape (`examples/2/example-2.27.yaml`, `…2.28.yaml`), and the route does
-- not care: `SeqEntryTail` is a production, not a stack entry.
#guard dropAt "S:\n- f: x\n  g: 2\n- f: y\n" 9 == "c=- k=0 park=[-1M,0M,2M] drop=[2M]"
#guard ev "S:\n- f: x\n  g: 2\n- f: y\n"
  == "+STR +DOC +MAP =VAL :S +SEQ +MAP =VAL :f =VAL :x =VAL :g =VAL :2 -MAP +MAP =VAL :f \
      =VAL :y -MAP -SEQ -MAP -DOC -STR"

-- TWO open levels — the punt.  The value of `a:` opens a second mapping, so the
-- landing crosses `4M` as well as `2M` and one width cannot name both.  Eight of
-- the 76.
#guard dropAt "- a:\n    b: 1\n- c\n" 6 == "c=- k=0 park=[-1M,0S,2M,4M] drop=[2M,4M]"

/-! ## §2  The corpus

`Scratch/CensusMapCascade.lean` (gitignored) re-reads item 166's 134
surviving-branch landings and splits the 76 that drop a level by the park's tail
token and by the level the landing comes back to:

    hits=134  drop=76
    tScalar=73  tAlias=2  tFlowSeqEnd=0  tFlowMapEnd=1
    atSeq=74  atMap=2  atNone=0
    pValue=75  pEntry=0  pOther=1

`pValue=75` is the finding that aimed this item: the token BEFORE the park's
tail is a `:` in 75 of the 76, so the park is a mapping value's content and the
route has to cross the `:`.  `atMap=2` is §8.2.1's `m = 0` (§1's third shape);
`pOther=1` is `examples/2/example-2.24.yaml`, whose tail is a flow mapping's `}`
— same family, different token.

`Scratch/CensusDropDepth.lean` splits the same 76 by how many levels the unwind
drops:

    drop1=68  drop1Map=68  drop2=8  drop3p=0
    drop1AtSeq=66  drop1AtMap=2

so one open level covers 68 and two covers the rest, and nothing in the corpus
needs three.  `Scratch/CensusSiblingHop.lean` then asks of those 68 whether the
entry they dedent OUT of spans one line or several:

    hits=68  oneLine=6  multiLine=62  unknown=0

which is why §3's hop ⑤ is the item.  Without it the cascade reaches only the
six one-line entries. -/

/-! ## §3  The route

Hop by hop, at the types the proof composes them at, and then the whole of
`- a: X⏎  b: Y⏎- c` in one term. -/

-- ① **The head is free.**  `pendingBlock.h_close_entry` and
-- `pendingBlockContent.h_closable_entry` ARE the sequence face at the park's own
-- width — `SeqEntryTail` unfolds to exactly their codomain — so the cascade
-- costs no new producer where it starts.
example {sp_start sp_scan : SurfPos} {n : Nat}
    (h : ∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid →
      ∀ sp_end, SCompactSeqTail n sp_mid sp_end → SLYamlStream sp_start sp_end) :
    ∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid → SeqEntryTail sp_start n sp_mid := h

-- ② **The compact `:` wraps into `[195]`** — `entryKeyPack_of_dispatch`'s
-- compact branch, one application short of where `compactMapRoute` stops.
example {sp_start sp_scan sp_key : SurfPos} {n w ke : Nat}
    (h_nodeS : ∀ sp, SBlockIndented n .blockIn sp_scan sp → SeqEntryTail sp_start ke sp)
    (h_ind : SIndent w sp_scan sp_key) :
    ∀ sp_v, SBlockMapEntry (n + 1 + w) sp_key sp_v →
      ∀ sp_e, SCompactMapTail (n + 1 + w) sp_v sp_e → SeqEntryTail sp_start ke sp_e :=
  fun sp_v h_entry sp_e h_tail =>
    h_nodeS sp_e
      (SBlockIndented.compactMap n .blockIn w sp_scan sp_key sp_e h_ind
        (SCompactMap.mk (n + 1 + w) sp_key sp_v sp_e h_entry h_tail))

-- ③ **The `:` parks the value** — `colon_open_map_implicit`, where the pack's
-- face becomes `pendingMapValue.h_seqF`.
example {sp_start sp_key sp_ws sp_scan' : SurfPos} {k ke : Nat}
    (h_routeS : ∀ sp_v, SBlockMapEntry k sp_key sp_v →
      ∀ sp_e, SCompactMapTail k sp_v sp_e → SeqEntryTail sp_start ke sp_e)
    (h_ik : SImplicitKey sp_key sp_ws) (h_lit : GLit ':' sp_ws sp_scan') :
    -- Item 179: the entry's value reads at the SHIFTED index.
    ∀ sp_mid, SBlockNode (k + 1) .blockIn sp_scan' sp_mid →
      ∀ sp_e, SCompactMapTail k sp_mid sp_e → SeqEntryTail sp_start ke sp_e :=
  fun sp_v h_node sp_e h_tail =>
    h_routeS sp_v
      (SBlockMapEntry.implicitKeyNode k sp_key sp_ws sp_scan' sp_v h_ik h_lit
        (SBlockNode_blockIn_to_blockOut h_node))
      sp_e h_tail

-- ⑤ **The sibling landing conses and keeps the collection** — the hop 62 of the
-- 68 need.  Since item 169 framed the lane this cons is `resumeMapRouteF` at
-- the `SeqEntryTail` bottom (the third instantiation of item 108's parameter);
-- the fused reading here is its `ks = []` instance, closed on the spot.
example {sp_start sp_land sp_key : SurfPos} {k ke : Nat}
    (h_ind : SIndent k sp_land sp_key)
    (h_seq : ∀ sp_end, SCompactMapTail k sp_land sp_end → SeqEntryTail sp_start ke sp_end) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e → SeqEntryTail sp_start ke sp_e :=
  fun sp_v h_entry sp_e h_tail =>
    (resumeMapRouteF h_ind
      (fun sp_end h_t => ResumeFrames.bottom sp_end (h_seq sp_end h_t))
      sp_v h_entry sp_e h_tail).close

-- ⑦ **…and the dedenting `-` spends it**, closing the level it stood in with an
-- empty tail and consing its own entry onto the collection underneath — item
-- 167's `seqEntryTail_cons`, reached at last by the family the corpus has.
example {sp_start sp_scan sp_mid sp_sc sp_scan' : SurfPos} {ke kk : Nat}
    (h_park : ∀ sp_m, SSLComments sp_scan sp_m →
      ∀ sp_e, SCompactMapTail kk sp_m sp_e → SeqEntryTail sp_start ke sp_e)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_ind : SIndent ke sp_mid sp_sc) (h_dash : GLit '-' sp_sc sp_scan')
    (h_gnot : GNot SNsChar sp_scan') :
    ∀ sp_final, SBlockIndented ke .blockIn sp_scan' sp_final →
      ∀ sp_end, SCompactSeqTail ke sp_final sp_end → SLYamlStream sp_start sp_end :=
  seqEntryTail_cons
    (h_park sp_mid h_ssl sp_mid (SCompactMapTail.nil kk sp_mid)) h_ind h_dash h_gnot

/-- **The whole of `- a: X⏎  b: Y⏎- c`**, composed from the faces the parks
    carry and nothing else.  The fields are optional (`∨ True`) at every hop, so
    a green build does not witness the wiring — this term does: it is the route
    the cascade builds, written out, with the sibling landing in the middle where
    the corpus puts it. -/
example {sp_start sp_scan sp_key sp_ws sp_val sp_park sp_land sp_key2 sp_ws2 sp_val2
         sp_park2 sp_mid sp_sc sp_scan' : SurfPos} {n w : Nat}
    -- the park the first `-` opened — `pendingBlock n`'s own entry closure
    (h_close_entry : ∀ sp, SBlockIndented n .blockIn sp_scan sp →
      ∀ sp_end, SCompactSeqTail n sp sp_end → SLYamlStream sp_start sp_end)
    -- `a: X` on the indicator's own line
    (h_ind : SIndent w sp_scan sp_key)
    (h_ik : SImplicitKey sp_key sp_ws) (h_lit : GLit ':' sp_ws sp_val)
    (h_node : ∀ sp_m, SSLComments sp_park sp_m → SBlockNode (n+1+w+1) .blockIn sp_val sp_m)
    -- `b: Y` — the SIBLING landing inside the same `[187]`
    (h_ssl : SSLComments sp_park sp_land)
    (h_ind2 : SIndent (n+1+w) sp_land sp_key2)
    (h_ik2 : SImplicitKey sp_key2 sp_ws2) (h_lit2 : GLit ':' sp_ws2 sp_val2)
    (h_node2 : ∀ sp_m, SSLComments sp_park2 sp_m → SBlockNode (n+1+w+1) .blockIn sp_val2 sp_m)
    -- `- c` — the dedent, back at the collection's own width
    (h_ssl2 : SSLComments sp_park2 sp_mid)
    (h_ind3 : SIndent n sp_mid sp_sc) (h_dash : GLit '-' sp_sc sp_scan')
    (h_gnot : GNot SNsChar sp_scan') :
    ∀ sp_final, SBlockIndented n .blockIn sp_scan' sp_final →
      ∀ sp_end, SCompactSeqTail n sp_final sp_end → SLYamlStream sp_start sp_end := by
  have f1 : ∀ sp, SBlockIndented n .blockIn sp_scan sp → SeqEntryTail sp_start n sp :=
    h_close_entry
  have f2 : ∀ sp_v, SBlockMapEntry (n+1+w) sp_key sp_v →
      ∀ sp_e, SCompactMapTail (n+1+w) sp_v sp_e → SeqEntryTail sp_start n sp_e :=
    fun sp_v h_entry sp_e h_tail =>
      f1 sp_e (SBlockIndented.compactMap n .blockIn w sp_scan sp_key sp_e h_ind
        (SCompactMap.mk (n+1+w) sp_key sp_v sp_e h_entry h_tail))
  have f3 : ∀ sp_m, SBlockNode (n+1+w+1) .blockIn sp_val sp_m →
      ∀ sp_e, SCompactMapTail (n+1+w) sp_m sp_e → SeqEntryTail sp_start n sp_e :=
    fun sp_m h_nd sp_e h_tail =>
      f2 sp_m (SBlockMapEntry.implicitKeyNode (n+1+w) sp_key sp_ws sp_val sp_m h_ik h_lit
        (SBlockNode_blockIn_to_blockOut h_nd)) sp_e h_tail
  have f4 : ∀ sp_m, SSLComments sp_park sp_m →
      ∀ sp_e, SCompactMapTail (n+1+w) sp_m sp_e → SeqEntryTail sp_start n sp_e :=
    fun sp_m h_c sp_e h_tail => f3 sp_m (h_node sp_m h_c) sp_e h_tail
  have f5 : ∀ sp_v, SBlockMapEntry (n+1+w) sp_key2 sp_v →
      ∀ sp_e, SCompactMapTail (n+1+w) sp_v sp_e → SeqEntryTail sp_start n sp_e :=
    fun sp_v h_entry sp_e h_tail =>
      (resumeMapRouteF h_ind2
        (fun sp_end h_t => ResumeFrames.bottom sp_end (f4 sp_land h_ssl sp_end h_t))
        sp_v h_entry sp_e h_tail).close
  have f6 : ∀ sp_m, SSLComments sp_park2 sp_m →
      ∀ sp_e, SCompactMapTail (n+1+w) sp_m sp_e → SeqEntryTail sp_start n sp_e :=
    fun sp_m h_c sp_e h_tail =>
      f5 sp_m (SBlockMapEntry.implicitKeyNode (n+1+w) sp_key2 sp_ws2 sp_val2 sp_m h_ik2 h_lit2
        (SBlockNode_blockIn_to_blockOut (h_node2 sp_m h_c))) sp_e h_tail
  exact seqEntryTail_cons
    (f6 sp_mid h_ssl2 sp_mid (SCompactMapTail.nil (n+1+w) sp_mid)) h_ind3 h_dash h_gnot

/-! ## §4  What is paid, and what is not

The face rides `ImplicitKeyPack` (a fourth twin beside items 93, 99 and 108),
`pendingMapValue.h_seqF`, `pendingContent.h_seqF` and `ResumeKeyCtx`, and is
spent at `accum_block_on_pendingContent` — which hands it to item 167's
`h_entryTail`, where the two readings of the landed `-` are still chosen once.

Producers.  `entryKeyPack_of_dispatch`'s COMPACT branch pays from the caller's
entry closure (hop ②); its landed branches punt, because their key belongs to a
mapping nested in the awaited node rather than to one that fills the entry.
`content_dispatch_routed`'s RESUMING context pays (hop ⑤); its suffix, head,
marker and root contexts punt, and each of those opens a document that no
sequence entry encloses.  `accum_content_on_pendingMapValue_indented` pays all
three of its content parks; the ROOT arm has no such parameter at all — a
`pendingMapValue` at index 0 is the root mapping's value.

What is punted, in the corpus's own numbers: the **8** landings that stand on two
open mapping levels (§1's fourth shape), which want
`ResumeFrames (SeqEntryTail sp_start ke)` in place of one width (item 169 built
it — `SeqTailResumeFrames.lean` carries them, plus the alone-headed entry this
file's compact hop ② never reached); and — from item 167 — the
sequence-crossing dedent the corpus does not contain at all.

The `[210]` flip still reports FIVE errors at the same five lemma definitions:
this item narrows a route's DOMAIN, as item 167 did, and removes no construction
site.  The census beside `DanglingParkFace` §3 changes in its last column only: -/

/-! | site | form | what is left of its domain |
|---|---|---|
| `accum_content_pending` ×2 (the content landing) | `bareNodeRoute_or_refused_content` | parks with no completed tail (item 165) |
| `accum_block_on_closeThenBlock` (the block landing) | `bareNodeRoute_or_refused` | the open sequence's next entry where no park names it, and parks with no completed tail (item 168) |
| `content_dispatch_after_close` (row 19's 1c) | `bareNodeRoute` | a ROUTE, not a refutation (item 156) | -/

end L4YAML.Tests.Guards.CompactMapSeqTail

end Blanket
