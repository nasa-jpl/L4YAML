module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The sequence lane's dedent, and the tail it lands in (DOCS item 167)

Item 166 measured `bareNodeRoute_or_refused`'s surviving branch at the block
landing and found it is not refutable: behind a completed node a landed `-`
stands on a `[183] l+block-sequence` that is already open at its own column, so
the bare-document reading is an over-approximation on the WHOLE of that domain
and what the arm lacks is a ROUTE.  This file is that route's measurement.

**The family splits in two, and the corpus only contains one half.**  Over 490
files the scanner dispatches 530 block entries; 76 of them land after an unwind
that drops at least one level, and in every one of those 76 the dropped levels
are block MAPPINGS.  Not one `-` in the corpus dedents out of an open block
SEQUENCE.  So the landing that needs a sequence frame is legal and accepted and
absent from every one of the 490 files the census walks (`yaml-test-suite/src`,
`examples`, `Tests`) — §1 has to write it out to show it at all.

`SeqEntryTail` names what the park owes the collection it stands inside, and
`seqEntryTail_cons` spends it: the landing's own entry conses onto that tail
instead of opening a second bare document.  §1 measures the family at the
runtime, §2 the corpus, §3 states the two declarations at their types, §4
records what is paid and what is not. -/

namespace L4YAML.Tests.Guards.SeqDedentEntryTail

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

private def stk (a : Array IndentEntry) : String :=
  String.intercalate "," (a.toList.map (fun e =>
    s!"{e.column}{if e.isSequence then "S" else "M"}"))

/-- The landing `n` steps in, read as the DEDENT arms read it: the park's own
    indent stack, the landing's column, and the levels preprocessing's unwind
    drops between the two.  A dropped `S` is a sequence level the landing can
    only close — the case with no frame to resume. -/
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

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

/-- The parser's own reading of the same input, which is the statement the
    route has to match: one document, the landing an ENTRY of the collection
    it dedented back into. -/
private def ev (input : String) : String :=
  match Events.streamToEvents input with
  | .ok es => String.intercalate " " ((es.splitOn "\n").filter (· ≠ ""))
  | .error e => s!"ERR {repr e}"

/-! ## §1  The sequence dedent, measured

Three shapes, each dropping an open `[183]` on the way down.  All three scan,
all three parse, and all three emit ONE document whose outer sequence takes the
landing as its next entry. -/

#guard scanOk "- - a\n- b\n" == "SCAN-OK"
#guard dropAt "- - a\n- b\n" 3 == "c=- k=0 park=[-1M,0S,2S] drop=[2S]"
#guard ev "- - a\n- b\n"
  == "+STR +DOC +SEQ +SEQ =VAL :a -SEQ =VAL :b -SEQ -DOC -STR"

#guard scanOk "-\n  -\n- b\n" == "SCAN-OK"
#guard dropAt "-\n  -\n- b\n" 2 == "c=- k=0 park=[-1M,0S,2S] drop=[2S]"
#guard ev "-\n  -\n- b\n"
  == "+STR +DOC +SEQ +SEQ =VAL : -SEQ =VAL :b -SEQ -DOC -STR"

#guard scanOk "- - - a\n- b\n" == "SCAN-OK"
#guard dropAt "- - - a\n- b\n" 4 == "c=- k=0 park=[-1M,0S,2S,4S] drop=[2S,4S]"
#guard ev "- - - a\n- b\n"
  == "+STR +DOC +SEQ +SEQ +SEQ =VAL :a -SEQ -SEQ =VAL :b -SEQ -DOC -STR"

-- The MAPPING dedent beside it — the shape the corpus does have.  Its dropped
-- levels are `M`, and a mapping level can only close, so the route it needs is
-- the same tail read at the same width.
#guard scanOk "- a:\n    b: 1\n- c\n" == "SCAN-OK"
#guard dropAt "- a:\n    b: 1\n- c\n" 6
  == "c=- k=0 park=[-1M,0S,2M,4M] drop=[2M,4M]"

-- …and one with both kinds in the drop, which is why the two halves are one
-- family and not two.
#guard scanOk "- k:\n    - a\n- b\n" == "SCAN-OK"
#guard dropAt "- k:\n    - a\n- b\n" 5
  == "c=- k=0 park=[-1M,0S,2M,4S] drop=[2M,4S]"

-- The SIBLING at the park's own width drops nothing: that is the landing
-- `pendingBlockContent`'s `k = n` arm has served since item 22, and it is what
-- makes the dedent the residue rather than the rule.
#guard dropAt "- - a\n  - b\n" 3 == "c=- k=2 park=[-1M,0S,2S] drop=[]"

/-! ## §2  The corpus

`Scratch/CensusSeqDedent.lean` (gitignored) walks `yaml-test-suite/src`,
`examples` and `Tests`, counting every `-` whose block-entry dispatch succeeds
and splitting it by what the unwind dropped:

    files=490 filesWithSeqDedent=0
    dash=530  dashDrop=76  dropSeq=0  dropMapOnly=76  dropSeqTail=0

and `Scratch/CensusSeqResumeTwin2.lean` (gitignored too) reads item 166's own
134 surviving-branch landings on the PARK's state rather than the post-unwind
one:

    hits=134  pop0=58  pop1=68  pop2p=8  popSq=0  popMap=76
    topSeqEqK=40  topMapEqK=18  topGtK=76  topLtK=0

Read together: 58 of the 134 land at the park's own top level (the sibling), 76
land strictly below it, and all 76 of those cross mapping levels alone.  The
`dropSeq=0` column is the finding: a dedenting `-` that crosses an open
SEQUENCE is legal — §1's first three rows — and no file among the 490 contains
one, which is why the payment below serves a family the corpus does not
contain. -/

/-! ## §3  The route

`SeqEntryTail sp_start ke sp_e` is the enclosing `[183]`'s remaining tail, still
owed at `sp_e`; it is the SEQUENCE lane's `ExplValueLine`.  Every fused closure
a park carries ends at the stream, which is that tail closed at `nil` — the fold
that makes a dedenting `-` a second bare document. -/

example {sp_start sp_e : SurfPos} {ke : Nat} (h : SeqEntryTail sp_start ke sp_e) :
    ∀ sp_end, SCompactSeqTail ke sp_e sp_end → SLYamlStream sp_start sp_end := h

-- Closing it at `nil` recovers the stream the closures already end at, which is
-- what says the field is a REFINEMENT of the close rather than a new promise.
example {sp_start sp_e : SurfPos} {ke : Nat} (h : SeqEntryTail sp_start ke sp_e) :
    SLYamlStream sp_start sp_e := h sp_e (SCompactSeqTail.nil ke sp_e)

-- …and the landing spends it by consing its own entry, at the width the tail
-- names.  This is the step `accum_block_on_closeThenBlock`'s `-` arm takes when
-- the park carries a collection at the landing's column.
example {sp_start sp_mid sp_sc sp_scan' : SurfPos} {k : Nat}
    (h_route : SeqEntryTail sp_start k sp_mid)
    (h_ind : SIndent k sp_mid sp_sc) (h_dash : GLit '-' sp_sc sp_scan')
    (h_gnot : GNot SNsChar sp_scan') :
    ∀ sp_final, SBlockIndented k .blockIn sp_scan' sp_final →
      ∀ sp_end, SCompactSeqTail k sp_final sp_end → SLYamlStream sp_start sp_end :=
  seqEntryTail_cons h_route h_ind h_dash h_gnot

-- …and the payer's own term, composed end to end.  The NESTED `-` hands the
-- inner park the OUTER park's `h_close_entry` read without spending its tail;
-- given the outer entry's node that IS a `SeqEntryTail` at the outer width, and
-- a landing back at that width conses onto it.  Nothing else is needed to close
-- `- - a⏎- b`'s landing through the collection it stands in.
example {sp_start sp_scan sp_mid sp_sc sp_scan' : SurfPos} {n : Nat}
    (h_close_entry : ∀ sp, SBlockIndented n .blockIn sp_scan sp →
      ∀ sp_end, SCompactSeqTail n sp sp_end → SLYamlStream sp_start sp_end)
    (h_node : SBlockIndented n .blockIn sp_scan sp_mid)
    (h_ind : SIndent n sp_mid sp_sc) (h_dash : GLit '-' sp_sc sp_scan')
    (h_gnot : GNot SNsChar sp_scan') :
    ∀ sp_final, SBlockIndented n .blockIn sp_scan' sp_final →
      ∀ sp_end, SCompactSeqTail n sp_final sp_end → SLYamlStream sp_start sp_end :=
  seqEntryTail_cons (h_close_entry sp_mid h_node) h_ind h_dash h_gnot

/-! ## §4  What is paid, and what is not

The field rides two parks — `pendingBlock.h_seqF` and
`pendingBlockContent.h_seqF` — and is spent at the two arms whose own comments
name the gap: `accum_block_on_pendingBlock`'s DEDENT arm ("resuming the
collection the dedent lands back in needs a FRAME the pending does not carry")
and `accum_block_on_pendingBlockContent`'s `k ≠ n` arm ("a dedent has no frame
to resume").  One producer pays: the NESTED `-`, where the outer park's own
`h_close_entry` read WITHOUT spending its tail is the enclosing collection
verbatim.

So what item 167 routes is the half of item 166's residue that crosses a
sequence level — §1's first three shapes — and `dropSeq=0` says the corpus
exhibits none of it.  The half the corpus DOES exhibit, all 76 of it, parks
inside a block mapping that fills the entry (`- a:⏎␣␣␣␣b: 1⏎- c`), and reaching
it means carrying the same field across the compact-mapping cascade —
`ImplicitKeyPack`, `pendingMapValue`, `pendingContent`.  **Item 168 carries it**
(`Tests/Guards/Proofs/CompactMapSeqTail.lean`), and reaches 68 of the 76: the
cascade is one width wide here too, so the 8 landings that stand on TWO open
mapping levels stay with `ResumeFrames` on this lane.

One width is carried, not a stack: `- - - a⏎- b` names its INNERMOST enclosing
collection, so a landing two levels out punts to the document reading.  A stack
would be `ResumeFrames` with `SCompactSeqTail` in place of `SCompactMapTail`;
nothing in the corpus asks for it, and §1's third row is the only shape that
would.

The `[210]` flip still reports FIVE errors at the same five lemma definitions:
this item narrows the route's DOMAIN at one of the five, it does not remove a
construction site.  The census beside `DanglingParkFace` §3 changes in its last
column only: -/

/-! | site | form | what is left of its domain |
|---|---|---|
| `accum_content_pending` ×2 (the content landing) | `bareNodeRoute_or_refused_content` | parks with no completed tail (item 165) |
| `accum_block_on_closeThenBlock` (the block landing) | `bareNodeRoute_or_refused` | the open sequence's next entry where no park names it (item 167), and parks with no completed tail |
| `content_dispatch_after_close` (row 19's 1c) | `bareNodeRoute` | a ROUTE, not a refutation (item 156) | -/

end L4YAML.Tests.Guards.SeqDedentEntryTail

end Blanket
