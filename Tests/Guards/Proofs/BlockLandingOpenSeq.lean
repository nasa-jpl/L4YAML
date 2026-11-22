module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The block landing's surviving branch (DOCS item 166)

Item 139 halved `bareNodeRoute`'s domain at the block landing: at a landing that
stands at NO open level a completed node is a second bare document and
`scanNextToken_checkBareDocument` fires AT the landing, so that half is refuted
outright.  The other half — resting ON an open level — stood whole, and items
158, 160, 161, 162, 163, 164 and 165 each forecast it the same way: "its `-`
family the scanner already refuses, its `:`/`?` family is LEGAL and routes
through the key cascade, so what is left is a CONSUMER to narrow."

**The `-` half of that forecast is wrong, and this file measures it.**  The
scanner refuses `a: 1⏎- x` and `k:⏎␣␣a: 1⏎␣␣- x`, but not because the landing
rests on an open level — `scanBlockEntryValidate` refuses a `-` at a block
MAPPING's own indent with no node slot awaited *and no same-indent sequence
open*.  Lift the last conjunct and the same shape is legal:

    - a:              - - a            a:
        b: 1          - b              - x
    - c                                - y

all three scan clean, parse clean, reach this branch behind a completed node,
and are the next entry of a `[183]` that is already open at the landing's own
column.  So the branch serves legal input, and what row 1c needs here is the
open collection's own continuation — a ROUTE — not another guard.

§1 measures the family at the runtime; §2 states the three readings the
refusal conjoins and the two lemmas that invert it; §3 spends them as
`blockEntry_landing_openSeq`; §4 records what the residue needs and why no park
carries it. -/

namespace L4YAML.Tests.Guards.BlockLandingOpenSeq

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

private def both (input : String) : String × String := (scanOk input, parseOk input)

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

/-- The landing `n` steps in, read as `bareNodeRoute_or_refused` reads it:
    the character, item 139's discriminator `h_op`, the park's completed tail,
    and the three conjuncts `scanBlockEntryValidate` decides on. -/
private def dashAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match scanNextToken_preprocess s with
    | .ok (some (s1, c)) =>
      let sd := if s1.allowDirectives then
          { s1 with allowDirectives := false, documentEverStarted := true }
        else s1
      let tail := match lastRealTokenVal? s.tokens with
        | some t => toString t.completesFlowValue
        | none => "noTok"
      s!"c={c} op={s1.indents.any (fun e => e.column == (s1.col : Int))} " ++
        s!"tail={tail} " ++
        s!"atMap={atMappingIndent sd} slot={nodeSlotAwaited sd.tokens} " ++
        s!"seq={sameIndentSequenceOpen sd.tokens (sd.col : Int)} disp=" ++
        (match scanNextToken_dispatchBlockIndicators sd c with
         | .ok (some _) => "ok"
         | .ok none => "none"
         | .error e => s!"ERR {repr e}")
    | .ok none => "EOF"
    | _ => "no-landing"

/-! ## §1  The family, measured

The two shapes every forecast since item 158 quoted, with the reading that
actually refuses them.  `op=true` in both: the landing DOES rest on an open
level, and that is not what decides the step. -/

#guard both "a: 1\n- x\n"
  == ("SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard dashAt "a: 1\n- x\n" 3
  == "c=- op=true tail=true atMap=true slot=false seq=false disp=ERR L4YAML.ScanError.invalidBareDocument 1 0"

#guard both "k:\n  a: 1\n  - x\n"
  == ("SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 2",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 2 2")
#guard dashAt "k:\n  a: 1\n  - x\n" 5
  == "c=- op=true tail=true atMap=true slot=false seq=false disp=ERR L4YAML.ScanError.invalidBareDocument 2 2"

-- Lift the third conjunct — a zero-indented sequence IS open at the mapping's
-- own column — and the identical landing is legal.  `atMap=true seq=true`:
#guard both "a:\n- x\n- y\n" == ("SCAN-OK", "PARSE-OK")
#guard dashAt "a:\n- x\n- y\n" 4
  == "c=- op=true tail=true atMap=true slot=false seq=true disp=ok"
#guard both "k:\n  a:\n  - x\n  - y\n" == ("SCAN-OK", "PARSE-OK")
#guard dashAt "k:\n  a:\n  - x\n  - y\n" 6
  == "c=- op=true tail=true atMap=true slot=false seq=true disp=ok"

-- …and the other disjunct, where the open sequence is the STACK's own and no
-- mapping stands at the column — the first off a mapping value nested inside
-- the entry, the second off a DEDENT out of a nested sequence.
#guard both "- a:\n    b: 1\n- c\n" == ("SCAN-OK", "PARSE-OK")
#guard dashAt "- a:\n    b: 1\n- c\n" 6
  == "c=- op=true tail=true atMap=false slot=false seq=true disp=ok"
#guard both "- - a\n- b\n" == ("SCAN-OK", "PARSE-OK")
#guard dashAt "- - a\n- b\n" 3
  == "c=- op=true tail=true atMap=false slot=false seq=true disp=ok"

-- The slot-awaiting landing is the third reading, and it is the one with no
-- completed tail — `h_tail139` punts there and item 139's refutation never
-- applied to it anyway (`a:⏎- x`, the FIRST entry).
#guard dashAt "a:\n- x\n- y\n" 2
  == "c=- op=true tail=false atMap=true slot=true seq=false disp=ok"

/-! ## §2  The refusal, inverted

`scanBlockEntryValidate` conjoins three readings, and only one of them is about
the indent stack.  §8.2.1's `m` is allowed to be 0, so a sequence at its parent
mapping's own column is never pushed and is visible in the TOKEN ARRAY alone —
which is why `sameIndentSequenceOpen` is a backward walk and not a stack test. -/

example {s : ScannerState} (h_noflow : s.inFlow = false)
    (h_map : atMappingIndent s = true) (h_slot : nodeSlotAwaited s.tokens = false)
    (h_seq : sameIndentSequenceOpen s.tokens (s.col : Int) = false) :
    ∃ e, scanBlockEntry s = .error e :=
  scanBlockEntry_error_of_bad h_noflow h_map h_slot h_seq

example {s s' : ScannerState}
    (h : scanNextToken_dispatchBlockIndicators s '-' = .ok (some s'))
    (h_noflow : s.inFlow = false) (h_slot : nodeSlotAwaited s.tokens = false)
    (h_map : atMappingIndent s = true) :
    sameIndentSequenceOpen s.tokens (s.col : Int) = true :=
  dispatchBlockEntry_sameIndentSeq h h_noflow h_slot h_map

-- The park's own tail pays the slot reading: `completesFlowValue` excludes both
-- the property `slotHolderIdx?` would step over and the slot it would offer,
-- and `preprocess_danglingPred` carries that across the landing.
example {sc s_prep : ScannerState} {c : Char} (h_tail : CompletedTail sc)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    nodeSlotAwaited (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep).tokens = false :=
  nodeSlotAwaited_false_of_landing h_tail h_pre

/-! ## §3  The branch, named

Put together: at a landed `-` off a park whose tail is a completed node, the
dispatch's own success says a `[183]` is open at this column.  The route
`bareNodeRoute_or_refused` hands that landing — a second bare document — is an
over-approximation on the WHOLE of its surviving domain, not on part of it. -/

example {sc s_prep s' : ScannerState} {c : Char}
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_tail : CompletedTail sc) (h_noflow : s_prep.inFlow = false)
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) '-' = .ok (some s')) :
    OpenSeqEntry (if s_prep.allowDirectives then
      { s_prep with allowDirectives := false, documentEverStarted := true }
    else s_prep) :=
  blockEntry_landing_openSeq h_pre h_tail h_noflow h_dispatch

-- …and the two disjuncts are the two places a `[183]` can be open, read off the
-- states §1 measured.  Neither is refutable, because neither input is refused.
example {s : ScannerState} (h : atMappingIndent s = false) : OpenSeqEntry s := Or.inl h
example {s : ScannerState} (h : sameIndentSequenceOpen s.tokens (s.col : Int) = true) :
    OpenSeqEntry s := Or.inr h

/-! ## §4  What the residue needs

The route the landing wants is the open collection's own continuation, at the
landing's width:

    ∀ sp_e, SBlockSeqEntries k sp_mid sp_e → SLYamlStream sp_start sp_e

and no park carries one at the width this landing lands at.
`pendingBlockContent.h_closable_entry` is exactly that shape at the park's OWN
width `n`, and `accum_block_on_pendingBlockContent` spends it for the sibling `-`
under its own `by_cases hkn : k = n` — so what is left for this branch is that
lemma's `k ≠ n` arm and the `pendingContent` park, which has no entry-level route
of any width.

Item 155 built the resume face for the levels below a landing — `ResumeFrames`
— and it records MAPPING levels by construction: the `-` opens a sequence
level, so the cover crosses the step untouched and the list is the mapping
widths alone.  The sequence's twin is the item behind this one.

The `[210]` flip still reports FIVE errors at the same five lemma definitions.
The census beside `DanglingParkFace` §3 changes in its last column only: -/

/-! | site | form | what is left of its domain |
|---|---|---|
| `accum_content_pending` ×2 (the content landing) | `bareNodeRoute_or_refused_content` | parks with no completed tail (item 165) |
| `accum_block_on_closeThenBlock` (the block landing) | `bareNodeRoute_or_refused` | the open sequence's next entry, and parks with no completed tail (item 166) |
| `content_dispatch_after_close` (row 19's 1c) | `bareNodeRoute` | a ROUTE, not a refutation (item 156) | -/

end L4YAML.Tests.Guards.BlockLandingOpenSeq

end Blanket
