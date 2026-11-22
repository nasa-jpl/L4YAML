module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The dangling park, derived at the producer (DOCS item 156)

Item 141 built the CONSUMER half of §9.2's dangling refusal —
`danglingNode_refutes_landing` and `danglingNode_refutes_eof`, in
`StreamDanglingParkRevocable` — and left the producer half unnamed: nothing in
the library said what a content dispatch's park READS.  This file is that half,
landed in `StreamAccum` and exercised here.

The chain is the token array's own, and every link is now a lemma:

* `dispatchContent_tokens_push` — off `&` and `!`, every content arm pushes
  exactly ONE node body, and pushes it at the dispatch's own `currentPos`
  (the block scalar included, through `scanBlockScalar_tokens_push`);
* `trailingNodeRun?_push_body` — a body pushed on top starts a trailing run of
  one, with the array's own last REAL slot as its predecessor
  (`prevRealIdx?_push`, `prevRealIdx?_lt`);
* `CompletedTail.danglingPred` — a completed node tail offers the next run no
  slot, because `completesFlowValue` and `offersNodeSlot` are disjoint;
* `danglingPark_of_dispatch` — so the park reads `some ⟨line, col⟩` at the
  landing's own column, whenever that column names an open level;
* `danglingPark_refutes_landing` / `danglingPark_refutes_eof` — spent against
  the two §9.2 checks.

§1 reads the chain's premises and its conclusion off the real scanner, over the
family item 141 named.  §2 is the correction this item makes to item 144's
attribution, at its type and over its own three witnesses.  §3 is the
correction to item 141's corpus.  §4 is the face, re-priced.  §5 is the wall,
re-confirmed with its witness. -/

namespace L4YAML.Tests.Guards.DanglingParkDerived

open L4YAML L4YAML.Scanner L4YAML.Proofs.StreamAccum

private def posStr : Option YamlPos → String
  | some p => s!"{p.line},{p.col}"
  | none => "none"

private def stepN (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | n + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepN s' n
    | _ => none

/-- `danglingPark_of_dispatch`'s two readable premises and its conclusion, taken
    at the landing state `n` steps in: the dispatch's own column, whether that
    column names an open level (`h_op`), whether the array's last REAL token
    offers the coming run a slot (`CompletedTail.danglingPred`'s half), and the
    reading the park then has. -/
private def chainAt (input : String) (n : Nat) : String :=
  match stepN ((ScannerState.mk' input).emit .streamStart) n with
  | none => "no-state"
  | some s =>
    match scanNextToken_preprocess s with
    | .ok (some (s1, _)) =>
      let op := s1.indents.any (fun e => e.column == (s1.col : Int))
      let pred := match prevRealIdx? s1.tokens s1.tokens.size with
        | some j => if s1.tokens[j]!.val.offersNodeSlot then "slot" else "no-slot"
        | none => "no-pred"
      match scanNextToken s with
      | .ok (some s2) => s!"col={s1.col} op={op} pred={pred} park={posStr (danglingNodePos? s2)}"
      | _ => s!"col={s1.col} op={op} pred={pred} park=no-step"
    | _ => "no-landing"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

/-! ## §1  The chain, read off the real scanner

Item 141's six-member family, at the landing that MAKES the park.  Every member
reads the lemma's premises — an open level at the dispatch's column, a last real
token that offers no slot — and every one gets the lemma's conclusion: `some` at
that same column.  The last two are this file's own additions, a sequence entry
and a plain value, so the family is not one shape. -/

#guard [("a: 1\nb", 3), ("a: 1\nb\nc: 2\n", 3), ("k:\n  a: 1\n  b\nc: 2\n", 5),
        ("a: &x 1\n*x : 2\n", 4), ("- a\nb", 2), ("k:\n  a\nb", 3)].map
    (fun (p : String × Nat) => chainAt p.1 p.2)
  == ["col=0 op=true pred=no-slot park=1,0",
      "col=0 op=true pred=no-slot park=1,0",
      "col=2 op=true pred=no-slot park=2,2",
      "col=0 op=true pred=no-slot park=1,0",
      "col=0 op=true pred=no-slot park=1,0",
      "col=0 op=true pred=no-slot park=2,0"]

-- …and the three whose landing the refusal actually reaches are refused there,
-- at exactly the column the lemma names.
#guard ["a: 1\nb\nc: 2\n", "k:\n  a: 1\n  b\nc: 2\n", "a: 1\nb"].map parseOk
  == ["PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 2 2",
      "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 0"]

/-! ## §2  What the face does NOT reach — item 144's attribution, corrected

Item 144 measured that `content_dispatch_after_close` cannot pay §9.2's landing
guard and recorded the residue as "row 19's 1c residue for the indented family —
**item 141's park face**".  The first half is right and the attribution is not:
the face reads `none` at all three of that lemma's callers, so it can never
refute them, and the three inputs are VALID.

The reason is structural, not a measurement, and it holds at the type — with
item 177's floor it is the COLUMN's, not the slot's: the three callers park at
landings indented strictly past every open level (the witness rows below read
`op=false`), and a run whose column names no open level reads `none` on either
side of the exemption.  The slot's own exemption survives only for the one run
shape another reading refuses (the props-less flow-close tail, item 172's
floor — item 178 folded the `[96]`-headed run into the check's own refusal),
because the offered slot cannot reach the level's own column —
`s-separate(n+1)`, Finding A's floor. -/

example (s : ScannerState) (h_noflow : s.inFlow = false) {st : Nat}
    {pred : Option Nat}
    (h_run : trailingNodeRun? s.tokens = some (st, pred))
    (h_col : (s.indents.any fun e =>
      e.column == ((s.tokens[st]!.pos).col : Int)) = false)
    -- Item 180: the column reading is no longer the whole verdict — the
    -- crossed-block clause reads the trailing block at ANY column, so its
    -- own `none` rides as a premise here.  Item 182: so does the
    -- break-crossing clause, which reads a column the RUN's start is not at.
    (hx : crossedPropsExcessPos? s.tokens = none)
    (hlc : runLineCrossDanglingPos? s.tokens s.indents = none) :
    danglingNodePos? s = none := by
  unfold danglingNodePos?
  rw [h_noflow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_run]
  simp only [h_col, Bool.false_eq_true, ↓reduceIte, ite_self, hx, hlc]

-- …and the exemption's surviving half, at the type: an offered run whose
-- start is neither a node body nor a property (item 178) — the props-less
-- flow-close tail, whose refusals are item 172's floor and whose sibling-key
-- readings never present a break-ended run.
example (s : ScannerState) (h_noflow : s.inFlow = false) {st j : Nat}
    (h_run : trailingNodeRun? s.tokens = some (st, some j))
    (h_slot : s.tokens[j]!.val.offersNodeSlot = true)
    (h_body : s.tokens[st]!.val.isNodeBody = false)
    (h_prop : s.tokens[st]!.val.isNodeProperty = false) :
    danglingNodePos? s = none := by
  unfold danglingNodePos?
  rw [h_noflow]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_run]
  simp [h_slot, h_body, h_prop]

-- The three witnesses, at their landings.  Two fail BOTH of the lemma's
-- premises (the landing is indented past every open level, and the last real
-- token is the `-`/`:` whose slot the content fills); the third stands at the
-- sentinel-only stack, which is item 144's own note.
#guard [("k:\n  -\n    b\n", 3), ("k:\n  a:\n    b\n", 4), ("&p\n  b\n", 1)].map
    (fun (p : String × Nat) => chainAt p.1 p.2)
  == ["col=4 op=false pred=slot park=none",
      "col=4 op=false pred=slot park=none",
      "col=2 op=false pred=no-slot park=none"]

-- …and all three PARSE.  There is nothing here for a refutation to do; what
-- these want is the enclosing park's own route.
#guard ["k:\n  -\n    b\n", "k:\n  a:\n    b\n", "&p\n  b\n"].map parseOk
  == ["PARSE-OK", "PARSE-OK", "PARSE-OK"]

/-! ## §3  Item 141's corpus, corrected

Item 141's census walked "the 490 `.yaml` files in `yaml-test-suite/src` and
`examples/`" and recorded **2275** observations: 2 `R`, 0 `E`, 2273 `D`.  Item
145 re-ran it and recorded every cell unchanged.  Both readings are over the
wrong files on the suite side: `yaml-test-suite/src/*.yaml` are test
DESCRIPTORS, each a root sequence of mappings — the correction item 155 made to
item 154's own census, made again here.

Re-walked with the same instrument, the 490 files read as:

| corpus | obs | `R` | `E` | `D` |
|---|---|---|---|---|
| the 490 files, walked as payloads (item 141's reading) | 2275 | 2 | 0 | 2273 |
| the suite's 406 extracted payloads | 183 | 6 | 6 | 171 |
| `examples/`, which are payloads already | 163 | 2 | 0 | 161 |

So the honest corpus is **346** observations, **14** of them discharge-able (8
`R` + 6 `E`) and **332** carried — 4.0 %, not item 141's 0.09 %.  The
descriptor sweep manufactured about 1 930 of its observations out of its own
nested mappings, and it hid all six of the `E`s, because a descriptor file never
ends on a dangling run.

**The structural conclusion is unchanged**, and it never rested on the census:
what decides the face's shape is §2's revocability measurement, which is over
hand-built inputs.  What the census decides is how HOT the carried disjunct is,
and at 96 % it is still the language rather than a corner of it. -/

/-! ## §4  The face, re-priced

Stated as a PREMISE rather than as item 141's conclusion-disjunct —
`h_closable : danglingNodePos? sc = none → ∀ sp_mid, …`, with
`PendingNode.close_with_ssl` taking the same premise — the face is **32**
distinct sites in **9** holders at the tree this item stands on:

| holder | sites |
|---|---|
| `accum_content_pending` | 11 |
| `accum_content_on_pendingMapValue_indented` | 6 |
| `accum_content_on_pendingMapValue` | 5 |
| `content_dispatch_routed` | 4 |
| `accum_step_flow` | 2 |
| `eof_pending`, `accum_structural_pending`, `accum_flow_open_depth0`, `accum_block_pending` | 1 each |

Item 141 priced the conclusion-disjunct shape at 19 → 28 → 32 over three waves
(14 producers, 5 consumers).  The producer count is the same 14; the five
consumers are the same five, one site each, and they are the last four rows
above plus `accum_content_pending`'s own.  The premise shape reaches 32 in one
wave because it never widens a conclusion — which is why it is the shape this
file records.  (The counts are the tree item 160 measured; item 179 deleted
`accum_content_on_pendingMapValue` and `accum_content_on_pendingBlock` — the
root instances of their indented twins — so those rows' faces are the twins'
arms now.) -/

/-! ## §5  The wall, re-confirmed

Four of the five consumers stand where §9.2 gives a refutation: `eof_pending`
at `scanLoop_checkDanglingNode`, which is gated on nothing, and the three
landing consumers at `scanNextToken_checkDanglingNode`, gated on the break the
landing crossed.  `accum_block_pending` does not: its `h_close_pending` is built
BEFORE the case split, and its live arm is a `:` on the park's own line, where
the flag is DOWN and the check stands aside by construction.

Item 141's punting witness is still the one that makes this real rather than
structural — an ALIAS key, which `pendingContent.h_key` does not pack, so the
`:` reaches `accum_block_on_closeThenBlock`'s fallback with a dangling park in
hand.  It scans clean and it parses. -/

#guard scanOk "a: &x 1\n*x : 2\n" == "SCAN-OK"
#guard parseOk "a: &x 1\n*x : 2\n" == "PARSE-OK"
#guard chainAt "a: &x 1\n*x : 2\n" 4 == "col=0 op=true pred=no-slot park=1,0"

-- The gating, at its type, restated here because it is what §5 turns on: with
-- the flag DOWN the mid-stream check succeeds on a state whose reading is
-- `some`, so `danglingPark_refutes_landing` has no premise to be given.
example (s_run s_land : ScannerState) (h : s_land.simpleKeyAllowed = false) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  unfold scanNextToken_checkDanglingNode
  rw [ite_eq_right (by simp [h])]

end L4YAML.Tests.Guards.DanglingParkDerived

end Blanket
