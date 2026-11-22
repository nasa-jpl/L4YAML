module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Proofs.Production.ScalarFoldAt

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The PLAIN walk's blank fold line is measured against the floor (DOCS item 100)

Item 62 gated the quoted fold (`ScannerBlankFoldTabRefused`) and left the
BLOCK plain walk as "a different production, untouched".  It is not a
different production: `[135] ns-plain-multi-line(n,c)` folds through
`[134] s-ns-plain-next-line(n,c)` → `[74] s-flow-folded(n)` →
`[73] b-l-folded(n,flow-in)`, whose empty lines are `l-empty(n,flow-in)` — the
same ones.  So the same shape has no arm here either: `[63] s-indent` is
spaces (§6.1), `[69] s-flow-line-prefix(n)` admits a tab only past the `n`th
space, and `[64] s-indent-lt(n)` takes its break immediately after its short
run.

`skipBlankLinesLoop` folded such a line anyway, which is why
`skipBlankLinesLoop_prod_at` carried `∨ True` for eleven items — and that
punt was the last feeder of `indentedValue_reads_at_any_indent`'s own
catch-all, hence of three `block_dispatch_deferred` sites.  The loop now
stops AT the offending line, exactly as `foldQuotedNewlinesLoop` does; the
caller's under-indent test ends the scalar there, and the document is
refused for want of structure rather than folded into a reading no grammar
admits.

The floor is the reading index: a continuation is read at `n = currentIndent
+ 1`, so "fewer than `n` spaces" is "at or below `currentIndent`", which is
what the gate measures.  §2 and §3 are the two ways not to be that shape —
the run clears the floor, or the run is not the scalar's at all. -/

namespace L4YAML.Tests.Guards.ScannerPlainBlankFoldTab

open L4YAML L4YAML.Scanner

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The narrowed shape: a blank line inside a folded PLAIN scalar whose white
-- run reaches a TAB before the floor.  A mapping value's floor is 1…
#guard refuses "k:\n  a\n\t\n  b\n"
-- …a sequence entry's is 1 as well…
#guard refuses "- a\n\t\n  b\n"
-- …a nested entry's is 3…
#guard refuses "k:\n  - a\n\t\n    b\n"
-- …and a nested mapping's is 3, so two spaces are still one short.
#guard refuses "k:\n  m:\n    a\n\t\n    b\n"
#guard refuses "k:\n  m:\n    a\n  \t\n    b\n"
-- The offending line need not be the only blank one, nor the first fold.
#guard refuses "k:\n  a\n\t\n\t\n  b\n"
#guard refuses "k:\n  a\n\t\n  b\n \t\n  c\n"

-- §2 The boundary, which must NOT move: a run that CLEARS the floor makes the
-- tab `s-separate-in-line` inside `s-flow-line-prefix(n)`.
-- One space is the whole floor here (`n = 1`).
#guard emits "k:\n  a\n \t\n  b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a\\nb", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a\n  \t\n  b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a\\nb", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  m:\n    a\n    \t\n    b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "=VAL :a\\nb", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- A pure-space run is `s-indent-lt(n)`, empty or not.
#guard emits "k:\n  a\n\n  b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a\\nb", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a\n   \n  b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a\\nb", "-MAP", "-DOC", "-STR"]
-- At the ROOT the floor is 0, so `s-indent(0)` is already met and a tab-only
-- blank line is a legitimate `l-empty(0)`.
#guard emits "a\n\t\nb\n"
  ["+STR", "+DOC", "=VAL :a\\nb", "-DOC", "-STR"]
#guard emits "a\n \t\nb\n"
  ["+STR", "+DOC", "=VAL :a\\nb", "-DOC", "-STR"]
-- The FLOW plain fold is `foldQuotedNewlines`' own path (item 62's gate) and
-- reads at the enclosing block floor, which is `-1` here.
#guard emits "[a\n\t\nb]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :a\\nb", "-SEQ", "-DOC", "-STR"]

-- §3 The other way not to be the shape: the blank run is not the SCALAR's,
-- because the fold ends before it.  These lines are `[79] s-l-comments` at the
-- document level, where `s-separate-in-line` admits the tab.
-- Nothing follows the run…
#guard emits "k:\n  a\n\t\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "-MAP", "-DOC", "-STR"]
-- …the next content line dedents out of the scalar…
#guard emits "k:\n  a\n\t\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "=VAL :b", "=VAL :2", "-MAP",
   "-DOC", "-STR"]
-- …the continuation collects nothing (the no-gain rewind)…
#guard emits "k:\n  a\n\t\n  \n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "-MAP", "-DOC", "-STR"]
-- …it is a comment…
#guard emits "k:\n  a\n\t\n  #c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "-MAP", "-DOC", "-STR"]
-- …or the scalar ended on its own line to begin with.
#guard emits "k: v\n\t\nj: w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :v", "=VAL :j", "=VAL :w", "-MAP",
   "-DOC", "-STR"]

-- §4 The readings that lost their disjunction with the gate.  Each `example`
-- is the lemma AT ITS TYPE: no `∨ True`, no residue to defer.
open L4YAML.Surface L4YAML.Scanner L4YAML.CharPredicates L4YAML.Proofs
  L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScalarFoldAt in
/-- Every line the skipper folds is an `l-empty(n)` — the punt that stood
    here fed `indentedValue_reads_at_any_indent`'s catch-all. -/
example {n : Nat} {sc : ScannerState} {sp : SurfPos} {cnt fuel inputEnd : Nat}
    (hcorr : ScannerSurfCorr sc sp) (hcol0 : sp.col = 0)
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    ∃ sp', GStar (SLEmpty n .flowIn) sp sp' ∧
      ScannerSurfCorr (skipBlankLinesLoop sc cnt fuel inputEnd).2 sp' ∧
      sp'.col = 0 :=
  skipBlankLinesLoop_prod_at n sc sp cnt fuel inputEnd hcorr hcol0 hn

open L4YAML.Surface L4YAML.Scanner L4YAML.CharPredicates L4YAML.Proofs
  L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScalarFoldAt in
/-- …so the block fold at `n` is total. -/
example {n : Nat} {sc : ScannerState} {sp : SurfPos} {c : Char}
    {content : String} {contentIndent inputEnd : Nat}
    {content' : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true)
    (hblk : collectPlainScalar_handleBlockLineBreak sc content contentIndent inputEnd
            = some (content', s'))
    (hn : n ≤ contentIndent)
    (hnci : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    ∃ sp₁ sp₂ sp', SBBreak sp sp₁ ∧ GStar (SLEmpty n .flowIn) sp₁ sp₂ ∧
      SFlowLinePrefix n sp₂ sp' ∧ ScannerSurfCorr s' sp' :=
  handleBlockLineBreak_prod_at n sc sp c content contentIndent inputEnd
    hcorr hpeek hlb hblk hn hnci

open L4YAML.Surface L4YAML.Scanner L4YAML.CharPredicates L4YAML.Proofs
  L4YAML.Proofs.CouplingBridge L4YAML.Proofs.ScalarFoldAt in
/-- …and the multi-line PLAIN value reads at the pending's own index with no
    residue at all. -/
example {n : Nat} {sc : ScannerState} {sp : SurfPos} {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s')
    (hinflow : sc.inFlow = false)
    (hn : n ≤ L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf sc) :
    ∃ sp_gram sp'', SFlowContent n .flowOut sp sp_gram ∧
      GStar SSWhite sp_gram sp'' ∧ ScannerSurfCorr s' sp'' :=
  let ⟨sp_gram, sp'', h1, h2, _, h4⟩ :=
    scanPlainScalar_to_flowContent_at n sc sp hcorr hpeek hstart h_not_doc hok hinflow hn
  ⟨sp_gram, sp'', h1, h2, h4⟩

end L4YAML.Tests.Guards.ScannerPlainBlankFoldTab

end Blanket
