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

/-! # The directive document's own `[211]` arm (DOCS item 138)

Items 136 and 137 gave the landing's route face its HEAD and MARKER arms and
moved whole caller families off the fallback, but the `implicitContinue`
application count did not move: those items delete callers, not sites.  This
one deletes a site, and the site it deletes is the one item 135 named and could
not fix.

**A directive document has no implicit-continuation reading at all.**  `[211]
l-yaml-stream`'s implicit continuation carries an `l-any-document?`, so it
TYPES a `[209] l-directive-document` — but the scanner refuses directives after
content with no `...` (§1), so no stream ever reaches a directive document that
way.  The two readings that exist are the stream's own head (`single`'s
`l-any-document?` slot, behind `[202] l-document-prefix*`) and the slot a `...`
opens (`suffixContinue`'s).  Item 135 wrote that down and left the site
standing, because WHICH of the two holds is a datum the park did not carry.

**What carries it is the flag `scanDirective` itself reads.**  A `%` reaches
`structural_dispatch_to_pending` only with `allowDirectives` up, and only two
parks can have it up: the stream's own seed (`noPending`, whose `h_nodoc` is
the prefix run) and a `...` (`pendingDocEnd`, whose marker and stream are the
suffix run).  Every other park is produced PAST the structural dispatch, where
`scanNextToken` has already cleared the flag — so this item gives those seven
constructors `h_nodir : sc.allowDirectives = false` and they refute the premise
instead of answering it.  `PendingNode.dirRoute` is that case split; the `%`
spends it once and hands the ROUTE down the run, and the `---` that finishes
the run applies it.

**Measured.**  A reference-count walk over the elaborated terms puts
`SLYamlStream.implicitContinue` at **ten** applications in **nine** holders,
down from eleven in ten: `structural_dispatch_after_directives` no longer
mentions it.  Flipping the constructor's `[210]` slot to `SLExplicitDocument`
gives **eight** errors in `StreamAccum`, down from nine, and the lemma that
leaves the list is that one.  The payment is fifty-odd construction sites for
`h_nodir`, one term each, off three per-dispatcher lemmas (§4).

No runtime file is touched, so every verdict in §1 is the one the pipelines
already gave.

§1 is the family at the runtime, §2 the two refusals it has to keep apart;
§3–§5 are the builds at their types; §6 is what remains. -/

namespace L4YAML.Tests.Guards.StreamDirectiveDocumentArm

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-! ## §1 The two arms at the runtime

A directive document is one document, and the stream it sits in has either
nothing in front of it but `[202]` prefixes, or a `[205]` suffix run. -/

-- THE HEAD ARM.  Nothing but prefixes in front of the `%`, so the document
-- lands in `single`'s own `l-any-document?` slot.
#guard emits "%YAML 1.2\n---\n- a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "%YAML 1.2\n---\na: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "%YAML 1.2\n---\nhello\n"
  ["+STR", "+DOC ---", "=VAL :hello", "-DOC", "-STR"]
-- The `[202]` prefixes themselves: a comment line and blank lines before the
-- directive are the `single` arm's own leading run.
#guard emits "# c\n%YAML 1.2\n---\na\n"
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
#guard emits "\n\n%YAML 1.2\n---\na\n"
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
-- `%` EXTENDS the run (`GPlus_snoc`), and the arm rides the extension
-- unchanged — it is the run's, not any one directive's.
#guard emits "%YAML 1.2\n%TAG !e! tag:example.com,2000:\n---\na\n"
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
-- ...including where the marker's document is EMPTY, which is the close's own
-- `GAlt.right` rather than a landing.
#guard emits "%YAML 1.2\n---\n" ["+STR", "+DOC ---", "=VAL :", "-DOC", "-STR"]
#guard emits "%YAML 1.2\n---\n...\n"
  ["+STR", "+DOC ---", "=VAL :", "-DOC ...", "-STR"]

-- THE SUFFIX ARM.  A `...` re-arms the flag (`scanDocumentEnd` sets
-- `allowDirectives := true`), so the directives that follow open a SECOND
-- document in `suffixContinue`'s own slot.
#guard emits "a: 1\n...\n%YAML 1.2\n---\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC ---", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "- a\n...\n%YAML 1.2\n---\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC ...",
   "+DOC ---", "+SEQ", "=VAL :b", "-SEQ", "-DOC", "-STR"]
-- A LEADING `...` parks the same constructor with an empty stream behind it,
-- and the arm is still `suffixContinue`'s.
#guard emits "...\n%YAML 1.2\n---\na\n"
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]

-- THE THIRD READING, refused.  This is why the implicit continuation has no
-- domain here: a directive after content with no `...` never scans.
#guard refuses "a: 1\n%YAML 1.2\n---\nb: 2\n"
#guard refuses "- a\n%YAML 1.2\n---\n- b\n"
#guard refuses "\"x\"\n%YAML 1.2\n---\na\n"
-- ...and the boundary that says the refusal is the DIRECTIVE scan's, not a
-- line-start rule: behind a PLAIN scalar the `%` line is the scalar's own
-- continuation (`[126] ns-plain-first` excludes `%` only at a node's start),
-- so nothing structural happens there at all.
#guard emits "hello\n%YAML 1.2\n---\na\n"
  ["+STR", "+DOC", "=VAL :hello %YAML 1.2", "-DOC",
   "+DOC ---", "=VAL :a", "-DOC", "-STR"]
#guard refuses "hello\n# c\n%YAML 1.2\n---\na\n"

/-! ## §2 The message the refusal actually carries

Item 135's note named `directiveWithoutDocument` for this input.  That is the
OTHER refusal — directives with no `---` after them — and both are pinned here
so the two stay apart.  (Struck and corrected in place at
`PendingNode.pendingDocStart`'s docstring.) -/

private def pipeErr (input : String) : Option String :=
  match Events.streamToEvents input with
  | .error e => some (toString e)
  | .ok _ => none

private def pipeErrIx (input : String) : Option String :=
  match Events.streamToEventsIx input with
  | .error e => some (toString e)
  | .ok _ => none

private def saysAlike (input : String) (e : ScanError) : Bool :=
  let m := some (toString e)
  pipeErr input == m && pipeErrIx input == m

-- The directive AFTER content: `scanDirective`'s own first test.
#guard saysAlike "a: 1\n%YAML 1.2\n---\nb: 2\n" (.directiveAfterContent 1)
#guard saysAlike "\"x\"\n%YAML 1.2\n---\na\n" (.directiveAfterContent 1)
#guard saysAlike "hello\n# c\n%YAML 1.2\n---\na\n" (.directiveAfterContent 2)
-- The directive with no document after it: `checkNoPendingDirectives`.
#guard saysAlike "%YAML 1.2\na: 1\n" (.directiveWithoutDocument 1)
#guard saysAlike "a: 1\n...\n%YAML 1.2\na: 2\n" (.directiveWithoutDocument 3)

/-! ## §3 The park's field, and the two arms it can hold -/

/-- `pendingDirective` carries a ROUTE for `[209]`, the shape item 135 gave
    `pendingDocStart` for `[208]`. -/
example {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}
    (h_dir_acc : ∀ sp_mid, SSLComments sp_scan sp_mid →
      GPlus SLDirective sp_block sp_mid)
    (h_stream : SLYamlStream sp_start sp_block)
    (h_dir_route : ∀ sp_end,
      SLDirectiveDocument sp_block sp_end → SLYamlStream sp_start sp_end)
    (h_next : sc.inFlow = false → NextIsSep sc) :
    PendingNode sc true sp_start sp_block sp_scan :=
  PendingNode.pendingDirective sp_start sp_block sp_scan h_dir_acc h_stream h_dir_route h_next

/-- The HEAD arm: `[211]`'s `single`, whose document slot the 1c tightening
    leaves untouched. -/
example {sp_start sp_mid sp_end : SurfPos}
    (h_pre : GStar SLDocumentPrefix sp_start sp_mid)
    (h_dd : SLDirectiveDocument sp_mid sp_end) :
    SLYamlStream sp_start sp_end :=
  SLYamlStream.single sp_start sp_mid sp_end sp_end h_pre
    (GOpt.some sp_mid sp_end (SLAnyDocument.directive sp_mid sp_end h_dd))
    (GStar.nil _)

/-- The SUFFIX arm: `suffixContinue`'s own `l-any-document?`, item 117's face
    with a directive document in the slot instead of a bare one. -/
example {sp_start sp₁ sp₂ sp_mid sp_end : SurfPos}
    (h_stream : SLYamlStream sp_start sp₁)
    (h_plus : GPlus SLDocumentSuffix sp₁ sp₂)
    (h_pre : GStar SLDocumentPrefix sp₂ sp_mid)
    (h_dd : SLDirectiveDocument sp_mid sp_end) :
    SLYamlStream sp_start sp_end :=
  SLYamlStream.suffixContinue sp_start sp₁ sp₂ sp_mid sp_end sp_end h_stream h_plus h_pre
    (GOpt.some sp_mid sp_end (SLAnyDocument.directive sp_mid sp_end h_dd))
    (GStar.nil _)

/-- ...and the arm the directive path no longer builds.  It still TYPES — the
    constructor is untightened, and that is exactly why the measurement is a
    reference COUNT and a constructor flip rather than a typechecker verdict. -/
example {sp_start sp_mid sp_end : SurfPos}
    (h_stream : SLYamlStream sp_start sp_mid)
    (h_dd : SLDirectiveDocument sp_mid sp_end) :
    SLYamlStream sp_start sp_end :=
  SLYamlStream.implicitContinue sp_start sp_mid sp_mid sp_end sp_end h_stream
    (GStar.nil _)
    (GOpt.some sp_mid sp_end (SLAnyDocument.directive sp_mid sp_end h_dd))
    (GStar.nil _)

/-! ## §4 The park face that decides between them -/

/-- `PendingNode.dirRoute` at its type: given the flag, the park says which
    arm — and the `%` branch is the only caller that can supply the flag. -/
example {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}
    (h : PendingNode sc false sp_start sp_block sp_scan)
    (h_stream : SLYamlStream sp_start sp_block)
    (h_noflow : sc.inFlow = false)
    (h_allow : sc.allowDirectives = true) :
    ∀ sp_mid, SSLComments sp_scan sp_mid →
      ∀ sp_end, SLDirectiveDocument sp_mid sp_end → SLYamlStream sp_start sp_end :=
  h.dirRoute h_stream h_noflow h_allow

/-- The seed pays the head arm off `h_nodoc` — the carrier item 116 built and
    item 135 made spendable by dropping its premise. -/
example {sc : ScannerState} {sp_start sp : SurfPos}
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    (h_noflow : sc.inFlow = false)
    (h_ssl : SSLComments sp sp)
    (h_col0 : sp.col = 0) :
    GStar SLDocumentPrefix sp_start sp :=
  ssl_comments_extend_prefixes (h_nodoc h_noflow) h_col0 h_ssl

/-- The `...` park pays the suffix arm off its own marker — `[205]
    l-document-suffix` is the marker plus the landing's `[79] s-l-comments`,
    which is item 117's `SuffixRun` with the slot still open. -/
example {sp_start sp_block sp_scan sp_mid : SurfPos}
    (h_stream : SLYamlStream sp_start sp_block)
    (h_marker : SCDocumentEnd sp_block sp_scan)
    (h_ssl : SSLComments sp_scan sp_mid) :
    SuffixRun sp_start sp_mid :=
  ⟨sp_block, sp_mid, h_stream,
   GPlus.mk sp_block sp_mid sp_mid
     (SLDocumentSuffix.mk sp_block sp_scan sp_mid h_marker h_ssl) (GStar.nil _),
   GStar.nil _⟩

/-- The other seven parks refute the premise, and this is the whole of the
    argument: the field against the flag. -/
example {sc : ScannerState} (h_nodir : sc.allowDirectives = false)
    (h_allow : sc.allowDirectives = true) : False := by
  simp [h_nodir] at h_allow

/-! ## §5 The `allowDirectives` face, paid once per dispatcher

Fifty-odd construction sites carry `h_nodir`, and none of them argues: the flag
is cleared before the three dispatchers run and none of them writes it again.
The three lemmas below are that sentence, and each site is one application of
one of them — item 47's `stale_of_dispatch` shape. -/

example {s_prep s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    s'.allowDirectives = false := nodir_of_content_dispatch h

example {s_prep s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    s'.allowDirectives = false := nodir_of_block_dispatch h

example {s_prep s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    s'.allowDirectives = false := nodir_of_flow_dispatch h

/-- The premise the `%` branch discharges, and the reason only it can. -/
example {s s' : ScannerState} (h : scanDirective s = .ok s') :
    s.allowDirectives = true :=
  L4YAML.Proofs.ScannerAllowDirectives.scanDirective_allowDirectives h

/-- And the `---` park's own answer, which needs no lemma: `scanDocumentStart`
    clears the flag itself (§9.1.2). -/
example (s : ScannerState) : (scanDocumentStart s).allowDirectives = false := rfl

/-! ## §6 What still reaches `implicitContinue`

Ten applications in nine holders after this item.  Seven of the nine append a
completed top-level node as a fresh BARE document — the family the refutation
is for — one is the `SLAnyDocument.explicit` wrapper at
`structural_dispatch_to_pending` (legal as written; the flip's error there is a
one-line unwrap), and one does not break at all. -/

/-- `ssl_comments_extend_stream`'s use passes `GOpt.none`: no document at all in
    the slot, so it types under either reading and the flip leaves it alone.
    That is why the application count (ten) and the flip's error count (eight)
    are different numbers, and both are worth stating. -/
example {sp_start sp sp_final : SurfPos}
    (h_stream : SLYamlStream sp_start sp)
    (h_pre : GStar SLDocumentPrefix sp sp_final) :
    SLYamlStream sp_start sp_final :=
  SLYamlStream.implicitContinue sp_start sp sp_final sp_final sp_final
    h_stream h_pre (GOpt.none _) (GStar.nil _)

/-- The bare-document family that remains — `rootMapRoute`'s shape, the
    fallback every punting park still uses.  Refuting it is the next item, and
    what it needs is a park field for "the last real token completes a node"
    plus a coupling to the indent stack. -/
example {sp_start sp_mid sp_end : SurfPos}
    (h_stream : SLYamlStream sp_start sp_mid)
    (h_bd : SLBareDocument sp_mid sp_end) :
    SLYamlStream sp_start sp_end :=
  SLYamlStream.implicitContinue sp_start sp_mid sp_mid sp_end sp_end h_stream
    (GStar.nil _)
    (GOpt.some sp_mid sp_end (SLAnyDocument.bare sp_mid sp_end h_bd))
    (GStar.nil _)

end L4YAML.Tests.Guards.StreamDirectiveDocumentArm

end Blanket
