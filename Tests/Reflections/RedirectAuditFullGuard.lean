/-!
# Reflection 413 — on redirect, audit the replacement producer's WHOLE guard; clearing one axis ≠ clearing another

Self-contained (core Lean, no `L4YAML` import) toy model of the de-risk behind the `h_seq_rec` producer
choice.

A de-risk refutes a producer/consumer-slot guard on ONE strength axis and REDIRECTS to a replacement
producer, attaching an adjective that names the CLEARED axis ("enclosure-blind"). The trap: a producer's
hypothesis bundle is a CONJUNCTION of guards on INDEPENDENT axes, and the adjective is silent on the
others. The replacement can carry a SECOND too-strong guard on an orthogonal axis — and that guard may
ALREADY be known-FALSE from an earlier probe, whose re-scoped PARALLEL type was built but NEVER
propagated into the replacement's signature, so the producer still consumes the stale false guard.

Mirrors L4YAML R412→R413: R412 refuted the navigator-locator's `SeqPathAllSeq` (axis A — the
enclosure/path routing tag) and redirected to `seqWindowRecSeqBody`, calling it "enclosure-blind". R413
re-read that producer's signature and found axis B: it consumes the OLD `FlowBodyContentDeep` (whose
opener field fires at MAP `{` openers), already proved false by R392, re-scoped to `FlowBodyContentDeepSeq`
by R393 — but the producer was never migrated onto the parallel type.

* `routingTagA` models axis A (the navigator's routing tag — the R412 axis).
* `deepOld` models axis B's OLD guard: every delta-1 opener (seq `[` OR map `{`) is followed by a content
  start. FALSE wherever a `{` precedes a `key`.
* `deepSeqNew` models axis B's RE-SCOPED parallel guard: only SEQ openers must be followed by content.
  TRUE on the same windows (the migration target).
-/

namespace Tests.Reflections.RedirectAuditFullGuard

set_option autoImplicit false

/-- A toy token kind: seq/map openers and closers, plus the map `key` and a content `scalar`. -/
inductive Tok where
  | seqStart | mapStart | key | scalar | seqEnd | mapEnd
  deriving DecidableEq

/-- A content start: a scalar or either opener (mirrors `isFlowContentStart`). -/
def isContentStart : Tok → Bool
  | .scalar | .seqStart | .mapStart => true
  | _ => false

/-- A delta-1 opener: BOTH `[` and `{` (mirrors `flowBracketDelta = 1`). -/
def isOpenerDelta1 : Tok → Bool
  | .seqStart | .mapStart => true
  | _ => false

/-- **Axis B, OLD guard** — every delta-1 opener is followed by a content start (mirrors
    `FlowBodyContentDeep.openerContentStart`). FALSE wherever a `{` precedes a `key`. -/
def deepOld : List Tok → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!isOpenerDelta1 a || isContentStart b) && deepOld (b :: rest)

/-- **Axis B, RE-SCOPED parallel guard** — only SEQ openers must be followed by content (mirrors
    `FlowBodyContentDeepSeq.openerContentStart`, keyed on `.flowSequenceStart`). VACUOUS at a `{`. -/
def deepSeqNew : List Tok → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!(a == Tok.seqStart) || isContentStart b) && deepSeqNew (b :: rest)

/-- **Axis A** — the navigator's routing tag (the R412 axis): the window does not OPEN with a map frame. -/
def routingTagA : List Tok → Bool
  | [] => false
  | a :: _ => a != Tok.mapStart

/-- A seq body window whose single entry is a MAP — `{ key scalar }`.  In the slot's weak-guard domain. -/
def mapWin : List Tok := [.mapStart, .key, .scalar, .mapEnd]
/-- An all-seq body window — `[ scalar ]`. -/
def seqWin : List Tok := [.seqStart, .scalar, .seqEnd]
/-- A window that PASSES axis A (opens with a seq) yet contains a `{ key` deeper in — the independence
    witness: clearing axis A leaves axis B broken. -/
def mixedWin : List Tok := [.seqStart, .scalar, .mapStart, .key, .seqEnd]

/-! ## NEGATIVE — the navigator's axis A fails on the map window (the R412 finding, recapped) -/

theorem navigator_axisA_fails_on_map : routingTagA mapWin = false := by decide

/-! ## NEGATIVE — the replacement producer's axis-B OLD guard ALSO fails on the SAME window

The redirect cleared axis A, but the replacement still consumes the stale `deepOld`, which is FALSE here —
the hidden second axis. -/

theorem replacement_axisB_old_fails_on_map : deepOld mapWin = false := by decide

/-! ## POSITIVE — the re-scoped parallel guard HOLDS, naming the migration target -/

theorem rescoped_axisB_new_holds_on_map : deepSeqNew mapWin = true := by decide

/-- **The minimal pair on ONE window** — the OLD axis-B guard is FALSE, the re-scoped parallel guard is
    TRUE, on the same window the slot must cover.  The discriminator is the opener keying (delta-1-any vs
    seq-only). -/
theorem map_window_minimal_pair :
    deepOld mapWin = false ∧ deepSeqNew mapWin = true := by decide

/-- **The crux — clearing axis A does NOT clear axis B.**  `mixedWin` PASSES the navigator's routing tag
    (axis A) yet the replacement producer's OLD deep-content guard (axis B) FAILS on it, while the
    re-scoped parallel guard HOLDS.  A redirect that only refuted axis A leaves axis B an independent,
    unaudited residual — the two strength axes vary independently. -/
theorem clearing_axisA_does_not_clear_axisB :
    routingTagA mixedWin = true ∧ deepOld mixedWin = false ∧ deepSeqNew mixedWin = true := by decide

-- the navigator can't serve the map window (axis A) …
#guard routingTagA mapWin == false
-- … and the redirect's replacement can't either (axis B OLD), on the very same window …
#guard deepOld mapWin == false
-- … but the re-scoped parallel guard holds — migrate the producer onto it.
#guard deepSeqNew mapWin == true
-- independence: a window can pass axis A yet fail axis B(old) while axis B(new) holds.
#guard routingTagA mixedWin && (deepOld mixedWin == false) && deepSeqNew mixedWin

end Tests.Reflections.RedirectAuditFullGuard
