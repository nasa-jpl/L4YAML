/-!
# Reflection 419 — a producer-mirror's ONE non-cloning boundary corner is the CONSUME side's carrier
END-DUAL: search the carrier before pricing it a fresh derivation

Self-contained (core Lean, no `L4YAML` import) toy model of `noTrailingSep_preClose_of_carrier` (R419),
the brick that SOURCES the owed boundary input of the R418 produce-side joint
`globalFlowSeqSepAdj_of_structure`.

R418 (`BoundaryDischargeGateTriggerTyped`) classified a gated producer-mirror's discharge: the five-way
`k`-split skeleton clones, EXCEPT the pre-close cell, and the seq separator lands in cell 3 (gate `≠ key`
ADMITS the close, trigger `sep` is balance-neutral) ⇒ it owes "a genuinely new no-trailing-X structural
fact" `tokAt l (size-3) ≠ sep`.  R418 HEDGED its sourcing ("from the carrier OR a fresh structure field").

This reflection RESOLVES the hedge.  The owed fact is NOT a fresh derivation — it is the END-DUAL of a
carrier the CONSUME side already threads:

* the PRODUCE side needs `tokAt l (size-3) ≠ sep`  (no trailing separator before the close);
* the CONSUME side's carrier `noTrailingFact l 2 (size-2)` (toy of R416 `noTrailingSepFact`) needs the
  DUAL — a `sep` at the window's LAST position would force its successor to be content-start.

They read the SAME last-position token, opposite polarities.  And the carrier is ALREADY a theorem
(delivered by a sibling whole-structure lemma for the root seed's per-window discharge — a DIFFERENT
consumer, not the producer mirror).  So the discharge is ONE carrier-instantiation at `k = size-3`:
instantiate, rewrite the successor to the close (`cls`), and the carrier's `isContent` conclusion is FALSE
there (the close is non-content) ⇒ the trailing-separator premise is refuted.  No fresh induction.

Mirrors L4YAML R419:
* `noTrailingFact`                — the consume-side carrier (toy of `noTrailingSepFact tokens 2 (size-2)`).
* `preCloseNotSep_of_carrier`     — the discharge: the R418 cell-3 residual `tokAt l (size-3) ≠ sep` from
                                     the carrier in one instantiation (the close is non-content).
* `preCloseNotSep_wOK`            — a concrete POSITIVE application on a well-formed witness.
* `carrier_false_on_trailing_sep` — NEGATIVE: the carrier is FALSE on a trailing-separator witness, so it
                                     is a genuine emitter constraint the discharge consumes, not vacuous.
* `carrier_holds_when_close_is_content` / `preClose_is_sep_when_close_is_content` — the load-bearing
                                     premise is `isContent(close) = false`: when the boundary successor IS
                                     content, the carrier holds yet the pre-close IS a separator, so the
                                     END-DUAL discharge would not go through.

Sharpens `BoundaryDischargeGateTriggerTyped` (R418 — resolves its cell-3 hedge to "the carrier, no fresh
field"); the discharge mechanism is the no-trailing END-DUAL (refute the trailing-trigger premise via its
false content-start conclusion past the window).
-/

namespace Tests.Reflections.NoncloningCornerEndDualOfCarrier

set_option autoImplicit false

/-- Toy token kinds: seq opener `opn` / closer `cls`, separator `sep`, content scalar `scal`. -/
inductive Tok where
  | opn | cls | sep | scal
  deriving DecidableEq, BEq

/-- Bracket balance delta (toy of `flowBracketDelta`): openers `+1`, closers `−1`, else `0`. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _ => 0

/-- A content start: a scalar or an opener (toy of `isFlowContentStart`).  Crucially `isContent cls =
    false` — the close is NOT content, the lever the END-DUAL discharge pulls. -/
def isContent : Tok → Bool
  | .scal | .opn => true
  | _ => false

/-- A token stream, indexed with a default so positions never need bounds proofs (toy of `tokens[·]!`). -/
def tokAt (l : List Tok) (i : Nat) : Tok := l.getD i Tok.scal

/-- Prefix balance (toy of `flowBracketBalance tokens 0 n`). -/
def bal (l : List Tok) : Nat → Int
  | 0 => 0
  | n + 1 => bal l n + delta (tokAt l n)

/-- Windowed balance `[a, b)` (toy of `flowBracketBalance tokens a b`).  `balW l a a = 0` always. -/
def balW (l : List Tok) (a b : Nat) : Int := bal l b - bal l a

/-! ## The CONSUME-side carrier — the END-form fact the root seed's per-window discharge already threads. -/

/-- The consume-side carrier (toy of `noTrailingSepFact tokens 2 (size-2)`, R416): a `sep` at the window's
    LAST position (`k + 1 = b`, depth-`0`) forces its successor to be a content start.  This is the
    END-DUAL of the producer's "no trailing separator before the close" — same last-position token, the
    opposite polarity. -/
def noTrailingFact (l : List Tok) (a b : Nat) : Prop :=
  ∀ k, a ≤ k → k + 1 = b → tokAt l k = Tok.sep → balW l a k = 0 →
    isContent (tokAt l (k + 1)) = true

/-! ## The discharge — the R418 cell-3 residual from the carrier in ONE instantiation. -/

/-- **The non-cloning corner is paid by the carrier** (toy of `noTrailingSep_preClose_of_carrier`, R419).
    R418's cell-3 owed `tokAt l (size-3) ≠ sep`.  It discharges from the consume-side carrier: instantiate
    `noTrailingFact l 2 (size-2)` at `k = size-3`, rewrite the successor to the close (`cls`), and the
    carrier's content-start conclusion is FALSE there (`isContent cls = false`) — the trailing-separator
    premise is refuted.  No fresh emitter induction; the boundary balance is the only side input. -/
theorem preCloseNotSep_of_carrier (l : List Tok)
    (h_sz : 5 ≤ l.length)
    (h_close : tokAt l (l.length - 2) = Tok.cls)
    (h_bal : balW l 2 (l.length - 3) = 0)
    (h_carrier : noTrailingFact l 2 (l.length - 2)) :
    tokAt l (l.length - 3) ≠ Tok.sep := by
  intro h_sep
  have hk : (l.length - 3) + 1 = l.length - 2 := by omega
  have h2 : 2 ≤ l.length - 3 := by omega
  have h_cs := h_carrier (l.length - 3) h2 hk h_sep h_bal
  rw [hk, h_close] at h_cs           -- h_cs : isContent cls = true
  simp [isContent] at h_cs           -- FALSE — the close is non-content

/-! ## POSITIVE — a well-formed witness `[opn, scal, scal, cls, scal]` (close at size-2, no trailing sep). -/

def wOK : List Tok := [Tok.opn, Tok.scal, Tok.scal, Tok.cls, Tok.scal]

#guard tokAt wOK (wOK.length - 2) == Tok.cls            -- close sits at size-2
#guard tokAt wOK (wOK.length - 3) == Tok.scal           -- pre-close is content, no trailing separator
#guard isContent (tokAt wOK (wOK.length - 2)) == false  -- the close is non-content (the END-DUAL's lever)

/-- The carrier holds on `wOK` — vacuously at the pre-close (its token is `scal`, not `sep`). -/
theorem carrier_wOK : noTrailingFact wOK 2 (wOK.length - 2) := by
  intro k _ hk1 hsep _
  have hlen : wOK.length = 5 := rfl
  have hk2 : k = 2 := by omega
  subst hk2
  exact absurd hsep (by decide)

/-- The R418 cell-3 residual, discharged on `wOK` via the carrier — a concrete positive instance. -/
theorem preCloseNotSep_wOK : tokAt wOK (wOK.length - 3) ≠ Tok.sep :=
  preCloseNotSep_of_carrier wOK (by decide) (by decide)
    (by show balW wOK 2 2 = 0; simp [balW]) carrier_wOK

/-! ## NEGATIVE — the carrier is a GENUINE constraint: FALSE on a trailing-separator witness. -/

/-- A trailing-separator witness `[opn, scal, sep, cls, scal]`: close `cls` at size-2, a `sep` at size-3.
    The discharge consumes the carrier, so the carrier must be a real (non-vacuous) emitter invariant —
    and here it is FALSE, exactly because the trailing separator's successor is the non-content close. -/
def wTrail : List Tok := [Tok.opn, Tok.scal, Tok.sep, Tok.cls, Tok.scal]

#guard tokAt wTrail (wTrail.length - 2) == Tok.cls   -- the close sits at size-2
#guard tokAt wTrail (wTrail.length - 3) == Tok.sep   -- a TRAILING separator sits at size-3

theorem carrier_false_on_trailing_sep : ¬ noTrailingFact wTrail 2 3 := by
  intro h
  have hbal : balW wTrail 2 2 = 0 := by simp [balW]
  have hc : isContent (tokAt wTrail (2 + 1)) = true :=
    h 2 (by decide) (by decide) (by decide) hbal
  exact absurd hc (by decide)

/-! ## The load-bearing premise — the END-DUAL needs `isContent(close) = false`.

    On a witness whose boundary successor IS content, the carrier HOLDS yet the pre-close IS a separator,
    so the discharge's conclusion `tokAt l (size-3) ≠ sep` would be FALSE.  The discharge works precisely
    because the boundary successor is the non-content close. -/

def wContentClose : List Tok := [Tok.opn, Tok.scal, Tok.sep, Tok.scal, Tok.scal]

#guard isContent (tokAt wContentClose (wContentClose.length - 2)) == true  -- boundary successor IS content
#guard tokAt wContentClose (wContentClose.length - 3) == Tok.sep           -- yet the pre-close IS a sep

/-- The carrier HOLDS when the boundary successor is content (its conclusion is satisfied, not refuted). -/
theorem carrier_holds_when_close_is_content : noTrailingFact wContentClose 2 3 := by
  intro k _ hk1 _ _
  have hk2 : k = 2 := by omega
  subst hk2
  decide

/-- … yet the pre-close IS a separator — so without `isContent(close) = false` the discharge cannot run. -/
theorem preClose_is_sep_when_close_is_content :
    tokAt wContentClose (wContentClose.length - 3) = Tok.sep := by decide

end Tests.Reflections.NoncloningCornerEndDualOfCarrier
