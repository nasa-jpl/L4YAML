/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Coupling.CouplingBridge
public import L4YAML.Proofs.Scanner.BlockScalarFlowGuard
public import L4YAML.Proofs.Scanner.ScannerLinePreservation
public import L4YAML.Proofs.Scanner.ScalarWalkColFloor

@[expose] public section Blanket

/-! # No inline flow open ahead — the depth-0 refutation fact (item 10, site 5)

`accum_flow_open_depth0`'s no-break arm (`col ≠ 0`, only `s-white` crossed)
must REFUTE the closeable pendings whose construct is already complete: after
a quoted scalar, an alias, a flow close back to block, or a `...`, a `[`/`{`
on the same line is exactly what the scanner's trailing-content family
rejects — `validateTrailingContent` ([109]/[120] via §7.5),
`validateAliasClose` (item 9h), `validateFlowClose` ([137]/[140]),
`scanDocumentEnd`'s suffix check ([204]) — and a plain scalar in block
context ABSORBS a same-line `[` (`ns-plain-safe-out` [128] admits it), while
a block scalar ends at column 0 or end of input.

This file packages that one dispatch's worth of lookahead as a fact about
the REST OF THE LINE, carried by the pending state to the flow-open step:

* **`LineStop P`** — the surface reading, INDEXED by its stop set: optional
  `s-white`, then either end of input or a non-white head in `P`.  Item 10
  wrote one set into the predicate (`NoOpenHead`) and projected every producer
  onto it; items 36/37 name the rungs the producers actually decide —
  `TailSuffix` (`[204]`'s `s-l-comments`), `NodeTail` (§7.5: `s-l-comments`
  plus `[154]`/`[155]`'s `:`), `OffLine` (outside `[1] c-printable`, or the
  BOM), and their union `NodeStop` — with `LineStop.mono` at the CONSUMER.
  `LineNoOpen` is `LineStop NoOpenHead`, and every old consumer is unchanged.
* **`RestNoOpen`** — the scanner-side reading, quantified over
  `CharsFromOffset` so producers never touch `SurfPos`.
* **Producers** — one per family, each reading the guard that ran when the
  pending was built.
* **Consumers** — transport under the preprocessing whites
  (`LineNoOpen.strip`), and the head refutation against a dispatched
  `[`/`{` (`LineNoOpen.not_open_head`).
-/

set_option maxHeartbeats 1000000

namespace L4YAML.Proofs.LineOpenGuard

open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.CouplingBridge
open L4YAML.CharPredicates
open L4YAML.Proofs.ScannerProgress
open L4YAML.Proofs.ScannerCorrectness.ScanHelpers
open L4YAML.Proofs.BlockScalarFlowGuard
open L4YAML.Proofs.ScalarWalkColFloor (advance_col_succ_of_peek skipWhitespace_col_ge)

/-! ## §1 The predicate and its surface consumers

The predicate is indexed by its STOP SET — the characters the producer's own
validator admitted.  Item 10 wrote one stop set INTO the predicate (`¬(c = '['
∨ c = '{')`) and projected all four validators onto it inside the producers
(`stop_of_allowlist`), because the consumer of the day asked only about a flow
open.  The strength discarded there is exactly what a later consumer needs:
`[204] l-document-suffix`'s tail is `[79] s-l-comments` and admits a break or
a `#` and nothing else, which refutes a same-line `-`/`?`/`:` as flatly as it
refutes a `[`.  So the set rides the predicate and the projection happens at
the CONSUMER (`LineStop.mono`), which costs the old consumers one `mono` and
buys the new ones the difference. -/

/-- The rest of the current line stops in `P`: optional `s-white` [33], then
    end of input or a head that is not white and satisfies `P`. -/
inductive LineStop (P : Char → Prop) : List Char → Prop where
  | nil : LineStop P []
  | stop {c : Char} (rest : List Char)
      (hnw : ¬(c = ' ' ∨ c = '\t'))
      (hst : P c) : LineStop P (c :: rest)
  | white {c : Char} {rest : List Char}
      (hw : c = ' ' ∨ c = '\t')
      (t : LineStop P rest) : LineStop P (c :: rest)

/-- **The projection, moved to the consumer.**  A stop set weakens freely;
    this single step is what every producer used to take on its own behalf. -/
lemma LineStop.mono {P Q : Char → Prop} (hPQ : ∀ c, P c → Q c) :
    ∀ {l : List Char}, LineStop P l → LineStop Q l := by
  intro l h
  induction h with
  | nil => exact .nil
  | stop rest hnw hst => exact .stop rest hnw (hPQ _ hst)
  | white hw _ ih => exact .white hw ih

/-- The head of a stopped line satisfies the stop set, once it is known not
    to be one of the leading whites. -/
lemma LineStop.head_stop {P : Char → Prop} {c : Char} {rest : List Char}
    (h : LineStop P (c :: rest)) (hnw : ¬(c = ' ' ∨ c = '\t')) : P c := by
  cases h with
  | stop _ _ hst => exact hst
  | white hw _ => exact absurd hw hnw

/-- One `s-white` step strips one white char and preserves the fact. -/
lemma LineStop.strip_one {P : Char → Prop} {sp sp' : SurfPos}
    (hw : SSWhite sp sp') (h : LineStop P sp.chars) : LineStop P sp'.chars := by
  cases hw with
  | space rest col =>
    cases h with
    | stop _ hnw _ => exact absurd (Or.inl rfl) hnw
    | white _ t => exact t
  | tab rest col =>
    cases h with
    | stop _ hnw _ => exact absurd (Or.inr rfl) hnw
    | white _ t => exact t

/-- Preprocessing's no-break residue is `s-white*`; the fact survives it. -/
lemma LineStop.strip {P : Char → Prop} {sp sp' : SurfPos}
    (hws : GStar SSWhite sp sp') (h : LineStop P sp.chars) :
    LineStop P sp'.chars := by
  induction hws with
  | nil => exact h
  | cons _ _ _ hstep _ ih => exact ih (h.strip_one hstep)

/-- **The consumer's own read**: the character a no-break step dispatches is
    in the stop set the producing validator admitted.  `hhead` is that
    character read back through the correspondence. -/
lemma LineStop.across_whites {P : Char → Prop} {sp sp' : SurfPos} {c : Char}
    (h : LineStop P sp.chars) (hws : GStar SSWhite sp sp')
    (hhead : sp'.chars.head? = some c) (hnw : ¬(c = ' ' ∨ c = '\t')) : P c := by
  have h' := h.strip hws
  cases hchars : sp'.chars with
  | nil => rw [hchars] at hhead; cases hhead
  | cons c' rest =>
    rw [hchars] at hhead h'
    injection hhead with hce
    subst hce
    exact h'.head_stop hnw

/-! ### §1a The stop sets

Three rungs, weakest last, each named for the production that decides it. -/

/-- `[204] l-document-suffix ::= c-document-end s-l-comments` — the tail of a
    `...`, which admits a break, a `#`, or end of input and NOTHING else: a
    document-end marker is not a node and cannot be a key. -/
def TailSuffix (c : Char) : Prop := isLineBreakBool c = true ∨ c = '#'

/-- Item 10's set: the rest of the line cannot dispatch a flow open.  (A
    break, `#`, `:`, `-`, a non-printable — anything a completed construct's
    trailing validation admits — satisfies it.) -/
def NoOpenHead (c : Char) : Prop := ¬(c = '[' ∨ c = '{')

lemma TailSuffix.toNoOpenHead {c : Char} (h : TailSuffix c) : NoOpenHead c := by
  simp only [TailSuffix, isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
    Bool.or_eq_true, beq_iff_eq] at h
  rintro (rfl | rfl) <;> simp_all

/-- §7.5's own allowlist — the tail of a COMPLETE block-context NODE:
    `[79] s-l-comments`, plus the `:` that `[154] ns-s-implicit-yaml-key` and
    `[155] c-s-implicit-json-key` put after a node on its own line.  This is
    what `validateTrailingContent`, `validateAliasClose` and
    `validateFlowClose` decide, character for character — one rung weaker than
    `[204]`'s, because a node CAN be a key and a `...` cannot. -/
def NodeTail (c : Char) : Prop := TailSuffix c ∨ c = ':'

/-- Outside `[1] c-printable`, or the byte order mark (`[3] c-byte-order-mark`
    is printable, but no production admits it mid-line): where the two scalar
    WALKS stop with no validator consulted at all.  A plain scalar absorbs
    every `ns-plain-safe-out` character it meets, so what it stops at is either
    `NodeTail` or this; a block scalar's line collection is the same walk. -/
def OffLine (c : Char) : Prop := isPrintableBool c = false ∨ c = '﻿'

/-- What a complete block-context node's line may stop at: the two families
    above, and nothing else.  A UNION, not a projection — the `NodeTail`
    producers keep their own sharper conclusion and weaken here (item 37). -/
def NodeStop (c : Char) : Prop := NodeTail c ∨ OffLine c

lemma TailSuffix.toNodeTail {c : Char} (h : TailSuffix c) : NodeTail c := Or.inl h

lemma NodeTail.toNodeStop {c : Char} (h : NodeTail c) : NodeStop c := Or.inl h

lemma OffLine.toNodeStop {c : Char} (h : OffLine c) : NodeStop c := Or.inr h

lemma NodeStop.toNoOpenHead {c : Char} (h : NodeStop c) : NoOpenHead c := by
  rcases h with (hts | rfl) | (hnp | rfl)
  · exact hts.toNoOpenHead
  · rintro (h | h) <;> exact absurd h (by decide)
  · rintro (rfl | rfl) <;> exact absurd hnp (by decide)
  · rintro (h | h) <;> exact absurd h (by decide)

/-- **What §7.5 refuses.**  A `-` and a `?` are printable, are not the BOM, are
    not breaks, and are neither `#` nor `:` — so no rung of the ladder admits
    them.  This is the whole content of item 37 at the character level. -/
lemma NodeStop.not_dash_or_question {c : Char} (h : NodeStop c)
    (hc : c = '-' ∨ c = '?') : False := by
  have hne : c ≠ '-' ∧ c ≠ '?' := by
    rcases h with ((hbr | hh) | hcol) | (hnp | hbom)
    · exact ⟨by rintro rfl; exact absurd hbr (by decide),
             by rintro rfl; exact absurd hbr (by decide)⟩
    · subst hh; exact ⟨by decide, by decide⟩
    · subst hcol; exact ⟨by decide, by decide⟩
    · exact ⟨by rintro rfl; exact absurd hnp (by decide),
             by rintro rfl; exact absurd hnp (by decide)⟩
    · subst hbom; exact ⟨by decide, by decide⟩
  rcases hc with rfl | rfl
  · exact hne.1 rfl
  · exact hne.2 rfl

/-- Item 10's predicate, as the specialization it now is. -/
abbrev LineNoOpen : List Char → Prop := LineStop NoOpenHead

/-- The tail of a `...`: `s-l-comments` and nothing else. -/
abbrev LineTailSuffix : List Char → Prop := LineStop TailSuffix

/-- §7.5's node tail: `s-l-comments` plus `[154]`/`[155]`'s `:`. -/
abbrev LineNodeTail : List Char → Prop := LineStop NodeTail

/-- The union a completed block-context node's park carries. -/
abbrev LineNodeStop : List Char → Prop := LineStop NodeStop

lemma LineTailSuffix.toLineNoOpen {l : List Char}
    (h : LineTailSuffix l) : LineNoOpen l :=
  h.mono (fun _ => TailSuffix.toNoOpenHead)

lemma LineNodeTail.toLineNodeStop {l : List Char}
    (h : LineNodeTail l) : LineNodeStop l :=
  h.mono (fun _ => NodeTail.toNodeStop)

lemma LineNodeStop.toLineNoOpen {l : List Char}
    (h : LineNodeStop l) : LineNoOpen l :=
  h.mono (fun _ => NodeStop.toNoOpenHead)

/-- The head of a `LineNoOpen` line is never a flow open. -/
lemma LineNoOpen.not_open_head {c : Char} {rest : List Char}
    (h : LineNoOpen (c :: rest)) (hc : c = '[' ∨ c = '{') : False := by
  cases h with
  | stop _ _ hno => exact hno hc
  | white hw _ => cases hc <;> cases hw <;> simp_all

/-- The refutation: a `LineNoOpen` position cannot reach a `[`/`{` across
    whites alone.  `hhead` is the dispatched char read back through the
    correspondence. -/
lemma LineNoOpen.no_open_across_whites {sp sp' : SurfPos} {c : Char}
    (h : LineNoOpen sp.chars) (hws : GStar SSWhite sp sp')
    (hhead : sp'.chars.head? = some c) (hc : c = '[' ∨ c = '{') : False :=
  h.across_whites hws hhead (by rintro (rfl | rfl) <;> cases hc <;> simp_all) hc

/-- **The `...` refutation** (item 36): after a document-end marker, a
    same-line step that crossed only `s-white` reaches a break or a `#`.  Any
    other dispatched character — every block indicator, every content head —
    contradicts `[204]`'s own suffix check. -/
lemma LineTailSuffix.no_content_across_whites {sp sp' : SurfPos} {c : Char}
    (h : LineTailSuffix sp.chars) (hws : GStar SSWhite sp sp')
    (hhead : sp'.chars.head? = some c)
    (hnw : ¬(c = ' ' ∨ c = '\t'))
    (hnb : isLineBreakBool c = false) (hnc : c ≠ '#') : False := by
  rcases h.across_whites hws hhead hnw with hbr | hhash
  · rw [hnb] at hbr; cases hbr
  · exact hnc hhash

/-- **The §7.5 refutation** (item 37): after a complete block-context node, a
    same-line step that crossed only `s-white` cannot dispatch a `-` or a `?`.
    The `:` is NOT refuted and must not be: it is `[154]`'s implicit key, the
    one same-line continuation the productions admit. -/
lemma LineNodeStop.no_indicator_across_whites {sp sp' : SurfPos} {c : Char}
    (h : LineNodeStop sp.chars) (hws : GStar SSWhite sp sp')
    (hhead : sp'.chars.head? = some c) (hc : c = '-' ∨ c = '?') : False :=
  NodeStop.not_dash_or_question
    (h.across_whites hws hhead
      (by rcases hc with rfl | rfl <;> rintro (h | h) <;> exact absurd h (by decide)))
    hc

/-! ## §2 The scanner-side reading and its bridges -/

/-- Scanner-side `LineStop`, quantified over the character suffix so
    producers reason with `peek?`/`advance` only. -/
def RestStop (P : Char → Prop) (s : ScannerState) : Prop :=
  ∀ l, CharsFromOffset s.input s.offset l → LineStop P l

abbrev RestNoOpen (s : ScannerState) : Prop := RestStop NoOpenHead s
abbrev RestTailSuffix (s : ScannerState) : Prop := RestStop TailSuffix s
abbrev RestNodeTail (s : ScannerState) : Prop := RestStop NodeTail s
abbrev RestNodeStop (s : ScannerState) : Prop := RestStop NodeStop s

/-- The projection, scanner side. -/
lemma RestStop.mono {P Q : Char → Prop} (hPQ : ∀ c, P c → Q c) {s : ScannerState}
    (h : RestStop P s) : RestStop Q s := fun l hl => (h l hl).mono hPQ

/-- Read the fact through the correspondence. -/
lemma RestStop.to_surface {P : Char → Prop} {s : ScannerState} {sp : SurfPos}
    (h : RestStop P s) (hcorr : ScannerSurfCorr s sp) : LineStop P sp.chars :=
  h _ hcorr.chars_from

/-- The two-disjunct form the pending state carries, read through the
    correspondence. -/
lemma col0_or_lineStop {P : Char → Prop} {s' : ScannerState} {sp : SurfPos}
    (h : s'.col = 0 ∨ RestStop P s') (hcorr : ScannerSurfCorr s' sp) :
    sp.col = 0 ∨ LineStop P sp.chars :=
  h.imp (fun h0 => hcorr.col_eq.trans h0) (fun hr => hr.to_surface hcorr)

lemma col0_or_lineNoOpen {s' : ScannerState} {sp : SurfPos}
    (h : s'.col = 0 ∨ RestNoOpen s') (hcorr : ScannerSurfCorr s' sp) :
    sp.col = 0 ∨ LineNoOpen sp.chars := col0_or_lineStop h hcorr

/-- Token emission and record updates leave the cursor alone. -/
lemma RestStop.congr {P : Char → Prop} {s s' : ScannerState}
    (hi : s'.input = s.input) (ho : s'.offset = s.offset)
    (h : RestStop P s) : RestStop P s' := by
  intro l hl
  rw [hi, ho] at hl
  exact h l hl

/-- A state whose `peek?` is `none` or a non-white head in `P` is
    `RestStop P` with an empty white prefix. -/
lemma restStop_of_peek_stop {P : Char → Prop} {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (h : ∀ c, s.peek? = some c → ¬(c = ' ' ∨ c = '\t') ∧ P c) :
    RestStop P s := by
  intro l hl
  cases hl with
  | at_end _ _ => exact .nil
  | cons p hlt c rest hc hrest =>
    have hpk : s.peek? = some c := by
      unfold ScannerState.peek?
      rw [ite_eq_left (by omega : s.offset < s.inputEnd)]
      exact congrArg some hc
    obtain ⟨h1, h2⟩ := h c hpk
    exact .stop _ h1 h2

lemma restNoOpen_of_peek_stop {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (h : ∀ c, s.peek? = some c → ¬(c = ' ' ∨ c = '\t') ∧ ¬(c = '[' ∨ c = '{')) :
    RestNoOpen s := restStop_of_peek_stop hend h

/-- A state at column 0 or end of input (the block-scalar endings). -/
lemma restStop_of_at_end {P : Char → Prop} {s : ScannerState}
    (h : s.offset ≥ s.inputEnd) (hend : s.inputEnd = s.input.utf8ByteSize) :
    RestStop P s := by
  intro l hl
  cases hl with
  | at_end _ _ => exact .nil
  | cons p hlt _ _ _ _ => omega

lemma restNoOpen_of_at_end {s : ScannerState}
    (h : s.offset ≥ s.inputEnd) (hend : s.inputEnd = s.input.utf8ByteSize) :
    RestNoOpen s := restStop_of_at_end h hend

/-- A peeked char is the surface head. -/
lemma head_of_peek {s : ScannerState} {sp : SurfPos} {c : Char}
    (hcorr : ScannerSurfCorr s sp) (hpk : s.peek? = some c) :
    sp.chars.head? = some c := by
  have hlt : s.offset < s.inputEnd := by
    unfold ScannerState.peek? at hpk
    by_cases h : s.offset < s.inputEnd
    · exact h
    · rw [ite_eq_right h] at hpk; cases hpk
  have hget : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
    unfold ScannerState.peek? at hpk
    rw [ite_eq_left hlt] at hpk
    exact Option.some.inj hpk
  have hcf := hcorr.chars_from
  have hend := hcorr.end_eq
  generalize hch : sp.chars = l at hcf ⊢
  cases hcf with
  | at_end _ h => rw [hend] at hlt; omega
  | cons p h c' rest hc hrest =>
    exact congrArg some (hc.symm.trans hget)

/-! ## §3 The shared white-skip core

`skipTrailingSpaces` (and its clone `skipDocEndWhitespace`) advance through
`s-white` only; if the landing `peek?` is acceptable, the whole window is
`RestNoOpen`.  Fuel adequacy: each step consumes at least one byte. -/

/-- `peek? = some c` exposes the `CharsFromOffset` head. -/
private lemma peek_some_head {s : ScannerState} {c : Char}
    (_hend : s.inputEnd = s.input.utf8ByteSize)
    (hpk : s.peek? = some c) :
    s.offset < s.inputEnd ∧ String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
  unfold ScannerState.peek? at hpk
  by_cases hlt : s.offset < s.inputEnd
  · rw [ite_eq_left hlt] at hpk
    exact ⟨hlt, Option.some.inj hpk⟩
  · rw [ite_eq_right hlt] at hpk
    cases hpk

private lemma skipTrailingSpaces_step_white {s : ScannerState} {c : Char} {fuel' : Nat}
    (hpk : s.peek? = some c) (hw : (c == ' ' || c == '\t') = true) :
    skipTrailingSpaces s (fuel' + 1) = skipTrailingSpaces s.advance fuel' := by
  have hstep : skipTrailingSpaces s (fuel' + 1) =
      (match s.peek? with
        | some c => if c == ' ' || c == '\t' then skipTrailingSpaces s.advance fuel' else s
        | none => s) := rfl
  rw [hstep, hpk]
  exact ite_eq_left hw

private lemma skipTrailingSpaces_step_stop {s : ScannerState} {c : Char} {fuel' : Nat}
    (hpk : s.peek? = some c) (hw : ¬(c == ' ' || c == '\t') = true) :
    skipTrailingSpaces s (fuel' + 1) = s := by
  have hstep : skipTrailingSpaces s (fuel' + 1) =
      (match s.peek? with
        | some c => if c == ' ' || c == '\t' then skipTrailingSpaces s.advance fuel' else s
        | none => s) := rfl
  rw [hstep, hpk]
  exact ite_eq_right hw

private lemma skipDocEndWhitespace_step_white {s : ScannerState} {c : Char} {fuel' : Nat}
    (hpk : s.peek? = some c) (hw : (c == ' ' || c == '\t') = true) :
    skipDocEndWhitespace s (fuel' + 1) = skipDocEndWhitespace s.advance fuel' := by
  have hstep : skipDocEndWhitespace s (fuel' + 1) =
      (match s.peek? with
        | some c => if c == ' ' || c == '\t' then skipDocEndWhitespace s.advance fuel' else s
        | none => s) := rfl
  rw [hstep, hpk]
  exact ite_eq_left hw

private lemma skipDocEndWhitespace_step_stop {s : ScannerState} {c : Char} {fuel' : Nat}
    (hpk : s.peek? = some c) (hw : ¬(c == ' ' || c == '\t') = true) :
    skipDocEndWhitespace s (fuel' + 1) = s := by
  have hstep : skipDocEndWhitespace s (fuel' + 1) =
      (match s.peek? with
        | some c => if c == ' ' || c == '\t' then skipDocEndWhitespace s.advance fuel' else s
        | none => s) := rfl
  rw [hstep, hpk]
  exact ite_eq_right hw

lemma restStop_of_skipTrailingSpaces {P : Char → Prop} (fuel : Nat) :
    ∀ (s : ScannerState),
    s.inputEnd = s.input.utf8ByteSize →
    (∀ c, (skipTrailingSpaces s fuel).peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ P c) →
    RestStop P s := by
  induction fuel with
  | zero => intro s hend hstop; exact restStop_of_peek_stop hend hstop
  | succ fuel' ih =>
    intro s hend hstop
    cases hpk : s.peek? with
    | none =>
      exact restStop_of_peek_stop hend (fun c hc => by rw [hc] at hpk; cases hpk)
    | some c =>
      obtain ⟨hlt, hget⟩ := peek_some_head hend hpk
      by_cases hw : (c == ' ' || c == '\t') = true
      · rw [skipTrailingSpaces_step_white hpk hw] at hstop
        have hadv : RestStop P s.advance := by
          refine ih s.advance ?_ hstop
          rw [advance_inputEnd, advance_input]; exact hend
        intro l hl
        cases hl with
        | at_end _ _ => omega
        | cons p hplt c' rest hc' hrest =>
          have hce : c' = c := by rw [← hget, ← hc']
          subst hce
          refine LineStop.white (by
            simp only [Bool.or_eq_true, beq_iff_eq] at hw
            exact hw) ?_
          refine hadv rest ?_
          rw [advance_input, advance_offset_eq s hlt]
          exact hrest
      · rw [skipTrailingSpaces_step_stop hpk hw] at hstop
        exact restStop_of_peek_stop hend (fun c' hc' => hstop c' hc')

lemma restNoOpen_of_skipTrailingSpaces (fuel : Nat) :
    ∀ (s : ScannerState),
    s.inputEnd = s.input.utf8ByteSize →
    (∀ c, (skipTrailingSpaces s fuel).peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ ¬(c = '[' ∨ c = '{')) →
    RestNoOpen s := restStop_of_skipTrailingSpaces fuel

/-- The `skipDocEndWhitespace` clone of the same walk. -/
lemma restStop_of_skipDocEndWhitespace {P : Char → Prop} (fuel : Nat) :
    ∀ (s : ScannerState),
    s.inputEnd = s.input.utf8ByteSize →
    (∀ c, (skipDocEndWhitespace s fuel).peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ P c) →
    RestStop P s := by
  induction fuel with
  | zero => intro s hend hstop; exact restStop_of_peek_stop hend hstop
  | succ fuel' ih =>
    intro s hend hstop
    cases hpk : s.peek? with
    | none =>
      exact restStop_of_peek_stop hend (fun c hc => by rw [hc] at hpk; cases hpk)
    | some c =>
      obtain ⟨hlt, hget⟩ := peek_some_head hend hpk
      by_cases hw : (c == ' ' || c == '\t') = true
      · rw [skipDocEndWhitespace_step_white hpk hw] at hstop
        have hadv : RestStop P s.advance := by
          refine ih s.advance ?_ hstop
          rw [advance_inputEnd, advance_input]; exact hend
        intro l hl
        cases hl with
        | at_end _ _ => omega
        | cons p hplt c' rest hc' hrest =>
          have hce : c' = c := by rw [← hget, ← hc']
          subst hce
          refine LineStop.white (by
            simp only [Bool.or_eq_true, beq_iff_eq] at hw
            exact hw) ?_
          refine hadv rest ?_
          rw [advance_input, advance_offset_eq s hlt]
          exact hrest
      · rw [skipDocEndWhitespace_step_stop hpk hw] at hstop
        exact restStop_of_peek_stop hend (fun c' hc' => hstop c' hc')

lemma restNoOpen_of_skipDocEndWhitespace (fuel : Nat) :
    ∀ (s : ScannerState),
    s.inputEnd = s.input.utf8ByteSize →
    (∀ c, (skipDocEndWhitespace s fuel).peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ ¬(c = '[' ∨ c = '{')) →
    RestNoOpen s := restStop_of_skipDocEndWhitespace fuel

/-! ## §4 Validator producers -/

/-- **The allowlist IS `NodeTail`** (item 37): `validateTrailingContent`'s
    three-way test is `[79] s-l-comments` plus `[154]`/`[155]`'s `:`, which is
    the set the production names.  Item 10 wrote the projection here — its
    consumer's `¬(c = '[' ∨ c = '{')` — and that is what made the residue's
    `-`/`?` unanswerable four sites later. -/
lemma stop_of_allowlist {c : Char}
    (h : isLineBreakBool c || c == '#' || c == ':') :
    ¬(c = ' ' ∨ c = '\t') ∧ NodeTail c := by
  simp only [Bool.or_eq_true, beq_iff_eq, isLineBreakBool,
    isLineFeedBool, isCarriageReturnBool] at h
  refine ⟨by rintro (rfl | rfl) <;> simp_all, ?_⟩
  rcases h with (hbr | rfl) | rfl
  · exact Or.inl (Or.inl (by rcases hbr with rfl | rfl <;> decide))
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr rfl

/-- §7.5: a passed `validateTrailingContent` leaves the rest of the line at
    `NodeTail` — a break, a `#`, or the `:` of an implicit key. -/
lemma restNodeTail_of_validateTrailingContent {s : ScannerState} {k : Nat}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : validateTrailingContent s k = .ok ()) :
    RestNodeTail s := by
  unfold validateTrailingContent at hok
  simp only [pure, Except.pure] at hok
  refine restStop_of_skipTrailingSpaces (k - s.offset + 1) s hend
    (fun c hc => ?_)
  split at hok
  · rename_i hnone
    rw [hc] at hnone; cases hnone
  · rename_i c' hsome
    rw [hc] at hsome
    injection hsome with hce
    subst hce
    split at hok
    · rename_i hallow
      exact stop_of_allowlist hallow
    · simp at hok

/-- [137]/[140]: a passed `validateFlowClose` at flow level 0 — the same five
    lines of code, and so the same set. -/
lemma restNodeTail_of_validateFlowClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hfl : s.flowLevel = 0)
    (hok : validateFlowClose s = .ok ()) :
    RestNodeTail s := by
  unfold validateFlowClose at hok
  rw [ite_eq_left (by simp [hfl])] at hok
  simp only [pure, Except.pure] at hok
  refine restStop_of_skipTrailingSpaces (s.inputEnd - s.offset + 1) s hend
    (fun c hc => ?_)
  split at hok
  · rename_i hnone
    rw [hc] at hnone; cases hnone
  · rename_i c' hsome
    rw [hc] at hsome
    injection hsome with hce
    subst hce
    split at hok
    · rename_i hallow
      exact stop_of_allowlist hallow
    · simp at hok

/-- [104] (item 9h): a passed `validateAliasClose` in block context — it IS
    `validateTrailingContent`, one `if` down. -/
lemma restNodeTail_of_validateAliasClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hflow : s.inFlow = false)
    (hok : validateAliasClose s = .ok ()) :
    RestNodeTail s := by
  unfold validateAliasClose at hok
  rw [ite_eq_right (by simp [hflow])] at hok
  exact restNodeTail_of_validateTrailingContent hend hok

/-! Item 10's conclusions, each one `mono` off the rung above.  Every consumer
that only ever asked about a flow open is unchanged. -/

lemma restNoOpen_of_validateTrailingContent {s : ScannerState} {k : Nat}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : validateTrailingContent s k = .ok ()) :
    RestNoOpen s :=
  (restNodeTail_of_validateTrailingContent hend hok).mono (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

lemma restNoOpen_of_validateFlowClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hfl : s.flowLevel = 0)
    (hok : validateFlowClose s = .ok ()) :
    RestNoOpen s :=
  (restNodeTail_of_validateFlowClose hend hfl hok).mono (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

lemma restNoOpen_of_validateAliasClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hflow : s.inFlow = false)
    (hok : validateAliasClose s = .ok ()) :
    RestNoOpen s :=
  (restNodeTail_of_validateAliasClose hend hflow hok).mono (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

/-- The flow-close producer at the union the park carries. -/
lemma restNodeStop_of_validateFlowClose {s : ScannerState}
    (hend : s.inputEnd = s.input.utf8ByteSize)
    (hfl : s.flowLevel = 0)
    (hok : validateFlowClose s = .ok ()) :
    RestNodeStop s :=
  (restNodeTail_of_validateFlowClose hend hfl hok).mono (fun _ => NodeTail.toNodeStop)

/-! ## §5 Scan-level producers: the quoted scalars and `...`

No loop analysis is needed: each validator ran on the very state the scan
returns (modulo token emission), and if its white-skip had exhausted fuel
mid-whites the landing peek would be a white — outside every allowlist — so
`.ok` itself rules that out.  The `hend'` inputs come from the call sites'
`ScannerSurfCorr` (its `end_eq` field). -/

lemma scanDoubleQuoted_restNodeTail {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanDoubleQuoted s = .ok s') :
    RestNodeTail s' := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i ev heq_loop
    obtain ⟨content, s_after_close⟩ := ev
    split at hok
    · split at hok
      · cases hok
      · rename_i u hval
        cases u
        injection hok with h_eq
        subst h_eq
        exact (restNodeTail_of_validateTrailingContent (s := s_after_close)
          hend' hval).congr rfl rfl
    · rename_i hnflow
      rw [hflow] at hnflow
      simp at hnflow

lemma scanSingleQuoted_restNodeTail {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanSingleQuoted s = .ok s') :
    RestNodeTail s' := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i ev heq_loop
    obtain ⟨content, s_after_close⟩ := ev
    split at hok
    · split at hok
      · cases hok
      · rename_i u hval
        cases u
        injection hok with h_eq
        subst h_eq
        exact (restNodeTail_of_validateTrailingContent (s := s_after_close)
          hend' hval).congr rfl rfl
    · rename_i hnflow
      rw [hflow] at hnflow
      simp at hnflow

/-! Item 10's two quoted conclusions, each one `mono` off the rung above. -/

lemma scanDoubleQuoted_restNoOpen {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanDoubleQuoted s = .ok s') :
    RestNoOpen s' :=
  (scanDoubleQuoted_restNodeTail hflow hend' hok).mono
    (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

lemma scanSingleQuoted_restNoOpen {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanSingleQuoted s = .ok s') :
    RestNoOpen s' :=
  (scanSingleQuoted_restNodeTail hflow hend' hok).mono
    (fun _ => NodeStop.toNoOpenHead ∘ NodeTail.toNodeStop)

/-- **[204] `l-document-suffix ::= c-document-end s-l-comments`** — the
    marker's own tail, at its own strength (item 36).  `scanDocumentEnd`'s
    suffix probe validated the returned state's window (the probe starts at
    `result.offset`) and admitted exactly `s-l-comments`: a break, a `#`, or
    end of input.  Nothing about a `[` here — the flow-open reading below is
    one `mono` away, and every OTHER character is refuted too, which is what a
    `...` parked mid-line owes the block dispatch. -/
lemma scanDocumentEnd_restTailSuffix {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanDocumentEnd s = .ok s') :
    RestTailSuffix s' := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · -- the suffix-probe match; each surviving arm pins the landing peek
    split at hok
    · -- peek = none
      rename_i hpk
      have h_eq := Except.ok.inj hok
      rw [h_eq] at hpk
      apply restStop_of_skipDocEndWhitespace _ s' hend'
      intro c hc
      rw [hc] at hpk
      cases hpk
    · -- peek = some '#'
      rename_i hpk
      have h_eq := Except.ok.inj hok
      rw [h_eq] at hpk
      apply restStop_of_skipDocEndWhitespace _ s' hend'
      intro c hc
      rw [hc] at hpk
      injection hpk with hce
      subst hce
      exact ⟨by decide, Or.inr rfl⟩
    · -- peek = some c, break required
      rename_i c₀ hne1 hne2 hpk
      split at hok
      · rename_i hbr
        have h_eq := Except.ok.inj hok
        rw [h_eq] at hpk
        apply restStop_of_skipDocEndWhitespace _ s' hend'
        intro c hc
        rw [hc] at hpk
        injection hpk with hce
        subst hce
        refine ⟨?_, Or.inl hbr⟩
        simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
          Bool.or_eq_true, beq_iff_eq] at hbr
        rintro (rfl | rfl) <;> simp_all
      · cases hok

/-- [204] read at item 10's strength: one `mono`, at the consumer. -/
lemma scanDocumentEnd_restNoOpen {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanDocumentEnd s = .ok s') :
    RestNoOpen s' :=
  (scanDocumentEnd_restTailSuffix hend' hok).mono (fun _ => TailSuffix.toNoOpenHead)


/-! ## §6 Offset/inputEnd walk facts for the two scalar loops -/

private lemma consumeNewline_fields (s : ScannerState) :
    s.offset ≤ (consumeNewline s).offset ∧ (consumeNewline s).inputEnd = s.inputEnd := by
  unfold consumeNewline
  split
  · exact ⟨advance_offset_ge s, advance_inputEnd s⟩
  · dsimp only []
    split
    · refine ⟨?_, advance_inputEnd s⟩
      show s.offset ≤ (String.Pos.Raw.next s.advance.input ⟨s.advance.offset⟩).byteIdx
      have h1 := advance_offset_ge s
      rw [next_byteIdx]
      have := Char.utf8Size_pos (String.Pos.Raw.get s.advance.input ⟨s.advance.offset⟩)
      omega
    · exact ⟨advance_offset_ge s, advance_inputEnd s⟩
  · exact ⟨Nat.le_refl _, rfl⟩

private lemma peek_some_lt {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) : s.offset < s.inputEnd := by
  unfold ScannerState.peek? at hpk
  by_cases h : s.offset < s.inputEnd
  · exact h
  · rw [ite_eq_right h] at hpk; cases hpk

private lemma peek_some_get {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
  unfold ScannerState.peek? at hpk
  rw [ite_eq_left (peek_some_lt hpk)] at hpk
  exact Option.some.inj hpk

private lemma consumeNewline_offset_gt {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true) :
    s.offset < (consumeNewline s).offset := by
  have hlt : s.offset < s.inputEnd := peek_some_lt hpk
  unfold consumeNewline
  rw [hpk]
  split
  · exact advance_offset_lt s hlt
  · dsimp only []
    split
    · show s.offset < (String.Pos.Raw.next s.advance.input ⟨s.advance.offset⟩).byteIdx
      have h1 := advance_offset_lt s hlt
      rw [next_byteIdx]
      have := Char.utf8Size_pos (String.Pos.Raw.get s.advance.input ⟨s.advance.offset⟩)
      omega
    · exact advance_offset_lt s hlt
  · rename_i hne1 hne2
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
      Bool.or_eq_true, beq_iff_eq] at hbr
    rcases hbr with rfl | rfl <;> simp_all

private lemma consumeNewline_col0 {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true) :
    (consumeNewline s).col = 0 := by
  have hlt : s.offset < s.inputEnd := peek_some_lt hpk
  have hget := peek_some_get hpk
  unfold consumeNewline
  rw [hpk]
  split
  · rename_i heq
    injection heq with hc'
    subst hc'
    exact advance_col_newline s hlt (by rw [hget]; rfl)
  · rename_i heq
    injection heq with hc'
    subst hc'
    have hcol0 : s.advance.col = 0 := advance_col_cr s hlt (by rw [hget]; rfl)
    dsimp only []
    split
    all_goals exact hcol0
  · rename_i hne1 hne2
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
      Bool.or_eq_true, beq_iff_eq] at hbr
    rcases hbr with rfl | rfl <;> simp_all

private lemma skipWhitespaceLoop_fields (fuel : Nat) : ∀ (s : ScannerState),
    s.offset ≤ (skipWhitespaceLoop s fuel).offset ∧
    (skipWhitespaceLoop s fuel).inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s; unfold skipWhitespaceLoop; exact ⟨Nat.le_refl _, rfl⟩
  | succ fuel' ih =>
    intro s
    unfold skipWhitespaceLoop
    split
    · split
      · obtain ⟨h1, h2⟩ := ih s.advance
        exact ⟨Nat.le_trans (advance_offset_ge s) h1, h2.trans (advance_inputEnd s)⟩
      · exact ⟨Nat.le_refl _, rfl⟩
    · exact ⟨Nat.le_refl _, rfl⟩

private lemma skipWhitespace_fields (s : ScannerState) :
    s.offset ≤ (skipWhitespace s).offset ∧ (skipWhitespace s).inputEnd = s.inputEnd :=
  skipWhitespaceLoop_fields _ s

private lemma skipSpacesLoop_fields (fuel : Nat) : ∀ (s : ScannerState),
    s.offset ≤ (skipSpacesLoop s fuel).offset ∧
    (skipSpacesLoop s fuel).inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s; unfold skipSpacesLoop; exact ⟨Nat.le_refl _, rfl⟩
  | succ fuel' ih =>
    intro s
    unfold skipSpacesLoop
    split
    · obtain ⟨h1, h2⟩ := ih s.advance
      exact ⟨Nat.le_trans (advance_offset_ge s) h1, h2.trans (advance_inputEnd s)⟩
    · exact ⟨Nat.le_refl _, rfl⟩

private lemma skipSpaces_fields (s : ScannerState) :
    s.offset ≤ (skipSpaces s).offset ∧ (skipSpaces s).inputEnd = s.inputEnd :=
  skipSpacesLoop_fields _ s

private lemma skipBlankLinesLoop_fields (fuel : Nat) : ∀ (s : ScannerState) (cnt inputEnd : Nat),
    s.offset ≤ (skipBlankLinesLoop s cnt fuel inputEnd).2.offset ∧
    (skipBlankLinesLoop s cnt fuel inputEnd).2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s cnt inputEnd; unfold skipBlankLinesLoop; exact ⟨Nat.le_refl _, rfl⟩
  | succ fuel' ih =>
    intro s cnt inputEnd
    unfold skipBlankLinesLoop
    dsimp only []
    split
    · split
      · -- item 100: the gate stops the run where it started
        split
        · exact ⟨Nat.le_refl _, rfl⟩
        · obtain ⟨h1, h2⟩ := ih (consumeNewline (skipWhitespace s)) (cnt + 1) inputEnd
          obtain ⟨hw1, hw2⟩ := skipWhitespace_fields s
          obtain ⟨hn1, hn2⟩ := consumeNewline_fields (skipWhitespace s)
          exact ⟨Nat.le_trans hw1 (Nat.le_trans hn1 h1),
                 h2.trans (hn2.trans hw2)⟩
      · exact ⟨Nat.le_refl _, rfl⟩
    · exact ⟨Nat.le_refl _, rfl⟩

/-- `collectPlainScalar_handleBlockLineBreak` starts with the break's
    `consumeNewline`, so a `some` result strictly advanced the offset. -/
private lemma handleBlockLineBreak_progress {s : ScannerState} {content : String}
    {ci ie : Nat} {content' : String} {s2 : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true)
    (h : collectPlainScalar_handleBlockLineBreak s content ci ie = some (content', s2)) :
    s.offset < s2.offset ∧ s2.inputEnd = s.inputEnd := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  simp only [] at h
  split at h
  · cases h
  · split at h
    · cases h
    · have hpair := Prod.mk.inj (Option.some.inj h)
      obtain ⟨-, h2⟩ := hpair
      subst h2
      have hgt := consumeNewline_offset_gt hpk hbr
      obtain ⟨hb1, hb2⟩ := skipBlankLinesLoop_fields (ie - (consumeNewline s).offset + 1)
        (consumeNewline s) 0 ie
      obtain ⟨hs1, hs2⟩ := skipSpaces_fields
        (skipBlankLinesLoop (consumeNewline s) 0 (ie - (consumeNewline s).offset + 1) ie).2
      obtain ⟨hw1, hw2⟩ := skipWhitespace_fields
        (skipSpaces (skipBlankLinesLoop (consumeNewline s) 0 (ie - (consumeNewline s).offset + 1) ie).2)
      have hn2 := (consumeNewline_fields s).2
      exact ⟨by omega, by omega⟩

/-! ## §7 The plain scalar: fuel adequacy, then the stop shape -/

/-- The `terminates?` probe stops the scan AT its own state, terminated, and
    only at `#`, `:` or a column-0 document boundary (block context).  The
    CONTENT is untouched (item 77, last so the older patterns still bind): a
    probe that fires reads the walk's accumulator back unchanged, which is what
    tells the caller's `result.content.length ≤ prevLen` test that nothing was
    added past the fold. -/
private lemma terminates?_inv {c : Char} {s : ScannerState}
    {content spaces : String} {r : PlainScalarResult}
    (h : collectPlainScalar_terminates? c s content spaces false = some r) :
    r.state = s ∧ r.terminated = true ∧ (c = '#' ∨ c = ':' ∨ s.col = 0) ∧
      r.content = content := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · rename_i hcond
    injection h with h; subst h
    refine ⟨rfl, rfl, Or.inl ?_, rfl⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.1
  · split at h
    · rename_i hcolon
      simp only [] at h
      split at h <;> split at h <;>
        first
          | (injection h with h; subst h;
             exact ⟨rfl, rfl, Or.inr (Or.inl (by simpa using hcolon)), rfl⟩)
          | cases h
    · split at h
      · rename_i hflow
        simp at hflow
      · split at h
        · rename_i hdoc
          injection h with h; subst h
          refine ⟨rfl, rfl, Or.inr (Or.inr ?_), rfl⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hdoc
          simpa using hdoc.1
        · cases h

/-- With more fuel than remaining bytes, the block-context plain-scalar walk
    always TERMINATES (never exits on fuel). -/
private lemma collectPlainScalarLoop_terminated (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    s.inputEnd - s.offset < fuel →
    r.terminated = true := by
  induction fuel with
  | zero => intro s _ _ _ _ r _ hb; omega
  | succ fuel' ih =>
    intro s content spaces ci ie r hok hb
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq; rfl
    · rename_i c hpk
      have hlt : s.offset < s.inputEnd := by
        unfold ScannerState.peek? at hpk
        by_cases h : s.offset < s.inputEnd
        · exact h
        · rw [ite_eq_right h] at hpk; cases hpk
      split at hok
      · rename_i hterm
        injection hok with h_eq; subst h_eq
        exact (terminates?_inv hterm).2.1
      · split at hok
        · -- break, block context
          rename_i hbr
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq; rfl
            · rename_i content' s2 hblk
              obtain ⟨hgt, hend2⟩ := handleBlockLineBreak_progress hpk hbr hblk
              split at hok
              · injection hok with h_eq; subst h_eq; rfl
              · dsimp only [] at hok
                generalize h_loop : collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq; rfl
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exact ih s2 content' "" ci ie _ h_loop (by omega)
                | error e => simp at hok
        · split at hok
          · -- whitespace: advance
            have hadv := advance_offset_lt s hlt
            have hend2 := advance_inputEnd s
            exact ih s.advance content _ ci ie r hok (by omega)
          · split at hok
            · injection hok with h_eq; subst h_eq; rfl
            · -- plain-safe content: advance
              simp only [] at hok
              have hadv := advance_offset_lt s hlt
              have hend2 := advance_inputEnd s
              exact ih s.advance _ "" ci ie r hok (by omega)

/-- `[128] ns-plain-safe-out` is `ns-char`, so what makes the walk stop
    without a validator is a character no production admits at all. -/
private lemma offLine_of_not_plainSafe {c : Char}
    (hnw : ¬(isWhiteSpaceBool c = true)) (hnb : ¬(isLineBreakBool c = true))
    (h : (!isPlainSafeBool c false) = true) : OffLine c := by
  have hw : isWhiteSpaceBool c = false := by simpa using hnw
  have hb : isLineBreakBool c = false := by simpa using hnb
  have hps : isPlainSafeBool c false = false := by simpa using h
  by_cases hbom : c = '﻿'
  · exact Or.inr hbom
  · refine Or.inl ?_
    by_cases hp : isPrintableBool c = true
    · rw [show isPlainSafeBool c false = true from by
        simp [isPlainSafeBool, hw, hb, hp, hbom]] at hps
      cases hps
    · simpa using hp

/-- A terminated block-context plain-scalar walk lands at column 0 or on a
    stop character — and the stop set is `NodeStop` exactly (item 37): the
    walk's own three exits are `#`, `:` and a break (`NodeTail`), plus a
    character outside `ns-plain-safe-out`, which is `OffLine`.  Every `-`, `?`
    and `[` is ABSORBED, which is why none of them can be here. -/
private lemma collectPlainScalarLoop_stop (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    r.terminated = true →
    r.state.col = 0 ∨ (∀ c, r.state.peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ NodeStop c) := by
  induction fuel with
  | zero =>
    intro s _ _ _ _ r hok hterm
    unfold collectPlainScalarLoop at hok
    injection hok with h_eq; subst h_eq
    cases hterm
  | succ fuel' ih =>
    intro s content spaces ci ie r hok hterm
    unfold collectPlainScalarLoop at hok
    split at hok
    · rename_i hpk
      injection hok with h_eq; subst h_eq
      exact Or.inr (fun c hc => by rw [hc] at hpk; cases hpk)
    · rename_i c hpk
      split at hok
      · rename_i hterm'
        obtain ⟨hst, -, hdisj, -⟩ := terminates?_inv hterm'
        injection hok with h_eq; subst h_eq
        rw [hst]
        rcases hdisj with rfl | rfl | hcol
        · exact Or.inr (fun c' hc' => by
            rw [hpk] at hc'
            injection hc' with hce
            subst hce
            exact ⟨by decide, Or.inl (Or.inl (Or.inr rfl))⟩)
        · exact Or.inr (fun c' hc' => by
            rw [hpk] at hc'
            injection hc' with hce
            subst hce
            exact ⟨by decide, Or.inl (Or.inr rfl)⟩)
        · exact Or.inl hcol
      · -- termination char classes below
        have hstop_break : isLineBreakBool c = true →
            (∀ c', s.peek? = some c' → ¬(c' = ' ' ∨ c' = '\t') ∧ NodeStop c') := by
          intro hbr c' hc'
          rw [hpk] at hc'
          injection hc' with hce
          subst hce
          refine ⟨?_, Or.inl (Or.inl (Or.inl hbr))⟩
          simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
            Bool.or_eq_true, beq_iff_eq] at hbr
          rintro (rfl | rfl) <;> simp_all
        split at hok
        · rename_i hbr
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact Or.inr (hstop_break hbr)
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq
                exact Or.inr (hstop_break hbr)
              · dsimp only [] at hok
                generalize h_loop : collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq
                    exact Or.inr (hstop_break hbr)
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exact ih s2 content' "" ci ie _ h_loop hterm
                | error e => simp at hok
        · split at hok
          · exact ih s.advance content _ ci ie r hok hterm
          · split at hok
            · rename_i hunsafe
              injection hok with h_eq; subst h_eq
              refine Or.inr (fun c' hc' => ?_)
              rw [hpk] at hc'
              injection hc' with hce
              subst hce
              rename_i hnbr hnws
              constructor
              · intro habs
                apply hnws
                simp only [isWhiteSpaceBool, isSpaceBool, isTabBool,
                  Bool.or_eq_true, beq_iff_eq]
                exact habs
              · exact Or.inr (offLine_of_not_plainSafe hnws hnbr hunsafe)
            · exact ih s.advance _ "" ci ie r hok hterm


/-! ### Item 77 — the walk's own column

`collectPlainScalarLoop_stop` leaves `r.state.col = 0` open because the
`terminates?` probe has a column-0 exit.  What the WALK says is that such an
exit never becomes the scan's answer: every stop that can sit at a line start
returns the walk's ENTRY state with the accumulator unchanged, and the fold's
`result.content.length ≤ prevLen` test then hands the break's own state back
instead.  So the loop's result is off column 0 whenever the loop moved at all,
and the dispatcher's guards say it moved. -/

/-- `advance` over a non-break spends a column. -/
private lemma advance_col_succ_of_peek {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false) :
    s.advance.col = s.col + 1 := by
  unfold ScannerState.peek? at hpk
  split at hpk
  · rename_i hlt
    have hc : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := Option.some.inj hpk
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnb
    exact advance_col_non_newline s hlt (by rw [hc]; simpa using hnb.1)
      (by rw [hc]; simpa using hnb.2)
  · cases hpk

/-- ... so it cannot land on one. -/
private lemma advance_col_pos_of_peek {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false) :
    0 < s.advance.col := by
  rw [advance_col_succ_of_peek hpk hnb]; omega

/-- **The walk moves or stays put** (item 77).  A block-context plain-scalar
    walk either ends off column 0 or returns exactly what it was handed — its
    own entry state and its own accumulator.  The three recursive branches all
    fall in the first case: the two `advance`s spend a column on a character
    that is not a break, and the fold's continuation survives its caller's
    length test only by ADDING content, which the second case forbids. -/
private lemma collectPlainScalarLoop_col_or_stuck (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    0 < r.state.col ∨ (r.state = s ∧ r.content = content) := by
  induction fuel with
  | zero =>
    intro s content spaces ci ie r hok
    unfold collectPlainScalarLoop at hok
    injection hok with h_eq; subst h_eq
    exact Or.inr ⟨rfl, rfl⟩
  | succ fuel' ih =>
    intro s content spaces ci ie r hok
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq
      exact Or.inr ⟨rfl, rfl⟩
    · rename_i c hpk
      split at hok
      · rename_i hterm'
        injection hok with h_eq; subst h_eq
        obtain ⟨hst, -, -, hcont⟩ := terminates?_inv hterm'
        exact Or.inr ⟨hst, hcont⟩
      · split at hok
        · -- a break, block context
          rename_i hbr
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact Or.inr ⟨rfl, rfl⟩
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq
                exact Or.inr ⟨rfl, rfl⟩
              · dsimp only [] at hok
                generalize h_loop : collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq
                    exact Or.inr ⟨rfl, rfl⟩
                  · rename_i hgrew
                    have h_eq := Except.ok.inj hok; subst h_eq
                    rcases ih s2 content' "" ci ie _ h_loop with h | ⟨-, hcont⟩
                    · exact Or.inl h
                    · exact absurd (Nat.le_of_eq (congrArg String.length hcont)) hgrew
                | error e => simp at hok
        · rename_i hbr
          have hnb : isLineBreakBool c = false := by simpa using hbr
          split at hok
          · rcases ih s.advance content _ ci ie r hok with h | ⟨hst, -⟩
            · exact Or.inl h
            · exact Or.inl (hst ▸ advance_col_pos_of_peek hpk hnb)
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact Or.inr ⟨rfl, rfl⟩
            · rcases ih s.advance _ "" ci ie r hok with h | ⟨hst, -⟩
              · exact Or.inl h
              · exact Or.inl (hst ▸ advance_col_pos_of_peek hpk hnb)

/-- `[126] ns-plain-first(c)` is inside `[128] ns-plain-safe-out`: a character
    that may START a block-context plain scalar may also CONTINUE one. -/
private lemma plainSafe_of_canStart {c : Char} {next : Option Char}
    (h : canStartPlainScalarBool c next false = true) :
    isPlainSafeBool c false = true := by
  show (!isWhiteSpaceBool c && !isLineBreakBool c && isPrintableBool c && c != '﻿') = true
  unfold canStartPlainScalarBool at h
  split at h
  · rename_i hind
    rcases hind with rfl | rfl | rfl <;> rfl
  · simp only [Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- `[126]`'s `-`/`?`/`:` arm names the FOLLOWER — not blank, printable, not the
    BOM — which is the exact negation of `terminates?`'s `:` test in block
    context.  This is why `:b` reaches the plain walk and `: ` does not. -/
private lemma colon_follower_not_terminating {s : ScannerState}
    (hstart : canStartPlainScalarBool ':' (s.peekAt? 1) false = true) :
    ∃ n, s.peekAt? 1 = some n ∧ isBlankBool n = false ∧
      isPrintableBool n = true ∧ (n == '﻿') = false := by
  unfold canStartPlainScalarBool at hstart
  rw [ite_eq_left (Or.inr (Or.inr rfl))] at hstart
  revert hstart
  cases hnext : s.peekAt? 1 with
  | none => intro h; simp at h
  | some n =>
    intro h
    simp only [Bool.and_eq_true] at h
    refine ⟨n, rfl, ?_, h.1.2, ?_⟩
    · simp only [isBlankBool, Bool.or_eq_false_iff]
      exact ⟨by simpa using h.1.1.1.1, by simpa using h.1.1.1.2⟩
    · simpa using h.2

/-- The dispatcher's own guards refute the probe at the walk's FIRST character:
    the accumulator is empty so `#` cannot fire, `:` is routed here only with a
    non-blank follower, the flow arm is dead in block context, and the
    structural dispatch already took every column-0 document boundary. -/
private lemma terminates?_none_of_canStart {c : Char} {s : ScannerState}
    (hstart : canStartPlainScalarBool c (s.peekAt? 1) false = true)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false) :
    collectPlainScalar_terminates? c s "" "" false = none := by
  unfold collectPlainScalar_terminates?
  split
  · rename_i hhash
    simp at hhash
  · split
    · rename_i hcolon
      have hc : c = ':' := by simpa using hcolon
      subst hc
      obtain ⟨n, hn, hbl, hpr, hbom⟩ := colon_follower_not_terminating hstart
      simp only []
      rw [hn]
      simp [hbl, hpr, hbom]
    · split
      · rename_i hfl
        simp at hfl
      · split
        · rename_i hdoc
          simp only [Bool.and_eq_true, beq_iff_eq] at hdoc
          exact absurd (hnotdoc hdoc.1) (by simp [hdoc.2])
        · rfl

/-- **A routed block-context plain scalar parks off a line start** (item 77).
    This is the CONTENT park's own column: the block scalar re-arms the simple
    key at its column-0 park, and every other content scan — this one, the two
    quoted ones, the alias — ends on a character it consumed, so no block park
    that carries a down flag can sit at a line start. -/
lemma scanPlainScalar_col_pos {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hpk : s.peek? = some c)
    (hstart : canStartPlainScalarBool c (s.peekAt? 1) false = true)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false)
    (hok : scanPlainScalar s = .ok s') :
    0 < s'.col := by
  have hlt : s.offset < s.inputEnd := by
    unfold ScannerState.peek? at hpk
    by_cases h : s.offset < s.inputEnd
    · exact h
    · rw [ite_eq_right h] at hpk; cases hpk
  have hps : isPlainSafeBool c false = true := plainSafe_of_canStart hstart
  have hnb : isLineBreakBool c = false := by
    revert hps
    show (!isWhiteSpaceBool c && !isLineBreakBool c && isPrintableBool c && c != '﻿') = true →
      isLineBreakBool c = false
    intro h
    simp only [Bool.and_eq_true] at h
    simpa using h.1.1.2
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  rw [hflow] at hok
  split at hok
  · cases hok
  · rename_i result h_loop
    injection hok with h_eq
    subst h_eq
    show 0 < result.state.col
    -- Peel the walk's first step: the guards above forbid every exit that could
    -- stop at `s`, so the loop advances and the invariant above applies.
    obtain ⟨fuel', hfuel⟩ : ∃ fuel', (s.inputEnd - s.offset + 1) * 2 = fuel' + 1 :=
      ⟨(s.inputEnd - s.offset + 1) * 2 - 1, by omega⟩
    rw [hfuel] at h_loop
    unfold collectPlainScalarLoop at h_loop
    split at h_loop
    · rename_i hnone
      rw [hnone] at hpk; cases hpk
    · rename_i c' hpk'
      rw [hpk] at hpk'
      obtain rfl : c' = c := (Option.some.inj hpk').symm
      split at h_loop
      · rename_i hterm
        rw [terminates?_none_of_canStart hstart hnotdoc] at hterm
        cases hterm
      · split at h_loop
        · rename_i hbr
          rw [hnb] at hbr
          cases hbr
        · split at h_loop
          · rcases collectPlainScalarLoop_col_or_stuck fuel' s.advance "" _ _ s.inputEnd result
              h_loop with h | ⟨hst, -⟩
            · exact h
            · exact hst ▸ advance_col_pos_of_peek hpk hnb
          · split at h_loop
            · rename_i hunsafe
              rw [hps] at hunsafe
              simp at hunsafe
            · rcases collectPlainScalarLoop_col_or_stuck fuel' s.advance _ "" _ s.inputEnd result
                h_loop with h | ⟨hst, -⟩
              · exact h
              · exact hst ▸ advance_col_pos_of_peek hpk hnb

/-- `scanPlainScalar` in block context: the emitted state sits at column 0 or
    on a `NodeStop` character.  (`hend'` from the caller's corr.) -/
lemma scanPlainScalar_restNodeStop {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanPlainScalar s = .ok s') :
    s'.col = 0 ∨ RestNodeStop s' := by
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  rw [hflow] at hok
  split at hok
  · cases hok
  · rename_i result h_loop
    injection hok with h_eq
    subst h_eq
    have hterm := collectPlainScalarLoop_terminated _ s "" "" _ s.inputEnd result h_loop
      (by omega)
    have hstop := collectPlainScalarLoop_stop _ s "" "" _ s.inputEnd result h_loop hterm
    cases hstop with
    | inl hcol => exact Or.inl hcol
    | inr hpk =>
      refine Or.inr ((restStop_of_peek_stop (s := result.state) hend' ?_).congr rfl rfl)
      exact hpk

lemma scanPlainScalar_restNoOpen {s s' : ScannerState}
    (hflow : s.inFlow = false)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanPlainScalar s = .ok s') :
    s'.col = 0 ∨ RestNoOpen s' :=
  (scanPlainScalar_restNodeStop hflow hend' hok).imp id
    (RestStop.mono (fun _ => NodeStop.toNoOpenHead))

/-! ## §8 The block scalar: every ending is a column-0 line, EOF, or a
non-printable stop -/

private lemma consumeExactSpaces_fields (count : Nat) : ∀ (s : ScannerState),
    s.offset ≤ (consumeExactSpaces s count).2.offset ∧
    (consumeExactSpaces s count).2.inputEnd = s.inputEnd := by
  induction count with
  | zero => intro s; unfold consumeExactSpaces; exact ⟨Nat.le_refl _, rfl⟩
  | succ count' ih =>
    intro s
    unfold consumeExactSpaces
    split
    · obtain ⟨h1, h2⟩ := ih s.advance
      exact ⟨Nat.le_trans (advance_offset_ge s) h1, h2.trans (advance_inputEnd s)⟩
    · exact ⟨Nat.le_refl _, rfl⟩

private lemma collectLineContentLoop_fields (fuel : Nat) : ∀ (s : ScannerState) (content : String),
    s.offset ≤ (collectLineContentLoop s content fuel).2.offset ∧
    (collectLineContentLoop s content fuel).2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s content; unfold collectLineContentLoop; exact ⟨Nat.le_refl _, rfl⟩
  | succ fuel' ih =>
    intro s content
    unfold collectLineContentLoop
    split
    · split
      · exact ⟨Nat.le_refl _, rfl⟩
      · obtain ⟨h1, h2⟩ := ih s.advance (content.push _)
        exact ⟨Nat.le_trans (advance_offset_ge s) h1, h2.trans (advance_inputEnd s)⟩
    · exact ⟨Nat.le_refl _, rfl⟩

/-- With adequate fuel, `collectLineContentLoop` stops at EOF, a break, a
    non-printable, or the BOM — never on a white or a bracket. -/
private lemma collectLineContentLoop_stop (fuel : Nat) : ∀ (s : ScannerState) (content : String),
    s.inputEnd - s.offset < fuel →
    ∀ c, (collectLineContentLoop s content fuel).2.peek? = some c →
      isLineBreakBool c = true ∨ isPrintableBool c = false ∨ c = '﻿' := by
  induction fuel with
  | zero => intro s _ hb; omega
  | succ fuel' ih =>
    intro s content hb c hc
    unfold collectLineContentLoop at hc
    split at hc
    · rename_i c₀ hpk
      split at hc
      · rename_i hstopc
        rw [hpk] at hc
        injection hc with hce
        subst hce
        exact or_assoc.mp (by simpa using hstopc)
      · rename_i hcont
        have hlt : s.offset < s.inputEnd := by
          unfold ScannerState.peek? at hpk
          by_cases h : s.offset < s.inputEnd
          · exact h
          · rw [ite_eq_right h] at hpk; cases hpk
        have hadv := advance_offset_lt s hlt
        have hend2 := advance_inputEnd s
        exact ih s.advance (content.push _) (by omega) c hc
    · rename_i hpk
      rw [hpk] at hc
      cases hc

/-- The block-scalar body walk: given a column-0-or-EOF entry, every exit is
    column 0, EOF, or an `OffLine` stop — the SAME line collection the plain
    scalar runs, so the same set (item 37).  A mid-line exit is the one arm
    that says anything, and `collectLineContentLoop_stop` already named it. -/
private lemma collectBlockScalarLoop_end (fuel : Nat) :
    ∀ (s : ScannerState) (raw : String) (ci ie : Nat),
    (s.col = 0 ∨ s.peek? = none) →
    s.inputEnd - s.offset < fuel →
    s.inputEnd ≤ ie →
    (collectBlockScalarLoop s raw fuel ci ie).2.col = 0 ∨
    (∀ c, (collectBlockScalarLoop s raw fuel ci ie).2.peek? = some c →
        ¬(c = ' ' ∨ c = '\t') ∧ OffLine c) := by
  induction fuel with
  | zero => intro s _ _ _ _ hb _; omega
  | succ fuel' ih =>
    intro s raw ci ie hentry hb hie
    unfold collectBlockScalarLoop
    split
    · -- document boundary at col 0
      rename_i hdoc
      simp only [Bool.and_eq_true, beq_iff_eq] at hdoc
      exact Or.inl (by simpa using hdoc.1)
    · -- name the indent-consumption result
      generalize hces : consumeExactSpaces s ci = pr
      obtain ⟨spc, sas⟩ := pr
      have hsas1 : s.offset ≤ sas.offset := by
        have h := (consumeExactSpaces_fields ci s).1; rw [hces] at h; exact h
      have hsas2 : sas.inputEnd = s.inputEnd := by
        have h := (consumeExactSpaces_fields ci s).2; rw [hces] at h; exact h
      try dsimp only []
      split
      · -- EOF after the indent spaces
        rename_i hpk
        exact Or.inr (fun c hc => by rw [hc] at hpk; cases hpk)
      · rename_i c₀ hpk
        have hlt := peek_some_lt hpk
        split
        · -- an empty line: consume its break and recurse at col 0
          rename_i hbr
          try dsimp only []
          have hgt := consumeNewline_offset_gt hpk hbr
          have hn2 := (consumeNewline_fields sas).2
          exact ih (consumeNewline sas) _ ci ie
            (Or.inl (consumeNewline_col0 hpk hbr)) (by omega) (by omega)
        · split
          · -- dedented non-empty line: return the ENTRY state
            cases hentry with
            | inl hcol => exact Or.inl hcol
            | inr hpk0 => exact Or.inr (fun c hc => by rw [hc] at hpk0; cases hpk0)
          · -- content line: name the line-collection result
            try dsimp only []
            generalize hlcl : collectLineContentLoop sas "" (ie - sas.offset + 1) = lr
            obtain ⟨lc, sal⟩ := lr
            have hsal1 : sas.offset ≤ sal.offset := by
              have h := (collectLineContentLoop_fields (ie - sas.offset + 1) sas "").1
              rw [hlcl] at h; exact h
            have hsal2 : sal.inputEnd = sas.inputEnd := by
              have h := (collectLineContentLoop_fields (ie - sas.offset + 1) sas "").2
              rw [hlcl] at h; exact h
            try dsimp only []
            split
            · rename_i c' hpk'
              split
              · -- break after the line: consume and recurse at col 0
                rename_i hbr'
                try dsimp only []
                have hgt := consumeNewline_offset_gt hpk' hbr'
                have hn2 := (consumeNewline_fields sal).2
                exact ih (consumeNewline sal) _ ci ie
                  (Or.inl (consumeNewline_col0 hpk' hbr')) (by omega) (by omega)
              · -- non-break stop mid-line: a non-printable or BOM
                rename_i hnbr
                split
                · -- empty line run: the scanner stays at `s`
                  rcases ‹s.col = 0 ∨ s.peek? = none› with h0 | hnone
                  · exact Or.inl h0
                  · refine Or.inr (fun c hc => ?_)
                    have hc' : s.peek? = some c := hc
                    rw [hnone] at hc'; cases hc'
                dsimp only
                refine Or.inr (fun c hc => ?_)
                rw [hpk'] at hc
                injection hc with hce
                subst hce
                have hstop := collectLineContentLoop_stop (ie - sas.offset + 1) sas ""
                  (by omega)
                rw [hlcl] at hstop
                rcases hstop c' hpk' with hbr2 | hnp | hbom
                · exact absurd hbr2 (by simpa using hnbr)
                · exact ⟨by rintro (rfl | rfl) <;> exact absurd hnp (by decide),
                         Or.inl hnp⟩
                · subst hbom
                  exact ⟨by decide, Or.inr rfl⟩
            · -- EOF after the line
              rename_i hpk'
              exact Or.inr (fun c hc => by rw [hc] at hpk'; cases hpk')

private lemma parseBlockHeaderLoop_inputEnd (fuel : Nat) :
    ∀ (s : ScannerState) (chomp : ChompStyle) (eo : Option Nat),
    (parseBlockHeaderLoop s chomp eo fuel).2.2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s _ _; rfl
  | succ fuel' ih =>
    intro s chomp eo
    unfold parseBlockHeaderLoop
    split
    · exact (ih s.advance _ _).trans (advance_inputEnd s)
    · exact (ih s.advance _ _).trans (advance_inputEnd s)
    · split
      · exact (ih s.advance _ _).trans (advance_inputEnd s)
      · rfl
    · rfl

private lemma collectCommentTextLoop_inputEnd (fuel : Nat) :
    ∀ (s : ScannerState) (text : String),
    (collectCommentTextLoop s text fuel).2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s _; unfold collectCommentTextLoop; rfl
  | succ fuel' ih =>
    intro s text
    unfold collectCommentTextLoop
    split
    · split
      · rfl
      · exact (ih s.advance _).trans (advance_inputEnd s)
    · rfl

private lemma scanBlockScalarSkipComment_inputEnd (s : ScannerState) :
    (scanBlockScalarSkipComment s).inputEnd = s.inputEnd := by
  unfold scanBlockScalarSkipComment
  split
  · dsimp only []
    generalize hp : collectCommentTextLoop s.advance ""
      (s.advance.inputEnd - s.advance.offset) = pr
    obtain ⟨text, s2⟩ := pr
    have hcc := collectCommentTextLoop_inputEnd
      (s.advance.inputEnd - s.advance.offset) s.advance ""
    rw [hp] at hcc
    dsimp only [] at hcc
    try dsimp only []
    split
    · split
      · exact hcc.trans (advance_inputEnd s)
      · rfl
    · rfl
  · rfl

private lemma scanBlockScalarConsumeNewline_inputEnd {s s' : ScannerState}
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.inputEnd = s.inputEnd := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · have he := Except.ok.inj h; subst he
      exact (consumeNewline_fields s).2
    · split at h
      · have he := Except.ok.inj h; subst he; rfl
      · cases h
  · have he := Except.ok.inj h; subst he; rfl

/-- `scanBlockScalarBody`: the emitted state sits at column 0 or at an
    `OffLine` stop — the collection loop's only mid-line stops are a
    non-printable or the BOM (item 47 strengthened this from `NodeStop`,
    which the `:`-residue refutation cannot use because `NodeStop` admits
    the `:` itself). -/
private lemma scanBlockScalarBody_restOffLine {s_orig s_after_newline s' : ScannerState}
    {chomp : ChompStyle} {eo : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (hentry : s_after_newline.col = 0 ∨ s_after_newline.peek? = none)
    (hie : s_after_newline.inputEnd ≤ s_orig.inputEnd)
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanBlockScalarBody s_orig s_after_newline chomp eo isLit startPos = .ok s') :
    s'.col = 0 ∨ RestStop OffLine s' := by
  cases eo with
  | some m =>
    unfold scanBlockScalarBody at hok
    dsimp only [] at hok
    generalize hlr : collectBlockScalarLoop s_after_newline ""
      (s_orig.inputEnd - s_after_newline.offset + 1)
      (max 0 (s_orig.currentIndent + (m : Int))).toNat s_orig.inputEnd = lr at hok
    have hloop := collectBlockScalarLoop_end (s_orig.inputEnd - s_after_newline.offset + 1)
      s_after_newline "" (max 0 (s_orig.currentIndent + (m : Int))).toNat
      s_orig.inputEnd hentry (by omega) hie
    rw [hlr] at hloop
    obtain ⟨raw2, sac⟩ := lr
    dsimp only [] at hok hloop
    split at hok
    · cases hok
    · injection hok with h_eq
      subst h_eq
      cases hloop with
      | inl h0 => exact Or.inl h0
      | inr hpk => exact Or.inr ((restStop_of_peek_stop (s := sac) hend' hpk).congr rfl rfl)
  | none =>
    unfold scanBlockScalarBody at hok
    dsimp only [] at hok
    generalize hci : autoDetectBlockScalarIndent s_after_newline
      (max 0 (s_orig.currentIndent + 1)).toNat s_orig.inputEnd = cip at hok
    obtain ⟨ci, err⟩ := cip
    dsimp only [] at hok
    cases err with
    | some e => cases hok
    | none =>
      dsimp only [] at hok
      generalize hlr : collectBlockScalarLoop s_after_newline ""
        (s_orig.inputEnd - s_after_newline.offset + 1) ci s_orig.inputEnd = lr at hok
      have hloop := collectBlockScalarLoop_end (s_orig.inputEnd - s_after_newline.offset + 1)
        s_after_newline "" ci s_orig.inputEnd hentry (by omega) hie
      rw [hlr] at hloop
      obtain ⟨raw2, sac⟩ := lr
      dsimp only [] at hok hloop
      split at hok
      · cases hok
      · injection hok with h_eq
        subst h_eq
        cases hloop with
        | inl h0 => exact Or.inl h0
        | inr hpk => exact Or.inr ((restStop_of_peek_stop (s := sac) hend' hpk).congr rfl rfl)

/-- `scanBlockScalar`: the emitted state sits at column 0, at end of input,
    or on an `OffLine` stop.  (`hend'` from the caller's corr.) -/
private lemma scanBlockScalar_restOffLine_aux {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanBlockScalar s = .ok s') :
    s'.col = 0 ∨ RestStop OffLine s' := by
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  split at hok
  · cases hok
  · rename_i s_after_newline hnl
    have hentry : s_after_newline.col = 0 ∨ s_after_newline.peek? = none := by
      unfold scanBlockScalarConsumeNewline at hnl
      split at hnl
      · rename_i c₀ hpk₀
        split at hnl
        · rename_i hbr₀
          have h := Except.ok.inj hnl
          subst h
          exact Or.inl (consumeNewline_col0 hpk₀ hbr₀)
        · split at hnl
          · rename_i hnomore
            have h := Except.ok.inj hnl
            subst h
            refine Or.inr ?_
            unfold ScannerState.peek?
            rw [ite_eq_right]
            simp only [Bool.not_eq_true', ScannerState.hasMore,
              decide_eq_false_iff_not] at hnomore
            exact hnomore
          · cases hnl
      · rename_i hpk₀
        have h := Except.ok.inj hnl
        subst h
        exact Or.inr hpk₀
    have hie : s_after_newline.inputEnd ≤ s.inputEnd := by
      have h1 := scanBlockScalarConsumeNewline_inputEnd hnl
      have h2 := scanBlockScalarSkipComment_inputEnd
        (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)
      have h3 := (skipWhitespace_fields (parseBlockHeaderLoop s.advance .clip none 2).2.2).2
      have h4 := parseBlockHeaderLoop_inputEnd 2 s.advance .clip none
      have h5 := advance_inputEnd s
      omega
    exact scanBlockScalarBody_restOffLine hentry hie hend' hok

/-- The `OffLine` form, for the `:`-residue refutation (item 47). -/
lemma scanBlockScalar_restOffLine {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanBlockScalar s = .ok s') :
    s'.col = 0 ∨ RestStop OffLine s' :=
  scanBlockScalar_restOffLine_aux hend' hok

lemma scanBlockScalar_restNodeStop {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanBlockScalar s = .ok s') :
    s'.col = 0 ∨ RestNodeStop s' :=
  (scanBlockScalar_restOffLine hend' hok).imp id
    (RestStop.mono (fun _ => OffLine.toNodeStop))

lemma scanBlockScalar_restNoOpen {s s' : ScannerState}
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanBlockScalar s = .ok s') :
    s'.col = 0 ∨ RestNoOpen s' :=
  (scanBlockScalar_restNodeStop hend' hok).imp id
    (RestStop.mono (fun _ => NodeStop.toNoOpenHead))

/-! ### The other content scans' columns (item 77)

The block scalar is the only content scan that can park at a line start, and it
re-arms the simple key when it does.  The remaining three end on a character
they consumed inside a line: the quoted scans on their closing quote, the alias
on its name.  Together with `scanPlainScalar_col_pos` this is what says a
block-context CONTENT park with the save flag down is never at column 0. -/

/-- The block scalar's park re-arms: `[170]`/`[174]` end past a break, so a key
    may start on the line the scan stopped at. -/
lemma scanBlockScalar_simpleKeyAllowed {s s' : ScannerState}
    (hok : scanBlockScalar s = .ok s') : s'.simpleKeyAllowed = true := by
  unfold scanBlockScalar at hok
  simp only [] at hok
  split at hok
  · contradiction
  · unfold scanBlockScalarBody at hok
    simp only [] at hok
    repeat (any_goals (split at hok))
    all_goals (try contradiction)
    all_goals (simp only [Except.ok.injEq] at hok; subst hok; rfl)

/-- The block-scalar body clears the saved key (§8.1: a block scalar is never
    an implicit key), so a park that follows one has nothing for the `:` to
    resolve — which is what refutes the pack's guard rather than punting it. -/
lemma scanBlockScalarBody_simpleKey_false {s0 s1 : ScannerState} {ch : ChompStyle}
    {off : Option Nat} {il : Bool} {sp : YamlPos} {s' : ScannerState}
    (h : scanBlockScalarBody s0 s1 ch off il sp = .ok s') :
    s'.simpleKey.possible = false := by
  unfold scanBlockScalarBody at h
  dsimp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (have h' := Except.ok.inj h; subst h'; rfl)

lemma scanBlockScalar_simpleKey_false {s s' : ScannerState}
    (h : scanBlockScalar s = .ok s') : s'.simpleKey.possible = false := by
  unfold scanBlockScalar at h
  dsimp only [] at h
  split at h
  · cases h
  · exact scanBlockScalarBody_simpleKey_false h

/-! ### The block scalar's own arming (item 154)

Item 77's note above says the block scalar is the only content scan that can
park at a line start.  These say what it leaves the INDENT CHECK doing when it
does, which is what a landing off such a park needs in order to spend a cover:
preprocessing's unwind runs on exactly that flag, and a park at column 0 has
crossed no break of its own for the landing walk to arm it with.

The one escape is measured, not guessed: a header at end of input consumes no
break (`scanBlockScalarConsumeNewline`'s `!hasMore` arm), and `"k: |"` really
does stop with the flag down.  It also stops with nothing left to read, which
is the disjunct a landing refutes.
-/

lemma consumeExactSpaces_preserves_nic (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).2.needIndentCheck = s.needIndentCheck := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ _ ih =>
    unfold consumeExactSpaces
    split
    · dsimp only []; rw [ih, advance_preserves_needIndentCheck]
    · rfl

lemma collectLineContentLoop_preserves_nic (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).2.needIndentCheck = s.needIndentCheck := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ _ ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih, advance_preserves_needIndentCheck]
    · rfl

/-- `consumeNewline` only ever raises the flag. -/
lemma consumeNewline_nic_mono {s : ScannerState} (h : s.needIndentCheck = true) :
    (consumeNewline s).needIndentCheck = true := by
  unfold consumeNewline
  split
  · rfl
  · simp only []; split <;> rfl
  · exact h


/-- The body's collection loop only ever raises the flag: every step that
    recurses goes through `consumeNewline`, and every step that stops reaches
    its state through the two flag-preserving walks. -/
lemma collectBlockScalarLoop_nic_mono (s : ScannerState) (raw : String)
    (fuel ci ie : Nat) (h : s.needIndentCheck = true) :
    (collectBlockScalarLoop s raw fuel ci ie).2.needIndentCheck = true := by
  induction fuel generalizing s raw with
  | zero => unfold collectBlockScalarLoop; exact h
  | succ _ ih =>
    unfold collectBlockScalarLoop
    split
    · exact h
    · simp only []
      split
      · rw [consumeExactSpaces_preserves_nic]; exact h
      · split
        · exact ih _ _ (consumeNewline_nic_mono
            (by rw [consumeExactSpaces_preserves_nic]; exact h))
        · split
          · exact h
          · split
            · split
              · exact ih _ _ (consumeNewline_nic_mono
                  (by rw [collectLineContentLoop_preserves_nic,
                          consumeExactSpaces_preserves_nic]; exact h))
              · split
                · exact h
                · rw [collectLineContentLoop_preserves_nic,
                    consumeExactSpaces_preserves_nic]; exact h
            · rw [collectLineContentLoop_preserves_nic,
                  consumeExactSpaces_preserves_nic]; exact h

lemma emitAt_preserves_nic (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).needIndentCheck = s.needIndentCheck := by
  unfold ScannerState.emitAt; rfl

lemma scanBlockScalarBody_nic_mono {s_orig s_nl s' : ScannerState} {chomp : ChompStyle}
    {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (hs : s_nl.needIndentCheck = true)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.needIndentCheck = true := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals (rw [emitAt_preserves_nic]
             exact collectBlockScalarLoop_nic_mono _ _ _ _ _ hs)

lemma consumeExactSpaces_atEnd {s : ScannerState} (h : s.peek? = none) (count : Nat) :
    consumeExactSpaces s count = (0, s) := by
  cases count with
  | zero => rfl
  | succ _ => unfold consumeExactSpaces; rw [h]

lemma collectBlockScalarLoop_atEnd {s : ScannerState} (h : s.peek? = none)
    (raw : String) (fuel ci ie : Nat) :
    (collectBlockScalarLoop s raw fuel ci ie).2 = s := by
  cases fuel with
  | zero => rfl
  | succ _ =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only [consumeExactSpaces_atEnd h, h]

lemma scanBlockScalarBody_atEnd {s_orig s_nl s' : ScannerState} {chomp : ChompStyle}
    {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (hs : s_nl.peek? = none)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.col = s_nl.col := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals (rw [collectBlockScalarLoop_atEnd hs]; unfold ScannerState.emitAt; rfl)

/-! The header's own column floor: `-`, `+`, the indentation digit, the
separation whites and the header comment are all `nb-char`, so none of them
moves the cursor LEFT, and the `|`/`>` the dispatch peeked at is spent by the
opening `advance`.  A header that stops without a break therefore stops
strictly inside its line — which is how the `"k: |"` escape is refuted at a
column-0 consumer rather than carried to one. -/

private lemma bsCommentTextLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (text : String),
    s.col ≤ (collectCommentTextLoop s text fuel).2.col := by
  induction fuel with
  | zero => intro s text; unfold collectCommentTextLoop; exact Nat.le_refl _
  | succ _ ih =>
    intro s text
    unfold collectCommentTextLoop
    split
    · rename_i c hpk
      split
      · exact Nat.le_refl _
      · rename_i hstop
        have := ih s.advance (text.push c)
        rw [advance_col_succ_of_peek hpk (by simpa using hstop)] at this
        omega
    · exact Nat.le_refl _

private lemma parseBlockHeaderLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (ch : ChompStyle) (m : Option Nat),
    s.col ≤ (parseBlockHeaderLoop s ch m fuel).2.2.col := by
  induction fuel with
  | zero => intro s ch m; unfold parseBlockHeaderLoop; exact Nat.le_refl _
  | succ _ ih =>
    intro s ch m
    unfold parseBlockHeaderLoop
    have hpeek : ∀ c, peekBlockHeaderIndicator? s ch m = some c → s.peek? = some c := by
      intro c h; unfold peekBlockHeaderIndicator? at h
      split at h <;> (try split at h) <;> simp_all
    split
    · rename_i hpk
      have := ih s.advance .strip m
      rw [advance_col_succ_of_peek (hpeek _ hpk) (by decide)] at this; omega
    · rename_i hpk
      have := ih s.advance .keep m
      rw [advance_col_succ_of_peek (hpeek _ hpk) (by decide)] at this; omega
    · rename_i c _ _ hpk
      split
      · rename_i hd
        have := ih s.advance ch (some (c.toNat - '0'.toNat))
        rw [advance_col_succ_of_peek (hpeek _ hpk) ?_] at this
        · omega
        · simp only [Bool.and_eq_true, bne_iff_ne] at hd
          have hdig : c.isDigit = true := hd.1
          simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
            Bool.or_eq_false_iff, beq_eq_false_iff_ne]
          constructor <;> (intro h; subst h; simp at hdig)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma scanBlockScalarSkipComment_col_ge (s : ScannerState) :
    s.col ≤ (scanBlockScalarSkipComment s).col := by
  unfold scanBlockScalarSkipComment
  split
  · rename_i hpk
    split
    · dsimp only []
      split
      · simp only []
        have := bsCommentTextLoop_col_ge (s.advance.inputEnd - s.advance.offset) s.advance ""
        rw [advance_col_succ_of_peek hpk (by decide)] at this
        exact Nat.le_trans (Nat.le_succ _) this
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- **The block scalar arms the indent check** (item 154) — the flag twin of
    item 77's `scanBlockScalar_simpleKeyAllowed`, carrying the same escape item
    77's own `col_pos_or_armed` carries, and for the same reason.

    `[170]`/`[174]`'s body begins past a `b-break`, and `consumeNewline` raises
    the flag on every one; the collection loop only ever raises it again.  The
    one header that consumes no break is the one at end of input — `"k: |"`
    really does stop with the flag DOWN — and that header never left its line,
    so it stops strictly right of column 0.  A landing at a column-0 park
    resolves the disjunction on the column it already has. -/
lemma scanBlockScalar_nic_or_col_pos {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanBlockScalar s = .ok s') :
    s'.needIndentCheck = true ∨ 0 < s'.col := by
  have hhdr : 0 < (scanBlockScalarSkipComment
      (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)).col := by
    have h1 := advance_col_succ_of_peek hpk hnb
    have h2 := parseBlockHeaderLoop_col_ge 2 s.advance .clip none
    have h3 := skipWhitespace_col_ge (parseBlockHeaderLoop s.advance .clip none 2).2.2
    have h4 := scanBlockScalarSkipComment_col_ge
      (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)
    omega
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  split at hok
  · cases hok
  · rename_i s_nl hnl
    unfold scanBlockScalarConsumeNewline at hnl
    split at hnl
    · rename_i c₀ hpk₀
      split at hnl
      · rename_i hbr₀
        have h := Except.ok.inj hnl; subst h
        exact Or.inl (scanBlockScalarBody_nic_mono
          (consumeNewline_needIndentCheck_of_break _ c₀ hpk₀ hbr₀) hok)
      · split at hnl
        · rename_i hnomore
          have hs_eq := Except.ok.inj hnl
          have hpkn : s_nl.peek? = none := by
            rw [← hs_eq]
            unfold ScannerState.peek?; rw [ite_eq_right]
            simp only [Bool.not_eq_true', ScannerState.hasMore,
              decide_eq_false_iff_not] at hnomore
            exact hnomore
          exact Or.inr (by rw [scanBlockScalarBody_atEnd hpkn hok, ← hs_eq]; exact hhdr)
        · cases hnl
    · rename_i hpk₀
      have hs_eq := Except.ok.inj hnl
      have hpkn : s_nl.peek? = none := by rw [← hs_eq]; exact hpk₀
      exact Or.inr (by rw [scanBlockScalarBody_atEnd hpkn hok, ← hs_eq]; exact hhdr)

/-- The dispatch-level form, mirroring `dispatchContent_blockScalar_restOffLine`. -/
lemma dispatchContent_blockScalar_nic {s s' : ScannerState} {c : Char}
    (hbs : c = '|' ∨ c = '>')
    (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.needIndentCheck = true ∨ 0 < s'.col := by
  have hnb : isLineBreakBool c = false := by rcases hbs with rfl | rfl <;> decide
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i heq
    have : c = '&' := by simpa using heq
    rcases hbs with rfl | rfl <;> simp at this
  split at hok
  · rename_i heq
    have : c = '*' := by simpa using heq
    rcases hbs with rfl | rfl <;> simp at this
  split at hok
  · rename_i heq
    have : c = '!' := by simpa using heq
    rcases hbs with rfl | rfl <;> simp at this
  split at hok
  · exact scanBlockScalar_nic_or_col_pos hpk hnb (peel_blockScalarGuard hok)
  · rename_i heq
    rcases hbs with rfl | rfl <;> simp at heq

/-- The anchor/alias name walk only ever advances over `[102] ns-anchor-char`,
    which is not a break, so it never moves LEFT. -/
private lemma collectAnchorNameLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (name : String),
    s.col ≤ (collectAnchorNameLoop s name fuel).2.col := by
  induction fuel with
  | zero => intro s name; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s name
    unfold collectAnchorNameLoop
    split
    · rename_i c hpk
      split
      · rename_i hchar
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hchar
        have := ih s.advance (name.push c)
        rw [advance_col_succ_of_peek hpk hchar.1.1.2] at this
        omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

/-- `[104] c-ns-alias-node` spends its `*` before the name, so the park is
    inside a line. -/
lemma scanAnchorOrAlias_col_pos {s s' : ScannerState} {c : Char} {b : Bool}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanAnchorOrAlias s b = .ok s') : 0 < s'.col := by
  unfold scanAnchorOrAlias at hok
  simp only [] at hok
  split at hok
  · cases hok
  · injection hok with h_eq; subst h_eq
    have h1 : 0 < s.advance.col := advance_col_pos_of_peek hpk hnb
    have h2 := collectAnchorNameLoop_col_ge (s.inputEnd - s.advance.offset) s.advance ""
    show 0 < (collectAnchorNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2.col
    omega

/-- `[120] c-single-quoted` ends on the closing `'` — the walk's only `.ok`
    exit is the `advance` over it. -/
private lemma collectSingleQuotedLoop_col_pos (fuel : Nat) :
    ∀ (s : ScannerState) (content : String) (startPos : YamlPos) (inFlow : Bool)
      (ci : Int) (ie : Nat) (rc : String) (s' : ScannerState),
    collectSingleQuotedLoop s content fuel startPos inFlow ci ie = .ok (rc, s') →
    0 < s'.col := by
  induction fuel with
  | zero => intro s content startPos inFlow ci ie rc s' hok; simp [collectSingleQuotedLoop] at hok
  | succ fuel' ih =>
    intro s content startPos inFlow ci ie rc s' hok
    unfold collectSingleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · rename_i hpk
      dsimp only [] at hok
      split at hok
      · exact ih _ _ _ _ _ _ _ _ hok
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        exact advance_col_pos_of_peek hpk (by decide)
    · rename_i c hpk hnq
      split at hok
      · simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · repeat' split at hok
          all_goals first
            | exact ih _ _ _ _ _ _ _ _ hok
            | simp at hok
      · split at hok
        · simp at hok
        · exact ih _ _ _ _ _ _ _ _ hok

lemma scanSingleQuoted_col_pos {s s' : ScannerState}
    (hok : scanSingleQuoted s = .ok s') : 0 < s'.col := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    have hcol := collectSingleQuotedLoop_col_pos _ _ _ _ _ _ _ _ _ hloop
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h; exact hcol
    · have h := Except.ok.inj hok; subst h; exact hcol

/-- `[109] c-double-quoted` ends on the closing `"`, the same way. -/
private lemma collectDoubleQuotedLoop_col_pos (fuel : Nat) :
    ∀ (p : Nat) (s : ScannerState) (content : String) (startPos : YamlPos)
      (inFlow : Bool) (ci : Int) (ie : Nat) (rc : String) (s' : ScannerState),
    collectDoubleQuotedLoop s content fuel startPos inFlow ci ie p = .ok (rc, s') →
    0 < s'.col := by
  induction fuel with
  | zero => intro p s content startPos inFlow ci ie rc s' hok; simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    intro p s content startPos inFlow ci ie rc s' hok
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · rename_i hpk
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      exact advance_col_pos_of_peek hpk (by decide)
    · dsimp only [] at hok
      split at hok
      · split at hok
        · simp only [bind, Except.bind] at hok
          repeat' split at hok
          all_goals first
            | exact ih _ _ _ _ _ _ _ _ _ hok
            | simp at hok
        · simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · exact ih _ _ _ _ _ _ _ _ _ hok
      · exact absurd hok (by simp)
    · split at hok
      · simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · repeat' split at hok
          all_goals first
            | exact ih _ _ _ _ _ _ _ _ _ hok
            | simp at hok
      · split at hok
        · simp at hok
        · exact ih _ _ _ _ _ _ _ _ _ hok

lemma scanDoubleQuoted_col_pos {s s' : ScannerState}
    (hok : scanDoubleQuoted s = .ok s') : 0 < s'.col := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    have hcol := collectDoubleQuotedLoop_col_pos _ _ _ _ _ _ _ _ _ _ hloop
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h; exact hcol
    · have h := Except.ok.inj hok; subst h; exact hcol

/-! ## §9 The dispatch-level producer

For a content dispatch that was NOT a property (`&`/`!`), in block context,
the emitted state sits at column 0 or stops the line where §7.5 says a
complete node's line stops: quoted scalars and aliases by their trailing
validation (`NodeTail` — `s-l-comments` plus `[154]`'s `:`), plain and block
scalars by their walks (`NodeTail` or `OffLine`).  The union is `NodeStop`,
and item 10's flow-open reading is one `mono` below it. -/

lemma dispatchContent_restNodeStop {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hna : c ≠ '&') (hnt : c ≠ '!')
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.col = 0 ∨ RestNodeStop s' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq
    exact absurd (by simpa using h_eq) hna
  · split at hok
    · -- '*': the alias arm keeps its validateAliasClose
      split at hok
      · simp at hok
      split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · rename_i v hv
          split at hok
          · simp at hok
          · rename_i u hval
            cases u
            have hvs : v = s' := Except.ok.inj hok
            subst hvs
            have hfl := ScannerCorrectness.scanAnchorOrAlias_preserves_flowLevel s false v hv
            have hflv : v.inFlow = false := by
              unfold ScannerState.inFlow at hflow ⊢
              rw [hfl]
              exact hflow
            exact Or.inr ((restNodeTail_of_validateAliasClose hend' hflv hval).mono
              (fun _ => NodeTail.toNodeStop))
    · split at hok
      · rename_i h_eq
        exact absurd (by simpa using h_eq) hnt
      · split at hok
        · -- '|' or '>': block scalar under the item-9c guard
          exact scanBlockScalar_restNodeStop hend' (peel_blockScalarGuard hok)
        · split at hok
          · -- '"': double-quoted, then the endLine touch-up
            split at hok
            · simp at hok
            · rename_i s_dq hdq
              have heq : (if s_dq.simpleKey.possible then
                  { s_dq with simpleKey := { s_dq.simpleKey with endLine := s_dq.line } }
                else s_dq) = s' := Except.ok.inj hok
              have hfields : s'.input = s_dq.input ∧ s'.offset = s_dq.offset ∧
                  s'.inputEnd = s_dq.inputEnd := by
                rw [← heq]
                split <;> exact ⟨rfl, rfl, rfl⟩
              have hend_dq : s_dq.inputEnd = s_dq.input.utf8ByteSize := by
                rw [← hfields.2.2, ← hfields.1]
                exact hend'
              exact Or.inr (((scanDoubleQuoted_restNodeTail hflow hend_dq hdq).mono
                (fun _ => NodeTail.toNodeStop)).congr hfields.1 hfields.2.1)
          · split at hok
            · -- '\'': single-quoted
              split at hok
              · simp at hok
              · rename_i s_sq hsq
                have heq : (if s_sq.simpleKey.possible then
                    { s_sq with simpleKey := { s_sq.simpleKey with endLine := s_sq.line } }
                  else s_sq) = s' := Except.ok.inj hok
                have hfields : s'.input = s_sq.input ∧ s'.offset = s_sq.offset ∧
                    s'.inputEnd = s_sq.inputEnd := by
                  rw [← heq]
                  split <;> exact ⟨rfl, rfl, rfl⟩
                have hend_sq : s_sq.inputEnd = s_sq.input.utf8ByteSize := by
                  rw [← hfields.2.2, ← hfields.1]
                  exact hend'
                exact Or.inr (((scanSingleQuoted_restNodeTail hflow hend_sq hsq).mono
                  (fun _ => NodeTail.toNodeStop)).congr hfields.1 hfields.2.1)
            · -- plain scalar (or error)
              split at hok
              · exact scanPlainScalar_restNodeStop hflow hend' hok
              · simp at hok

/-- **The content park's own column** (item 77).  Outside the property arms, a
    block-context content dispatch parks either with the simple key ARMED — the
    block scalar, whose `[170]`/`[174]` body ends past a break, so a key may
    start on the line it stops at — or strictly inside a line: the quoted scans
    end on their closing quote, the alias on its name, and the plain walk moves
    (`scanPlainScalar_col_pos`) because the dispatcher's own guards say the
    probe cannot fire at its first character.

    This is what `col0_or_lineStop`'s disjunction could not say.  A park at a
    line start with the save DOWN is the one shape the landing's re-arm (item
    76) does not fund, and it has no inhabitant. -/
lemma dispatchContent_col_pos_or_armed {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hna : c ≠ '&') (hnt : c ≠ '!')
    (hpk : s.peek? = some c)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    ((c = '|' ∨ c = '>') ∧
        s'.simpleKeyAllowed = true ∧ s'.simpleKey.possible = false) ∨ 0 < s'.col := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq
    exact absurd (by simpa using h_eq) hna
  · split at hok
    · -- '*': the alias node's name is spent inside the line
      rename_i hstar
      have hnb : isLineBreakBool c = false := by
        have hc : c = '*' := by simpa using hstar
        subst hc; decide
      split at hok
      · simp at hok
      split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · rename_i v hv
          split at hok
          · simp at hok
          · rename_i u hval
            cases u
            have hvs : v = s' := Except.ok.inj hok
            subst hvs
            exact Or.inr (scanAnchorOrAlias_col_pos hpk hnb hv)
    · split at hok
      · rename_i h_eq
        exact absurd (by simpa using h_eq) hnt
      · split at hok
        · -- '|' or '>': the block scalar re-arms at its column-0 park — with
          -- the saved key CLEARED (§8.1), which is the second half item 80
          -- records: the one armed content park has nothing for a `:` to
          -- resolve.
          -- **Item 206 pins the HEAD here too.**  The disjunction's left half
          -- was item 77's answer to "where does a content park stand"; naming
          -- the character that produces it turns the same term into the answer
          -- to "which content scan can reach a line start", which is the
          -- reading `dispatchContent_nic_or_col` spends below.
          rename_i h_bs
          exact Or.inl ⟨by simpa using h_bs,
                        scanBlockScalar_simpleKeyAllowed (peel_blockScalarGuard hok),
                        scanBlockScalar_simpleKey_false (peel_blockScalarGuard hok)⟩
        · split at hok
          · -- '"': the closing quote, then the endLine touch-up (no column)
            split at hok
            · simp at hok
            · rename_i s_dq hdq
              have heq : (if s_dq.simpleKey.possible then
                  { s_dq with simpleKey := { s_dq.simpleKey with endLine := s_dq.line } }
                else s_dq) = s' := Except.ok.inj hok
              have hcol : s'.col = s_dq.col := by rw [← heq]; split <;> rfl
              exact Or.inr (hcol ▸ scanDoubleQuoted_col_pos hdq)
          · split at hok
            · -- '\'': the same
              split at hok
              · simp at hok
              · rename_i s_sq hsq
                have heq : (if s_sq.simpleKey.possible then
                    { s_sq with simpleKey := { s_sq.simpleKey with endLine := s_sq.line } }
                  else s_sq) = s' := Except.ok.inj hok
                have hcol : s'.col = s_sq.col := by rw [← heq]; split <;> rfl
                exact Or.inr (hcol ▸ scanSingleQuoted_col_pos hsq)
            · -- the plain walk
              split at hok
              · rename_i hcan
                rw [hflow] at hcan
                exact Or.inr (scanPlainScalar_col_pos hflow hpk hcan hnotdoc hok)
              · simp at hok

/-! ### The tag property's column (item 77)

`[97] c-ns-tag-property` spends its `!` and then walks `ns-uri-char` /
`ns-tag-char` / `ns-word-char`, none of which is a break — so the park is
inside a line, exactly as the anchor's is. -/

private lemma not_lineBreak_of_uriChar {c : Char} (h : isUriCharBool c = true) :
    isLineBreakBool c = false := by
  simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  constructor <;> (rintro rfl; exact absurd h (by decide))

private lemma not_lineBreak_of_tagChar {c : Char} (h : isTagCharBool c = true) :
    isLineBreakBool c = false := by
  simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  constructor <;> (rintro rfl; exact absurd h (by decide))

private lemma not_lineBreak_of_wordChar {c : Char} (h : isWordCharBool c = true) :
    isLineBreakBool c = false := by
  simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  constructor <;> (rintro rfl; exact absurd h (by decide))

private lemma collectVerbatimTagLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (uri : String),
    s.col ≤ (collectVerbatimTagLoop s uri fuel).2.2.col := by
  induction fuel with
  | zero => intro s uri; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s uri
    unfold collectVerbatimTagLoop
    split
    · rename_i hpk
      exact Nat.le_of_lt (by rw [advance_col_succ_of_peek hpk (by decide)]; omega)
    · rename_i c _ hpk
      split
      · rename_i huri
        have := ih s.advance (uri.push c)
        rw [advance_col_succ_of_peek hpk (not_lineBreak_of_uriChar huri)] at this
        omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma collectTagSuffixLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (suffix : String),
    s.col ≤ (collectTagSuffixLoop s suffix fuel).2.col := by
  induction fuel with
  | zero => intro s suffix; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s suffix
    unfold collectTagSuffixLoop
    split
    · rename_i c hpk
      split
      · rename_i htag
        have := ih s.advance (suffix.push c)
        rw [advance_col_succ_of_peek hpk (not_lineBreak_of_tagChar htag)] at this
        omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma collectTagHandleLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (chars : String),
    s.col ≤ (collectTagHandleLoop s chars fuel).2.2.col := by
  induction fuel with
  | zero => intro s chars; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s chars
    unfold collectTagHandleLoop
    split
    · rename_i hpk
      exact Nat.le_of_lt (by rw [advance_col_succ_of_peek hpk (by decide)]; omega)
    · rename_i c _ hpk
      split
      · rename_i hword
        have := ih s.advance (chars.push c)
        rw [advance_col_succ_of_peek hpk (not_lineBreak_of_wordChar hword)] at this
        omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma scanVerbatimTag_col_ge {s s' : ScannerState} {p : YamlPos}
    (hpk : s.peek? = some '<') (hok : scanVerbatimTag s p = .ok s') : s.col < s'.col := by
  have h1 := advance_col_succ_of_peek hpk (by decide)
  have h2 := collectVerbatimTagLoop_col_ge (p.offset + s.inputEnd - s.advance.offset) s.advance ""
  unfold scanVerbatimTag at hok
  simp only [] at hok
  split at hok
  · cases hok
  · split at hok
    · cases hok
    · have heq : s' = (collectVerbatimTagLoop s.advance ""
          (p.offset + s.inputEnd - s.advance.offset)).2.2.emitAt p
            (.tag "" (collectVerbatimTagLoop s.advance ""
              (p.offset + s.inputEnd - s.advance.offset)).1) := (Except.ok.inj hok).symm
      rw [heq]
      show s.col < (collectVerbatimTagLoop s.advance ""
        (p.offset + s.inputEnd - s.advance.offset)).2.2.col
      omega

private lemma scanSecondaryTag_col_ge (s : ScannerState) (p : YamlPos)
    (hpk : s.peek? = some '!') : s.col < (scanSecondaryTag s p).col := by
  have h1 := advance_col_succ_of_peek hpk (by decide)
  have h2 := collectTagSuffixLoop_col_ge (p.offset + s.inputEnd - s.advance.offset) s.advance ""
  show s.col < (collectTagSuffixLoop s.advance ""
    (p.offset + s.inputEnd - s.advance.offset)).2.col
  omega

private lemma emitAt_col (s : ScannerState) (p : YamlPos) (t : YamlToken) :
    (s.emitAt p t).col = s.col := rfl

private lemma scanNamedTag_col_ge (s : ScannerState) (p : YamlPos) (ie : Nat) :
    s.col ≤ (scanNamedTag s p ie).col := by
  have h2 := collectTagHandleLoop_col_ge (ie - s.offset) s ""
  unfold scanNamedTag
  simp only []
  split
  · have h3 := collectTagSuffixLoop_col_ge
      (ie - (collectTagHandleLoop s "" (ie - s.offset)).2.2.offset)
      (collectTagHandleLoop s "" (ie - s.offset)).2.2 ""
    simp only [emitAt_col]
    exact Nat.le_trans h2 h3
  · have h3 := collectTagSuffixLoop_col_ge
      (ie - (collectTagHandleLoop s "" (ie - s.offset)).2.2.offset)
      (collectTagHandleLoop s "" (ie - s.offset)).2.2
      (collectTagHandleLoop s "" (ie - s.offset)).fst
    simp only [emitAt_col]
    exact Nat.le_trans h2 h3

/-- `[97] c-ns-tag-property` spends its `!` before the handle, so its park is
    inside a line — the tag's half of item 77's content sweep. -/
lemma scanTag_col_pos {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanTag s = .ok s') : 0 < s'.col := by
  have hbang : 0 < s.advance.col := advance_col_pos_of_peek hpk hnb
  unfold scanTag at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · have hlt : s.advance.peek? = some '<' := by assumption
    split at hok
    · cases hok
    · rename_i v hv
      have heq : s' = { v with simpleKeyAllowed := false } := (Except.ok.inj hok).symm
      have := scanVerbatimTag_col_ge hlt hv
      rw [heq]
      show 0 < v.col
      omega
  · have hbb : s.advance.peek? = some '!' := by assumption
    have heq : s' = { scanSecondaryTag s.advance s.currentPos with
      simpleKeyAllowed := false } := (Except.ok.inj hok).symm
    have := scanSecondaryTag_col_ge s.advance s.currentPos hbb
    rw [heq]
    show 0 < (scanSecondaryTag s.advance s.currentPos).col
    omega
  · have heq : s' = { scanNamedTag s.advance s.currentPos s.inputEnd with
      simpleKeyAllowed := false } := (Except.ok.inj hok).symm
    have := scanNamedTag_col_ge s.advance s.currentPos s.inputEnd
    rw [heq]
    show 0 < (scanNamedTag s.advance s.currentPos s.inputEnd).col
    omega

/-- The two document markers re-arm as well: `[203]`/`[204]` end a document's
    own line, so a key may start on the next one. -/
lemma scanDocumentStart_simpleKeyAllowed (s : ScannerState) :
    (scanDocumentStart s).simpleKeyAllowed = true := rfl

lemma scanDocumentEnd_simpleKeyAllowed {s s' : ScannerState}
    (hok : scanDocumentEnd s = .ok s') : s'.simpleKeyAllowed = true := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok; rfl)

/-- **Item 223: and they CLEAR, which is the other half of the same fact.**
    Item 77 asked the two markers only whether the save comes back up; item 80
    gave the content parks a strictly stronger arm — the save up AND the saved
    key down — and items 222/223 close the gap for the rest of the family.  The
    `---` scan writes `simpleKey := {}` on its way past; `unwindIndents`, `emit`
    and `advanceN` stand between the write and the read, so this is not `rfl`
    the way its `_simpleKeyAllowed` sibling above is. -/
lemma scanDocumentStart_simpleKey_false (s : ScannerState) :
    (scanDocumentStart s).simpleKey.possible = false := by
  simp only [scanDocumentStart, advanceN_preserves_simpleKey, emit_preserves_simpleKey]

/-- …and the `...` scan clears on every arm that returns — the marker ends a
    document, so nothing it left behind can still be a key head. -/
lemma scanDocumentEnd_simpleKey_false {s s' : ScannerState}
    (hok : scanDocumentEnd s = .ok s') : s'.simpleKey.possible = false := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       simp only [advanceN_preserves_simpleKey, emit_preserves_simpleKey])
    | simp_all

/-- **The stream seed's rung** (item 223).  `ScannerState.mk'` writes the
    register empty, and the block-context park's ONE non-flow producer stands
    on the state the `streamStart` emission and §5.2's BOM advance leave — so
    the seed pays `noPending.h_arm`'s tightened conjunct the same way it has
    paid its flag since item 76.  `mk'`'s own half is `rfl`; the two carriers
    in front of it are not. -/
lemma mk'_simpleKey_false (input : String) :
    (ScannerState.mk' input).simpleKey.possible = false := rfl

/-- The two PROPERTY arms spend their `&`/`!` before the name, so they park
    inside a line too — which is what lets item 77's disjunction be stated for
    EVERY content character rather than for the node-producing ones alone. -/
private lemma dispatchContent_props_col_pos {s s' : ScannerState} {c : Char}
    (hprops : c = '&' ∨ c = '!')
    (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchContent s c = .ok s') : 0 < s'.col := by
  have hnb : isLineBreakBool c = false := by rcases hprops with rfl | rfl <;> decide
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- `&`
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i v hv
        rw [(Except.ok.inj hok).symm]
        show 0 < v.col
        exact scanAnchorOrAlias_col_pos hpk hnb hv
  · split at hok
    · exfalso
      rename_i hstar
      have hc : c = '*' := by simpa using hstar
      rcases hprops with rfl | rfl <;> simp at hc
    · split at hok
      · -- `!`
        split at hok
        · simp at hok
        · exact scanTag_col_pos hpk hnb hok
      · exfalso
        rcases hprops with rfl | rfl
        · exact absurd (by decide : (('&' : Char) == '&') = true) (by assumption)
        · exact absurd (by decide : (('!' : Char) == '!') = true) (by assumption)

/-- Item 77 for EVERY content character: the property arms by their own
    indicator, the rest by `dispatchContent_col_pos_or_armed`. -/
lemma dispatchContent_arm_or_col_any {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hpk : s.peek? = some c)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    (s'.simpleKeyAllowed = true ∧ s'.simpleKey.possible = false) ∨ 0 < s'.col := by
  by_cases hprops : c = '&' ∨ c = '!'
  · exact Or.inr (dispatchContent_props_col_pos hprops hpk hok)
  · exact (dispatchContent_col_pos_or_armed hflow (fun h => hprops (Or.inl h))
      (fun h => hprops (Or.inr h)) hpk hnotdoc hok).imp_left And.right

/-- Item 77 at the accumulation site: the same disjunction, with the column
    read on the SURFACE side, where every park states it. -/
lemma dispatchContent_arm_or_col {s s' : ScannerState} {sp' : SurfPos} {c : Char}
    (hflow : s.inFlow = false)
    (hpk : s.peek? = some c)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false)
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (hcorr' : ScannerSurfCorr s' sp') :
    (s'.simpleKeyAllowed = true ∧ s'.simpleKey.possible = false) ∨ 0 < sp'.col :=
  (dispatchContent_arm_or_col_any hflow hpk hnotdoc hok).imp id
    (fun h => by rw [hcorr'.col_eq]; exact h)

/-- **Item 206: the same case analysis, read for the INDENT-CHECK flag.**

    Item 154 asked what a content park at a line start left the check doing and
    could answer only for `|`/`>`, because that was the one arm
    `dispatchContent_col_pos_or_armed` did not deliver a column for.  The arm
    now NAMES itself, so the question closes for every content character:
    outside the block scalar no content scan reaches column 0 at all, and the
    block scalar reaches it by consuming the break that arms the check.

    This is the sentence item 154 wrote in a comment (`content_park_nic`,
    "the only content scan that reaches column 0") turned into the thing that
    states it.  §10: a quantity gets described in prose exactly when it is
    doing work nothing states. -/
lemma dispatchContent_nic_or_col_any {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hpk : s.peek? = some c)
    (hnotdoc : s.col = 0 → atDocumentBoundary s = false)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.needIndentCheck = true ∨ 0 < s'.col := by
  by_cases hprops : c = '&' ∨ c = '!'
  · exact Or.inr (dispatchContent_props_col_pos hprops hpk hok)
  · rcases dispatchContent_col_pos_or_armed hflow (fun h => hprops (Or.inl h))
      (fun h => hprops (Or.inr h)) hpk hnotdoc hok with ⟨hbs, _⟩ | h
    · exact dispatchContent_blockScalar_nic hbs hpk hok
    · exact Or.inr h

/-! ## §12  The BLOCK indicator's own column (item 206)

The content dispatch above needed a case analysis to say where its park
stands, because its scans span lines.  The block indicator's does not: `-`,
`?` and `:` are one character each, every one of the three scans ends with a
single `advance` over that character, and none of them is a line break.  So
the park a block indicator opens is at its own column plus one — never at a
line start, whatever the indicator was parked on.

That is the whole of `block_dispatch_deferred`'s new premise at ten of its
eleven application sites: the flag the premise asks about is asked for only at
column 0, and the dispatch has just proved it is not there. -/

/-- The `-` scan: push, emit, advance. -/
private lemma scanBlockEntry_col_succ {s s' : ScannerState} (hpk : s.peek? = some '-')
    (hok : scanBlockEntry s = .ok s') : s'.col = s.col + 1 := by
  have step : ∀ (t : ScannerState), t.col = s.col → t.peek? = s.peek? →
      ((t.emit .blockEntry).advance).col = s.col + 1 := by
    intro t hc hp
    rw [advance_col_succ_of_peek (c := '-')
      (show (t.emit YamlToken.blockEntry).peek? = some '-' by
        rw [show (t.emit YamlToken.blockEntry).peek? = t.peek? from rfl, hp]; exact hpk)
      (by decide)]
    rw [show (t.emit YamlToken.blockEntry).col = t.col from rfl, hc]
  have hpush : ∀ (col : Int), (pushSequenceIndent s col).col = s.col ∧
      (pushSequenceIndent s col).peek? = s.peek? := by
    intro col; unfold pushSequenceIndent; split <;> exact ⟨rfl, rfl⟩
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       show (ScannerState.advance (ScannerState.emit _ _)).col = _
       first | exact step _ (hpush _).1 (hpush _).2 | exact step s rfl rfl)
    | simp_all

/-- The `?` scan: the same shape, one token over. -/
private lemma scanKey_col_succ {s s' : ScannerState} (hpk : s.peek? = some '?')
    (hok : scanKey s = .ok s') : s'.col = s.col + 1 := by
  have step : ∀ (t : ScannerState), t.col = s.col → t.peek? = s.peek? →
      ((t.emit .key).advance).col = s.col + 1 := by
    intro t hc hp
    rw [advance_col_succ_of_peek (c := '?')
      (show (t.emit YamlToken.key).peek? = some '?' by
        rw [show (t.emit YamlToken.key).peek? = t.peek? from rfl, hp]; exact hpk)
      (by decide)]
    rw [show (t.emit YamlToken.key).col = t.col from rfl, hc]
  have hpush : ∀ (col : Int), (pushMappingIndent s col).col = s.col ∧
      (pushMappingIndent s col).peek? = s.peek? := by
    intro col; unfold pushMappingIndent; repeat (first | exact ⟨rfl, rfl⟩ | split)
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       show (ScannerState.advance (ScannerState.emit _ _)).col = _
       first | exact step _ (hpush _).1 (hpush _).2 | exact step s rfl rfl)
    | simp_all

/-- The `:` scan: `scanValueClearKey` and `scanValuePrepare` write tokens,
    indents and the pending key — never the cursor — so the advance is still
    the only motion. -/
private lemma scanValue_col_succ {s s' : ScannerState} (hpk : s.peek? = some ':')
    (hok : scanValue s = .ok s') : s'.col = s.col + 1 := by
  have step : ∀ (t : ScannerState), t.col = s.col → t.peek? = s.peek? →
      ((t.emit .value).advance).col = s.col + 1 := by
    intro t hc hp
    rw [advance_col_succ_of_peek (c := ':')
      (show (t.emit YamlToken.value).peek? = some ':' by
        rw [show (t.emit YamlToken.value).peek? = t.peek? from rfl, hp]; exact hpk)
      (by decide)]
    rw [show (t.emit YamlToken.value).col = t.col from rfl, hc]
  have hclear : ∀ (t : ScannerState), (scanValueClearKey t).col = t.col ∧
      (scanValueClearKey t).peek? = t.peek? := by
    intro t; unfold scanValueClearKey; repeat (first | exact ⟨rfl, rfl⟩ | split)
  have hprep : ∀ (t : ScannerState), (scanValuePrepare t).col = t.col ∧
      (scanValuePrepare t).peek? = t.peek? := by
    intro t; unfold scanValuePrepare pushMappingIndent
    repeat (first | exact ⟨rfl, rfl⟩ | split)
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       show (ScannerState.advance (ScannerState.emit _ _)).col = _
       exact step _ (by rw [(hprep _).1, (hclear s).1]) (by rw [(hprep _).2, (hclear s).2]))
    | simp_all

/-- **The block indicator spends a column** (item 206), so the park it opens is
    never at a line start.  `dispatchContent_nic_or_col_any`'s twin for the
    OTHER dispatcher, and a strictly simpler statement: the content scans
    needed a disjunction because one of them crosses breaks, and none of these
    three does. -/
lemma dispatchBlockIndicators_col_pos {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    0 < s'.col := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i hg
    have hc : c = '-' := by
      have := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).1
      simpa using this
    subst hc
    split at hok
    · simp at hok
    · rename_i se he
      simp only [Except.ok.injEq, Option.some.injEq] at hok
      subst hok
      rw [scanBlockEntry_col_succ hpk he]; omega
  · split at hok
    · rename_i hg
      have hc : c = '?' := by
        have := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp hg).1).1).1
        simpa using this
      subst hc
      split at hok
      · simp at hok
      · rename_i se he
        simp only [Except.ok.injEq, Option.some.injEq] at hok
        subst hok
        rw [scanKey_col_succ hpk he]; omega
    · split at hok
      · rename_i hg
        have hc : c = ':' := by
          have := (Bool.and_eq_true_iff.mp hg).1
          simpa using this
        subst hc
        split at hok
        · simp at hok
        · rename_i se he
          simp only [Except.ok.injEq, Option.some.injEq] at hok
          subst hok
          rw [scanValue_col_succ hpk he]; omega
      · simp at hok

/-- **…and it re-establishes the real final slot** (item 221).

    `FlowAdjacency.LastTokenReal`'s own docstring says "every emitting dispatch
    re-establishes this; only `saveSimpleKey` can break it", and nothing stated
    it.  The block indicator's three scans all end the same way — emit the
    indicator token, then advance over its one character — so the slot the
    dispatch leaves holds a `-`, `?` or `:` and never a reservation
    placeholder.

    `pendingBlock` is the one block-context park that carries no `h_real`
    (`pendingDocStart`, `pendingMapValue` and `pendingProps` all do), which is
    why item 220's census read `pendingBlock ⊆ pendingMapValue` as an invariant
    with a separating state rather than an entailment.  This is the fact that
    closes it, and the ONLY one of item 220's five residuals that needed a new
    scanner lemma at all. -/
private lemma emit_advance_lastTokenReal (t : ScannerState) (tok : YamlToken)
    (h : tok ≠ .placeholder) :
    FlowAdjacency.LastTokenReal ((t.emit tok).advance).tokens := by
  rw [ScannerCorrectness.advance_preserves_tokens]
  exact FlowAdjacency.lastTokenReal_push (p := { pos := t.currentPos, val := tok }) h

/-- The `-` scan's final slot. -/
private lemma scanBlockEntry_lastTokenReal {s s' : ScannerState}
    (hok : scanBlockEntry s = .ok s') : FlowAdjacency.LastTokenReal s'.tokens := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       exact emit_advance_lastTokenReal _ _ (by decide))
    | simp_all

/-- The `?` scan's. -/
private lemma scanKey_lastTokenReal {s s' : ScannerState}
    (hok : scanKey s = .ok s') : FlowAdjacency.LastTokenReal s'.tokens := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       exact emit_advance_lastTokenReal _ _ (by decide))
    | simp_all

/-- The `:` scan's — `scanValueClearKey` and `scanValuePrepare` write the
    pending key and the indents, and the emit is still the last write to the
    array. -/
private lemma scanValue_lastTokenReal {s s' : ScannerState}
    (hok : scanValue s = .ok s') : FlowAdjacency.LastTokenReal s'.tokens := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       exact emit_advance_lastTokenReal _ _ (by decide))
    | simp_all

/-- `dispatchBlockIndicators_col_pos`'s twin for the token array. -/
lemma dispatchBlockIndicators_lastTokenReal {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    FlowAdjacency.LastTokenReal s'.tokens := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq, Option.some.injEq] at hok
       subst hok
       first
         | exact scanBlockEntry_lastTokenReal ‹_›
         | exact scanKey_lastTokenReal ‹_›
         | exact scanValue_lastTokenReal ‹_›)
    | simp_all

/-- The block-scalar arm's `OffLine` form (item 47): with `c` pinned at a
    block-scalar head, the dispatch is `scanBlockScalar` under the item-9c
    guard, and the scan ends at a line start or an `OffLine` stop — which is
    what refutes an inline `:` after a block-scalar park. -/
lemma dispatchContent_blockScalar_restOffLine {s s' : ScannerState} {c : Char}
    (hbs : c = '|' ∨ c = '>')
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.col = 0 ∨ RestStop OffLine s' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i heq
    have : c = '&' := by simpa using heq
    rcases hbs with rfl | rfl <;> simp at this
  split at hok
  · rename_i heq
    have : c = '*' := by simpa using heq
    rcases hbs with rfl | rfl <;> simp at this
  split at hok
  · rename_i heq
    have : c = '!' := by simpa using heq
    rcases hbs with rfl | rfl <;> simp at this
  split at hok
  · exact scanBlockScalar_restOffLine hend' (peel_blockScalarGuard hok)
  · rename_i heq
    rcases hbs with rfl | rfl <;> simp at heq

/-- Item 10's dispatch-level conclusion, one `mono` below §9's own. -/
lemma dispatchContent_restNoOpen {s s' : ScannerState} {c : Char}
    (hflow : s.inFlow = false)
    (hna : c ≠ '&') (hnt : c ≠ '!')
    (hend' : s'.inputEnd = s'.input.utf8ByteSize)
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.col = 0 ∨ RestNoOpen s' :=
  (dispatchContent_restNodeStop hflow hna hnt hend' hok).imp id
    (RestStop.mono (fun _ => NodeStop.toNoOpenHead))

/-- A character outside `[204]`/§7.5's stop families, except the `:` — the
    component form `dispatchContent_ok_charFacts` supplies branchwise. -/
private lemma nodeStop_colon_of_class {c : Char}
    (hhash : c ≠ '#') (hbr : isLineBreakBool c = false)
    (hp : isPrintableBool c = true) (hbom : c ≠ '﻿') :
    NodeStop c → c = ':' := by
  rintro (((hb | hh) | hc) | (hn | hb2))
  · rw [hbr] at hb; cases hb
  · exact absurd hh hhash
  · exact hc
  · rw [hp] at hn; cases hn
  · exact absurd hb2 hbom

/-- **The dispatch's own character class** (item 42).  A content dispatch that
    returns `.ok` read one of the seven construct heads (`&`, `*`, `!`, `|`,
    `>`, `"`, `'`) or a `[126] ns-plain-first` character.  None of these is
    white or a break, and the only one `NodeStop` admits is the `:` whose
    follower is non-blank (`[126]`'s exception list) — a `#`, a non-printable
    and the BOM are all refused by the dispatch itself (`unexpectedChar`), so
    the question item 36 answered with `commentOk` never has to be asked: a
    park whose line stops at `TailSuffix` hands this dispatch NO same-line
    character at all, and one whose line stops at `NodeStop` hands it exactly
    `[154]`'s `:`. -/
lemma dispatchContent_ok_charFacts {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    ¬(c = ' ' ∨ c = '\t') ∧ (NodeStop c → c = ':') := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq
    have hc : c = '&' := by simpa using h_eq
    subst hc
    exact ⟨by decide, nodeStop_colon_of_class (by decide) (by decide) (by decide) (by decide)⟩
  · split at hok
    · rename_i h_eq
      have hc : c = '*' := by simpa using h_eq
      subst hc
      exact ⟨by decide, nodeStop_colon_of_class (by decide) (by decide) (by decide) (by decide)⟩
    · split at hok
      · rename_i h_eq
        have hc : c = '!' := by simpa using h_eq
        subst hc
        exact ⟨by decide, nodeStop_colon_of_class (by decide) (by decide) (by decide) (by decide)⟩
      · split at hok
        · rename_i h_eq
          have hc : c = '|' ∨ c = '>' := by simpa using h_eq
          rcases hc with rfl | rfl <;>
            exact ⟨by decide, nodeStop_colon_of_class (by decide) (by decide) (by decide) (by decide)⟩
        · split at hok
          · rename_i h_eq
            have hc : c = '"' := by simpa using h_eq
            subst hc
            exact ⟨by decide, nodeStop_colon_of_class (by decide) (by decide) (by decide) (by decide)⟩
          · split at hok
            · rename_i h_eq
              have hc : c = '\'' := by simpa using h_eq
              subst hc
              exact ⟨by decide, nodeStop_colon_of_class (by decide) (by decide) (by decide) (by decide)⟩
            · split at hok
              · rename_i h_can
                unfold canStartPlainScalarBool at h_can
                split at h_can
                · rename_i h3
                  refine ⟨by rcases h3 with rfl | rfl | rfl <;> decide, ?_⟩
                  intro h
                  rcases h3 with rfl | rfl | rfl
                  · exact (NodeStop.not_dash_or_question h (Or.inl rfl)).elim
                  · exact (NodeStop.not_dash_or_question h (Or.inr rfl)).elim
                  · rfl
                · simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h_can
                  obtain ⟨⟨⟨⟨hind, hws⟩, hbr⟩, hp⟩, hbom⟩ := h_can
                  refine ⟨?_, nodeStop_colon_of_class ?_ hbr hp hbom⟩
                  · rintro (rfl | rfl) <;> exact absurd hws (by decide)
                  · rintro rfl; exact absurd hind (by decide)
              · simp at hok

/-- `[204]`'s reading of the same fact: the dispatch never returns `.ok` on a
    `TailSuffix` character (a break or a `#`). -/
lemma dispatchContent_ok_not_tailSuffix {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (hts : TailSuffix c) : False := by
  have hc := (dispatchContent_ok_charFacts hok).2 hts.toNodeTail.toNodeStop
  subst hc
  rcases hts with hb | hh
  · exact absurd hb (by decide)
  · exact absurd hh (by decide)

end L4YAML.Proofs.LineOpenGuard

end Blanket
