/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.FlowIndentStable
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-!
# The indent stack's base (DOCS item 128)

`ScannerState.WellFormed`'s sixth conjunct says the stack's bottom entry is the
sentinel `{ column := -1, isSequence := false }`, and the scanner's own state
OPERATIONS preserve it — `advance`, `emit`, `emitAt`, `saveSimpleKey` and the two
pushes, in `ScannerLoopInvariant` / `ScannerScalar` / `ScannerSimpleKey` /
`ScannerIndentStack`.  What is missing is a form the PRODUCTION side can hold:
`scanNextToken`'s own preservation is `ScannerDispatch` §7, which is
`#guard`-first by design (the concrete checks live in the guard tree's twin), and
a proof about an arbitrary accumulation state cannot spend a check on a concrete
state.  So no proof downstream of the scanner has a route to the sentinel.

This file carries the sixth conjunct alone — as `SentinelBase`, a statement
about `indents[0]?` — through every scanner step, in the shape the two other
whole-scanner field walks use (`ScannerFlowStackPreservation`,
`ScannerEkStackPreservation`).  The stack is touched in exactly four places
(`pushMappingIndent`, `pushSequenceIndent`, `unwindIndentsLoop` and
`scanValuePrepare`'s own `push`), and each preserves index 0: a push writes
past the end, and the unwind's guard stops at size 1.  Every other step is an
`indents` equation, so §3 supplies the ones the existing files lacked and §4–§5
assemble the walk.

**What it buys** (item 127's named escape).  `preprocess_landing_at_level` reads
a popping landing's column off the top entry, and had to carry
`s_prep.indents.size ≤ 1` as a disjunct: a stack popped to one entry rests on
something the accumulation could not name.  With the base it can — a lone entry
is the sentinel, at `-1`, and no landing column is negative — so the landing is
an equation outright.  The runtime agrees for the family the escape describes:
an indented root pushes at its own column over the sentinel, and a landing to
its left is `trailingContent` (`  a: 1⏎b: 2`, `  - x⏎y: 1`, `  a:⏎    b: 1⏎c: 2`),
pinned in `Tests/Guards/Proofs/IndentBaseThreaded.lean`.

§1 the predicate and its two consequences.  §2 the four stack writers.  §3 the
`indents` equations the earlier walks did not need (the directive chain, the
block-scalar chain, `advanceN`, `skipToEndOfLine`, the document-end whites).
§4 the steps that move the stack.  §5 the five `scanNextToken` stages and the
step itself.  §6 the seed.
-/

namespace L4YAML.Proofs.IndentStackBase

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.FlowIndentStable
open L4YAML.Proofs.ScannerWhitespace

/-! ## §1  The predicate -/

/-- **The indent stack's base**: the bottom entry is the sentinel.  This is
    `ScannerState.WellFormed`'s sixth conjunct, packaged so that it carries its
    own non-emptiness (`getElem?` at 0 is `none` on an empty stack). -/
def SentinelBase (s : ScannerState) : Prop :=
  s.indents[0]? = some { column := -1, isSequence := false }

lemma SentinelBase.size_pos {s : ScannerState} (h : SentinelBase s) :
    0 < s.indents.size := by
  rcases Nat.eq_zero_or_pos s.indents.size with hz | hp
  · rw [SentinelBase, Array.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  · exact hp

/-- A step that leaves the stack alone carries the base. -/
lemma SentinelBase.of_indents_eq {s s' : ScannerState} (h : SentinelBase s)
    (heq : s'.indents = s.indents) : SentinelBase s' := by
  rw [SentinelBase, heq]; exact h

/-- **The escape's refutation** (item 127): a stack popped to its base sits at
    `-1`, which no column reaches. -/
lemma SentinelBase.currentIndent_of_size_le_one {s : ScannerState}
    (h : SentinelBase s) (hsz : s.indents.size ≤ 1) : s.currentIndent = -1 := by
  have hpos := h.size_pos
  have hone : s.indents.size = 1 := by omega
  have hback : s.indents.back? = s.indents[0]? := by
    rw [Array.back?_eq_getElem?, hone]
  simp only [ScannerState.currentIndent, hback]
  rw [show s.indents[0]? = some { column := -1, isSequence := false } from h]

/-! ## §2  The four stack writers

    A push writes past the end and the unwind's guard stops at size 1, so index
    0 survives both. -/

lemma base_pop {a : Array IndentEntry} (h : 1 < a.size) : a.pop[0]? = a[0]? := by
  rw [Array.getElem?_eq_getElem (by omega : 0 < a.size),
      Array.getElem?_eq_getElem (by simp; omega : 0 < a.pop.size)]
  simp [Array.getElem_pop]

lemma base_push {a : Array IndentEntry} {x : IndentEntry} (h : 0 < a.size) :
    (a.push x)[0]? = a[0]? := by
  rw [Array.getElem?_eq_getElem h,
      Array.getElem?_eq_getElem (by simp : 0 < (a.push x).size)]
  rw [Array.getElem_push_lt h]

lemma unwindIndentsLoop_base (s : ScannerState) (col : Int) (fuel : Nat)
    (h : SentinelBase s) : SentinelBase (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; exact h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · rename_i hguard
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
      refine ih _ ?_
      show ((s.emit .blockEnd).indents.pop)[0]? = _
      rw [emit_indents, base_pop hguard.2]
      exact h
    · exact h

lemma unwindIndents_base (s : ScannerState) (col : Int) (h : SentinelBase s) :
    SentinelBase (unwindIndents s col) :=
  unwindIndentsLoop_base s col s.indents.size h

lemma pushMappingIndent_base (s : ScannerState) (col : Int) (h : SentinelBase s) :
    SentinelBase (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · show (s.indents.push _)[0]? = _
    rw [base_push h.size_pos]; exact h
  · exact h

lemma pushSequenceIndent_base (s : ScannerState) (col : Int) (h : SentinelBase s) :
    SentinelBase (pushSequenceIndent s col) := by
  unfold pushSequenceIndent
  split
  · show (s.indents.push _)[0]? = _
    rw [base_push h.size_pos]; exact h
  · exact h

/-! ## §3  The `indents` equations the earlier walks did not need

    Cloned from the `_preserves_flowStack` / `_preserves_explicitKeyStack`
    twins, which walk the same functions for the two other stacks. -/

lemma advanceNLoop_preserves_indents (s : ScannerState) (n : Nat) :
    (s.advanceNLoop n).indents = s.indents := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; rfl
  | succ _ ih =>
    unfold ScannerState.advanceNLoop
    exact (ih s.advance).trans (ScannerLoopInvariant.advance_indents s)

lemma advanceN_preserves_indents (s : ScannerState) (n : Nat) :
    (s.advanceN n).indents = s.indents := by
  unfold ScannerState.advanceN; exact advanceNLoop_preserves_indents s n

lemma skipToEndOfLineLoop_preserves_indents (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).indents = s.indents := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop
    split
    · split
      · rfl
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
    · rfl

lemma skipToEndOfLine_preserves_indents (s : ScannerState) :
    (skipToEndOfLine s).indents = s.indents := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_indents s _

lemma collectDirectiveNameLoop_preserves_indents (s : ScannerState) (name : String)
    (fuel : Nat) : (collectDirectiveNameLoop s name fuel).snd.indents = s.indents := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ _ ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
      · rfl
    · rfl

lemma collectVersionMajorLoop_preserves_indents (s : ScannerState) (major : String)
    (fuel : Nat) : (collectVersionMajorLoop s major fuel).snd.indents = s.indents := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ _ ih =>
    unfold collectVersionMajorLoop; split
    · exact ScannerLoopInvariant.advance_indents s
    · split
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
      · rfl
    · rfl

lemma collectVersionMinorLoop_preserves_indents (s : ScannerState) (minor : String)
    (fuel : Nat) : (collectVersionMinorLoop s minor fuel).snd.indents = s.indents := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ _ ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
      · rfl
    · rfl

lemma collectTagHandleDirectiveLoop_preserves_indents (s : ScannerState) (handle : String)
    (fuel : Nat) : (collectTagHandleDirectiveLoop s handle fuel).snd.indents = s.indents := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ _ ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
      · rfl
    · rfl

lemma collectTagPrefixLoop_preserves_indents (s : ScannerState) (pfx : String)
    (fuel : Nat) : (collectTagPrefixLoop s pfx fuel).snd.indents = s.indents := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ _ ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
      · rfl
    · rfl

lemma parseBlockHeaderLoop_preserves_indents (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.indents = s.indents := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ _ ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact ScannerLoopInvariant.advance_indents s
    · rw [ih]; exact ScannerLoopInvariant.advance_indents s
    · split
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
      · rfl
    · rfl

lemma consumeExactSpaces_preserves_indents (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.indents = s.indents := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ _ ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact ScannerLoopInvariant.advance_indents s
    · rfl

lemma collectLineContentLoop_preserves_indents (s : ScannerState) (content : String)
    (fuel : Nat) : (collectLineContentLoop s content fuel).snd.indents = s.indents := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ _ ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
    · rfl

lemma collectBlockScalarLoop_preserves_indents (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.indents
      = s.indents := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ _ ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_indents s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_indents, consumeExactSpaces_preserves_indents]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_indents,
                    collectLineContentLoop_preserves_indents,
                    consumeExactSpaces_preserves_indents]
              · split
                · rfl
                · rw [collectLineContentLoop_preserves_indents,
                    consumeExactSpaces_preserves_indents]
            · rw [collectLineContentLoop_preserves_indents,
                  consumeExactSpaces_preserves_indents]

lemma skipDocEndWhitespace_preserves_indents (s : ScannerState) (fuel : Nat) :
    (skipDocEndWhitespace s fuel).indents = s.indents := by
  induction fuel generalizing s with
  | zero => unfold skipDocEndWhitespace; rfl
  | succ _ ih =>
    unfold skipDocEndWhitespace
    split
    · split
      · rw [ih]; exact ScannerLoopInvariant.advance_indents s
      · rfl
    · rfl

lemma scanBlockScalarSkipComment_preserves_indents (s : ScannerState) :
    (scanBlockScalarSkipComment s).indents = s.indents := by
  unfold scanBlockScalarSkipComment
  split
  · split
    · dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_indents, ScannerLoopInvariant.advance_indents]
      · rfl
    · rfl
  · rfl

lemma scanBlockScalarConsumeNewline_preserves_indents {s s' : ScannerState}
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.indents = s.indents := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_indents s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

lemma scanBlockScalarBody_preserves_indents {s_orig s_nl s' : ScannerState}
    {chomp : ChompStyle} {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (h_ids : s_nl.indents = s_orig.indents)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.indents = s_orig.indents := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_indents, collectBlockScalarLoop_preserves_indents, h_ids]

lemma scanBlockScalar_preserves_indents {s s' : ScannerState}
    (h : scanBlockScalar s = .ok s') : s'.indents = s.indents := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_indents
      (by rw [scanBlockScalarConsumeNewline_preserves_indents (by assumption),
              scanBlockScalarSkipComment_preserves_indents,
              skipWhitespace_preserves_indents,
              parseBlockHeaderLoop_preserves_indents,
              ScannerLoopInvariant.advance_indents]) h

lemma scanDirective_preserves_indents {s s' : ScannerState}
    (h : scanDirective s = .ok s') : s'.indents = s.indents := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_preserves_indents]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [emitAt_indents, skipWhitespace_preserves_indents,
              collectVersionMinorLoop_preserves_indents,
              collectVersionMajorLoop_preserves_indents])
        all_goals (rw [collectDirectiveNameLoop_preserves_indents,
                       ScannerLoopInvariant.advance_indents])
      · contradiction
    · split at h
      · split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_preserves_indents]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner
          · contradiction  -- [89]: a malformed `%TAG` handle is refused
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [emitAt_indents, collectTagPrefixLoop_preserves_indents,
                skipWhitespace_preserves_indents,
                collectTagHandleDirectiveLoop_preserves_indents,
                collectDirectiveNameLoop_preserves_indents,
                ScannerLoopInvariant.advance_indents]
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_preserves_indents, skipWhitespace_preserves_indents,
              collectDirectiveNameLoop_preserves_indents,
              ScannerLoopInvariant.advance_indents]

/-! ## §4  The steps that move the stack -/

lemma scanDocumentStart_base (s : ScannerState) (h : SentinelBase s) :
    SentinelBase (scanDocumentStart s) := by
  refine SentinelBase.of_indents_eq (unwindIndents_base s (-1) h) ?_
  unfold scanDocumentStart
  simp [advanceN_preserves_indents, emit_indents]

lemma scanDocumentEnd_base {s s' : ScannerState} (hok : scanDocumentEnd s = .ok s')
    (h : SentinelBase s) : SentinelBase s' := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals
    refine SentinelBase.of_indents_eq (unwindIndents_base s (-1) h) ?_
  all_goals simp [advanceN_preserves_indents, emit_indents]

/-- In BLOCK context the `?` pushes a mapping level at its own column
    (`scanKey_indents`), and the push keeps the base.  The flow context needs no
    arm of its own: `dispatchBlockIndicators_preserves_indents` covers the whole
    dispatcher there. -/
lemma scanKey_base {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanKey s = .ok s') (h : SentinelBase s) : SentinelBase s' :=
  SentinelBase.of_indents_eq (pushMappingIndent_base s (s.col : Int) h)
    (scanKey_indents h_noflow hok)

/-- …and the `-` pushes a sequence level, the same way. -/
lemma scanBlockEntry_base {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanBlockEntry s = .ok s') (h : SentinelBase s) : SentinelBase s' :=
  SentinelBase.of_indents_eq (pushSequenceIndent_base s (s.col : Int) h)
    (scanBlockEntry_indents h_noflow hok)

lemma scanValuePrepare_base (s : ScannerState) (h : SentinelBase s) :
    SentinelBase (scanValuePrepare s) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · show (s.indents.push _)[0]? = _
        rw [base_push h.size_pos]; exact h
      · exact h
    · exact h
  · split
    · exact h
    · split
      · exact pushMappingIndent_base s s.col h
      · exact h

lemma scanValue_base {s s' : ScannerState} (hok : scanValue s = .ok s')
    (h : SentinelBase s) : SentinelBase s' := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok; subst hok
  have h_ck : (scanValueClearKey s).indents = s.indents := by
    unfold scanValueClearKey; split
    · split
      · rfl
      · split <;> rfl
    · rfl
  refine SentinelBase.of_indents_eq
    (scanValuePrepare_base _ (h.of_indents_eq h_ck)) ?_
  simp [ScannerLoopInvariant.advance_indents, emit_indents]

/-! ## §5  The five stages, and the step -/

lemma preprocess_base {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : SentinelBase s) :
    SentinelBase s' := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have h_skip_ids : s_skip.indents = s.indents :=
      skipToContent_preserves_indents s s_skip h_skip
    have h_c : SentinelBase s_skip := h.of_indents_eq h_skip_ids
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, _⟩ := hok
            refine SentinelBase.of_indents_eq ?_ ((closeStaleExplicitKey_indents _).trans (saveSimpleKey_preserves_indents _))
            show SentinelBase { unwindIndents s_skip (s_skip.col : Int) with
              needIndentCheck := false }
            exact SentinelBase.of_indents_eq
              (unwindIndents_base s_skip (s_skip.col : Int) h_c) rfl
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, _⟩ := hok
            exact SentinelBase.of_indents_eq h_c ((closeStaleExplicitKey_indents _).trans (saveSimpleKey_preserves_indents _))

lemma dispatchStructural_base {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchStructural s c = .ok (some s')) (h : SentinelBase s) :
    SentinelBase s' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_base s h
    | exact scanDocumentEnd_base (by assumption) h
    | exact SentinelBase.of_indents_eq h (scanDirective_preserves_indents (by assumption))

lemma dispatchFlowIndicators_base {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (h : SentinelBase s) :
    SentinelBase s' :=
  h.of_indents_eq (dispatchFlowIndicators_preserves_indents hok)

lemma dispatchBlockIndicators_base {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) (h : SentinelBase s) :
    SentinelBase s' := by
  by_cases hf : s.inFlow = true
  · exact h.of_indents_eq (dispatchBlockIndicators_preserves_indents hf hok)
  · have h_noflow : s.inFlow = false := by simpa using hf
    unfold scanNextToken_dispatchBlockIndicators at hok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
    repeat (any_goals (split at hok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    all_goals first
      | exact scanBlockEntry_base h_noflow (by assumption) h
      | exact scanKey_base h_noflow (by assumption) h
      | exact scanValue_base (by assumption) h

/-- The content dispatch writes tokens, never the indent stack: a scalar, an
    anchor, an alias and a tag all leave the block structure alone.  (Item 129
    reads the same equation for the frames' cover, so it is stated once here
    rather than inlined into the base's own arm.) -/
lemma dispatchContent_preserves_indents {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') : s'.indents = s.indents := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · split at hok
    · simp at hok
    generalize h_fn : scanAnchorOrAlias s true = result at hok
    cases result with
    | error e => simp at hok
    | ok s_a =>
      simp only [Except.ok.injEq] at hok; subst hok; dsimp only []
      exact scanAnchorOrAlias_preserves_indents h_fn
  · split at hok
    · split at hok
      · simp at hok
      split at hok
      · simp at hok
      · replace hok := aliasArm_scan_ok hok
        generalize h_fn : scanAnchorOrAlias s false = result at hok
        cases result with
        | error e => simp at hok
        | ok s_a =>
          simp only [Except.ok.injEq] at hok; subst hok
          exact scanAnchorOrAlias_preserves_indents h_fn
    · split at hok
      · split at hok
        · simp at hok
        generalize h_fn : scanTag s = result at hok
        cases result with
        | error e => simp at hok
        | ok s_t =>
          simp only [Except.ok.injEq] at hok; subst hok
          exact scanTag_preserves_indents h_fn
      · repeat (any_goals (split at hok))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_indents (by assumption)
          | exact EmitterScannability.scanDoubleQuoted_preserves_indents _ _ (by assumption)
          | exact scanSingleQuoted_preserves_indents (by assumption)
          | exact scanPlainScalar_preserves_indents (by assumption)
          | (simp_all; done)

lemma dispatchContent_base {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') (h : SentinelBase s) :
    SentinelBase s' :=
  h.of_indents_eq (dispatchContent_preserves_indents hok)

/-- **The step preserves the base.**  The four writers are the only ones that
    touch the stack, and each keeps index 0. -/
lemma scanNextToken_base {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : SentinelBase s) : SentinelBase s' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp at hok
    · rename_i sp c h_pre
      have h_pp : SentinelBase sp := preprocess_base h_pre h
      -- §9.2 dangling-node check (item 133)
      split at hok
      · cases hok
      -- §8.1 flow-value floor (item 172)
      split at hok
      · cases hok
      split at hok
      · cases hok
      · split at hok
        · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
          exact dispatchStructural_base ‹_› h_pp
        · split at hok
          · cases hok
          -- §9.2 bare-document check (item 132)
          split at hok
          · cases hok
          · -- The directive flag's own record update, which the stack
            -- does not see (`ScannerState.WellFormed`'s conjuncts split the
            -- same way — see `StaleCursorFloor`'s skeleton).
            rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at hok
            · generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_base h_fi h_pp
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_base h_bi h_pp
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_base h_dc h_pp
            · generalize h_sp2 :
                (({ sp with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at hok
              have h_pp2 : SentinelBase sp2 := by rw [← h_sp2]; exact h_pp
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_base h_fi h_pp2
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_base h_bi h_pp2
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp2 c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp2 c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_base h_dc h_pp2

/-! ## §6  The seed -/

/-- The initial state's stack IS the sentinel. -/
lemma mk'_base (input : String) : SentinelBase (ScannerState.mk' input) := rfl

end L4YAML.Proofs.IndentStackBase

end Blanket
