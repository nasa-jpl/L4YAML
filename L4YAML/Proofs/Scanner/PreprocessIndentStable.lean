/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerWhitespace
public import L4YAML.Proofs.Scanner.ScannerLoopInvariant
public import L4YAML.Proofs.Scanner.ScannerLinePreservation

@[expose] public section Blanket

/-!
# The indent stack across preprocessing (DOCS item 27)

Item 26 left the indented block scalar one inequality short of composing:
`[170] c-l+literal(n)` reads at every `n ≤ d`, where `d` is the indent the
scanner collected the body at, and the scanner's own floor for `d` is
`(max 0 (currentIndent + 1)).toNat` — so the accumulator owes
`(n : Int) ≤ currentIndent + 1` for the entry index it parked.  That is true of
every accepted input and was unstatable, because `currentIndent` occurred in the
accumulation invariant exactly zero times.

Carrying it on the pending is only half the job: the pending is parked at the
INDICATOR's state and consumed at the VALUE's, one preprocessing step later, so
the fact has to survive `scanNextToken_preprocess`.  It does not survive
unconditionally — that is what `unwindIndents` is for — but it survives exactly
when the step crossed no break, which is the same discriminant every other
break-free reading in `StreamAccum` already splits on:

    scanNextToken_preprocess s
      = skipToContent s ⟩⟩ (if !inFlow && needIndentCheck then unwindIndents … else id)
        ⟩⟩ saveSimpleKey

`skipToContent` never touches `indents` (it only walks the cursor and raises
`needIndentCheck`), and `saveSimpleKey` only pushes tokens — so the ONLY writer
is the armed `unwindIndents`, and the arming flag is `s_content.needIndentCheck`.
This module proves the walk half of that (`skipToContent_preserves_indents`, by
the mechanical descent the `_preserves_flowLevel` family already makes over the
same five functions) and then the preprocessing statement conditioned on the
flag being down at the point of the test.

Kept out of `ScannerCorrectness` deliberately: that module is imported by
essentially everything, and this is a leaf the accumulator alone reads.
-/

namespace L4YAML.Proofs.PreprocessIndentStable

open L4YAML.Scanner
open L4YAML.Proofs.ScannerWhitespace
open L4YAML.Proofs.ScannerLoopInvariant

/-! ## §1  The walk never writes the indent stack

Five functions, each mirroring its `_preserves_flowLevel` sibling in
`ScannerCorrectness`.  `indents` and `flowLevel` are both plain fields of
`ScannerState` and neither is read by any of these, so the proof scripts are the
same descent. -/

/-- `skipSpacesLoop` only advances. -/
lemma skipSpacesLoop_preserves_indents (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).indents = s.indents := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' ih =>
    unfold skipSpacesLoop
    split
    · rw [ih, advance_indents]
    · rfl

/-- `skipSpaces` — `s-space*`, `[63] s-indent(n)`'s consumer. -/
lemma skipSpaces_preserves_indents (s : ScannerState) :
    (skipSpaces s).indents = s.indents := skipSpacesLoop_preserves_indents s _

/-- `skipWhitespaceLoop` only advances. -/
lemma skipWhitespaceLoop_preserves_indents (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).indents = s.indents := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' ih =>
    unfold skipWhitespaceLoop
    split
    · split
      · rw [ih, advance_indents]
      · rfl
    · rfl

/-- `skipWhitespace` — `s-white*`, `[66] s-separate-in-line`'s consumer. -/
lemma skipWhitespace_preserves_indents (s : ScannerState) :
    (skipWhitespace s).indents = s.indents := skipWhitespaceLoop_preserves_indents s _

/-- `collectCommentTextLoop` advances and accumulates a string. -/
lemma collectCommentTextLoop_preserves_indents (s : ScannerState) (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.indents = s.indents := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' ih =>
    unfold collectCommentTextLoop
    split
    · split
      · rfl
      · rw [ih, advance_indents]
    · rfl

/-- `skipToContentComment` — `[75] c-nb-comment-text`; pushes a comment onto the
    side channel and nothing else. -/
lemma skipToContentComment_preserves_indents (s : ScannerState) :
    (skipToContentComment s).indents = s.indents := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_indents, advance_indents]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_indents, advance_indents]
      · rfl
  · rfl

/-- `skipToContentWs` — the tab-as-indentation gate READS `currentIndent` but
    never writes it; every successful exit is a `skipSpaces`/`skipWhitespace`
    composite. -/
lemma skipToContentWs_preserves_indents (s s' : ScannerState)
    (h : skipToContentWs s = .ok s') :
    s'.indents = s.indents := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h
          rw [← h, skipWhitespace_preserves_indents, skipSpaces_preserves_indents]
        · split at h
          · simp at h
            rw [← h, skipWhitespace_preserves_indents, skipSpaces_preserves_indents]
          · split at h
            · simp at h
              rw [← h, skipWhitespace_preserves_indents, skipSpaces_preserves_indents]
            · simp at h
        · simp at h
          rw [← h, skipWhitespace_preserves_indents, skipSpaces_preserves_indents]
      · simp at h
        rw [← h, skipSpaces_preserves_indents]
    · simp at h
      rw [← h, skipWhitespace_preserves_indents, skipSpaces_preserves_indents]
  · simp at h
    rw [← h, skipWhitespace_preserves_indents]

/-- `skipToContentLoop` — one `[79] s-l-comments` line per iteration. -/
lemma skipToContentLoop_preserves_indents (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.indents = s.indents := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · rw [ih _ h, consumeNewline_preserves_indents,
                skipToContentComment_preserves_indents]
            exact skipToContentWs_preserves_indents s s1 hws
          · rw [ih _ h, consumeNewline_preserves_indents,
                skipToContentComment_preserves_indents]
            exact skipToContentWs_preserves_indents s s1 hws
        · simp at h
          rw [← h, skipToContentComment_preserves_indents]
          exact skipToContentWs_preserves_indents s s1 hws
      · simp at h
        rw [← h, skipToContentComment_preserves_indents]
        exact skipToContentWs_preserves_indents s s1 hws

/-- **The walk half**: reaching the next content character never changes the
    indent stack.  Only `unwindIndents` does, and `skipToContent` does not call
    it — it merely raises `needIndentCheck` so that the caller will. -/
lemma skipToContent_preserves_indents (s s' : ScannerState)
    (h : skipToContent s = .ok s') :
    s'.indents = s.indents := by
  unfold skipToContent at h
  exact skipToContentLoop_preserves_indents s s' _ h

/-! ## §1b  What the unwind does to the stack (item 60)

The loop only POPS, and it stops as soon as the top is at or left of the
column it is unwinding to.  Two consequences are all the accumulator needs:
either nothing was popped and the stack is UNCHANGED, or the size strictly
dropped — which is the very condition preprocessing's own trailing-content
check tests, so an accepted input tells the caller which case it is in. -/

/-- The loop never grows the stack. -/
lemma unwindIndentsLoop_size_le (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).indents.size ≤ s.indents.size := by
  induction fuel generalizing s with
  | zero => simp [unwindIndentsLoop]
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · exact Nat.le_trans (ih _) (by simp [ScannerState.emit])
    · exact Nat.le_refl _

/-- …and it either popped something or left the stack alone. -/
lemma unwindIndentsLoop_shrink_or_eq (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).indents.size < s.indents.size ∨
      (unwindIndentsLoop s col fuel).indents = s.indents := by
  induction fuel generalizing s with
  | zero => exact Or.inr (by simp [unwindIndentsLoop])
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · rename_i hgo
      refine Or.inl (Nat.lt_of_le_of_lt (unwindIndentsLoop_size_le _ _ _) ?_)
      have h1 : 1 < s.indents.size := by
        have := (Bool.and_eq_true_iff.mp hgo).2
        simpa using this
      have he : (s.emit .blockEnd).indents = s.indents := by simp [ScannerState.emit]
      show (((s.emit .blockEnd).indents.pop)).size < s.indents.size
      rw [he, Array.size_pop]
      omega
    · exact Or.inr rfl

/-- The unwind moves no cursor: `col` is the column it unwinds TO, not one it
    writes. -/
lemma unwindIndentsLoop_col (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).col = s.col := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

lemma unwindIndents_col (s : ScannerState) (col : Int) :
    (unwindIndents s col).col = s.col :=
  unwindIndentsLoop_col s col s.indents.size

/-- The whole unwind, at the fuel the scanner gives it. -/
lemma unwindIndents_shrink_or_eq (s : ScannerState) (col : Int) :
    (unwindIndents s col).indents.size < s.indents.size ∨
      (unwindIndents s col).indents = s.indents :=
  unwindIndentsLoop_shrink_or_eq s col s.indents.size

/-! ## §1c  Where the unwind STOPS (item 127)

§1b says whether the loop popped.  This says where it came to rest, which is the
scanner half of the frames ↔ indent-stack coupling (DOCS's U3): the loop runs
until the top of the stack is at or left of the column it is unwinding to, so a
landing that popped anything and survived preprocessing's own trailing-content
check sits EXACTLY at an open level's column — not merely at or below one.  That
is stronger than the membership `ResumeFrames.resumeAt` asks for, and it is the
fact a coupled frames field would spend.

The one escape is the sentinel: a loop that pops to a one-entry stack rests on
`{ column := -1 }`, which no landing column can equal.  It is named here rather
than discharged, because ruling it out is a statement about the incoming stack
(`ScannerState.WellFormed`'s sixth conjunct) that the accumulation does not
carry. -/

/-- `e ∈ a.pop → e ∈ a`, for the indent stack. -/
lemma indents_mem_of_mem_pop {a : Array IndentEntry} {e : IndentEntry}
    (h : e ∈ a.pop) : e ∈ a := by
  rw [Array.mem_iff_getElem] at h ⊢
  obtain ⟨i, hi, hie⟩ := h
  exact ⟨i, by simpa using Nat.lt_of_lt_of_le hi (by simp), by simpa using hie⟩

/-- The loop stops on its own GUARD, not on its fuel, whenever it is given at
    least as much fuel as the stack has entries — each iteration pops one, and
    the guard already refuses to pop the last.  So the result satisfies the
    guard's negation: the top is at or left of `col`, or only the sentinel is
    left. -/
lemma unwindIndentsLoop_terminal (s : ScannerState) (col : Int) (fuel : Nat)
    (h_fuel : s.indents.size ≤ fuel) :
    (unwindIndentsLoop s col fuel).currentIndent ≤ col ∨
      (unwindIndentsLoop s col fuel).indents.size ≤ 1 := by
  induction fuel generalizing s with
  | zero =>
    right
    rw [show unwindIndentsLoop s col 0 = s by unfold unwindIndentsLoop; rfl]
    omega
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · rename_i hgo
      refine ih _ ?_
      have h1 : 1 < s.indents.size := by
        have := (Bool.and_eq_true_iff.mp hgo).2
        simpa using this
      show ((s.emit .blockEnd).indents.pop).size ≤ fuel
      have he : (s.emit .blockEnd).indents = s.indents := by simp [ScannerState.emit]
      rw [he, Array.size_pop]
      omega
    · rename_i hno
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hno
      by_cases h1 : 1 < s.indents.size
      · have hnot : ¬ (col < s.currentIndent) := fun hgt => hno hgt h1
        exact Or.inl (Int.not_lt.mp hnot)
      · exact Or.inr (by omega)

/-- The whole unwind, at the fuel the scanner gives it. -/
lemma unwindIndents_terminal (s : ScannerState) (col : Int) :
    (unwindIndents s col).currentIndent ≤ col ∨
      (unwindIndents s col).indents.size ≤ 1 :=
  unwindIndentsLoop_terminal s col s.indents.size (Nat.le_refl _)

/-- …and the level it rests on is one the incoming stack already held: the loop
    only pops, so its top is an entry of the stack it started from. -/
lemma unwindIndentsLoop_back_mem (s : ScannerState) (col : Int) (fuel : Nat)
    (e : IndentEntry) :
    (unwindIndentsLoop s col fuel).indents.back? = some e → e ∈ s.indents := by
  induction fuel generalizing s with
  | zero =>
    rw [show unwindIndentsLoop s col 0 = s by unfold unwindIndentsLoop; rfl]
    exact fun h => Array.mem_of_getElem? h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · intro h
      have hm := ih _ h
      have he : ({ s.emit .blockEnd with
          indents := (s.emit .blockEnd).indents.pop,
          pendingKeys := (s.emit .blockEnd).pendingKeys.pop } : ScannerState).indents
          = s.indents.pop := by simp [ScannerState.emit]
      rw [he] at hm
      exact indents_mem_of_mem_pop hm
    · exact fun h => Array.mem_of_getElem? h

lemma unwindIndents_back_mem (s : ScannerState) (col : Int) (e : IndentEntry) :
    (unwindIndents s col).indents.back? = some e → e ∈ s.indents :=
  unwindIndentsLoop_back_mem s col s.indents.size e

/-- …and EVERY entry it leaves was on the incoming stack — the loop only pops. -/
lemma unwindIndentsLoop_mem (s : ScannerState) (col : Int) (fuel : Nat)
    (e : IndentEntry) :
    e ∈ (unwindIndentsLoop s col fuel).indents → e ∈ s.indents := by
  induction fuel generalizing s with
  | zero =>
    rw [show unwindIndentsLoop s col 0 = s by unfold unwindIndentsLoop; rfl]
    exact id
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · intro h
      have hm := ih _ h
      have he : ({ s.emit .blockEnd with
          indents := (s.emit .blockEnd).indents.pop,
          pendingKeys := (s.emit .blockEnd).pendingKeys.pop } : ScannerState).indents
          = s.indents.pop := by simp [ScannerState.emit]
      rw [he] at hm
      exact indents_mem_of_mem_pop hm
    · exact id

lemma unwindIndents_mem (s : ScannerState) (col : Int) (e : IndentEntry) :
    e ∈ (unwindIndents s col).indents → e ∈ s.indents :=
  unwindIndentsLoop_mem s col s.indents.size e

/-- **…and the level it rests on is a MAPPING level** — §8.2.1, read off the
    `:`'s own validation.  A saved key at or left of the floor whose column is
    the top entry's own column is refused when that entry is a SEQUENCE
    (`a:⏎  - x⏎  b: 2` = `trailing content`), so a `:` that validates at such a
    column has a mapping level under it.  That is the half `ResumeFrames` needs
    beyond the column itself: the frames record mapping widths only, because a
    sequence level a dedent landing crosses can only close. -/
lemma scanValue_top_not_sequence {s : ScannerState} {top : IndentEntry}
    (hok : scanValueValidate s = .ok ())
    (h_poss : s.simpleKey.possible = true) (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.simpleKey.pos.col : Int) = top.column)
    (h_le : (s.simpleKey.pos.col : Int) ≤ s.currentIndent) :
    top.isSequence = false := by
  cases htop : top.isSequence with
  | false => rfl
  | true =>
    exfalso
    unfold scanValueValidate at hok
    have hbeq : ((s.simpleKey.pos.col : Int) == top.column) = true := by simp [h_at]
    simp [bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, h_poss, h_noflow, h_top, htop, h_le, hbeq] at hok
    split at hok
    · split at hok <;> simp at hok
    · simp at hok

/-- **…and so does the `?`** (item 131).  §8.2.1's check runs at `scanKey` as
    well as at `scanValueValidate`, so the explicit-key indicator refutes the
    same disjunct the `:` does: an accepted `?` standing at the top entry's own
    column has a MAPPING level under it (`a:⏎  - x⏎  ? c⏎  : 2` is
    `trailing content`, exactly as its implicit twin is).  The `:`'s lemma above
    asks for a `≤ currentIndent` side condition because its check carries one;
    `atSequenceIndent` does not, since the top's column IS `currentIndent`. -/
lemma scanKey_top_not_sequence {s s' : ScannerState} {top : IndentEntry}
    (hok : scanKey s = .ok s') (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.col : Int) = top.column) :
    top.isSequence = false := by
  cases htop : top.isSequence with
  | false => rfl
  | true =>
    exfalso
    unfold scanKey scanKeyValidate atSequenceIndent at hok
    have hbeq : ((s.col : Int) == top.column) = true := by simp [h_at]
    simp [bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, h_noflow, h_top, htop, hbeq] at hok
    -- Every branch of `scanKeyValidate` throws here: the tab check, the
    -- same-line check, and §8.2.1's own.
    split at hok
    · exact absurd hok (by simp)
    · -- The `.ok` arm's own equation is the refutation: every branch of
      -- `scanKeyValidate` throws here — the tab check, the same-line check,
      -- and §8.2.1's own.
      rename_i heq
      split at heq
      · exact absurd heq (by simp)
      · split at heq <;> exact absurd heq (by simp)

/-! ## §2  `saveSimpleKey` pushes tokens, not indents -/

/-- The last step of preprocessing touches `tokens` and `simpleKey` only. -/
lemma saveSimpleKey_preserves_indents (s : ScannerState) :
    (saveSimpleKey s).indents = s.indents := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl

/-- The key save moves no cursor either (item 60). -/
lemma saveSimpleKey_col (s : ScannerState) : (saveSimpleKey s).col = s.col := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl

/-! ## §3  Where the two halves meet

The statement the accumulator actually reads is not here but in
`preprocess_some_ssl_comments_anyCol` (`StreamAccum`), because the flag the
unwind branch tests is `skipToContent`'s OWN result, not the caller's: the flag
can go UP during the walk (a break sets it), and the fact that it did not is
exactly the surface no-break disjunct that lemma already returns.  So the two
travel together — §1's `skipToContent_preserves_indents` plus §2's key save
discharge the payload's new conjunct there, and the armed branch is refuted by
the same flag transparency item 12's payload already uses. -/

/-! ## §4  From the stack to the floor

`currentIndent` is the stack's top column, so an equal stack is an equal indent;
and the scanner's block-scalar floor is `(max 0 (currentIndent + 1)).toNat`, so
the accumulator's carried `(n : Int) ≤ currentIndent + 1` is exactly what says
the entry's index is one the body's content indent admits. -/

/-- Equal stacks, equal indent. -/
lemma currentIndent_of_indents_eq {s t : ScannerState} (h : s.indents = t.indents) :
    s.currentIndent = t.currentIndent := by
  unfold ScannerState.currentIndent; rw [h]

/-- The scanner's own floor for a block scalar's content indent, named: this is
    `scanBlockScalarBody`'s `minContentIndent`, and `scanBlockScalar_prod_at`
    concludes that the indent the body was actually collected at is at least
    this.  So it is the largest index an entry can sit at and still have its
    `[170]`/`[174]` body read at that index. -/
def minContentIndentOf (s : ScannerState) : Nat := (max 0 (s.currentIndent + 1)).toNat

/-- An equal stack is an equal floor — the transport, once the walk half above
    has said the stack survived. -/
lemma minContentIndentOf_congr {s t : ScannerState} (h : s.indents = t.indents) :
    minContentIndentOf s = minContentIndentOf t := by
  unfold minContentIndentOf; rw [currentIndent_of_indents_eq h]

/-- The carried inequality, in the shape the floor wants. -/
lemma le_minContentIndentOf_of_int_le {n : Nat} {s : ScannerState}
    (h : (n : Int) ≤ s.currentIndent) : n ≤ minContentIndentOf s := by
  unfold minContentIndentOf; omega

/-- **What a pending owes if its index is to survive into a block scalar.**

    Two decidable facts about the scanner state the pending is parked at: the
    indent-check flag is down (so the next preprocessing step cannot unwind the
    stack out from under the index — §3), and the index is at or below the
    floor a block scalar's body would be collected against (§4).

    It is carried as `IndentFloor sc n ∨ True`, exactly as items 15/17 carry
    `ImplicitKeyPack` / `PropsKeyPack`: a producer that can measure it hands the
    left side over, one that cannot hands `True`, and the CONSUMER's route to
    the escape is unchanged either way.  So the escape's call-site count is
    fixed by construction and what the item moves is the domain (R645/R646). -/
def IndentFloor (sc : ScannerState) (n : Nat) : Prop :=
  sc.needIndentCheck = false ∧ n ≤ minContentIndentOf sc

/-- At index 0 the floor is free: `minContentIndentOf` is a `Nat`. -/
lemma IndentFloor.zero {sc : ScannerState} (h : sc.needIndentCheck = false) :
    IndentFloor sc 0 := ⟨h, Nat.zero_le _⟩

/-- A floor measured at the SHIFTED index (item 179) still admits every reading
    the raw index made: `SBlockNode`'s `n_lean = n_spec + 1` convention puts the
    awaited node one above the entry column, and the entry-column reads weaken
    to it. -/
lemma IndentFloor.of_succ {sc : ScannerState} {n : Nat}
    (h : IndentFloor sc (n + 1)) : IndentFloor sc n :=
  ⟨h.1, Nat.le_of_succ_le h.2⟩

/-- The shifted floor's second conjunct read back as the LEVEL (item 386): the
    park's index is at or below the stack top, `minContentIndentOf` being the top
    plus one.  The converse of `succ_le_minContentIndentOf_of_int_le`. -/
lemma IndentFloor.int_le_of_succ {sc : ScannerState} {n : Nat}
    (h : IndentFloor sc (n + 1)) : (n : Int) ≤ sc.currentIndent := by
  have h2 := h.2; unfold minContentIndentOf at h2; omega

/-- The carried inequality, in the SHIFTED floor's shape (item 179): a stack
    top at or above the entry column admits the awaited node's index, because
    the scalar floor is the top plus one. -/
lemma succ_le_minContentIndentOf_of_int_le {n : Nat} {s : ScannerState}
    (h : (n : Int) ≤ s.currentIndent) : n + 1 ≤ minContentIndentOf s := by
  unfold minContentIndentOf; omega

/-- `IndentFloor` at the shifted index, off the same push fact the raw floor
    spent (item 179). -/
lemma IndentFloor.succ_of_int_le {sc : ScannerState} {n : Nat}
    (h_nic : sc.needIndentCheck = false) (h : (n : Int) ≤ sc.currentIndent) :
    IndentFloor sc (n + 1) :=
  ⟨h_nic, succ_le_minContentIndentOf_of_int_le h⟩

/-- **The floor's transport** (item 27): a step that leaves the indent stack
    alone carries the pending's measurement forward verbatim, and a pending
    that never had one still has none.  Every re-park in the accumulator goes
    through this. -/
lemma IndentFloor.transport {sc s' : ScannerState} {n : Nat}
    (h_floor : IndentFloor sc n ∨ True)
    (h_nic_s : s'.needIndentCheck = false)
    (h_ind : sc.needIndentCheck = false → s'.indents = sc.indents) :
    IndentFloor s' n ∨ True := by
  rcases h_floor with ⟨h_nic_sc, h_le⟩ | _
  · exact Or.inl ⟨h_nic_s, by rw [minContentIndentOf_congr (h_ind h_nic_sc)]; exact h_le⟩
  · exact Or.inr trivial

/-! ## §5  The runtime's own pushes

`[183] l+block-sequence(n)` and `[187] l+block-mapping(n)` are opened by the
scanner's `pushSequenceIndent` / `pushMappingIndent`, both of which take the
INDICATOR's column — which is exactly the index item 22 gave the pending.  So
the pending's floor is discharged by the push it was created alongside. -/

/-- `emit` writes tokens. -/
@[simp] lemma emit_indents (s : ScannerState) (t : YamlToken) :
    (s.emit t).indents = s.indents := rfl

/-- `emitAt` writes tokens. -/
@[simp] lemma emitAt_indents (s : ScannerState) (p : YamlPos) (t : YamlToken) :
    (s.emitAt p t).indents = s.indents := rfl

/-- After a sequence push the stack's top is at or below the pushed column —
    either it IS that column, or the push was skipped because the top was
    already at least that deep. -/
lemma pushSequenceIndent_le (s : ScannerState) (col : Int) :
    col ≤ (pushSequenceIndent s col).currentIndent := by
  unfold pushSequenceIndent
  split
  · show col ≤ ScannerState.currentIndent _
    unfold ScannerState.currentIndent
    rw [show ({ (s.emit .blockSequenceStart) with
          indents := (s.emit .blockSequenceStart).indents.push
            { column := col, isSequence := true } } : ScannerState).indents
        = (s.emit .blockSequenceStart).indents.push { column := col, isSequence := true } from rfl,
      Array.back?_push]
    simp
  · omega

/-- `[187]`'s twin. -/
lemma pushMappingIndent_le (s : ScannerState) (col : Int) :
    col ≤ (pushMappingIndent s col).currentIndent := by
  unfold pushMappingIndent
  split
  · show col ≤ ScannerState.currentIndent _
    unfold ScannerState.currentIndent
    rw [show ({ (s.emit .blockMappingStart) with
          indents := (s.emit .blockMappingStart).indents.push
            { column := col, isSequence := false } } : ScannerState).indents
        = (s.emit .blockMappingStart).indents.push { column := col, isSequence := false } from rfl,
      Array.back?_push]
    simp
  · omega

/-- Neither push touches the flag. -/
lemma pushSequenceIndent_needIndentCheck (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).needIndentCheck = s.needIndentCheck := by
  unfold pushSequenceIndent; split <;> rfl

/-- See `pushSequenceIndent_needIndentCheck`. -/
lemma pushMappingIndent_needIndentCheck (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).needIndentCheck = s.needIndentCheck := by
  unfold pushMappingIndent; split <;> rfl

/-- The `-` scan's only write to the indent stack is `[183]`'s push. -/
lemma scanBlockEntry_indents {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hok : scanBlockEntry s = .ok s') :
    s'.indents = (pushSequenceIndent s (s.col : Int)).indents := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true] at hok
  split at hok
  · simp at hok
  · split at hok
    · simp at hok  -- item 48 same-line check
    split at hok
    · simp at hok  -- `scanBlockEntryValidate` (item 134)
    simp only [Except.ok.injEq] at hok
    subst hok
    show (ScannerState.advance (ScannerState.emit _ _)).indents = _
    rw [advance_indents]; rfl

/-- **The `-` producer's floor** (`[183]`): a block entry pushes at its own
    column, so the entry index the accumulator parks is at or below the stack
    top the next step will measure a block scalar against. -/
lemma scanBlockEntry_col_le_currentIndent {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hok : scanBlockEntry s = .ok s') :
    (s.col : Int) ≤ s'.currentIndent := by
  rw [currentIndent_of_indents_eq (scanBlockEntry_indents h_noflow hok)]
  exact pushSequenceIndent_le s _

/-- The `-` scan leaves the indent-check flag where it found it. -/
lemma scanBlockEntry_needIndentCheck {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hok : scanBlockEntry s = .ok s') :
    s'.needIndentCheck = s.needIndentCheck := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true] at hok
  split at hok
  · simp at hok
  · split at hok
    · simp at hok  -- item 48 same-line check
    split at hok
    · simp at hok  -- `scanBlockEntryValidate` (item 134)
    simp only [Except.ok.injEq] at hok
    subst hok
    show (ScannerState.advance (ScannerState.emit _ _)).needIndentCheck = _
    rw [advance_preserves_needIndentCheck]
    exact pushSequenceIndent_needIndentCheck s _

/-- The `?` scan's only write to the indent stack is `[187]`'s push. -/
lemma scanKey_indents {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hok : scanKey s = .ok s') :
    s'.indents = (pushMappingIndent s (s.col : Int)).indents := by
  unfold scanKey at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       show (ScannerState.advance (ScannerState.emit _ _)).indents = _
       rw [advance_indents]; rfl)
    | simp_all

/-- **The `?` producer's floor** (`[187]`): the explicit-key indicator pushes a
    mapping indent at its own column, `scanBlockEntry`'s twin. -/
lemma scanKey_col_le_currentIndent {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hok : scanKey s = .ok s') :
    (s.col : Int) ≤ s'.currentIndent := by
  rw [currentIndent_of_indents_eq (scanKey_indents h_noflow hok)]
  exact pushMappingIndent_le s _

/-- The `?` scan leaves the indent-check flag where it found it. -/
lemma scanKey_needIndentCheck {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hok : scanKey s = .ok s') :
    s'.needIndentCheck = s.needIndentCheck := by
  unfold scanKey at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true] at hok
  repeat' split at hok
  all_goals first
    | (simp only [Except.ok.injEq] at hok
       subst hok
       show (ScannerState.advance (ScannerState.emit _ _)).needIndentCheck = _
       rw [advance_preserves_needIndentCheck]
       exact pushMappingIndent_needIndentCheck s _)
    | simp_all

/-! ## §6  Property scans do not touch the stack

`[96] c-ns-properties` is a decoration, not a collection: `&`/`!` walk a name
and emit a token.  So a run parked at an entry's route index keeps whatever
floor the entry had — which is what lets `  - &a |` reuse `  - |`'s. -/

/-- `collectAnchorNameLoop` advances. -/
lemma collectAnchorNameLoop_preserves_indents (s : ScannerState) (name : String) (fuel : Nat) :
    (collectAnchorNameLoop s name fuel).2.indents = s.indents := by
  induction fuel generalizing s name with
  | zero => unfold collectAnchorNameLoop; rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · split
      · rw [ih, advance_indents]
      · rfl
    · rfl

/-- `collectVerbatimTagLoop` advances. -/
lemma collectVerbatimTagLoop_preserves_indents (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).2.2.indents = s.indents := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · exact advance_indents s
    · split
      · rw [ih, advance_indents]
      · rfl
    · rfl

/-- `collectTagSuffixLoop` advances. -/
lemma collectTagSuffixLoop_preserves_indents (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).2.indents = s.indents := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih, advance_indents]
      · rfl
    · rfl

/-- `collectTagHandleLoop` advances. -/
lemma collectTagHandleLoop_preserves_indents (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).2.2.indents = s.indents := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · exact advance_indents s
    · split
      · rw [ih, advance_indents]
      · rfl
    · rfl

/-- `&`/`*` — walk a name, emit at the marker. -/
lemma scanAnchorOrAlias_preserves_indents {s s' : ScannerState} {isAnchor : Bool}
    (hok : scanAnchorOrAlias s isAnchor = .ok s') : s'.indents = s.indents := by
  unfold scanAnchorOrAlias at hok
  simp only [] at hok
  split at hok
  · simp at hok
  · simp only [Except.ok.injEq] at hok
    subst hok
    simp only [ScannerState.emitAt]
    rw [collectAnchorNameLoop_preserves_indents, advance_indents]

/-- `!<uri>`. -/
lemma scanVerbatimTag_preserves_indents {s s' : ScannerState} {p : YamlPos}
    (hok : scanVerbatimTag s p = .ok s') : s'.indents = s.indents := by
  unfold scanVerbatimTag at hok
  simp only [] at hok
  split at hok
  · simp at hok
  · split at hok
    · simp at hok
    · simp only [Except.ok.injEq] at hok
      subst hok
      simp only [ScannerState.emitAt]
      rw [collectVerbatimTagLoop_preserves_indents, advance_indents]

/-- `!!suffix`. -/
lemma scanSecondaryTag_preserves_indents (s : ScannerState) (p : YamlPos) :
    (scanSecondaryTag s p).indents = s.indents := by
  unfold scanSecondaryTag
  simp only [ScannerState.emitAt]
  rw [collectTagSuffixLoop_preserves_indents, advance_indents]

/-- `!handle!suffix` / `!suffix`. -/
lemma scanNamedTag_preserves_indents (s : ScannerState) (p : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s p inputEnd).indents = s.indents := by
  unfold scanNamedTag
  simp only []
  split
  · simp only [ScannerState.emitAt]
    rw [collectTagSuffixLoop_preserves_indents, collectTagHandleLoop_preserves_indents]
  · simp only [ScannerState.emitAt]
    rw [collectTagSuffixLoop_preserves_indents, collectTagHandleLoop_preserves_indents]

/-- `[97] c-ns-tag-property` in all four shapes. -/
lemma scanTag_preserves_indents {s s' : ScannerState}
    (hok : scanTag s = .ok s') : s'.indents = s.indents := by
  unfold scanTag at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · split at hok
    · simp at hok
    · rename_i s_inner h_inner
      simp only [Except.ok.injEq] at hok
      subst hok
      show s_inner.indents = _
      rw [scanVerbatimTag_preserves_indents h_inner, advance_indents]
  · simp only [Except.ok.injEq] at hok
    subst hok
    show (scanSecondaryTag s.advance s.currentPos).indents = _
    rw [scanSecondaryTag_preserves_indents, advance_indents]
  · simp only [Except.ok.injEq] at hok
    subst hok
    show (scanNamedTag s.advance s.currentPos s.inputEnd).indents = _
    rw [scanNamedTag_preserves_indents, advance_indents]

/-! ## §6b  The `:` producer

`scanValue` is the one indicator whose entry column is not necessarily its own:
it resolves a pending implicit key and pushes at the KEY's column.  When the
save is FRESH — the `:` opens `[189]`'s empty-key entry, which is the shape
`colon_open_map` parks — the key sits at the `:` itself and the push is at the
indicator's column like the other two.  When it is inherited the key is an
earlier column the accumulator does not carry, and this item leaves that case
to the punt. -/

/-- `scanValueClearKey` only ever CLEARS the saved key. -/
lemma scanValueClearKey_simpleKey (s : ScannerState) :
    (scanValueClearKey s).simpleKey = s.simpleKey ∨
    (scanValueClearKey s).simpleKey.possible = false := by
  unfold scanValueClearKey
  split
  · split
    · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact Or.inl rfl

/-- …and touches nothing else. -/
lemma scanValueClearKey_fields (s : ScannerState) :
    (scanValueClearKey s).col = s.col ∧
    (scanValueClearKey s).indents = s.indents ∧
    (scanValueClearKey s).inFlow = s.inFlow ∧
    (scanValueClearKey s).currentPos = s.currentPos ∧
    (scanValueClearKey s).explicitKeyLine = s.explicitKeyLine ∧
    (scanValueClearKey s).line = s.line ∧
    (scanValueClearKey s).needIndentCheck = s.needIndentCheck := by
  unfold scanValueClearKey
  split
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `scanValueValidate` pins an explicit `:` to the mapping's own indent
    (`[197] l-block-map-explicit-value(n) = s-indent(n) ":" …`), which is what
    makes the no-push arm safe. -/
lemma scanValueValidate_explicit_col {s : ScannerState}
    (h_poss : s.simpleKey.possible = false) (h_noflow : s.inFlow = false)
    (h_ek : s.explicitKeyLine.isSome = true)
    (h_valid : scanValueValidate s = .ok ()) :
    (s.col : Int) = s.currentIndent := by
  obtain ⟨ekLine, hek⟩ := Option.isSome_iff_exists.mp h_ek
  unfold scanValueValidate at h_valid
  simp only [bind, Except.bind, pure, Except.pure, h_poss, Bool.false_and,
    ite_eq_right Bool.false_ne_true, hek] at h_valid
  repeat' split at h_valid
  all_goals simp_all

/-- `scanValuePrepare`'s three arms, measured against the indicator's column:
    the resolved-key arm pushes at the KEY (equal to the `:`'s column exactly
    when the save was fresh), the explicit-value arm pushes nothing but has
    been validated to sit at the mapping's indent, and the fresh-mapping arm
    pushes at the `:`. -/
lemma scanValuePrepare_col_le {s : ScannerState}
    (h_noflow : s.inFlow = false)
    (h_fresh : s.simpleKey.possible = true → s.simpleKey.pos.col = s.col)
    (h_valid : scanValueValidate s = .ok ()) :
    (s.col : Int) ≤ (scanValuePrepare s).currentIndent := by
  unfold scanValuePrepare
  split
  · rename_i h_poss
    rw [ite_eq_left (by simpa using h_noflow : (!s.inFlow) = true)]
    split
    · rename_i h_gt
      show (s.col : Int) ≤ ScannerState.currentIndent _
      unfold ScannerState.currentIndent
      rw [show ({ s with
            tokens := _,
            pendingKeys := _,
            indents := s.indents.push
              { column := (s.simpleKey.pos.col : Int), isSequence := false },
            simpleKey := { possible := false } } : ScannerState).indents
          = s.indents.push { column := (s.simpleKey.pos.col : Int), isSequence := false } from rfl,
        Array.back?_push]
      simp [h_fresh h_poss]
    · rename_i h_le
      show (s.col : Int) ≤ s.currentIndent
      rw [← h_fresh h_poss]
      exact Int.not_lt.mp h_le
  · split
    · rename_i h_poss h_ek
      show (s.col : Int) ≤ s.currentIndent
      exact Int.le_of_eq
        (scanValueValidate_explicit_col (by simpa using h_poss) h_noflow h_ek h_valid)
    · rw [ite_eq_left (by simpa using h_noflow : (!s.inFlow) = true)]
      exact pushMappingIndent_le s _

/-- **The `:` producer's floor**, when the saved key is the fresh one at the
    indicator itself — which is exactly `[189]`'s empty-key entry.

    The coupling is asked for at the COLUMN (item 74), not at the whole
    position: `scanValuePrepare`'s push reads `simpleKey.pos.col` and nothing
    else, so a producer that can only place the save on the line pays the same
    price as one that can name its offset. -/
lemma scanValue_col_le_currentIndent {s s' : ScannerState}
    (h_noflow : s.inFlow = false)
    (h_fresh : s.simpleKey.possible = true → s.simpleKey.pos.col = s.col)
    (hok : scanValue s = .ok s') :
    (s.col : Int) ≤ s'.currentIndent := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  -- Three `Except` guards now, not two: item 31 inserted
  -- `scanValueIndentTabCheck` between `scanValueValidate` and the prepare.
  split at hok
  · simp at hok
  rename_i h_valid
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  simp only [Except.ok.injEq] at hok
  subst hok
  obtain ⟨hcol, hind, hfl, hpos, _, _, _⟩ := scanValueClearKey_fields s
  have h_kc_fresh : (scanValueClearKey s).simpleKey.possible = true →
      (scanValueClearKey s).simpleKey.pos.col = (scanValueClearKey s).col := by
    intro hp
    rcases scanValueClearKey_simpleKey s with heq | hfalse
    · rw [heq, hcol]
      rw [heq] at hp
      exact h_fresh hp
    · rw [hfalse] at hp; exact absurd hp Bool.false_ne_true
  have h_prep := scanValuePrepare_col_le
    (s := scanValueClearKey s) (by rw [hfl]; exact h_noflow) h_kc_fresh h_valid
  rw [hcol] at h_prep
  -- Item 48: the epilogue's record widened; step to the advance-chain state
  -- (field-wise definitional) and rewrite its indents as before.
  show (s.col : Int) ≤
    (((scanValuePrepare (scanValueClearKey s)).emit YamlToken.value).advance).currentIndent
  rw [currentIndent_of_indents_eq
    (show (((scanValuePrepare (scanValueClearKey s)).emit YamlToken.value).advance).indents
        = (scanValuePrepare (scanValueClearKey s)).indents from by
      rw [advance_indents]; rfl)]
  exact h_prep

/-! ## §6c  The `:` producer, measured at the KEY instead of at itself

Item 27 read `scanValuePrepare`'s push at the INDICATOR's column, which is the
key's own only when the save was fresh, and punted otherwise.  Item 28 measures
the same push at the column it actually uses — `s.simpleKey.pos.col`, the
resolved key's — so an entry whose index is at or below the KEY is bounded
whether the save was fresh or inherited.  The two arms need no case split
between them: the arm that pushes lands the stack top exactly at the key, and
the arm that does not push was gated by `keyCol ≤ currentIndent`, which is the
same inequality already.

The EXPLICIT-key clear (`scanValueClearKey`, `[197]`'s arm) stopped punting at
item 81: both of its branches demand things a live same-line key that sits
strictly behind the cursor cannot supply — branch (2) a key from the `?`'s own
earlier line, branch (1) a key saved AT the `:` itself — and
`KeysBehindCursor` (ScannerCorrectness) says every reachable saved key IS
strictly behind.  `scanValueClearKey_keyrun` names the pair, and the floor
lemmas below take the two coordinates as premises and return the floor
unconditionally. -/

/-- **The clear is a no-op unless the key it clears sat AT the cursor.**
    `scanValueClearKey`'s two branches both need the `:` on a different line
    from the `?`; with the key recorded on the `:`'s own line, the second is
    impossible and the first names the offset it cleared. -/
lemma scanValueClearKey_keyrun {s : ScannerState}
    (h_kline : s.simpleKey.pos.line = s.line) :
    (scanValueClearKey s).simpleKey = s.simpleKey ∨
      ((scanValueClearKey s).simpleKey.possible = false ∧
        s.simpleKey.pos.offset = s.offset) := by
  unfold scanValueClearKey
  split
  · rename_i ekLine hek
    split
    · rename_i h1
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
      exact Or.inr ⟨rfl, h1.1.2⟩
    · split
      · rename_i h2
        exfalso
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h2
        exact h2.1.2 (h_kline ▸ h2.1.1.2)
      · exact Or.inl rfl
  · exact Or.inl rfl

/-- **The resolved key's floor.**  `scanValuePrepare` pushes `[187]`'s indent at
    `s.simpleKey.pos.col`, and declines to push exactly when that column is
    already at or below the stack top — so an index bounded by the key's column
    is bounded by the resulting stack top either way. -/
lemma scanValuePrepare_key_col_le {s : ScannerState} {k : Nat}
    (h_noflow : s.inFlow = false)
    (h_poss : s.simpleKey.possible = true)
    (h_key : (k : Int) ≤ (s.simpleKey.pos.col : Int)) :
    (k : Int) ≤ (scanValuePrepare s).currentIndent := by
  unfold scanValuePrepare
  split
  · rw [ite_eq_left (by simpa using h_noflow : (!s.inFlow) = true)]
    split
    · show (k : Int) ≤ ScannerState.currentIndent _
      unfold ScannerState.currentIndent
      rw [show ({ s with
            tokens := _,
            pendingKeys := _,
            indents := s.indents.push
              { column := (s.simpleKey.pos.col : Int), isSequence := false },
            simpleKey := { possible := false } } : ScannerState).indents
          = s.indents.push { column := (s.simpleKey.pos.col : Int), isSequence := false } from rfl,
        Array.back?_push]
      simpa using h_key
    · rename_i h_le
      show (k : Int) ≤ s.currentIndent
      exact Int.le_trans h_key (Int.not_lt.mp h_le)
  · rename_i h_np
    exact absurd h_poss h_np

/-- **The `:` scan's floor at the resolved key** (item 81, total).  A key on
    the `:`'s own line that does not sit AT the cursor survives the clear
    (`scanValueClearKey_keyrun`), so the push is at the key. -/
lemma scanValue_key_col_le {s s' : ScannerState} {k : Nat}
    (h_noflow : s.inFlow = false)
    (h_poss : s.simpleKey.possible = true)
    (h_kline : s.simpleKey.pos.line = s.line)
    (h_behind : s.simpleKey.pos.offset ≠ s.offset)
    (h_key : (k : Int) ≤ (s.simpleKey.pos.col : Int))
    (hok : scanValue s = .ok s') :
    (k : Int) ≤ s'.currentIndent := by
  rcases scanValueClearKey_keyrun h_kline with heq | ⟨_, h_at⟩
  · unfold scanValue at hok
    simp only [bind, Except.bind] at hok
    split at hok
    · simp at hok
    split at hok
    · simp at hok
    split at hok
    · simp at hok
    simp only [Except.ok.injEq] at hok
    subst hok
    obtain ⟨_, _, hfl, _, _, _, _⟩ := scanValueClearKey_fields s
    have h_prep := scanValuePrepare_key_col_le (s := scanValueClearKey s) (k := k)
      (by rw [hfl]; exact h_noflow) (by rw [heq]; exact h_poss) (by rw [heq]; exact h_key)
    -- Item 48: same advance-chain step as the fresh-save producer above.
    show (k : Int) ≤
      (((scanValuePrepare (scanValueClearKey s)).emit YamlToken.value).advance).currentIndent
    rw [currentIndent_of_indents_eq
      (show (((scanValuePrepare (scanValueClearKey s)).emit YamlToken.value).advance).indents
          = (scanValuePrepare (scanValueClearKey s)).indents from by
        rw [advance_indents]; rfl)]
    exact h_prep
  · exact absurd h_at h_behind

/-- `scanValuePrepare` writes tokens, indents and the saved key. -/
lemma scanValuePrepare_needIndentCheck (s : ScannerState) :
    (scanValuePrepare s).needIndentCheck = s.needIndentCheck := by
  unfold scanValuePrepare
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndent_needIndentCheck s _
      · rfl

/-- The `:` scan leaves the indent-check flag where it found it. -/
lemma scanValue_needIndentCheck {s s' : ScannerState}
    (hok : scanValue s = .ok s') : s'.needIndentCheck = s.needIndentCheck := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  split at hok
  · simp at hok
  simp only [Except.ok.injEq] at hok
  subst hok
  show (ScannerState.advance _).needIndentCheck = _
  rw [advance_preserves_needIndentCheck]
  show (scanValuePrepare (scanValueClearKey s)).needIndentCheck = _
  rw [scanValuePrepare_needIndentCheck, (scanValueClearKey_fields s).2.2.2.2.2.2]

/-! ## §7  The dispatchers, in the shape the producers consume

Each wrapper hands back the floor together with the flag, and punts the FLOW
case rather than assuming it away: `scanKey` pushes only in block context, and
`isKeyCandidate` does not exclude a flow `?`.  Punting here costs a field value,
not a call site — which is the whole point of carrying the floor as
`IndentFloor sc n ∨ True`. -/

/-- The `-` arm names its own scan, and its guard carries `!inFlow`. -/
lemma dispatchBlockIndicators_dash_scan {s s' : ScannerState}
    (hok : scanNextToken_dispatchBlockIndicators s '-' = .ok (some s')) :
    s.inFlow = false ∧ scanBlockEntry s = .ok s' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i hguard
    refine ⟨by simpa using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hguard).1).2, ?_⟩
    split at hok
    · simp at hok
    · rename_i s_e he
      simp only [Except.ok.injEq, Option.some.injEq] at hok
      subst hok; exact he
  · exfalso
    have h2 : (('-' : Char) == '?' : Bool) = false := by decide
    have h3 : (('-' : Char) == ':' : Bool) = false := by decide
    simp only [h2, h3, Bool.false_and, ite_eq_right Bool.false_ne_true] at hok
    simp at hok

/-- The `?` arm names its own scan — but NOT `!inFlow`. -/
lemma dispatchBlockIndicators_key_scan {s s' : ScannerState}
    (hok : scanNextToken_dispatchBlockIndicators s '?' = .ok (some s')) :
    scanKey s = .ok s' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  have hdash : (('?' : Char) == '-' : Bool) = false := by decide
  have hcolon : (('?' : Char) == ':' : Bool) = false := by decide
  simp only [bind, Except.bind, pure, Except.pure, hdash, hcolon, Bool.false_and,
    ite_eq_right Bool.false_ne_true] at hok
  split at hok
  · split at hok
    · simp at hok
    · rename_i s_k hk
      simp only [Except.ok.injEq, Option.some.injEq] at hok
      subst hok; exact hk
  · simp at hok

/-- **The `-` producer's floor, packaged.** -/
lemma dash_floor {s s' : ScannerState}
    (hok : scanNextToken_dispatchBlockIndicators s '-' = .ok (some s')) :
    (s.col : Int) ≤ s'.currentIndent ∧ s'.needIndentCheck = s.needIndentCheck :=
  let ⟨h_noflow, h_scan⟩ := dispatchBlockIndicators_dash_scan hok
  ⟨scanBlockEntry_col_le_currentIndent h_noflow h_scan,
   scanBlockEntry_needIndentCheck h_noflow h_scan⟩

/-- **The `?` producer's floor, packaged** — with the flow case punted. -/
lemma key_floor_or {s s' : ScannerState}
    (hok : scanNextToken_dispatchBlockIndicators s '?' = .ok (some s')) :
    (s.inFlow = false ∧ (s.col : Int) ≤ s'.currentIndent ∧
      s'.needIndentCheck = s.needIndentCheck) ∨ s.inFlow = true := by
  by_cases h : s.inFlow = true
  · exact Or.inr h
  · have h_noflow : s.inFlow = false := by simpa using h
    have h_scan := dispatchBlockIndicators_key_scan hok
    exact Or.inl ⟨h_noflow, scanKey_col_le_currentIndent h_noflow h_scan,
                  scanKey_needIndentCheck h_noflow h_scan⟩

/-- The `:` arm names its own scan. -/
lemma dispatchBlockIndicators_value_scan {s s' : ScannerState}
    (hok : scanNextToken_dispatchBlockIndicators s ':' = .ok (some s')) :
    scanValue s = .ok s' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  have hdash : ((':' : Char) == '-' : Bool) = false := by decide
  have hkey : ((':' : Char) == '?' : Bool) = false := by decide
  simp only [bind, Except.bind, pure, Except.pure, hdash, hkey, Bool.false_and,
    ite_eq_right Bool.false_ne_true] at hok
  split at hok
  · split at hok
    · simp at hok
    · rename_i s_v hv
      simp only [Except.ok.injEq, Option.some.injEq] at hok
      subst hok; exact hv
  · simp at hok

/-- **The `:` producer's floor, packaged** — with the flow case and the
    inherited-key case both punted.  The freshness premise is the column one
    (item 74). -/
lemma value_floor_or {s s' : ScannerState}
    (h_fresh : s.simpleKey.possible = true → s.simpleKey.pos.col = s.col)
    (hok : scanNextToken_dispatchBlockIndicators s ':' = .ok (some s')) :
    (s.inFlow = false ∧ (s.col : Int) ≤ s'.currentIndent ∧
      s'.needIndentCheck = s.needIndentCheck) ∨ s.inFlow = true := by
  by_cases h : s.inFlow = true
  · exact Or.inr h
  · have h_noflow : s.inFlow = false := by simpa using h
    have h_scan := dispatchBlockIndicators_value_scan hok
    exact Or.inl ⟨h_noflow, scanValue_col_le_currentIndent h_noflow h_fresh h_scan,
                  scanValue_needIndentCheck h_scan⟩

/-- **The `:` producer's floor measured at the RESOLVED key** (item 28; total
    since item 81), which is the coordinate `scanValuePrepare` actually pushes
    at.  Item 27's `value_floor_or` is the special case where the two coincide;
    this one asks the caller for the coupling instead of assuming the save was
    fresh, and so reaches the implicit-key entry (`  a: |`) as well as the
    empty-key one.  The two coordinates that used to be punts — the key on the
    `:`'s line, and strictly behind its cursor — are premises now: every caller
    is a pack consumer, the pack's guard is the first, and `KeysBehindCursor`
    is the second. -/
lemma value_key_floor {s s' : ScannerState} {k : Nat}
    (h_noflow : s.inFlow = false)
    (h_poss : s.simpleKey.possible = true)
    (h_kline : s.simpleKey.pos.line = s.line)
    (h_behind : s.simpleKey.pos.offset ≠ s.offset)
    (h_key : (k : Int) ≤ (s.simpleKey.pos.col : Int))
    (hok : scanNextToken_dispatchBlockIndicators s ':' = .ok (some s')) :
    (k : Int) ≤ s'.currentIndent ∧ s'.needIndentCheck = s.needIndentCheck :=
  have h_scan := dispatchBlockIndicators_value_scan hok
  ⟨scanValue_key_col_le h_noflow h_poss h_kline h_behind h_key h_scan,
   scanValue_needIndentCheck h_scan⟩

/-- A `[96]` property scan leaves the indent stack alone, so a run parked at an
    entry's route index inherits the entry's floor unchanged. -/
lemma dispatchContent_props_indents {s s' : ScannerState} {c : Char}
    (hc : c = '&' ∨ c = '!') (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.indents = s.indents := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  cases hc with
  | inl h =>
    subst h
    simp only [beq_self_eq_true, ite_true] at hok
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i s_a ha
        simp only [Except.ok.injEq] at hok
        subst hok
        show s_a.indents = s.indents
        exact scanAnchorOrAlias_preserves_indents ha
  | inr h =>
    subst h
    have h1 : (('!' : Char) == '&' : Bool) = false := by decide
    have h2 : (('!' : Char) == '*' : Bool) = false := by decide
    simp only [h1, h2, ite_eq_right Bool.false_ne_true, beq_self_eq_true, ite_true] at hok
    split at hok
    · simp at hok
    · exact scanTag_preserves_indents hok

/-! ## §7  A tab in the indentation refuses, in every arm (DOCS item 32)

`[63] s-indent(n)` is spaces only, and all three block indicators stand
directly after one — `[184]`'s own entry for `-`, `[191]`'s for `?`, and for a
keyless `:` either `[192]`'s `e-node` entry or `[195]`'s explicit value.  Each
scanner says so, and this is the form the accumulator's tab branch reads: a
successful dispatch is impossible.  The `-` arm has carried its scan since Step
5b.2, the `?` and `:` arms since item 31. -/

/-- `?` and `-` read the run in front of the indicator (`[66]`'s walk); `:`
    reads the whole line (`[63]`'s), because the run in front of a keyless `:`
    IS the entry's indentation. -/
lemma scanBlockEntry_tab_ne {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (htab : s.hasTabInPrecedingWhitespace = true) :
    scanBlockEntry s ≠ .ok s' := by
  intro hok
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true, htab] at hok
  simp at hok

lemma scanKey_tab_ne {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (htab : s.hasTabInPrecedingWhitespace = true) :
    scanKey s ≠ .ok s' := by
  intro hok
  unfold scanKey scanKeyValidate at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true, htab] at hok
  simp at hok

/-- `scanValueClearKey` writes `simpleKey` and nothing else, so the two scans
    read the same string, offset and column on either side of it. -/
lemma scanValueClearKey_scan_fields (s : ScannerState) :
    (scanValueClearKey s).inFlow = s.inFlow ∧
    (scanValueClearKey s).tabInLineIndent = s.tabInLineIndent ∧
    (scanValueClearKey s).line = s.line ∧ (scanValueClearKey s).col = s.col := by
  unfold scanValueClearKey ScannerState.tabInLineIndent ScannerState.inFlow
  split <;> (try split) <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl⟩

lemma scanValueIndentTabCheck_tab {s : ScannerState}
    (h_noflow : s.inFlow = false) (htab : s.tabInLineIndent = true) :
    scanValueIndentTabCheck s = .error (.tabInIndentation s.line s.col) := by
  unfold scanValueIndentTabCheck
  simp only [h_noflow, htab, Bool.false_eq_true, ite_false, ite_true]
  rfl

lemma scanValue_tab_ne {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (htab : s.tabInLineIndent = true) :
    scanValue s ≠ .ok s' := by
  intro hok
  obtain ⟨h_fl, h_tab, _, _⟩ := scanValueClearKey_scan_fields s
  have h_check := scanValueIndentTabCheck_tab (s := scanValueClearKey s)
    (by rw [h_fl]; exact h_noflow) (by rw [h_tab]; exact htab)
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rw [h_check] at hok
    simp at hok

/-! ## §8  …and in front of a COMPACT `:`, from the run (DOCS item 34)

§7 refutes the tab from `[63] s-indent`'s own coordinate — `tabInLineIndent`,
the whole line in front of the token — and that coordinate answers `false` for a
COMPACT indicator by design: `- →: a` has the entry's `-` on the line, so the
line-walk stops there and reports "something precedes this token", which is
true and is not the question.  The question is whether the run BETWEEN the two
indicators is `[185] s-l+block-indented`'s `s-indent(m)`, and that run is what
`[66]`'s backward scan reads.

`scanBlockEntry` and `scanKey` read it directly (§7's two `_tab_ne`s, which need
nothing but the run).  `scanValue` consults the simple-key machine first, and
the branch it takes is not the one the shape suggests: on the indicator's own
line preprocessing has just SAVED a key at the `:` itself — every block
indicator's scan leaves `simpleKeyAllowed := true`, and a break-free step never
clears it — so the key branch walks back from the same offset the fallback
branch would.  Both read the run; the run has a tab; the scan throws either way.

That is the whole content of the two lemmas below: a `:` whose recorded key, if
any, sits AT the cursor cannot be scanned over a tabbed run. -/

/-- The `-` scan re-arms fresh saves.  This is what puts a recorded key at the
    NEXT indicator when nothing intervenes, and so what sends the `:` scan's
    tab test to the run in front of it. -/
lemma scanBlockEntry_simpleKeyAllowed {s s' : ScannerState}
    (hok : scanBlockEntry s = .ok s') : s'.simpleKeyAllowed = true := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · split at hok
    · simp at hok
    · split at hok
      · simp at hok  -- item 48 same-line check
      · split at hok
        · simp at hok  -- `scanBlockEntryValidate` (item 134)
        · simp only [Except.ok.injEq] at hok; rw [← hok]
  · simp only [Except.ok.injEq] at hok; rw [← hok]

/-- The dispatcher's `-` arm, in the form the accumulator's producers hold. -/
lemma dispatchBlockEntry_simpleKeyAllowed {s s' : ScannerState}
    (hok : scanNextToken_dispatchBlockIndicators s '-' = .ok (some s')) :
    s'.simpleKeyAllowed = true :=
  scanBlockEntry_simpleKeyAllowed (dispatchBlockIndicators_dash_scan hok).2

/-- The `?` scan re-arms too (item 58): the explicit key it opens is a fresh
    context for a save, so the tab test at the NEXT indicator reads the run in
    front of that indicator — which is what refutes the inline tab residue at a
    `?`-park. -/
lemma scanKey_simpleKeyAllowed {s s' : ScannerState}
    (hok : scanKey s = .ok s') : s'.simpleKeyAllowed = true := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp at hok; done)
    | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
    | (exfalso; simp_all [throw, throwThe, MonadExceptOf.throw])

/-- …and so does the `:` scan. -/
lemma scanValue_simpleKeyAllowed {s s' : ScannerState}
    (hok : scanValue s = .ok s') : s'.simpleKeyAllowed = true := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | (simp at hok; done)
    | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
    | (exfalso; simp_all [throw, throwThe, MonadExceptOf.throw])

/-- The dispatcher's `?` arm, in the producers' form. -/
lemma dispatchBlockKey_simpleKeyAllowed {s s' : ScannerState}
    (hok : scanNextToken_dispatchBlockIndicators s '?' = .ok (some s')) :
    s'.simpleKeyAllowed = true :=
  scanKey_simpleKeyAllowed (dispatchBlockIndicators_key_scan hok)

/-- The dispatcher's `:` arm. -/
lemma dispatchBlockValue_simpleKeyAllowed {s s' : ScannerState}
    (hok : scanNextToken_dispatchBlockIndicators s ':' = .ok (some s')) :
    s'.simpleKeyAllowed = true :=
  scanValue_simpleKeyAllowed (dispatchBlockIndicators_value_scan hok)

/-- `scanValueClearKey` writes `simpleKey` and nothing else, so both tab tests
    read the same string and the same offset on either side of it — and the key
    it leaves is either the incoming one or none at all. -/
lemma scanValueClearKey_key_fields (s : ScannerState) :
    (scanValueClearKey s).input = s.input ∧
    (scanValueClearKey s).offset = s.offset ∧
    ((scanValueClearKey s).simpleKey.possible = false ∨
      (scanValueClearKey s).simpleKey = s.simpleKey) := by
  unfold scanValueClearKey
  split
  · split
    · exact ⟨rfl, rfl, Or.inl rfl⟩
    · split
      · exact ⟨rfl, rfl, Or.inl rfl⟩
      · exact ⟨rfl, rfl, Or.inr rfl⟩
  · exact ⟨rfl, rfl, Or.inr rfl⟩

/-- **Both branches read the same run.**  With a tab in the whitespace behind
    the cursor and any recorded key sitting AT it, `scanValueIndentTabCheck`
    throws: the key branch walks back from `simpleKey.pos.offset` and the
    fallback branch from `offset`, and the hypothesis says those are one. -/
lemma scanValueIndentTabCheck_run {s : ScannerState}
    (h_noflow : s.inFlow = false)
    (h_run : s.hasTabInPrecedingWhitespace = true)
    (h_key : s.simpleKey.possible = true → s.simpleKey.pos.offset = s.offset) :
    ∃ e, scanValueIndentTabCheck s = .error e := by
  by_cases h_til : s.tabInLineIndent = true
  · exact ⟨_, scanValueIndentTabCheck_tab h_noflow h_til⟩
  · have h_til' : s.tabInLineIndent = false := by simpa using h_til
    by_cases h_poss : s.simpleKey.possible = true
    · -- the recorded key sits AT the cursor, so its walk IS the cursor's
      have hh : ScannerState.hasTabInPrecedingWhitespaceLoop s.input
          s.simpleKey.pos.offset s.simpleKey.pos.offset = true := by
        rw [h_key h_poss]; exact h_run
      refine ⟨.tabInIndentation s.simpleKey.pos.line s.simpleKey.pos.col, ?_⟩
      unfold scanValueIndentTabCheck
      simp only [h_noflow, h_til', h_poss, hh, Bool.false_eq_true, ite_false, ite_true]
      rfl
    · have h_poss' : s.simpleKey.possible = false := by simpa using h_poss
      refine ⟨.tabInIndentation s.line s.col, ?_⟩
      unfold scanValueIndentTabCheck
      simp only [h_noflow, h_til', h_poss', h_run, Bool.false_eq_true, ite_false, ite_true]
      rfl

/-- The `:` scan over a tabbed run, in the shape the dispatch hands it. -/
lemma scanValue_tab_run_ne {s s' : ScannerState}
    (h_noflow : s.inFlow = false)
    (h_run : s.hasTabInPrecedingWhitespace = true)
    (h_key : s.simpleKey.possible = true → s.simpleKey.pos.offset = s.offset) :
    scanValue s ≠ .ok s' := by
  intro hok
  obtain ⟨h_fl, _, _, _⟩ := scanValueClearKey_scan_fields s
  obtain ⟨h_inp, h_off, h_sk⟩ := scanValueClearKey_key_fields s
  have h_run' : (scanValueClearKey s).hasTabInPrecedingWhitespace = true := by
    unfold ScannerState.hasTabInPrecedingWhitespace at h_run ⊢
    rw [h_inp, h_off]; exact h_run
  have h_key' : (scanValueClearKey s).simpleKey.possible = true →
      (scanValueClearKey s).simpleKey.pos.offset = (scanValueClearKey s).offset := by
    intro h_poss
    rcases h_sk with h | h
    · rw [h] at h_poss; simp at h_poss
    · rw [h, h_off]; exact h_key (by rw [← h]; exact h_poss)
  obtain ⟨e, h_check⟩ := scanValueIndentTabCheck_run (s := scanValueClearKey s)
    (by rw [h_fl]; exact h_noflow) h_run' h_key'
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rw [h_check] at hok
    simp at hok

end L4YAML.Proofs.PreprocessIndentStable

end Blanket
