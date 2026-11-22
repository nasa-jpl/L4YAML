/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Coupling.ScannerCoupling
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps

@[expose] public section Blanket

/-! # The located tab and §6.1's own gate (DOCS item 64)

A white run that the grammar has split as `[63] s-indent(j)` followed by a TAB
names a character the scanner reads too, and this file is the bridge between
the two readings — item 62 built it inside `ScalarFoldAt` for the fold's blank
lines, and item 64 needs the same bridge one level up, inside preprocessing,
where `ScalarFoldAt` sits too high in the import graph to be used.

* **`skipSpaces_lands_at_tab`** — the surface split says the run opens with `j`
  spaces and then a tab, so the scanner's own space-skip ends exactly there, at
  column `sp.col + j`.  Its whole content is that the two splits COINCIDE:
  `skipSpaces` never stops on a space (`skipSpaces_peek_ne_space`), so the
  scanner's `j` and the grammar's are the same number.

* **`skipToContentWs_tab_under_indent`** — §6.1's gate, read as a fact about
  what survives it.  A tab at or left of the block's current indent leaves
  preprocessing only three ways: the line goes on to a comment, to a break, or
  to the end of input.  Anything else is `tabInIndentation`, so a landing whose
  run under-runs `s-indent(n)` and then carries a tab CANNOT be followed by
  content — which is what refutes the tab half of `WhiteRunUnderRun`.

The stream-level exemption (`currentIndent < 0`, where a tab before a flow
indicator is `[66] s-separate-in-line` rather than indentation) is excluded by
the caller's own floor: an under-run needs `0 < n`, and `n ≤ currentIndent + 1`
then forces `0 ≤ currentIndent`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.LandingTab

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling

/-! ## §1 The grammar's split and the scanner's coincide -/

/-- `[63]`'s column arithmetic. -/
lemma SIndent_col' {k : Nat} {sp sp' : SurfPos} (h : SIndent k sp sp') :
    sp'.col = sp.col + k := by
  induction h with
  | zero => rfl
  | succ n rest col s' _ ih => simpa [ih] using by omega

/-- Two surface positions agree when their characters and columns do. -/
lemma surfpos_eq {a b : SurfPos} (hc : a.chars = b.chars) (hl : a.col = b.col) :
    a = b := by
  cases a; cases b
  simp only [] at hc hl
  subst hc; subst hl; rfl

/-- `peek?` from correspondence and a known leading character. -/
lemma peek_of_head {sc : ScannerState} {sp : SurfPos} {c : Char} {rest : List Char}
    (hcorr : ScannerSurfCorr sc sp) (h : sp.chars = c :: rest) : sc.peek? = some c := by
  have hsp : sp = ⟨c :: rest, sp.col⟩ := surfpos_eq (by simpa using h) rfl
  rw [hsp] at hcorr
  exact (L4YAML.Proofs.EmitterScannability.peek_of_chars_cons _ _ _ _ hcorr).1

/-- `[63]`'s characters: `s-indent(k)` consumes exactly `k` spaces. -/
lemma sindent_chars {k : Nat} {sp sp' : SurfPos} (h : SIndent k sp sp') :
    sp.chars = List.replicate k ' ' ++ sp'.chars := by
  induction h with
  | zero => rfl
  | succ n rest col s' _ ih => simpa [List.replicate_succ] using ih

/-- Cancel a shorter space prefix against a longer one. -/
lemma replicate_split_cancel {k j : Nat} {A B : List Char} (hkj : k ≤ j)
    (h : List.replicate k ' ' ++ A = List.replicate j ' ' ++ B) :
    A = List.replicate (j - k) ' ' ++ B := by
  have hj : List.replicate j (' ' : Char)
      = List.replicate k ' ' ++ List.replicate (j - k) ' ' := by
    rw [List.replicate_append_replicate, show k + (j - k) = j from by omega]
  rw [hj, List.append_assoc] at h
  exact List.append_cancel_left h

/-- `skipSpaces` stops where `[63] s-indent` runs out: its landing is never
    itself a space. -/
private lemma skipSpacesLoop_peek_ne_space :
    ∀ (fuel : Nat) (s : ScannerState), s.inputEnd - s.offset ≤ fuel →
      (skipSpacesLoop s fuel).peek? ≠ some ' '
  | 0, s, hf => by
      unfold skipSpacesLoop
      intro h
      have := peek_some_hasMore s ' ' h
      omega
  | fuel + 1, s, hf => by
      unfold skipSpacesLoop
      split
      · rename_i hpk
        exact skipSpacesLoop_peek_ne_space fuel s.advance
          (advance_fuel_budget s fuel (peek_some_hasMore s ' ' hpk) (by omega))
      · rename_i hne
        exact hne

lemma skipSpaces_peek_ne_space (s : ScannerState) :
    (skipSpaces s).peek? ≠ some ' ' :=
  skipSpacesLoop_peek_ne_space _ s (Nat.le_refl _)

/-- **`skipSpaces` lands exactly on the located tab.**  The surface's split
    says the run opens with `j` spaces and then a tab; the scanner's own
    space-skip therefore ends at that character, at column `sp.col + j`.  This
    is what lets a *runtime* check read a fact the *grammar* located. -/
lemma skipSpaces_lands_at_tab {j : Nat} {sc : ScannerState} {sp sx : SurfPos}
    (hcorr : ScannerSurfCorr sc sp)
    (hind : SIndent j sp sx) (htab : sx.chars.head? = some '\t') :
    (skipSpaces sc).peek? = some '\t' ∧ (skipSpaces sc).col = sp.col + j := by
  obtain ⟨k, sp_k, hind_k, hcorr_k⟩ := skipSpaces_corr sc sp hcorr
  have hc_j := sindent_chars hind
  have hc_k := sindent_chars hind_k
  have hkj : k = j := by
    rcases Nat.lt_trichotomy k j with h | h | h
    · exfalso
      have heq : sp_k.chars = List.replicate (j - k) ' ' ++ sx.chars :=
        replicate_split_cancel (Nat.le_of_lt h) (hc_k.symm.trans hc_j)
      rw [show j - k = (j - k - 1) + 1 from by omega, List.replicate_succ,
        List.cons_append] at heq
      exact skipSpaces_peek_ne_space sc (peek_of_head hcorr_k heq)
    · exact h
    · exfalso
      have heq : sx.chars = List.replicate (k - j) ' ' ++ sp_k.chars :=
        replicate_split_cancel (Nat.le_of_lt h) (hc_j.symm.trans hc_k)
      rw [show k - j = (k - j - 1) + 1 from by omega, List.replicate_succ,
        List.cons_append] at heq
      rw [heq] at htab
      simp at htab
  subst hkj
  have hsp : sp_k = sx :=
    surfpos_eq (List.append_cancel_left (hc_k.symm.trans hc_j))
      (by rw [SIndent_col' hind_k, SIndent_col' hind])
  subst hsp
  obtain ⟨rest, hrest⟩ : ∃ rest, sp_k.chars = '\t' :: rest := by
    cases hh : sp_k.chars with
    | nil => rw [hh] at htab; simp at htab
    | cons a as =>
      rw [hh] at htab
      simp only [List.head?_cons, Option.some.injEq] at htab
      exact ⟨as, by simp [htab]⟩
  refine ⟨peek_of_head hcorr_k hrest, ?_⟩
  rw [← hcorr_k.col_eq, SIndent_col' hind_k]

/-! ## §2 §6.1's gate, read as a fact about what survives it -/

/-- `consumeNewline` never writes the indent stack. -/
lemma consumeNewline_indents (s : ScannerState) :
    (consumeNewline s).indents = s.indents := by
  unfold consumeNewline
  split
  · exact advance_indents s
  · dsimp only []
    split
    · exact advance_indents s
    · exact advance_indents s
  · rfl


/-- `skipSpaces` only advances, so it never writes the indent stack. -/
lemma skipSpacesLoop_indents (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).indents = s.indents := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' ih =>
    unfold skipSpacesLoop
    split
    · rw [ih, advance_indents]
    · rfl

lemma skipSpaces_currentIndent (s : ScannerState) :
    (skipSpaces s).currentIndent = s.currentIndent := by
  unfold ScannerState.currentIndent skipSpaces; rw [skipSpacesLoop_indents]

/-- **§6.1 at a landing line.**  A tab at or left of the block's current
    indent survives `skipToContentWs` only when the line has nothing else on
    it: what follows the whites is a comment, a break, or the end of input.
    Every other continuation is `tabInIndentation`.

    The `0 ≤ s.currentIndent` premise is what excludes the stream-level
    exemption, where a tab before a flow indicator is legal separation. -/
lemma skipToContentWs_tab_under_indent {s s' : ScannerState}
    (hok : skipToContentWs s = .ok s')
    (hnic : s.needIndentCheck = true)
    (hci : 0 ≤ s.currentIndent)
    (htab : (skipSpaces s).peek? = some '\t')
    (hle : ((skipSpaces s).col : Int) ≤ s.currentIndent) :
    s'.peek? = none ∨
      ∃ ch, s'.peek? = some ch ∧ (ch = '#' ∨ isLineBreakBool ch = true) := by
  unfold skipToContentWs at hok
  rw [ite_eq_left hnic] at hok
  rw [ite_eq_left (by rw [skipSpaces_currentIndent]; simp [hle]), htab] at hok
  split at hok
  · -- the tab branch: what follows the whites decides
    simp only [] at hok
    split at hok
    · rename_i hpk
      have := Except.ok.inj hok; subst this
      exact Or.inr ⟨'#', hpk, Or.inl rfl⟩
    · rename_i c hne hpk
      split at hok
      · rename_i hlb
        have := Except.ok.inj hok; subst this
        exact Or.inr ⟨c, hpk, Or.inr hlb⟩
      · split at hok
        · rename_i hflow
          exfalso
          rw [skipSpaces_currentIndent] at hflow
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hflow
          omega
        · exact absurd hok (by simp)
    · rename_i hpk
      have := Except.ok.inj hok; subst this
      exact Or.inl hpk
  · rename_i hne
    exact absurd rfl hne

/-- **What a tab under the indent leaves of the line** (item 64).  A landing
    whose `[63] s-indent` run under-runs the pending's index and then carries a
    TAB cannot be followed by content: §6.1 refuses the tab unless the line
    stops there, so preprocessing ends at the input's end or at a `#`.

    Stated over the SCALARS the loop transports — the indent and the final
    peek — rather than over the scanner state, so that `unwindIndents` and
    `saveSimpleKey` carry it without a rewrite. -/
def NoLandingTabAt (ci : Int) (pk : Option Char) (sp_mid : SurfPos) : Prop :=
  0 ≤ ci → ∀ j sx, SIndent j sp_mid sx → (sx.col : Int) ≤ ci →
    sx.chars.head? = some '\t' → pk = none ∨ pk = some '#'

/-- The fact as the loop can state it.  §6.1's check runs on a line the loop
    ARRIVED at — so either the check was already armed on entry, or the loop
    crossed a break to get here, and `sp_mid ≠ sp` is how the surface says so.
    Writing the two as one premise is what lets the fact compose through the
    recursion: an iteration discharges it with the break it just consumed and
    never has to know which of the two its own caller had. -/
def LandingTabFacts (ci : Int) (nic : Bool) (pk : Option Char)
    (sp sp_mid : SurfPos) : Prop :=
  (nic = true ∨ sp_mid ≠ sp) → NoLandingTabAt ci pk sp_mid

/-- Move the fact across an iteration: the indent stack is what §6.1 reads,
    and every break re-arms the check. -/
lemma LandingTabFacts.transport {ci ci' : Int} {nic nic' : Bool}
    {pk : Option Char} {sp sp' sp_mid : SurfPos}
    (hci : ci' = ci) (hnic : nic' = true) (h : LandingTabFacts ci' nic' pk sp' sp_mid) :
    LandingTabFacts ci nic pk sp sp_mid := by
  intro _ h0 j sx hind hj htab
  exact h (Or.inl hnic) (by rw [hci]; exact h0) j sx hind (by rw [hci]; exact hj) htab

end L4YAML.Proofs.LandingTab

end Blanket
