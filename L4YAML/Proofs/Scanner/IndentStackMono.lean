/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.IndentStackBase
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-!
# The indent stack is monotone (DOCS item 130)

`ScannerState.WellFormed`'s FIFTH conjunct says consecutive entries of
`indents` have strictly increasing columns.  Like the sixth (item 128), it is
proved for the state OPERATIONS and nowhere for `scanNextToken`, so no proof
downstream of the scanner can spend it.  This file carries it as `Mono`,
through every scanner step, in the shape item 128's walk uses — and it costs
much less than that walk did, because every `indents` equation item 128 proved
is reusable verbatim and only the four writers need an argument of their own.

**What it buys.**  A cover (item 129) says every open mapping level is one of
the frames.  Monotonicity is what turns a fact about the stack's TOP into a
fact about the whole stack: with `Mono`, `s.currentIndent ≤ c` says that every
entry sits at or left of `c`, so every entry AT OR RIGHT of `c` is `c` itself.
That is `IndentStackCover.Covered c [c] s`, the cover with its floor AT the
level a producer opens — payable from the landing alone, without knowing what
stands below it.  At floor 0 the same statement is not payable there: the levels
below `c` are real, and the frames a fused park hands over do not name them.

§1 the predicate, its transports and the two consequences.  §2 the four stack
writers.  §3 the steps that move the stack.  §4 the five `scanNextToken` stages
and the step.  §5 the seed.
-/

namespace L4YAML.Proofs.IndentStackMono

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.FlowIndentStable
open L4YAML.Proofs.IndentStackBase

/-! ## §1  The predicate -/

/-- **The indent stack is strictly increasing**, entry by entry.  This is
    `ScannerState.WellFormed`'s fifth conjunct, on the array alone. -/
def MonoArr (a : Array IndentEntry) : Prop :=
  ∀ (i : Nat) (h : i + 1 < a.size), (a[i]'(by omega)).column < (a[i + 1]'h).column

/-- The same statement about a scanner state. -/
def Mono (s : ScannerState) : Prop := MonoArr s.indents

/-- A step that leaves the stack alone carries it. -/
lemma Mono.of_indents_eq {s s' : ScannerState} (h : Mono s)
    (heq : s'.indents = s.indents) : Mono s' := by
  rw [Mono, heq]; exact h

/-- **Monotone means the top is the maximum.**  Walking up from `i` to the last
    index costs one strict step each time, so the entry at `i` is at or below
    it. -/
lemma MonoArr.le_last {a : Array IndentEntry} (h : MonoArr a) :
    ∀ (j : Nat) (hj : j < a.size) (i : Nat) (hi : i < a.size), i ≤ j →
      (a[i]'hi).column ≤ (a[j]'hj).column := by
  intro j
  induction j with
  | zero =>
    intro hj i hi hij
    have : i = 0 := by omega
    subst this; exact Int.le_refl _
  | succ j ih =>
    intro hj i hi hij
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hjs : j < a.size := by omega
      exact Int.le_trans (ih hjs i hi (by omega)) (Int.le_of_lt (h j hj))
    · have : i = j + 1 := by omega
      subst this; exact Int.le_refl _

/-- `currentIndent` IS the last entry's column, whenever there is one. -/
lemma currentIndent_eq_last {s : ScannerState} (h : 0 < s.indents.size) :
    s.currentIndent = (s.indents[s.indents.size - 1]'(by omega)).column := by
  simp only [ScannerState.currentIndent, Array.back?_eq_getElem?,
    Array.getElem?_eq_getElem (show s.indents.size - 1 < s.indents.size by omega)]

/-- **The consequence the cover spends**: on a monotone stack every entry sits
    at or left of the top. -/
lemma Mono.le_currentIndent {s : ScannerState} (h : Mono s) :
    ∀ e ∈ s.indents, e.column ≤ s.currentIndent := by
  intro e he
  rw [Array.mem_iff_getElem] at he
  obtain ⟨i, hi, rfl⟩ := he
  have hpos : 0 < s.indents.size := by omega
  rw [currentIndent_eq_last hpos]
  exact h.le_last _ (by omega) i hi (by omega)

/-! ## §2  The four stack writers

    A pop keeps every pair it keeps; a push is guarded by `col > currentIndent`
    at each of the four sites, which is exactly the strict step the new top
    owes the old one. -/

lemma monoArr_pop {a : Array IndentEntry} (h : MonoArr a) : MonoArr a.pop := by
  intro i hi
  have h1 : i + 1 < a.size := by
    have := Array.size_pop (xs := a); omega
  have hi0 : i < a.size := by omega
  simp only [Array.getElem_pop]
  exact h i h1

lemma monoArr_push {a : Array IndentEntry} {x : IndentEntry} (h : MonoArr a)
    (hx : ∀ (hs : 0 < a.size), (a[a.size - 1]'(by omega)).column < x.column) :
    MonoArr (a.push x) := by
  intro i hi
  rw [Array.size_push] at hi
  simp only [Array.getElem_push]
  split
  · rename_i hi1
    split
    · rename_i hi2
      exact h i hi2
    · rename_i hi2
      have hpos : 0 < a.size := by omega
      have hlast : i = a.size - 1 := by omega
      subst hlast
      exact hx hpos
  · rename_i hi1
    exact absurd (show i < a.size by omega) hi1

/-- The state-level push, with the guard in the form the writers hand over. -/
lemma mono_push_of_currentIndent {s : ScannerState} {x : IndentEntry}
    (h : Mono s) (hpos : 0 < s.indents.size) (hx : s.currentIndent < x.column) :
    MonoArr (s.indents.push x) := by
  refine monoArr_push h (fun _ => ?_)
  rw [← currentIndent_eq_last hpos]; exact hx

lemma unwindIndentsLoop_mono (s : ScannerState) (col : Int) (fuel : Nat)
    (h : Mono s) : Mono (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; exact h
  | succ fuel ih =>
    unfold unwindIndentsLoop
    split
    · refine ih _ ?_
      show MonoArr ((s.emit .blockEnd).indents.pop)
      rw [emit_indents]
      exact monoArr_pop h
    · exact h

lemma unwindIndents_mono (s : ScannerState) (col : Int) (h : Mono s) :
    Mono (unwindIndents s col) :=
  unwindIndentsLoop_mono s col s.indents.size h

lemma pushMappingIndent_mono (s : ScannerState) (col : Int) (h : Mono s)
    (hbase : SentinelBase s) : Mono (pushMappingIndent s col) := by
  unfold pushMappingIndent
  split
  · rename_i hgt
    show MonoArr (s.indents.push _)
    exact mono_push_of_currentIndent h hbase.size_pos hgt
  · exact h

lemma pushSequenceIndent_mono (s : ScannerState) (col : Int) (h : Mono s)
    (hbase : SentinelBase s) : Mono (pushSequenceIndent s col) := by
  unfold pushSequenceIndent
  split
  · rename_i hgt
    show MonoArr (s.indents.push _)
    exact mono_push_of_currentIndent h hbase.size_pos hgt
  · exact h

/-! ## §3  The steps that move the stack -/

lemma scanDocumentStart_mono (s : ScannerState) (h : Mono s) :
    Mono (scanDocumentStart s) := by
  refine Mono.of_indents_eq (unwindIndents_mono s (-1) h) ?_
  unfold scanDocumentStart
  simp [advanceN_preserves_indents, emit_indents]

lemma scanDocumentEnd_mono {s s' : ScannerState} (hok : scanDocumentEnd s = .ok s')
    (h : Mono s) : Mono s' := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals
    refine Mono.of_indents_eq (unwindIndents_mono s (-1) h) ?_
  all_goals simp [advanceN_preserves_indents, emit_indents]

/-- In BLOCK context the `?` pushes a mapping level at its own column, and the
    push is guarded by `col > currentIndent`. -/
lemma scanKey_mono {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanKey s = .ok s') (h : Mono s) (hbase : SentinelBase s) : Mono s' :=
  Mono.of_indents_eq (pushMappingIndent_mono s (s.col : Int) h hbase)
    (scanKey_indents h_noflow hok)

/-- …and the `-` pushes a sequence level under the same guard. -/
lemma scanBlockEntry_mono {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanBlockEntry s = .ok s') (h : Mono s) (hbase : SentinelBase s) : Mono s' :=
  Mono.of_indents_eq (pushSequenceIndent_mono s (s.col : Int) h hbase)
    (scanBlockEntry_indents h_noflow hok)

/-- `scanValuePrepare`'s own `push` is the fourth writer, and it carries the
    same guard inline (`s.simpleKey.pos.col > s.currentIndent`). -/
lemma scanValuePrepare_mono (s : ScannerState) (h : Mono s) (hbase : SentinelBase s) :
    Mono (scanValuePrepare s) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · rename_i hgt
        show MonoArr (s.indents.push _)
        exact mono_push_of_currentIndent h hbase.size_pos hgt
      · exact h
    · exact h
  · split
    · exact h
    · split
      · exact pushMappingIndent_mono s s.col h hbase
      · exact h

lemma scanValue_mono {s s' : ScannerState} (hok : scanValue s = .ok s')
    (h : Mono s) (hbase : SentinelBase s) : Mono s' := by
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
  refine Mono.of_indents_eq
    (scanValuePrepare_mono _ (h.of_indents_eq h_ck) (hbase.of_indents_eq h_ck)) ?_
  simp [ScannerLoopInvariant.advance_indents, emit_indents]

/-! ## §4  The five stages, and the step -/

lemma preprocess_mono {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : Mono s) : Mono s' := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have h_skip_ids : s_skip.indents = s.indents :=
      skipToContent_preserves_indents s s_skip h_skip
    have h_c : Mono s_skip := h.of_indents_eq h_skip_ids
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, _⟩ := hok
            refine Mono.of_indents_eq ?_ ((closeStaleExplicitKey_indents _).trans (saveSimpleKey_preserves_indents _))
            show Mono { unwindIndents s_skip (s_skip.col : Int) with
              needIndentCheck := false }
            exact Mono.of_indents_eq
              (unwindIndents_mono s_skip (s_skip.col : Int) h_c) rfl
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, _⟩ := hok
            exact Mono.of_indents_eq h_c ((closeStaleExplicitKey_indents _).trans (saveSimpleKey_preserves_indents _))

lemma dispatchStructural_mono {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchStructural s c = .ok (some s')) (h : Mono s) :
    Mono s' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_mono s h
    | exact scanDocumentEnd_mono (by assumption) h
    | exact Mono.of_indents_eq h (scanDirective_preserves_indents (by assumption))

lemma dispatchFlowIndicators_mono {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (h : Mono s) :
    Mono s' :=
  h.of_indents_eq (dispatchFlowIndicators_preserves_indents hok)

lemma dispatchBlockIndicators_mono {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) (h : Mono s)
    (hbase : SentinelBase s) : Mono s' := by
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
      | exact scanBlockEntry_mono h_noflow (by assumption) h hbase
      | exact scanKey_mono h_noflow (by assumption) h hbase
      | exact scanValue_mono (by assumption) h hbase

lemma dispatchContent_mono {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') (h : Mono s) : Mono s' :=
  h.of_indents_eq (dispatchContent_preserves_indents hok)

/-- **The step keeps the stack monotone.**  The four writers are the only ones
    that touch it, and each writes under its own `col > currentIndent` guard. -/
lemma scanNextToken_mono {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : Mono s) (hbase : SentinelBase s) :
    Mono s' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp at hok
    · rename_i sp c h_pre
      have h_pp : Mono sp := preprocess_mono h_pre h
      have h_pb : SentinelBase sp := preprocess_base h_pre hbase
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
          exact dispatchStructural_mono ‹_› h_pp
        · split at hok
          · cases hok
          -- §9.2 bare-document check (item 132)
          split at hok
          · cases hok
          · rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at hok
            · generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_mono h_fi h_pp
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_mono h_bi h_pp h_pb
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
                        exact dispatchContent_mono h_dc h_pp
            · generalize h_sp2 :
                (({ sp with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at hok
              have h_pp2 : Mono sp2 := by rw [← h_sp2]; exact h_pp
              have h_pb2 : SentinelBase sp2 := by rw [← h_sp2]; exact h_pb
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_mono h_fi h_pp2
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_mono h_bi h_pp2 h_pb2
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
                        exact dispatchContent_mono h_dc h_pp2

/-! ## §5  The seed -/

/-- The initial stack is one entry, and one entry has no pair to order. -/
lemma mk'_mono (input : String) : Mono (ScannerState.mk' input) := by
  intro i hi
  exact absurd hi (by simp [ScannerState.mk'])

end L4YAML.Proofs.IndentStackMono

end Blanket
