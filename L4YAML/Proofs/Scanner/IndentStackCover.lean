/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.IndentStackBase
public import L4YAML.Proofs.Scanner.IndentStackMono
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-!
# The indent stack, covered by the frames (DOCS item 129)

Item 127 read a popping landing from the SCANNER's side: the column an accepted
landing rests at is the top entry's own column, on an entry the incoming stack
already held.  `ResumeFrames.resumeAt` asks a SURFACE question about the same
landing — is that width one of the still-open mapping frames? — and the two
sides meet only if the stack's open mapping levels are frames.

This file carries that direction as `Covered lo ks s`: every entry of `s.indents`
that is a MAPPING level at a non-negative column has its column in `ks`.  The
sentinel is exempt by its own `-1` (item 128's conjunct is about the same entry,
from the other side), and sequence levels are exempt because the frames record
mapping widths only — a dedent landing that crosses a sequence level can only
close it (`PreprocessIndentStable.scanValue_top_not_sequence`).

**The walk is cheap where the stack does not move.**  A step's only stack motion
is preprocessing's unwind, which POPS, and one of three pushes: `scanKey`'s
`[187]` at the `?`'s column, and `scanValuePrepare`'s two — the implicit key's
column and, keyless, the `:`'s own.  `scanBlockEntry`'s `[183]` pushes a
SEQUENCE level, which the predicate exempts, and every other stage is an
`indents` equation (item 128 §3 proved those; this file reuses them).  So the
step is `CoverStep`: the cover survives, or ONE mapping level opened, at the
top, and the frames gain exactly its column.

§1 the predicate and its four transports.  §2 the writers.  §3 the step's shape.
§4 the stages.  §5 the step and the seed.
-/

namespace L4YAML.Proofs.IndentStackCover

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.FlowIndentStable
open L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.IndentStackMono

/-! ## §1  The predicate -/

/-- A still-open level as the frame lists name it: the scanner's `IndentEntry`
    with its column a `Nat` and its kind kept (item 332).  `List Nat` lost the
    kind, and a resume fact that must resume a level of ONE kind could not say
    which; carrying it makes "the level at `k` is a mapping" membership of
    `FrameLevel.map k`, read off the list the proof already holds. -/
structure FrameLevel where
  width : Nat
  isSeq : Bool
deriving DecidableEq, Repr

/-- The scanner's entry, as a frame. -/
def FrameLevel.ofEntry (e : IndentEntry) : FrameLevel := ⟨e.column.toNat, e.isSequence⟩

/-- A mapping level of width `k`. -/
abbrev FrameLevel.map (k : Nat) : FrameLevel := ⟨k, false⟩

/-- A sequence level of width `k`. -/
abbrev FrameLevel.seq (k : Nat) : FrameLevel := ⟨k, true⟩

@[simp] lemma FrameLevel.width_map (k : Nat) : (FrameLevel.map k).width = k := rfl
@[simp] lemma FrameLevel.width_seq (k : Nat) : (FrameLevel.seq k).width = k := rfl
@[simp] lemma FrameLevel.map_inj {k k' : Nat} : FrameLevel.map k = FrameLevel.map k' ↔ k = k' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ rfl⟩

/-- **Every open mapping level is a frame.**  `ks` is the accumulation's frame
    list (still-open mapping widths); this says the scanner's stack holds no
    mapping level the surface does not know about.  Negative columns are exempt
    (the sentinel is the only one) and so are sequence levels. -/
def Covered (lo : Nat) (ks : List FrameLevel) (s : ScannerState) : Prop :=
  ∀ e ∈ s.indents, e.isSequence = false → (lo : Int) ≤ e.column → FrameLevel.map e.column.toNat ∈ ks

/-- A step that leaves the stack alone carries the cover. -/
lemma Covered.of_indents_eq {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (h : Covered lo ks s) (heq : s'.indents = s.indents) : Covered lo ks s' := by
  intro e he; rw [heq] at he; exact h e he

/-- A step that only POPS carries it too. -/
lemma Covered.of_subset {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} (h : Covered lo ks s)
    (hsub : ∀ e ∈ s'.indents, e ∈ s.indents) : Covered lo ks s' :=
  fun e he => h e (hsub e he)

/-- The cover is monotone in the frames. -/
lemma Covered.mono {lo : Nat} {ks ks' : List FrameLevel} {s : ScannerState} (h : Covered lo ks s)
    (hsub : ∀ e ∈ ks, e ∈ ks') : Covered lo ks' s :=
  fun e he hseq hnn => hsub _ (h e he hseq hnn)

/-- **Where a carried cover is spendable** (item 148).  A landing reads as a
    frame only at or right of the floor (`preprocess_landing_mem_or_seq`), and
    the landing that spends a park's cover stands BELOW that park's own index —
    so a floor bounded by the index alone is spendable nowhere.  Bounding it by
    the widths alone is the opposite failure: where the frames are empty the
    bound says nothing and the cover weakens to vacuity (`Covered.raise_floor`).
    Both together is the reading that travels: at or below the level's own
    index, and at or below every width the frames name. -/
def Floor (lo n : Nat) (ks : List FrameLevel) : Prop :=
  lo ≤ n ∧ ∀ e ∈ ks, lo ≤ e.width

/-- A frame the surface opens is bounded as soon as its own width is. -/
lemma Floor.cons {lo n c : Nat} {ks : List FrameLevel} (h : Floor lo n ks) (hc : lo ≤ c) :
    Floor lo n (FrameLevel.map c :: ks) :=
  ⟨h.1, fun k' hk' => by
    rcases List.mem_cons.mp hk' with rfl | h'
    · exact hc
    · exact h.2 k' h'⟩

/-- The width a dedent landing names is at or right of the floor — which is
    exactly what `preprocess_landing_mem_or_seq` asks its caller for. -/
lemma Floor.le_of_mem {lo n j : Nat} {ks : List FrameLevel} (h : Floor lo n ks) (hj : FrameLevel.map j ∈ ks) :
    lo ≤ j := h.2 _ hj

/-- A deeper level inherits the bound of the level it opened under. -/
lemma Floor.mono_index {lo n n' : Nat} {ks : List FrameLevel} (h : Floor lo n ks) (hn : n ≤ n') :
    Floor lo n' ks := ⟨Nat.le_trans h.1 hn, h.2⟩

/-- **The dedent's hop on the frames** (item 149).  A landing pops to a width
    the frames already name, and what it resumes on is that width plus the ones
    strictly below it — all of them frames the incoming list held.  So the
    bound travels without moving: the floor was at or below every width in
    `ks`, and `w :: ks'` names nothing `ks` did not. -/
lemma Floor.pop_to {lo n w : Nat} {ks ks' : List FrameLevel}
    (h : Floor lo n ks) (hmem : FrameLevel.map w ∈ ks) (hsub : ∀ e ∈ ks', e ∈ ks) :
    Floor lo w (FrameLevel.map w :: ks') :=
  ⟨h.2 _ hmem, fun e he => by
    rcases List.mem_cons.mp he with rfl | h'
    · exact h.2 _ hmem
    · exact h.2 e (hsub e h')⟩

/-- A width named twice is named once (item 148) — the shape a `:` leaves when
    the level it opens is already one of the frames. -/
lemma Covered.dedup_head {lo k : Nat} {ks : List FrameLevel} {s : ScannerState}
    (h : Covered lo (FrameLevel.map k :: FrameLevel.map k :: ks) s) : Covered lo (FrameLevel.map k :: ks) s :=
  h.mono fun _ hx => by
    rcases List.mem_cons.mp hx with rfl | h'
    · exact List.mem_cons_self
    · exact h'

/-- …in particular a frame the surface opens costs the cover nothing. -/
lemma Covered.cons {lo : Nat} {ks : List FrameLevel} {s : ScannerState} (c : Nat)
    (h : Covered lo ks s) :
    Covered lo (FrameLevel.map c :: ks) s :=
  h.mono fun _ hk => List.mem_cons_of_mem _ hk

/-! ## §2  The writers

    The unwind pops, the sequence push is exempt, and the mapping push is the
    one place the frames have to pay. -/

lemma unwindIndentsLoop_mem (s : ScannerState) (col : Int) (fuel : Nat)
    {e : IndentEntry} : e ∈ (unwindIndentsLoop s col fuel).indents → e ∈ s.indents := by
  induction fuel generalizing s with
  | zero => rw [show unwindIndentsLoop s col 0 = s by unfold unwindIndentsLoop; rfl]; exact id
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

lemma unwindIndents_cover {lo : Nat} {ks : List FrameLevel} {s : ScannerState} (col : Int)
    (h : Covered lo ks s) : Covered lo ks (unwindIndents s col) :=
  h.of_subset fun _ he => unwindIndentsLoop_mem s col s.indents.size he

lemma pushSequenceIndent_cover {lo : Nat} {ks : List FrameLevel} {s : ScannerState} (col : Int)
    (h : Covered lo ks s) : Covered lo ks (pushSequenceIndent s col) := by
  unfold pushSequenceIndent
  split
  · intro e he hseq _
    show FrameLevel.map e.column.toNat ∈ ks
    rcases Array.mem_push.mp (by simpa [ScannerState.emit] using he) with hmem | rfl
    · exact h e (by simpa [ScannerState.emit] using hmem) hseq ‹_›
    · exact absurd hseq (by simp)
  · exact h

/-- **The one place the frames pay.**  `[187]`'s push opens a mapping level at
    `c`, and the cover holds again once `c` is a frame. -/
lemma pushMappingIndent_cover {lo : Nat} {ks : List FrameLevel} {s : ScannerState} (c : Nat)
    (h : Covered lo ks s) : Covered lo (FrameLevel.map c :: ks) (pushMappingIndent s (c : Int)) := by
  unfold pushMappingIndent
  split
  · intro e he hseq hnn
    rcases Array.mem_push.mp (by simpa [ScannerState.emit] using he) with hmem | rfl
    · exact List.mem_cons_of_mem _
        (h e (by simpa [ScannerState.emit] using hmem) hseq hnn)
    · simp
  · exact h.cons c

/-- …and the level it opened is the one on top. -/
lemma pushMappingIndent_back (s : ScannerState) (c : Nat)
    (hgt : (c : Int) > s.currentIndent) :
    (pushMappingIndent s (c : Int)).indents.back?
      = some { column := (c : Int), isSequence := false } := by
  unfold pushMappingIndent
  rw [ite_eq_left hgt]
  show ((s.emit .blockMappingStart).indents.push _).back? = _
  simp

/-! ## §3  The step's shape

    A step opens at most ONE mapping level, and if it did, that level is the
    stack's top — which is where item 127 reads the landing from, so the two
    compose. -/

/-- **What one scanner step does to the cover.**  Either it survives, or one
    mapping level opened at the top and the frames gain exactly its column. -/
def CoverStep (lo : Nat) (ks : List FrameLevel) (s : ScannerState) : Prop :=
  Covered lo ks s ∨ ∃ c : Nat,
    s.indents.back? = some { column := (c : Int), isSequence := false } ∧
      Covered lo (FrameLevel.map c :: ks) s

lemma CoverStep.of_covered {lo : Nat} {ks : List FrameLevel} {s : ScannerState}
    (h : Covered lo ks s) :
    CoverStep lo ks s := Or.inl h

lemma CoverStep.of_indents_eq {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (h : CoverStep lo ks s) (heq : s'.indents = s.indents) : CoverStep lo ks s' := by
  rcases h with h | ⟨c, hb, hc⟩
  · exact Or.inl (h.of_indents_eq heq)
  · exact Or.inr ⟨c, by rw [heq]; exact hb, hc.of_indents_eq heq⟩

/-! ## §4  The stages -/

lemma scanDocumentStart_cover {lo : Nat} {ks : List FrameLevel} {s : ScannerState}
    (h : Covered lo ks s) :
    Covered lo ks (scanDocumentStart s) := by
  refine Covered.of_indents_eq (unwindIndents_cover (-1) h) ?_
  unfold scanDocumentStart
  simp [advanceN_preserves_indents, emit_indents]

lemma scanDocumentEnd_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (hok : scanDocumentEnd s = .ok s') (h : Covered lo ks s) : Covered lo ks s' := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals refine Covered.of_indents_eq (unwindIndents_cover (-1) h) ?_
  all_goals simp [advanceN_preserves_indents, emit_indents]

/-- The `-`'s `[183]` opens a SEQUENCE level, which the frames do not record —
    so the cover survives it untouched. -/
lemma scanBlockEntry_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hok : scanBlockEntry s = .ok s') (h : Covered lo ks s) :
    Covered lo ks s' :=
  Covered.of_indents_eq (pushSequenceIndent_cover (s.col : Int) h)
    (scanBlockEntry_indents h_noflow hok)

/-- The `?`'s `[187]` opens a MAPPING level at the indicator's own column. -/
lemma scanKey_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hok : scanKey s = .ok s') (h : Covered lo ks s) :
    CoverStep lo ks s' := by
  have heq := scanKey_indents h_noflow hok
  by_cases hgt : (s.col : Int) > s.currentIndent
  · exact Or.inr ⟨s.col, by rw [heq]; exact pushMappingIndent_back s s.col hgt,
      (pushMappingIndent_cover s.col h).of_indents_eq heq⟩
  · refine Or.inl (h.of_indents_eq ?_)
    rw [heq]; unfold pushMappingIndent; rw [ite_eq_right hgt]

/-- The `:`'s two pushes: the implicit key's column (`[193]`), and the keyless
    entry's own (`[195]`'s empty key). -/
lemma scanValuePrepare_cover {lo : Nat} {ks : List FrameLevel} {s : ScannerState}
    (h : Covered lo ks s) :
    CoverStep lo ks (scanValuePrepare s) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · rename_i hgt
        refine Or.inr ⟨s.simpleKey.pos.col, by simp, ?_⟩
        intro e he hseq hnn
        rcases Array.mem_push.mp (by simpa using he) with hmem | rfl
        · exact List.mem_cons_of_mem _ (h e (by simpa using hmem) hseq hnn)
        · simp
      · exact Or.inl h
    · exact Or.inl h
  · split
    · exact Or.inl h
    · split
      · by_cases hgt : (s.col : Int) > s.currentIndent
        · exact Or.inr ⟨s.col, pushMappingIndent_back s s.col hgt,
            pushMappingIndent_cover s.col h⟩
        · refine Or.inl (h.of_indents_eq ?_)
          unfold pushMappingIndent; rw [ite_eq_right hgt]
      · exact Or.inl h

lemma scanValue_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (hok : scanValue s = .ok s') (h : Covered lo ks s) : CoverStep lo ks s' := by
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
  refine CoverStep.of_indents_eq (scanValuePrepare_cover (h.of_indents_eq h_ck)) ?_
  simp [ScannerLoopInvariant.advance_indents, emit_indents]

/-! ## §5  The five stages, the step, and the seed -/

/-- Preprocessing's own unwind only POPS, and the key save is an equation. -/
lemma preprocess_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : Covered lo ks s) :
    Covered lo ks s' := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have h_c : Covered lo ks s_skip :=
      h.of_indents_eq (skipToContent_preserves_indents s s_skip h_skip)
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, _⟩ := hok
            refine Covered.of_indents_eq ?_ ((closeStaleExplicitKey_indents _).trans (saveSimpleKey_preserves_indents _))
            show Covered lo ks { unwindIndents s_skip (s_skip.col : Int) with
              needIndentCheck := false }
            exact Covered.of_indents_eq
              (unwindIndents_cover (s_skip.col : Int) h_c) rfl
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, _⟩ := hok
            exact Covered.of_indents_eq h_c ((closeStaleExplicitKey_indents _).trans (saveSimpleKey_preserves_indents _))

lemma dispatchStructural_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchStructural s c = .ok (some s')) (h : Covered lo ks s) :
    Covered lo ks s' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_cover h
    | exact scanDocumentEnd_cover (by assumption) h
    | exact Covered.of_indents_eq h (scanDirective_preserves_indents (by assumption))

lemma dispatchFlowIndicators_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (h : Covered lo ks s) :
    Covered lo ks s' :=
  h.of_indents_eq (dispatchFlowIndicators_preserves_indents hok)

lemma dispatchBlockIndicators_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) (h : Covered lo ks s) :
    CoverStep lo ks s' := by
  by_cases hf : s.inFlow = true
  · exact Or.inl (h.of_indents_eq (dispatchBlockIndicators_preserves_indents hf hok))
  · have h_noflow : s.inFlow = false := by simpa using hf
    unfold scanNextToken_dispatchBlockIndicators at hok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
    repeat (any_goals (split at hok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    all_goals first
      | exact Or.inl (scanBlockEntry_cover h_noflow (by assumption) h)
      | exact scanKey_cover h_noflow (by assumption) h
      | exact scanValue_cover (by assumption) h

lemma dispatchContent_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') (h : Covered lo ks s) :
    Covered lo ks s' :=
  h.of_indents_eq (dispatchContent_preserves_indents hok)

lemma scanNextToken_cover {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : Covered lo ks s) : CoverStep lo ks s' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp at hok
    · rename_i sp c h_pre
      have h_pp : Covered lo ks sp := preprocess_cover h_pre h
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
          exact Or.inl (dispatchStructural_cover ‹_› h_pp)
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
                  exact Or.inl (dispatchFlowIndicators_cover h_fi h_pp)
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_cover h_bi h_pp
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
                        exact Or.inl (dispatchContent_cover h_dc h_pp)
            · generalize h_sp2 :
                (({ sp with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at hok
              have h_pp2 : Covered lo ks sp2 := by rw [← h_sp2]; exact h_pp
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact Or.inl (dispatchFlowIndicators_cover h_fi h_pp2)
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_cover h_bi h_pp2
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
                        exact Or.inl (dispatchContent_cover h_dc h_pp2)

/-! ## §6  The seed -/

/-- The initial stack is the sentinel alone, which no frame has to cover. -/
lemma mk'_cover (input : String) (lo : Nat) (ks : List FrameLevel) :
    Covered lo ks (ScannerState.mk' input) := by
  intro e he _ hnn
  have : e = { column := -1, isSequence := false } := by
    simpa [ScannerState.mk'] using he
  subst this
  simp only [] at hnn
  omega

/-! ## §6  The sequence disjunct, refuted at the `:`

    The cover exempts sequence levels, so a landing that rests on one is not a
    frame — and cannot be made into one, because the frames record mapping
    widths.  §8.2.1 says the scanner refuses that landing, but it says so at the
    `:`'s own validation (`scanValue_top_not_sequence`), which is a state the
    landing's own step does not yet hold.  So the refutation is a lemma the
    CONSUMER spends, not something the landing carries. -/

/-- **A `:` that validates at a landing column puts that column in the frames.**
    The top entry is a mapping level (`scanValue_top_not_sequence` — a saved key
    at or left of the floor whose column is a SEQUENCE level's own is
    `trailing content`), and the cover carries mapping levels to frames. -/
lemma landing_mem_of_value {lo : Nat} {ks : List FrameLevel} {s : ScannerState} {top : IndentEntry}
    (hok : scanValueValidate s = .ok ())
    (h_poss : s.simpleKey.possible = true) (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.simpleKey.pos.col : Int) = top.column)
    (h_le : (s.simpleKey.pos.col : Int) ≤ s.currentIndent)
    (h_floor : lo ≤ s.simpleKey.pos.col)
    (h_cov : Covered lo ks s) :
    FrameLevel.map s.simpleKey.pos.col ∈ ks := by
  have h_seq : top.isSequence = false :=
    scanValue_top_not_sequence hok h_poss h_noflow h_top h_at h_le
  have h_mem : top ∈ s.indents :=
    Array.mem_of_getElem? (by rw [← Array.back?_eq_getElem?]; exact h_top)
  have h_nn : (lo : Int) ≤ top.column := by
    rw [← h_at]; exact Int.ofNat_le.mpr h_floor
  have := h_cov top h_mem h_seq h_nn
  rwa [← h_at, Int.toNat_natCast] at this

/-- **…and the `?` refutes it too** (item 131).  The same disjunct, at the
    other indicator that consumes a landing.  `scanKey` runs §8.2.1's check now,
    so an explicit key accepted at the landing's own column has a mapping level
    under it and the landing is a frame — the exemption is a residue at neither
    consumer. -/
lemma landing_mem_of_key {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    {top : IndentEntry}
    (hok : scanKey s = .ok s') (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.col : Int) = top.column)
    (h_floor : lo ≤ s.col)
    (h_cov : Covered lo ks s) :
    FrameLevel.map s.col ∈ ks := by
  have h_seq : top.isSequence = false :=
    scanKey_top_not_sequence hok h_noflow h_top h_at
  have h_mem : top ∈ s.indents :=
    Array.mem_of_getElem? (by rw [← Array.back?_eq_getElem?]; exact h_top)
  have h_nn : (lo : Int) ≤ top.column := by
    rw [← h_at]; exact Int.ofNat_le.mpr h_floor
  have := h_cov top h_mem h_seq h_nn
  rwa [← h_at, Int.toNat_natCast] at this

/-! ## §7  The floor, and the payment a landing can make alone (item 130)

    `Covered 0` is the whole stack, and it is not what a producer can pay.  A
    producer that opens a mapping at `c` knows the landing and the frames it
    conses — it does NOT know the levels below the node its own park fused, and
    those levels are real: `a:⏎  b: 1⏎  : 2` holds levels 0 and 2 open while a
    root route reads the landing as a fresh document at width 2.  The floor is
    what makes the statement payable: at or right of `c` the stack is `c` alone,
    which is a fact about the TOP once the stack is monotone. -/

/-- Raising the floor weakens the cover: fewer entries are asked about. -/
lemma Covered.raise_floor {lo lo' : Nat} {ks : List FrameLevel} {s : ScannerState}
    (h : Covered lo ks s) (hle : lo ≤ lo') : Covered lo' ks s :=
  fun e he hseq hlo => h e he hseq (Int.le_trans (Int.ofNat_le.mpr hle) hlo)

/-- **The landing's own floor, where the unwind supplies it.**  The unwind stops
    on its guard, so the top is at or left of the column it unwound to; the
    guard's other exit is a stack popped to the sentinel, at `-1`. -/
lemma unwindIndents_top_le {s : ScannerState} {col : Int} (h : SentinelBase s)
    (hnn : 0 ≤ col) : (unwindIndents s col).currentIndent ≤ col := by
  rcases unwindIndents_terminal s col with h1 | h2
  · exact h1
  · rw [(unwindIndents_base s col h).currentIndent_of_size_le_one h2]; omega

/-- **What preprocessing leaves behind**: either the landing has its floor — the
    top at or left of the landing column — or the step did not unwind at all,
    and the stack it hands on is the one it was given.  The right disjunct is
    where a threaded floor would be spent; the left is free. -/
lemma preprocess_top_le_col {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : SentinelBase s) :
    s'.currentIndent ≤ (s'.col : Int) ∨ s'.indents = s.indents := by
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
            have key : (unwindIndents s_skip (s_skip.col : Int)).currentIndent
                ≤ (s_skip.col : Int) :=
              unwindIndents_top_le h_c (Int.natCast_nonneg _)
            exact Or.inl (by
              simpa [ScannerState.currentIndent, unwindIndents_col] using key)
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, _⟩ := hok
            exact Or.inr (by rw [closeStaleExplicitKey_indents, saveSimpleKey_preserves_indents]; exact h_skip_ids)

/-- **The landing's own floor** (item 147) — `preprocess_top_le_col`'s escape,
    closed by the walk that produced the landing.

    That lemma's right disjunct is not "the unwind popped nothing"; it is "the
    unwind never ran", and the unwind runs on exactly one condition outside a
    flow: the indent check is armed when preprocessing reaches it.  The walk
    arms it — `consumeNewline` raises the flag on every `b-break` and
    `skipToContentLoop_needIndentCheck_mono` keeps it up — so a step whose walk
    crossed a break has no escape at all, and the only disjunct left is the
    SENTINEL: a stack popped to one entry, which `SentinelBase` reads as `-1`.

    This is what a landing consumer can spend.  `skipToContentLoop_anyCol_prod`'s
    landing arm hands the flag over for any park off a line start (item 147),
    which is precisely the park a column-0 landing is reached from. -/
lemma preprocess_top_le_col_of_armed {s s_walk s' : ScannerState} {c : Char}
    (h_skip : skipToContent s = .ok s_walk)
    (h_flow : s_walk.inFlow = false)
    (h_nic : s_walk.needIndentCheck = true)
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) :
    s'.currentIndent ≤ (s'.col : Int) ∨ s'.indents.size ≤ 1 := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip'
    have h_eq : s_skip = s_walk := by
      rw [h_skip] at h_skip'; exact (Except.ok.inj h_skip').symm
    subst h_eq
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, _⟩ := hok
            have hcol : (closeStaleExplicitKey (saveSimpleKey { unwindIndents s_skip (s_skip.col : Int) with
                needIndentCheck := false })).col = s_skip.col := by
              rw [closeStaleExplicitKey_col, saveSimpleKey_col]
              exact unwindIndents_col s_skip (s_skip.col : Int)
            have hind : (closeStaleExplicitKey (saveSimpleKey { unwindIndents s_skip (s_skip.col : Int) with
                needIndentCheck := false })).indents
                = (unwindIndents s_skip (s_skip.col : Int)).indents :=
              (closeStaleExplicitKey_indents _).trans (saveSimpleKey_preserves_indents _)
            rcases unwindIndents_terminal s_skip (s_skip.col : Int) with h | h
            · exact Or.inl (by rw [currentIndent_of_indents_eq hind, hcol]; exact h)
            · exact Or.inr (by rw [hind]; exact h)
      · rename_i h_noarm
        exact absurd (by simp [h_flow, h_nic]) h_noarm

/-- **A mapping push cannot leave the top right of the column it pushed at.**
    Either the push happened, and the top IS that column, or it did not, and the
    top is the one the landing already floored. -/
lemma pushMappingIndent_top_le {s : ScannerState} {col : Int}
    (h_floor : s.currentIndent ≤ col) :
    (pushMappingIndent s col).currentIndent ≤ col := by
  unfold pushMappingIndent
  split
  · show (({ (s.emit .blockMappingStart) with
      indents := (s.emit .blockMappingStart).indents.push
        { column := col, isSequence := false } } : ScannerState)).currentIndent ≤ col
    simp [ScannerState.currentIndent]
  · exact h_floor

/-- `[187]`'s `?` opens at its own column, so the landing's floor survives it. -/
lemma scanKey_top_le {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanKey s = .ok s') (h_floor : s.currentIndent ≤ (s.col : Int)) :
    s'.currentIndent ≤ (s.col : Int) := by
  rw [currentIndent_of_indents_eq (scanKey_indents h_noflow hok)]
  exact pushMappingIndent_top_le h_floor

/-- …and so does `[196]`'s keyless `:`, the other opener that pushes at the
    landing's own column.  (With a simple key live the push is at the KEY's
    column instead, which is a different level and a different payment.) -/
lemma scanValuePrepare_top_le_keyless {s : ScannerState}
    (h_nokey : s.simpleKey.possible = false) (h_noexpl : s.explicitKeyLine = none)
    (h_noflow : s.inFlow = false) (h_floor : s.currentIndent ≤ (s.col : Int)) :
    (scanValuePrepare s).currentIndent ≤ (s.col : Int) := by
  unfold scanValuePrepare
  rw [ite_eq_right (by simp [h_nokey]), ite_eq_right (by simp [h_noexpl])]
  rw [ite_eq_left (by simp [h_noflow])]
  exact pushMappingIndent_top_le h_floor

/-- `scanValueClearKey` either leaves the state alone or clears the saved key;
    it touches nothing else (item 147). -/
lemma scanValueClearKey_id_or_clear (s : ScannerState) :
    scanValueClearKey s = s ∨
      scanValueClearKey s = { s with simpleKey := { possible := false } } := by
  unfold scanValueClearKey
  split
  · split
    · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact Or.inl rfl

/-- **`[193]`/`[196]`'s push, bounded by the line's own column** (item 147) —
    the general form of `scanValuePrepare_top_le_keyless`.  With a simple key
    live the push is at the KEY's column, so the bound holds exactly when the
    save was FRESH, which is what preprocessing's landing save makes it.  Both
    other branches either push at `s.col` itself or push nothing. -/
lemma scanValuePrepare_top_le {s : ScannerState}
    (h_fresh : s.simpleKey.possible = true → s.simpleKey.pos.col = s.col)
    (h_floor : s.currentIndent ≤ (s.col : Int)) :
    (scanValuePrepare s).currentIndent ≤ (s.col : Int) := by
  unfold scanValuePrepare
  split
  · rename_i h_poss
    split
    · split
      · show ((_ : ScannerState)).currentIndent ≤ _
        simp only [ScannerState.currentIndent]
        rw [Array.back?_push]
        simp only []
        rw [h_fresh h_poss]
        exact Int.le_refl _
      · exact h_floor
    · exact h_floor
  · split
    · exact h_floor
    · split
      · exact pushMappingIndent_top_le h_floor
      · exact h_floor

/-- The `:`'s whole step, bounded the same way (item 147): the key clear moves
    no indent, the prepare is the only writer, and the emit and the advance
    leave the stack alone. -/
lemma scanValue_top_le {s s' : ScannerState}
    (hok : scanValue s = .ok s')
    (h_fresh : s.simpleKey.possible = true → s.simpleKey.pos.col = s.col)
    (h_floor : s.currentIndent ≤ (s.col : Int)) :
    s'.currentIndent ≤ (s.col : Int) := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok; subst hok
  have key : (scanValuePrepare (scanValueClearKey s)).currentIndent ≤ (s.col : Int) := by
    rcases scanValueClearKey_id_or_clear s with h | h
    · rw [h]; exact scanValuePrepare_top_le h_fresh h_floor
    · rw [h]
      refine scanValuePrepare_top_le (fun hp => absurd hp (by simp)) ?_
      show ({ s with simpleKey := { possible := false } } : ScannerState).currentIndent ≤ _
      exact h_floor
  show (((scanValuePrepare (scanValueClearKey s)).emit _).advance).currentIndent ≤ _
  rw [currentIndent_of_indents_eq
    (by simp [ScannerLoopInvariant.advance_indents, emit_indents] :
      (((scanValuePrepare (scanValueClearKey s)).emit YamlToken.value).advance).indents
        = (scanValuePrepare (scanValueClearKey s)).indents)]
  exact key

/-- **What the key clear leaves the `:` to read** (item 148).  Either the saved
    key survives at its own column, or it is gone AND an explicit `?` line is
    what took it — which is the branch `scanValuePrepare` answers without
    pushing at all.  The third shape, an empty register with no `?` line, is
    `[196]`'s keyless entry, and this lemma says a live key never reaches it. -/
lemma scanValueClearKey_arm {s : ScannerState} (h : s.simpleKey.possible = true) :
    ((scanValueClearKey s).simpleKey.possible = true ∧
        (scanValueClearKey s).simpleKey.pos.col = s.simpleKey.pos.col) ∨
      ((scanValueClearKey s).simpleKey.possible = false ∧
        (scanValueClearKey s).explicitKeyLine.isSome = true) := by
  unfold scanValueClearKey
  split
  · rename_i ekLine h_ek
    split
    · exact Or.inr ⟨rfl, by simp [h_ek]⟩
    · split
      · exact Or.inr ⟨rfl, by simp [h_ek]⟩
      · exact Or.inl ⟨h, rfl⟩
  · exact Or.inl ⟨h, rfl⟩

/-- **The implicit `:`'s own column bound** (item 402): a live block-context key at
    or right of the stack top keeps the top at or left of the KEY's column through
    `scanValuePrepare` — the push lands exactly at the key's column, and the no-push
    branch (key at or left of the top) collapses to equality under the premise. -/
lemma scanValuePrepare_top_le_key {s : ScannerState}
    (h_poss : s.simpleKey.possible = true) (h_noflow : s.inFlow = false)
    (h_floor : s.currentIndent ≤ (s.simpleKey.pos.col : Int)) :
    (scanValuePrepare s).currentIndent ≤ (s.simpleKey.pos.col : Int) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · show ((_ : ScannerState)).currentIndent ≤ _
        simp only [ScannerState.currentIndent]
        rw [Array.back?_push]
        simp only []
        exact Int.le_refl _
      · exact h_floor
    · rename_i h
      exact absurd h (by simp [h_noflow])
  · rename_i h
    exact absurd h_poss h

/-- The `:`'s whole step under a live key (item 402), `scanValue_top_le`'s twin for
    the IMPLICIT key: the clear either keeps the key (and the prepare pushes at its
    column) or drops it for an explicit `?` line (and the prepare moves nothing). -/
lemma scanValue_top_le_key {s s' : ScannerState}
    (hok : scanValue s = .ok s')
    (h_poss : s.simpleKey.possible = true) (h_noflow : s.inFlow = false)
    (h_floor : s.currentIndent ≤ (s.simpleKey.pos.col : Int)) :
    s'.currentIndent ≤ (s.simpleKey.pos.col : Int) := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only [Except.ok.injEq] at hok; subst hok
  have key : (scanValuePrepare (scanValueClearKey s)).currentIndent ≤ (s.simpleKey.pos.col : Int) := by
    have harm := scanValueClearKey_arm h_poss
    rcases scanValueClearKey_id_or_clear s with h | h
    · rw [h]; exact scanValuePrepare_top_le_key h_poss h_noflow h_floor
    · rw [h] at harm ⊢
      rcases harm with ⟨hp, _⟩ | ⟨_, hek⟩
      · exact absurd hp (by simp)
      · unfold scanValuePrepare
        simp only [hek, Bool.false_eq_true, ite_false, ite_true]
        exact h_floor
  show (((scanValuePrepare (scanValueClearKey s)).emit _).advance).currentIndent ≤ _
  rw [currentIndent_of_indents_eq
    (by simp [ScannerLoopInvariant.advance_indents, emit_indents] :
      (((scanValuePrepare (scanValueClearKey s)).emit YamlToken.value).advance).indents
        = (scanValuePrepare (scanValueClearKey s)).indents)]
  exact key

/-- **The `:` opens at the KEY's own column** (item 148) — the named form of
    `scanValuePrepare_cover`.  That lemma reports the opened level with an
    existential, which is all a step-generic caller can say; a caller that holds
    the live key holds its column too, so the frames it hands on are `k :: ks`
    for a KNOWN `k` rather than `c :: ks` for an unknown one.  The first premise
    is what keeps `[196]`'s keyless push at `s.col` out: that branch wants the
    register empty and no `?` line, and the two arms here are the other two. -/
lemma scanValuePrepare_cover_key {lo k : Nat} {ks : List FrameLevel} {s : ScannerState}
    (h_arm : s.simpleKey.possible = true ∨ s.explicitKeyLine.isSome = true)
    (h_col : s.simpleKey.possible = true → s.simpleKey.pos.col = k)
    (h : Covered lo ks s) :
    Covered lo (FrameLevel.map k :: ks) (scanValuePrepare s) := by
  unfold scanValuePrepare
  split
  · rename_i h_poss
    split
    · split
      · intro e he hseq hnn
        rcases Array.mem_push.mp (by simpa using he) with hmem | rfl
        · exact List.mem_cons_of_mem _ (h e (by simpa using hmem) hseq hnn)
        · simp [h_col h_poss]
      · exact h.cons k
    · exact h.cons k
  · rename_i h_nposs
    split
    · exact h.cons k
    · rename_i h_noexpl
      exact absurd (h_arm.resolve_left (by simpa using h_nposs)) (by simp [h_noexpl])

/-- The `:`'s whole step (item 148): the key clear either keeps the column or
    hands the prepare its `?` line, the prepare is the only writer, and the emit
    and the advance leave the stack alone. -/
lemma scanValue_cover_key {lo k : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (hok : scanValue s = .ok s') (h_poss : s.simpleKey.possible = true)
    (h_col : s.simpleKey.pos.col = k) (h : Covered lo ks s) :
    Covered lo (FrameLevel.map k :: ks) s' := by
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
  have key : Covered lo (FrameLevel.map k :: ks) (scanValuePrepare (scanValueClearKey s)) := by
    rcases scanValueClearKey_arm h_poss with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact scanValuePrepare_cover_key (Or.inl h1) (fun _ => h2.trans h_col)
        (h.of_indents_eq h_ck)
    · exact scanValuePrepare_cover_key (Or.inr h2) (fun hp => absurd hp (by simp [h1]))
        (h.of_indents_eq h_ck)
  exact key.of_indents_eq
    (by simp [ScannerLoopInvariant.advance_indents, emit_indents])

/-- **The payment.**  On a monotone stack every entry is at or left of the top,
    so a top at or left of `c` leaves exactly one level at or right of `c` — `c`
    itself, if it is open at all.  This is the cover a producer that opens a
    mapping at the landing can hand over without knowing anything below it. -/
lemma covered_singleton_of_top_le {s : ScannerState} {c : Nat}
    (h_mono : Mono s) (h_top : s.currentIndent ≤ (c : Int)) : Covered c [FrameLevel.map c] s := by
  intro e he _ hlo
  have hle : e.column ≤ s.currentIndent := h_mono.le_currentIndent e he
  have hc : e.column = (c : Int) := by omega
  rw [hc, Int.toNat_natCast]
  exact List.mem_cons_self

/-- **A step whose top is pinned names the level it opened** (item 259).
    `CoverStep` reports an opened level with an existential, which is all a
    step-generic lemma can say; a producer that holds the top from both sides
    — the floor its park measured and the bound the step's own push obeys —
    knows the top IS its index, and the frames it hands on are `k :: ks` for
    that index rather than `c :: ks` for an unknown `c`.  The left arm costs
    the frames nothing (`Covered.cons`); in the right arm the opened level is
    the top, and the top is `k`. -/
lemma CoverStep.cons_of_top_eq {lo k : Nat} {ks : List FrameLevel} {s : ScannerState}
    (h : CoverStep lo ks s) (h_top : s.currentIndent = (k : Int)) :
    Covered lo (FrameLevel.map k :: ks) s := by
  rcases h with h | ⟨c, hb, hc⟩
  · exact h.cons k
  · have hck : c = k := by
      have : s.currentIndent = (c : Int) := by simp [ScannerState.currentIndent, hb]
      omega
    subst hck; exact hc

/-- **The dedent's hop on the stack** (item 149) — `covered_singleton_of_top_le`
    for a cover that is already carried rather than freshly measured.  The same
    two readings do the work: the landing's own floor puts the top at or left of
    `w`, and monotonicity puts every remaining entry at or left of the top.  So
    a level the cover still names is `w` itself or strictly left of it — and the
    frames strictly left of `w` are exactly the ones the landing resumes on
    (`ResumeFrames.resumeAt`'s `ResumeWidths`, whose `keep` direction is this
    lemma's third argument).  What it does NOT need is the floor's own value: the
    incoming cover keeps it, and this hop only re-lists the widths. -/
lemma Covered.pop_to {lo w : Nat} {ks ks' : List FrameLevel} {s : ScannerState}
    (h_mono : Mono s) (h_top : s.currentIndent ≤ (w : Int))
    (h_keep : ∀ e ∈ ks, e.width < w → e ∈ ks')
    (h : Covered lo ks s) : Covered lo (FrameLevel.map w :: ks') s := by
  intro e he hseq hlo
  have hle : e.column ≤ s.currentIndent := h_mono.le_currentIndent e he
  have hmem := h e he hseq hlo
  have hnn : (0 : Int) ≤ e.column := Int.le_trans (Int.natCast_nonneg lo) hlo
  have hlew : e.column.toNat ≤ w := by omega
  rcases Nat.lt_or_ge e.column.toNat w with hlt | hge
  · exact List.mem_cons_of_mem _ (h_keep _ hmem hlt)
  · rw [Nat.le_antisymm hlew hge]; exact List.mem_cons_self

/-- **The value-line seed** (item 150).  A value-line-bottomed stack names the
    mapping levels INSIDE an explicit key and stops at the `?`: resuming at the
    `?`'s own column is that entry's unpaid value line, not a sibling, so the
    level the `?` opened is deliberately not one of the frames.  A cover over
    those frames therefore cannot stand at the `?`'s own floor — it starts ONE
    column above it, and there it is the EMPTY cover, because a monotone stack's
    top is its maximum and the `?`'s push put that top at `c`.  This is what the
    `?` producer pays, and it is why the value-line faces carry
    `Floor lo (n + 1) ks` where the stream faces carry `Floor lo n ks`. -/
lemma covered_nil_of_top_le {s : ScannerState} {c : Nat}
    (h_mono : Mono s) (h_top : s.currentIndent ≤ (c : Int)) : Covered (c + 1) [] s := by
  intro e he _ hlo
  have hle : e.column ≤ s.currentIndent := h_mono.le_currentIndent e he
  exfalso
  have hc : ((c : Int) + 1) ≤ e.column := by exact_mod_cast hlo
  omega

/-- **The seed's cover** (item 256).  A stack whose top is NEGATIVE holds the
    sentinel alone, so no mapping level stands at or right of column 0 and the
    empty frame list covers it at floor 0 — the one floor every dedent width is
    at or right of.  This is what the stream's root `-` pays: the park it is
    dispatched from crossed no walk, its stack is the seed's, and `h_ntop` says
    exactly that the top is below zero.  The base is not needed: monotonicity
    puts every entry at or left of the top, and the top is below the floor. -/
lemma covered_nil_of_ntop {s : ScannerState}
    (h_mono : Mono s) (h_ntop : s.currentIndent < 0) : Covered 0 [] s := by
  intro e he _ hlo
  exfalso
  have := h_mono.le_currentIndent e he
  omega

/-- **A SEQUENCE push cannot leave the top right of the column it pushed at**
    (item 204) — `pushMappingIndent_top_le`'s twin on the other opener.  Either
    the push happened and the top IS that column, or it did not and the top is
    the one the landing already floored. -/
lemma pushSequenceIndent_top_le {s : ScannerState} {col : Int}
    (h_floor : s.currentIndent ≤ col) :
    (pushSequenceIndent s col).currentIndent ≤ col := by
  unfold pushSequenceIndent
  split
  · show (({ (s.emit .blockSequenceStart) with
      indents := (s.emit .blockSequenceStart).indents.push
        { column := col, isSequence := true } } : ScannerState)).currentIndent ≤ col
    simp [ScannerState.currentIndent]
  · exact h_floor

/-- **`[183]`'s `-` opens at its OWN column, so the landing's floor survives
    it** (item 204) — `scanKey_top_le`'s twin.  This is the upper bound the
    entry parks owed: `pendingBlock.h_floor` says the stack reaches DOWN to the
    entry's index, and this says it reaches no FURTHER RIGHT, which together
    pin the top at the indicator's column. -/
lemma scanBlockEntry_top_le {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanBlockEntry s = .ok s') (h_floor : s.currentIndent ≤ (s.col : Int)) :
    s'.currentIndent ≤ (s.col : Int) := by
  rw [currentIndent_of_indents_eq (scanBlockEntry_indents h_noflow hok)]
  exact pushSequenceIndent_top_le h_floor

end L4YAML.Proofs.IndentStackCover

end Blanket
