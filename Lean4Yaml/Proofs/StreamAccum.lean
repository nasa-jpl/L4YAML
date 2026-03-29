import Lean4Yaml.Proofs.DocumentProduction
import Lean4Yaml.Proofs.PreprocessProduction

/-! # Stream Grammar Accumulator (Layer 4c)

    Threads a grammar accumulator through `scanLoop` alongside `ScannerSurfCorr`,
    narrowing the sorry in `scan_content_gives_stream` from the entire stream
    construction to a single per-token step.

    ## Architecture

    The scan loop processes tokens one at a time via `scanNextToken`. Each call
    advances the scanner position (tracked by `ScannerSurfCorr`). Layer 4c
    threads an additional invariant: the portion scanned so far forms a valid
    `SLYamlStream`.

    The grammar accumulator is simply `SLYamlStream sp_start sp_current` —
    the entire consumed portion is a valid stream at every step. This works
    because `SLYamlStream` can be extended:
    - `stream_append_suffix` for `...` tokens
    - `stream_implicit_continue` for `---` + content
    - An `afterDoc` state is just `SLYamlStream` itself

    ## Sorry narrowing

    The broad sorry in `scan_content_gives_stream` (covering full stream
    construction) is replaced by a sorry in `scanNextToken_accum_step`
    (covering a single token's contribution to the stream). This precisely
    isolates the gap to per-token production coupling.

    When all content `_prod` theorems (Layer 4a remaining) are complete,
    `scanNextToken_accum_step` can be proven by case-splitting on the token
    dispatch branch, using the appropriate `_prod` theorem for each case.
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.StreamAccum

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScanStrictCoupling
open Lean4Yaml.Proofs.ScannerCoupling
open Lean4Yaml.Proofs.ScalarCoupling
open Lean4Yaml.Proofs.DocumentProduction
open Lean4Yaml.Proofs.PreprocessProduction

/-! ## §1 Per-Dispatch Grammar Accumulator Lemmas

    Each dispatcher has a sorry lemma producing `SLYamlStream sp_start sp'`.
    The preprocessing is included in each — the characters consumed by
    `skipToContent` are part of the grammar production (e.g., `SLDocumentPrefix`
    for inter-document whitespace, or `SSLComments` for trailing material).

    ### §1a Preprocessing + EOF

    When `scanNextToken_preprocess` returns `none`, the scanner reached EOF.
    All remaining characters (whitespace, comments, breaks) form trailing
    grammar material that extends the stream. -/

theorem preprocessing_eof_extends_stream (sc : ScannerState) (sp_start sp : SurfPos)
    (h_stream : SLYamlStream sp_start sp)
    (h_corr : ScannerSurfCorr sc sp)
    (h_preprocess : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  -- The gap sp → sp_final is whitespace/comments consumed by skipToContent
  -- before EOF was detected. This forms GStar SLComment → SLDocumentPrefix.
  -- At col=0: directly via skipToContent_documentPrefix_prod.
  -- At col>0: first iteration consumes trailing ws + break → col=0, then standard.
  -- At EOF with sp.chars=[]: gap is zero (sp = sp_final).
  sorry

/-! ### §1b Preprocessing + Structural Dispatch

    `scanNextToken_dispatchStructural` handles `---`, `...`, `%`-directives.
    Combined with preprocessing: the preprocessing produces `SLDocumentPrefix`,
    and the structural token extends the stream accordingly. -/

theorem accum_step_structural (sc : ScannerState) (sp_start sp : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp)
    (h_corr : ScannerSurfCorr sc sp)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp', SLYamlStream sp_start sp' ∧ ScannerSurfCorr s' sp' := by
  -- Preprocessing → SLDocumentPrefix. Then:
  -- `---` → scanDocumentStart_prod → SCDirectivesEnd → stream_implicit_continue
  -- `...` → scanDocumentEnd_prod → SCDocumentEnd → stream_append_suffix
  -- `%`  → scanDirective_prod → absorbed into document prefix
  sorry

/-! ### §1c Preprocessing + Flow Indicator Dispatch

    `scanNextToken_dispatchFlowIndicators` handles `[`, `]`, `{`, `}`, `,`.
    These are single-character tokens within flow collections. -/

theorem accum_step_flow (sc : ScannerState) (sp_start sp : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp)
    (h_corr : ScannerSurfCorr sc sp)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp', SLYamlStream sp_start sp' ∧ ScannerSurfCorr s' sp' := by
  -- Flow indicators are single-char advances within an ongoing document.
  -- Preprocessing → SSLComments or SLDocumentPrefix.
  -- Flow indicator → part of SFlowSequence/SFlowMapping content.
  sorry

/-! ### §1d Preprocessing + Block Indicator Dispatch

    `scanNextToken_dispatchBlockIndicators` handles `-`, `?`, `:`.
    Block indicators modify indentation tracking and emit structure tokens. -/

theorem accum_step_block (sc : ScannerState) (sp_start sp : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp)
    (h_corr : ScannerSurfCorr sc sp)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp', SLYamlStream sp_start sp' ∧ ScannerSurfCorr s' sp' := by
  -- Block indicators extend block collections: - (sequence entry),
  -- ? (mapping key), : (mapping value). Part of SBlockSequence/SBlockMapping.
  sorry

/-! ### §1e Preprocessing + Content Dispatch

    `scanNextToken_dispatchContent` handles all content tokens:
    `&` anchor, `*` alias, `!` tag, `|`/`>` block scalar, `"` double-quoted,
    `'` single-quoted, plain scalar. Never returns `none`. -/

theorem accum_step_content (sc : ScannerState) (sp_start sp : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp)
    (h_corr : ScannerSurfCorr sc sp)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp', SLYamlStream sp_start sp' ∧ ScannerSurfCorr s' sp' := by
  -- Content tokens produce grammar nodes within the current document.
  -- Preprocessing → SLDocumentPrefix or SSLComments (separation).
  -- Content → appropriate _prod theorem:
  --   scanDoubleQuoted_prod ✅, scanSingleQuoted_prod ✅,
  --   scanAnchorOrAlias_*_prod ✅, scanTag_prod ✅,
  --   scanPlainScalar_prod ❌, scanBlockScalar_prod ❌,
  --   flow collection _prod ❌, block collection _prod ❌
  sorry

/-! ### §1f Composition: Per-Dispatch → Full accum_step

    Unfold `scanNextToken`, split on preprocessing and dispatch results,
    and delegate to the per-dispatch sorry lemmas above. -/

theorem scanNextToken_accum_step (sc : ScannerState) (sp_start sp : SurfPos)
    (s' : ScannerState)
    (h_stream : SLYamlStream sp_start sp)
    (h_corr : ScannerSurfCorr sc sp)
    (h_ok : scanNextToken sc = .ok (some s')) :
    ∃ sp', SLYamlStream sp_start sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · exact absurd (Except.ok.inj h_ok) nofun
    · rename_i s_pre c_pre h_pre
      split at h_ok
      · simp at h_ok
      · split at h_ok
        · rename_i s_str h_str
          have h := Except.ok.inj h_ok; injection h with h; subst h
          exact accum_step_structural sc sp_start sp s_pre s_str c_pre
            h_stream h_corr h_pre h_str
        · -- Past structural dispatch: allowDirectives update
          split at h_ok
          · simp at h_ok
          · -- scanNextToken_checkBlockFlowIndent — pure check, no state change
            split at h_ok
            · simp at h_ok
            · split at h_ok
              · rename_i s_flow h_flow
                have h := Except.ok.inj h_ok; injection h with h; subst h
                exact accum_step_flow sc sp_start sp s_pre s_flow c_pre
                  h_stream h_corr h_pre h_flow
              · split at h_ok
                · simp at h_ok
                · split at h_ok
                  · rename_i s_blk h_blk
                    have h := Except.ok.inj h_ok; injection h with h; subst h
                    exact accum_step_block sc sp_start sp s_pre s_blk c_pre
                      h_stream h_corr h_pre h_blk
                  · split at h_ok
                    · simp at h_ok
                    · rename_i s_cnt h_cnt
                      have h := Except.ok.inj h_ok; injection h with h; subst h
                      exact accum_step_content sc sp_start sp s_pre s_cnt c_pre
                        h_stream h_corr h_pre h_cnt

/-! ## §2 EOF Step: scanNextToken returns none

    When `scanNextToken` returns `.ok none`, the only code path is through
    `scanNextToken_preprocess` returning `none` (EOF detected).
    Proven by unfolding `scanNextToken` and contradicting all `some` paths. -/

theorem scanNextToken_none_stream (sc : ScannerState) (sp_start sp : SurfPos)
    (h_stream : SLYamlStream sp_start sp)
    (h_corr : ScannerSurfCorr sc sp)
    (h_ok : scanNextToken sc = .ok none) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · rename_i h_pre
      exact preprocessing_eof_extends_stream sc sp_start sp h_stream h_corr h_pre
    · split at h_ok
      · simp at h_ok
      · split at h_ok
        · exact absurd (Except.ok.inj h_ok) nofun
        · split at h_ok
          · simp at h_ok
          · split at h_ok
            · simp at h_ok
            · split at h_ok
              · exact absurd (Except.ok.inj h_ok) nofun
              · split at h_ok
                · simp at h_ok
                · split at h_ok
                  · exact absurd (Except.ok.inj h_ok) nofun
                  · split at h_ok
                    · simp at h_ok
                    · exact absurd (Except.ok.inj h_ok) nofun

/-! ## §3 scanLoop with Grammar Accumulation

    Fuel induction threading both `ScannerSurfCorr` and `SLYamlStream`. -/

theorem scanLoop_grammar_prod (sc : ScannerState) (sp_start sp : SurfPos)
    (fuel : Nat) (tokens : Array (Positioned YamlToken))
    (h_stream : SLYamlStream sp_start sp)
    (h_corr : ScannerSurfCorr sc sp)
    (h_ok : scanLoop sc fuel = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  induction fuel generalizing sc sp tokens with
  | zero => simp [scanLoop] at h_ok
  | succ fuel' ih =>
    simp only [scanLoop] at h_ok
    split at h_ok
    · -- scanNextToken = .error → contradicts .ok
      simp at h_ok
    · -- scanNextToken = .ok none → EOF
      rename_i h_none
      -- Validate flow/directive checks (they don't affect grammar)
      split at h_ok <;> try (simp at h_ok; done)
      split at h_ok <;> try (simp at h_ok; done)
      -- Scanner reached EOF — stream is complete
      exact scanNextToken_none_stream sc sp_start sp h_stream h_corr h_none
    · -- scanNextToken = .ok (some s') → one step + recurse
      rename_i s_next h_next
      obtain ⟨sp', h_stream', h_corr'⟩ :=
        scanNextToken_accum_step sc sp_start sp s_next h_stream h_corr h_next
      exact ih s_next sp' tokens h_stream' h_corr' h_ok

/-! ## §4 Initial Stream + BOM Handling

    Establish the initial `SLYamlStream` and `ScannerSurfCorr` for `scan`. -/

/-- BOM at position 0: `'\uFEFF'` gives `SLDocumentPrefix.bom`. -/
theorem bom_advance_gives_prefix (input : String) (sp : SurfPos)
    (h_corr : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart) sp)
    (h_peek : ((ScannerState.mk' input).emit .streamStart).peek? = some '\uFEFF') :
    ∃ sp', SLDocumentPrefix sp sp' ∧
           ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart).advance sp' := by
  have h_more := peek_some_hasMore _ _ h_peek
  obtain ⟨rest, h_chars⟩ := peek_some_chars _ sp '\uFEFF' h_corr h_peek
  have h_col := h_corr.col_eq
  have h_sp_eq : sp = ⟨'\uFEFF' :: rest, 0⟩ := by
    cases sp with | mk cs cl =>
    dsimp only [] at h_chars h_col ⊢
    subst h_chars
    have : cl = 0 := by
      rw [h_col]; unfold ScannerState.emit ScannerState.mk'; rfl
    subst this; rfl
  subst h_sp_eq
  -- After advancing past BOM, we're at ⟨rest, 1⟩ with col = 1
  have h_adv := advance_non_newline_corr
    ((ScannerState.mk' input).emit .streamStart) '\uFEFF' rest
    h_corr h_more (by decide) (by decide)
  exact ⟨⟨rest, 1⟩,
         SLDocumentPrefix.bom rest 0 ⟨rest, 1⟩ (GStar.nil _),
         h_adv⟩

/-- Initial stream: at position 0, the empty stream is valid. -/
theorem initial_stream_and_prefix (input : String) :
    ∃ sp, SLYamlStream ⟨input.toList, 0⟩ sp ∧
          ScannerSurfCorr
            (match (ScannerState.mk' input |>.emit .streamStart).peek? with
             | some '\uFEFF' => (ScannerState.mk' input |>.emit .streamStart).advance
             | _ => ScannerState.mk' input |>.emit .streamStart) sp := by
  have h_chars := CouplingBridge.chars_from_zero_toList input
  have h_init := initial_corr input input.toList h_chars
  have h_emit : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart)
      ⟨input.toList, 0⟩ :=
    ⟨h_init.chars_from, h_init.col_eq, h_init.end_eq⟩
  split
  · -- BOM present
    rename_i h_peek
    obtain ⟨sp', h_prefix, h_corr'⟩ := bom_advance_gives_prefix input _ h_emit h_peek
    -- prefix gives SLDocumentPrefix, wrap in SLYamlStream.single
    exact ⟨sp',
      SLYamlStream.single ⟨input.toList, 0⟩ sp' sp' sp'
        (GStar.cons _ sp' _ h_prefix (GStar.nil _))
        (GOpt.none _) (GStar.nil _),
      h_corr'⟩
  · -- No BOM
    exact ⟨⟨input.toList, 0⟩, empty_to_stream _, h_emit⟩

/-! ## §5 Top-Level Composition: scan → SLYamlStream

    Compose initial stream + scanLoop_grammar_prod to prove scan_content_gives_stream.
    This replaces the broad sorry with the narrower per-token sorry. -/

-- The improved version of scan_content_gives_stream.
-- The remaining sorry is now isolated in scanNextToken_accum_step (§1)
-- and scanNextToken_none_stream (§2).
theorem scan_content_gives_stream_v2
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
                           sp_final.chars = [] := by
  unfold scan at h
  simp only [] at h
  obtain ⟨sp, h_stream, h_corr⟩ := initial_stream_and_prefix input
  exact scanLoop_grammar_prod _ ⟨input.toList, 0⟩ sp _ tokens h_stream h_corr h

/-! ## §6 Gap Analysis

    Five sorry lemmas remain, each precisely scoped to one dispatch path:

    1. `preprocessing_eof_extends_stream` (§1a): When preprocessing reaches
       EOF, extend stream with trailing whitespace/comments. Requires
       showing the gap forms `SLDocumentPrefix` (via `GStar SLComment`).
       At col=0: direct via `skipToContent_documentPrefix_prod`.
       At col>0: first consumed break transitions to col=0, then standard.

    2. `accum_step_structural` (§1b): `---`/`...`/`%` via existing `_prod`
       theorems. Closest to proven: `scanDocumentStart_prod` ✅,
       `scanDocumentEnd_prod` ✅, `scanDirective_prod` ✅.

    3. `accum_step_flow` (§1c): Flow indicators `[`,`]`,`{`,`}`,`,`.
       Single-char advance tokens within flow collections.

    4. `accum_step_block` (§1d): Block indicators `-`,`?`,`:`.
       Indent tracking + structure token emission.

    5. `accum_step_content` (§1e): Content tokens (scalars, anchors, tags).
       Status: `scanDoubleQuoted_prod` ✅, `scanSingleQuoted_prod` ✅,
       `scanAnchorOrAlias_*_prod` ✅, `scanTag_prod` ✅,
       `scanPlainScalar_prod` ❌, `scanBlockScalar_prod` ❌,
       flow/block collections ❌.

    Proven (composition-only, delegating to above sorry):
    - `scanNextToken_accum_step` (§1f): unfolds `scanNextToken`, dispatches
    - `scanNextToken_none_stream` (§2): unfolds `scanNextToken`, EOF path
    - `scanLoop_grammar_prod` (§3): fuel induction
    - `scan_content_gives_stream_v2` (§5): top-level composition

    Total sorry narrowing: 1 broad sorry → 5 precisely scoped sorry.
    Each sorry isolates a specific scanner dispatch path.
-/

end Lean4Yaml.Proofs.StreamAccum
