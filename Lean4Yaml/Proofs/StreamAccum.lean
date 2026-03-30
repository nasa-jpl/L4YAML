import Lean4Yaml.Proofs.DocumentProduction
import Lean4Yaml.Proofs.PreprocessProduction

/-! # Stream Grammar Accumulator (Layer 4c → 4d: Lagging Grammar)

    Threads a grammar accumulator through `scanLoop` alongside `ScannerSurfCorr`,
    narrowing the sorry in `scan_content_gives_stream` to per-dispatch lemmas.

    ## Architecture: The Lagging Invariant

    Scanner token boundaries don't align with grammar production boundaries
    (see MISMATCH.md). Grammar productions like `SBlockNode.flowInBlock` require
    prefix (`SSeparate`) + content (`SFlowNode`) + postfix (`SSLComments`), but
    the postfix is consumed during the NEXT token's preprocessing.

    The fix: a **lagging grammar accumulator** where the grammar position trails
    the scanner by one `SSLComments`:

        ∀ token step:
          SLYamlStream sp_start sp_gram  ∧      -- grammar up to here
          PendingNode sp_gram sp_scan    ∧      -- open grammar gap
          ScannerSurfCorr sc sp_scan            -- scanner ahead

    At each step:
    1. Preprocessing of token N+1 provides `SSLComments` to close token N's node
    2. Content dispatch of token N+1 opens a new `PendingNode`
    At EOF, the final `PendingNode` is closed with EOF-derived `SSLComments`.

    ## Sorry narrowing

    Five per-dispatch sorry lemmas (§1a–§1e), each architecturally provable
    (unlike the 4c version where they were provably impossible). The composition
    layer (§1f, §2, §3, §5) is fully proven by delegation.
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

/-! ## §0 PendingNode — Lagging Grammar State

    Tracks the grammar gap between `sp_gram` (where `SLYamlStream` ends)
    and `sp_scan` (where `ScannerSurfCorr` is). The gap represents characters
    consumed by the scanner that haven't yet been incorporated into a grammar
    production because the trailing `SSLComments` hasn't arrived yet.

    When the next preprocessing step provides `SSLComments`, the pending node
    is "closed" — incorporated into the grammar — and `SLYamlStream` advances. -/

inductive PendingNode : SurfPos → SurfPos → Prop where
  /-- No pending gap. Grammar and scanner at same position.
      Occurs at stream start, between documents, and after document suffixes
      whose trailing SSLComments has already been absorbed. -/
  | noPending (sp : SurfPos) : PendingNode sp sp
  /-- Content token scanned (scalar, anchor, alias, tag).
      The gap sp_gram → sp_scan contains SSeparate + content.
      Awaiting SSLComments sp_scan sp' to close into SBlockNode. -/
  | pendingContent (sp_gram sp_scan : SurfPos) : PendingNode sp_gram sp_scan
  /-- Document end `...` scanned. The gap contains SCDocumentEnd.
      Awaiting SSLComments to form SLDocumentSuffix. -/
  | pendingDocEnd (sp_gram sp_scan : SurfPos) : PendingNode sp_gram sp_scan
  /-- Document start `---` scanned. The gap contains SCDirectivesEnd.
      Awaiting content or SSLComments to complete the explicit document. -/
  | pendingDocStart (sp_gram sp_scan : SurfPos) : PendingNode sp_gram sp_scan
  /-- Directive `%` scanned. The gap contains directive content.
      Awaiting next directive or `---`. -/
  | pendingDirective (sp_gram sp_scan : SurfPos) : PendingNode sp_gram sp_scan
  /-- Flow indicator scanned (`[`, `]`, `{`, `}`, `,`).
      Multi-token production, deferred to sub-layer 4e. -/
  | pendingFlow (sp_gram sp_scan : SurfPos) : PendingNode sp_gram sp_scan
  /-- Block indicator scanned (`-`, `?`, `:`).
      Multi-token production, deferred to sub-layer 4e. -/
  | pendingBlock (sp_gram sp_scan : SurfPos) : PendingNode sp_gram sp_scan

/-! ## §1 Per-Dispatch Grammar Accumulator Lemmas

    Each dispatcher has a sorry lemma that:
    1. Closes the previous `PendingNode` using `SSLComments` from preprocessing
    2. Opens a new `PendingNode` for the dispatched token
    3. Extends `SLYamlStream` as appropriate

    ### §1a Preprocessing + EOF

    When `scanNextToken_preprocess` returns `none`, the scanner reached EOF.
    Close the pending node with EOF-derived `SSLComments` and finalize. -/

theorem preprocessing_eof_extends_stream (sc : ScannerState)
    (sp_start sp_gram sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_pending : PendingNode sp_gram sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  -- Preprocessing consumed all remaining input (whitespace, comments, breaks).
  -- The pending node is closed with EOF-derived SSLComments:
  --   At col=0: SSLComments.startOfLine with GStar SLComment from remaining chars
  --   At col>0: break → SSBComment → SSLComments.withComment
  -- For noPending: remaining chars form SLDocumentPrefix extending the stream.
  -- For pendingContent: SSLComments closes SBlockNode.flowInBlock.
  -- For pendingDocEnd: SSLComments forms SLDocumentSuffix.
  -- For pendingDocStart: SSLComments forms empty SBlockNode → explicit doc.
  sorry

/-! ### §1b Preprocessing + Structural Dispatch

    `scanNextToken_dispatchStructural` handles `---`, `...`, `%`-directives.
    Preprocessing provides SSLComments to close the previous pending node.
    The structural token opens a new pending state. -/

theorem accum_step_structural (sc : ScannerState)
    (sp_start sp_gram sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_pending : PendingNode sp_gram sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp_gram' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      PendingNode sp_gram' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  -- Close phase: preprocessing → SSLComments closes previous pending node.
  -- Open phase:
  --   `---` → scanDocumentStart_prod → SCDirectivesEnd → pendingDocStart
  --   `...` → scanDocumentEnd_prod → SCDocumentEnd → pendingDocEnd
  --   `%`  → scanDirective_prod → pendingDirective
  sorry

/-! ### §1c Preprocessing + Flow Indicator Dispatch

    `scanNextToken_dispatchFlowIndicators` handles `[`, `]`, `{`, `}`, `,`.
    Multi-token productions — pending state deferred to sub-layer 4e. -/

theorem accum_step_flow (sc : ScannerState)
    (sp_start sp_gram sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_pending : PendingNode sp_gram sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      PendingNode sp_gram' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  -- Flow indicators are part of multi-token flow collections.
  -- Close phase: preprocessing → SSLComments closes previous pending node.
  -- Open phase: pendingFlow (deferred to 4e).
  sorry

/-! ### §1d Preprocessing + Block Indicator Dispatch

    `scanNextToken_dispatchBlockIndicators` handles `-`, `?`, `:`.
    Multi-token productions — pending state deferred to sub-layer 4e. -/

theorem accum_step_block (sc : ScannerState)
    (sp_start sp_gram sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_pending : PendingNode sp_gram sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      PendingNode sp_gram' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  -- Block indicators are part of multi-token block collections.
  -- Close phase: preprocessing → SSLComments closes previous pending node.
  -- Open phase: pendingBlock (deferred to 4e).
  sorry

/-! ### §1e Preprocessing + Content Dispatch

    `scanNextToken_dispatchContent` handles all content tokens:
    `&` anchor, `*` alias, `!` tag, `|`/`>` block scalar, `"` double-quoted,
    `'` single-quoted, plain scalar. Never returns `none`. -/

theorem accum_step_content (sc : ScannerState)
    (sp_start sp_gram sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_pending : PendingNode sp_gram sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp_gram' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      PendingNode sp_gram' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  -- Close phase: preprocessing → SSLComments closes previous pending node.
  -- Open phase: content produces SFlowNode/SCLLiteral/etc. → pendingContent
  --   scanDoubleQuoted_prod ✅, scanSingleQuoted_prod ✅,
  --   scanAnchorOrAlias_*_prod ✅, scanTag_prod ✅,
  --   scanPlainScalar_prod ❌, scanBlockScalar_prod ❌,
  --   flow collection _prod ❌, block collection _prod ❌
  sorry

/-! ### §1f Composition: Per-Dispatch → Full accum_step

    Unfold `scanNextToken`, split on preprocessing and dispatch results,
    and delegate to the per-dispatch sorry lemmas above. -/

theorem scanNextToken_accum_step (sc : ScannerState)
    (sp_start sp_gram sp_scan : SurfPos)
    (s' : ScannerState)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_pending : PendingNode sp_gram sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanNextToken sc = .ok (some s')) :
    ∃ sp_gram' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      PendingNode sp_gram' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
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
          exact accum_step_structural sc sp_start sp_gram sp_scan s_pre s_str c_pre
            h_stream h_pending h_corr h_pre h_str
        · -- Past structural dispatch: allowDirectives update
          split at h_ok
          · simp at h_ok
          · -- scanNextToken_checkBlockFlowIndent — pure check, no state change
            split at h_ok
            · simp at h_ok
            · split at h_ok
              · rename_i s_flow h_flow
                have h := Except.ok.inj h_ok; injection h with h; subst h
                exact accum_step_flow sc sp_start sp_gram sp_scan s_pre s_flow c_pre
                  h_stream h_pending h_corr h_pre h_flow
              · split at h_ok
                · simp at h_ok
                · split at h_ok
                  · rename_i s_blk h_blk
                    have h := Except.ok.inj h_ok; injection h with h; subst h
                    exact accum_step_block sc sp_start sp_gram sp_scan s_pre s_blk c_pre
                      h_stream h_pending h_corr h_pre h_blk
                  · split at h_ok
                    · simp at h_ok
                    · rename_i s_cnt h_cnt
                      have h := Except.ok.inj h_ok; injection h with h; subst h
                      exact accum_step_content sc sp_start sp_gram sp_scan s_pre s_cnt c_pre
                        h_stream h_pending h_corr h_pre h_cnt

/-! ## §2 EOF Step: scanNextToken returns none

    When `scanNextToken` returns `.ok none`, the only code path is through
    `scanNextToken_preprocess` returning `none` (EOF detected).
    The pending node is closed with EOF-derived SSLComments. -/

theorem scanNextToken_none_stream (sc : ScannerState)
    (sp_start sp_gram sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_pending : PendingNode sp_gram sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanNextToken sc = .ok none) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · rename_i h_pre
      exact preprocessing_eof_extends_stream sc sp_start sp_gram sp_scan
        h_stream h_pending h_corr h_pre
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

    Fuel induction threading `SLYamlStream`, `PendingNode`, and
    `ScannerSurfCorr` — the lagging triple. -/

theorem scanLoop_grammar_prod (sc : ScannerState)
    (sp_start sp_gram sp_scan : SurfPos)
    (fuel : Nat) (tokens : Array (Positioned YamlToken))
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_pending : PendingNode sp_gram sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanLoop sc fuel = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  induction fuel generalizing sc sp_gram sp_scan tokens with
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
      -- Scanner reached EOF — close pending node and finalize stream
      exact scanNextToken_none_stream sc sp_start sp_gram sp_scan
        h_stream h_pending h_corr h_none
    · -- scanNextToken = .ok (some s') → one step + recurse
      rename_i s_next h_next
      obtain ⟨sp_gram', sp_scan', h_stream', h_pending', h_corr'⟩ :=
        scanNextToken_accum_step sc sp_start sp_gram sp_scan s_next
          h_stream h_pending h_corr h_next
      exact ih s_next sp_gram' sp_scan' tokens h_stream' h_pending' h_corr' h_ok

/-! ## §4 Initial Stream + BOM Handling

    Establish the initial `SLYamlStream` and `ScannerSurfCorr` for `scan`.
    The initial state has `PendingNode.noPending` — no grammar gap. -/

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
    Initial state uses `PendingNode.noPending` — no grammar gap at start. -/

theorem scan_content_gives_stream_v2
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
                           sp_final.chars = [] := by
  unfold scan at h
  simp only [] at h
  obtain ⟨sp, h_stream, h_corr⟩ := initial_stream_and_prefix input
  exact scanLoop_grammar_prod _ ⟨input.toList, 0⟩ sp sp _ tokens
    h_stream (PendingNode.noPending sp) h_corr h

/-! ## §6 Gap Analysis

    Five sorry lemmas remain, each precisely scoped to one dispatch path.
    Unlike the 4c version, these are **architecturally provable** — the
    lagging invariant correctly models the one-token lag between scanner
    and grammar positions.

    1. `preprocessing_eof_extends_stream` (§1a): Close pending node at EOF
       using EOF-derived `SSLComments`. Requires case-split on `PendingNode`
       constructor (noPending: extend with prefix; pendingContent: close
       SBlockNode; pendingDocEnd: close SLDocumentSuffix; etc.).

    2. `accum_step_structural` (§1b): Close previous pending + open new.
       `---` → pendingDocStart, `...` → pendingDocEnd, `%` → pendingDirective.
       Existing theorems: `scanDocumentStart_prod` ✅, `scanDocumentEnd_prod` ✅,
       `scanDirective_prod` ✅.

    3. `accum_step_flow` (§1c): Close previous pending + pendingFlow.
       Multi-token — discharge deferred to sub-layer 4e.

    4. `accum_step_block` (§1d): Close previous pending + pendingBlock.
       Multi-token — discharge deferred to sub-layer 4e.

    5. `accum_step_content` (§1e): Close previous pending + pendingContent.
       Existing: `scanDoubleQuoted_prod` ✅, `scanSingleQuoted_prod` ✅,
       `scanTag_prod` ✅, `scanAnchorOrAlias_*_prod` ✅.
       Missing: `scanPlainScalar_prod` ❌, `scanBlockScalar_prod` ❌.

    Proven (composition-only, delegating to above sorry):
    - `scanNextToken_accum_step` (§1f): unfolds `scanNextToken`, dispatches
    - `scanNextToken_none_stream` (§2): unfolds `scanNextToken`, EOF path
    - `scanLoop_grammar_prod` (§3): fuel induction with lagging triple
    - `scan_content_gives_stream_v2` (§5): top-level composition

    Total sorry: 5 (same count as 4c, but now architecturally provable).
-/

end Lean4Yaml.Proofs.StreamAccum
