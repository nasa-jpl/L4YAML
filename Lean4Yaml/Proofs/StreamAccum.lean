import Lean4Yaml.Proofs.DocumentProduction
import Lean4Yaml.Proofs.PreprocessProduction

/-! # Stream Grammar Accumulator (Layer 4d + 4e: Lagging Grammar with Block Stack)

    Threads a grammar accumulator through `scanLoop` alongside `ScannerSurfCorr`,
    narrowing the sorry in `scan_content_gives_stream` to per-dispatch lemmas.

    ## Architecture: The Lagging Invariant with Block Stack

    Scanner token boundaries don't align with grammar production boundaries
    (see MISMATCH.md). Grammar productions like `SBlockNode.flowInBlock` require
    prefix (`SSeparate`) + content (`SFlowNode`) + postfix (`SSLComments`), but
    the postfix is consumed during the NEXT token's preprocessing.

    Additionally, block collections (`SBlockSeqEntries`, `SBlockMapEntries`) span
    multiple `scanNextToken` calls. A block sequence `- a\n- b` involves ≥4 tokens.
    The scanner tracks this via an indent stack; the grammar needs a corresponding
    `BlockStack`.

    The fix: a **four-component state** (the "lagging quad"):

        ∀ token step:
          SLYamlStream sp_start sp_gram  ∧      -- grammar up to here
          BlockStack sp_gram sp_block    ∧      -- nested block collections
          PendingNode sp_block sp_scan   ∧      -- immediate pending state
          ScannerSurfCorr sc sp_scan            -- scanner ahead

    At each step:
    1. Preprocessing of token N+1 provides `SSLComments` to close token N
    2. `unwindIndents` may pop `BlockStack` levels (forming `SBlockNode`)
    3. `pushSequenceIndent`/`pushMappingIndent` may push `BlockStack` levels
    4. Content dispatch of token N+1 opens a new `PendingNode`
    At EOF, the final `BlockStack` is fully unwound and `PendingNode` closed.

    ## Sorry narrowing

    Five per-dispatch sorry lemmas (§1a–§1e), each architecturally provable.
    The composition layer (§1f, §2, §3, §5) is fully proven by delegation.
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

/-! ## §0a PendingNode — Immediate Pending State

    Tracks the gap between the `BlockStack` top (`sp_block`) and the scanner
    position (`sp_scan`). This gap contains the most recent token's characters
    that haven't yet been incorporated into either a block collection entry
    or a standalone grammar production.

    When the next preprocessing step provides `SSLComments`, the pending node
    is "closed" — incorporated into the grammar — and the state advances. -/

inductive PendingNode : SurfPos → SurfPos → Prop where
  /-- No pending gap. Block stack top and scanner at same position.
      Occurs at stream start, between documents, after document suffixes
      whose trailing SSLComments has already been absorbed, and at the
      start of a new block collection level (before any entry content). -/
  | noPending (sp : SurfPos) : PendingNode sp sp
  /-- Content token scanned (scalar, anchor, alias, tag).
      The gap sp_block → sp_scan contains SSeparate + content.
      Awaiting SSLComments sp_scan sp' to close into SBlockNode. -/
  | pendingContent (sp_block sp_scan : SurfPos) : PendingNode sp_block sp_scan
  /-- Document end `...` scanned. The gap contains SCDocumentEnd.
      Awaiting SSLComments to form SLDocumentSuffix. -/
  | pendingDocEnd (sp_block sp_scan : SurfPos) : PendingNode sp_block sp_scan
  /-- Document start `---` scanned. The gap contains SCDirectivesEnd.
      Awaiting content or SSLComments to complete the explicit document. -/
  | pendingDocStart (sp_block sp_scan : SurfPos) : PendingNode sp_block sp_scan
  /-- Directive `%` scanned. The gap contains directive content.
      Awaiting next directive or `---`. -/
  | pendingDirective (sp_block sp_scan : SurfPos) : PendingNode sp_block sp_scan
  /-- Flow indicator scanned (`[`, `]`, `{`, `}`, `,`).
      Multi-token flow collection production (future work). -/
  | pendingFlow (sp_block sp_scan : SurfPos) : PendingNode sp_block sp_scan
  /-- Block indicator scanned (`-`, `?`, `:`).
      The gap sp_block → sp_scan contains the indicator character.
      The block nesting is tracked separately by `BlockStack`. -/
  | pendingBlock (sp_block sp_scan : SurfPos) : PendingNode sp_block sp_scan

/-! ## §0b BlockStack — Nested Block Collection Accumulator

    Tracks partially-accumulated block collections being built across
    multiple `scanNextToken` calls. Mirrors the scanner's indent stack
    (minus the sentinel entry at column -1).

    Each level records:
    - `col`: The column where this block collection starts (matching
      scanner's `IndentEntry.column`)
    - Whether it's a sequence or mapping (matching `IndentEntry.isSequence`)
    - Position boundaries for this nesting level's character coverage

    The actual grammar types are:
    - `SBlockSeqEntries n` (`single | cons`): entries for block sequences
    - `SBlockMapEntries n` (`single | cons`): entries for block mappings
    - `SBlockNode.blockSeq`: wraps `SBlockSeqEntries` with `GOpt props + SSLComments`
    - `SBlockNode.blockMap`: wraps `SBlockMapEntries` with `GOpt props + SSLComments`

    **Protocol (mirrors scanner's indent stack operations):**

    - **Push** (`pushSequenceIndent`/`pushMappingIndent`): When `col > currentIndent`,
      a new indent entry is pushed and `.blockSequenceStart`/`.blockMappingStart`
      is emitted. `BlockStack` gets a corresponding `.seqLevel`/`.mapLevel`.

    - **Pop** (`unwindIndents` in preprocessing): When content moves to a lower
      column, indent entries are popped and `.blockEnd` tokens emitted. Each pop
      finalizes the block collection into `SBlockNode.blockSeq`/`.blockMap`,
      potentially extending `SLYamlStream`.

    - **Same-level entry** (e.g., second `-` at same indent): The current level's
      accumulated entries grow by one (`SBlockSeqEntries.cons` / `SBlockMapEntries.cons`).
      No push/pop occurs.

    Evidence-free: positions and columns only. Grammar witnesses
    (`SBlockSeqEntries`, `SBlockMapEntries`) are constructed when sorry
    lemmas are discharged. -/

inductive BlockStack : SurfPos → SurfPos → Prop where
  /-- No active block collections. At document level or stream start. -/
  | nil (sp : SurfPos) : BlockStack sp sp
  /-- Block sequence being accumulated at column `col`.
      Outer stack covers sp → sp_mid. This level's character coverage
      is sp_mid → sp'. Entries will form `SBlockSeqEntries (seqSpaces n c)`
      where `n` is determined by `col`. -/
  | seqLevel (col : Int) (sp sp_mid sp' : SurfPos) :
      BlockStack sp sp_mid → BlockStack sp sp'
  /-- Block mapping being accumulated at column `col`.
      Entries will form `SBlockMapEntries n`. -/
  | mapLevel (col : Int) (sp sp_mid sp' : SurfPos) :
      BlockStack sp sp_mid → BlockStack sp sp'

/-! ## §1 Per-Dispatch Grammar Accumulator Lemmas

    Each dispatcher has a sorry lemma that:
    1. Closes the previous `PendingNode` using `SSLComments` from preprocessing
    2. May pop `BlockStack` levels if `unwindIndents` fired (dedent)
    3. May push `BlockStack` levels if `pushSequenceIndent`/`pushMappingIndent` fired
    4. Opens a new `PendingNode` for the dispatched token
    5. Extends `SLYamlStream` as needed (dedent closures, document boundaries)

    ### §1a Preprocessing + EOF

    When `scanNextToken_preprocess` returns `none`, the scanner reached EOF.
    Close all pending state — unwind entire BlockStack, close PendingNode,
    and finalize the stream. -/

theorem preprocessing_eof_extends_stream (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  -- At EOF, preprocessing consumed all remaining input.
  -- 1. SSLComments from remaining whitespace/comments/breaks closes PendingNode.
  -- 2. unwindIndents pops ALL indent levels → BlockStack fully unwound.
  --    Each pop: accumulated entries → SBlockSeqEntries/SBlockMapEntries
  --    → SBlockNode.blockSeq/.blockMap → extends SLYamlStream.
  -- 3. For noPending + nil: remaining chars form SLDocumentPrefix.
  -- 4. Stream finalized with empty GOpt/GStar suffix sections.
  sorry

/-! ### §1b Preprocessing + Structural Dispatch

    `scanNextToken_dispatchStructural` handles `---`, `...`, `%`-directives.
    Preprocessing provides SSLComments to close the previous pending node.
    If indent levels decreased, BlockStack pops accordingly.
    The structural token opens a new pending state. -/

theorem accum_step_structural (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      PendingNode sp_block' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  -- Close phase: preprocessing → SSLComments closes previous PendingNode.
  --   If unwindIndents fired → BlockStack pops, forming SBlockNode entries.
  -- Open phase:
  --   `---` → scanDocumentStart_prod → SCDirectivesEnd → pendingDocStart
  --   `...` → scanDocumentEnd_prod → SCDocumentEnd → pendingDocEnd
  --   `%`  → scanDirective_prod → pendingDirective
  --   Structural tokens at col 0 cause full dedent → BlockStack becomes nil.
  sorry

/-! ### §1c Preprocessing + Flow Indicator Dispatch

    `scanNextToken_dispatchFlowIndicators` handles `[`, `]`, `{`, `}`, `,`.
    Multi-token flow collection productions (future work). -/

theorem accum_step_flow (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      PendingNode sp_block' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  -- Flow indicators are part of multi-token flow collections.
  -- Close phase: preprocessing → SSLComments closes previous PendingNode.
  --   If unwindIndents fired → BlockStack pops.
  -- Open phase: pendingFlow (flow accumulation is future work).
  sorry

/-! ### §1d Preprocessing + Block Indicator Dispatch

    `scanNextToken_dispatchBlockIndicators` handles `-`, `?`, `:`.
    This is the core of block collection accumulation:

    1. Preprocessing may unwind indent levels → BlockStack pops
    2. `pushSequenceIndent`/`pushMappingIndent` may push → BlockStack pushes
    3. The indicator character is consumed → pendingBlock

    **Scanner → BlockStack correspondence:**
    - `scanBlockEntry` calls `pushSequenceIndent s s.col`:
      If `col > currentIndent` → `.seqLevel col` pushed onto BlockStack
    - `scanKey` calls `pushMappingIndent s s.col`:
      If `col > currentIndent` → `.mapLevel col` pushed onto BlockStack
    - `scanValue` calls `scanValuePrepare` which may retroactively emit
      `.blockMappingStart` → `.mapLevel` pushed if needed -/

theorem accum_step_block (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      PendingNode sp_block' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  -- Close phase:
  --   1. SSLComments from preprocessing closes previous PendingNode
  --   2. If unwindIndents popped indent levels, BlockStack pops correspondingly.
  --      Each pop: accumulated entries form SBlockSeqEntries/SBlockMapEntries
  --      → SBlockNode.blockSeq/.blockMap → may extend SLYamlStream
  -- Open phase:
  --   3. If pushSequenceIndent/pushMappingIndent pushed (col > currentIndent):
  --      BlockStack gets new .seqLevel/.mapLevel
  --   4. The `-`/`?`/`:` indicator + advance → pendingBlock
  sorry

/-! ### §1e Preprocessing + Content Dispatch

    `scanNextToken_dispatchContent` handles all content tokens:
    `&` anchor, `*` alias, `!` tag, `|`/`>` block scalar, `"` double-quoted,
    `'` single-quoted, plain scalar. Never returns `none`.

    When inside an active BlockStack, the content token contributes to the
    current block entry's `SBlockIndented` component. The BlockStack itself
    doesn't change — only PendingNode transitions to pendingContent. -/

theorem accum_step_content (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp_gram' sp_block' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      PendingNode sp_block' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  -- Close phase: preprocessing → SSLComments closes previous PendingNode.
  --   If unwindIndents fired → BlockStack pops.
  -- Open phase: content produces the token's grammar witness → pendingContent.
  --   BlockStack may be unchanged (content inside current entry) or
  --   newly nil (content at document level after all blocks closed).
  --   Existing _prod theorems:
  --     scanDoubleQuoted_prod ✅, scanSingleQuoted_prod ✅,
  --     scanTag_prod ✅, scanAnchorOrAlias_*_prod ✅.
  --   Missing: scanPlainScalar_prod ❌, scanBlockScalar_prod ❌.
  sorry

/-! ### §1f Composition: Per-Dispatch → Full accum_step

    Unfold `scanNextToken`, split on preprocessing and dispatch results,
    and delegate to the per-dispatch sorry lemmas above. -/

theorem scanNextToken_accum_step (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan : SurfPos)
    (s' : ScannerState)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanNextToken sc = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      PendingNode sp_block' sp_scan' ∧
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
          exact accum_step_structural sc sp_start sp_gram sp_block sp_scan s_pre s_str c_pre
            h_stream h_stack h_pending h_corr h_pre h_str
        · -- Past structural dispatch: allowDirectives update
          split at h_ok
          · simp at h_ok
          · -- scanNextToken_checkBlockFlowIndent — pure check, no state change
            split at h_ok
            · simp at h_ok
            · split at h_ok
              · rename_i s_flow h_flow
                have h := Except.ok.inj h_ok; injection h with h; subst h
                exact accum_step_flow sc sp_start sp_gram sp_block sp_scan s_pre s_flow c_pre
                  h_stream h_stack h_pending h_corr h_pre h_flow
              · split at h_ok
                · simp at h_ok
                · split at h_ok
                  · rename_i s_blk h_blk
                    have h := Except.ok.inj h_ok; injection h with h; subst h
                    exact accum_step_block sc sp_start sp_gram sp_block sp_scan s_pre s_blk c_pre
                      h_stream h_stack h_pending h_corr h_pre h_blk
                  · split at h_ok
                    · simp at h_ok
                    · rename_i s_cnt h_cnt
                      have h := Except.ok.inj h_ok; injection h with h; subst h
                      exact accum_step_content sc sp_start sp_gram sp_block sp_scan s_pre s_cnt c_pre
                        h_stream h_stack h_pending h_corr h_pre h_cnt

/-! ## §2 EOF Step: scanNextToken returns none

    When `scanNextToken` returns `.ok none`, the only code path is through
    `scanNextToken_preprocess` returning `none` (EOF detected).
    All BlockStack levels are unwound and PendingNode closed. -/

theorem scanNextToken_none_stream (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanNextToken sc = .ok none) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · rename_i h_pre
      exact preprocessing_eof_extends_stream sc sp_start sp_gram sp_block sp_scan
        h_stream h_stack h_pending h_corr h_pre
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

    Fuel induction threading the lagging quad:
    `SLYamlStream`, `BlockStack`, `PendingNode`, and `ScannerSurfCorr`. -/

theorem scanLoop_grammar_prod (sc : ScannerState)
    (sp_start sp_gram sp_block sp_scan : SurfPos)
    (fuel : Nat) (tokens : Array (Positioned YamlToken))
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_pending : PendingNode sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanLoop sc fuel = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  induction fuel generalizing sc sp_gram sp_block sp_scan tokens with
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
      -- Scanner reached EOF — unwind BlockStack, close PendingNode, finalize stream
      exact scanNextToken_none_stream sc sp_start sp_gram sp_block sp_scan
        h_stream h_stack h_pending h_corr h_none
    · -- scanNextToken = .ok (some s') → one step + recurse
      rename_i s_next h_next
      obtain ⟨sp_gram', sp_block', sp_scan', h_stream', h_stack', h_pending', h_corr'⟩ :=
        scanNextToken_accum_step sc sp_start sp_gram sp_block sp_scan s_next
          h_stream h_stack h_pending h_corr h_next
      exact ih s_next sp_gram' sp_block' sp_scan' tokens
        h_stream' h_stack' h_pending' h_corr' h_ok

/-! ## §4 Initial Stream + BOM Handling

    Establish the initial `SLYamlStream` and `ScannerSurfCorr` for `scan`.
    The initial state has `BlockStack.nil` and `PendingNode.noPending` —
    no grammar gap, no active block collections. -/

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
    Initial state uses `BlockStack.nil` and `PendingNode.noPending` — no gap. -/

theorem scan_content_gives_stream_v2
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream ⟨input.toList, 0⟩ sp_final ∧
                           sp_final.chars = [] := by
  unfold scan at h
  simp only [] at h
  obtain ⟨sp, h_stream, h_corr⟩ := initial_stream_and_prefix input
  exact scanLoop_grammar_prod _ ⟨input.toList, 0⟩ sp sp sp _ tokens
    h_stream (BlockStack.nil sp) (PendingNode.noPending sp) h_corr h

/-! ## §6 Gap Analysis

    Five sorry lemmas remain, each precisely scoped to one dispatch path.
    All are architecturally provable — the lagging quad (SLYamlStream +
    BlockStack + PendingNode + ScannerSurfCorr) correctly models the
    multi-token protocol for block collections.

    The BlockStack component (sub-layer 4e) addresses the hardest remaining
    gap: block sequences and mappings spanning multiple `scanNextToken` calls.

    **Discharge strategy per sorry:**

    1. `preprocessing_eof_extends_stream` (§1a): Case-split on BlockStack depth.
       - nil: remaining chars → SLDocumentPrefix → extend stream.
       - seqLevel/mapLevel: each level forms SBlockSeqEntries/SBlockMapEntries
         → SBlockNode.blockSeq/.blockMap → extend stream. Recurse on stack.
       Then case-split on PendingNode to close the innermost gap.

    2. `accum_step_structural` (§1b): Close previous pending + BlockStack.
       Structural tokens (`---`/`...`/`%`) only appear at col 0, causing
       full dedent. So BlockStack becomes nil after preprocessing.
       Existing `scanDocumentStart_prod` ✅, `scanDocumentEnd_prod` ✅,
       `scanDirective_prod` ✅.

    3. `accum_step_flow` (§1c): Close previous pending + BlockStack pops
       if needed. Flow indicator → pendingFlow (flow accumulation future work).

    4. `accum_step_block` (§1d): The core of 4e.
       - Close: SSLComments + BlockStack pops for dedent.
       - Push: If `pushSequenceIndent`/`pushMappingIndent` fires,
         new `.seqLevel`/`.mapLevel` pushed.
       - Each `-` at same level: extends the current seqLevel's entries.
       - The `-`/`?`/`:` chars → pendingBlock.

    5. `accum_step_content` (§1e): Close previous pending.
       BlockStack may shrink (dedent during preprocessing) but not grow.
       Content token → pendingContent. BlockStack threaded through.
       Missing _prod theorems: `scanPlainScalar_prod` ❌, `scanBlockScalar_prod` ❌.

    **Proven (composition-only, delegating to above sorry):**
    - `scanNextToken_accum_step` (§1f): unfolds `scanNextToken`, dispatches
    - `scanNextToken_none_stream` (§2): unfolds `scanNextToken`, EOF path
    - `scanLoop_grammar_prod` (§3): fuel induction with lagging quad
    - `scan_content_gives_stream_v2` (§5): top-level composition

    Total sorry: 5 (architecturally provable with BlockStack).
-/

end Lean4Yaml.Proofs.StreamAccum
