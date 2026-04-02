import Lean4Yaml.Proofs.PreprocessProduction
import Lean4Yaml.Proofs.ScanStrictCoupling
import Lean4Yaml.Proofs.StructureProduction

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
          PendingNode sp_start sp_block sp_scan   ∧      -- immediate pending state
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
open Lean4Yaml.Proofs.StructureCoupling
open Lean4Yaml.Proofs.PreprocessProduction
open Lean4Yaml.Proofs.StructureProduction
open Lean4Yaml.Proofs.ScalarProduction
open Lean4Yaml.Proofs.NodeProduction

/-! ## §0a PendingNode — Immediate Pending State

    Tracks the gap between the `BlockStack` top (`sp_block`) and the scanner
    position (`sp_scan`). This gap contains the most recent token's characters
    that haven't yet been incorporated into either a block collection entry
    or a standalone grammar production.

    When the next preprocessing step provides `SSLComments`, the pending node
    is "closed" — incorporated into the grammar — and the state advances.

    **Evidence-bearing design (v0.4.7):** Structural pending variants carry
    grammar markers directly (`SCDirectivesEnd` for `---`, `SCDocumentEnd` for `...`).
    These are constructed at dispatch time using `_prod` theorems and consumed
    when preprocessing provides SSLComments — the marker plus SSLComments compose
    directly into `SLExplicitDocument` or `SLDocumentSuffix` without any closure.
    Other pending variants retain `h_closable` closures for now. -/

inductive PendingNode : SurfPos → SurfPos → SurfPos → Prop where
  /-- No pending gap. Block stack top and scanner at same position.
      Occurs at stream start, between documents, after document suffixes
      whose trailing SSLComments has already been absorbed, and at the
      start of a new block collection level (before any entry content). -/
  | noPending (sp_start sp : SurfPos) : PendingNode sp_start sp sp
  /-- Content token scanned (scalar, anchor, alias, tag).
      The gap sp_block → sp_scan contains SSeparate + content.
      Awaiting SSLComments sp_scan sp' to close into SBlockNode.
      `h_closable` constructs the stream extension using grammar evidence
      and the stream captured at dispatch time. The `SLYamlStream sp_start`
      is captured inside the closure, not passed at consumption time. -/
  | pendingContent (sp_start sp_block sp_scan : SurfPos)
      (h_closable : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        SLYamlStream sp_start sp_mid) :
      PendingNode sp_start sp_block sp_scan
  /-- Document end `...` scanned. The gap contains SCDocumentEnd.
      Awaiting SSLComments to form SLDocumentSuffix.
      Carries the marker directly for compositional consumption. -/
  | pendingDocEnd (sp_start sp_block sp_scan : SurfPos)
      (h_marker : SCDocumentEnd sp_block sp_scan) :
      PendingNode sp_start sp_block sp_scan
  /-- Document start `---` scanned. The gap contains SCDirectivesEnd
      (possibly preceded by directives). Awaiting content or SSLComments
      to complete the document.
      `h_doc_builder` abstracts whether this is an explicit document
      (standalone `---`) or a directive document (`%YAML` ... `---`).
      Given content evidence after `---`, it produces `SLAnyDocument`. -/
  | pendingDocStart (sp_start sp_block sp_scan : SurfPos)
      (h_doc_builder : ∀ sp_end,
        GAlt SLBareDocument (GSeq SENode SSLComments) sp_scan sp_end →
        SLAnyDocument sp_block sp_end) :
      PendingNode sp_start sp_block sp_scan
  /-- Directive `%` scanned. The gap contains directive content.
      Awaiting next `%` (accumulate) or `---` (form directive document).
      Carries an accumulator that, given SSLComments, produces
      `GPlus SLDirective` covering all directives so far.
      Also captures the stream at the point before the first directive. -/
  | pendingDirective (sp_start sp_block sp_scan : SurfPos)
      (h_dir_acc : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        GPlus SLDirective sp_block sp_mid)
      (h_stream : SLYamlStream sp_start sp_block) :
      PendingNode sp_start sp_block sp_scan
  /-- Flow indicator scanned (`[`, `]`, `{`, `}`, `,`).
      Multi-token flow collection production (future work). -/
  | pendingFlow (sp_start sp_block sp_scan : SurfPos)
      (h_closable : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        SLYamlStream sp_start sp_mid) :
      PendingNode sp_start sp_block sp_scan
  /-- Content token scanned INSIDE a block entry (e.g., `- "hello"`).
      Like `pendingContent`, but additionally carries entry-level evidence
      via `h_closable_entry`. When this content is closed and a new `-`
      follows at the same level, `h_closable_entry` returns accumulated
      `SBlockSeqEntries` + continuation for further snocing. -/
  | pendingBlockContent (sp_start sp_block sp_scan : SurfPos)
      (h_closable : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        SLYamlStream sp_start sp_mid)
      (h_closable_entry : ∀ sp_mid,
        SSLComments sp_scan sp_mid →
        ∃ sp_first,
          SBlockSeqEntries 0 sp_first sp_mid ∧
          (∀ sp_end, SBlockSeqEntries 0 sp_first sp_end → SLYamlStream sp_start sp_end)) :
      PendingNode sp_start sp_block sp_scan
  /-- Block indicator scanned (`-`, `?`, `:`).
      The gap sp_block → sp_scan contains the indicator character.
      The block nesting is tracked separately by `BlockStack`.
      `h_close` takes the entry CONTENT as `SBlockNode` and produces the
      stream. For empty entries (no content follows), the caller provides
      `SBlockNode.emptyNode ... h_ssl`; for content entries, the caller
      provides `SBlockNode.flowInBlock ...` etc. The closure captures
      entry opener evidence (indent, dash/key/value, preprocessing) and
      the stream at the dispatch point.
      `h_close_entry` is the **entry-level** variant: instead of producing
      the full stream, it returns the accumulated `SBlockSeqEntries` and a
      continuation that can produce the stream from any extended entries.
      This enables same-level `-` to snoc new entries via
      `SBlockSeqEntries_snoc` without closing the sequence. -/
  | pendingBlock (sp_start sp_block sp_scan : SurfPos)
      (h_close : ∀ sp_mid,
        SBlockNode 0 .blockIn sp_scan sp_mid →
        SLYamlStream sp_start sp_mid)
      (h_close_entry : ∀ sp_mid,
        SBlockNode 0 .blockIn sp_scan sp_mid →
        ∃ sp_first,
          SBlockSeqEntries 0 sp_first sp_mid ∧
          (∀ sp_end, SBlockSeqEntries 0 sp_first sp_end → SLYamlStream sp_start sp_end)) :
      PendingNode sp_start sp_block sp_scan

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

    Each `seqLevel`/`mapLevel` carries a compositional closure
    `h_closable` that can extend the stream from the stack's outer
    boundary (`sp`) through all accumulated block content to the
    level's top (`sp'`). This avoids requiring explicit grammar
    witnesses (`SBlockSeqEntries`, `SBlockMapEntries`) at this stage —
    those are constructed inside the closure when the closure is
    provided (future work). -/

inductive BlockStack : SurfPos → SurfPos → Prop where
  /-- No active block collections. At document level or stream start. -/
  | nil (sp : SurfPos) : BlockStack sp sp
  /-- Block sequence being accumulated at column `col`.
      Outer stack covers sp → sp_mid. This level's character coverage
      is sp_mid → sp'. Entries will form `SBlockSeqEntries (seqSpaces n c)`
      where `n` is determined by `col`.
      `h_closable`: given any stream ending at `sp`, extends it to `sp'`
      by incorporating the inner stack + this level's accumulated entries. -/
  | seqLevel (col : Int) (sp sp_mid sp' : SurfPos) :
      BlockStack sp sp_mid →
      (∀ (sp_start : SurfPos), SLYamlStream sp_start sp → SLYamlStream sp_start sp') →
      BlockStack sp sp'
  /-- Block mapping being accumulated at column `col`.
      Entries will form `SBlockMapEntries n`.
      `h_closable`: given any stream ending at `sp`, extends it to `sp'`
      by incorporating the inner stack + this level's accumulated entries. -/
  | mapLevel (col : Int) (sp sp_mid sp' : SurfPos) :
      BlockStack sp sp_mid →
      (∀ (sp_start : SurfPos), SLYamlStream sp_start sp → SLYamlStream sp_start sp') →
      BlockStack sp sp'

/-! ## §0b' FlowStack — Nested Flow Collection Accumulator

    Tracks partially-accumulated flow collections (`[...]`, `{...}`) being
    built across multiple `scanNextToken` calls. Mirrors the scanner's
    `flowLevel` counter. Each `[`/`{` pushes a level; each `]`/`}` pops one.

    FlowStack sits between BlockStack and PendingNode in the position chain:
    `SLYamlStream → BlockStack → FlowStack → PendingNode → ScannerSurfCorr`

    Like BlockStack, each level carries a compositional closure
    `h_closable` that extends the stream. Flow collection grammar witnesses
    (`SFlowSequence`, `SFlowMapping`) are constructed inside the closure
    when provided (future work — Layer 4h). -/

inductive FlowStack : SurfPos → SurfPos → Prop where
  /-- No active flow collections. At block level or stream start. -/
  | nil (sp : SurfPos) : FlowStack sp sp
  /-- Flow sequence `[...]` being accumulated.
      Outer stack covers sp → sp_mid. This level covers sp_mid → sp'.
      Entries will form `SFlowSequence n c`.
      `h_closable`: given any stream ending at `sp`, extends it to `sp'`
      by incorporating the outer stack + this level's accumulated entries. -/
  | flowSeqLevel (sp sp_mid sp' : SurfPos) :
      FlowStack sp sp_mid →
      (∀ (sp_start : SurfPos), SLYamlStream sp_start sp → SLYamlStream sp_start sp') →
      FlowStack sp sp'
  /-- Flow mapping `{...}` being accumulated.
      Entries will form `SFlowMapping n c`.
      `h_closable`: given any stream ending at `sp`, extends it to `sp'`
      by incorporating the outer stack + this level's accumulated entries. -/
  | flowMapLevel (sp sp_mid sp' : SurfPos) :
      FlowStack sp sp_mid →
      (∀ (sp_start : SurfPos), SLYamlStream sp_start sp → SLYamlStream sp_start sp') →
      FlowStack sp sp'

/-- Absorb both BlockStack and FlowStack into the stream via h_closable.
    Used by all main theorems to reduce the 3×3 case split to a single call. -/
theorem absorb_stacks (sp_start sp_gram sp_block sp_flow : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow) : SLYamlStream sp_start sp_flow := by
  cases h_stack with
  | nil =>
    cases h_flow with
    | nil => exact h_stream
    | flowSeqLevel _ _ _ h_cl => exact h_cl sp_start h_stream
    | flowMapLevel _ _ _ h_cl => exact h_cl sp_start h_stream
  | seqLevel _ _ _ _ _ h_cl_b =>
    cases h_flow with
    | nil => exact h_cl_b sp_start h_stream
    | flowSeqLevel _ _ _ h_cl => exact h_cl sp_start (h_cl_b sp_start h_stream)
    | flowMapLevel _ _ _ h_cl => exact h_cl sp_start (h_cl_b sp_start h_stream)
  | mapLevel _ _ _ _ _ h_cl_b =>
    cases h_flow with
    | nil => exact h_cl_b sp_start h_stream
    | flowSeqLevel _ _ _ h_cl => exact h_cl sp_start (h_cl_b sp_start h_stream)
    | flowMapLevel _ _ _ h_cl => exact h_cl sp_start (h_cl_b sp_start h_stream)

/-! ## §0c Helpers for §1a (EOF Stream Extension)

    Two helpers needed to discharge the `nil + noPending + col=0` case of §1a:
    1. `preprocess_none_ssl_comments_col0`: unfolds `scanNextToken_preprocess`,
       shows only `!hasMore` path fires, delegates to `skipToContent_eof_ssl_comments_col0`
    2. `ssl_comments_extend_stream_col0`: converts `SSLComments` → `GStar SLComment`
       → `SLDocumentPrefix` → extends `SLYamlStream` via `implicitContinue`

    Together these prove: at col=0, preprocessing EOF extends the stream. -/

/-- When `scanNextToken_preprocess` returns `none` (EOF) and the scanner
    is at col=0, the remaining characters form `SSLComments`. -/
theorem preprocess_none_ssl_comments_col0 (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SSLComments sp sp_final ∧ sp_final.chars = [] := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    split at hok
    · -- !s_content.hasMore → EOF on skipToContent (the only reachable path)
      rename_i h_notMore
      have heof : ¬s_content.hasMore := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_notMore
        exact fun h => by simp [h] at h_notMore
      exact skipToContent_eof_ssl_comments_col0 sc sp s_content hcorr hcol
        (show skipToContent sc = .ok s_content by unfold skipToContent; exact h_skip) heof
    · -- s_content.hasMore: all branches return (some ...) or error, not none.
      -- Proof: unwindIndents/saveSimpleKey preserve offset/input, so peek? is
      -- still some (since hasMore). The peek?=none branches are absurd.
      rename_i h_hasMore
      split at hok
      · split at hok
        · simp at hok
        · split at hok
          · rename_i h_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none; dsimp only [] at h_peek_none
            unfold unwindIndents at h_peek_none
            simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd,
              unwindIndentsLoop_input] at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_hasMore
              simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok
      · split at hok
        · simp at hok
        · split at hok
          · rename_i h_no_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_hasMore
              simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok

-- General version: no col=0 requirement.
theorem preprocess_none_ssl_comments (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SSLComments sp sp_final ∧ sp_final.chars = [] := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    split at hok
    · rename_i h_notMore
      have heof : ¬s_content.hasMore := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_notMore
        exact fun h => by simp [h] at h_notMore
      exact skipToContent_eof_ssl_comments sc sp s_content hcorr
        (show skipToContent sc = .ok s_content by unfold skipToContent; exact h_skip) heof
    · rename_i h_hasMore
      split at hok
      · split at hok
        · simp at hok
        · split at hok
          · rename_i h_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none; dsimp only [] at h_peek_none
            unfold unwindIndents at h_peek_none
            simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd,
              unwindIndentsLoop_input] at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_hasMore
              simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok
      · split at hok
        · simp at hok
        · split at hok
          · rename_i h_no_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h_hasMore
              simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok

/-- Extend `SLYamlStream` with `SSLComments` at col=0.

    `SSLComments` → `GStar SLComment` → `SLDocumentPrefix.comments`
    → `SLYamlStream.implicitContinue` with no explicit document. -/
theorem ssl_comments_extend_stream_col0
    (sp_start sp sp_final : SurfPos)
    (hcol : sp.col = 0)
    (h_stream : SLYamlStream sp_start sp)
    (h_ssl : SSLComments sp sp_final) :
    SLYamlStream sp_start sp_final := by
  have h_gstar := SSLComments_to_GStar_col0 sp sp_final hcol h_ssl
  exact SLYamlStream.implicitContinue sp_start sp sp_final sp_final sp_final
    h_stream
    (GStar.cons sp sp_final sp_final (SLDocumentPrefix.comments sp sp_final h_gstar) (GStar.nil _))
    (GOpt.none _)
    (GStar.nil _)

/-! ## §0d Preprocessing → SSLComments for `some` result at col=0

    When `scanNextToken_preprocess` returns `some (s_prep, c)` and the
    scanner starts at col=0, the characters consumed by `skipToContent`
    form `SSLComments`. This is the key building block for closing pending
    nodes: the SSLComments is provided to `h_closable` of the previous
    `PendingNode` to extend the stream.

    The `sp_mid` returned is the SSLComments boundary (where comment lines
    end), and `sp_prep` is the scanner's final position (which may be past
    `sp_mid` due to trailing whitespace from the last `skipToContent` iteration). -/

/-- When preprocessing returns `some` at col=0, extract `SSLComments` from the
    consumed characters plus `ScannerSurfCorr` for the resulting state. -/
theorem preprocess_some_ssl_comments_col0 (sc : ScannerState) (sp : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_mid sp_ws sp_prep, SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
                      GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp_prep ∧
                      ScannerSurfCorr s_prep sp_prep := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, hcorr_sc⟩ :=
      skipToContent_startOfLine_comments_prod sc sp s_content hcorr hcol h_skip
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            have hcorr2 := unwindIndents_corr_exact s_content sp_sc hcorr_sc (↑s_content.col)
            have hcorr3 : ScannerSurfCorr
                { (unwindIndents s_content ↑s_content.col) with
                  needIndentCheck := false } sp_sc :=
              ⟨hcorr2.chars_from, hcorr2.col_eq, hcorr2.end_eq, hcorr2.input_prefix, hcorr2.indent_cols_nonneg⟩
            exact ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, saveSimpleKey_corr _ sp_sc hcorr3⟩
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            exact ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, saveSimpleKey_corr _ sp_sc hcorr_sc⟩

/-- Preprocessing at col=0 with content character produces `SSeparateLines 0`.

    This wraps `preprocess_some_ssl_comments_col0` by converting
    `SSLComments + GStar SSWhite` into `SSeparateLines.commented 0`
    using `SFlowLinePrefix 0` (zero-indent + optional whitespace).

    **GOpt.some case**: When `preprocess_some_ssl_comments_col0` returns
    `GOpt.some (SCNbCommentText)`, the scanner consumed a `#` comment in the
    final `skipToContentLoop` iteration. This case is unreachable when
    `scanNextToken_preprocess` returns `some (s_prep, c)` because:
    - After `collectCommentTextLoop`, `peek?` returns break or EOF
      (by `collectCommentTextLoop_stops_at_break_or_eof`)
    - But `scanNextToken_preprocess` returned content, meaning `peek?` found
      a non-break character (the loop's stopping condition)
    - These are contradictory

    The contradiction requires connecting the scanner's `peek?` through
    `skipToContentComment` → `unwindIndents` → `saveSimpleKey` state
    preservation chain. Currently deferred as a non-structural sorry. -/
theorem preprocess_some_separate_lines_0 (sc : ScannerState) (sp : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_prep, SSeparateLines 0 sp sp_prep ∧ ScannerSurfCorr s_prep sp_prep := by
  obtain ⟨sp_mid, sp_ws, sp_prep, h_ssl, hcol_mid, h_ws, h_cmt, hcorr_out⟩ :=
    preprocess_some_ssl_comments_col0 sc sp s_prep c hcorr hcol hok
  cases h_cmt with
  | none =>
    -- GOpt.none: sp_ws = sp_prep. Build SSeparateLines.commented 0.
    exact ⟨sp_ws,
      SSeparateLines.commented 0 sp sp_mid sp_ws h_ssl
        (SFlowLinePrefix.mk 0 sp_mid sp_mid sp_ws (SIndent.zero sp_mid)
          (ScalarProduction.gstar_sswhite_to_gopt_sep h_ws)),
      hcorr_out⟩
  | some h_comment_text =>
    -- GOpt.some: unreachable (scanner's comment loop is greedy, stops at break/EOF,
    -- but scanNextToken_preprocess returned a non-break content character).
    -- Deferred: requires peek? preservation through skipToContentComment struct update.
    exact ⟨sp_prep, sorry, hcorr_out⟩

/-- General-column version of `preprocess_some_ssl_comments_col0`.
    When preprocessing returns `some`, extract `SSLComments` disjunction plus
    `GStar SSWhite` and `ScannerSurfCorr`. No col=0 requirement. -/
theorem preprocess_some_ssl_comments_anyCol (sc : ScannerState) (sp : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_mid sp_ws sp_prep,
      (SSLComments sp sp_mid ∧ sp_mid.col = 0 ∨ sp_mid = sp) ∧
      GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp_prep ∧
      ScannerSurfCorr s_prep sp_prep := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    obtain ⟨sp_mid, sp_ws, sp_sc, h_disj, hws, hcmt, hcorr_sc⟩ :=
      skipToContent_anyCol_prod sc sp s_content hcorr h_skip
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            have hcorr2 := unwindIndents_corr_exact s_content sp_sc hcorr_sc (↑s_content.col)
            have hcorr3 : ScannerSurfCorr
                { (unwindIndents s_content ↑s_content.col) with
                  needIndentCheck := false } sp_sc :=
              ⟨hcorr2.chars_from, hcorr2.col_eq, hcorr2.end_eq, hcorr2.input_prefix, hcorr2.indent_cols_nonneg⟩
            exact ⟨sp_mid, sp_ws, sp_sc, h_disj, hws, hcmt, saveSimpleKey_corr _ sp_sc hcorr3⟩
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            exact ⟨sp_mid, sp_ws, sp_sc, h_disj, hws, hcmt, saveSimpleKey_corr _ sp_sc hcorr_sc⟩

/-- General-column `SSeparateLines 0` from preprocessing with content.
    Works at any starting column — uses nil `SSLComments` when no break consumed,
    and `SIndent 0` (zero-width) which has no column requirement.

    Like `preprocess_some_separate_lines_0`, the `GOpt.some` comment case is
    unreachable but deferred (same root cause). -/
theorem preprocess_some_separate_0_anyCol (sc : ScannerState) (sp : SurfPos)
    (s_prep : ScannerState) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_prep, SSeparateLines 0 sp sp_prep ∧ ScannerSurfCorr s_prep sp_prep := by
  obtain ⟨sp_mid, sp_ws, sp_prep, h_disj, h_ws, h_cmt, hcorr_out⟩ :=
    preprocess_some_ssl_comments_anyCol sc sp s_prep c hcorr hok
  cases h_cmt with
  | none =>
    cases h_disj with
    | inl h_ssl_col =>
      exact ⟨sp_ws,
        SSeparateLines.commented 0 sp sp_mid sp_ws h_ssl_col.1
          (SFlowLinePrefix.mk 0 sp_mid sp_mid sp_ws (SIndent.zero sp_mid)
            (ScalarProduction.gstar_sswhite_to_gopt_sep h_ws)),
        hcorr_out⟩
    | inr h_eq =>
      subst h_eq
      -- No break consumed (sp_mid = sp). Need SSeparateLines 0 sp_mid sp_ws
      -- but SSLComments requires break. Would need SSeparateInLine (whites/startOfLine).
      exact ⟨sp_ws, sorry, hcorr_out⟩
  | some =>
    exact ⟨sp_prep, sorry, hcorr_out⟩

/-- When `scanNextToken_preprocess` returns `some (s_prep, c)`, the resulting
    scanner state has `s_prep.peek? = some c`. This follows from the definition's
    final `match s.peek? with | some c => return some (s, c)`. -/
theorem preprocess_some_peek {sc s_prep : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.peek? = some c := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok  -- skipToContent
  · simp at hok
  · split at hok  -- hasMore
    · simp at hok
    · split at hok  -- indent handling
      all_goals (  -- both indent branches have identical structure
        split at hok  -- trailing content check
        <;> (try simp at hok)  -- error case
        <;> (split at hok  -- peek? match
          <;> (try simp at hok)  -- none case
          <;> (obtain ⟨h1, h2⟩ := hok; subst h1; subst h2; assumption)))

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
    and finalize the stream.

    **Proven case**: `BlockStack.nil` + `PendingNode.noPending` + col=0.
    This is the primary path for non-BOM inputs. Uses
    `preprocess_none_ssl_comments_col0` → `ssl_comments_extend_stream_col0`.

    **Sorry case**: col≠0 (BOM edge case) or non-nil stack/pending (from §1b–§1e).
    The col≠0 sorry is a genuine YAML grammar limitation — `SSeparateInLine`
    requires either `s-white+` or start-of-line, and after BOM at col=1 with
    a bare break, neither applies. See §0c docstring.
    The non-nil stack/pending cases are downstream of §1b–§1e sorry. -/

-- Helper: handles all PendingNode cases for EOF given stream at sp_block.
theorem eof_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  cases h_pending with
  | noPending =>
    by_cases hcol : sp_block.col = 0
    · obtain ⟨sp_final, h_ssl, h_empty⟩ :=
        preprocess_none_ssl_comments_col0 sc sp_block h_corr hcol h_preprocess
      exact ⟨sp_final, ssl_comments_extend_stream_col0 sp_start sp_block sp_final
        hcol h_stream_block h_ssl, h_empty⟩
    · sorry
  | pendingContent =>
    rename_i h_close_fn
    obtain ⟨sp_final, h_ssl, h_empty⟩ :=
      preprocess_none_ssl_comments sc sp_scan h_corr h_preprocess
    exact ⟨sp_final, h_close_fn sp_final h_ssl, h_empty⟩
  | pendingDocEnd =>
    rename_i h_marker
    obtain ⟨sp_final, h_ssl, h_empty⟩ :=
      preprocess_none_ssl_comments sc sp_scan h_corr h_preprocess
    have h_suffix : SLDocumentSuffix sp_block sp_final :=
      SLDocumentSuffix.mk sp_block sp_scan sp_final h_marker h_ssl
    exact ⟨sp_final,
      SLYamlStream.suffixContinue sp_start sp_block sp_final sp_final sp_final sp_final
        h_stream_block
        (GPlus.mk sp_block sp_final sp_final h_suffix (GStar.nil _))
        (GStar.nil _) (GOpt.none _) (GStar.nil _),
      h_empty⟩
  | pendingDocStart =>
    rename_i h_doc_builder
    obtain ⟨sp_final, h_ssl, h_empty⟩ :=
      preprocess_none_ssl_comments sc sp_scan h_corr h_preprocess
    have h_any_doc : SLAnyDocument sp_block sp_final :=
      h_doc_builder sp_final
        (GAlt.right sp_scan sp_final
          (GSeq.mk sp_scan sp_scan sp_final (GEps.mk sp_scan) h_ssl))
    exact ⟨sp_final,
      SLYamlStream.implicitContinue sp_start sp_block sp_block sp_final sp_final
        h_stream_block
        (GStar.nil _) (GOpt.some sp_block sp_final h_any_doc) (GStar.nil _),
      h_empty⟩
  | pendingDirective =>
    -- Directive at EOF without `---` is invalid YAML; sorry
    rename_i h_dir_acc h_stream_cap
    sorry
  | pendingFlow =>
    rename_i h_close_fn
    obtain ⟨sp_final, h_ssl, h_empty⟩ :=
      preprocess_none_ssl_comments sc sp_scan h_corr h_preprocess
    exact ⟨sp_final, h_close_fn sp_final h_ssl, h_empty⟩
  | pendingBlockContent =>
    rename_i h_close_fn _
    obtain ⟨sp_final, h_ssl, h_empty⟩ :=
      preprocess_none_ssl_comments sc sp_scan h_corr h_preprocess
    exact ⟨sp_final, h_close_fn sp_final h_ssl, h_empty⟩
  | pendingBlock =>
    rename_i h_close_fn _
    obtain ⟨sp_final, h_ssl, h_empty⟩ :=
      preprocess_none_ssl_comments sc sp_scan h_corr h_preprocess
    exact ⟨sp_final,
           h_close_fn sp_final (SBlockNode.emptyNode 0 .blockIn sp_scan sp_final h_ssl),
           h_empty⟩

theorem preprocessing_eof_extends_stream (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow)
    (h_pending : PendingNode sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  exact eof_pending sc sp_start sp_flow sp_scan
    (absorb_stacks sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
    h_pending h_corr h_preprocess

-- Helper: `ScannerSurfCorr` is preserved by the `allowDirectives` flag update
-- used between structural dispatch and block/flow/content dispatch.
theorem corr_of_allowDirectives_update {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr
      (if sc.allowDirectives then
        { sc with allowDirectives := false, documentEverStarted := true }
      else sc) sp := by
  split
  · exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  · exact hcorr

/-! ### §1b Preprocessing + Structural Dispatch

    `scanNextToken_dispatchStructural` handles `---`, `...`, `%`-directives.
    Preprocessing provides SSLComments to close the previous pending node.
    If indent levels decreased, BlockStack pops accordingly.
    The structural token opens a new pending state.

    **Proven case**: `BlockStack.nil` + `PendingNode.noPending`.
    No pending to close. Structural dispatch preserves corr via
    `dispatchStructural_corr`. Opens appropriate pending state. -/

-- Helper: structural dispatch preserves `ScannerSurfCorr` on `some` paths.
theorem dispatchStructural_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_dispatchStructural sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- Flow indent guard
  split at hok
  · split at hok
    · simp at hok
    · -- passes guard; fall through
      split at hok
      · simp at hok  -- documentMarkerInFlow error
      · split at hok
        · have h := Except.ok.inj hok; injection h with h; subst h
          exact scanDocumentStart_corr sc sp hcorr
        · split at hok
          · split at hok
            · simp at hok
            · rename_i s_de hde
              have h := Except.ok.inj hok; injection h with h; subst h
              exact scanDocumentEnd_corr sc sp hcorr s_de hde
          · split at hok
            · split at hok
              · simp at hok
              · rename_i s_dir hdir
                have h := Except.ok.inj hok; injection h with h; subst h
                exact scanDirective_corr sc sp hcorr s_dir hdir
            · simp at hok  -- none case
  · -- not inFlow or indent ok; same dispatch
    split at hok
    · simp at hok
    · split at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanDocumentStart_corr sc sp hcorr
      · split at hok
        · split at hok
          · simp at hok
          · rename_i s_de hde
            have h := Except.ok.inj hok; injection h with h; subst h
            exact scanDocumentEnd_corr sc sp hcorr s_de hde
        · split at hok
          · split at hok
            · simp at hok
            · rename_i s_dir hdir
              have h := Except.ok.inj hok; injection h with h; subst h
              exact scanDirective_corr sc sp hcorr s_dir hdir
          · simp at hok  -- none

-- Helper (4f.2): structural dispatch at a position produces marker evidence.
-- Every `.ok (some _)` branch of `scanNextToken_dispatchStructural` requires
-- `s.col = 0`, and the marker is either `SCDirectivesEnd` (for `---`) or
-- `SCDocumentEnd` (for `...`). Directive (`%`) produces pendingDirective
-- with sorry for the accumulator (future: scanDirective_prod).
theorem structural_dispatch_to_pending
    (s_prep s' : ScannerState) (c : Char) (sp_start sp : SurfPos)
    (hcorr : ScannerSurfCorr s_prep sp)
    (h_stream : SLYamlStream sp_start sp)
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp', sp.col = 0 ∧ PendingNode sp_start sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchStructural at h_dispatch
  simp only [bind, Except.bind, pure, Except.pure] at h_dispatch
  -- Reusable subproof for document-start branches
  suffices doc_start_tac : ∀ (hat : atDocumentStart s_prep = true)
      (hcol_s : s_prep.col = 0) (_ : s' = scanDocumentStart s_prep),
      ∃ sp', sp.col = 0 ∧ PendingNode sp_start sp sp' ∧ ScannerSurfCorr s' sp' by
    -- Reusable subproof for document-end branches
    suffices doc_end_tac : ∀ (hat : atDocumentEnd s_prep = true)
        (s_de : ScannerState) (hde : scanDocumentEnd s_prep = .ok s_de)
        (_ : s' = s_de),
        ∃ sp', sp.col = 0 ∧ PendingNode sp_start sp sp' ∧ ScannerSurfCorr s' sp' by
      -- Dispatch case splitting
      split at h_dispatch
      · split at h_dispatch
        · simp at h_dispatch
        · split at h_dispatch
          · simp at h_dispatch
          · split at h_dispatch
            · -- atDocumentStart (inFlow)
              rename_i _ _ _ h_cond
              rw [Bool.and_eq_true] at h_cond
              have h := Except.ok.inj h_dispatch; injection h with h
              exact doc_start_tac h_cond.2 (beq_iff_eq.mp h_cond.1) h.symm
            · -- atDocumentEnd (inFlow): use by_cases to preserve condition
              by_cases h_docEnd : (s_prep.col == 0 && atDocumentEnd s_prep) = true
              · rw [if_pos h_docEnd] at h_dispatch
                rw [Bool.and_eq_true] at h_docEnd
                split at h_dispatch
                · simp at h_dispatch
                · rename_i s_de hde
                  have h := Except.ok.inj h_dispatch; injection h with h
                  exact doc_end_tac h_docEnd.2 s_de hde h.symm
              · rw [if_neg h_docEnd] at h_dispatch
                by_cases h_dir : (c == '%' && s_prep.col == 0) = true
                · rw [if_pos h_dir] at h_dispatch
                  rw [Bool.and_eq_true] at h_dir
                  split at h_dispatch
                  · simp at h_dispatch
                  · rename_i s_dir h_dir_ok
                    have h := Except.ok.inj h_dispatch; injection h with h; subst h
                    have hcol : sp.col = 0 := by rw [hcorr.col_eq]; exact beq_iff_eq.mp h_dir.2
                    obtain ⟨sp', hcorr'⟩ := scanDirective_corr s_prep sp hcorr s_dir h_dir_ok
                    exact ⟨sp', hcol,
                      PendingNode.pendingDirective sp_start sp sp' sorry h_stream,
                      hcorr'⟩
                · rw [if_neg h_dir] at h_dispatch
                  simp at h_dispatch
      · split at h_dispatch
        · simp at h_dispatch
        · split at h_dispatch
          · -- atDocumentStart (not inFlow)
            rename_i _ _ h_cond
            rw [Bool.and_eq_true] at h_cond
            have h := Except.ok.inj h_dispatch; injection h with h
            exact doc_start_tac h_cond.2 (beq_iff_eq.mp h_cond.1) h.symm
          · -- atDocumentEnd (not inFlow): use by_cases to preserve condition
            by_cases h_docEnd : (s_prep.col == 0 && atDocumentEnd s_prep) = true
            · rw [if_pos h_docEnd] at h_dispatch
              rw [Bool.and_eq_true] at h_docEnd
              split at h_dispatch
              · simp at h_dispatch
              · rename_i s_de hde
                have h := Except.ok.inj h_dispatch; injection h with h
                exact doc_end_tac h_docEnd.2 s_de hde h.symm
            · rw [if_neg h_docEnd] at h_dispatch
              by_cases h_dir : (c == '%' && s_prep.col == 0) = true
              · rw [if_pos h_dir] at h_dispatch
                rw [Bool.and_eq_true] at h_dir
                split at h_dispatch
                · simp at h_dispatch
                · rename_i s_dir h_dir_ok
                  have h := Except.ok.inj h_dispatch; injection h with h; subst h
                  have hcol : sp.col = 0 := by rw [hcorr.col_eq]; exact beq_iff_eq.mp h_dir.2
                  obtain ⟨sp', hcorr'⟩ := scanDirective_corr s_prep sp hcorr s_dir h_dir_ok
                  exact ⟨sp', hcol,
                    PendingNode.pendingDirective sp_start sp sp' sorry h_stream,
                    hcorr'⟩
              · rw [if_neg h_dir] at h_dispatch
                simp at h_dispatch
    -- Proof of doc_end_tac
    intro hat s_de hde h_eq; subst h_eq
    obtain ⟨rest, hchars, hcol⟩ := atDocumentEnd_chars s_prep sp hcorr hat
    obtain ⟨sp', h_marker, hcorr'⟩ := scanDocumentEnd_prod s_prep sp hcorr rest hchars hcol s' hde
    exact ⟨sp', hcol, PendingNode.pendingDocEnd sp_start sp sp' h_marker, hcorr'⟩
  -- Proof of doc_start_tac
  intro hat hcol_s h_eq; subst h_eq
  have hcol : sp.col = 0 := by rw [hcorr.col_eq]; exact hcol_s
  obtain ⟨rest, hchars, _⟩ := atDocumentStart_chars s_prep sp hcorr hat
  obtain ⟨sp', h_marker, hcorr'⟩ := scanDocumentStart_prod s_prep sp hcorr rest hchars hcol
  exact ⟨sp', hcol,
    PendingNode.pendingDocStart sp_start sp sp'
      (fun sp_end h_content =>
        SLAnyDocument.explicit sp sp_end
          (SLExplicitDocument.withContent sp sp' sp_end h_marker h_content)),
    hcorr'⟩

-- Helper (4f.3): gap closure + dispatch → PendingNode at SSLComments midpoint.
-- Factors out the shared pattern: close the position gap between sp_mid (SSLComments
-- endpoint) and sp_prep (ScannerSurfCorr position) using col=0 evidence, then
-- construct the new PendingNode with correctly unified positions.
theorem dispatch_new_pending
    (s_prep s' : ScannerState) (c : Char)
    (sp_start sp_mid sp_ws sp_gap sp_prep sp_scan' : SurfPos)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_gap : ScannerSurfCorr s_prep sp_gap)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (hcol_mid : sp_mid.col = 0)
    (hws : GStar SSWhite sp_mid sp_ws)
    (hcmt : GOpt SCNbCommentText sp_ws sp_gap)
    (h_stream_mid : SLYamlStream sp_start sp_mid)
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    PendingNode sp_start sp_mid sp_scan' := by
  have h_gap_eq : sp_gap = sp_prep := ScannerSurfCorr_unique hcorr_gap hcorr_prep
  obtain ⟨sp_disp, hcol_prep, h_pending_new, hcorr_disp⟩ :=
    -- sorry: h_stream needs sp_mid=sp_prep equality proved first (only affects directive case)
    structural_dispatch_to_pending s_prep s' c sp_start sp_prep hcorr_prep sorry h_dispatch
  have h_disp_eq : sp_disp = sp_scan' := ScannerSurfCorr_unique hcorr_disp hcorr_result
  have h_mid_prep : sp_mid = sp_prep := by
    have hcol_gap : sp_gap.col = 0 := h_gap_eq ▸ hcol_prep
    cases hcmt with
    | none =>
      have h1 : sp_ws = sp_mid := gstar_sswhite_col_eq_nil sp_mid sp_ws (by omega) hws
      exact h1.symm.trans h_gap_eq
    | some =>
      rename_i hc
      exfalso; have := scnb_comment_col_gt sp_ws sp_gap hc; omega
  rw [← h_mid_prep, h_disp_eq] at h_pending_new
  exact h_pending_new

-- Helper: handles all PendingNode cases given a stream at sp_block.
-- Factored out so nil, seqLevel, and mapLevel all delegate here.
theorem accum_structural_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  obtain ⟨sp_scan', hcorr_result⟩ :=
    dispatchStructural_corr s_prep sp_prep c hcorr_prep h_dispatch
  cases h_pending with
  | noPending =>
    by_cases hcol : sp_block.col = 0
    · obtain ⟨sp_mid, sp_ws, sp_gap, h_ssl, hcol_mid, hws, hcmt, hcorr_gap⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_block s_prep c h_corr hcol h_preprocess
      have h_stream_mid : SLYamlStream sp_start sp_mid :=
        ssl_comments_extend_stream_col0 sp_start sp_block sp_mid hcol h_stream_block h_ssl
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream_mid, BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             dispatch_new_pending s_prep s' c sp_start sp_mid sp_ws sp_gap sp_prep sp_scan'
               hcorr_prep hcorr_gap hcorr_result hcol_mid hws hcmt h_stream_mid h_dispatch,
             hcorr_result⟩
    · sorry
  | pendingDocEnd =>
    rename_i h_marker_old
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, sp_ws, sp_gap, h_ssl, hcol_mid, hws, hcmt, hcorr_gap⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_suffix : SLDocumentSuffix sp_block sp_mid :=
        SLDocumentSuffix.mk sp_block sp_scan sp_mid h_marker_old h_ssl
      have h_stream' : SLYamlStream sp_start sp_mid :=
        SLYamlStream.suffixContinue sp_start sp_block sp_mid sp_mid sp_mid sp_mid
          h_stream_block (GPlus.mk sp_block sp_mid sp_mid h_suffix (GStar.nil _))
          (GStar.nil _) (GOpt.none _) (GStar.nil _)
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream', BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             dispatch_new_pending s_prep s' c sp_start sp_mid sp_ws sp_gap sp_prep sp_scan'
               hcorr_prep hcorr_gap hcorr_result hcol_mid hws hcmt h_stream' h_dispatch,
             hcorr_result⟩
    · sorry
  | pendingDocStart =>
    rename_i h_doc_builder_old
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, sp_ws, sp_gap, h_ssl, hcol_mid, hws, hcmt, hcorr_gap⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_any : SLAnyDocument sp_block sp_mid :=
        h_doc_builder_old sp_mid
          (GAlt.right sp_scan sp_mid
            (GSeq.mk sp_scan sp_scan sp_mid (GEps.mk sp_scan) h_ssl))
      have h_stream' : SLYamlStream sp_start sp_mid :=
        SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
          h_stream_block (GStar.nil _) (GOpt.some sp_block sp_mid h_any) (GStar.nil _)
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream', BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             dispatch_new_pending s_prep s' c sp_start sp_mid sp_ws sp_gap sp_prep sp_scan'
               hcorr_prep hcorr_gap hcorr_result hcol_mid hws hcmt h_stream' h_dispatch,
             hcorr_result⟩
    · sorry
  | pendingDirective =>
    -- Directive at structural dispatch: requires scanDirective_prod infrastructure
    rename_i h_dir_acc_old h_stream_old
    sorry
  | pendingContent h_closable_old
  | pendingFlow h_closable_old =>
    all_goals (
      rename_i h_closable_old
      by_cases hcol : sp_scan.col = 0
      · obtain ⟨sp_mid, sp_ws, sp_gap, h_ssl, hcol_mid, hws, hcmt, hcorr_gap⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        have h_stream_new := h_closable_old sp_mid h_ssl
        exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
               h_stream_new,
               BlockStack.nil sp_mid,
               FlowStack.nil sp_mid,
               dispatch_new_pending s_prep s' c sp_start sp_mid sp_ws sp_gap sp_prep sp_scan'
                 hcorr_prep hcorr_gap hcorr_result hcol_mid hws hcmt h_stream_new h_dispatch,
               hcorr_result⟩
      · sorry)
  | pendingBlockContent =>
    rename_i h_closable_old _
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, sp_ws, sp_gap, h_ssl, hcol_mid, hws, hcmt, hcorr_gap⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_stream_new := h_closable_old sp_mid h_ssl
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
             h_stream_new,
             BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             dispatch_new_pending s_prep s' c sp_start sp_mid sp_ws sp_gap sp_prep sp_scan'
               hcorr_prep hcorr_gap hcorr_result hcol_mid hws hcmt h_stream_new h_dispatch,
             hcorr_result⟩
    · sorry
  | pendingBlock =>
    rename_i h_close_old _
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, sp_ws, sp_gap, h_ssl, hcol_mid, hws, hcmt, hcorr_gap⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_stream_new :=
        h_close_old sp_mid (SBlockNode.emptyNode 0 .blockIn sp_scan sp_mid h_ssl)
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
             h_stream_new,
             BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             dispatch_new_pending s_prep s' c sp_start sp_mid sp_ws sp_gap sp_prep sp_scan'
               hcorr_prep hcorr_gap hcorr_result hcol_mid hws hcmt h_stream_new h_dispatch,
             hcorr_result⟩
    · sorry

theorem accum_step_structural (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow)
    (h_pending : PendingNode sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchStructural s_prep c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  exact accum_structural_pending sc sp_start sp_flow sp_scan s_prep s' c
    (absorb_stacks sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
    h_pending h_corr h_preprocess h_dispatch

/-! ### §1c Preprocessing + Flow Indicator Dispatch

    `scanNextToken_dispatchFlowIndicators` handles `[`, `]`, `{`, `}`, `,`.
    Flow collection tracking via FlowStack:
    - `[`/`{`: push FlowStack level (flowSeqLevel/flowMapLevel)
    - `]`/`}`: close flow collection (FlowStack popped at next absorption)
    - `,`: entry separator within current flow level

    **Architecture (4h.2):** Character-dependent FlowStack construction.
    A local helper `new_flow_state` case-splits on `c` to determine
    whether to push a FlowStack level (`[`/`{`) or produce nil with
    `PendingNode.pendingFlow` (`]`/`}`/`,`). -/

-- Helper: flow indicator dispatch preserves `ScannerSurfCorr` on `some` paths.
theorem dispatchFlowIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_dispatchFlowIndicators sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- c == '['
  split at hok
  · have h := Except.ok.inj hok; injection h with h; subst h
    exact scanFlowSequenceStart_corr sc sp hcorr
  -- c == ']'
  · split at hok
    · split at hok
      · simp at hok  -- flowEndOutsideFlow
      · -- validateFlowClose is Except Unit, split on it
        split at hok
        · simp at hok
        · have h := Except.ok.inj hok; injection h with h; subst h
          exact scanFlowSequenceEnd_corr sc sp hcorr
    -- c == '{'
    · split at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanFlowMappingStart_corr sc sp hcorr
      -- c == '}'
      · split at hok
        · split at hok
          · simp at hok  -- flowEndOutsideFlow
          · split at hok
            · simp at hok
            · have h := Except.ok.inj hok; injection h with h; subst h
              exact scanFlowMappingEnd_corr sc sp hcorr
        -- c == ','
        · split at hok
          · split at hok
            · simp at hok  -- flowEndOutsideFlow
            · split at hok
              · simp at hok
              · rename_i s_fe hfe
                have h := Except.ok.inj hok; injection h with h; subst h
                exact scanFlowEntry_corr sc sp hcorr s_fe hfe
          -- none (fallthrough)
          · simp at hok

-- Helper: handles all PendingNode cases for flow dispatch given stream at sp_block.
theorem accum_flow_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  obtain ⟨sp_scan', hcorr_result⟩ :=
    dispatchFlowIndicators_corr _ sp_prep c (corr_of_allowDirectives_update hcorr_prep) h_dispatch
  -- Character-dependent FlowStack + PendingNode construction (4h.2).
  -- For `[`/`{`: push FlowStack level + PendingNode.noPending (clean state inside flow).
  -- For `]`/`}`/`,`: FlowStack.nil + PendingNode.pendingFlow (flow contribution pending).
  have new_flow_state : ∀ (sp_mid : SurfPos) (h_str_mid : SLYamlStream sp_start sp_mid),
      ∃ sp_flow', FlowStack sp_mid sp_flow' ∧ PendingNode sp_start sp_flow' sp_scan' := by
    intro sp_mid h_str_mid
    by_cases hc_seq : c = '['
    · exact ⟨sp_scan',
             FlowStack.flowSeqLevel sp_mid sp_mid sp_scan' (FlowStack.nil sp_mid)
               (fun _ h_str => sorry),
             PendingNode.noPending sp_start sp_scan'⟩
    · by_cases hc_map : c = '{'
      · exact ⟨sp_scan',
               FlowStack.flowMapLevel sp_mid sp_mid sp_scan' (FlowStack.nil sp_mid)
                 (fun _ h_str => sorry),
               PendingNode.noPending sp_start sp_scan'⟩
      · exact ⟨sp_mid,
               FlowStack.nil sp_mid,
               PendingNode.pendingFlow sp_start sp_mid sp_scan'
                 (fun sp_mid2 h_ssl => sorry)⟩
  cases h_pending with
  | noPending =>
    obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_block h_stream_block
    exact ⟨sp_block, sp_block, sp_flow', sp_scan', h_stream_block,
           BlockStack.nil sp_block, h_flow', h_pend', hcorr_result⟩
  | pendingDocEnd =>
    rename_i h_marker_old
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_suffix : SLDocumentSuffix sp_block sp_mid :=
        SLDocumentSuffix.mk sp_block sp_scan sp_mid h_marker_old h_ssl
      have h_stream' : SLYamlStream sp_start sp_mid :=
        SLYamlStream.suffixContinue sp_start sp_block sp_mid sp_mid sp_mid sp_mid
          h_stream_block (GPlus.mk sp_block sp_mid sp_mid h_suffix (GStar.nil _))
          (GStar.nil _) (GOpt.none _) (GStar.nil _)
      obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_mid h_stream'
      exact ⟨sp_mid, sp_mid, sp_flow', sp_scan', h_stream',
             BlockStack.nil sp_mid, h_flow', h_pend', hcorr_result⟩
    · sorry
  | pendingDocStart =>
    rename_i h_doc_builder_old
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_any : SLAnyDocument sp_block sp_mid :=
        h_doc_builder_old sp_mid
          (GAlt.right sp_scan sp_mid
            (GSeq.mk sp_scan sp_scan sp_mid (GEps.mk sp_scan) h_ssl))
      have h_stream' : SLYamlStream sp_start sp_mid :=
        SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
          h_stream_block (GStar.nil _) (GOpt.some sp_block sp_mid h_any) (GStar.nil _)
      obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_mid h_stream'
      exact ⟨sp_mid, sp_mid, sp_flow', sp_scan', h_stream',
             BlockStack.nil sp_mid, h_flow', h_pend', hcorr_result⟩
    · sorry
  | pendingDirective =>
    rename_i h_dir_acc_old h_stream_old
    sorry
  | pendingContent h_closable_old
  | pendingFlow h_closable_old =>
    all_goals (
      rename_i h_closable_old
      by_cases hcol : sp_scan.col = 0
      · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        have h_stream_mid : SLYamlStream sp_start sp_mid := h_closable_old sp_mid h_ssl
        obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_mid h_stream_mid
        exact ⟨sp_mid, sp_mid, sp_flow', sp_scan',
               h_stream_mid,
               BlockStack.nil sp_mid, h_flow', h_pend', hcorr_result⟩
      · sorry)
  | pendingBlockContent =>
    rename_i h_closable_old _
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_stream_mid : SLYamlStream sp_start sp_mid := h_closable_old sp_mid h_ssl
      obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_mid h_stream_mid
      exact ⟨sp_mid, sp_mid, sp_flow', sp_scan',
             h_stream_mid,
             BlockStack.nil sp_mid, h_flow', h_pend', hcorr_result⟩
    · sorry
  | pendingBlock =>
    rename_i h_close_old _
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_stream_mid : SLYamlStream sp_start sp_mid :=
        h_close_old sp_mid (SBlockNode.emptyNode 0 .blockIn sp_scan sp_mid h_ssl)
      obtain ⟨sp_flow', h_flow', h_pend'⟩ := new_flow_state sp_mid h_stream_mid
      exact ⟨sp_mid, sp_mid, sp_flow', sp_scan',
             h_stream_mid,
             BlockStack.nil sp_mid, h_flow', h_pend', hcorr_result⟩
    · sorry

theorem accum_step_flow (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow)
    (h_pending : PendingNode sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchFlowIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  exact accum_flow_pending sc sp_start sp_flow sp_scan s_prep s' c
    (absorb_stacks sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
    h_pending h_corr h_preprocess h_dispatch

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
      `.blockMappingStart` → `.mapLevel` pushed if needed

    **Proven case**: `BlockStack.nil` + `PendingNode.noPending`.
    No pending to close. Block indicator opens `pendingBlock`. -/

-- Helper: block indicator dispatch preserves `ScannerSurfCorr` on `some` paths.
theorem dispatchBlockIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_dispatchBlockIndicators sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- c == '-' && !inFlow && isBlockEntryCandidate
  split at hok
  · split at hok
    · simp at hok
    · rename_i s_be hbe
      have h := Except.ok.inj hok; injection h with h; subst h
      exact scanBlockEntry_corr sc sp hcorr s_be hbe
  -- c == '?' && isKeyCandidate
  · split at hok
    · split at hok
      · simp at hok
      · rename_i s_k hk
        have h := Except.ok.inj hok; injection h with h; subst h
        exact scanKey_corr sc sp hcorr s_k hk
    -- c == ':' && isValueCandidate
    · split at hok
      · split at hok
        · simp at hok
        · rename_i s_v hv
          have h := Except.ok.inj hok; injection h with h; subst h
          exact scanValue_corr sc sp hcorr s_v hv
      -- none (fallthrough)
      · simp at hok

-- Block entry dispatch full production: GLit '-' + GNot SNsChar + ScannerSurfCorr.
-- Unfolds dispatchBlockIndicators for the '-' case. The result includes:
-- 1) A literal dash character
-- 2) Negative lookahead: the char after '-' is not ns-char
-- 3) Scanner/surface correspondence after the dash
theorem dispatchBlockEntry_full_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '-')
    (hok : scanNextToken_dispatchBlockIndicators sc '-' = .ok (some s')) :
    ∃ sp', GLit '-' sp sp' ∧ GNot SNsChar sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- '-' == '-' && ... is true: enter scanBlockEntry path
    rename_i h_entry_cond
    have h_candidate : isBlockEntryCandidate sc = true := by
      simp [Bool.and_eq_true] at h_entry_cond; exact h_entry_cond.2
    split at hok
    · simp at hok
    · rename_i s_be hbe
      have h := Except.ok.inj hok; injection h with h; subst h
      obtain ⟨sp', h_lit, hcorr'⟩ := scanBlockEntry_prod sc ⟨'-' :: rest, sc.col⟩
        hcorr hpeek s_be hbe
      cases h_lit
      exact ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col,
             blockEntryCandidate_gnot sc rest sc.col hcorr h_candidate, hcorr'⟩
  · -- First branch failed: '-' ≠ '?' and '-' ≠ ':' means remaining dispatch returns none
    have hq : ('-' == '?' : Bool) = false := by native_decide
    have hc : ('-' == ':' : Bool) = false := by native_decide
    simp only [hq, hc, Bool.false_and, if_neg Bool.false_ne_true] at hok
    simp at hok

-- Helper: handles all PendingNode cases for block dispatch given stream at sp_block.
theorem accum_block_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  obtain ⟨sp_scan', hcorr_result⟩ :=
    dispatchBlockIndicators_corr _ sp_prep c (corr_of_allowDirectives_update hcorr_prep) h_dispatch
  cases h_pending with
  | noPending =>
    by_cases hcol : sp_block.col = 0
    · by_cases hc : c = '-'
      · -- Block entry '-' at col=0: build real h_closable (empty entry)
        subst hc
        -- Extract block entry evidence from dispatch
        have hpeek_disp : (if s_prep.allowDirectives then
            { s_prep with allowDirectives := false, documentEverStarted := true }
          else s_prep).peek? = some '-' := by
          have := preprocess_some_peek h_preprocess
          split
          · show s_prep.peek? = some '-'; exact this
          · exact this
        obtain ⟨sp_dash, h_dash, h_gnot, hcorr_dash⟩ :=
          dispatchBlockEntry_full_prod _ sp_prep
            (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
        have hsp_dash_eq := ScannerSurfCorr_unique hcorr_dash hcorr_result
        rw [hsp_dash_eq] at h_dash h_gnot
        -- Extract preprocessing evidence
        obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl_pre, hcol_mid, hws, hcmt, hcorr_sc⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_block s_prep '-' h_corr hcol h_preprocess
        have hsp_sc_eq := ScannerSurfCorr_unique hcorr_sc hcorr_prep
        subst hsp_sc_eq
        -- Case-split on whitespace: need sp_mid = sp_prep for SIndent 0
        cases hws with
        | nil =>
          cases hcmt with
          | none =>
            -- sp_prep = sp_mid at col=0: dash is at column 0
            -- h_dash : GLit '-' sp_mid sp_scan'
            -- h_gnot : GNot SNsChar sp_scan'
            exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                   BlockStack.nil sp_block, FlowStack.nil sp_block,
                   PendingNode.pendingBlock sp_start sp_block sp_scan'
                     (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                       have h_indented :=
                         SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                       have h_entry :=
                         SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' sp_scan' sp_final
                           (SIndent.zero sp_mid) h_dash h_gnot h_indented
                       have h_block :=
                         SBlockNode.blockSeq 0 .blockIn sp_block sp_block sp_mid sp_final
                           (GOpt.none sp_block) h_ssl_pre h_entry
                       have h_bare := SLBareDocument.mk sp_block sp_final h_block
                       SLYamlStream.implicitContinue sp_start sp_block sp_block sp_final sp_final
                         h_stream_block (GStar.nil _)
                         (GOpt.some sp_block sp_final
                           (SLAnyDocument.bare sp_block sp_final h_bare))
                         (GStar.nil _))
                     (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                       have h_indented :=
                         SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                       have h_entry :=
                         SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' sp_scan' sp_final
                           (SIndent.zero sp_mid) h_dash h_gnot h_indented
                       ⟨sp_mid, h_entry, fun sp_end h_entries =>
                         have h_block :=
                           SBlockNode.blockSeq 0 .blockIn sp_block sp_block sp_mid sp_end
                             (GOpt.none sp_block) h_ssl_pre h_entries
                         have h_bare := SLBareDocument.mk sp_block sp_end h_block
                         SLYamlStream.implicitContinue sp_start sp_block sp_block sp_end sp_end
                           h_stream_block (GStar.nil _)
                           (GOpt.some sp_block sp_end
                             (SLAnyDocument.bare sp_block sp_end h_bare))
                           (GStar.nil _)⟩),
                   hcorr_result⟩
          | some =>
            -- Comment text before '-' — unreachable (scanner greedily consumes comments)
            exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                   BlockStack.nil sp_block, FlowStack.nil sp_block,
                   PendingNode.pendingBlock sp_start sp_block sp_scan'
                     (fun sp_mid2 _h_node => sorry)
                     (fun sp_mid2 _h_node => sorry), hcorr_result⟩
        | cons =>
          -- Whitespace before '-': dash at col > 0, can't build SBlockSeqEntries 0
          exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                 BlockStack.nil sp_block, FlowStack.nil sp_block,
                 PendingNode.pendingBlock sp_start sp_block sp_scan'
                   (fun sp_mid2 _h_node => sorry)
                   (fun sp_mid2 _h_node => sorry), hcorr_result⟩
      · -- c ≠ '-': block key (?) or value (:) — grammar evidence deferred
        exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
               BlockStack.nil sp_block, FlowStack.nil sp_block,
               PendingNode.pendingBlock sp_start sp_block sp_scan'
                 (fun sp_mid _h_node => sorry)
                 (fun sp_mid _h_node => sorry), hcorr_result⟩
    · -- col ≠ 0: deferred
      exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
             BlockStack.nil sp_block, FlowStack.nil sp_block,
             PendingNode.pendingBlock sp_start sp_block sp_scan'
               (fun sp_mid _h_node => sorry)
               (fun sp_mid _h_node => sorry), hcorr_result⟩
  | pendingDocEnd =>
    rename_i h_marker_old
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_suffix : SLDocumentSuffix sp_block sp_mid :=
        SLDocumentSuffix.mk sp_block sp_scan sp_mid h_marker_old h_ssl
      have h_stream' : SLYamlStream sp_start sp_mid :=
        SLYamlStream.suffixContinue sp_start sp_block sp_mid sp_mid sp_mid sp_mid
          h_stream_block (GPlus.mk sp_block sp_mid sp_mid h_suffix (GStar.nil _))
          (GStar.nil _) (GOpt.none _) (GStar.nil _)
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream', BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             PendingNode.pendingBlock sp_start sp_mid sp_scan'
               (fun sp_mid2 _h_node => sorry)
               (fun sp_mid2 _h_node => sorry), hcorr_result⟩
    · sorry
  | pendingDocStart =>
    rename_i h_doc_builder_old
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_any : SLAnyDocument sp_block sp_mid :=
        h_doc_builder_old sp_mid
          (GAlt.right sp_scan sp_mid
            (GSeq.mk sp_scan sp_scan sp_mid (GEps.mk sp_scan) h_ssl))
      have h_stream' : SLYamlStream sp_start sp_mid :=
        SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
          h_stream_block (GStar.nil _) (GOpt.some sp_block sp_mid h_any) (GStar.nil _)
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream', BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             PendingNode.pendingBlock sp_start sp_mid sp_scan'
               (fun sp_mid2 _h_node => sorry)
               (fun sp_mid2 _h_node => sorry), hcorr_result⟩
    · sorry
  | pendingDirective =>
    rename_i h_dir_acc_old h_stream_old
    sorry
  | pendingContent h_closable_old
  | pendingFlow h_closable_old =>
    all_goals (
      rename_i h_closable_old
      by_cases hcol : sp_scan.col = 0
      · by_cases hc : c = '-'
        · -- '-' at col=0: close old pending, start new block sequence with real closures
          subst hc
          obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, hcorr_sc⟩ :=
            preprocess_some_ssl_comments_col0 sc sp_scan s_prep '-' h_corr hcol h_preprocess
          have hsp_sc_eq := ScannerSurfCorr_unique hcorr_sc hcorr_prep
          subst hsp_sc_eq
          have h_stream_new := h_closable_old sp_mid h_ssl
          cases hws with
          | nil =>
            cases hcmt with
            | none =>
              -- sp_mid at col=0, dash at sp_mid
              have hpeek_disp : (if s_prep.allowDirectives then
                  { s_prep with allowDirectives := false, documentEverStarted := true }
                else s_prep).peek? = some '-' := by
                have := preprocess_some_peek h_preprocess
                split
                · show s_prep.peek? = some '-'; exact this
                · exact this
              obtain ⟨sp_dash, h_dash, h_gnot, hcorr_dash⟩ :=
                dispatchBlockEntry_full_prod _ sp_mid
                  (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
              have hsp_dash_eq := ScannerSurfCorr_unique hcorr_dash hcorr_result
              rw [hsp_dash_eq] at h_dash h_gnot
              -- Build zero-width SSLComments at col=0
              have hcol_eq : sp_mid = ⟨sp_mid.chars, 0⟩ := by
                cases sp_mid; simp at hcol_mid; simp [hcol_mid]
              have h_ssl_zero : SSLComments sp_mid sp_mid :=
                hcol_eq ▸ SSLComments.startOfLine sp_mid.chars ⟨sp_mid.chars, 0⟩
                  (GStar.nil ⟨sp_mid.chars, 0⟩)
              exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream_new,
                     BlockStack.nil sp_mid, FlowStack.nil sp_mid,
                     PendingNode.pendingBlock sp_start sp_mid sp_scan'
                       (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                         have h_indented :=
                           SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                         have h_entry :=
                           SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' sp_scan' sp_final
                             (SIndent.zero sp_mid) h_dash h_gnot h_indented
                         have h_block :=
                           SBlockNode.blockSeq 0 .blockIn sp_mid sp_mid sp_mid sp_final
                             (GOpt.none sp_mid) h_ssl_zero h_entry
                         have h_bare := SLBareDocument.mk sp_mid sp_final h_block
                         SLYamlStream.implicitContinue sp_start sp_mid sp_mid sp_final sp_final
                           h_stream_new (GStar.nil _)
                           (GOpt.some sp_mid sp_final
                             (SLAnyDocument.bare sp_mid sp_final h_bare))
                           (GStar.nil _))
                       (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                         have h_indented :=
                           SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                         have h_entry :=
                           SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' sp_scan' sp_final
                             (SIndent.zero sp_mid) h_dash h_gnot h_indented
                         ⟨sp_mid, h_entry, fun sp_end h_entries =>
                           have h_block :=
                             SBlockNode.blockSeq 0 .blockIn sp_mid sp_mid sp_mid sp_end
                               (GOpt.none sp_mid) h_ssl_zero h_entries
                           have h_bare := SLBareDocument.mk sp_mid sp_end h_block
                           SLYamlStream.implicitContinue sp_start sp_mid sp_mid sp_end sp_end
                             h_stream_new (GStar.nil _)
                             (GOpt.some sp_mid sp_end
                               (SLAnyDocument.bare sp_mid sp_end h_bare))
                             (GStar.nil _)⟩),
                     hcorr_result⟩
            | some =>
              exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream_new,
                     BlockStack.nil sp_mid, FlowStack.nil sp_mid,
                     PendingNode.pendingBlock sp_start sp_mid sp_scan'
                       (fun sp_mid2 _h_node => sorry)
                       (fun sp_mid2 _h_node => sorry), hcorr_result⟩
          | cons =>
            exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream_new,
                   BlockStack.nil sp_mid, FlowStack.nil sp_mid,
                   PendingNode.pendingBlock sp_start sp_mid sp_scan'
                     (fun sp_mid2 _h_node => sorry)
                     (fun sp_mid2 _h_node => sorry), hcorr_result⟩
        · -- c ≠ '-': close old pending, new block with sorry closures
          obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
            preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
          exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
                 h_closable_old sp_mid h_ssl,
                 BlockStack.nil sp_mid,
                 FlowStack.nil sp_mid,
                 PendingNode.pendingBlock sp_start sp_mid sp_scan'
                   (fun sp_mid2 _h_node => sorry)
                   (fun sp_mid2 _h_node => sorry), hcorr_result⟩
      · sorry)
  | pendingBlockContent =>
    rename_i h_closable_old h_entry_old
    by_cases hcol : sp_scan.col = 0
    · by_cases hc : c = '-'
      · -- Same-level '-': accumulate entries via h_entry_old (content variant)
        subst hc
        obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, hcorr_sc⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep '-' h_corr hcol h_preprocess
        have hsp_sc_eq := ScannerSurfCorr_unique hcorr_sc hcorr_prep
        subst hsp_sc_eq
        cases hws with
        | nil =>
          cases hcmt with
          | none =>
            have hpeek_disp : (if s_prep.allowDirectives then
                { s_prep with allowDirectives := false, documentEverStarted := true }
              else s_prep).peek? = some '-' := by
              have := preprocess_some_peek h_preprocess
              split
              · show s_prep.peek? = some '-'; exact this
              · exact this
            obtain ⟨sp_dash2, h_dash2, h_gnot2, hcorr_dash2⟩ :=
              dispatchBlockEntry_full_prod _ sp_mid
                (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
            have hsp_dash2_eq := ScannerSurfCorr_unique hcorr_dash2 hcorr_result
            rw [hsp_dash2_eq] at h_dash2 h_gnot2
            -- Accumulate: extend entries from entry closure
            obtain ⟨sp_first, h_entries_old, h_cont⟩ :=
              h_entry_old sp_mid h_ssl
            exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                   BlockStack.nil sp_block, FlowStack.nil sp_block,
                   PendingNode.pendingBlock sp_start sp_block sp_scan'
                     (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                       have h_indented :=
                         SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                       h_cont sp_final (SBlockSeqEntries_snoc h_entries_old
                         (SIndent.zero sp_mid) h_dash2 h_gnot2 h_indented))
                     (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                       have h_indented :=
                         SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                       ⟨sp_first, SBlockSeqEntries_snoc h_entries_old
                         (SIndent.zero sp_mid) h_dash2 h_gnot2 h_indented, h_cont⟩),
                   hcorr_result⟩
          | some =>
            exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
                   h_closable_old sp_mid h_ssl,
                   BlockStack.nil sp_mid, FlowStack.nil sp_mid,
                   PendingNode.pendingBlock sp_start sp_mid sp_scan'
                     (fun sp_mid2 _h_node => sorry)
                     (fun sp_mid2 _h_node => sorry), hcorr_result⟩
        | cons =>
          exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
                 h_closable_old sp_mid h_ssl,
                 BlockStack.nil sp_mid, FlowStack.nil sp_mid,
                 PendingNode.pendingBlock sp_start sp_mid sp_scan'
                   (fun sp_mid2 _h_node => sorry)
                   (fun sp_mid2 _h_node => sorry), hcorr_result⟩
      · -- c ≠ '-': close content to stream
        obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
               h_closable_old sp_mid h_ssl,
               BlockStack.nil sp_mid, FlowStack.nil sp_mid,
               PendingNode.pendingBlock sp_start sp_mid sp_scan'
                 (fun sp_mid2 _h_node => sorry)
                 (fun sp_mid2 _h_node => sorry), hcorr_result⟩
    · sorry
  | pendingBlock =>
    rename_i h_close_old h_close_entry_old
    by_cases hcol : sp_scan.col = 0
    · by_cases hc : c = '-'
      · -- Same-level '-': accumulate entries via h_close_entry_old
        subst hc
        obtain ⟨sp_mid, sp_ws, sp_sc, h_ssl, hcol_mid, hws, hcmt, hcorr_sc⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep '-' h_corr hcol h_preprocess
        have hsp_sc_eq := ScannerSurfCorr_unique hcorr_sc hcorr_prep
        subst hsp_sc_eq
        have h_node_old : SBlockNode 0 .blockIn sp_scan sp_mid :=
          SBlockNode.emptyNode 0 .blockIn sp_scan sp_mid h_ssl
        cases hws with
        | nil =>
          cases hcmt with
          | none =>
            -- sp_sc = sp_mid: dash is at column 0
            have hpeek_disp : (if s_prep.allowDirectives then
                { s_prep with allowDirectives := false, documentEverStarted := true }
              else s_prep).peek? = some '-' := by
              have := preprocess_some_peek h_preprocess
              split
              · show s_prep.peek? = some '-'; exact this
              · exact this
            obtain ⟨sp_dash2, h_dash2, h_gnot2, hcorr_dash2⟩ :=
              dispatchBlockEntry_full_prod _ sp_mid
                (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
            have hsp_dash2_eq := ScannerSurfCorr_unique hcorr_dash2 hcorr_result
            rw [hsp_dash2_eq] at h_dash2 h_gnot2
            -- Accumulate: extend entries from previous iteration
            obtain ⟨sp_first, h_entries_old, h_cont⟩ :=
              h_close_entry_old sp_mid h_node_old
            exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                   BlockStack.nil sp_block, FlowStack.nil sp_block,
                   PendingNode.pendingBlock sp_start sp_block sp_scan'
                     (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                       have h_indented :=
                         SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                       h_cont sp_final (SBlockSeqEntries_snoc h_entries_old
                         (SIndent.zero sp_mid) h_dash2 h_gnot2 h_indented))
                     (fun sp_final (h_node : SBlockNode 0 .blockIn sp_scan' sp_final) =>
                       have h_indented :=
                         SBlockIndented.node 0 .blockIn sp_scan' sp_final h_node
                       ⟨sp_first, SBlockSeqEntries_snoc h_entries_old
                         (SIndent.zero sp_mid) h_dash2 h_gnot2 h_indented, h_cont⟩),
                   hcorr_result⟩
          | some =>
            -- Comment before dash — sorry
            exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
                   h_close_old sp_mid h_node_old,
                   BlockStack.nil sp_mid, FlowStack.nil sp_mid,
                   PendingNode.pendingBlock sp_start sp_mid sp_scan'
                     (fun sp_mid2 _h_node => sorry)
                     (fun sp_mid2 _h_node => sorry), hcorr_result⟩
        | cons =>
          -- Whitespace before dash — sorry
          exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
                 h_close_old sp_mid h_node_old,
                 BlockStack.nil sp_mid, FlowStack.nil sp_mid,
                 PendingNode.pendingBlock sp_start sp_mid sp_scan'
                   (fun sp_mid2 _h_node => sorry)
                   (fun sp_mid2 _h_node => sorry), hcorr_result⟩
      · -- c ≠ '-': close old entry to stream
        obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
               h_close_old sp_mid (SBlockNode.emptyNode 0 .blockIn sp_scan sp_mid h_ssl),
               BlockStack.nil sp_mid, FlowStack.nil sp_mid,
               PendingNode.pendingBlock sp_start sp_mid sp_scan'
                 (fun sp_mid2 _h_node => sorry)
                 (fun sp_mid2 _h_node => sorry), hcorr_result⟩
    · sorry

theorem accum_step_block (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow)
    (h_pending : PendingNode sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  exact accum_block_pending sc sp_start sp_flow sp_scan s_prep s' c
    (absorb_stacks sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
    h_pending h_corr h_preprocess h_dispatch

/-! ### §1e Preprocessing + Content Dispatch

    `scanNextToken_dispatchContent` handles all content tokens:
    `&` anchor, `*` alias, `!` tag, `|`/`>` block scalar, `"` double-quoted,
    `'` single-quoted, plain scalar. Never returns `none`.

    When inside an active BlockStack, the content token contributes to the
    current block entry's `SBlockIndented` component. The BlockStack itself
    doesn't change — only PendingNode transitions to pendingContent.

    **Helper**: `dispatchContent_corr` proves that all content dispatch paths
    preserve `ScannerSurfCorr`. This factors out the dispatch analysis from
    the per-case proofs below.

    **Proven case**: `BlockStack.nil` + `PendingNode.noPending`.
    No pending to close — stream unchanged, opens `pendingContent`.
    This is the primary path for the first content token in any document. -/

-- Helper: content dispatch preserves `ScannerSurfCorr` on all `.ok` paths.
-- Unfolds `scanNextToken_dispatchContent`, splits on character checks,
-- and delegates to per-scanner `_corr` theorems.
theorem dispatchContent_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- c == '&' (anchor)
  split at hok
  · have h := Except.ok.inj hok; subst h
    obtain ⟨sp', hcorr'⟩ := scanAnchorOrAlias_corr sc sp hcorr true
    exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  -- c == '*' (alias)
  · split at hok
    · split at hok
      · simp at hok  -- undefinedAlias error
      · have h := Except.ok.inj hok; subst h
        exact scanAnchorOrAlias_corr sc sp hcorr false
    -- c == '!' (tag)
    · split at hok
      · have h := Except.ok.inj hok; subst h
        exact scanTag_corr sc sp hcorr
      -- c == '|' || c == '>' (block scalar)
      · split at hok
        · split at hok
          · simp at hok
          · rename_i s_bs hbs
            have h := Except.ok.inj hok; subst h
            exact scanBlockScalar_corr sc sp hcorr hbs
        -- c == '"' (double-quoted)
        · split at hok
          · split at hok
            · simp at hok
            · rename_i s_dq hdq
              have h := Except.ok.inj hok; subst h
              obtain ⟨sp', hcorr'⟩ := scanDoubleQuoted_corr sc sp hcorr hdq
              -- simpleKey endLine update preserves corr
              split
              · exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq,
                              hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
              · exact ⟨sp', hcorr'⟩
          -- c == '\'' (single-quoted)
          · split at hok
            · split at hok
              · simp at hok
              · rename_i s_sq hsq
                have h := Except.ok.inj hok; subst h
                obtain ⟨sp', hcorr'⟩ := scanSingleQuoted_corr sc sp hcorr hsq
                split
                · exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq,
                                hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
                · exact ⟨sp', hcorr'⟩
            -- canStartPlainScalarBool (plain scalar)
            · split at hok
              · split at hok
                · simp at hok
                · rename_i s_ps hps
                  have h := Except.ok.inj hok; subst h
                  exact scanPlainScalar_corr sc sp hcorr hps
              -- error: unexpectedChar
              · simp at hok

-- Content dispatch for double-quoted: returns `SCDoubleQuoted 0 .blockIn` grammar evidence.
-- Needed for Layer 4i h_closable composition (quoted scalar → SBlockNode → stream).
-- Unfolds `scanNextToken_dispatchContent` for `c = '"'`, applies `scanDoubleQuoted_prod`,
-- and handles the simpleKey endLine update that follows.
theorem dispatchContent_doubleQuoted_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '"')
    (hok : scanNextToken_dispatchContent sc '"' = .ok s') :
    ∃ sp', SCDoubleQuoted 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  -- Skip false character checks: '&', '*', '!', '|'/'>'
  split at hok
  · rename_i h_eq; exact absurd h_eq (by decide)
  · split at hok
    · rename_i h_eq; exact absurd h_eq (by decide)
    · split at hok
      · rename_i h_eq; exact absurd h_eq (by decide)
      · split at hok
        · rename_i h_eq; exact absurd h_eq (by decide)
        · -- '"' == '"' = true: this branch
          split at hok
          · split at hok  -- bind on scanDoubleQuoted
            · simp at hok
            · rename_i s_dq hdq
              have h := Except.ok.inj hok; subst h
              obtain ⟨sp', h_gram, hcorr'⟩ :=
                scanDoubleQuoted_prod sc sp hcorr hpeek hdq
              exact ⟨sp', h_gram, by
                -- simpleKey endLine update preserves ScannerSurfCorr
                split
                · exact ⟨hcorr'.chars_from, hcorr'.col_eq,
                         hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩
                · exact hcorr'⟩
          · rename_i h_neq; exact absurd rfl h_neq

-- Content dispatch for single-quoted: returns `SCSingleQuoted 0 .blockIn` grammar evidence.
theorem dispatchContent_singleQuoted_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '\'')
    (hok : scanNextToken_dispatchContent sc '\'' = .ok s') :
    ∃ sp', SCSingleQuoted 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq; exact absurd h_eq (by decide)
  · split at hok
    · rename_i h_eq; exact absurd h_eq (by decide)
    · split at hok
      · rename_i h_eq; exact absurd h_eq (by decide)
      · split at hok
        · rename_i h_eq; exact absurd h_eq (by decide)
        · split at hok
          · rename_i h_eq; exact absurd h_eq (by decide)
          · -- '\'' == '\'' = true: this branch
            split at hok
            · split at hok  -- bind on scanSingleQuoted
              · simp at hok
              · rename_i s_sq hsq
                have h := Except.ok.inj hok; subst h
                obtain ⟨sp', h_gram, hcorr'⟩ :=
                  scanSingleQuoted_prod sc sp hcorr hpeek hsq
                exact ⟨sp', h_gram, by
                  split
                  · exact ⟨hcorr'.chars_from, hcorr'.col_eq,
                           hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩
                  · exact hcorr'⟩
            · rename_i h_neq; exact absurd rfl h_neq

-- Helper: handles all PendingNode cases for content dispatch given stream at sp_block.
theorem accum_content_pending (sc : ScannerState)
    (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream_block : SLYamlStream sp_start sp_block)
    (h_pending : PendingNode sp_start sp_block sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  obtain ⟨sp_prep, hcorr_prep⟩ :=
    scanNextToken_preprocess_corr sc sp_scan h_corr s_prep c h_preprocess
  obtain ⟨sp_scan', hcorr_result⟩ :=
    dispatchContent_corr _ sp_prep c (corr_of_allowDirectives_update hcorr_prep) h_dispatch
  cases h_pending with
  | noPending =>
    by_cases hcol : sp_block.col = 0
    · -- col = 0: can build SSeparateLines 0 and compose grammar for quoted scalars
      obtain ⟨sp_sep, h_sep, hcorr_sep⟩ :=
        preprocess_some_separate_lines_0 sc sp_block s_prep c h_corr hcol h_preprocess
      have hsp_eq := ScannerSurfCorr_unique hcorr_prep hcorr_sep; subst hsp_eq
      -- h_sep : SSeparateLines 0 sp_block sp_prep (= SSeparate 0 .flowOut)
      have hpeek : s_prep.peek? = some c := preprocess_some_peek h_preprocess
      -- Dispatch peek? preserved through allowDirectives update
      have hpeek_disp : (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep).peek? = some c := by
        split
        · show s_prep.peek? = some c; exact hpeek
        · exact hpeek
      by_cases hc_dq : c = '"'
      · -- DOUBLE-QUOTED SCALAR: full grammar composition
        subst hc_dq
        obtain ⟨sp_dq, h_dq_gram, hcorr_dq⟩ :=
          dispatchContent_doubleQuoted_prod _ sp_prep
            (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
        have hsp_dq_eq := ScannerSurfCorr_unique hcorr_dq hcorr_result
        rw [hsp_dq_eq] at h_dq_gram hcorr_dq
        -- h_dq_gram : SCDoubleQuoted 0 .blockIn sp_prep sp_scan'
        have h_flow : SFlowNode 0 .flowOut sp_prep sp_scan' :=
          SFlowNode_doubleQ_ctx_lift h_dq_gram (by decide) (by decide)
        exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
               BlockStack.nil sp_block, FlowStack.nil sp_block,
               PendingNode.pendingContent sp_start sp_block sp_scan'
                 (fun sp_mid h_ssl =>
                   have h_blockNode :=
                     flowInBlock_blockNode h_sep h_flow h_ssl
                   have h_bare := SLBareDocument.mk sp_block sp_mid h_blockNode
                   SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
                     h_stream_block (GStar.nil _)
                     (GOpt.some sp_block sp_mid
                       (SLAnyDocument.bare sp_block sp_mid h_bare))
                     (GStar.nil _)),
               hcorr_result⟩
      · by_cases hc_sq : c = '\''
        · -- SINGLE-QUOTED SCALAR: symmetric to double-quoted
          subst hc_sq
          obtain ⟨sp_sq, h_sq_gram, hcorr_sq⟩ :=
            dispatchContent_singleQuoted_prod _ sp_prep
              (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
          have hsp_sq_eq := ScannerSurfCorr_unique hcorr_sq hcorr_result
          rw [hsp_sq_eq] at h_sq_gram hcorr_sq
          have h_flow : SFlowNode 0 .flowOut sp_prep sp_scan' :=
            SFlowNode_singleQ_ctx_lift h_sq_gram (by decide) (by decide)
          exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                 BlockStack.nil sp_block, FlowStack.nil sp_block,
                 PendingNode.pendingContent sp_start sp_block sp_scan'
                   (fun sp_mid h_ssl =>
                     have h_blockNode :=
                       flowInBlock_blockNode h_sep h_flow h_ssl
                     have h_bare := SLBareDocument.mk sp_block sp_mid h_blockNode
                     SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
                       h_stream_block (GStar.nil _)
                       (GOpt.some sp_block sp_mid
                         (SLAnyDocument.bare sp_block sp_mid h_bare))
                       (GStar.nil _)),
                 hcorr_result⟩
        · -- Other content types (anchor, alias, tag, block scalar, plain scalar):
          -- grammar composition deferred to later iterations
          exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
                 BlockStack.nil sp_block, FlowStack.nil sp_block,
                 PendingNode.pendingContent sp_start sp_block sp_scan'
                   (fun sp_mid h_ssl => sorry), hcorr_result⟩
    · -- col ≠ 0: deferred (BOM edge case)
      sorry
  | pendingDocEnd =>
    rename_i h_marker_old
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_suffix : SLDocumentSuffix sp_block sp_mid :=
        SLDocumentSuffix.mk sp_block sp_scan sp_mid h_marker_old h_ssl
      have h_stream' : SLYamlStream sp_start sp_mid :=
        SLYamlStream.suffixContinue sp_start sp_block sp_mid sp_mid sp_mid sp_mid
          h_stream_block (GPlus.mk sp_block sp_mid sp_mid h_suffix (GStar.nil _))
          (GStar.nil _) (GOpt.none _) (GStar.nil _)
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream', BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             PendingNode.pendingContent sp_start sp_mid sp_scan'
               (fun sp_mid2 h_ssl => sorry), hcorr_result⟩
    · sorry
  | pendingDocStart =>
    rename_i h_doc_builder_old
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      have h_any : SLAnyDocument sp_block sp_mid :=
        h_doc_builder_old sp_mid
          (GAlt.right sp_scan sp_mid
            (GSeq.mk sp_scan sp_scan sp_mid (GEps.mk sp_scan) h_ssl))
      have h_stream' : SLYamlStream sp_start sp_mid :=
        SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
          h_stream_block (GStar.nil _) (GOpt.some sp_block sp_mid h_any) (GStar.nil _)
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan', h_stream', BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             PendingNode.pendingContent sp_start sp_mid sp_scan'
               (fun sp_mid2 h_ssl => sorry), hcorr_result⟩
    · sorry
  | pendingDirective =>
    rename_i h_dir_acc_old h_stream_old
    sorry
  | pendingContent h_closable_old
  | pendingFlow h_closable_old =>
    all_goals (
      rename_i h_closable_old
      by_cases hcol : sp_scan.col = 0
      · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
          preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
        exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
               h_closable_old sp_mid h_ssl,
               BlockStack.nil sp_mid,
               FlowStack.nil sp_mid,
               PendingNode.pendingContent sp_start sp_mid sp_scan'
                 (fun sp_mid2 h_ssl => sorry), hcorr_result⟩
      · sorry)
  | pendingBlockContent =>
    rename_i h_closable_old _
    by_cases hcol : sp_scan.col = 0
    · obtain ⟨sp_mid, _, _, h_ssl, hcol_mid, _, _, _⟩ :=
        preprocess_some_ssl_comments_col0 sc sp_scan s_prep c h_corr hcol h_preprocess
      exact ⟨sp_mid, sp_mid, sp_mid, sp_scan',
             h_closable_old sp_mid h_ssl,
             BlockStack.nil sp_mid,
             FlowStack.nil sp_mid,
             PendingNode.pendingContent sp_start sp_mid sp_scan'
               (fun sp_mid2 h_ssl => sorry), hcorr_result⟩
    · sorry
  | pendingBlock =>
    rename_i h_close_old h_close_entry_old
    -- Block entry pending: compose content INSIDE the block entry.
    -- Use general-column SSeparateLines 0 (works at any col after dash).
    obtain ⟨sp_prep', h_sep, hcorr_sep⟩ :=
      preprocess_some_separate_0_anyCol sc sp_scan s_prep c h_corr h_preprocess
    have hsp_eq := ScannerSurfCorr_unique hcorr_prep hcorr_sep; subst hsp_eq
    have hpeek : s_prep.peek? = some c := preprocess_some_peek h_preprocess
    have hpeek_disp : (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep).peek? = some c := by
      split
      · show s_prep.peek? = some c; exact hpeek
      · exact hpeek
    by_cases hc_dq : c = '"'
    · -- DOUBLE-QUOTED: compose content inside block entry
      subst hc_dq
      obtain ⟨sp_dq, h_dq_gram, hcorr_dq⟩ :=
        dispatchContent_doubleQuoted_prod _ sp_prep
          (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
      have hsp_dq_eq := ScannerSurfCorr_unique hcorr_dq hcorr_result
      rw [hsp_dq_eq] at h_dq_gram hcorr_dq
      have h_flow : SFlowNode 0 .flowOut sp_prep sp_scan' :=
        SFlowNode_doubleQ_ctx_lift h_dq_gram (by decide) (by decide)
      exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
             BlockStack.nil sp_block, FlowStack.nil sp_block,
             PendingNode.pendingBlockContent sp_start sp_block sp_scan'
               (fun sp_final h_ssl =>
                 h_close_old sp_final
                   (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_scan' sp_final
                     h_sep h_flow h_ssl))
               (fun sp_final h_ssl =>
                 h_close_entry_old sp_final
                   (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_scan' sp_final
                     h_sep h_flow h_ssl)),
             hcorr_result⟩
    · by_cases hc_sq : c = '\''
      · -- SINGLE-QUOTED: symmetric
        subst hc_sq
        obtain ⟨sp_sq, h_sq_gram, hcorr_sq⟩ :=
          dispatchContent_singleQuoted_prod _ sp_prep
            (corr_of_allowDirectives_update hcorr_prep) hpeek_disp h_dispatch
        have hsp_sq_eq := ScannerSurfCorr_unique hcorr_sq hcorr_result
        rw [hsp_sq_eq] at h_sq_gram hcorr_sq
        have h_flow : SFlowNode 0 .flowOut sp_prep sp_scan' :=
          SFlowNode_singleQ_ctx_lift h_sq_gram (by decide) (by decide)
        exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
               BlockStack.nil sp_block, FlowStack.nil sp_block,
               PendingNode.pendingBlockContent sp_start sp_block sp_scan'
                 (fun sp_final h_ssl =>
                   h_close_old sp_final
                     (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_scan' sp_final
                       h_sep h_flow h_ssl))
                 (fun sp_final h_ssl =>
                   h_close_entry_old sp_final
                     (SBlockNode.flowInBlock 0 .blockIn sp_scan sp_prep sp_scan' sp_final
                       h_sep h_flow h_ssl)),
               hcorr_result⟩
      · -- Other content: sorry (anchor, alias, tag, block scalar, plain scalar)
        exact ⟨sp_block, sp_block, sp_block, sp_scan', h_stream_block,
               BlockStack.nil sp_block, FlowStack.nil sp_block,
               PendingNode.pendingContent sp_start sp_block sp_scan'
                 (fun sp_final h_ssl => sorry), hcorr_result⟩

theorem accum_step_content (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s_prep s' : ScannerState) (c : Char)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow)
    (h_pending : PendingNode sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchContent
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) c = .ok s') :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' := by
  exact accum_content_pending sc sp_start sp_flow sp_scan s_prep s' c
    (absorb_stacks sp_start sp_gram sp_block sp_flow h_stream h_stack h_flow)
    h_pending h_corr h_preprocess h_dispatch

/-! ### §1f Composition: Per-Dispatch → Full accum_step

    Unfold `scanNextToken`, split on preprocessing and dispatch results,
    and delegate to the per-dispatch sorry lemmas above. -/

theorem scanNextToken_accum_step (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (s' : ScannerState)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow)
    (h_pending : PendingNode sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanNextToken sc = .ok (some s')) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStack sp_block' sp_flow' ∧
      PendingNode sp_start sp_flow' sp_scan' ∧
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
          exact accum_step_structural sc sp_start sp_gram sp_block sp_flow sp_scan s_pre s_str c_pre
            h_stream h_stack h_flow h_pending h_corr h_pre h_str
        · -- Past structural dispatch: allowDirectives update
          split at h_ok
          · simp at h_ok
          · -- scanNextToken_checkBlockFlowIndent — pure check, no state change
            split at h_ok
            · simp at h_ok
            · split at h_ok
              · rename_i s_flow_out h_flow_disp
                have h := Except.ok.inj h_ok; injection h with h; subst h
                exact accum_step_flow sc sp_start sp_gram sp_block sp_flow sp_scan s_pre s_flow_out c_pre
                  h_stream h_stack h_flow h_pending h_corr h_pre h_flow_disp
              · split at h_ok
                · simp at h_ok
                · split at h_ok
                  · rename_i s_blk h_blk
                    have h := Except.ok.inj h_ok; injection h with h; subst h
                    exact accum_step_block sc sp_start sp_gram sp_block sp_flow sp_scan s_pre s_blk c_pre
                      h_stream h_stack h_flow h_pending h_corr h_pre h_blk
                  · split at h_ok
                    · simp at h_ok
                    · rename_i s_cnt h_cnt
                      have h := Except.ok.inj h_ok; injection h with h; subst h
                      exact accum_step_content sc sp_start sp_gram sp_block sp_flow sp_scan s_pre s_cnt c_pre
                        h_stream h_stack h_flow h_pending h_corr h_pre h_cnt

/-! ## §2 EOF Step: scanNextToken returns none

    When `scanNextToken` returns `.ok none`, the only code path is through
    `scanNextToken_preprocess` returning `none` (EOF detected).
    All BlockStack levels are unwound and PendingNode closed. -/

theorem scanNextToken_none_stream (sc : ScannerState)
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow)
    (h_pending : PendingNode sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanNextToken sc = .ok none) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · rename_i h_pre
      exact preprocessing_eof_extends_stream sc sp_start sp_gram sp_block sp_flow sp_scan
        h_stream h_stack h_flow h_pending h_corr h_pre
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
    (sp_start sp_gram sp_block sp_flow sp_scan : SurfPos)
    (fuel : Nat) (tokens : Array (Positioned YamlToken))
    (h_stream : SLYamlStream sp_start sp_gram)
    (h_stack : BlockStack sp_gram sp_block)
    (h_flow : FlowStack sp_block sp_flow)
    (h_pending : PendingNode sp_start sp_flow sp_scan)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_ok : scanLoop sc fuel = .ok tokens) :
    ∃ sp_final : SurfPos, SLYamlStream sp_start sp_final ∧ sp_final.chars = [] := by
  induction fuel generalizing sc sp_gram sp_block sp_flow sp_scan tokens with
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
      exact scanNextToken_none_stream sc sp_start sp_gram sp_block sp_flow sp_scan
        h_stream h_stack h_flow h_pending h_corr h_none
    · -- scanNextToken = .ok (some s') → one step + recurse
      rename_i s_next h_next
      obtain ⟨sp_gram', sp_block', sp_flow', sp_scan', h_stream', h_stack', h_flow', h_pending', h_corr'⟩ :=
        scanNextToken_accum_step sc sp_start sp_gram sp_block sp_flow sp_scan s_next
          h_stream h_stack h_flow h_pending h_corr h_next
      exact ih s_next sp_gram' sp_block' sp_flow' sp_scan' tokens
        h_stream' h_stack' h_flow' h_pending' h_corr' h_ok

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
    ⟨h_init.chars_from, h_init.col_eq, h_init.end_eq, h_init.input_prefix, h_init.indent_cols_nonneg⟩
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
    exact ⟨⟨input.toList, 0⟩,
      SLYamlStream.single _ _ _ _ (GStar.nil _) (GOpt.none _) (GStar.nil _),
      h_emit⟩

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
  exact scanLoop_grammar_prod _ ⟨input.toList, 0⟩ sp sp sp sp _ tokens
    h_stream (BlockStack.nil sp) (FlowStack.nil sp) (PendingNode.noPending ⟨input.toList, 0⟩ sp) h_corr h

/-! ## §6 Gap Analysis

    Six sorry declarations remain in this file, structurally decomposed
    across the dispatch path. The lagging quint (SLYamlStream + BlockStack +
    FlowStack + PendingNode + ScannerSurfCorr) correctly models the
    multi-token protocol.

    **v0.4.9 Architecture: FlowStack (Layer 4h.1)**

    FlowStack tracks flow collection nesting between BlockStack and
    PendingNode. Position chain:
    ```
    SLYamlStream sp_start sp_gram
      → BlockStack sp_gram sp_block
        → FlowStack sp_block sp_flow
          → PendingNode sp_start sp_flow sp_scan
            → ScannerSurfCorr sc sp_scan
    ```
    `absorb_stacks` composes both stacks via h_closable (3×3 = 9 cases),
    simplifying each `accum_step_*` theorem from 3-case BlockStack split
    to a single delegation call.

    Non-trivial `PendingNode` variants carry `h_closable`:
    ```
    h_closable : ∀ sp_mid,
      SSLComments sp_scan sp_mid →
      SLYamlStream sp_start sp_mid
    ```
    The stream `SLYamlStream sp_start sp_block` is captured inside the
    closure at construction time. `sp_start` is a type index on PendingNode.
    This closure is constructed at dispatch time and consumed when the next
    preprocessing step supplies SSLComments (EOF or next token).

    **Proven branches (v0.4.9):**

    `preprocessing_eof_extends_stream` (§1a):
    - `nil + nil + noPending + col=0`: FULLY PROVEN ✅
    - `nil + nil + pendingX + col=0` (all 6 variants): PROVEN ✅ via h_closable
    - `nil + nil + noPending + col≠0`: sorry (BOM edge case)
    - `nil + nil + pendingX + col≠0`: sorry (BOM edge case)
    - `seqLevel | mapLevel` (BlockStack or FlowStack): absorbed by `absorb_stacks`

    `accum_step_structural/block/content` (§1b, §1d, §1e):
    - `absorbed + noPending`: PROVEN ✅ (stream unchanged, new PendingNode opened)
      h_closable in the new PendingNode is `sorry` — requires grammar
      composition from `_prod` theorems (see below)
    - `absorbed + pendingX + col=0` (all 6 variants): PROVEN ✅ (old pending
      closed via `preprocess_some_ssl_comments_col0` + h_closable). New
      PendingNode opened with h_closable sorry (same root cause as noPending).
    - `absorbed + pendingX + col≠0`: sorry (preprocessing SSLComments not
      available at non-zero column — flow context or BOM edge case)
    - BlockStack/FlowStack levels: absorbed by `absorb_stacks` (no case split)

    `accum_step_flow` (§1c) — character-dependent FlowStack (4h.2):
    - `absorbed + noPending + c='['`: PROVEN ✅ FlowStack.flowSeqLevel pushed,
      PendingNode.noPending (clean state inside flow). FlowStack h_closable sorry.
    - `absorbed + noPending + c='{'`: PROVEN ✅ FlowStack.flowMapLevel pushed.
    - `absorbed + noPending + other`: PROVEN ✅ FlowStack.nil, PendingNode.pendingFlow sorry.
    - `absorbed + pendingX + col=0 + c='['/'{'`: PROVEN ✅ FlowStack level pushed.
    - `absorbed + pendingX + col=0 + other`: PROVEN ✅ FlowStack.nil, PendingNode.pendingFlow sorry.
    - `absorbed + pendingX + col≠0`: sorry (same BOM root cause)

    **Sorry root causes (3 independent):**

    1. **h_closable construction** (§1b–§1e noPending): The `fun sp_mid h_ssl => sorry`
       in PendingNode construction (§1b,§1d,§1e) and `fun _ h_str => sorry` in
       FlowStack construction (§1c, for `[`/`{`). Requires `dispatchContent_prod`
       composition: scanner _prod → SFlowNode (n+1) .flowOut → SBlockNode.flowInBlock
       → stream ext via `SLYamlStream.implicitContinue` (now accepts bare documents
       via `GOpt SLAnyDocument`). Blocked on 4i: _prod theorems give
       `SFlowNode 0 .blockIn` but flowInBlock needs `SFlowNode (n+1) .flowOut`.

    2. **BOM col≠0** (§1a): SSeparateInLine requires s-white+ or start-of-line.
       After BOM at col=1 with bare break, neither applies. Genuine YAML grammar
       formalization limitation (not a proof gap).

    3. **Stack operations**: Now handled by `absorb_stacks`. Former BlockStack
       case splits (seqLevel/mapLevel) are fully absorbed — no sorry needed.

    **Dispatch _corr helpers (all PROVEN):**
    - `dispatchStructural_corr` (§1b): structural dispatch → ScannerSurfCorr
    - `dispatchFlowIndicators_corr` (§1c): flow dispatch → ScannerSurfCorr
    - `dispatchBlockIndicators_corr` (§1d): block dispatch → ScannerSurfCorr
    - `dispatchContent_corr` (§1e): content dispatch → ScannerSurfCorr
    - `corr_of_allowDirectives_update`: allowDirectives flag preservation

    **Composition chain (PROVEN):**
    - `scanNextToken_accum_step` (§1f): unfolds scanNextToken, dispatches
    - `scanNextToken_none_stream` (§2): EOF path
    - `scanLoop_grammar_prod` (§3): fuel induction with lagging quint
    - `scan_content_gives_stream_v2` (§5): top-level entry point

    **New helper (v0.4.8):**
    - `preprocess_some_ssl_comments_col0` (§0d): PROVEN ✅. Extracts
      SSLComments from `scanNextToken_preprocess` when col=0, threading
      ScannerSurfCorr through skipToContent → unwindIndents → saveSimpleKey.

    Total sorry declarations: 6 (in §1a–§1e).
    Total sorry source sites: 24 (8 in §1a + 4×4 in §1b–§1e).
    New in v0.4.7: 6 EOF pending cases at col=0 PROVEN via h_closable.
    New in v0.4.8: 24 pending-at-col=0 cases (6×4 dispatch) PROVEN for
      old-pending closure; h_closable for new PendingNode remains sorry
      (same root cause as noPending h_closable).
    New in v0.4.9: FlowStack added as 5th invariant component. absorb_stacks
      eliminates all BlockStack/FlowStack case splits (3×3 → 1 call).
      Each accum_step_* simplified from 3-case to 1-line. §3 comment
      updated: lagging quad → lagging quint.
    New in v0.4.9 (4h.2): Flow dispatch §1c now character-dependent.
      `[`/`{` push FlowStack level (flowSeqLevel/flowMapLevel with sorry
      h_closable) + PendingNode.noPending. `]`/`}`/`,` produce FlowStack.nil
      + PendingNode.pendingFlow sorry. Entry accumulation (4h.3) and flow
      finalization (4h.4) blocked on 4i (context parameter lifting).
    New in v0.4.10: SLYamlStream.implicitContinue now takes GOpt SLAnyDocument
      (matching spec [211]) instead of GOpt SLExplicitDocument. This unblocks
      bare document stream extension. PendingNode refactored to capture sp_start
      as a type index; h_closable simplified from `∀ sp_start sp_mid, SLYamlStream
      sp_start sp_block → SSLComments ... → ...` to `∀ sp_mid, SSLComments ... → ...`
      with the stream captured inside the closure at construction time.
-/

end Lean4Yaml.Proofs.StreamAccum
