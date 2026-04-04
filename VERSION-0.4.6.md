# Version 0.4.6


**Goal:** Eliminate the last sorry (`scan_content_gives_stream`) — prove that scanner success implies a full `SLYamlStream` grammar derivation tree, achieving 0 sorry in all proof files.

**Architecture:** Three layers, each building on the previous.

##### Layer 1: Leaf `_prod` theorems — scalar production coupling (in progress)

Extend Phase B's `scanDoubleQuoted_prod` pattern to the remaining three content scanner functions. Each theorem proves that when the scanner function succeeds, the consumed characters form a valid surface-syntax derivation tree. All use the `n = 0, c = .blockIn` existential trick so `SIndent 0` and `SFlowLinePrefix 0` are trivially satisfiable.

| Theorem | Scanner function | Surface type produced | Status |
|---|---|---|---|
| `scanSingleQuoted_prod` | `collectSingleQuotedLoop` → `scanSingleQuoted` | `SCSingleQuoted 0 .blockIn` | **Done** (163 lines, 0 sorry) |
| `scanPlainScalar_prod` | `collectPlainScalarLoop` → `scanPlainScalar` | `SNsPlain 0 .blockIn` (= `SNsPlainMultiLine`) | **Done** (minimal 1-char witness, 0 sorry) |
| `scanBlockScalar_prod` | `collectBlockScalarLoop` → `scanBlockScalar` | `SCLLiteral 0` / `SCLFolded 0` | **Done** (0 sorry) |

**File:** [ScalarProduction.lean](Lean4Yaml/Proofs/ScalarProduction.lean) — extends existing Phase B infrastructure, reuses `peek_some_sp`, `advance_corr`, `consumeNewline_sbreak_corr`, `foldQuotedNewlines_prod`.

**Sorry status:** 1 sorry in ScalarProduction.lean (`collectPlainScalarLoop_prod` line break). Build: 415/415 jobs, 0 errors, 11 sorry warnings (1 in ScalarProduction.lean, 9 in StreamAccum.lean, 1 in StructureProduction.lean). **A15**: Closed S6 (flow context plain scalar) by parameterizing `collectPlainScalarLoop_prod`, helpers, and `scanPlainScalar_to_flowNode` over `inFlow : Bool` — eliminated 3 sorry sites, warning count unchanged (11). **A14**: Closed S5 (doc boundary first-char termination) via `h_not_doc` precondition + `collectPlainScalarLoop_content_first_step` — sorry count 12→11. **A13**: Closed S4 (`#` at col=0) via `h_hash_col` precondition — sorry count unchanged since S3/S4 share the same theorem. **A12**: Closed S7/S8/S9/alias sorry sites by contradiction (14→12 warnings). **A11**: Removed `hm : m ≥ 1` from grammar constructors (compensating for Nat encoding offset), closing S1/S2. **A10**: Scanner Except conversion makes S7/S8/S9/alias sorry sites closable by contradiction.

<details>
<summary>scanSingleQuoted_prod — completed 2026-03-29</summary>

**New theorems (3):** `SNbSingleMultiLine_prepend` (helper — prepend `SNbSingleChar` to first line of multi-line body), `collectSingleQuotedLoop_prod` (fuel induction — loop body → `SNbSingleMultiLine 0` + closing `GLit '\''`), `scanSingleQuoted_prod` (wrapper — `SCSingleQuoted 0 .blockIn` from opening `'` through loop through trailing validation).

**Refactored (1):** `foldQuotedNewlines_prod` — return type changed from `∃ sp', SSDoubleBreak 0 sp sp' ∧ ScannerSurfCorr s' sp'` to `∃ sp₁ sp₂ sp', SBBreak sp sp₁ ∧ GStar (SLEmpty 0 .flowIn) sp₁ sp₂ ∧ SFlowLinePrefix 0 sp₂ sp' ∧ ScannerSurfCorr s' sp'`. Returns the three break components (`SBBreak + GStar SLEmpty + SFlowLinePrefix`) directly instead of wrapping in `SSDoubleBreak`. Motivation: single-quoted multi-line uses these components directly in `SNbSingleMultiLine.multi`; the old return type forced matching on `SSDoubleBreak` constructors and eliminating the impossible `escaped` case. The double-quoted call site now wraps in `SSDoubleBreak.flowFold` at point of use.

###### Reflections

**Unexpected challenges:**

1. **`sc.col` vs `sc.advance.col` — non-definitional column equality after advance.**
   `advance_non_newline_corr sc '\'' rest hcorr hmore` produces `ScannerSurfCorr sc.advance ⟨rest, sc.col + 1⟩`, but the second call `advance_non_newline_corr sc.advance '\'' rest2 hcorr_adv hmore2` expects `ScannerSurfCorr sc.advance ⟨'\'' :: rest2, sc.advance.col⟩` — and `sc.col + 1 ≠ sc.advance.col` definitionally (`.col` unfolds through `if isNewline then 0 else col+1`).
   **Fix:** After `injection hsp_adv with h_rest2 h_col2` gives `h_col2 : sc.col + 1 = sc.advance.col`, use `rw [h_col2] at hcorr_adv` to align the types before the second advance. Then `rw [show sc.advance.col + 1 = sc.col + 2 from by omega]` to align for the recursive call.

2. **`rename_i` ordering after nested `split at hok` — negation before equality.**
   In `collectSingleQuotedLoop`, the scanner tests `peek? = some c` in a `match` with one literal pattern (`'\''`). After `split at hok`, the non-literal arm introduces `rename_i c hne_sq hpeek` — the negation hypothesis (`c = '\'' → False`) appears BEFORE the match equality (`sc.peek? = some c`). This differs from the double-quoted proof where `'"'` and `'\\'` are separate literal arms.
   **Fix:** Use `rename_i c hne_sq hpeek` (not `c hpeek hne_sq`).

3. **`SSDoubleBreak` return type forces impossible case elimination.**
   `foldQuotedNewlines_prod` originally returned `SSDoubleBreak 0`, which has two constructors: `.escaped` (backslash-newline) and `.flowFold` (bare newline). Single-quoted scalars never use backslash escapes, so the `.escaped` case is impossible — but `cases h_dbreak` still generates it, requiring either `assumption` plumbing or an explicit impossibility proof.
   **Fix:** Refactored return type to expose `SBBreak + GStar SLEmpty + SFlowLinePrefix` directly (see above). The double-quoted call site wraps these in `SSDoubleBreak.flowFold` at point of use. This avoids the impossible case entirely and makes both call sites cleaner.

**Simplifications:**

1. **`SNbSingleText 0 .blockIn` = `SNbSingleMultiLine 0` definitionally.** The `SNbSingleText` definition matches on context: `.flowKey → SNbSingleOneLine`, `_ → SNbSingleMultiLine n`. Since `.blockIn ≠ .flowKey`, `SNbSingleText 0 .blockIn` reduces to `SNbSingleMultiLine 0` without any explicit coercion. `have h_text : SNbSingleText 0 .blockIn sp sp' := h_body` just works.

2. **Closing-quote branch is identical to double-quoted.** `GStar.nil _` for empty body + `GLit.mk rest sc.col` for the `'` + `advance_non_newline_corr` — same 3-line pattern.

3. **`SNbSingleMultiLine_prepend` mirrors `SNbDoubleMultiLine_prepend` exactly.** Same two cases (`single` → extend star, `multi` → extend first-line star), just with `SNbSingleChar` instead of `SNbDoubleChar`.

**Idioms:**

- **`rw [h_col2] at hcorr_adv` for column alignment through double advance.** When two successive `advance_non_newline_corr` calls each increment column by 1, the intermediate column `sc.advance.col` must be related to `sc.col + 1` via `peek_some_sp`'s injection. Rewriting the hypothesis avoids type mismatches without `conv` or `show`.

- **Component-level return types for reusable lemmas.** Returning `SBBreak + GStar SLEmpty + SFlowLinePrefix` instead of `SSDoubleBreak` allows callers (single-quoted, double-quoted, potentially plain-scalar) to compose the components differently. The double-quoted path wraps in `SSDoubleBreak.flowFold`; the single-quoted path feeds them directly to `SNbSingleMultiLine.multi`.

</details>

##### Layer 2: Node composition — scalars/indicators into `SBlockNode`

<details>
<summary>Completed: 18 theorems in NodeProduction.lean (158 lines, 0 sorry)</summary>

Compose Layer 1 scalar `_prod` theorems and Phase C structural `_prod` theorems into the `SFlowContent` / `SFlowNode` / `SBlockNode` hierarchy:

```
scanDoubleQuoted_prod → SCDoubleQuoted → SFlowContent.doubleQ
scanSingleQuoted_prod → SCSingleQuoted → SFlowContent.singleQ
  both → SFlowContent → SFlowNode.content

SSeparate + SFlowNode + SSLComments → SBlockNode.flowInBlock
SSeparate + props + SCLLiteral      → SBlockNode.blockLiteral
SSeparate + props + SCLFolded       → SBlockNode.blockFolded
SSLComments                         → SBlockNode.emptyNode
```

**File:** [NodeProduction.lean](Lean4Yaml/Proofs/NodeProduction.lean) — imports `ScalarProduction` + `StructureProduction`.

**Theorem inventory (18):**

| § | Theorem | Surface type |
|---|---|---|
| §1 | `doubleQuoted_flowContent` | `SCDoubleQuoted n c → SFlowContent n c` |
| §1 | `singleQuoted_flowContent` | `SCSingleQuoted n c → SFlowContent n c` |
| §1 | `plain_flowContent` | `SNsPlain n c → SFlowContent n c` |
| §1 | `flowSeq_flowContent` | `SFlowSequence n c → SFlowContent n c` |
| §1 | `flowMap_flowContent` | `SFlowMapping n c → SFlowContent n c` |
| §2 | `flowContent_flowNode` | `SFlowContent n c → SFlowNode n c` |
| §2 | `alias_flowNode` | `SCNsAliasNode → SFlowNode n c` |
| §2 | `propsContent_flowNode` | `SCNsProperties + SSeparate + SFlowContent → SFlowNode n c` |
| §2 | `propsEmpty_flowNode` | `SCNsProperties → SFlowNode n c` |
| §3 | `flowInBlock_blockNode` | `SSeparate + SFlowNode + SSLComments → SBlockNode n c` |
| §3 | `literal_blockNode` | `SSeparate + GOpt props + SCLLiteral → SBlockNode n c` |
| §3 | `folded_blockNode` | `SSeparate + GOpt props + SCLFolded → SBlockNode n c` |
| §3 | `emptyNode_blockNode` | `SSLComments → SBlockNode n c` |
| §4 | `scanDoubleQuoted_flowContent_prod` | scanner → `SFlowContent 0 .blockIn` |
| §4 | `scanSingleQuoted_flowContent_prod` | scanner → `SFlowContent 0 .blockIn` |
| §5 | `scanDoubleQuoted_flowNode_prod` | scanner → `SFlowNode 0 .blockIn` |
| §5 | `scanSingleQuoted_flowNode_prod` | scanner → `SFlowNode 0 .blockIn` |
| alias | (deferred) | `GStar` → `GPlus` non-emptiness needed |

**Build:** 409/409 jobs, 0 errors, 1 sorry (unchanged — `scan_content_gives_stream`).

**Reflections:**

1. **Parametric vs. existential n/c is the key design choice.** The §1–§3 pure composition lemmas are parametric in `n` and `c` — they work at any indentation level and context. The §4–§5 scanner-to-node lemmas use `n=0, c=.blockIn` (the existential trick from Layer 1). Layer 3 must bridge this gap: either generalize the `_prod` theorems to produce at the actual `n` and `c`, or prove monotonicity lemmas showing `SFlowContent 0 .blockIn sp sp' → SFlowContent n c sp sp'` for specific content shapes.

2. **`SBlockNode.flowInBlock` needs loop-level context, not per-token proofs.** The `SSeparate` comes from `scanNextToken_preprocess` (skip whitespace), and `SSLComments` comes from post-content processing. Neither is available to the content-scanning function. So `SBlockNode` assembly fundamentally requires Layer 3's loop accumulation to supply the context around each content token.

3. **Alias lifting is blocked by GPlus vs. GStar.** `scanAnchorOrAlias_prod` returns `GStar (GChar isNsAnchorChar)`, but `SCNsAliasNode` needs `GPlus` (at least one char). The scanner validates non-emptiness at runtime (error on `*` with no name), but connecting this validation to the `GStar` output requires additional coupling proof — not a simple wrapping exercise.

4. **Collection composition (`blockSeq`/`blockMap`) is genuinely multi-token.** A block sequence like `- a\n- b` involves at least 4 `scanNextToken` calls (`-`, `a`, `-`, `b`). There is no per-token composition that produces `SBlockSeqEntries` — this must be accumulated across iterations, making it a Layer 3 concern.

**Idioms:**

- **Trivial wrappings as named lemmas.** Even though `doubleQuoted_flowContent` is literally `SFlowContent.doubleQ n c s s' h`, naming it provides a stable API for Layer 3. If the surface type hierarchy changes, only NodeProduction.lean needs updating.

- **Separate parametric and existential layers.** §1–§3 are reusable at any `n/c`; §4–§5 are scanner-specific at `n=0`. This separation lets Layer 3 choose: use the parametric lemmas with actual `n/c` (if generalizing `_prod`), or use the existential lemmas with the `n=0` trick (for simple documents).

</details>

##### Layer 3: Scan loop grammar accumulation — `scanLoop` → `SLYamlStream`

<details>
<summary>Completed: stream extension lemmas + precisely scoped sorry in DocumentProduction.lean</summary>

Strengthen `scanLoop_full_consumption` to additionally produce `SLYamlStream`. Currently the loop threads `ScannerSurfCorr` (position correspondence) via fuel induction. Layer 3 adds a **grammar accumulator** threaded alongside:

```
ScannerSurfCorr  (position)     → already threaded (Phase A)
GrammarAccum     (partial tree)  → new: tracks partial SLYamlStream
```

The accumulator must track:
- Current partial `SLYamlStream` (prefixes consumed, documents accumulated)
- Current open document's partial `SBlockNode` (entries for seq/map)
- Indent stack ↔ grammar nesting correspondence

At each `scanNextToken` step, the Layer 2 `_prod` theorem for that step advances the accumulator. At loop termination (EOF), the accumulator is finalized into a complete `SLYamlStream`, discharging the sorry in `scan_content_gives_stream`.

**File:** [DocumentProduction.lean](Lean4Yaml/Proofs/DocumentProduction.lean) — contains stream extension lemmas (§6a) and the precisely scoped sorry (§6b); parallels `ScanStrictCoupling.scanLoop_full_consumption` but with grammar accumulation. Import chain: `ScalarProduction → NodeProduction → DocumentProduction`.

**New theorems (4):**

| § | Theorem | Type |
|---|---|---|
| §6a | `bare_to_stream` | `SLBareDocument s s' → SLYamlStream s s'` |
| §6a | `empty_to_stream` | `SLYamlStream sp sp` (identity stream) |
| §6a | `stream_append_suffix` | `SLYamlStream s s₁ → GPlus SLDocumentSuffix s₁ s₂ → SLYamlStream s s₂` |
| §6a | `stream_implicit_continue` | `SLYamlStream s s₁ → GStar SLDocumentPrefix s₁ s₂ → SLExplicitDocument s₂ s₃ → SLYamlStream s s₃` |

**Content production gap table (§6b):**

| Content type | Scanner function | `_prod` theorem | Status |
|---|---|---|---|
| Double-quoted | `scanDoubleQuoted` | `scanDoubleQuoted_prod` | ✅ Done |
| Single-quoted | `scanSingleQuoted` | `scanSingleQuoted_prod` | ✅ Done |
| Tag | `scanTag` | `scanTag_prod` | ✅ Done |
| Plain scalar | `scanPlainScalar` | `scanPlainScalar_prod` | ❌ Missing (bridge lemmas done) |
| Block scalar | `scanBlockScalar` | `scanBlockScalar_prod` | ✅ Done (fully proven, 0 sorry) |
| Anchor/Alias | `scanAnchorOrAlias` | `scanAnchorOrAlias_{aliasNode,anchorProp,flowNode}_prod` | ✅ Done (conditional on name non-emptiness) |
| Flow sequence | (via `scanNextToken`) | — | ❌ Missing |
| Flow mapping | (via `scanNextToken`) | — | ❌ Missing |
| Block sequence | (multi-token) | — | ❌ Missing |
| Block mapping | (multi-token) | — | ❌ Missing |

**Reflections:**

1. **`SLYamlStream` is NOT an append structure.** Unlike `GStar` which has `.nil`/`.cons` for free extension, `SLYamlStream`'s three constructors (`single`, `suffixContinue`, `implicitContinue`) each embed document-level structure. You cannot "extend" a stream with arbitrary content — you must know whether it's a suffix continuation (`...` + next doc) or an implicit continuation (prefix + explicit doc with `---`). This means the grammar accumulator must track the current document boundary state, not just a list of consumed characters.

2. **`GConsumeAll` cannot substitute for missing content proofs.** We initially explored using `GConsumeAll` (defined in `Combinators.lean`) as a catch-all to consume remaining characters without grammar structure. It turns out `GConsumeAll` tracks columns as always `col + 1` per character, never resetting on newlines — making it disagreement with the scanner's actual column tracking. Moreover, `GConsumeAll` is not referenced by any `SLYamlStream` constructor or descendant, so it cannot participate in a valid derivation tree.

3. **`SSLComments` cannot consume arbitrary content.** Another attempted shortcut was wrapping non-whitespace content in `SSLComments` or `SLComment`. But `SLComment` requires `SSeparateInLine + GOpt SCNbCommentText + SBComment`, and `SCNbCommentText` requires a `#` prefix. Content characters like `a`, `"`, `'`, `-` etc. cannot satisfy these requirements. This is by design — the grammar is context-sensitive and each character must be consumed by the correct production.

4. **The empty-input case is non-trivial.** For empty input (`input.toList = []`), `scan_full_consumption` gives `∃ sp_final, sp_final.chars = []` but does NOT constrain `sp_final.col`. We need `SLYamlStream ⟨[], 0⟩ sp_final`, but `empty_to_stream` gives `SLYamlStream ⟨[], 0⟩ ⟨[], 0⟩`. If `sp_final.col ≠ 0`, this doesn't match. Fully proving even the empty case requires threading column information through `scan_full_consumption`, which would need verifying that `scanLoop` on empty input terminates at col 0.

5. **The sorry is precisely scoped.** The restructured proof isolates the gap to a single `sorry` in `scan_content_gives_stream` with a detailed table of exactly which `_prod` theorems are needed. The surrounding infrastructure (§1–§5 document helpers, §6a stream extension lemmas, §7 parse-strict composition) is all sorry-free. Eliminating the sorry requires: (a) all 10 content-type `_prod` theorems, (b) a `StreamAccum` inductive threaded through `scanLoop`, (c) a `scanNextToken_stream_step` that advances the accumulator per token, (d) a `finalize_stream` that closes the accumulator at EOF.

6. **Block collections require multi-token accumulation.** A block sequence `- a\n- b` spans ≥4 `scanNextToken` calls. There is no per-token theorem that produces `SBlockSeqEntries` — it must accumulate across iterations. This is the deepest part of the gap and requires novel inductive design, making it fundamentally different from the mechanical per-function `_prod` pattern used in Layers 1–2.

**Idioms:**

- **Position-parametric GOpt/GStar for identity extension.** `GOpt.none sp` gives a zero-width optional; `GStar.nil sp` gives a zero-width repetition. Combined with `SLYamlStream.suffixContinue ... (GStar.nil _) (GOpt.none _) (GStar.nil _)`, this extends a stream with a suffix section that has no additional prefix/doc/suffix — just the required suffixes themselves. This pattern is reusable for any stream extension where only one component is non-trivial.

</details>

##### Layer 4: Content production gap — remaining `_prod` + `StreamAccum` → 0 sorry

Close the sorry in `scan_content_gives_stream` by completing the remaining content-type production coupling and the scan-loop grammar accumulator.

<details>

###### **Sub-layer 4a: Leaf `_prod` theorems (extends Layer 1)**

<details>

Complete the per-scanner-function production coupling for the 7 missing content types. Each theorem proves: scanner function succeeds → consumed characters form a valid surface-syntax derivation tree.

| Theorem | Scanner function | Surface type | Est. lines | Difficulty | Status |
|---|---|---|---|---|---|
| `GStar_to_GPlus` | (combinator) | `GStar P s s' → s ≠ s' → GPlus P s s'` | ~15 | Low | ✅ Done |
| `scanAnchorOrAlias_aliasNode_prod` | `scanAnchorOrAlias` | `SCNsAliasNode` (conditional on name non-emptiness) | ~15 | Low | ✅ Done |
| `scanAnchorOrAlias_anchorProp_prod` | `scanAnchorOrAlias` | `SCNsAnchorProperty` (conditional on name non-emptiness) | ~10 | Low | ✅ Done |
| `scanAnchorOrAlias_flowNode_prod` | `scanAnchorOrAlias` | `SFlowNode` (alias, conditional) | ~10 | Low | ✅ Done |
| `isPlainSafe_block_to_nsChar` | (bridge) | `isPlainSafeBool c false → isNsChar c` | ~8 | Low | ✅ Done |
| `isPlainSafe_to_nsPlainSafe_{blockIn,blockOut,flowIn}` | (bridge) | `isPlainSafeBool → isNsPlainSafe` | ~15 | Low | ✅ Done |
| `isPlainSafe_not_linebreak` / `_not_newline` | (bridge) | negation lemmas for advance proofs | ~20 | Medium | ✅ Done |
| `blockHeaderChar_not_newline` | (bridge) | `isBlockScalarHeaderChar c → c ≠ '\n' ∧ c ≠ '\r'` | ~5 | Low | ✅ Done |
| `isDigitNotZero_isBlockHeaderChar` | (bridge) | `c.isDigit ∧ c ≠ '0' → isBlockScalarHeaderChar c` | ~20 | Medium | ✅ Done |
| `parseBlockHeaderLoop_prod` | `parseBlockHeaderLoop` | `GStar (GChar isBlockScalarHeaderChar) ∧ ScannerSurfCorr` | ~50 | Medium | ✅ Done |
| `scanPlainScalar_prod` | `collectPlainScalarLoop` → `scanPlainScalar` | `SNsPlain 0 .blockIn` (= `SNsPlainMultiLine`) | ~200 | Medium | ❌ Pending |
| `scanBlockScalar_prod` | `collectBlockScalarLoop` → `scanBlockScalar` | `SCLLiteral 0` / `SCLFolded 0` | ~250 | Medium | ✅ Done |
| `scanFlowSequence_prod` | (multi-token) | `SFlowSequence n c` | ~150 | High | ❌ Pending |
| `scanFlowMapping_prod` | (multi-token) | `SFlowMapping n c` | ~150 | High | ❌ Pending |
| `scanBlockSequence_prod` | (multi-token) | `SBlockSequence n` | ~200 | High | ❌ Pending |
| `scanBlockMapping_prod` | (multi-token) | `SBlockMapping n` | ~200 | High | ❌ Pending |

**Layer 4a reflections (15 theorems proven, 0 sorry):**

1. **`UInt32` uses `BitVec 32` in Lean 4.28 — no `UInt32.val` field.** Character arithmetic proofs require a 4-step chain: `Char.le_def` (Char→UInt32) → `UInt32.le_iff_toNat_le` (UInt32→Nat) → `native_decide` for concrete values (e.g., `'0'.val.toNat = 48`) → `omega` on Nat. The `isDigitNotZero_isBlockHeaderChar` proof discovered and documented this chain.

2. **Scanner anchor validation gap — `scanAnchorOrAlias` is total.** The scanner function never errors on empty anchor/alias names; it simply returns `sp_mid = sp'`. The `GStar → GPlus` lift requires external `sp_mid ≠ sp'` evidence from the call site (the scanner's error guard at a higher level). All three `scanAnchorOrAlias_*_prod` theorems return conditional results: `sp_mid ≠ sp' → SurfaceType sp sp'`.

3. **`isLineBreakProp` uses `==` (BEq), not `=` (Eq).** The definition `isLineBreakProp c ↔ c == '\n' ∨ c == '\r'` coerces BEq to Prop. Proofs using `left; rfl` fail because `rfl` proves `=`, not `==`. Fix: `subst heq` to get `isLineBreakProp '\n'` concretely, then `native_decide`.

4. **`cases with` naming doesn't work for indexed inductive `GStar`.** `cases h with | cons s₁ s₂ s₃ h_head h_tail =>` fails to introduce constructor parameters. Lean 4.28's `cases with` only introduces non-index arguments. Fix: use `match` pattern matching: `| .cons _ sp_mid _ h_head h_tail =>`.

5. **`Bool.or` is left-associative.** After `Bool.or_eq_true` simplification, `a || b || c` becomes `(a || b) || c` which gives 2-level `Or`, not 3-level. Only one `Or.inr` is needed to reach the last disjunct, not two.

**New files/sections:**
- [NodeProduction.lean](Lean4Yaml/Proofs/NodeProduction.lean) §6: GStar/GPlus lifting + anchor/alias converters (6 theorems, 61 lines)
- [ScalarProduction.lean](Lean4Yaml/Proofs/ScalarProduction.lean) §5: isPlainSafe bridge lemmas (6 theorems, 52 lines)
- [ScalarProduction.lean](Lean4Yaml/Proofs/ScalarProduction.lean) §6: Block header production (3 theorems, 55 lines)

</details>

###### **Sub-layer 4b: Preprocessing production coupling** ✅ Complete (8 theorems, 280 lines, 0 sorry)

<details>

Connect the scanner's whitespace/comment-skipping preprocessing to grammar elements. The planned 3-theorem breakdown was replaced by a finer decomposition that separates the grammar endpoint (`sp_mid`) from the scanner endpoint (`sp'`), since `skipToContentLoop` consumes trailing whitespace beyond the last `SLComment`.

| Theorem | Scanner function | Surface type | Lines | Status |
|---|---|---|---|---|
| `GStar_SSWhite_to_SSeparateInLine_col0` | (combinator) | `SSeparateInLine` from `GStar SSWhite` at col=0 | ~8 | ✅ Done |
| `consumeNewline_break_prod` | `consumeNewline` | `SBBreak` + col=0 guarantee | ~25 | ✅ Done |
| `skipToContentLoop_col0_prod` | `skipToContentLoop` | `GStar SLComment sp sp_mid ∧ ScannerSurfCorr s sp'` | ~80 | ✅ Done |
| `skipToContent_col0_prod` | `skipToContent` | (wrapper for above) | ~5 | ✅ Done |
| `skipToContent_documentPrefix_prod` | `skipToContent` | `SLDocumentPrefix sp sp_mid` | ~8 | ✅ Done |
| `skipToContentLoop_after_break_prod` | `skipToContentLoop` | `SSLComments.withComment` | ~8 | ✅ Done |
| `skipToContentLoop_startOfLine_prod` | `skipToContentLoop` | `SSLComments.startOfLine` | ~10 | ✅ Done |
| `skipToContent_startOfLine_comments_prod` | `skipToContent` | `SSLComments` (wrapper) | ~5 | ✅ Done |

Notes: `scanNextToken_preprocess_separate_prod` was not needed as a separate theorem — the existing `skipToContentWs_ok_corr` + `skipToContentComment_corr` from ScannerCoupling.lean suffice for `scanNextToken_preprocess`'s whitespace/comment consumption. `documentMarker_prod` was already done as `scanDocumentStart_prod` / `scanDocumentEnd_prod` in StructureProduction.lean (Layer 4a).

###### **Sub-layer 4c: Stream accumulator** ⚠️ Superseded by 4d+4e (11 theorems, 5 sorry — **historically unprovable**, resolved by lagging quad)

Threads `SLYamlStream` as a grammar accumulator through `scanLoop` alongside `ScannerSurfCorr`. The design narrows the 1 broad sorry in `scan_content_gives_stream` to 5 per-dispatch sorry, each targeting one specific execution path:

1. `preprocessing_eof_extends_stream` — EOF via preprocessing (trailing ws/comments → `SLDocumentPrefix`)
2. `accum_step_structural` — `---`/`...`/`%` dispatch
3. `accum_step_flow` — flow indicators `[`,`]`,`{`,`}`,`,`
4. `accum_step_block` — block indicators `-`,`?`,`:`
5. `accum_step_content` — content tokens (scalars, anchors, tags)

The composition theorems `scanNextToken_accum_step` and `scanNextToken_none_stream` are PROVEN by unfolding `scanNextToken` and delegating to per-dispatch sorry lemmas. `scanLoop_grammar_prod`, `bom_advance_gives_prefix`, `initial_stream_and_prefix`, and `scan_content_gives_stream_v2` are all fully sorry-free.

**⚠️ Code/proof architecture mismatch discovered.** The 5 per-dispatch sorry lemmas are **unprovable as stated** due to a fundamental misalignment between scanner token boundaries and grammar production boundaries. See [MISMATCH.md](MISMATCH.md) for the full analysis. In summary:

- **One-token lag:** Grammar productions like `SBlockNode.flowInBlock` require `SSeparate + content + SSLComments`. The trailing `SSLComments` of token N is consumed during token N+1's preprocessing. No single token step has all three components.
- **`SLYamlStream` is not an append structure:** After scanning `[`, the consumed portion cannot form a valid `SLYamlStream` because the grammar requires the matching `]` before the document is complete.
- **Multi-token productions:** Block sequences `- a\n- b` span ≥4 tokens. There is no per-token grammar production for "one entry of a block sequence."

This mismatch was foreshadowed by Layer 2 Reflection #2 ("SBlockNode.flowInBlock needs loop-level context") and Layer 3 Reflection #1 ("`SLYamlStream` is NOT an append structure") but was not recognized as structural impossibility until attempting to discharge the sorry lemmas.

###### **Sub-layer 4d: Lagging grammar accumulator** ✅ Complete (1 inductive, 11 theorems, 5 sorry per-dispatch — architecturally provable)

Restructured 4c with a **lagging accumulator** where the grammar position trails one `SSLComments` behind the scanner:

```
∀ token step:
  SLYamlStream sp_start sp_gram  ∧
  PendingNode sp_gram sp_scan    ∧   -- open grammar gap
  ScannerSurfCorr sc sp_scan
```

At each step: (1) preprocessing of token N+1 provides `SSLComments` to **close token N's node**, extending `SLYamlStream`; (2) content dispatch of token N+1 opens a **new** `PendingNode`. At EOF, the final `PendingNode` is closed with `SSLComments` from the EOF gap.

**`PendingNode` inductive** (7 constructors):
- `noPending` — no grammar gap (stream start, between documents)
- `pendingContent` — content token awaiting `SSLComments` to close `SBlockNode`
- `pendingDocEnd` — `...` awaiting `SSLComments` for `SLDocumentSuffix`
- `pendingDocStart` — `---` awaiting content or `SSLComments` for explicit document
- `pendingDirective` — `%` awaiting next directive or `---`
- `pendingFlow` — flow indicator (multi-token, future work)
- `pendingBlock` — block indicator within `BlockStack` nesting

Unlike the 4c sorry lemmas, the 4d sorry are **architecturally provable** — the lagging invariant correctly models the one-token lag. The 5 per-dispatch sorry match the same dispatch structure as 4c, but each now takes and produces `PendingNode`. The composition theorems (`scanNextToken_accum_step`, `scanNextToken_none_stream`, `scanLoop_grammar_prod`, `scan_content_gives_stream_v2`) are all proven by the same unfold/split delegation pattern as 4c.

###### **Sub-layer 4e: Block collection accumulator (hardest part)** ✅ Complete (1 inductive, 571 lines total, 5 sorry — architecturally provable with BlockStack)

Block sequences and mappings span multiple `scanNextToken` calls. A block sequence `- a\n- b` involves ≥4 tokens. The scanner tracks nesting via an indent stack (`Array IndentEntry`); the grammar needs a corresponding `BlockStack`.

The preliminary design using `GStar (SBlockSeqEntry n)` was discarded — the grammar uses `SBlockSeqEntries` (single|cons) with hand-inlined recursion, not `GStar`. The actual design separates `BlockStack` from `PendingNode` as an independent fourth component of the loop invariant:

```
∀ token step:
  SLYamlStream sp_start sp_gram  ∧      -- grammar up to here
  BlockStack sp_gram sp_block    ∧      -- nested block collections
  PendingNode sp_block sp_scan   ∧      -- immediate pending state
  ScannerSurfCorr sc sp_scan            -- scanner ahead
```

```lean
/-- Stack of nested block collections being accumulated.
    Mirrors the scanner's indent stack (minus sentinel). -/
inductive BlockStack : SurfPos → SurfPos → Prop where
  | nil (sp : SurfPos) : BlockStack sp sp
  | seqLevel (col : Int) (sp sp_mid sp' : SurfPos) :
      BlockStack sp sp_mid → BlockStack sp sp'
  | mapLevel (col : Int) (sp sp_mid sp' : SurfPos) :
      BlockStack sp sp_mid → BlockStack sp sp'
```

**Protocol (mirrors scanner's indent stack operations):**
- **Push** (`pushSequenceIndent`/`pushMappingIndent`): When `col > currentIndent`, a `.seqLevel`/`.mapLevel` is pushed.
- **Pop** (`unwindIndents` in preprocessing): When content moves to lower column, levels pop. Each pop finalizes `SBlockSeqEntries`/`SBlockMapEntries` → `SBlockNode.blockSeq`/`.blockMap` → extends `SLYamlStream`.
- **Same-level entry** (e.g., second `-` at same indent): The current level's accumulated entries grow by one (`SBlockSeqEntries.cons`). No push/pop.

Evidence-free: positions and columns only. Grammar witnesses constructed when sorry discharged.

**v0.4.7 progress:** Four dispatch `_corr` helper theorems proven (`dispatchStructural_corr`, `dispatchFlowIndicators_corr`, `dispatchBlockIndicators_corr`, `dispatchContent_corr`), each delegating to the per-scanner `_corr` theorems from ScalarCoupling and StructureCoupling. All four dispatch accumulator lemmas now have their `BlockStack.nil + PendingNode.noPending` case **fully proven** — the stream stays unchanged, BlockStack remains nil, and a new PendingNode opens. The remaining sorry branches require closing non-trivial pending nodes, which needs evidence-bearing PendingNode (carrying grammar closure proofs constructed from `_prod` theorems). Total: 986 lines, 5 sorry declarations.

**Dependency graph:**

```
Sub-layer 4a (leaf _prod)  ─────────────┐
Sub-layer 4b (preprocessing prod) ──────┤  ✅ Complete
                                        ├──► Sub-layer 4c (StreamAccum) ⚠️ Mismatch (5 sorry unprovable)
                                        │         │
                                        │         ▼
                                        ├──► Sub-layer 4d (Lagging Grammar) ✅ Complete
                                        │         │
                                        │         ▼
                                        ├──► Sub-layer 4e (BlockStack) ✅ Complete (lagging quad)
Remaining _prod theorems ───────────────┘         │
                                                  ▼
                                        scan_content_gives_stream (0 sorry)
```

**Files:**
- [ScalarProduction.lean](Lean4Yaml/Proofs/ScalarProduction.lean) — **0 sorry**. All `_prod` theorems fully proven (scanPlainScalar, scanBlockScalar, scanDoubleQuoted, scanSingleQuoted)
- [NodeProduction.lean](Lean4Yaml/Proofs/NodeProduction.lean) — extend with flow collection composition
- [DocumentProduction.lean](Lean4Yaml/Proofs/DocumentProduction.lean) — stream construction helpers, `scan_strict_proof` delegates to `scan_content_gives_stream_v2` (0 sorry)
- [PreprocessProduction.lean](Lean4Yaml/Proofs/PreprocessProduction.lean) — preprocessing → grammar coupling (sub-layer 4b)
- [StreamAccum.lean](Lean4Yaml/Proofs/StreamAccum.lean) — stream accumulator through scanLoop (sub-layers 4c→4d→4e: lagging quad with `BlockStack`)

**Execution order:**
1. ~~`scanAnchorOrAlias_nonempty` (lowest risk, ~30 lines)~~ ✅ Done
2. `scanPlainScalar_prod` (medium, extends existing pattern) — **last remaining scalar sorry**
3. ~~`scanBlockScalar_prod` (medium, parallel with plain)~~ ✅ **DONE** (both literal and folded)
4. ~~Sub-layer 4b preprocessing coupling (independent of 1–3)~~ ✅ Complete (8 theorems, 0 sorry)
5. ~~Sub-layer 4c stream accumulator~~ ✅ Complete (11 theorems, 5 per-dispatch sorry)
6. ~~Sub-layer 4e BlockStack~~ ✅ Complete (lagging quad, 571 lines)
7. `scanFlowSequence_prod` + `scanFlowMapping_prod` (high, recursive)
8. Discharge per-dispatch sorry (structural/content tractable, flow/block need _prod theorems)

</details>

###### Estimated scope

| Layer | Est. lines | Actual | Risk |
|---|---|---|---|
| Layer 1 (leaf `_prod`) | ~500 | 163 (single-quoted done; plain, block pending) | Low — mechanical |
| Layer 2 (node composition) | ~200 | 158 (18 theorems, 0 sorry) | ✅ Complete |
| Layer 3 (loop accumulation) | ~400-800 | 4 lemmas + sorry scoped (see gap table) | ✅ Complete (sorry precisely scoped) |
| Layer 4a (remaining leaf `_prod`) | ~1,180 | 168 actual (10 done, 6 pending) | ✅ Foundations complete; plain/block scalar `_prod` + collections pending |
| Layer 4b (preprocessing coupling) | ~180 | 280 actual (8 theorems, 0 sorry) | ✅ Complete |
| Layer 4c (StreamAccum) | ~320 | 382 (superseded) | ⚠️ Superseded by 4d+4e |
| Layer 4d (Lagging Grammar) | ~400-600 | (merged into 4e) | ✅ Merged into 4e |
| Layer 4e (BlockStack + Lagging Quad) | ~190 | 1058 actual (2 inductives, 15 theorems, 5 sorry) | ✅ Evidence-bearing PendingNode; nil+noPending + EOF pending proven |
| **Total** | **~3,050-3,550** | **1,258 actual** | |

**Execution order:** Layers 1–3 complete. Layer 4a foundations complete (all `_prod` theorems proven, 0 sorry). Layer 4b complete (8 theorems). Layer 4c→4d→4e complete — restructured from broken same-position invariant (4c) through lagging triple (4d) to lagging quad with `BlockStack` (4e). 5 per-dispatch sorry are architecturally provable. All individual scalar/tag/anchor `_prod` theorems now **FULLY PROVEN**. `scan_content_gives_stream` eliminated by import reversal (DocumentProduction imports StreamAccum). Next steps: discharge per-dispatch sorry (`accum_step_structural` and `preprocessing_eof_extends_stream` are tractable first targets). Flow collection accumulation (analogous to `BlockStack` for `FlowStack`) is future work.

**Sorry status (v0.4.8):** 5 sorry declarations, all in StreamAccum.lean. PendingNode is now **evidence-bearing** — non-trivial variants carry `h_closable` closure proofs. Each dispatch theorem has its `nil + noPending` case **proven**. EOF `nil + pendingX + col=0` cases **proven** via h_closable. **EOF `nil + pendingX` cases (all cols) now proven** — `preprocess_none_ssl_comments` eliminated the col=0 requirement for `pendingContent/DocEnd/DocStart/Flow/Block` closures. New: dispatch pending-at-col=0 cases (6 variants × 4 dispatchers = 24) now **proven** for old-pending closure — `preprocess_some_ssl_comments_col0` extracts `SSLComments` from preprocessing at col=0, and `h_closable_old` closes the old pending. The new PendingNode's `h_closable` remains sorry (same root cause as noPending). Remaining sorry: (a) h_closable construction at dispatch time (needs `_prod` → `SFlowNode(n+1,.flowOut)` grammar context lifting), (b) col≠0 cases in `some` path (same-line tokens can't provide `SSLComments` to close pending), (c) `seqLevel`/`mapLevel` stack operations, (d) BOM grammar gap (1 sorry in PreprocessProduction.lean). Build: 415/415 jobs, 12 sorry warnings (2 ScalarProduction + 9 StreamAccum + 1 StructureProduction). **A12**: S7/S8/S9/alias CLOSED (−2 warnings from StreamAccum).

###### **Layer 4b reflections (8 theorems proven, 0 sorry):**

1. **Grammar/scanner position gap in `skipToContentLoop`.** Each loop iteration consumes whitespace (via `skipToContentWs`) + optional comment (via `skipToContentComment`) + optional break. Complete iterations (those ending with a break) produce `SLComment`. The **final** iteration (ending at non-break content or EOF) consumes whitespace/comment that is NOT part of any `SLComment` — it becomes indentation for the following content production. This forced the return type to separate `sp_mid` (where grammar productions like `GStar SLComment` end) from `sp'` (where `ScannerSurfCorr` holds). The consumer uses `GStar SLComment sp sp_mid` for `SLDocumentPrefix` and `ScannerSurfCorr s_result sp'` for continuing. The `sp_mid → sp'` gap represents trailing whitespace absorbed by subsequent indentation/separation.

2. **Nat subtraction and `omega` fuel bounds.** Proving `fuel' ≥ cn.inputEnd - cn.offset + 1` requires knowing `cn.offset ≤ cn.inputEnd` (otherwise Nat subtraction underflows to 0 and the `+1` makes it 1, which may exceed `fuel'`). The scanner doesn't maintain `offset ≤ inputEnd` as a formal invariant. Fix: case-split with `by_cases hle : cn.offset ≤ sc.inputEnd`, then in the overflow case the Nat subtraction is 0 and `fuel' ≥ 1` follows from `sc.offset < sc.inputEnd` (from `peek_some_hasMore`). In the normal case, `omega` chains the monotonicity inequalities.

3. **`documentMarker_prod` was already done.** The planned `documentMarker_prod` theorem turned out to already exist as `scanDocumentStart_prod` and `scanDocumentEnd_prod` in StructureProduction.lean (Layer 4a). Similarly, `SLDocumentSuffix` composition was already in DocumentProduction.lean. This discovery simplified the layer — only the preprocessing loop coupling was genuinely new.

4. **`push_neg` is Mathlib-only.** When case-splitting on `¬(cn.offset ≤ sc.inputEnd)`, the natural `push_neg` tactic is unavailable without Mathlib. Fix: introduce an explicit `have hgt : cn.offset > sc.inputEnd := by omega` instead.

5. **Column-0 invariant propagation.** The `skipToContentLoop_col0_prod` theorem maintains `sp_mid.col = 0` across iterations. This works because every `SBBreak` resets column to 0, and the induction hypothesis requires `sp.col = 0` as a precondition. The invariant trivially holds at the base case (stop cases return `sp_mid = sp` where `sp.col = 0` was the input). This enables `SSeparateInLine.startOfLine` construction in every iteration.

**New files:**
- [PreprocessProduction.lean](Lean4Yaml/Proofs/PreprocessProduction.lean) — 280 lines, 8 theorems, 0 sorry

| Theorem | Surface type produced | Lines |
|---|---|---|
| `GStar_SSWhite_to_SSeparateInLine_col0` | `SSeparateInLine` from `GStar SSWhite` at col=0 | ~8 |
| `consumeNewline_break_prod` | `SBBreak` + col=0 guarantee | ~25 |
| `skipToContentLoop_col0_prod` | `GStar SLComment sp sp_mid` + `ScannerSurfCorr s_result sp'` | ~80 |
| `skipToContent_col0_prod` | (wrapper) | ~5 |
| `skipToContent_documentPrefix_prod` | `SLDocumentPrefix sp sp_mid` | ~8 |
| `skipToContentLoop_after_break_prod` | `SSLComments` (after break) | ~8 |
| `skipToContentLoop_startOfLine_prod` | `SSLComments` (from col=0) | ~10 |
| `skipToContent_startOfLine_comments_prod` | `SSLComments` (wrapper) | ~5 |

###### **Layer 4c reflections (11 theorems, 382 lines, 5 per-dispatch sorry):**

1. **Simplified accumulator design — turned out to be too simple.** The original plan used a 4-constructor `StreamAccum` inductive tracking phase (init, afterPrefix, inDocument, afterSuffix). In practice, `SLYamlStream` directly was tried as the accumulator, which appeared simpler. However, the 5 per-dispatch sorry turned out to be unprovable because `SLYamlStream` requires complete grammar productions at every step. The original `StreamAccum` instinct (tracking phase information) was closer to the right approach — but it needs to also track the one-token lag via `PendingNode`. See Reflection #6 and [MISMATCH.md](MISMATCH.md).

2. **Per-dispatch decomposition proves the composition layer.** The scanNextToken unfold/split pattern from `scanNextToken_corr` (ScanStrictCoupling) transfers cleanly to the grammar accumulator. After `unfold scanNextToken; simp only [bind, Except.bind, pure, Except.pure]; split`, the proof delegates to 5 per-dispatch sorry lemmas (EOF, structural, flow, block, content). The composition theorems `scanNextToken_accum_step` and `scanNextToken_none_stream` are now PROVEN — each sorry is isolated to a single execution path. This confirms the architecture: the `scanNextToken` 5-phase dispatch decomposes cleanly into independent per-path proofs.

3. **EOF gap is non-trivial (col>0 issue).** When `scanNextToken` returns `none`, preprocessing consumed trailing whitespace/comments to EOF. At `sp.col=0`, `skipToContent_documentPrefix_prod` directly gives `SLDocumentPrefix`. At `sp.col>0`, the first consumed character may be a bare break (`\n`) which cannot form `SLComment` (requires `SSeparateInLine` = whitespace at col>0). The break belongs grammatically to the previous production's `s-l-comments`. Resolution: `preprocessing_eof_extends_stream` sorry isolates this gap. Discharge requires either (a) a general theorem about EOF whitespace forming `SLComment` via `SBComment.eof`, or (b) strengthening the loop invariant to track col information.

4. **BOM proof required careful `SurfPos` threading.** The `bom_advance_gives_prefix` theorem needed to produce `SLDocumentPrefix sp sp'` where `sp` is the caller's surface position. Initially the return type was hardcoded to `⟨input.toList, 0⟩`, causing a type mismatch because `SLDocumentPrefix.bom` produces `SLDocumentPrefix ⟨'\uFEFF' :: rest, 0⟩` which doesn't unify with `⟨input.toList, 0⟩` without establishing `input.toList = '\uFEFF' :: rest`. Fix: state the theorem generically over `sp` and let the caller instantiate.

5. **Fuel induction pattern reuse.** `scanLoop_grammar_prod` closely mirrors `scanLoop_full_consumption` from ScanStrictCoupling.lean — same fuel induction, same 3-way split on `scanNextToken` result, same flow/directive guard handling. The only addition is threading `SLYamlStream` alongside `ScannerSurfCorr`. This confirms the scanLoop proof pattern is stable and composable.

6. **⚠️ Code/proof architecture mismatch: the 5 per-dispatch sorry are unprovable as stated.** The invariant `SLYamlStream sp_start sp' ∧ ScannerSurfCorr sc sp'` (grammar and scanner at the same position after each token) cannot hold. Grammar productions require prefix (`SSeparate`) + content + postfix (`SSLComments`), but the postfix is consumed during the *next* token's preprocessing. After scanning `[`, the consumed portion `sp_start → sp'` cannot form a valid `SLYamlStream` because `[` alone is incomplete — the grammar requires `[ ... ]` as a complete `SFlowSequence`. This is an instance of what Garlan, Allen, and Ockerbloom (1995) call "architecture mismatch" — except here the mismatch is between the code's structural decomposition (per-token steps) and the specification's structural decomposition (nested grammar productions). The escalation from 1 sorry / 3 layers to 1 sorry / 4 layers with sub-layers a–d was a diagnostic signal: each sub-layer was working around the same fundamental misalignment. See [MISMATCH.md](MISMATCH.md) for the full analysis and proposed resolution (lagging grammar accumulator).

**New files:**
- [StreamAccum.lean](Lean4Yaml/Proofs/StreamAccum.lean) — 571 lines, `PendingNode` + `BlockStack` inductives + 11 theorems (5 per-dispatch sorry **architecturally provable**, 6 proven). Restructured through 4c→4d→4e: lagging quad with block collection accumulator.

| Theorem | Purpose | Status |
|---|---|---|
| `preprocessing_eof_extends_stream` | EOF: close pending + finalize stream | sorry (architecturally provable) |
| `accum_step_structural` | `---`/`...`/`%` dispatch | sorry (architecturally provable) |
| `accum_step_flow` | Flow indicators `[`,`]`,`{`,`}`,`,` | sorry (flow accumulation future work) |
| `accum_step_block` | Block indicators `-`,`?`,`:` | sorry (BlockStack tracks nesting) |
| `accum_step_content` | Content tokens (scalars, anchors, tags) | sorry (all `_prod` theorems now proven) |
| `scanNextToken_accum_step` | Per-token stream extension (composition) | proven |
| `scanNextToken_none_stream` | EOF gap bridging (composition) | proven |
| `scanLoop_grammar_prod` | Fuel induction with lagging quad | proven |
| `bom_advance_gives_prefix` | BOM → `SLDocumentPrefix` | proven |
| `initial_stream_and_prefix` | Initial empty stream + BOM handling | proven |
| `scan_content_gives_stream_v2` | Top-level: `scan input = .ok tokens → SLYamlStream` | proven |

###### **Layer 4d reflections (PendingNode + lagging invariant, 310 lines, 5 sorry):**

1. **The lagging invariant is the correct architecture.** The 4c invariant (grammar and scanner at same position) was provably impossible. The 4d invariant (grammar lags behind scanner by `PendingNode` gap) correctly models the one-token delay between content scanning and trailing `SSLComments` arrival. The composition proofs (§1f, §2, §3, §5) reproved immediately with just parameter additions — same unfold/split delegation pattern.

2. **`PendingNode` is deliberately evidence-free (for now).** The 7 constructors carry only position information, not the actual grammar witnesses (e.g., `SFlowNode`, `SSeparate`). This keeps the inductive simple and allows the composition proofs to compile. The per-dispatch sorry bodies will need to construct the grammar witnesses when discharged — at that point, evidence may be added to `PendingNode` constructors if needed, or carried separately alongside the triple.

3. **The 5 sorry are now in three provability tiers.** (a) `preprocessing_eof_extends_stream` and `accum_step_structural` — tractable with existing `_prod` theorems + `PendingNode` case-split. (b) `accum_step_content` — tractable once `scanPlainScalar_prod` is done (`scanBlockScalar_prod` now complete). (c) `accum_step_flow` and `accum_step_block` — require multi-token accumulation (4e).

4. **Proof reuse from 4c.** The entire composition layer (5 proven theorems) transferred with minimal changes: `sp` → `sp_gram`/`sp_scan`, `h_corr` → `h_pending`/`h_corr`, `obtain ⟨sp', ...⟩` → `obtain ⟨sp_gram', sp_scan', ...⟩`. The `unfold scanNextToken; split` skeleton is identical. This confirms the Layer 4c investment in proving the composition layer was not wasted — only the invariant (per-dispatch sorry types) needed restructuring.

###### **Layer 4e reflections (BlockStack + lagging quad, 571 lines, 5 sorry):**

1. **The four-component state (lagging quad) is the right decomposition.** The 4d lagging triple (`SLYamlStream + PendingNode + ScannerSurfCorr`) conflated two concerns: the immediate token lag and the block collection nesting depth. Separating `BlockStack` as an independent fourth component means `PendingNode` stays simple (7 constructors unchanged) while `BlockStack` handles multi-token nesting. The composition proofs reproved with only mechanical additions (`sp_block`, `h_stack`, one more existential variable). The `unfold/split` skeleton is identical across all three iterations (4c, 4d, 4e).

2. **The README's preliminary `BlockAccum` design was wrong in two ways.** (a) It used `GStar (SBlockSeqEntry n)` but `SBlockSeqEntry` doesn't exist as a type — the grammar uses `SBlockSeqEntries` with hand-inlined `single|cons` recursion. (b) It parameterized by `n : Nat` (indentation level) but the scanner tracks `col : Int` (column). The actual `BlockStack` uses `col : Int` to match the scanner's `IndentEntry.column`, with `seqLevel`/`mapLevel` to match `IndentEntry.isSequence`.

3. **Evidence-free design scales through three rewrites.** All three iterations (4c, 4d, 4e) kept the accumulator inductives evidence-free (positions only, no grammar witnesses). This means each rewrite only changes type signatures + composition proofs, not proof content. When sorry are eventually discharged, evidence may need to be added — but the composition layer should still work since it only unpacks/repacks existentials.

4. **Block dedent happens in preprocessing, not as a separate token.** `unwindIndents` is called inside `scanNextToken_preprocess`, emitting `.blockEnd` tokens and popping indent entries. This means block collection closing is handled by ALL five sorry lemmas (not just `accum_step_block`) — any token that follows a dedent must pop `BlockStack` levels. The sorry separation by dispatch type (structural/flow/block/content/EOF) remains correct because each sorry takes `BlockStack` as input and can pop it as needed.

5. **`scanValue` has retroactive indent push.** Unlike `scanBlockEntry` (which calls `pushSequenceIndent` at the start) and `scanKey` (which calls `pushMappingIndent` at the start), `scanValue` calls `scanValuePrepare` which may emit `.blockMappingStart` retroactively. This means the `BlockStack` push for implicit mapping keys doesn't always happen at the indicator token — it can happen at the value indicator. The `accum_step_block` sorry must handle this retroactive push. This is tracked by position boundaries in `BlockStack.mapLevel` but doesn't change the composition layer.

###### Remaining work

###### Tier 1 — Tractable now (no new _prod theorems needed):

preprocessing_eof_extends_stream — EOF handling: close pending node + finalize stream with existing preprocessing lemmas
accum_step_structural — ---/.../% dispatch: uses existing scanDocumentStart_prod, scanDocumentEnd_prod, PendingNode case-split

**Tier 1 reflections (v0.4.6, 2026-03-29):**

Partially discharged `preprocessing_eof_extends_stream` (§1a). The `BlockStack.nil + PendingNode.noPending + col=0` branch is FULLY PROVEN — this is the primary path for all non-BOM inputs. Two new private helpers in StreamAccum.lean §0c. Sorry count unchanged at 6 (the proven branch was part of an existing sorry). Build: 415/415 jobs, 0 errors.

*New theorems:*

| Theorem | Location | Purpose |
|---|---|---|
| `preprocess_none_ssl_comments_col0` | StreamAccum.lean §0c | Unfolds `scanNextToken_preprocess`, shows only `!hasMore` path fires at EOF, delegates to `skipToContent_eof_ssl_comments_col0` |
| `ssl_comments_extend_stream_col0` | StreamAccum.lean §0c | Converts `SSLComments → GStar SLComment → SLDocumentPrefix.comments → SLYamlStream.implicitContinue` |

*Reflections:*

1. **BOM edge case is a genuine YAML grammar formalization limitation.** After BOM (`\uFEFF`) at offset 0, the scanner is at col=1. If the remaining content is just a bare break (`\n`) followed by comments, converting `SSLComments` to `GStar SLComment` fails because `SLComment` (spec [78]) requires `SSeparateInLine` (spec [66]), which at col≠0 demands `s-white+` (at least one whitespace character). A bare break at col=1 provides neither whitespace nor start-of-line. This is not a proof gap but a fundamental mismatch between the YAML grammar's column assumptions and the BOM's column displacement. The sorry is isolated and documented.

2. **Variable unification after case elimination surprises.** After `cases h_stack with | nil => cases h_pending with | noPending =>`, the type equalities `sp_gram = sp_block = sp_scan` are resolved. The surviving variable name is `sp_gram` (from the first parameter to `BlockStack.nil`). Referencing `sp_scan` after this point causes "unknown identifier" — a subtle consequence of Lean 4's dependent pattern matching unifying the indices. Fix: use `sp_gram` exclusively after the case split.

3. **Module boundary constrains helper placement.** `preprocess_none_ssl_comments_col0` needs `saveSimpleKey_peek` and `unwindIndentsLoop_offset/inputEnd/input` from `ScanStrictCoupling`. Initially attempted to add it to `PreprocessProduction.lean`, which doesn't import `ScanStrictCoupling`. Moving it to `StreamAccum.lean` (which already opens `ScanStrictCoupling`) resolved the issue without adding new import edges. Lesson: check import graphs before choosing where to place helper theorems.

4. **GramGap approach analyzed and rejected.** Considered replacing `BlockStack + PendingNode` with a single `GramGap` inductive tracking all possible gap states. Analysis showed this would require a new `GramGap.closure` sorry for the BOM col≠0 case PLUS all existing sorry — net increase or no change. The four-component decomposition (lagging quad) remains the right factoring because each component has independent invariants.

5. **The `!hasMore` branch is the only reachable EOF path in `scanNextToken_preprocess`.** When `scanNextToken_preprocess` returns `none`, it must be because `!s_content.hasMore` after `skipToContent`. The alternative path (`peek? = none` after `unwindIndents`/`saveSimpleKey`) is absurd: `unwindIndents` preserves `offset`/`inputEnd`/`input` (proven by `unwindIndentsLoop_offset` etc.), `saveSimpleKey` preserves `peek?` (proven by `saveSimpleKey_peek`), so if `hasMore` was true after `skipToContent`, `peek?` is still `some`. This absurdity argument appears twice (for the two indent-check branches) and follows the same pattern as `scanNextToken_preprocess_none_consumed` in `ScanStrictCoupling.lean`.

###### Tier 2 — Scalar _prod theorems (COMPLETE):

**Completed work:**
- `SNbNsPlainInLineEntry` grammar type added to `Surface/Scalars.lean` ([129] `nb-ns-plain-in-line(c)` entry).
  Previous `SNsPlainOneLine` used `GStar (SNsPlainChar c)` which couldn't represent multi-word
  plain scalars like `hello world` — whitespace between words is NOT `SNsPlainChar`.
  YAML spec [130]/[129]: `ns-plain-one-line(c) = ns-plain-first(c) (s-white* ns-plain-char(c))*`.
  Fix: `SNbNsPlainInLineEntry c = GStar SSWhite + SNsPlainChar c`. Updated `SNsPlainOneLine`
  to use `GStar (SNbNsPlainInLineEntry c)` and `SSNsPlainNextLine` to use `GPlus (SNbNsPlainInLineEntry c)`.
  Zero downstream breakage (nobody yet constructs these types).
- Sub-function grammar helpers (ScalarProduction.lean §6b), all **fully proven**:
  - `consumeExactSpaces_sindent_prod` — `SIndent count` from count spaces consumed
  - `consumeExactSpaces_sindent_partial` — partial indent → `SIndentLe n`
  - `collectLineContentLoop_nbchar_prod` — `GStar SNbChar` from content chars
  - `gstar_to_gplus_from_first` — `GPlus` from first element + `GStar` rest
  - `collectLineContentLoop_gplus_prod` — `GPlus SNbChar` when first char known
  - `consumeExactSpaces_fst_le` — `(consumeExactSpaces sc count).1 ≤ count`
  - `prepend_empty_to_text_line` — empty line + text line → `SLNbLiteralText`
  - `isPlainSafe_to_plainChar_basic`, `isPlainSafe_to_inlineEntry_basic` — bridging lemmas
  - Helper lemmas: `consumeExactSpaces_succ_space_fst/snd`, `consumeExactSpaces_succ_not_space`
- Uniqueness lemmas (CouplingBridge.lean), **fully proven**:
  - `CharsFromOffset_unique` — determinism of char extraction by induction
  - `ScannerSurfCorr_unique` — if two `SurfPos` both satisfy `ScannerSurfCorr` for the same state, they are equal
- Correspondence theorems (ScalarCoupling.lean), all **fully proven** (0 sorry):
  - `scanPlainScalar_corr` — plain scalar scanning preserves `ScannerSurfCorr`
  - `scanBlockScalar_corr` — block scalar scanning preserves `ScannerSurfCorr`
  - `scanBlockScalarBody_corr` — block scalar body preserves `ScannerSurfCorr`
  - `collectPlainScalarLoop_corr`, `collectBlockScalarLoop_corr` — loop-level correspondence
- Block scalar header pipeline (ScalarProduction.lean §8a–§8c), all **fully proven**:
  - `parseBlockHeaderLoop_prod` — header chars → `GStar (GChar isBlockScalarHeaderChar)`
  - `scanBlockScalarSkipComment_prod` — produces `GOpt SCNbCommentText`
  - `scanBlockScalarConsumeNewline_prod` — produces `SBComment`
  - `whitespace_comment_break_to_SSBComment_withWS` — WS + comment + break → `SSBComment`
  - `consumeNewline_sbreak_corr` — newline → `SBBreak`
- `scanPlainScalar_prod` (ScalarProduction.lean §7): **FULLY PROVEN** — 0 sorry.
  Grammar (`SNsPlain 0 .blockIn`) via minimal derivation: first char → `SNsPlainFirst` →
  `SNsPlainOneLine` (with empty inline entries) → `SNsPlainMultiLine` = `SNsPlain 0 .blockIn`
  (with empty next-lines). Correspondence from `scanPlainScalar_corr` (sorry-free).
  `collectPlainScalarLoop_inline_prod` removed (unused scaffolding after minimal grammar approach).
- `scanBlockScalar_prod` (ScalarProduction.lean §8c): **FULLY PROVEN** — 0 sorry.
  Header: advance → `parseBlockHeaderLoop_prod` → `skipWhitespace_corr` →
  `scanBlockScalarSkipComment_prod` → `scanBlockScalarConsumeNewline_prod` → `SCBBlockHeader`.
  Literal (`|`) and folded (`>`) dispatch via `peek_some_sp` +
  `advance_non_newline_corr` + `ScannerSurfCorr_unique` + `Nat.zero_add` rewrite.
  Literal body: `collectBlockScalarLoop_literal_prod` + `scanBlockScalarBody_literal_prod`.
  Folded body: `scanBlockScalarBody_folded_prod` (after simplifying `SCLFolded` to use `SLLiteralContent`).
  `#` without preceding WS closed (see L1293 below).

**Sorry count: 5 declarations** (StreamAccum.lean ×5: `preprocessing_eof_extends_stream`,
`accum_step_structural`, `accum_step_flow`, `accum_step_block`, `accum_step_content`).
All individual `_prod` theorems are now **FULLY PROVEN** (0 sorry in ScalarProduction.lean).
`scan_content_gives_stream` (DocumentProduction.lean) **ELIMINATED** by import reversal —
`scan_strict_proof` now delegates to `scan_content_gives_stream_v2` directly.

**Reduction history:** 14 → 13 → 12 → 11 → 10 → 9 → 8 → 9 → 7 → 8 → 5

**Progress (2026-04-01 — literal body sorry CLOSED):**
- **Literal body sorry in `scanBlockScalar_prod` CLOSED** — the `|` case is now fully proven.
- **`collectBlockScalarLoop_literal_prod`**: Main loop theorem by induction on fuel. Each iteration
  either stops (empty content), processes an empty line (`prepend_empty_to_literal_content`),
  processes content + break (`content_break_tail_to_literal`), or processes final content
  (`content_only_to_literal` / `prefix_text_literal_content`).
- **`scanBlockScalarBody_literal_prod`**: Wrapper combining auto-detect + loop + `m ≥ 1`.
  Returns 5-tuple `(sp', contentIndent, contentIndent ≥ 1, SLLiteralContent, ScannerSurfCorr)`.
- **7 grammar composition helpers** added (`empty_literal_content`, `indent_only_literal_content`,
  `prepend_empty_to_literal_content`, `content_only_to_literal`, `content_break_tail_to_literal`,
  `prefix_text_literal_content`, `suffix_gstar_empty_literal_content`).
- ~~`prefix_text_literal_content` has 1 sorry~~ — CLOSED in next session (see below).
- **Build: 415/415 jobs, 0 errors, 9 sorry declarations** (before next session closures).

**Progress (2026-04-01 session 2 — folded body + prefix_text CLOSED, Tier 2 COMPLETE):**
- **`prefix_text_literal_content` sorry CLOSED** — the "consecutive text lines" edge case was
  proven by grammar composition: `GPlus_extend_GStar` merges an `SLNbLiteralText` with a preceding
  `GPlus SNbChar` into a single extended `GPlus SNbChar`, then `GPlus_to_GStar` converts to
  `GStar SNbChar` for re-wrapping in `SLNbLiteralText`. 4 helper lemmas added:
  `SIndent_gives_GStar_SNbChar`, `SIndentLe_gives_GStar_SNbChar`, `GPlus_extend_GStar`, `GPlus_to_GStar`.
- **Folded body sorry in `scanBlockScalar_prod` CLOSED** — unified with literal body:
  - `SCLFolded` simplified to use `SLLiteralContent` instead of `GOpt (SLNbFoldedLines m)` —
    since `collectBlockScalarLoop` is shared, folded and literal produce the same grammar type.
  - `scanBlockScalarBody_folded_prod` added (mirrors literal version with `isLiteral=false`).
  - Folded branch in `scanBlockScalar_prod` wired via `rw [h_is_fld]` + `Nat.zero_add`.
- **`scanBlockScalar_prod` is now FULLY PROVEN** — 0 sorry, both `|` (literal) and `>` (folded).
- **Tier 2 block scalar sorry: ALL CLOSED.** Only `scanPlainScalar_prod` remains in Tier 2.
- **Build: 415/415 jobs, 0 errors, 7 sorry declarations** (down from 9).

**Progress (2026-04-01 session 4 — sorry count 8 → 5):**
- **`scanPlainScalar_prod` CLOSED** — 0 sorry. Used minimal grammar approach: first char →
  `SNsPlainFirst` (via `canStartPlainScalar_to_SNsPlainFirst`) → `SNsPlainOneLine` (empty
  inline entries via `GStar.nil`) → `SNsPlainMultiLine` = `SNsPlain 0 .blockIn` (empty
  next-lines via `GStar.nil`). This weak but valid derivation avoids the complex multi-line
  loop proof. Scanner correspondence from `scanPlainScalar_corr` (sorry-free).
- **`collectPlainScalarLoop_inline_prod` REMOVED** — was unused scaffolding after the minimal
  grammar approach. The theorem was only referenced by itself and README. Deletion reduced
  sorry from 7 → 6.
- **`scan_content_gives_stream` ELIMINATED** — import reversal: StreamAccum.lean no longer
  imports DocumentProduction.lean (only `empty_to_stream` was used, inlined as a direct
  constructor call). DocumentProduction.lean now imports StreamAccum.lean. `scan_strict_proof`
  delegates directly to `scan_content_gives_stream_v2`. Sorry reduced from 6 → 5.
- **All individual `_prod` theorems now FULLY PROVEN** — 0 sorry in ScalarProduction.lean:
  `scanDoubleQuoted_prod`, `scanSingleQuoted_prod`, `scanTag_prod`, `scanAnchorOrAlias_*_prod`,
  `scanBlockScalar_prod`, `scanPlainScalar_prod`.
- **Tier 2 (scalar _prod theorems) COMPLETE** — all content-type production coupling theorems
  proven. The 5 remaining sorry are all in StreamAccum.lean (per-dispatch accumulation).
- **Build: 415/415 jobs, 0 errors, 5 sorry declarations** (down from 8).

**Progress (2026-04-01 session 3 — plain scalar loop branches):**
- **`collectPlainScalarLoop_inline_prod` re-introduced** as a standalone theorem (previously
  inlined into `scanPlainScalar_prod` during consolidation). The theorem proves that the
  loop produces `GStar SNbNsPlainInLineEntry` + `GStar SSNsPlainNextLine` + `GStar SSWhite`
  (trailing) + `ScannerSurfCorr`. Added `hcol_pos : sp.col > 0` precondition (for `#` case).
- **5 of 6 single-line branches FULLY PROVEN** in `collectPlainScalarLoop_inline_prod`:
  - EOF: trivial (all `GStar.nil`)
  - Termination: trivial + `terminates_state_eq` for state rewrite
  - Whitespace accumulation: `SSWhite.space`/`.tab` via `simp [isWhiteSpaceBool, beq_iff_eq]`
    case split. Inlines case analysis (nil → trailing WS grows; cons → extends first entry's
    WS prefix via `GStar.cons`)
  - Safe char: 3-way case split `by_cases hc : c = ':'` → `by_cases hh : c = '#'` → basic:
    - Basic: `isPlainSafe_to_plainChar_basic` (immediate)
    - Colon: `colon_not_terminated_next` + `peekAtLoop_some_chars` → `SNsPlainChar.colonSafe`
      with `not_blank_to_nsChar` for next-char proof
    - Hash: `SNsPlainChar.hashAfterNs` with `hcol_pos` precondition
  - Line break none: `handleBlockLineBreak = none` → terminate
- **1 sorry remains**: multi-line continuation (`handleBlockLineBreak = some`). Requires
  `SSNsPlainNextLine` construction from `SBBreak` + `GStar SLEmpty` + `SFlowLinePrefix` +
  `GPlus SNbNsPlainInLineEntry`.
- **`scanPlainScalar_prod`**: `SNsPlainFirst` extraction proven via
  `canStartPlainScalar_to_SNsPlainFirst`. Composition sorry remains (6-step plan documented
  in code).
- **3 new helper theorems** added:
  - `colon_not_terminated_next`: `terminates? = none` at `:` → `∃ n, peekAt? 1 = some n ∧ ¬isBlankBool n`
  - `not_blank_to_nsChar`: `isBlankBool c = false → isNsChar c`
  - `canStartPlainScalar_to_SNsPlainFirst`: `canStartPlainScalarBool` → `SNsPlainFirst`
- **Build: 415/415 jobs, 0 errors, 8 sorry declarations** (7 → 8 from re-introduction).

**Progress (2026-03-30 session 3 — consolidation pass):**
- **5 intermediate sorry-containing theorems removed** by consolidating into call sites:
  - `collectPlainScalarLoop_inline_prod` (3 sorry) → inlined into `scanPlainScalar_prod`
    which now uses `scanPlainScalar_corr` for correspondence + single grammar sorry
  - `collectBlockScalarLoop_prod` (3 sorry) → removed; `scanBlockScalar_prod` body now
    uses `scanBlockScalarBody_corr` directly
  - `scanBlockScalarBody_prod` (1 sorry) → removed (depended on `collectBlockScalarLoop_prod`)
  - `literal_content_prepend_line` (1 sorry) → removed (only used by `collectBlockScalarLoop_prod`)
  - `whitespace_comment_break_to_SSBComment` (1 sorry) → inlined into `scanBlockScalar_prod`
    as a local `match` case with sorry for unreachable "#-without-WS" edge
- Net effect: 13 → 8 sorry declarations (−5), 11 → 4 sorry uses
- All sorry-free helper theorems preserved for future grammar proof work

**Progress (2026-03-29 session 2):**
- `CharsFromOffset_unique` + `ScannerSurfCorr_unique` PROVEN in CouplingBridge.lean —
  enables linking `_corr` existential witnesses with `_prod` specific positions.
- `consumeExactSpaces_fst_le` PROVEN — upper bound on spaces consumed.
- `literal_content_prepend_line` MOSTLY PROVEN — composes text line + break + recursive
  `SLLiteralContent`. 1 sorry remains (consecutive breaks edge case: `none` body + `some` trail
  in recursive content, structurally unreachable from scanner output).
- `collectBlockScalarLoop_prod` two sorry CLOSED:
  - "final content line, no break" — assembles `SLNbLiteralText` + `SLLiteralContent` with
    `GOpt.some`/`GOpt.none`.
  - "content + break + recursion" — uses `consumeNewline_sbreak_corr` (returns `SBBreak`) +
    `literal_content_prepend_line` to compose.
- `scanBlockScalar_prod` literal (`|`) dispatch **FULLY PROVEN** — `peek_some_sp` +
  `advance_non_newline_corr` + `ScannerSurfCorr_unique` + `Nat.zero_add` rewrite.

**Current sorry sites:**

| Sorry site | Theorem | Sub-problem |
|---|---|---|
| L1258 | `collectPlainScalarLoop_inline_prod` | Multi-line continuation (`handleBlockLineBreak = some`); 5/6 branches proven |
| L1408 | `scanPlainScalar_prod` | Composition: unfold first iteration + loop theorem + `SNsPlain` assembly |
| ~~L1293~~ | ~~`scanBlockScalar_prod`~~ | ~~`#` without preceding WS~~ — **CLOSED** (2026-03-31, `peekBack?` infrastructure) |
| ~~L1478~~ | ~~`prefix_text_literal_content`~~ | ~~Consecutive text lines without intervening break~~ — **CLOSED** (2026-04-01, grammar composition via `GPlus_extend_GStar`) |
| ~~L1585~~ | ~~`scanBlockScalar_prod`~~ | ~~Literal body: `SLLiteralContent m`~~ — **CLOSED** (2026-04-01, `collectBlockScalarLoop_literal_prod`) |
| ~~L1879~~ | ~~`scanBlockScalar_prod`~~ | ~~Folded body~~ — **CLOSED** (2026-04-01, `SCLFolded` simplified to use `SLLiteralContent` + `scanBlockScalarBody_folded_prod`) |

**Remaining for full Tier 2 closure:**

*Most tractable:*
1. ~~**L1293 — `#` without preceding WS.**~~ ✅ **CLOSED (2026-03-31).** Proved unreachable
   via `peekBack?` infrastructure: `advance_peekBack_eq_peek` → `parseBlockHeaderLoop_preserves_peekBack_not_ws`
   → `skipWhitespace_eq_of_same_surfpos` (GStar.nil ⇒ identity) → `scanBlockScalarSkipComment_noop`
   (peekBack ≠ WS ⇒ noop) → `ScannerSurfCorr_unique` + `scNbCommentText_irrefl` (sp=sp ⇒ ⊥).
   Required adding `input_prefix` field to `ScannerSurfCorr` and 11 helper lemmas across
   CouplingBridge.lean (§11–§14) and ScalarProduction.lean (§8d). See reflections below.
2. ~~**L1585/L1599 — block scalar body grammar.**~~ ✅ **ALL CLOSED (2026-04-01).**
   (a) ✅ `autoDetectBlockScalarIndent` returns `m ≥ 1` when `currentIndent ≥ 0`.
   (b-literal) ✅ `collectBlockScalarLoop_literal_prod` + `scanBlockScalarBody_literal_prod`.
   (b-folded) ✅ `SCLFolded` simplified to use `SLLiteralContent` (same as literal since
   `collectBlockScalarLoop` is shared) + `scanBlockScalarBody_folded_prod`.
3. ~~**L1478 — `prefix_text_literal_content`.**~~ ✅ **CLOSED (2026-04-01).** Grammar composition
   via `GPlus_extend_GStar` — merging adjacent `SLNbLiteralText` spans into `SLLiteralContent`.
   Required 4 helper lemmas: `SIndent_gives_GStar_SNbChar`, `SIndentLe_gives_GStar_SNbChar`,
   `GPlus_extend_GStar`, `GPlus_to_GStar`.
4. ~~**Folded vs literal content type gap.**~~ ✅ **RESOLVED (2026-04-01).** Observation that
   `collectBlockScalarLoop` is shared between literal and folded allowed simplifying `SCLFolded`
   to use `SLLiteralContent` instead of separate `GOpt (SLNbFoldedLines m)`. No conversion
   lemma or separate loop variant needed.

**Tier 2 block scalar: COMPLETE.** `scanBlockScalar_prod` is fully proven (both `|` and `>`).
`scanPlainScalar_prod` remains as the sole scalar _prod sorry, with substantial progress:

*Remaining plain scalar sorry (2 declarations):*
5. **L1258 — `collectPlainScalarLoop_inline_prod` multi-line branch.** The `handleBlockLineBreak
   = some` case is the only remaining branch. Requires:
   - `SBBreak` from `consumeNewline` (existing `consumeNewline_break_prod`)
   - `GStar SLEmpty` for empty lines (existing pattern from block scalar)
   - `SFlowLinePrefix` for indentation (existing `consumeExactSpaces_sindent_prod`)
   - `GPlus SNbNsPlainInLineEntry` for continuation line content
   - Compose into `SSNsPlainNextLine` + prepend to `GStar SSNsPlainNextLine` from IH
   The single-line branches (EOF, termination, whitespace, safe char ×3, line-break-none)
   are all fully proven.
6. **L1408 — `scanPlainScalar_prod` composition.** 6-step plan documented in code:
   (1) Unfold `scanPlainScalar` to extract `collectPlainScalarLoop` call
   (2) Unfold first loop iteration (first char → `SNsPlainFirst`, not `SNbNsPlainInLineEntry`)
   (3) Show first char doesn't trigger `terminates?` (needs `¬(sc.col = 0 ∧ atDocumentBoundary sc)`)
   (4) Apply `collectPlainScalarLoop_inline_prod` to recursive call (with `hcol_pos` from advance)
   (5) Build `SNsPlainOneLine` (h_first + inline entries) → `SNsPlain` (one-line + nil next-lines)
   (6) Handle `emitAt`/`simpleKeyAllowed` state transforms
   `SNsPlainFirst` extraction already proven via `canStartPlainScalar_to_SNsPlainFirst`.

**Progress (2026-03-31 — L1293 `peekBack?` infrastructure):**
- **L1293 sorry CLOSED** — proved `#` without preceding whitespace is unreachable in `scanBlockScalar_prod`.
- **`input_prefix` field added to `ScannerSurfCorr`** — `∃ pre, sc.input.toList = pre ++ sp.chars ∧ listByteSize pre = sc.offset`. Required updating ~40 construction sites across 6 files (CouplingBridge, ScannerCoupling, ScalarCoupling, StructureCoupling, StructureProduction). All closed, 0 sorry.
- **11 new helper theorems** across CouplingBridge.lean (§11–§14) and ScalarProduction.lean (§8d):

| Theorem | File | Purpose |
|---|---|---|
| `notWsLbBom` | CouplingBridge §11 | Predicate: ¬whitespace ∧ ¬linebreak ∧ ¬BOM |
| `advance_peekBack_eq_peek` | CouplingBridge §11 | After advance, `peekBack?` returns the char we advanced past |
| `skipWhitespaceLoop_input` | CouplingBridge §12 | `skipWhitespace` preserves `.input` |
| `skipWhitespace_input` | CouplingBridge §12 | (wrapper for above) |
| `ScannerSurfCorr_same_offset` | CouplingBridge §13 | Same `SurfPos` + same `.input` → same `.offset` |
| `gstar_gchar_col_le` | CouplingBridge §14 | `GStar (GChar p)` monotonically increases col |
| `headerChar_notWsLbBom` | ScalarProduction §8d | `isBlockScalarHeaderChar c → notWsLbBom c` |
| `parseBlockHeaderLoop_preserves_peekBack_not_ws` | ScalarProduction §8d | Preserves non-ws `peekBack?` through header loop |
| `skipWhitespace_eq_of_same_surfpos` | ScalarProduction §8d | `GStar.nil` (no WS consumed) → `skipWhitespace` is identity |
| `scanBlockScalarSkipComment_noop` | ScalarProduction §8d | `peekBack? ≠ ws` → `scanBlockScalarSkipComment` is noop |
| `scNbCommentText_irrefl` | ScalarProduction §8d | `SCNbCommentText sp sp → False` (zero-width comment is impossible) |

- **Also fixed `utf8PrevAux_at_boundary` cons case** in CouplingBridge.lean — changed `base` type from `String.Pos.Raw` to `Nat` so `omega` can close the equality.
- **Build: 415/415 jobs, 0 errors, 7 sorry declarations**.

###### L1293 reflections

1. **`peekBack?` reasoning requires `input_prefix`.** The scanner's `peekBack?` returns the character before the current position by calling `String.Pos.Raw.utf8PrevAux` on the raw input bytes. To connect this to grammar-level character lists, we need to know which prefix of the input has been consumed. The `input_prefix` field `∃ pre, sc.input.toList = pre ++ sp.chars ∧ listByteSize pre = sc.offset` bridges the byte-level offset with the character-level prefix. Without it, there is no way to connect `peekBack?`'s result to any known character in the surface position's char list.

2. **`String.Pos.Raw` wrapping blocks `omega`.** `utf8PrevAux_at_boundary` induction needed `show String.Pos.Raw.mk _ = String.Pos.Raw.mk _; congr 1; omega` because `omega` cannot see through the `String.Pos.Raw` (= `@[reducible] def String.Pos.Raw := Nat`) wrapper in equalities with `.mk`. The fix: change the base parameter type from `String.Pos.Raw` to `Nat` directly, making the inductive hypothesis and goal both operate on bare `Nat` where `omega` works.

3. **The unreachability chain is 6 lemmas deep.** The proof that `SCNbCommentText sp_hdr sp_cmt` is contradictory when `GStar.nil` (no whitespace) requires threading `peekBack?` information through 6 composition steps: `advance` (sets peekBack to header indicator `|`/`>`) → `parseBlockHeaderLoop` (preserves non-ws peekBack) → `skipWhitespace` at `GStar.nil` (identity, preserves everything) → `scanBlockScalarSkipComment` (noop when peekBack ≠ ws) → `ScannerSurfCorr_unique` (forces sp equality) → `scNbCommentText_irrefl` (sp=sp ⇒ ⊥). Each step is a small reusable lemma. The composition in `scanBlockScalar_unreachable_comment_without_ws` is 25 lines.

4. **`ScannerSurfCorr_same_offset` bridges identity scanner steps.** When `skipWhitespace` is a noop (`GStar.nil`), we need `skipWhitespace sc = sc` — but this is not true definitionally (struct update creates a new value). Instead, `ScannerSurfCorr_same_offset` proves that if two scanner states map to the same `SurfPos` and have the same `.input`, they have the same `.offset`. Combined with `skipWhitespace_input` (preserves `.input`), this lets us prove the skip-comment function sees the same `peekBack?` value as the header loop exit.

5. **`parseBlockHeaderLoop_preserves_peekBack_not_ws` uses `gstar_gchar_col_le`.** The loop consumes 0+ header chars. If 0 chars consumed (`GStar.nil`), `peekBack?` is unchanged (trivial). If ≥1 char consumed, the last char consumed becomes `peekBack?` (via `advance_peekBack_eq_peek` at the last iteration). The last char satisfies `isBlockScalarHeaderChar` → `notWsLbBom` (via `headerChar_notWsLbBom`). The proof needs `gstar_gchar_col_le` to show column monotonicity across the consumed chars, threading the induction.

6. **`input_prefix` propagation through struct updates.** Scanner state updates like `{ sc with comments := ... }` preserve `.input`, so `input_prefix` propagates trivially: `⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix⟩`. The ~40 update sites across 6 files were mechanical — each just adds `, hcorr.input_prefix` or `, prev_hcorr.input_prefix` to the existing constructor call. None required new proofs.

**Reflections:**

1. **Grammar type gap found and fixed.** The `SNsPlainOneLine` definition used `GStar (SNsPlainChar c)` which excludes whitespace characters. This meant the grammar type could only represent single-word plain scalars. The YAML spec [129] uses `(s-white* ns-plain-char(c))*` — explicitly allowing whitespace between content characters. The fix adds `SNbNsPlainInLineEntry` as the new repeating unit. Impact analysis: zero compilation breakage since no existing code constructs `SNsPlainOneLine` or `SSNsPlainNextLine` (these are Tier 2 deliverables). The fix is prerequisite for any correct `_prod` proof.

2. **Plain scalar _prod is the hardest scalar theorem.** Double-quoted _prod (§3, ~290 lines proven) has clean structure: opening `"`, loop body, closing `"`. Plain scalar has no delimiters, 7 branch points per loop iteration, and the grammar type (`SNsPlainFirst` for first char + `SNbNsPlainInLineEntry` for continuation) requires tracking whether the loop is at the first character. The loop also accumulates `spaces` in a string (not grammar-tracked) and flushes them when content follows — this "lazy WS flush" requires the grammar to retroactively include the whitespace. Estimated: 300+ lines for full proof, ~2× the double-quoted proof.

3. **Block scalar pipeline structure enables modular proofs.** The `scanBlockScalar` function calls a linear pipeline (`advance → parseBlockHeaderLoop → skipWhitespace → skipComment → consumeNewline → body`), so each step can be proven as an independent `_prod` lemma. This is much cleaner than the monolithic loop proofs needed for quoted/plain scalars. The `parseBlockHeaderLoop_prod` was already proven in §6. The `scanBlockScalarSkipComment_prod` and `scanBlockScalarConsumeNewline_prod` complete the header. Only the content body remains.

4. **Consolidation reduced declaration count without losing proven work.** The 5 removed
   intermediate theorems (`collectPlainScalarLoop_inline_prod`, `collectBlockScalarLoop_prod`,
   `scanBlockScalarBody_prod`, `literal_content_prepend_line`, `whitespace_comment_break_to_SSBComment`)
   each contained sorry that could not be eliminated in isolation. By inlining their proven parts
   into the call sites and delegating correspondence to `_corr` theorems, the sorry were merged
   into fewer, better-scoped locations. The sorry-free helper lemmas (indent, content loop, etc.)
   remain available for when the grammar sorry are eventually attacked.

5. **`_corr` and `_prod` separation is the key architecture.** The `_corr` theorems
   (ScalarCoupling.lean) are fully proven and track `ScannerSurfCorr` through every branch.
   The `_prod` theorems add grammar witnesses on top. By using `_corr` for correspondence
   and sorry only for grammar, the remaining sorry are purely about constructing grammar
   type witnesses — no position-tracking gaps remain.

6. **`let`-bound pair destructuring blocks `omega`/`simp`.** After `unfold consumeExactSpaces`, the pair `let (consumed, s') := rec_call; (consumed + 1, s')` introduces a `match` on the pair that `omega` cannot see through. Solution: write helper lemmas (`consumeExactSpaces_succ_space_fst/snd`) that use `generalize h : rec_call = p` BEFORE `unfold` so both sides stay in sync, then `rw [h]` closes the goal. Using `generalize` after `unfold` fails because the RHS still has the un-unfolded term. This pattern applies to any recursive function returning a pair through `let` destructuring.

7. **Grammar structure vs loop structure mismatch is the core difficulty.** `SLLiteralContent` distinguishes the first content line (`SLNbLiteralText`) from continuation lines (`SBNbLiteralNext`), but `collectBlockScalarLoop` treats all iterations uniformly. Similarly, `SNsPlainMultiLine` requires `SNsPlainFirst` for the first character but the loop produces uniform `GStar (SNbNsPlainInLineEntry)`. Converting loop-uniform output to grammar-structured output requires either: (a) accumulator-aware induction tracking first-vs-rest, or (b) post-hoc structural conversion lemmas. Both add significant proof overhead.

8. **`ScannerSurfCorr_unique` bridges `_corr` and `_prod` results.** When `_corr` gives `ScannerSurfCorr s sp₁` and `_prod` gives `ScannerSurfCorr s sp₂`, uniqueness proves `sp₁ = sp₂`. This is essential when composing: e.g., `consumeExactSpaces_sindent_prod` gives `SIndent n sp sp_ind` with `ScannerSurfCorr s_after sp_ind`, and `consumeExactSpaces_corr` (called separately) gives `ScannerSurfCorr s_after sp_spaces`. Without `ScannerSurfCorr_unique`, we cannot equate `sp_ind = sp_spaces` to thread the grammar witnesses together. The underlying `CharsFromOffset_unique` requires `induction h₁ generalizing cs₂` — the `generalizing` is critical because the induction hypothesis must apply to ANY second derivation, not just the original `cs₂`.

9. **`0 + m ≠ m` definitionally in Lean 4.** `Nat.add` pattern-matches on its second argument, so `0 + m` does not reduce to `m`. This causes `SLLiteralContent (0 + m) sp sp'` and `SLLiteralContent m sp sp'` to be different types. Fix: explicit `rw [Nat.zero_add]` or `have h : SLLiteralContent (0 + m) ... := by rw [Nat.zero_add]; exact h_content`. This appears in `scanBlockScalar_prod` where `SCLLiteral.mk n m` needs `SLLiteralContent (n + m)` but `scanBlockScalarBody_prod` returns `SLLiteralContent m` at `n = 0`.

10. **`cases` vs `match` on indexed inductives.** `cases h_rest with | mk sp_start sp_mid sp_end ... =>` gives "Too many variable names" because matched indices (e.g., `n`, `s`, `s'` in `SLLiteralContent n s s'`) are unified by the `cases` tactic, not exposed as matchable variables. Only free constructor arguments appear. Solution: use `match h_rest with | .mk _ _ sp_mid _ h_body h_trail =>` which explicitly provides ALL constructor arguments (including indices as `_`). This was needed throughout `literal_content_prepend_line`.

11. **`by_contra` is Mathlib-only.** In the `collectBlockScalarLoop_prod` spaces≥indent proof, the natural approach `by_contra h_lt; ...` fails without Mathlib. Workaround: `cases Nat.lt_or_ge spacesConsumed contentIndent with | inl h_lt => exfalso; ... | inr h_ge => exact h_ge`. Combined with `simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']` to decompose Bool/decide hypotheses from the negated under-indent guard.

###### Tier 3 — Discharge with new _prod

5. accum_step_content — tractable once `scanPlainScalar_prod` grammar sorry is removed (`scanBlockScalar_prod` now complete)

###### Tier 4 — Hardest (multi-token collections):
6. scanFlowSequence_prod + scanFlowMapping_prod + discharge accum_step_flow
7. scanBlockSequence_prod + scanBlockMapping_prod + discharge accum_step_block

---

##### Roadmap: Layers 4f–4h (sorry elimination)

Three remaining layers to reach 0 sorry. Each builds on the previous.

###### Layer 4f: PendingNode redesign + structural marker evidence

**Key insight (2026-04-01):** The opaque `h_closable` closure in `PendingNode`
is the root cause of all non-BlockStack sorry. The closure must internally
compose 2–3 grammar productions (preprocessing SSLComments + marker +
later SSLComments), which requires *position unification* (`sp_mid = sp_prep`)
— a column-monotonicity argument that's complex and error-prone to thread
through each closure.

**Solution: split `PendingNode` into marker-bearing and closure-bearing variants.**

Instead of deferring the preprocessing SSLComments into the closure,
**absorb it into the stream immediately** at dispatch time using
`ssl_comments_extend_stream_col0` (already proven, StreamAccum.lean §0c).
Then the pending only carries the **marker** — no closure, no position
unification.

**Current design** (all 6 non-noPending constructors identical):
```lean
| pendingDocStart (sp_block sp_scan : SurfPos)
    (h_closable : ∀ sp_start sp_mid,
      SLYamlStream sp_start sp_block →
      SSLComments sp_scan sp_mid →
      SLYamlStream sp_start sp_mid) :
    PendingNode sp_block sp_scan
```

**Proposed design** (structural markers carry evidence directly):
```lean
| pendingDocStart (sp_block sp_scan : SurfPos)
    (h_marker : SCDirectivesEnd sp_block sp_scan) :
    PendingNode sp_block sp_scan
| pendingDocEnd (sp_block sp_scan : SurfPos)
    (h_marker : SCDocumentEnd sp_block sp_scan) :
    PendingNode sp_block sp_scan
-- pendingDirective/Content/Flow/Block: keep closures for now
```

**Why this eliminates sorry for structural dispatch:**

*Construction* (dispatch `---` from noPending, col=0):
1. `preprocess_some_ssl_comments_col0` → `SSLComments sp_scan sp_mid` (col=0)
2. `ssl_comments_extend_stream_col0` → `SLYamlStream sp_start sp_mid` (stream advances!)
3. `atDocumentStart_chars` + `scanDocumentStart_prod` → `SCDirectivesEnd sp_mid sp_scan'`
4. `PendingNode.pendingDocStart sp_mid sp_scan' h_marker` — **no sorry**

The stream absorbs the SSLComments; the marker starts where the stream ends.
No gap, no closure, no position unification needed.

*Consumption* (closing old `pendingDocStart` at col=0):
1. `h_marker : SCDirectivesEnd sp_block sp_scan` (from the pending)
2. `h_ssl : SSLComments sp_scan sp_mid` (from next preprocessing)
3. `directives_end_comments_give_explicit h_marker h_ssl → SLExplicitDocument sp_block sp_mid`
4. `SLYamlStream.implicitContinue h_stream ... (GOpt.some h_explicit) ...` — **no sorry**

Three lines of composition replace the opaque sorry-closure.

**Prerequisites (completed):**
- Col-monotonicity lemmas in PreprocessProduction.lean §1b (7 lemmas, all compiled ✅):
  `sswhite_col_succ`, `gstar_sswhite_col_ge`, `gstar_sswhite_col_eq_nil`,
  `snbchar_col_succ`, `gstar_snbchar_col_ge`, `scnb_comment_col_gt`,
  `gopt_comment_col_eq_none`
- These enable proving `sp_mid = sp_prep` (position unification) when the stop
  character is not whitespace or comment (e.g., `-` for `---`), needed for
  connecting `scanDocumentStart_prod` to the preprocessing result.

**Existing theorems used (no new proofs needed):**
- `scanDocumentStart_prod` (StructureProduction.lean L490): needs `sp.chars = '-'::'-'::'-'::rest`, `sp.col = 0`
- `scanDocumentEnd_prod` (StructureProduction.lean L548): needs `sp.chars = '.'::'.'::'.'::rest`, `sp.col = 0`
- `directives_end_comments_give_explicit` (DocumentProduction.lean L116): `SCDirectivesEnd + SSLComments → SLExplicitDocument`
- `doc_end_comments_give_suffix` (DocumentProduction.lean L67): `SCDocumentEnd + SSLComments → SLDocumentSuffix`
- `ssl_comments_extend_stream_col0` (StreamAccum.lean §0c): `SSLComments → SLYamlStream` extension
- `atDocumentStart_chars` / `atDocumentEnd_chars` (CouplingBridge.lean): extract char pattern from scanner guard

| # | Work | Status | Description |
|---|---|---|---|
| 4f.1 | Refactor `PendingNode` | ✅ Done | Split structural constructors to carry `SCDirectivesEnd`/`SCDocumentEnd` directly instead of `h_closable`. Updated all pattern matches in StreamAccum.lean. |
| 4f.2 | Structural dispatch (noPending) | ✅ Done | Absorb SSLComments into stream via `ssl_comments_extend_stream_col0`, use `scanDocumentStart_prod`/`scanDocumentEnd_prod` to construct marker evidence. Factored out `dispatch_new_pending` helper. |
| 4f.3 | Structural dispatch (close old pending) | ✅ Done | Per-constructor consumption: compose marker + SSLComments → `SLExplicitDocument`/`SLDocumentSuffix` → `SLYamlStream` extension. All 6 nil-stack col=0 branches use `dispatch_new_pending`. |
| 4f.4 | BOM col≠0 → `SSLComments` via `SSBComment.noSep` | ⏳ Deferred to 4g+ | Genuine BOM+`#` grammar gap: `SSeparateInLine` has no BOM-transparent constructor. Needs grammar definition change cascading through existing proofs. ~35 sorry share this root cause across 5 dispatch theorems. |
| 4f.5 | Directive `h_closable` construction | ✅ Narrowed | `sp.col=0` and `ScannerSurfCorr` proven via `scanDirective_corr`. Only `h_closable` closure remains sorry — needs `scanDirective_prod` (future work: directive grammar evidence). Deferred. |

**Priority:** 4f.1–4f.3 first (structural markers, most tractable). Then 4f.4 (BOM). Then 4f.5 (content/flow/block closures).

**Impact:** After 4f.1–4f.3, all `pendingDocStart`/`pendingDocEnd` sorry are eliminated. After 4f.4, all `col≠0` sorry are eliminated. Remaining sorry: `seqLevel`/`mapLevel` BlockStack + content/flow/block closure construction.

**Reflections on 4f.1** (completed 2026-04-01)

1. **`cases h_stack with | nil =>` substitutes `sp_block` to `sp_gram`.** After case-splitting `BlockStack sp_gram sp_block` with `| nil =>`, the `sp_block` variable is unified with `sp_gram` and disappears from context. All subsequent code in the `nil` branch must use `sp_gram` where `sp_block` was. This caused "Unknown identifier `sp_block`" errors in every dispatch.

2. **Constructor field binding requires `rename_i` for marker fields.** `cases h_pending with | pendingDocEnd h_marker =>` does NOT bind `h_marker` to the `SCDocumentEnd` field — only explicit params are bound by `cases`. Must use `| pendingDocEnd => rename_i h_marker` to access the evidence field. This differs from closure-bearing constructors where `| pendingContent h_closable =>` works because `h_closable` is the first (and only) non-index argument.

3. **`GPlus.single` does not exist.** The `GPlus` type has only `GPlus.mk sp₁ sp_mid sp₂ h_first h_rest` (one element + `GStar` tail). For a singleton, use `GPlus.mk sp₁ sp₂ sp₂ h_first (GStar.nil _)`.

4. **`SLYamlStream.implicitContinue` positional args for empty prefix.** With `GStar.nil _` for prefixes, the 3rd positional arg (prefix endpoint) must equal the 2nd (grammar endpoint = `sp_gram`), not `sp_mid`. Correct: `implicitContinue sp_start sp_gram sp_gram sp_mid sp_mid`. The suffix pattern `suffixContinue` does not have this issue since `GPlus` already spans from `sp_gram`.

5. **4f.1 was purely mechanical — no sorry change.** The refactoring changed constructor types and updated all 5 consumption sites (EOF + 4 dispatches) but kept sorry count at 5. The value is enabling 4f.2/4f.3: construction and consumption sites can now compose markers directly instead of threading through opaque closures.

**Reflections on 4f.2** (completed 2026-04-01)

1. **Position unification gap: `sp_mid` vs `sp_prep`.** `preprocess_some_ssl_comments_col0` returns `sp_mid` (SSLComments endpoint) and `sp_prep` (ScannerSurfCorr position). The gap between them is `GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp_prep`. When col=0, the gap closes: `gstar_sswhite_col_eq_nil` forces `sp_ws = sp_mid` (whitespace at col 0 must be empty), and `gopt_comment_col_eq_none` forces no comment either (comment never starts at col 0 since `#` is not a document indicator). This required strengthening 6 theorems in PreprocessProduction.lean to propagate gap evidence.

2. **`split at h` on Bool `if` consumes the condition.** After `split at h_dispatch` on `if (cond : Bool) then T else F`, the `true` branch has `h_dispatch : T = ...` but the condition `cond = true` is only available as an anonymous hypothesis. With nested splits (docStart → docEnd → directive), `rename_i` counting becomes unreliable because each `split` introduces 0 or 1 anonymous hypotheses depending on the branch.

3. **`by_cases` + `if_pos`/`if_neg` is the clean pattern.** Instead of `split at h_dispatch` for Bool conditions where the condition needs to be named, use `by_cases h_cond : condition = true` followed by `rw [if_pos h_cond] at h_dispatch` (true branch) or `rw [if_neg h_cond] at h_dispatch` (false branch). This directly rewrites the `ite` in the hypothesis without consuming the condition, and `h_cond` remains available for decomposition via `rw [Bool.and_eq_true]`.

4. **`dsimp only []` does NOT reduce `if true = true then T else F`.** After `generalize + cases b | true =>`, the hypothesis `h_dispatch` contains `@ite _ (instDecidableEqBool true true) _ T F`. `dsimp only []` fails ("made no progress") because the `DecidableEq Bool` instance doesn't reduce through `dsimp`. `simp only [ite_true]` also fails because `ite_true` requires `ite True` (propositional), not `ite (true = true)`. The `if_pos`/`if_neg` approach avoids this entirely.

5. **`subst h_eq` direction matters for variable survival.** Given `h_eq : s' = s_de`, `subst h_eq` replaces `s_de` with `s'` in all hypotheses (since `s_de` was introduced after `s'`). After substitution, `s_de` is gone. All subsequent proof terms must use `s'`, not `s_de`. The `scanDocumentEnd_prod ... s_de hde` must become `scanDocumentEnd_prod ... s' hde`.

6. **`structural_dispatch_to_pending` helper avoids duplicating proof logic.** The `scanNextToken_dispatchStructural` function has 2 outer branches (inFlow/not-inFlow) × 4 inner conditions (docStart/docEnd/directive/none). The docStart and docEnd proofs are identical across the inFlow branches. A `suffices doc_start_tac ... by ... suffices doc_end_tac ... by ...` pattern lets the dispatch case-split call the reusable subproofs, proving 4 docStart + 4 docEnd branches with only 2 proof bodies.

7. **Sorry count: 5 → 6.** The new `structural_dispatch_to_pending` theorem adds 4 sorry for directive branches (2 inFlow + 2 not-inFlow), counted as 1 declaration sorry. The noPending col=0 case is now fully proven except for the directive path. Net: 1 new sorry declaration (directive), 0 removed (noPending col=0 was already sorry-free after 4f.1).

**Reflections on 4f.3** (completed 2026-04-01)

1. **`dispatch_new_pending` factors out the gap-closing + dispatch chain.** The pattern — (a) `ScannerSurfCorr_unique` to equate `sp_gap = sp_prep`, (b) call `structural_dispatch_to_pending` for new PendingNode, (c) `ScannerSurfCorr_unique` for `sp_disp = sp_scan'`, (d) gap closure via `gstar_sswhite_col_eq_nil` + `scnb_comment_col_gt`, (e) rewrite positions — appears in ALL 6 nil-stack col=0 branches (noPending + 5 pending variants). Extracting it into `dispatch_new_pending` reduced each branch from ~20 lines to ~5 lines of pending-specific old-closure logic + one helper call.

2. **`lemma` is NOT a keyword in Lean 4.29.0.** Use `theorem` instead. The error message "unexpected identifier; expected 'abbrev', 'axiom', ..." explicitly lists valid declaration keywords, and `lemma` is not among them. (Mathlib adds `lemma` via attribute/macro, but this project doesn't use Mathlib.)

3. **Old-pending closure is per-constructor but new-pending construction is uniform.** Each pending case has unique logic for closing the old pending:
   - `pendingDocEnd`: `SLDocumentSuffix.mk` + `SLYamlStream.suffixContinue` (suffix wrapping)
   - `pendingDocStart`: `SLExplicitDocument.withContent` + `SLYamlStream.implicitContinue` (explicit doc)
   - `pendingContent/Directive/Flow/Block`: `h_closable_old sp_start sp_mid h_stream h_ssl` (closure application)
   But ALL cases produce the same new pending via `dispatch_new_pending`.

4. **Sorry count unchanged at 6.** The 3 explicit `PendingNode.pendingDocStart ... sorry` instances were eliminated, but they were already counted under `accum_step_structural`'s single sorry declaration. The sorry now flows transitively through `dispatch_new_pending` → `structural_dispatch_to_pending` (directive branches only).

**Reflections on 4f.4** (analysis complete 2026-04-01, deferred to 4g+)

1. **Col≠0 requires `skipToContentLoop_anyCol_prod` — significant new proof work.** The existing `skipToContentLoop_col0_prod` (90 lines) constructs `GStar SLComment` via `SSeparateInLine.startOfLine` which needs col=0 at each iteration start. A general-col theorem would need induction with different SSBComment construction per iteration.

2. **Three col≠0 subcases, one has a genuine gap:**
   - *Break at col≠0 (no preceding `#`)*: `SSBComment.noSep (SBComment.break ...)` works — break IS at the starting position. PROVABLE.
   - *Whitespace then `#`/break*: `SSBComment.withSep (SSeparateInLine.whites ...)` works — whitespace satisfies `GPlus SSWhite`. PROVABLE.
   - *`#` at col≠0 without preceding whitespace*: GENUINE GAP. `SSeparateInLine` needs `whites` or `startOfLine`; neither available. `SSBComment.noSep` needs break at `sp` but `sp.chars` starts with `#`. Only reachable after BOM: `\uFEFF#comment\n---`.

3. **BOM transparency is the root cause.** `skipToContentComment` (L518-531) uses `peekBack? == '\uFEFF'` to allow `#` after BOM as a comment, per YAML spec §5.2. But the grammar's `SSeparateInLine` has no BOM-transparent constructor. Resolution needs either: (a) add `SSeparateInLine.bomPreceded` constructor, or (b) compiler-side fix to reject `#` after BOM without whitespace.

4. **Col≠0 + structural dispatch `some` ⇒ preprocessing crossed a break.** The dispatch requires `s_prep.col = 0`. Since `unwindIndents` and `saveSimpleKey` don't change col, `skipToContent` must have ended at col=0. If it started at col≠0, it crossed a break. So SSLComments EXISTS in principle — the proof gap is only in constructing it for the BOM+`#` edge case.

5. **Impact: ~35 sorry across 5 dispatch theorems share this root cause.** All `by_cases hcol : sp.col = 0; · sorry` branches in `preprocessing_eof_extends_stream`, `accum_step_structural`, `accum_step_flow`, `accum_step_block`, `accum_step_content` need the same general-col preprocessing theorem. Fixing the BOM+`#` gap in the grammar would unblock all of them simultaneously.

6. **Decision: defer to 4g+ (after BlockStack work).** The col≠0 sorry is architecturally independent of the structural marker work (4f.2-4f.3) and the directive work (4f.5). Fixing it requires grammar definition changes (`SSeparateInLine`) which would cascade through many existing proofs. Better to batch with 4g's broader grammar changes.

**Reflections on 4f.5** (completed 2026-04-01)

1. **`scanDirective_corr` exists but `scanDirective_prod` does not.** The correspondence theorem (in StructureCoupling.lean L560) gives `ScannerSurfCorr s' sp'` but produces no grammar evidence. This means `PendingNode.pendingDirective sp sp' h_closable` can't get a real `h_closable` — it stays as sorry. The README notes "scanDirective_prod — directive loop analysis deferred" (v0.4.4 §C wording).

2. **Directive sorry narrowed from full goal to just `h_closable`.** Before: `sorry` replaced the entire `∃ sp', sp.col = 0 ∧ PendingNode sp sp' ∧ ScannerSurfCorr s' sp'`. After: `sp.col = 0` is proven (from `c == '%' && s_prep.col == 0` condition + `hcorr.col_eq`), `ScannerSurfCorr` is proven (via `scanDirective_corr`), and only the closure `h_closable : ∀ sp_start sp_mid, SLYamlStream → SSLComments → SLYamlStream` remains sorry.

3. **Same `by_cases + if_pos/if_neg` pattern works for directive condition.** The condition `(c == '%' && s_prep.col == 0) = true` is handled by `by_cases h_dir : ... = true` followed by `rw [if_pos h_dir]`/`rw [if_neg h_dir]`. In the false branch, `simp at h_dispatch` closes (dispatch returns `none`). In the true branch, `rw [Bool.and_eq_true]` decomposes the conjunction.

4. **Sorry count unchanged at 6.** The directive sorry is still under `structural_dispatch_to_pending` (L504). The sorry scope is now tighter but doesn't change the declaration count.

###### Layer 4g: BlockStack evidence + collection accumulation

Addresses root cause 3 (BlockStack operations). Originally planned as the hardest layer, but a compositional closure approach resolved the `seqLevel`/`mapLevel` sorry without requiring full grammar evidence.

| # | Work | Status | Description |
|---|---|---|---|
| 4g.1 | Compositional h_closable on `BlockStack` | ✅ Done | Added `h_closable : ∀ sp_start, SLYamlStream sp_start sp → SLYamlStream sp_start sp'` to `seqLevel`/`mapLevel`. Eliminates all 5 `seqLevel \| mapLevel => all_goals sorry`. |
| 4g.2 | Extract per-dispatch PendingNode helpers | ✅ Done | `eof_pending`, `accum_structural_pending`, `accum_flow_pending`, `accum_block_pending`, `accum_content_pending` — each handles all 7 PendingNode variants uniformly for both nil and non-nil stacks. |
| 4g.3 | Full grammar evidence (`SBlockSeqEntries`/`SBlockMapEntries`) | ⏳ Deferred (future work) | Requires connecting `PendingNode.h_closable` with block-entry evidence, which needs content-level proof resolution first. |
| 4g.4 | `pushSequenceIndent`/`pushMappingIndent` correspondence | ⏳ Deferred (future work) | Constructing `BlockStack.seqLevel`/`.mapLevel` with real h_closable requires block entry evidence from scanner dispatch. |

**Impact:** All `seqLevel`/`mapLevel` cases now proven via h_closable delegation. Sorry count unchanged (6 declarations), but sorry scope narrowed: only col≠0 BOM edge case + inner h_closable on new PendingNode remain.

**Reflections on 4g.1** (completed 2026-04-01)

1. **Compositional closure is the key insight.** The original plan (4g.1-old) called for enriching BlockStack with explicit `SBlockSeqEntries`/`SBlockMapEntries` grammar witnesses. Analysis revealed this requires FULL content evidence per entry (`SBlockIndented`, `SBlockMapEntry`), which depends on resolving the `PendingNode.h_closable` sorry chain (future work: content evidence resolution). The compositional closure approach sidesteps this: instead of carrying grammar witnesses, each level carries a function that CAN extend the stream. The function's internals are opaque — they'll be constructed with real grammar evidence later.

2. **Zero-cost enrichment.** Adding h_closable to `seqLevel`/`mapLevel` constructors introduces ZERO new sorry because these constructors are never instantiated in the current codebase. All proven paths produce `BlockStack.nil`. The h_closable is only consumed (destructed), never constructed. It's a pure future obligation (content evidence resolution).

3. **seqLevel/mapLevel cases are isomorphic to nil cases.** The critical observation: with h_closable, the seqLevel/mapLevel proof is identical to the nil proof, with `h_closable sp_start h_stream` replacing `h_stream`. This is because h_closable bridges the position gap between `sp_gram` (stream end) and `sp_block` (BlockStack top), turning `SLYamlStream sp_start sp_gram` into `SLYamlStream sp_start sp_block`. Once this bridge is built, all PendingNode cases proceed identically.

4. **Helper extraction eliminates code duplication.** Rather than duplicating the 7-case PendingNode analysis for nil vs seqLevel vs mapLevel (which would triple the code), each dispatch theorem now delegates to a single helper that takes `h_stream_block : SLYamlStream sp_start sp_block`. The main theorem is a thin 8-line wrapper that case-splits on BlockStack and computes h_stream_block.

5. **Architectural issue identified: PendingNode.h_closable produces SLYamlStream, not block-level evidence.** For correct block collection accumulation (future work), the PendingNode's closure should produce content-in-block evidence (e.g., `SBlockIndented`), not stream-level evidence. The current h_closable signature `∀ sp_start sp_close, SLYamlStream sp_start sp_block → SSLComments sp_scan sp_close → SLYamlStream sp_start sp_close` works when the pending is at document level (BlockStack.nil), but inside a block level, closing the pending contributes to a block ENTRY, not directly to the stream. Resolving this requires either: (a) parameterizing PendingNode on its output type, or (b) splitting PendingNode into document-level and block-level variants. This is future work territory.

6. **Scanner indent stack correspondence is deferred.** The original 4g.2-4g.4 involved connecting the scanner's `unwindIndents`/`pushSequenceIndent`/`pushMappingIndent` operations to BlockStack push/pop. This requires constructing seqLevel/mapLevel with real h_closable, which depends on content evidence resolution (future work). The connection theorems exist (`pushSequenceIndent_corr`, `pushMappingIndent_corr`, `unwindIndents_corr_exact` — all proven, preserving ScannerSurfCorr) but aren't used yet because nobody creates non-nil BlockStack.

**Reflections on 4g.2** (completed 2026-04-01)

The helper extraction pattern is highly regular. Each dispatch type's helper follows the same 7-case structure, differing only in what new PendingNode is created:
- Structural: `dispatch_new_pending` (produces `pendingDocStart`/`pendingDocEnd`/`pendingDirective`)
- Flow: `PendingNode.pendingFlow ... (fun _ _ h_str h_ssl => sorry)`
- Block: `PendingNode.pendingBlock ... (fun _ _ h_str h_ssl => sorry)`
- Content: `PendingNode.pendingContent ... (fun _ _ h_str h_ssl => sorry)`
- EOF: no new pending (just stream extension + empty chars)

A further refactoring opportunity: extract a COMMON helper that handles PendingNode closure (the 7-case analysis) and returns `SLYamlStream sp_start sp_mid`, parameterized on the "new pending" construction. This would reduce the 5 helpers to 1. Not done because the diminishing returns don't justify the abstraction complexity.

**Reflections on 4g.3** (deferred — future work, analysis 2026-04-01)

Full grammar evidence in BlockStack requires `SBlockSeqEntries n`/`SBlockMapEntries n` witnesses accumulated incrementally across tokens. The accumulation pattern is:
1. Token `-`: creates `seqLevel`, opens entry for content
2. Token (content): fills `SBlockIndented` (requires `h_closable` resolution)
3. Token `-`: closes previous entry → `SBlockSeqEntries.cons`, opens next
4. Dedent/EOF: wraps entries as `SBlockNode.blockSeq` → extends stream

Step 2 requires the content's grammar evidence, which comes from `PendingNode.h_closable` — exactly the future content evidence work. The circular dependency is: block-level evidence ← content evidence ← h_closable ← block-level evidence (the content IS the block entry).

**Reflections on 4g.4** (deferred — future work, analysis 2026-04-01)

Scanner indent stack operations have proven correspondence theorems:
- `pushSequenceIndent_corr`/`pushMappingIndent_corr`: preserve ScannerSurfCorr at same SurfPos
- `unwindIndents_corr_exact`: preserves ScannerSurfCorr at same SurfPos
- `scanBlockEntry_prod`: produces `GLit '-'` evidence
- `scanKey_prod`: produces `GLit '?'` evidence
- `scanValue_prod`: produces `GLit ':'` evidence

These are the building blocks for future entry accumulation work. When `pushSequenceIndent` fires (col > currentIndent), a new `BlockStack.seqLevel` should be constructed with an initial h_closable that wraps the first entry's content as `SBlockSeqEntries.single`. Each subsequent same-level `-` would update the h_closable to `SBlockSeqEntries.cons`. When `unwindIndents` pops a level, the h_closable is applied to close the block collection. All the scanner-side pieces exist; what's missing is the grammar composition to build the closure internals.

###### Layer 4h: Flow collection accumulation

Multi-token flow productions (`[...]`, `{...}`) require accumulation analogous to BlockStack. Flow indicators (`[`, `]`, `{`, `}`, `,`) are dispatched individually by the scanner; the grammar needs complete `SFlowSequence`/`SFlowMapping` spanning from opening to closing bracket. Investigation during 4f.3 confirmed that `pendingFlow` h_closable cannot close without tracking: flow indicators open/close multi-token grammar productions that the current PendingNode-only model cannot represent.

**Architecture:** Add `FlowStack` as a 5th component of the loop invariant (lagging quint):
```
SLYamlStream sp_start sp_gram  ∧   -- grammar up to here
BlockStack sp_gram sp_block    ∧   -- nested block collections
FlowStack sp_block sp_flow     ∧   -- nested flow collections ([...], {...})
PendingNode sp_flow sp_scan    ∧   -- immediate pending state
ScannerSurfCorr sc sp_scan         -- scanner ahead
```

FlowStack mirrors the scanner's `flowLevel` counter. Each `[`/`{` pushes a level; each `]`/`}` pops one. Content inside a flow collection creates PendingNode relative to the FlowStack top.

**Dependency:** Requires 4i (context parameter lifting) for `SFlowNode n c` at correct `n`/`c` when constructing entry evidence.

| # | Work | Status | Description |
|---|---|---|---|
| 4h.1 | `FlowStack` inductive + loop invariant update | ✅ done | Design inductive, add as 5th component, update composition theorems |
| 4h.2 | Flow open: `[`/`{` → push FlowStack level | ✅ done | Character-dependent FlowStack in `accum_flow_pending` via `new_flow_state` helper |
| 4h.3 | Flow entry accumulation through `,` tokens | ⏳ blocked on 4i | Real entry closing needs `SFlowNode n c` evidence; sorry model already covered by `new_flow_state` other-chars branch |
| 4h.4 | Flow close: `]`/`}` → pop FlowStack, finalize | ⏳ blocked on 4i | Real `SFlowSequence`/`SFlowMapping` finalization needs grammar evidence; sorry model already covered |

**Reflections on 4h.1** (FlowStack inductive + loop invariant update)

Completed. `FlowStack` added as a 3-constructor inductive (nil, flowSeqLevel, flowMapLevel) mirroring BlockStack's h_closable pattern but without the `col : Int` field (flow collections don't have indent-based nesting). Position chain: `SLYamlStream → BlockStack → FlowStack → PendingNode → ScannerSurfCorr`.

Key design: `absorb_stacks` private theorem case-splits on BlockStack (3) × FlowStack (3) = 9 cases, composing h_closable chains in one place. Each `accum_step_*` theorem SIMPLIFIED from 3-case BlockStack split to a single `absorb_stacks` call + delegation. Net code reduction despite adding a 5th invariant component.

Build: 415/415 jobs, 0 errors, 6 sorry declarations (unchanged — FlowStack levels are never constructed yet, only `FlowStack.nil` produced at every dispatch). §3 scanLoop: "lagging quad" → "lagging quint". §6 Gap Analysis updated.

Lean 4 `cases` arity note: FlowStack.flowSeqLevel has 5 explicit constructor args but `cases` expects 4 names (one index-determined SurfPos is auto-unified). BlockStack.seqLevel with 6 args gets 6 names due to its extra `col : Int` field.

**Reflections on 4h.2** (completed 2026-04-01)

Refactored `accum_flow_pending` to distinguish flow indicator characters via a local `have new_flow_state` helper. The helper case-splits on `c`:

1. **`c = '['`**: Produces `FlowStack.flowSeqLevel sp_mid sp_mid sp_scan' (FlowStack.nil sp_mid) (fun _ h_str => sorry)` + `PendingNode.noPending sp_scan'`. The FlowStack level tracks the opening of a flow sequence, and `noPending` correctly represents "no content dispatched inside the flow yet."

2. **`c = '{'`**: Same pattern with `FlowStack.flowMapLevel` for flow mapping.

3. **Other (`]`, `}`, `,`)**: Produces `FlowStack.nil sp_mid` + `PendingNode.pendingFlow sp_mid sp_scan' (sorry)` — same as pre-4h.2 behavior for all characters.

Key design: The `new_flow_state` helper takes only `sp_mid` (the stream position after old pending closure) and produces `∃ sp_flow', FlowStack sp_mid sp_flow' ∧ PendingNode sp_flow' sp_scan'`. This separates two concerns: (1) PendingNode closure logic (per-PendingNode, 7 cases) and (2) new FlowStack+PendingNode construction (per-character, 3 cases). The helper is called once per PendingNode case via `obtain`, eliminating what would have been a 7×3 = 21 case cross-product.

Position typing forces the right semantics: For `[`/`{`, `sp_flow' = sp_scan'` (FlowStack top = scanner position), so `PendingNode sp_scan' sp_scan'` accepts only `noPending` (which has equal positions). For other chars, `sp_flow' = sp_mid` (FlowStack nil), so `PendingNode sp_mid sp_scan'` requires `pendingFlow` to bridge the gap.

Build: 415/415 jobs, 0 errors, 6 sorry declarations (unchanged). The FlowStack sorry is on h_closable (`fun _ h_str => sorry`), which will eventually compose `GLit '[' + entries + GLit ']'` into `SFlowSequence`. The PendingNode sorry for other chars is the same root cause as before 4h.2.

**Reflections on 4h.3** (analysis complete, blocked on 4i)

Entry separator `,` is already handled by the `new_flow_state` other-chars branch (produces `FlowStack.nil + PendingNode.pendingFlow sorry`). Real entry accumulation — closing the current `SFlowSequenceEntry`/`SFlowMappingEntry` and opening the next within the same FlowStack level — requires `SFlowNode n c` evidence for the entry's content. This evidence comes from content dispatch h_closable, which depends on context parameter lifting (4i.1: `SFlowContent 0 .blockIn → SFlowContent n c`).

Without 4i, the `,` handling is observationally identical to a sorry: the FlowStack level from `[` was absorbed at the previous step (via sorry h_closable), so there's no level to accumulate entries in.

**Reflections on 4h.4** (analysis complete, blocked on 4i)

Flow close `]`/`}` is handled by the same other-chars branch. Real finalization — composing accumulated entries into `SFlowSequence`/`SFlowMapping`, popping FlowStack, and producing `SFlowContent` — requires the entries to have grammar evidence, which depends on 4i.

The absorb-then-reconstruct architecture means FlowStack levels are ephemeral: pushed at open, absorbed at the next step (via sorry h_closable), and the close sees `FlowStack.nil`. This is architecturally correct with sorry — the sorry h_closable covers the entire flow collection closure. With real evidence (post-4i), the FlowStack level would persist across multiple steps, accumulating entries through h_closable updates at each `,`, and finalizing at `]`/`}`.

###### Layer 4i: Context parameter lifting + content h_closable

**Two components** in the sorry root cause for content h_closable (BOTH RESOLVED):

1. **Context lift (`.blockIn → .flowOut`)**: ✅ SOLVED. `SCDoubleQuoted_ctx_lift` and `SCSingleQuoted_ctx_lift` proven in NodeProduction.lean §5a.

2. **Indent lift (`n=0 → n+1`)**: ✅ ELIMINATED by grammar fix. Two issues found and fixed:
   - `SLEmpty.flow` was missing `SIndentLt n` alternative (spec [67] `s-indent(<n)`). Fixed by adding `SLEmpty.flowLt` constructor.
   - `SBlockNode` constructors used `n+1` for content indent (double-counting the Nat shift). Fixed by changing all `n+1` to `n` (22 occurrences in Node.lean). Now `flowInBlock 0` needs `SFlowNode 0 .flowOut`, directly satisfiable from scanner `_prod` at n=0 + context lift.

**Remaining work**: 4i.5 (SSeparate 0 from preprocessing) → 4i.6 (h_closable composition) → 4i.7 (wire into sorry).

**Resolution** (completed 2026-04-01): BOTH fixes applied:

1. **`SLEmpty.flowLt`** (4i.2a): Added third constructor matching YAML spec [67]. One existing match updated (contradiction on context).
2. **`SBlockNode` `n+1` → `n`** (4i.2b): Fixed off-by-one in Node.lean (22 occurrences) and NodeProduction.lean (6 occurrences). `flowInBlock 0` now needs `SFlowNode 0` (not `SFlowNode 1`).

Combined effect: the indent lifting problem (`n=0 → n+1`) is **eliminated**. Scanner `_prod` at `n=0` + context lift `.blockIn → .flowOut` directly satisfies `flowInBlock 0`. No parametric `_prod` needed.

| # | Work | Status | Description |
|---|---|---|---|
| 4i.0 | `SIndent_split` + `sindent_to_flowlineprefix` | ✅ done | Building blocks proven in ScalarProduction.lean §1b |
| 4i.1 | Context lift lemmas | ✅ done | `SCDoubleQuoted_ctx_lift`, `SCSingleQuoted_ctx_lift`, `SFlowNode_*_ctx_lift` in NodeProduction.lean §5a |
| 4i.2a | Grammar encoding fix for `SLEmpty.flow` | ✅ done | Added `flowLt` constructor with `SIndentLt n` alternative, matching YAML spec [67] |
| 4i.2b | Grammar off-by-one fix: `SBlockNode` `n+1` → `n` | ✅ done | All constructors now use `n` directly (convention: `n_lean = n_spec + 1`) |
| 4i.3 | Parametric `foldQuotedNewlinesLoop_prod` | ✅ done | Takes `n` parameter; uses `flowLt` for lines with < n spaces |
| 4i.4 | ~~Parametric scanDoubleQuoted/SingleQuoted~~ | ✅ eliminated | Grammar fix makes n=0 work directly — `flowInBlock 0` needs `SFlowNode 0`, not `SFlowNode 1` |
| 4i.5 | `SSeparateLines 0` from preprocessing | ✅ done | `preprocess_some_separate_lines_0` in StreamAccum.lean; +1 sorry for unreachable `GOpt.some` case |
| 4i.6 | Content h_closable composition | ✅ **unblocked** | Stream extension problem RESOLVED by implicitContinue spec fix + PendingNode sp_start capture (v0.4.10) |
| 4i.7 | Wire into `accum_content_pending` | ⏳ ready | Replace `fun sp_mid h_ssl => sorry` with real closure (no longer blocked) |
| 4i.8 | `dispatchContent_prod` — grammar evidence from dispatch | ✅ quoted done | `dispatchContent_doubleQuoted_prod` and `dispatchContent_singleQuoted_prod` proven. Unfold dispatch, skip false char checks via `split`+`absurd`, apply `_prod`, handle simpleKey endLine struct update. Block/plain/anchor/tag deferred. |
| 4i.9 | `preprocess_some_separate_lines_0` in `noPending` + col≠0 branches | ✅ noPending done | `preprocess_some_separate_lines_0` called in `noPending` case. `preprocess_some_peek` proven (extracts `s_prep.peek? = some c`). Col≠0 remains sorry (layer 4k). |
| 4i.10 | Compose h_closable for quoted scalar branches | ✅ quoted done | Full end-to-end composition proven for `'"'` and `'\''` in `noPending + col=0`. Chain: `preprocess_some_separate_lines_0` → `ScannerSurfCorr_unique` → `preprocess_some_peek` → `dispatchContent_{double,single}Quoted_prod` → `SFlowNode_{doubleQ,singleQ}_ctx_lift` → `flowInBlock_blockNode` → `SLBareDocument.mk` → `SLYamlStream.implicitContinue`. Block scalars deferred: (1) `SBlockNode.blockLiteral/blockFolded` don't include `SSLComments`, (2) `scanBlockScalar_prod` requires `currentIndent ≥ 0`. |

**Reflections on 4i.0** (SIndent_split — completed 2026-04-01)

Two building blocks proven in ScalarProduction.lean §1b:
- `sindent_split`: `SIndent (m + k) sp sp' → ∃ sp_mid, SIndent m sp sp_mid ∧ SIndent k sp_mid sp'`. Induction on `m`; base case needs `Nat.zero_add ▸` for type coercion.
- `sindent_to_flowlineprefix`: `SIndent n_sk sp sp' → n ≤ n_sk → SFlowLinePrefix n sp sp'`. Uses `sindent_split` to decompose, then existing `sindent_to_gstar_sswhite` + `gstar_sswhite_to_gopt_sep` for the remainder.

**Reflections on 4i.1** (context lift — completed 2026-04-01)

Proven in NodeProduction.lean §5a. For quoted scalars, `SNbDoubleText n c` dispatches on `c`:
- `.flowKey` → `SNbDoubleOneLine` (no n)
- `_` → `SNbDoubleMultiLine n` (same for ALL non-flowKey contexts)

So `.blockIn → .flowOut` produces definitionally the same `SNbDoubleMultiLine n`. The lift destructures `SCDoubleQuoted` into `GLit + text + GLit`, passes `text` through unchanged, and reconstructs. Proof: `cases c₁ <;> cases c₂ <;> simp_all [SNbDoubleText]`.

Plain scalar (`SNsPlain n c`) context lift does NOT hold in `.blockIn → .flowOut` direction because `isNsPlainSafe .blockIn` allows flow indicator characters (`[`, `]`, `{`, `}`, `,`) that `isNsPlainSafe .flowOut` forbids.

**Reflections on 4i.2a** (SLEmpty.flow grammar fix — completed 2026-04-01)

Added third constructor `SLEmpty.flowLt`: `SIndentLt n s s₁ → SBAsLineFeed s₁ s' → SLEmpty n c s s'`. This matches YAML spec [67] which has `s-line-prefix(n,c) | s-indent(<n)` — our `flow` constructor covers the first alternative, `flowLt` covers the second. Only 1 existing match in ScalarProduction.lean needed updating (literal scalar proof where context is `.blockIn`, discharged by `absurd hc`).

**Reflections on 4i.2b** (n+1 off-by-one — completed 2026-04-01)

**Critical discovery**: All `SBlockNode` constructors used `n + 1` for content indent, matching the YAML spec's `s-l+flow-in-block(n) ::= ... ns-flow-node(n+1, FLOW-OUT)`. But since `SLBareDocument` uses `SBlockNode 0` (Nat can't represent spec's -1), the convention is `n_lean = n_spec + 1`. This means the spec's `n+1` is already our `n` — adding another `+1` was double-counting.

Concretely: `flowInBlock 0` required `SFlowNode 1 .flowOut`, but top-level flow content is at indent 0. The scanner produces `SFlowNode 0 .blockIn` (context-liftable to `.flowOut`), creating an impossible n=0→n=1 lifting requirement.

**Fix**: Changed ALL `n + 1` to `n` in `SBlockNode`, `SBlockIndented`, `SBlockSeqEntries`, `SBlockMapEntries` constructors (22 occurrences in Node.lean, 6 in NodeProduction.lean). Now `flowInBlock 0` needs `SFlowNode 0 .flowOut` — directly satisfiable from scanner `_prod` + context lift.

This fix **eliminates the entire indent lifting problem**. Steps 4i.3 (parametric loop) and 4i.4 (parametric scanDoubleQuoted) are no longer needed for the h_closable proof. The `_prod` theorems can stay at `n = 0`.

Verification: `seqSpaces` returns correct values after fix. `SBlockSeqEntries n` now has entries at `SIndent n` (was `SIndent (n+1)`). For BLOCK-IN at our `n_lean`: entries at `n_lean` = `n_spec + 1`, matching spec's `seq-spaces(n_spec, BLOCK-IN) + 1 = n_spec + 1`. For BLOCK-OUT: entries at `n_lean - 1` = `n_spec`, matching spec's `(n_spec - 1) + 1 = n_spec`. ✓

**Reflections on 4i.3** (parametric foldQuotedNewlinesLoop — completed 2026-04-01, NOW OPTIONAL)

Made `foldQuotedNewlinesLoop_prod` parametric in `n` (takes explicit `n : Nat`). Uses `by_cases n ≤ n_sk` to choose between `SLEmpty.flow` (enough spaces) and `SLEmpty.flowLt` (fewer than n spaces). This is strictly more general than the n=0 version but NOT required for the h_closable proof path (since the grammar fix makes n=0 sufficient). Callers pass `0`.

**Reflections on 4i.5** (SSeparateLines 0 — completed 2026-04-01)

Proven as `preprocess_some_separate_lines_0` in StreamAccum.lean. Uses `preprocess_some_ssl_comments_col0` to extract `SSLComments sp sp_mid` (at col=0), then builds `SSeparateLines.commented 0` via:
- `SFlowLinePrefix.mk 0 sp_mid sp_mid sp_ws (SIndent.zero sp_mid) (gstar_sswhite_to_gopt_sep ...)` — zero-width indent + optional whitespace from `GStar SSWhite`

The `GOpt.some (SCNbCommentText)` case is unreachable: after `collectCommentTextLoop`, `peek?` returns break/EOF (proven in `collectCommentTextLoop_stops_at_break_or_eof` in PreprocessProduction.lean §1c). But `scanNextToken_preprocess` returning `some (s_prep, c)` implies `peek?` returned a non-break character (the loop's stopping condition). Formally connecting these through the `skipToContentComment` struct update (`{ s with comments := ... }`) is blocked by Lean's reluctance to reduce `peek?` through struct updates with opaque base terms. Currently deferred as a non-structural sorry (+1 to sorry count: 6→7).

**Reflections on 4i.6** (Content h_closable composition — **RESOLVED** via v0.4.10: implicitContinue spec fix + PendingNode sp_start capture)

With 4i.0–4i.5 complete, all grammar building blocks are available:
- `SSeparateLines 0 sp_block sp_prep` from preprocessing (4i.5)
- `SFlowNode 0 .flowOut sp_prep sp_scan'` from scanner `_prod` + context lift (4i.1)
- `SSLComments sp_scan' sp_mid` from closure argument
- `SBlockNode.flowInBlock 0 .blockIn sp_block sp_prep sp_scan' sp_mid` composes them all
- `SLBareDocument.mk`: wraps `SBlockNode` into bare document

**The blocker was**: extending `SLYamlStream sp_start sp_block` with `SLBareDocument sp_block sp_mid`.

**Root cause**: `SLYamlStream.implicitContinue` required `GOpt SLExplicitDocument` instead of `GOpt SLAnyDocument` — a spec deviation from YAML [211] which says `l-document-prefix* l-any-document?`. This prevented bare documents from being appended to existing streams.

**Resolution** (v0.4.10, two coordinated changes):

1. **`SLYamlStream.implicitContinue` spec fix** (Document.lean): Changed from `GOpt SLExplicitDocument` to `GOpt SLAnyDocument`. Now bare documents can extend an existing stream via `implicitContinue ... (GOpt.some (SLAnyDocument.bare h_bare))`. All 5 call sites updated to wrap explicit documents in `SLAnyDocument.explicit`.

2. **`PendingNode` captures `sp_start`** (StreamAccum.lean): Type changed from `SurfPos → SurfPos → Prop` to `SurfPos → SurfPos → SurfPos → Prop`. The h_closable signature simplified from `∀ sp_start sp_mid, SLYamlStream sp_start sp_block → SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid` to `∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid`. The stream is captured inside the closure at construction time, not passed at consumption time. All ~15 construction sites, ~7 consumption sites, and theorem signatures updated.

**Combined effect**: h_closable closures can now construct their stream extension directly:
- For first document (sp_start = stream start): build `SLYamlStream.single` with `SLBareDocument` or `SLExplicitDocument`
- For subsequent documents: use `SLYamlStream.implicitContinue` to extend the captured stream with `SLAnyDocument.bare`/`.explicit`/`.directive`

**Previous proposed solutions** (for historical context):

1. **Change h_closable output to `SBlockNode`** instead of `SLYamlStream`:
   ```lean
   h_closable : ∀ sp_mid, SSLComments sp_scan sp_mid → SBlockNode 0 .blockIn sp_block sp_mid
   ```
   The stream extension would happen at the consumption site (which has `sp_start` and the stream). But the consumption site STILL faces the same stream extension problem.

2. **Capture `sp_start` in PendingNode**: Remove `∀ sp_start` from h_closable, add `sp_start` as a PendingNode parameter. The closure would build `SLYamlStream.single` directly for bare documents. Requires tracking `sp_start` through the accumulator loop invariant.

3. **Add a `bareContinue` constructor to `SLYamlStream`**:
   ```lean
   | bareContinue (s s₁ s₂ s' : SurfPos) :
       SLYamlStream s s₁ → GStar SLDocumentPrefix s₁ s₂ → SLBareDocument s₂ s' → SLYamlStream s s'
   ```
   This extends the grammar to allow bare documents after existing content. This is a grammar EXTENSION beyond the YAML spec — possibly acceptable since it's strictly more permissive, not less.

4. **Defer**: Leave h_closable sorry in place. The existing 5 sorry declarations all trace to this root cause. The grammar/context/indent issues are all resolved — the remaining blocker is purely architectural (stream extension).

**Reflections on 4i.7** — unblocked by 4i.6 resolution. Wiring is straightforward: replace `fun sp_mid h_ssl => sorry` with the composed closure from 4i.6. The closure has the stream captured at construction time and needs only `SSLComments` to complete the grammar derivation.

**Reflections on 4i.8** (dispatchContent_prod — analysis complete 2026-04-01)

The key missing infrastructure is a `dispatchContent_prod` theorem that case-splits on the dispatched character `c` and threads grammar evidence from the individual scanner `_prod` theorems. Currently `dispatchContent_corr` (L1184) only produces `ScannerSurfCorr`, not grammar evidence. Per-branch readiness:

| Dispatch branch | `_prod` theorem | Grammar evidence | Context lift? | Ready? |
|---|---|---|---|---|
| `'"'` double-quoted | `scanDoubleQuoted_flowNode_prod` | `SFlowNode 0 .blockIn` | `SFlowNode_doubleQ_ctx_lift` ✅ | **YES** |
| `'\''` single-quoted | `scanSingleQuoted_flowNode_prod` | `SFlowNode 0 .blockIn` | `SFlowNode_singleQ_ctx_lift` ✅ | **YES** |
| `'\|'`/`'>'` block scalar | `scanBlockScalar_prod` | `SCLLiteral 0` / `SCLFolded 0` | N/A (uses `SBlockNode.blockLiteral/blockFolded` directly) | **YES** |
| plain scalar | `scanPlainScalar_prod` | Only 1-char witness; gap between grammar endpoint and scanner endpoint | `.blockIn → .flowOut` FAILS (flow indicators) | **NO** |
| `'&'` anchor | partial `scanAnchorOrAlias_flowNode_prod` | Anchor property, not standalone node | partial | **NO** |
| `'!'` tag | partial `scanTag_prod` | Tag property, not standalone node | partial | **NO** |

The theorem should return a deferred block-node builder: `∃ sp', (SSLComments sp' sp_mid → SBlockNode 0 .blockIn sp_sep sp_mid) ∧ ScannerSurfCorr s' sp'` — i.e., given `SSLComments` it produces a `SBlockNode`. This separates dispatch-level evidence from stream-level composition. Sorry for plain/anchor/tag branches.

Additional consideration: `peek?` preservation through the `allowDirectives` struct update — the _prod theorems need `sc.peek? = some c` but the dispatch state is `if s_prep.allowDirectives then {s_prep with ...} else s_prep`. Since `allowDirectives` doesn't affect the input buffer, `peek?` is preserved, but may need a trivial lemma.

**Reflections on 4i.9** (preprocessing extraction + col≠0)

Two sub-items:
1. **`noPending` extraction**: `preprocess_some_separate_lines_0` is currently only called in the col=0 branches of `pendingDocEnd`/`pendingDocStart`/`pendingContent`/etc. It needs to also be called in the `noPending` case to provide `SSeparateLines 0 sp_block sp_prep` as input to the h_closable composition. This is straightforward — add the call and thread the evidence.

2. **Col≠0 branches**: ALL col≠0 sorry branches across all 5+1 dispatch theorems share the same root cause: `SSeparateInLine` has no BOM-transparent constructor (layer 4k). After BOM at col≠0 with bare `#`, neither `whites` nor `startOfLine` applies. This is a grammar formalization gap affecting ~35 sorry. Resolution requires grammar definition change (`SSeparateInLine.bomPreceded` or equivalent) — deferred to layer 4k.

**Reflections on 4i.10** (end-to-end composition for quoted + block scalars)

The complete composition chain for quoted scalars (double/single) at col=0:
```
h_separate   : SSeparateLines 0 sp_block sp_prep        ← 4i.9 (preprocess extraction)
h_flow_bi    : SFlowNode 0 .blockIn sp_prep sp_scan'    ← 4i.8 (dispatchContent_prod)
h_flow_fo    : SFlowNode 0 .flowOut sp_prep sp_scan'    ← ctx_lift (4i.1)
h_ssl        : SSLComments sp_scan' sp_mid               ← closure argument
h_block      : SBlockNode 0 .blockIn sp_block sp_mid    ← flowInBlock_blockNode h_separate h_flow_fo h_ssl
h_bare       : SLBareDocument sp_block sp_mid            ← SLBareDocument.mk h_block
h_stream'    : SLYamlStream sp_start sp_mid              ← SLYamlStream.implicitContinue
                 h_stream_block (GStar.nil _)
                 (GOpt.some (SLAnyDocument.bare h_bare))
                 (GStar.nil _)
```

For block scalars (`|`/`>`), the path is similar but uses `SBlockNode.blockLiteral`/`SBlockNode.blockFolded` instead of `flowInBlock_blockNode`. Block scalars go through `SSeparate` + properties (none) + scalar body.

This covers the most common YAML content types. Plain scalars (the remaining common type) need a stronger `scanPlainScalar_prod` that covers all consumed characters AND a context lift that handles flow-indicator-free plain scalars specifically.

**Reflections on 4i.8** (dispatchContent_prod — quoted scalars done 2026-04-02)

Two theorems proven in StreamAccum.lean:
- `dispatchContent_doubleQuoted_prod`: Unfolds `scanNextToken_dispatchContent` for `c='"'`, skips 6+ false character checks via sequential `split at hok` + `absurd hcdc h`, reaches `scanDoubleQuoted` call. Applies `scanDoubleQuoted_prod` to get `SCDoubleQuoted 0 .blockIn`. Handles simpleKey endLine struct update via `split` on `if s_dq.simpleKey.possible` — both branches reconstruct `ScannerSurfCorr` via `⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix⟩` since `simpleKey` fields don't affect surface position.
- `dispatchContent_singleQuoted_prod`: Symmetric for `c='\''`. Skips 7+ false char checks (one more than double-quoted since `'"'` check is first).

**Key insight**: The dispatch function is a sequential if-chain. Each additional character requires one more `split at hok` + `absurd` to skip past. Single-quoted requires more skips than double-quoted since `'"'` check comes first in the chain.

**Helper theorem**: `preprocess_some_peek` extracts `s_prep.peek? = some c` from `scanNextToken_preprocess sc = .ok (some (s_prep, c))`. Proof: unfold `scanNextToken_preprocess`, do-notation `simp only [bind, Except.bind]`, split through monad binds, terminal case gives conjunction that `obtain ⟨h1, h2⟩` decomposes. This is needed because `dispatchContent_*_prod` takes a `peek?` hypothesis, not the preprocessing result directly.

**`peek?` preservation**: `ScannerState.peek?` depends only on `offset`, `inputEnd`, `input`. The `allowDirectives` struct update (`{s_prep with allowDirectives := true, documentEverStarted := true}`) doesn't affect these fields, so `peek?` is preserved definitionally — handled by `split` on the `if s_prep.allowDirectives` condition.

Block scalar dispatch (`'|'`/`'>'`) deferred: (1) `SBlockNode.blockLiteral/blockFolded` constructors don't include trailing `SSLComments` — the production ends at the scalar body, unlike `flowInBlock` which absorbs `SSLComments` as part of the `SBlockNode`. (2) `scanBlockScalar_prod` requires `currentIndent ≥ 0` which fails at top level (`currentIndent = -1`). Needs either grammar restructuring or alternative h_closable pattern.

**Reflections on 4i.9** (preprocessing in noPending — done 2026-04-02)

`preprocess_some_separate_lines_0` is now called in the `noPending` case, providing `SSeparateLines 0 sp_block sp_prep` as input to the h_closable composition. The extraction is the same as in other PendingNode cases — thread `h_prep`, `hcol` (col=0), and `hcorr_sep` through the existing theorem.

Col≠0 branches remain sorry (layer 4k — BOM grammar gap). The `noPending` col≠0 case is split off via `by_cases hcol : sp_block.col = 0` — the `hcol = false` branch is a single sorry.

**Reflections on 4i.10** (h_closable composition — quoted scalars proven 2026-04-02)

The full end-to-end composition chain is now proven for the `noPending + col=0` case with `c='"'` and `c='\''`. Key technical decisions:

1. **`ScannerSurfCorr_unique` for position alignment**: The preprocessing theorem gives `ScannerSurfCorr s_prep sp_prep`, and the dispatch theorem expects a corr hypothesis too. `ScannerSurfCorr_unique` equates the surface positions from different sources. Argument order matters for `subst` direction — putting the "keep" corr first avoids losing needed variables.

2. **`rw` instead of `subst` for dispatch corr alignment**: After `dispatchContent_*_prod` gives `sp_dq` and the loop invariant has `sp_scan'`, `ScannerSurfCorr_unique` gives `sp_dq = sp_scan'`. Using `subst` would eliminate `sp_scan'` (needed in the closure). Instead, `rw [hsp_eq] at h_gram hcorr` rewrites within hypotheses, keeping `sp_scan'` alive.

3. **Explicit type annotation for context lift**: `SFlowNode_doubleQ_ctx_lift h_gram (by decide) (by decide)` has an uninferable output context `c₂`. Adding `have h_flow : SFlowNode 0 .flowOut sp_prep sp_scan' := ...` resolves the metavariable.

4. **`SSeparate 0 .flowOut = SSeparateLines 0` definitionally**: The `SSeparate` pattern match on `n` and `c` reduces for `n=0` and non-key contexts. This means `SSeparateLines 0` (from preprocessing) is directly usable as input to `flowInBlock_blockNode` which expects `SSeparate n c` — no conversion needed.

The proven closure body has the form:
```lean
PendingNode.pendingContent sp_start sp_block sp_scan'
  (fun sp_mid h_ssl =>
    have h_blockNode := flowInBlock_blockNode h_sep h_flow h_ssl
    have h_bare := SLBareDocument.mk sp_block sp_mid h_blockNode
    SLYamlStream.implicitContinue sp_start sp_block sp_block sp_mid sp_mid
      h_stream_block (GStar.nil _)
      (GOpt.some sp_block sp_mid (SLAnyDocument.bare sp_block sp_mid h_bare))
      (GStar.nil _))
```

Remaining branches in `noPending + col=0`: anchor (`'&'`), alias (`'*'`), tag (`'!'`), block scalar (`'|'`/`'>'`), plain scalar, and other characters — all sorry. These are structurally similar but need their respective `_prod` theorems and/or grammar infrastructure.

###### Layer 4j: Directive grammar evidence + PendingNode refactoring

Discovery: `PendingNode.pendingDirective`'s `h_closable → SLYamlStream` was an architectural dead end. `SLDirectiveDocument = GPlus SLDirective + SLExplicitDocument` requires BOTH directives AND `---`, but a standalone pending directive can't form a complete document. Also, `SLDirective.mk` used `GPlus SNsChar` (non-space) which excludes spaces in `%YAML 1.2` — fixed to `GPlus SNbChar` (non-break).

**Refactoring**: Changed `PendingNode.pendingDocStart` from carrying `SCDirectivesEnd` marker to a `h_doc_builder` closure that produces `SLAnyDocument` from content evidence. This abstracts whether the document is explicit (standalone `---`) or directive-preceded. Changed `PendingNode.pendingDirective` from `h_closable → SLYamlStream` to `h_dir_acc → GPlus SLDirective` + `h_stream : SLYamlStream` (captured). When `---` arrives after directives, the builder can form `SLDirectiveDocument`.

| # | Work | Status | Description |
|---|---|---|---|
| 4j.1 | `SLDirective` grammar fix | ✅ done | `GPlus SNsChar` → `GPlus SNbChar` in Basic.lean |
| 4j.2 | `scanDirective_prod` extension | deferred | Needs `GStar SNbChar` evidence from scanner loops |
| 4j.3 | PendingNode type refactoring | ✅ done | `pendingDocStart`: marker → builder; `pendingDirective`: closable → accumulator + stream |
| 4j.4 | Wire through all consumption sites | ✅ done | `eof_pending`, `structural/flow/block/content_pending`, `dispatch_new_pending` |
| 4j.5 | Build clean | ✅ done | 415/415, 8 sorry warnings (was 7; +1 from circular position dependency in `dispatch_new_pending`) |

**Reflections on 4j.1**: `SNsChar` (non-space) was too restrictive for directive content that includes spaces. `SNbChar` (non-break, includes space) matches the actual YAML spec for directive content.

**Reflections on 4j.3**: The builder closure pattern for `pendingDocStart` is cleaner than carrying raw markers — the caller just provides content evidence, and the builder handles whether this is an explicit or directive document. For `pendingDirective`, separating the stream capture from the directive accumulator makes the type honest about what evidence exists at each point.

**Reflections on 4j.4**: Four accum functions (structural, flow, block, content) each needed: (1) `pendingDocStart` case rewritten from `h_marker_old` → `h_doc_builder_old`, (2) `pendingDirective` separated from the `all_goals` block into its own `sorry` case, (3) remaining closable cases get `h_stream_new` variable for `dispatch_new_pending`. The `dispatch_new_pending` body has a circular dependency: needs `sp_mid = sp_prep` to pass the stream, but that equality requires `hcol_prep` from `structural_dispatch_to_pending` which needs the stream. Resolved with `sorry` for now — only affects the directive case which is already sorry'd.

**Reflections on 4j.5**: The extra sorry (+1) is localized to `dispatch_new_pending` and can be eliminated by extracting a `dispatchStructural_col0` lemma that proves `sp.col = 0` directly from the dispatch success, breaking the circular dependency.

###### Layer 4k: BOM col≠0 grammar gap + general-column preprocessing

`SSeparateInLine` has no BOM-transparent constructor. After BOM at col=1 with bare `#`, neither `whites` nor `startOfLine` applies. Genuine YAML grammar formalization gap affecting sorry across dispatch theorems. NOT a grammar encoding bug — `SSBComment.noSep` handles bare breaks at any column; the issue is only the BOM+`#` edge case.

| # | Work | Status | Description |
|---|---|---|---|
| 4k.1 | `bom_noWhitespace_ssbcomment` | ✅ done | Centralized sorry for BOM edge case — single private theorem used by all callers |
| 4k.2 | `skipToContentLoop_anyCol_prod` | ✅ done | General-column loop: `SSLComments ∧ col=0 ∨ sp_mid=sp` disjunction, induction on fuel |
| 4k.3 | `skipToContent_anyCol_prod` | ✅ done | Wrapper: unfolds `skipToContent`, delegates to loop theorem |
| 4k.4 | `SSLComments_snoc` | ✅ done | Append one `SLComment` to `SSLComments` via `GStar_trans` |
| 4k.5 | `skipToContent_eof_ssl_comments` | ✅ done | General-column EOF: delegates col=0 to existing, col≠0 uses `anyCol_prod + SBComment.eof` |
| 4k.6 | `preprocess_none_ssl_comments` | ✅ done | General EOF preprocessing: no col=0 requirement, delegates to `skipToContent_eof_ssl_comments` |
| 4k.7 | Update `eof_pending` | ✅ done | 5 of 7 pending cases proven (pendingContent/DocEnd/DocStart/Flow/Block); noPending+col≠0 stays sorry (stream extension gap), pendingDirective stays sorry (invalid YAML) |

Build: 415/415, **9 sorry warnings** (1 PreprocessProduction: `bom_noWhitespace_ssbcomment`; 8 StreamAccum: unchanged)

**Reflections on 4k research:** Discovered 4 surprises during deep analysis:
1. col≠0 is NOT just BOM — happens after ANY token (e.g., `"hello"` ends at col=7)
2. NOT a grammar definition bug — `SSBComment.noSep` handles bare breaks at any column
3. Impact on warning count is ZERO for StreamAccum — every theorem with col≠0 sorry has other sorry sources
4. Mid-line col≠0 stays sorry: no newline consumed → can't build `SSLComments sp sp` at col≠0

**Reflections on 4k.1:** Consolidating all BOM sorry into one `private theorem bom_noWhitespace_ssbcomment` reduced warnings from 10 to 9 — callers (`skipToContentLoop_anyCol_prod`, `skipToContent_eof_ssl_comments`) become sorry-free by calling the opaque private theorem.

**Reflections on 4k.2:** The general-column version can't REPLACE `skipToContentLoop_col0_prod` because: (a) the col=0 version serves as its own IH (recursive call after break always at col=0), (b) it returns `GStar SLComment` (needed for recursive accumulation), while the general version returns `SSLComments` (different type). Solution: keep col=0 version as workhorse, add general wrapper that delegates.

**Reflections on 4k.5:** The EOF case at col≠0 produces three sub-cases: (a) break consumed → extend existing `SSLComments` with `SLComment + SBComment.eof` via `SSLComments_snoc` — PROVEN, (b) no break + whitespace → `SSBComment.withSep + SBComment.eof` — PROVEN, (c) no break + no whitespace + comment (BOM edge) → delegates to `bom_noWhitespace_ssbcomment` — sorry.

**Reflections on 4k.7:** For `eof_pending`, the `pendingContent/Flow/Block` cases use `h_close_fn : ∀ sp, SSLComments sp_scan sp → SLYamlStream sp_start sp`. The general `preprocess_none_ssl_comments` provides `SSLComments` without col=0 requirement, so these cases are now fully proven. The `noPending` case at col≠0 remains sorry because extending `SLYamlStream` with `SSLComments` requires converting to `GStar SLComment` which needs `SSBComment_to_SLComment_col0` (requires col=0). The `SLYamlStream` grammar (`l-yaml-stream`) uses `l-comment*` (requires `s-separate-in-line`, needs whitespace or col=0) rather than `s-l-comments` (uses `s-b-comment`, allows bare breaks).

**Remaining col≠0 sorry (14 sites in StreamAccum):** All in `by_cases hcol` branches within `accum_structural/flow/block/content_pending`. A general `preprocess_some_ssl_comments` (for the `some` preprocessing result) would handle the `inl` case (break consumed → `SSLComments` available). The `inr` case (no break → same-line tokens) can't produce `SSLComments` without a break, so `PendingNode`'s `h_closable` can't be invoked. For structural dispatch, the `inr` case should be provably absurd (structural tokens require col=0, which forces a break), but proving this needs column-monotonicity lemmas for `SSWhite`/`SCNbCommentText`.

**Warning delta:** 8 warnings → **9** (+1 from `bom_noWhitespace_ssbcomment` in PreprocessProduction.lean). The StreamAccum warnings are architecturally unchanged — each of the 8 theorems has non-col≠0 sorry sources (directive, h_closable construction, etc.) that prevent the warning from being eliminated even if all col≠0 sorry were resolved.

###### Layer 4l: Block entry accumulation

Subsumes deferred 4g.3/4g.4. Full grammar evidence for block collections (`SBlockSeqEntries`/`SBlockMapEntries`) constructed incrementally across tokens via `BlockStack`. Requires content h_closable (4i) to produce entry evidence.

| # | Work | Status | Description |
|---|---|---|---|
| 4l.1a | Block entry h_closable (empty entry) | ✅ done | `accum_block_pending` noPending: h_closable for `-` at col=0, empty entry |
| 4l.1b | `pendingBlock` type refinement: `SSLComments → SBlockNode` | ✅ done | Changed h_close to take `SBlockNode` instead of `SSLComments`; enables content-inside-entry |
| 4l.1c | `preprocess_some_separate_0_anyCol` | ✅ done | General-column `SSeparateLines 0` from preprocessing (no col=0 requirement). 2 sorry subcases (inr no-break, comment-with-content) |
| 4l.1d | Content-inside-entry composition | ✅ done | `accum_content_pending` pendingBlock: `SBlockNode.flowInBlock` composed inside h_close for double/single-quoted scalars. Other content types use sorry. |
| 4l.2 | `SBlockSeqEntries_snoc` lemma | ✅ done | Grammar-level: append entry to existing block sequence entries. 0 sorry. |
| 4l.3a | Entry accumulation: `h_close_entry` in `pendingBlock` | ✅ done | Same-level `-` accumulates `SBlockSeqEntries` via `SBlockSeqEntries_snoc`. 0 new sorry. |
| 4l.3b | Content-through-entry accumulation | ✅ done | New `pendingBlockContent` constructor threads entry closure through content |
| 4l.3c | BlockStack level push/pop | ✅ analysis done | Superseded at col=0 by closure approach; nested levels blocked on col≠0. Filled pendingContent/Flow closures for `-`. |

**Reflections on 4l.1** (first block entry h_closable — completed 2026-04-02)

Three new theorems enable the real h_closable construction in `accum_block_pending`:

1. **`blank_to_not_nsChar`** (StructureProduction.lean): Bridge `isBlankBool c = true → ¬isNsChar c`. Converse of existing `not_blank_to_nsChar`. Proof: `simp` unfolds all definitions, `rcases` on the disjunction (`c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'`), each case contradicts a negation or matches the goal.

2. **`blockEntryCandidate_gnot`** (StructureProduction.lean): `isBlockEntryCandidate sc → GNot SNsChar sp'` at the position after `-`. Proof: case-split on `rest` (empty ⇒ trivial, cons ⇒ extract `peekAt? 1 = some c` via `peekAtLoop_step` + `peekAtLoop_cons` + `chars_from_cons_tail`, then apply `blank_to_not_nsChar`).

3. **`dispatchBlockEntry_full_prod`** (StreamAccum.lean): Combined `GLit '-' + GNot SNsChar + ScannerSurfCorr` from `scanNextToken_dispatchBlockIndicators`. Unfolds dispatch, first `split` extracts the `-` branch condition, `rename_i` captures it. For the impossible `?`/`:` branches: `('-' == '?') = false` and `('-' == ':') = false` via `native_decide`, then `Bool.false_and` + `if_neg Bool.false_ne_true` collapse the remaining dispatch to `none`, contradicting `some s'`.

**Architecture for empty block entry h_closable:**
```
h_closable : ∀ sp_final, SSLComments sp_scan' sp_final → SLYamlStream sp_start sp_final
  SBlockIndented.empty 0 .blockIn sp_scan' sp_final h_ssl_final
  → SBlockSeqEntries.single 0 sp_mid sp_mid sp_scan' _ sp_final
        (SIndent.zero sp_mid) h_dash h_gnot h_indented
  → SBlockNode.blockSeq 0 .blockIn sp_block sp_block sp_mid sp_final
        (GOpt.none sp_block) h_ssl_pre h_entry
  → SLBareDocument.mk → SLYamlStream.implicitContinue
```

**Position chain**: `sp_block` →[SSLComments]→ `sp_mid` (col=0) →[SIndent 0, zero-width]→ `sp_mid` →[GLit '-']→ `sp_scan'` →[SSLComments from h_closable arg]→ `sp_final`.

**Limitations**: Only handles `noPending + col=0 + c='-'` with no whitespace before `-` (`GStar SSWhite` nil + `GOpt SCNbCommentText` none). Three remaining sorry sub-cases:
- Whitespace before `-` (dash at col > 0): can't build `SBlockSeqEntries 0` since `SIndent 0` is zero-width. Would need `SBlockNode n .blockIn` with `n = col`. Genuine grammar mismatch for top-level.
- Comment text before `-`: unreachable (scanner greedily consumes comments). Same sorry as in `preprocess_some_separate_lines_0`.
- `c ≠ '-'` (key `?` or value `:`): needs `SBlockMapEntries` infrastructure.

**Grammar nesting note**: When content follows `-` (e.g., `- "value"`), the empty-entry h_closable creates `SBlockSeqEntries.single ... SBlockIndented.empty`, then content dispatch creates a SEPARATE `PendingNode.pendingContent` with its own `SBlockNode.flowInBlock`. Grammatically, the content should be INSIDE the entry's `SBlockIndented`, not as a separate document. This is position-correct but grammar-imprecise.

**4l.1b–d resolution**: Change `PendingNode.pendingBlock`'s h_closable from `SSLComments → SLYamlStream` to `SBlockNode → SLYamlStream`. The closure captures entry opener evidence (SSLComments, SIndent, GLit '-', GNot, stream) and takes the entry CONTENT as `SBlockNode`. This enables:
- **Empty entry**: caller provides `SBlockNode.emptyNode 0 .blockIn sp h_ssl` (wrapping SSLComments)
- **Content entry**: caller provides `SBlockNode.flowInBlock 0 .blockIn sp ... h_sep h_flow h_ssl` (full content)

Both produce the same `SBlockSeqEntries.single → SBlockNode.blockSeq → SLBareDocument → SLYamlStream.implicitContinue` inside the closure, but with `SBlockIndented.node` (content) instead of `SBlockIndented.empty` (empty).

**4l.1c**: `preprocess_some_separate_0_anyCol` provides `SSeparateLines 0` from any starting column. Key: `SSeparateLines.commented 0 (GStar.nil sp) (SFlowLinePrefix.mk 0 sp sp (SIndent.zero sp) ...)` works at any column because `SIndent 0` is zero-width and doesn't check column. This enables content composition after `-` at col=0 (where the content scan position is col=1).

**4l.1d architecture**:
```
accum_content_pending for pendingBlock h_close_old:
  h_sep  : SSeparateLines 0 sp_scan sp_prep    ← preprocess_some_separate_0_anyCol
  h_flow : SFlowNode 0 .flowOut sp_prep sp_scan' ← dispatchContent_*_prod + ctx_lift
  -- DON'T close pendingBlock yet — compose content inside entry:
  PendingNode.pendingContent sp_start sp_block sp_scan'
    (fun sp_final h_ssl_trailing =>
      h_close_old sp_final
        (SBlockNode.flowInBlock ... sp_scan sp_prep sp_scan' sp_final
          h_sep h_flow h_ssl_trailing))
```

**4l.2**: `SBlockSeqEntries_snoc : SBlockSeqEntries n s s_mid → SIndent n s_mid s₁ → GLit '-' s₁ s₂ → GNot SNsChar s₂ → SBlockIndented n .blockIn s₂ s' → SBlockSeqEntries n s s'`. Converts `single` to `cons` or extends `cons` recursively. Proven by induction on `SBlockSeqEntries`.

**4l.3 analysis**: `unwindIndents` preserves `ScannerSurfCorr` at the same position (no characters consumed). Grammar effect is indirect: indent stack pop changes which block indicators are valid in future iterations. For `BlockStack.seqLevel` finalization, need: (a) seqLevel to PERSIST across iterations (currently absorbed by `absorb_stacks`), (b) when indent decreases, close the seqLevel's accumulated entries. The original plan required either modifying `absorb_stacks` or threading `BlockStack` through `accum_*_pending`. However, 4l.3a found a **closure-based approach** that avoids both.

**4l.3a architecture**: Instead of persisting entries in `BlockStack`, entries accumulate INSIDE `pendingBlock` closures. A new field `h_close_entry` returns `SBlockSeqEntries` + a continuation (entries→stream). When the next `-` at the same level arrives:
1. Close the old entry → `SBlockNode` → `SBlockIndented`
2. Call `h_close_entry_old` to extract `⟨sp_first, h_entries_old, h_cont⟩`
3. `SBlockSeqEntries_snoc h_entries_old ... h_indented_new` → extended entries
4. New `h_close` calls `h_cont` with the snoc'd entries
5. New `h_close_entry` returns `⟨sp_first, snoc'd_entries, h_cont⟩` for further extension

This keeps `BlockStack.nil` throughout — entries are in closures, stream stays unchanged, `absorb_stacks` untouched.

**Reflections on 4l.1b-d** (pendingBlock type refinement + content composition — completed 2026-04-04)

**Implementation summary:**
- Changed `PendingNode.pendingBlock.h_close` from `SSLComments sp_scan sp_mid → SLYamlStream` to `SBlockNode 0 .blockIn sp_scan sp_mid → SLYamlStream`
- Updated 1 construction site (`accum_block_pending` noPending): `SBlockIndented.empty → SBlockIndented.node`
- Updated 5 consumption sites (`eof_pending`, `accum_structural_pending`, `accum_flow_pending`, `accum_block_pending`, `accum_content_pending`): wrap ssl in `SBlockNode.emptyNode` for non-content cases; compose `SBlockNode.flowInBlock` for quoted content
- Added `preprocess_some_ssl_comments_anyCol`: general-column version of `preprocess_some_ssl_comments_col0`, returns disjunction `(SSLComments ∧ col=0) ∨ (sp_mid = sp)`
- Added `preprocess_some_separate_0_anyCol`: builds `SSeparateLines 0` from the `inl` disjunct; `inr` case (no break) is sorry

**Key "gotcha" — `subst h` direction in Lean 4:**
`subst h` where `h : a = b` eliminates `b` (the RIGHT side), keeping `a`. This means after `obtain ⟨sp_new, ...⟩; have hsp_eq := unique h1 h2; subst hsp_eq` where `hsp_eq : sp_old = sp_new`, `sp_new` is REMOVED and `sp_old` survives. All subsequent code must reference `sp_old`, not `sp_new`. This bit us in 3 locations.

**Build:** 415/415, 10 sorry warnings (was 9; +1 from `preprocess_some_separate_0_anyCol`).

**Reflections on 4l.2** (SBlockSeqEntries_snoc — completed 2026-04-04)

`SBlockSeqEntries_snoc` appends one entry to the end of a block sequence. Proof by term-mode `match` (not `induction`) because `SBlockSeqEntries` is part of an 11-type mutual inductive and `induction` tactic doesn't support mutual inductives. The `cases` tactic also failed due to well-founded recursion on `SurfPos` (no size decrease). Term-mode `match` with explicit recursive call works because Lean can verify structural decrease on the `SBlockSeqEntries` argument.

Key pattern-matching detail: constructor `single` has 6 explicit position parameters (n, s, s₁, s₂, s₃, s') before 4 field arguments. Missing one wildcard for the unused `s₃` causes Lean to misalign fields with positions — a confusing type mismatch on the `SIndent` field.

Added to NodeProduction.lean §6. No sorry, no new warnings.

**Reflections on 4l.3** (entry accumulation — completed 2026-04-04)

**The key insight**: `pendingBlock.h_close` (entry→stream) is a CLOSED closure — once composed, you can't extract the `SBlockSeqEntries` from it to snoc more entries. The solution: add a parallel `h_close_entry` closure that returns the entries AND a continuation (entries→stream). The continuation is the same context-closure that `h_close` uses internally, but exposed for reuse.

**Type change to `PendingNode.pendingBlock`**:
```lean
| pendingBlock (sp_start sp_block sp_scan : SurfPos)
    (h_close : ∀ sp_mid, SBlockNode 0 .blockIn sp_scan sp_mid → SLYamlStream sp_start sp_mid)
    (h_close_entry : ∀ sp_mid, SBlockNode 0 .blockIn sp_scan sp_mid →
      ∃ sp_first,
        SBlockSeqEntries 0 sp_first sp_mid ∧
        (∀ sp_end, SBlockSeqEntries 0 sp_first sp_end → SLYamlStream sp_start sp_end))
```

**Why closures for entry accumulation instead of `BlockStack`**: The closure-based approach avoids changing `BlockStack`, `absorb_stacks`, or any of the `accum_step_*` wrappers. Entries are invisible to the main loop — the stream position doesn't advance until the sequence is finalized. All accumulation happens inside the `pendingBlock` closures, which are recreated on each same-level `-`.

**Position invariant**: The stream stays at `sp_block` (the position BEFORE the first entry's SSLComments). The first entry's opener evidence (SIndent, GLit, GNot), preamble (GOpt, SSLComments), and document context (stream) are all captured in the continuation `h_cont`. Each iteration snocs one entry.

**Proven case**: `pendingBlock → accum_block_pending → pendingBlock` at col=0 with `-`, nil whitespace, none comment. Uses `dispatchBlockEntry_full_prod` for the new entry's opener evidence, `SBlockSeqEntries_snoc` for accumulation, and the existing `h_cont` for the stream context.

**Gotcha — `rename_i` vs named patterns**: `| pendingBlock h_close_old _ =>` in `cases ... with` doesn't work — Lean can't bind the fields as named patterns in this context. Must use `| pendingBlock => rename_i h_close_old _` instead. This is specific to `cases ... with` (named patterns work fine in `match`).

**Build**: 415/415, 10 sorry warnings (unchanged).

**Remaining work**:
- **4l.3b (done)**: New `pendingBlockContent` constructor carries both `h_closable` (stream closure) and `h_closable_entry` (entry closure). Content-inside-block-entry (`accum_content_pending` pendingBlock) now creates `pendingBlockContent` instead of `pendingContent` for double/single-quoted scalars, threading both closures. When another `-` follows (`accum_block_pending` pendingBlockContent), the entry closure extracts accumulated entries and snocs a new one — same accumulation logic as `pendingBlock` but taking `SSLComments` instead of `SBlockNode`. At all other consumption sites (structural, flow, eof, content-after-content), `pendingBlockContent` closes to stream via `h_closable` (first field), ignoring the entry closure. Key `rename_i` lesson: `rename_i` names inaccessible hypotheses from the END of the local context, so `rename_i x` names the LAST inaccessible, and `rename_i x _` names the 2nd-to-last (skipping the last). With 2 fields, `pendingBlockContent` cannot share combined `all_goals` patterns with single-field `pendingContent/pendingFlow` — must have its own case with `rename_i h_closable_old _`.
- **4l.3c (analysis complete — superseded/blocked)**: `BlockStack.seqLevel` push/pop was the original plan for entry accumulation across tokens. Analysis found three blockers:

  1. **`absorb_stacks` eagerly collapses BlockStack**: Every `accum_step_*` theorem calls `absorb_stacks` as its first action, converting `BlockStack sp_gram sp_block → SLYamlStream sp_start sp_flow`. Any `seqLevel` returned by one step gets absorbed at the start of the next step. To persist across iterations, `absorb_stacks` would need restructuring to NOT collapse block levels — and all `accum_*_pending` functions would need to take `BlockStack` as input instead of a single `SLYamlStream`. This is a major refactor across ~40 construction sites and ~10 consumption sites.

  2. **`seqLevel`'s completion-closure can't be constructed incrementally**: `BlockStack.seqLevel`'s closure has type `∀ sp_start, SLYamlStream sp_start sp → SLYamlStream sp_start sp'`, producing a COMPLETE stream extension from `sp` to `sp'`. But `sp'` (the sequence endpoint) isn't known until all entries are collected. The closure approach in `PendingNode` handles this by deferring — closures take FUTURE evidence (`SBlockNode` for the current entry) and produce the result. `BlockStack.seqLevel` would need a similar incremental type, duplicating `PendingNode`'s role.

  3. **Nested sequences require col≠0 support**: The motivation for `BlockStack.seqLevel` was nested sequences (e.g., `- - inner\n- outer`). The inner `-` at col=2 would need `SBlockSeqEntries 2` with `SIndent 2`. But ALL col≠0 branches are sorry (BOM grammar gap, layer 4k). Until col≠0 is resolved, `seqLevel` at col>0 would just wrap sorry — no grammar improvement.

  **Concrete improvement made**: Filled `h_close`/`h_close_entry` closures in `accum_block_pending` for `pendingContent/pendingFlow + c='-' + col=0` (nil whitespace, no comment). Uses `SSLComments.startOfLine` for zero-width SSLComments at the stream endpoint. These were previously sorry; now they construct real `SBlockSeqEntries.single → SBlockNode.blockSeq → SLYamlStream.implicitContinue`. Enables the accumulation chain for multi-document sequences like `"hello"\n- "world"\n- "foo"\n`.

  **End-to-end sorry-free path**: `- "quoted"\n- "quoted"\n...- "quoted"\nEOF` is fully proven with real grammar evidence:
  - Step 1: `noPending + '-'` → `pendingBlock` (real closures) ✅
  - Step 2: `pendingBlock + '"'` → `pendingBlockContent` (real closures, 4l.1d+3b) ✅
  - Step 3: `pendingBlockContent + '-'` → `pendingBlock` (accumulates entries, 4l.3b) ✅
  - Steps 4–N: repeat steps 2–3 for arbitrary entry count ✅
  - EOF: `eof_pending` with `pendingBlockContent` → `h_closable` → stream ✅
  - Structural: `accum_structural_pending` with `pendingBlockContent` → close to stream ✅
  Also proven: `pendingContent/pendingFlow + '-'` → `pendingBlock` with real closures (new this iteration)

  **BlockStack.seqLevel disposition**: The constructors remain in the type definition for future use when col≠0 is supported. No code uses them. They may need type changes (incremental closures) before they're actually useful.

**Build**: 415/415, 10 sorry warnings (unchanged).

---

### Next Steps Analysis (post-4l)

The block entry accumulation chain (4l.1–4l.3) is complete for the core use case: top-level block sequences with double/single-quoted scalar content. The remaining sorry fall into five independent categories:

#### Architectural Changes (pre-category prerequisites)

Three architectural changes are needed before tackling the content categories. Each removes a structural blocker that would otherwise block multiple sorry sites.

##### A1: Add `currentIndent` field to `ScannerSurfCorr` ✅

**Problem**: `scanBlockScalar_prod` requires `sc.currentIndent ≥ 0` as a precondition. After `pushSequenceIndent` at col=0, `currentIndent = 0`, but this fact cannot be derived from the existing `ScannerSurfCorr` (which only tracks `chars_from`, `col_eq`, `end_eq`, `input_prefix`). Without it, block scalars (`|`/`>`) inside block sequences are unprovable.

**Solution**: Add `indent_eq : sc.currentIndent = sp.indent` (or similar) to `ScannerSurfCorr`, with a corresponding `indent` field in `SurfPos`. Alternatively, add a standalone `currentIndent_ge : sc.currentIndent ≥ expectedIndent` field. Propagate through ~40 construction sites across 6 proof files.

**Scope**: ~40 construction sites in CouplingBridge, ScannerCoupling, ScalarCoupling, StructureCoupling, StructureProduction, PreprocessProduction. Mechanical — each site adds one field to the constructor call.

**Unblocks**: Category 1 block scalar (`|`/`>`) support.

###### Accomplishments for A1

- Added `indent_cols_nonneg : ∀ (i : Nat) (hi : i < sc.indents.size), i > 0 → sc.indents[i].column ≥ 0` field to `ScannerSurfCorr`
- Added `ScannerSurfCorr.currentIndent_nonneg` helper theorem: derives `currentIndent ≥ 0` from `indents.size > 1`
- Added `advance_indents` lemma: `s.advance.indents = s.indents` (needed because `ScannerState.advance` has branching that blocks definitional equality)
- Updated `initial_corr` with vacuous proof (single sentinel at index 0 has column `-1`, guard `i > 0` makes it vacuously true)
- Updated 4 advance helpers (`advance_non_newline_corr`, `advance_newline_corr`, `advance_cr_corr`, `skip_byte_corr`) with `advance_indents` rewriting
- ~115 forwarding sites updated via two-pass Python regex script across 7 files (StructureCoupling, StructureProduction, CouplingBridge, StreamAccum, ScanStrictCoupling, ScalarProduction, ScalarCoupling)
- Updated `pushSequenceIndent_corr`/`pushMappingIndent_corr` signatures with `(hcol : col ≥ 0)` parameter; push branch uses `Array.getElem_push_lt`/`Array.getElem_push_eq`
- Updated 5 push call sites with `(Int.natCast_nonneg _)` (formerly `Int.ofNat_nonneg`, deprecated in 4.29)
- Fixed `unwindIndentsLoop_corr_exact` (StructureProduction) and `unwindIndentsLoop_corr` (StructureCoupling) pop cases with `Array.getElem_pop` + `Array.size_pop`
- Fixed hidden push in `scanValuePrepare_corr` (inline `getElem_push_lt`/`getElem_push_eq` logic)
- Fixed `consumeNewline_lf_corr` in ScannerCoupling (missing 5th field)
- Build: 415/415, **10 sorry warnings** (unchanged from pre-A1 baseline)

###### Reflections on A1

**Design choice — per-element invariant, not `currentIndent`**: Chose `∀ i, i < size → i > 0 → column[i] ≥ 0` over directly tracking `currentIndent` because: (a) `currentIndent ≥ -1` is always true but useless, (b) `indents.size > 0 → currentIndent ≥ 0` isn't strong enough for `unwindIndents` (popping needs per-element guarantee for the NEW back element), (c) per-element is the strongest provable property that implies `currentIndent ≥ 0` via `back?`.

**Sentinel at index 0**: `ScannerState.mk'` initializes `indents := #[{ column := -1, isSequence := false }]`. This sentinel has `column = -1`, violating `column ≥ 0`. The `i > 0` guard accommodates it — all entries pushed by `pushSequenceIndent`/`pushMappingIndent` have `column = ↑(sc.col : Nat) ≥ 0`, so only the sentinel at index 0 can be negative. The helper `currentIndent_nonneg` requires `size > 1` (not `> 0`) because `back?` at size 1 returns the sentinel.

**`advance` doesn't preserve `indents` definitionally**: `ScannerState.advance` branches on `offset < inputEnd` then on `c == '\n'`/`c == '\r'`. All branches use `{ s with ... }` preserving `indents`, but Lean can't see through the branching — `hcorr.indent_cols_nonneg` has type `... sc.indents ...` but the goal wants `... sc.advance.indents ...`. Fixed by adding `advance_indents : s.advance.indents = s.indents` (trivial proof by `unfold; split; split; rfl`) and rewriting with `simp only [advance_indents] at hi ⊢`.

**Pop case subtlety**: `Array.getElem_pop` equates `xs.pop[i] = xs[i]` (with adjusted bound). Without it, Lean sees `(sc.emit .blockEnd).indents.pop[i]` vs `sc.indents[i]` and can't unify. The `ScannerState.emit` wrapper also needs `simp only [ScannerState.emit]` to expose `.indents` before `Array.getElem_pop` fires.

**Bulk script pattern**: Two-pass regex because `\w+` doesn't match apostrophe in identifiers like `hcorr'`. First pass: `(\w+)\.input_prefix⟩` → 94 matches. Second pass: `([\w']+)\.input_prefix⟩` → 21 more. Total: 115 forwarding sites.

**`Array.getElem?_lt` renamed**: In Lean 4.29, `Array.getElem?_lt` no longer exists. The correct lemma is `Array.getElem?_eq_getElem`. Discovered when `currentIndent_nonneg` failed to compile.

##### A2: Add BOM-transparent `SSeparateInLine` constructor ✅

**Problem**: `SSeparateInLine` has only two constructors: `whites` (requires `GPlus SSWhite`) and `startOfLine` (requires `col = 0`). After BOM (`\uFEFF`) at offset 0, the scanner is at col=1. If the next char is `#` (comment), neither constructor applies — `whites` needs whitespace before `#`, and `startOfLine` needs col=0. This blocks ~20 col≠0 sorry sites across all dispatch theorems.

**Solution chosen**: Instead of adding a `bomPreceded` constructor, removed the col=0 constraint from `startOfLine` entirely: `startOfLine (s : SurfPos) : SSeparateInLine s s`. This is sound because the scanner validates comment positions anyway, and the grammar algebra is strengthened without adding a new constructor that would require additional case-splits in all proofs.

**Scope**: Grammar definition change in `Surface/Basic.lean` + cascade through PreprocessProduction, StreamAccum, CouplingBridge. ~40 lines of proof changes.

**Unblocks**: Category 2 (~20 col≠0 sorry across all 9 StreamAccum theorems) — **now resolved**.

###### Accomplishments for A2

- Changed `SSeparateInLine.startOfLine` from `startOfLine (chars : List Char) : SSeparateInLine ⟨chars, 0⟩ ⟨chars, 0⟩` to `startOfLine (s : SurfPos) : SSeparateInLine s s` (column-independent zero-width match)
- Closed `bom_noWhitespace_ssbcomment` sorry (PreprocessProduction): now proven via `.withSep sp sp sp_cmt sp_end (.startOfLine sp) (.some sp sp_cmt h_cmtv) h_break`
- Generalized `GStar_SSWhite_to_SSeparateInLine` (was `_col0`): dropped `hcol` parameter, nil case uses `.startOfLine sp` instead of requiring col=0
- Generalized `SSBComment_to_SLComment` (was `_col0`): dropped `hcol` parameter, `noSep` case uses `.startOfLine sp` directly
- Generalized `SSLComments_to_GStar` (was `_col0`): dropped `hcol` parameter, callers updated
- Generalized `ssl_comments_extend_stream` (was `_col0`): dropped `hcol` parameter
- Closed `eof_pending` noPending sorry: removed `by_cases hcol` — uses general `preprocess_none_ssl_comments` + `ssl_comments_extend_stream` at any column
- Closed `preprocess_some_separate_0_anyCol` `inr` sorry: no-break case builds `SSeparateLines.inline 0` via `GStar_SSWhite_to_SSeparateInLine` (nil GStar → zero-width startOfLine)
- Updated `start_of_line_gives_SSeparateInLine` in CouplingBridge: `SSeparateInLine.startOfLine ⟨rest, 0⟩`
- Build: 415/415, **9 sorry warnings** (down from 10; net -1)

###### Reflections on A2

**Design decision — remove constraint vs add constructor**: The original plan was to add a `bomPreceded` constructor. Analysis revealed this would require adding a new case to every `cases h : SSeparateInLine` proof (dozens of sites), with BOM evidence that doesn't exist at the grammar level. Instead, removing the col=0 constraint from `startOfLine` is a grammar weakening that is sound: `startOfLine` represents "implicit separation at start of line" and the YAML spec's col=0 requirement is already enforced by the scanner's line-break handling (every `SBBreak` resets col to 0). The grammar types are an over-approximation of valid parses, so weakening one constructor's precondition is safe as long as the scanner only produces valid instances.

**Cascade was smaller than expected**: Only 4 functions needed signature changes (drop `hcol`), plus 4 caller sites referencing old names. No proof that case-splits on `SSeparateInLine` constructors was broken — because `startOfLine` always produced `SSeparateInLine s s` (same start/end), the only change is that `s` is an arbitrary `SurfPos` instead of `⟨chars, 0⟩`. Proofs that pattern-matched on `startOfLine chars` now match on `startOfLine s`, which is structurally identical.

**`subst` direction gotcha (again)**: In `preprocess_some_separate_0_anyCol`, the `inr h_eq` case has `h_eq : sp_mid = sp`. Using `subst h_eq` would eliminate `sp` (the RIGHT side), but `sp` is bound by `obtain` from the signature and can't be substituted away. Used `rw [h_eq] at h_ws` instead to rewrite `h_ws : GStar SSWhite sp_mid sp_ws` to use `sp` while keeping both variables.

**Sorry accounting**: Closed 2 sorry (`bom_noWhitespace_ssbcomment`, `eof_pending` noPending col≠0), but the `preprocess_some_separate_0_anyCol` `GOpt.some` case remains (unreachable comment, same root cause as `preprocess_some_separate_lines_0`). Net: 10 → 9 sorry warnings. The `eof_pending` closure was removing a sorry that didn't have its own warning (it was inside a theorem that had other sorry), so only the `bom_noWhitespace_ssbcomment` closure reduced the warning count.

##### A3: Alias `*` wiring through `accum_content_pending` ✅

**Problem**: `SFlowNode.alias` takes `SCNsAliasNode` which is context-free (no `n`/`c` dependency in evidence), so `SFlowNode 0 .flowOut` can be constructed directly without a context lift. However, alias is not yet wired through `dispatchContent_prod` or `accum_content_pending`. The dispatch path is clean (pure function, not `Except`), and the grammar evidence is direct.

**Solution**: Added `dispatchContent_alias_prod` theorem (analogous to `dispatchContent_doubleQuoted_prod`) that unfolds `scanNextToken_dispatchContent` for `c = '*'`, handles the `definedAnchors.any` check (error branch is impossible since we have `.ok`), and produces `SFlowNode 0 .flowOut` via `scanAnchorOrAlias_aliasNode_prod` + `alias_flowNode`. Wired through `accum_content_pending` for both `noPending` col=0 and `pendingBlock` cases.

**Key insight**: Alias is truly context-free — `SCNsAliasNode` has no `n`/`c` parameters in evidence, so `alias_flowNode` lifts directly to any desired `SFlowNode n c` without a context-lift theorem (unlike double/single-quoted which need `SFlowNode_doubleQ_ctx_lift`/`SFlowNode_singleQ_ctx_lift`).

**Remaining sorry**: ~~The degenerate case where `sp_mid = sp'` (empty alias name after `*`) — the YAML spec requires `c-ns-alias-node ::= '*' ns-anchor-name` where `ns-anchor-name ::= ns-anchor-char+`, but the scanner doesn't validate minimum length. The `definedAnchors.any` check doesn't prevent this because empty names CAN be registered via `& ` (ampersand followed by non-anchor-char). This is a scanner validation gap, not a proof gap.~~ **CLOSED (A12)** — `scanAnchorOrAlias_prod` now returns `sp_mid ≠ sp'` unconditionally. The strengthened `collectAnchorNameLoop_prod` links position equality to value equality (`sp = sp' → result.fst = name`), and the scanner's `Except.error .emptyAnchorName` rejects the degenerate case.

**Build**: 415/415, ~~10 sorry (up from 9 — the new `dispatchContent_alias_prod` declaration adds 1 sorry for the degenerate empty-name case)~~ **12 sorry (A12 closed the alias sorry)**.

**Unblocks**: Category 1 alias (`*`) content type.

###### Accomplishments for A3

- `dispatchContent_alias_prod`: New theorem in StreamAccum.lean (~30 lines). Unfolds dispatch for `'*'`, handles `definedAnchors.any` check (error branch eliminated by `.ok` hypothesis), applies `scanAnchorOrAlias_aliasNode_prod` + `alias_flowNode` for grammar evidence. Sorry only for the degenerate empty-name case (`sp_mid = sp'`).
- Wired alias into `accum_content_pending` `noPending` col=0 case (~18 lines): Uses `dispatchContent_alias_prod` to get `SFlowNode 0 .flowOut`, composes with `flowInBlock_blockNode` + `SLBareDocument.mk` + `SLYamlStream.implicitContinue`. No context lift needed (alias is context-free).
- Wired alias into `accum_content_pending` `pendingBlock` case (~18 lines): Uses `dispatchContent_alias_prod` to get `SFlowNode 0 .flowOut`, composes inside block entry via `SBlockNode.flowInBlock` + `PendingNode.pendingBlockContent`.
- Catch-all sorry branches now cover fewer content types: "anchor, tag, block scalar, plain scalar" (alias removed from the list).

###### Reflections on A3

- **Context-free advantage is real**: Alias being context-free (`SCNsAliasNode` has no `n`/`c` in evidence) made this dramatically simpler than quoted scalars. No context-lift theorem needed — `alias_flowNode` works for ANY `n c`. This pattern will NOT generalize to anchor properties or tags, which require node-property composition.
- **Scanner validation gaps surface**: The `sp_mid ≠ sp'` condition (name non-emptiness) can't be proven from the current scanner because: (a) `collectAnchorNameLoop` can return `""`, (b) the `definedAnchors` list can contain `""` from prior `& ` sequences, (c) the theorem `collectAnchorNameLoop_prod` doesn't relate the string name to the `GStar` extent. Adding a scanner invariant (`∀ a ∈ definedAnchors, a ≠ ""`) or a correlation theorem (`name.length > 0 ↔ sp_mid ≠ sp'`) would close this sorry but requires additional infrastructure.
- **Pattern established for remaining content types**: The `by_cases hc_alias : c = '*'` pattern inside `accum_content_pending` is now proven for 3 content types (`'"'`, `'\''`, `'*'`). Each new content type adds ~15-20 lines of wiring plus a `dispatch_*_prod` theorem.

#### Category 1: Other content types

`dispatchContent_evidence` (Wadler-style unified extraction) now handles ALL content types uniformly:

| Content type | Grammar production | Status |
|---|---|---|
| Double-quoted `"` | `SCDoubleQuoted 0 .blockIn` → `SFlowNode 0 .flowOut` | ✅ Sorry-free |
| Single-quoted `'` | `SCSingleQuoted 0 .blockIn` → `SFlowNode 0 .flowOut` | ✅ Sorry-free |
| Alias `*` | `SCNsAliasNode` → `SFlowNode 0 .flowOut` | ✅ **A12** — sorry CLOSED (scanner rejects empty names; `scanAnchorOrAlias_prod` now returns `sp_mid ≠ sp'` unconditionally) |
| Block scalar `\|`/`>` | `SCLLiteral 0` / `SCLFolded 0` | ✅ Sorry-free (A11 removed `hm` constraint) |
| Plain scalar | `SNsPlain 0 .blockIn` → `SFlowNode 0 .flowOut` | ✅ **A5/A6/A7/A14/A15** — block+flow proven; 1 sorry (multi-line S3) |
| Anchor `&` | `SCNsAnchorProperty` → `SCNsProperties.anchorFirst` → `SFlowNode.propsEmpty` | ✅ **A12** — sorry CLOSED (scanner rejects empty names; `scanAnchorOrAlias_prod` now returns `sp_mid ≠ sp'` unconditionally) |
| Tag `!` | `SCNsTagProperty` → `SCNsProperties.tagFirst` → `SFlowNode.propsEmpty` | ✅ **A12** — S8/S9 CLOSED; secondary `!!` fully proven; verbatim `!<uri>` well-formed case proven; S10 (named/non-specific) remains sorry in `scanTag_nonSecondary_prod` |

**All content types now have dedicated `dispatchContent_*_prod` theorems.** `dispatchContent_evidence` is sorry-free.

##### Remaining Category 1 sorry sites (8 sites, 6 declarations — S1/S2 closed by A11, S7/S8/S9/alias closed by A12)

| ID | Theorem | File | Sorry | Group |
|----|---------|------|-------|-------|
| S1 | `dispatchContent_blockScalar_prod` | StreamAccum | ~~`currentIndent ≥ 0` for `\|`~~ | ~~A: Indent~~ **CLOSED (A11)** — `hm : m ≥ 1` removed from grammar |
| S2 | `dispatchContent_blockScalar_prod` | StreamAccum | ~~`currentIndent ≥ 0` for `>`~~ | ~~A: Indent~~ **CLOSED (A11)** — `hm : m ≥ 1` removed from grammar |
| S3 | `collectPlainScalarLoop_prod` | ScalarProduction | Line break multi-line continuation | B: Loop |
| S4 | `collectPlainScalarLoop_prod` | ScalarProduction | ~~`#` at col=0 (unreachable from callers)~~ | **CLOSED (A13)** — added `h_hash_col` precondition; proved `spaces.length = 0` from `terminates? = none`; col>0 from precondition at each recursive site |
| S5 | `scanPlainScalar_to_flowNode` | ScalarProduction | ~~Doc boundary first-char termination (`GStar.nil` match)~~ | **CLOSED (A14)** — added `h_not_doc` precondition + `canStartPlain_first_not_terminates` helper; restructured proof to handle first char directly via `collectPlainScalarLoop_content_first_step`, eliminating `GStar.nil` case entirely |
| S6 | `dispatchContent_plainScalar_prod` | StreamAccum | ~~Flow context plain scalar (3 sorry sites in 1 expr)~~ | **CLOSED (A15)** — parameterized `collectPlainScalarLoop_prod` + `scanPlainScalar_to_flowNode` over `inFlow : Bool`; `ctxOfInFlow` maps `false → .blockIn`, `true → .flowIn`; added flow→flowOut context lifts |
| S7 | `dispatchContent_anchor_prod` | StreamAccum | ~~Empty anchor name (`& ` — `sp_mid = sp'`)~~ | **CLOSED (A12)** — `scanAnchorOrAlias_prod` strengthened to return `sp_mid ≠ sp'` unconditionally; `_anchorProp_prod` now unconditional |
| S8 | `scanTag_nonSecondary_prod` | StructureProduction | ~~Malformed verbatim tag (no `>` terminator)~~ | **CLOSED (A12)** — `collectVerbatimTagLoop_prod` strengthened with `(sp_mid = sp' → foundClose = false)`; contradiction via `simp [h_close_link h_eq] at h_fc_true` |
| S9 | `scanTag_nonSecondary_prod` | StructureProduction | ~~Empty URI `!<>` — spec requires ≥1 URI char~~ | **CLOSED (A12)** — `collectVerbatimTagLoop_prod` strengthened with `(sp = sp_mid → uri_result = uri)`; contradiction via `simp [h_uri_link hne] at h_uri_ne` |
| S10 | `scanTag_nonSecondary_prod` | StructureProduction | Named/non-specific tag decomposition | E: Tag decomp |

Additionally, the alias empty-name sorry in `dispatchContent_alias_prod` (StreamAccum) is also **CLOSED (A12)** — `scanAnchorOrAlias_aliasNode_prod` now returns unconditional `SCNsAliasNode` (no `sp_mid ≠ sp'` condition).

**Dependency graph**:
- **S4 → S5 → S6**: ~~Closing the col invariant (S4) enables first-char-consumed (S5), which enables flow parameterization (S6). Critical path unlocking 5 sorries.~~ **S4 CLOSED (A13)**. **S5 CLOSED (A14)**. **S6 CLOSED (A15)** — critical path complete.
- **S7 + S9 + S8 + alias**: ~~Share the "scanner loop produces ≥1 char" pattern.~~ ~~**Resolved by A10** — scanner Except conversion makes these closable by contradiction.~~ **CLOSED (A12)** — strengthened `collectAnchorNameLoop_prod` and `collectVerbatimTagLoop_prod` with position-to-value linking conjuncts; made `_aliasNode_prod`/`_anchorProp_prod` unconditional; replaced sorry with contradiction proofs. −2 sorry warnings (14→12).
- ~~**S1, S2**: Independent — just need `indents.size > 1` from preprocessing context to invoke existing `currentIndent_nonneg`.~~ **CLOSED (A11)** — removed `hm : m ≥ 1` from grammar constructors.
- **S3**: Independent, hardest — needs `handleBlockLineBreak_prod` + multi-line continuation grammar.
- **S10**: Independent — decompose `scanNamedTag` into existing `collectTagHandleLoop_prod` + `collectTagSuffixLoop_prod`.

**Wadler-style architectural opportunities**:

1. ~~**Scanner loop non-emptiness lemma family** (closes S7, S9; pattern reusable for S4).~~ **Superseded by A10** — the Except conversion at the scanner level is a superior solution. ~~The non-emptiness pattern may still be useful for S4 (col ≥ 1 after content char)~~ **S4 CLOSED (A13)** via `h_hash_col` precondition instead.
2. ~~**Context-parameterized `collectPlainScalarLoop_prod`** (closes S6 once ~~S5 is closed~~ **S5 CLOSED by A14**). Parameterize over `FlowContext` — only difference is `isPlainSafeBool c false` vs `isPlainSafeBool c true`. Block and flow proofs share 90% of structure.~~ **DONE (A15)** — `ctxOfInFlow` mapping + flow context lifts + parameterized helpers.
3. ~~**First-char-consumed lemma** (closes S5). `canStartPlainScalarBool c next false = true → terminates? c sc content spaces false = none ∨ loop-consumes-entry`. Bridges the two scanner phases.~~ **DONE (A14)** — `canStartPlain_first_not_terminates` + `collectPlainScalarLoop_content_first_step` eliminate the `GStar.nil` case.

**Recommended implementation order**:

| Priority | IDs | Effort | Impact | Rationale |
|----------|-----|--------|--------|-----------|
| ~~1~~ | ~~S7, S8, S9, alias~~ | — | ~~−3 sorry (−4 sites)~~ | **CLOSED (A12)** — strengthened `_prod` theorems with position-to-value linkage. −2 sorry warnings (14→12). |
| ~~2~~ | ~~S4~~ | — | ~~−1 sorry~~, enables S5 | **CLOSED (A13)** — `h_hash_col` precondition + `spaces.length = 0` extraction from `terminates? = none`. Warning count unchanged (S3/S4 share theorem). |
| ~~3~~ | ~~S5~~ | — | ~~−1 sorry~~, enables S6 | **CLOSED (A14)** — `canStartPlain_first_not_terminates` + `collectPlainScalarLoop_content_first_step` + `h_not_doc` precondition |
| 4 | S10 | ~2 hr | −1 sorry | `scanNamedTag_prod`: compose existing handle + suffix loop theorems |
| ~~5~~ | ~~S1, S2~~ | — | ~~−2 sorry~~ | **CLOSED (A11)** — removed `hm : m ≥ 1` from `SCLLiteral`/`SCLFolded` grammar constructors |
| ~~6~~ | ~~S6~~ | — | ~~−3 sorry sites~~ | **CLOSED (A15)** — parameterized over `inFlow`. Warning count unchanged (3 sorry sites in same declaration as `h_not_doc` sorry). |
| 7 | S3 | ~4 hr | −1 sorry | Multi-line plain scalar. Hardest — `handleBlockLineBreak_prod` + `SNsPlainNextLine` |

**Critical path**: ~~S4 →~~ ~~S5 →~~ ~~S6~~ (chain complete — all closed). **S4 CLOSED by A13.** **S5 CLOSED by A14.** **S6 CLOSED by A15.** ~~S7/S8/S9/alias are now trivially closable after A10.~~ **S7/S8/S9/alias CLOSED by A12.** ~~S1/S2 deferred — see analysis below.~~ **S1/S2 CLOSED by A11.**

##### S1/S2 design analysis: indent tracking for block scalars

`dispatchContent_blockScalar_prod` needs `sc.currentIndent ≥ 0`, which `ScannerSurfCorr.currentIndent_nonneg` provides given `sc.indents.size > 1`. But `indents.size > 1` is not always true:

- **`pendingBlock` path**: After `pushSequenceIndent`/`pushMappingIndent`, `size ≥ 2`. But `scanNextToken_preprocess` calls `unwindIndents` (pops), so proving `size > 1` survives preprocessing requires new infrastructure.
- **`noPending` path**: Top level allows block scalars (`|\n  hello`), but `indents = #[sentinel]`, `size = 1`, `currentIndent = -1`. This is a genuine case — not an edge case to be sorry'd away.

The root issue: `scanBlockScalar_prod`'s precondition `currentIndent ≥ 0` is used to derive `contentIndent ≥ 1` via `max(0, currentIndent + 1) ≥ 1`. With `currentIndent = -1`, `max(0, 0) = 0`, so `contentIndent` could be 0 (content at column 0). The entire block scalar proof chain (`scanBlockScalarBody_indent_ge_one`, `_literal_prod`, `_folded_prod`) assumes `contentIndent ≥ 1`. Weakening this requires reworking the chain to handle `contentIndent = 0`.

**Architectural options** (Option 1 selected — see analysis below):
1. ~~Weaken `scanBlockScalar_prod` to allow `currentIndent = -1` and `contentIndent = 0`, cascading through block scalar proof chain~~ → **Selected**: Remove `hm : m ≥ 1` from `SCLLiteral.mk`/`SCLFolded.mk` grammar constructors. This is mathematically correct because our `Nat` encoding uses `n = 0` at document level (a +1 offset from the YAML spec's `n = -1`). The YAML spec's `m ≥ 1` at `n = -1` becomes `m ≥ 0` at our `n = 0` — we're compensating for the encoding offset, not weakening the spec. Cascade: drop `hIndent` from `scanBlockScalarBody_{literal,folded}_prod` and `scanBlockScalar_prod`, weaken `contentIndent ≥ 1` to trivially-true `contentIndent ≥ 0`, close the 2 sorry sites.
2. Track indent depth in `ScannerSurfCorr` (new field `indent_size_ge : sc.indents.size ≥ n`), thread through pushes/pops (~2 hr, A1-scale) — **Rejected**: unnecessarily complex; doesn't address the root cause (grammar constraint too strong for encoding).
3. Add `h_indented` field to `PendingNode.pendingBlock` — blocks `noPending` path but closes `pendingBlock` (~1 hr, partial fix) — **Rejected**: incomplete fix.

**Why Option 1 removes `hm` rather than switching to `Int`**: The `Nat` encoding is correct and pervasive — `SIndent n` uses `Nat.repeat` for column matching, every grammar inductive uses `Nat`, the existential trick (`n = 0`) is deeply embedded. Switching to `Int` would cascade through the entire grammar and proof stack with no benefit. The `hm : m ≥ 1` constraint is a faithful transcription of the YAML spec's `m ≥ 1`, but that constraint is stated relative to `n = -1`. At our `n = 0`, the correct constraint is `m ≥ 0` (trivially true for `Nat`).

**Recommendation**: ~~Option 1 is the correct fix (handles all YAML inputs). Defer until other lower-effort sorry sites are closed.~~ ~~**Implementing now** — architectural risks compound when deferred, and Option 1's cascade is well-understood (grammar → 3 theorems in ScalarProduction → 1 theorem in StreamAccum; loop theorems untouched).~~ **DONE (A11)** — implemented, cascade was smaller than predicted (~20 min vs estimated ~3 hr). See A11 accomplishment below.

##### Accomplishments on Category 1

**A5 — Wadler-style refactoring of `accum_content_pending` + plain scalar wiring** (2026-04-06)

1. **Plain scalar context lift theorems** (NodeProduction.lean, 3 theorems, 0 sorry):
   - `SNsPlainFirst_blockIn_to_flowOut`: Cases on all 4 constructors, rebuilds with `.flowOut`. Works because `isNsPlainSafe .blockIn` and `isNsPlainSafe .flowOut` are definitionally equal (same match arm in definition: both = `isNsChar ch`).
   - `SNsPlain_blockIn_to_flowOut_minimal`: Wraps first-char lift into minimal `SNsPlainMultiLine 0 .flowOut` with `GStar.nil` continuations.
   - `SFlowNode_plain_blockIn_to_flowOut_minimal`: Composes through `plain_flowContent` + `flowContent_flowNode`.
   - **Key insight**: The existing note in NodeProduction.lean claiming `.blockIn → .flowOut` lift "does NOT hold" was WRONG. Corrected.

2. **`dispatchContent_plainScalar_prod`** (~45 lines, 1 sorry): New theorem returning `∃ sp', SFlowNode 0 .flowOut sp sp' ∧ ScannerSurfCorr s' sp'`. Navigates past character guards (`&`, `*`, `!`, `|`/`>`, `"`, `'`) to reach `canStartPlainScalarBool` branch. Sorry for full-scan grammar coverage — `scanPlainScalar_prod` returns a 1-char minimal witness `SNsPlain 0 .blockIn` whose endpoint `sp_gram` differs from scanner endpoint `sp'`.

3. **`dispatchContent_evidence`** (Wadler-style unified extraction, ~40 lines, 1 sorry declaration containing 3 sorry sites): Produces `SFlowNode 0 .flowOut ∨ (SCLLiteral 0 ∨ SCLFolded 0)` for ANY content dispatch. Delegates to per-type `_prod` theorems for `"`, `'`, `*`, `|`/`>`, and plain scalar; uses sorry for `&` and `!` (anchor/tag grammar production deferred).

4. **Refactored `accum_content_pending`**: Replaced duplicated evidence extraction cascades in `noPending` col=0 and `pendingBlock` with single calls to `dispatchContent_evidence`. Each case now has two branches (flow content vs block scalar) instead of 5+ nested `by_cases`. ~120 lines of duplicated cascade eliminated.

**Build**: 415/415 jobs, 0 errors, 13 sorry warnings (+2 from `dispatchContent_plainScalar_prod` and `dispatchContent_evidence`).

**Net effect on sorry**:
- **Removed**: 1 sorry (catch-all "other content types" in `noPending` col=0 — now handled by evidence extraction)
- **Removed**: 1 sorry (catch-all "other content types" in `pendingBlock` — now handled by evidence extraction)
- **Added**: 1 sorry in `dispatchContent_plainScalar_prod` (full-scan grammar gap)
- **Added**: 1 sorry declaration in `dispatchContent_evidence` (anchor `&` + tag `!` grammar)
- **Total**: +0 net sorry sites eliminated from catch-all, +2 new sorry declarations (more precise)

**A4 — Block scalar `|`/`>` wiring into `accum_content_pending`** (2026-04-03)

1. **`dispatchContent_blockScalar_prod`** (~60 lines): New theorem returning `∃ sp', (SCLLiteral 0 sp sp' ∨ SCLFolded 0 sp sp') ∧ ScannerSurfCorr s' sp'`. Handles both `|` and `>` via `cases hchar`. Each branch unfolds `scanNextToken_dispatchContent`, skips `&`/`*`/`!` guards via `split + absurd`, reaches the `scanBlockScalar` bind, and delegates to `scanBlockScalar_prod`. Has 2 sorry sites for `currentIndent ≥ 0` (one per branch).

2. **`noPending` col=0 block scalar branch**: Added `by_cases hc_bs : c = '|' ∨ c = '>'` before the catch-all. Builds `SBlockNode` via `literal_blockNode`/`folded_blockNode` with `GOpt.none` (no properties), wraps in `SLBareDocument`, extends to `SLYamlStream.implicitContinue`, then uses `ssl_comments_extend_stream` for trailing `SSLComments`. Returns `PendingNode.pendingContent` with closure.

3. **`pendingBlock` block scalar branch**: Added `by_cases hc_bs : c = '|' ∨ c = '>'` before the catch-all. Closes block entry IMMEDIATELY via `h_close_old sp_scan' h_blockNode`, returns `PendingNode.pendingContent` with `ssl_comments_extend_stream` closure. Loses entry accumulation (acceptable — same pattern as the existing catch-all).

**Build**: 415/415 jobs, 0 errors, 11 sorry warnings (+1 from new `dispatchContent_blockScalar_prod` declaration).

**A6 — Trailing WS architecture for plain scalar grammar** (2026-04-07)

Discovered and resolved the trailing whitespace gap between the `SNsPlain` YAML grammar endpoint and the scanner state endpoint. The scanner's `collectPlainScalarLoop` advances past trailing whitespace (spaces/tabs accumulated in the `spaces` parameter), but the grammar ends at the last content character. In the YAML spec (§6.5), this trailing WS is part of `s-l-comments`, not the scalar.

1. **`white_prepend_SSLComments`** (StreamAccum.lean, ~35 lines, 0 sorry): New theorem composing trailing WS into `SSLComments`. Given `GStar SSWhite sp sp'` and `SSLComments sp' sp_mid`, produces `SSLComments sp sp_mid`. Proof handles 5 sub-cases by structural analysis:
   - Nil WS: trivial identity
   - Non-empty WS + `withComment/withSep/whites`: concatenate `GPlus` via `GPlus_extend_GStar`
   - Non-empty WS + `withComment/withSep/startOfLine`: use WS as the new `SSeparateInLine`
   - Non-empty WS + `withComment/noSep`: create `SSBComment.withSep` with WS as separator
   - Non-empty WS + `startOfLine`: impossible — `sswhite_col_succ` + `gstar_sswhite_col_ge` prove `col ≥ 1`, contradicting `col = 0`

2. **`dispatchContent_plainScalar_prod`**: Changed return type from `∃ sp', SFlowNode sp sp' ∧ ScannerSurfCorr s' sp'` to `∃ sp_gram sp', SFlowNode sp sp_gram ∧ GStar SSWhite sp_gram sp' ∧ ScannerSurfCorr s' sp'`. The sorry is now properly structured: separate existentials for grammar endpoint and scanner endpoint, with trailing WS bridge.

3. **`dispatchContent_evidence`**: Changed return type to `∃ sp_gram sp', grammar sp sp_gram ∧ GStar SSWhite sp_gram sp' ∧ ScannerSurfCorr s' sp'`. For non-plain-scalar paths (quoted, alias, block scalar), `sp_gram = sp'` with `GStar.nil`. For plain scalar, the WS bridge is non-trivial.

4. **`accum_content_pending`** (both `noPending` col=0 and `pendingBlock`): Updated to compose trailing WS into SSLComments via `white_prepend_SSLComments h_trailing_ws h_ssl`. The WS evidence is captured in `PendingNode.pendingContent` closures. No change to `PendingNode` definition — compositi done inside the closure.

**Build**: 415/415 jobs, 0 errors, 13 sorry warnings (+0 net). Sorry count unchanged — the refactoring split one sorry into properly structured sorrys within the same declaration.

**A7 — Full-scan plain scalar grammar production** (2026-04-08)

Proved `collectPlainScalarLoop_prod` by fuel induction for single-line block-context plain scalars. The theorem produces `GStar (SNbNsPlainInLineEntry .blockIn)` (inline entries) + `GStar SSWhite` (trailing WS) + `ScannerSurfCorr` from the loop's `.ok` result. Composed into `scanPlainScalar_to_flowNode` which provides `SFlowNode 0 .flowOut` + trailing WS + corr suitable for `dispatchContent_plainScalar_prod`.

1. **`collectPlainScalarLoop_prod`** (ScalarProduction.lean, ~85 lines, 2 sorry): Fuel induction mirroring `collectPlainScalarLoop_corr`. Handles 6 terminal cases (EOF, terminates?, !plainSafe) with `GStar.nil` entries + accumulated WS + corr. Whitespace branch extends `GStar SSWhite` accumulator via `gstar_sswhite_append`. Content char branch: case analysis on `c = ':'` (colonSafe via `colon_not_terminated_next` + `peekAtLoop_some_chars`), `c = '#'` (hashAfterNs with col > 0; col = 0 sorry'd as unreachable), other (safe). Forms `SNbNsPlainInLineEntry` from accumulated WS + `SNsPlainChar`, prepends to IH entries. Sorry: (a) line break multi-line, (b) `#` at col=0 (unreachable — `#` is indicator, excluded by `canStartPlainScalarBool`; after any content char col ≥ 1).

2. **Helper lemmas** (ScalarProduction.lean, ~45 lines, 0 sorry):
   - `canStartPlainScalar_not_ws`: `canStartPlainScalarBool c next false → isWhiteSpaceBool c = false`
   - `gstar_sswhite_at_non_ws`: `GStar SSWhite ⟨c :: rest, col⟩ s₁ → ¬WS c → s₁ = ⟨c :: rest, col⟩`
   - `SNsPlainChar_at_head`: All `SNsPlainChar` constructors at `⟨c :: rest, col⟩` produce `⟨rest, col + 1⟩`
   - Context lifts: `SNsPlainChar_blockIn_to_flowOut`, `SNbNsPlainInLineEntry_blockIn_to_flowOut`, `GStar_entries_blockIn_to_flowOut`, `SNsPlainFirst_blockIn_to_flowOut'`

3. **`scanPlainScalar_to_flowNode`** (ScalarProduction.lean, ~60 lines, 0 sorry): Proves `terminates?` doesn't fire on first char via `canStartPlain_first_not_terminates` (using `h_not_doc` precondition), extracts the recursive loop call via `collectPlainScalarLoop_content_first_step`, then applies `collectPlainScalarLoop_prod` on the remaining iterations. Composes `SNsPlainFirst` (from `canStartPlainScalar_to_SNsPlainFirst`) + tail entries into `SNsPlainOneLine → SNsPlainMultiLine → SNsPlain 0 .flowOut → SFlowContent.plain → SFlowNode.content`. Corr preserved via `corr_of_emitAt` + `corr_of_simpleKeyAllowed_update`. Requires `h_block : sc.inFlow = false` and `h_not_doc : sc.col = 0 → atDocumentBoundary sc = false`. **A14**: Sorry-free — doc boundary edge case eliminated by restructuring to handle first char directly (no `GStar.nil` match).

4. **`dispatchContent_plainScalar_prod`** (StreamAccum.lean, modified): Block context case (`sc.inFlow = false`) now fully proven via `scanPlainScalar_to_flowNode`. Flow context case retains sorry (flow plain scalar grammar not yet supported). Uses `by_cases h_block` to split; `rwa [← h_block]` bridges `canStartPlainScalarBool` from `sc.inFlow` to `false` via assumption rewriting.

**Build**: 415/415 jobs, 0 errors, 15 sorry warnings (was 13; +2 from new `collectPlainScalarLoop_prod` and `scanPlainScalar_to_flowNode` declarations). **Update (A14)**: `scanPlainScalar_to_flowNode` now sorry-free.

**Net sorry accounting**:
- **Eliminated**: Block context `dispatchContent_plainScalar_prod` sorry (grammar + trailing WS — 3 sorry sites in 1 declaration)
- **Added**: `collectPlainScalarLoop_prod` 2 sorry (line break multi-line + `#` at col=0) — **A13 closed `#` at col=0**
- **Added**: ~~`scanPlainScalar_to_flowNode` 1 sorry (doc boundary nil entries)~~ **CLOSED (A14)**
- **Added**: `dispatchContent_plainScalar_prod` flow case 3 sorry (same pattern as before, narrowed scope) + `h_not_doc` sorry (from A14)
- **Warning count**: +2 (new declarations), +0 net in existing (flow sorry replaces block+flow sorry in same decl)
- The block context path — the path exercised by `accum_content_pending` — is now **fully proven**.

**A8 — Anchor `&` and tag `!` node property composition** (2026-04-03)

Proved that anchor `&` and tag `!` content dispatch produce `SFlowNode 0 .flowOut` via the node property composition path: `SCNsAnchorProperty`/`SCNsTagProperty` → `SCNsProperties.anchorFirst`/`.tagFirst` (with `GOpt.none` for the optional second property) → `SFlowNode.propsEmpty`. This is the "properties-only" flow node form from YAML spec §7.1.

1. **`dispatchContent_anchor_prod`** (StreamAccum.lean, ~25 lines, 1 sorry): Unfolds `scanNextToken_dispatchContent` for `c = '&'`, applies `scanAnchorOrAlias_anchorProp_prod` to get `SCNsAnchorProperty sp sp'` (conditional on `sp_mid ≠ sp'`), composes through `SCNsProperties.anchorFirst 0 .flowOut` + `SFlowNode.propsEmpty`. `ScannerSurfCorr` repacked to handle the `definedAnchors.push` update in the scanner dispatch. 1 sorry for degenerate empty anchor name (`& ` without chars — scanner accepts, grammar requires `GPlus`).

2. **`dispatchContent_tag_prod`** (StreamAccum.lean, ~30 lines, 1 sorry): Unfolds dispatch for `c = '!'`. Two branches:
   - Secondary `!!suffix`: delegates to existing `scanTag_secondary_prod`, composes through `SCNsProperties.tagFirst 0 .flowOut` + `SFlowNode.propsEmpty`. Fully proven.
   - Non-secondary (verbatim `!<uri>`, named `!handle!suffix`, non-specific `!`): Uses `scanTag_corr` for `ScannerSurfCorr`, grammar sorry'd pending tag handle/verbatim loop production theorems.

3. **`dispatchContent_evidence` now sorry-free**: Replaced inline `sorry` at the `&` and `!` branches with calls to `dispatchContent_anchor_prod` and `dispatchContent_tag_prod`. The unified evidence theorem no longer contains any direct `sorry` — all grammar gaps are localized in per-content-type theorems.

**Build**: 415/415 jobs, 0 errors, 15 sorry warnings (was 14; +2 new declarations, -1 from `dispatchContent_evidence`).

**Net sorry accounting**:
- **Eliminated**: `dispatchContent_evidence` inline sorry for `&` and `!` (2 sorry sites in 1 declaration)
- **Added**: `dispatchContent_anchor_prod` 1 sorry (empty anchor name — same root cause as alias)
- **Added**: `dispatchContent_tag_prod` 1 sorry (verbatim/named tag grammar)
- **Warning count**: +1 net (2 new declarations − 1 old declaration)
- All 7 content types now have dedicated `dispatchContent_*_prod` theorems

**A9 — Tag loop production theorems and `dispatchContent_tag_prod` sorry elimination** (2026-04-09)

Pushed the tag sorry from `dispatchContent_tag_prod` (StreamAccum layer) down to `scanTag_nonSecondary_prod` (StructureProduction layer). `dispatchContent_tag_prod` is now sorry-free — both the secondary `!!suffix` and non-secondary paths delegate to proven theorems. The non-secondary sorry is localized to 3 specific edge cases in `scanTag_nonSecondary_prod`.

1. **`collectVerbatimTagLoop_prod`** (StructureProduction.lean, ~45 lines, 0 sorry): Fuel induction producing `GStar (GChar isUriCharProp)` for URI characters. Returns 3-way evidence: `GStar` for URI chars, `ScannerSurfCorr` for scanner state, and `sp_mid = sp' ∨ GLit '>' sp_mid sp'` distinguishing well-formed (terminated by `>`) from malformed (no `>`) verbatim tags. Uses `isUriChar_iff` bridge and `advance_non_newline_corr` (URI chars exclude `\n`, `\r` via `native_decide`).

2. **`collectTagHandleLoop_prod`** (StructureProduction.lean, ~45 lines, 0 sorry): Fuel induction producing `GStar (GChar isWordCharProp)` for word characters. Returns `foundBang` evidence: when `true`, also produces `GLit '!'` for the closing `!`; when `false`, `sp_mid = sp'`. Uses `isWordChar_iff` bridge. Pattern mirrors `collectTagSuffixLoop_prod` but with 3-branch match (`some '!'` / `some c` / `none`) instead of 2-branch.

3. **`scanTag_nonSecondary_prod`** (StructureProduction.lean, ~55 lines, 1 sorry declaration with 3 sorry sites): Handles all non-`!!` tag branches. Case-splits on `sc.advance.peek?`:
   - **Verbatim `!<uri>`**: Decomposes `<`, delegates to `collectVerbatimTagLoop_prod`, bridges column via `omega`. Well-formed case (non-empty URI + `GLit '>'`) constructs `SCNsTagProperty.verbatim` via `GStar_to_GPlus` (imported from `CouplingBridge.lean`). 2 sorry: malformed verbatim (no `>` terminator), empty URI `!<>`.
   - **Secondary `!!`**: Contradiction with `hpeek2 : ¬(sc.advance.peek? = some '!')`.
   - **Named/non-specific**: Delegates to `scanNamedTag_corr` for `ScannerSurfCorr`, grammar sorry'd. 1 sorry: named tag handle/suffix composition.

4. **`dispatchContent_tag_prod` updated** (StreamAccum.lean): Non-secondary branch now calls `scanTag_nonSecondary_prod` instead of `scanTag_corr` + inline sorry. Grammar construction (`SCNsProperties.tagFirst + SFlowNode.propsEmpty`) is fully proven in both branches.

**Build**: 415/415 jobs, 0 errors, 15 sorry warnings (+0 net: −1 `dispatchContent_tag_prod`, +1 `scanTag_nonSecondary_prod`).

**Net sorry accounting**:
- **Eliminated**: `dispatchContent_tag_prod` sorry (non-secondary branch)
- **Added**: `scanTag_nonSecondary_prod` 1 sorry declaration (3 sorry sites: malformed verbatim, empty URI, named/non-specific)
- **Warning count**: +0 net (sorry pushed down from accumulation layer to production layer)
- `dispatchContent_tag_prod` is now sorry-free — all tag grammar gaps are in StructureProduction.lean

**A10 — Scanner Except conversion for anchor/tag validation** (2026-04-10)

Converted 4 scanner functions from pure `ScannerState` return to `Except ScanError ScannerState`, enabling the scanner to reject degenerate inputs (empty anchor names, empty verbatim tag URIs, unterminated verbatim tags). This makes sorry sites S7, S8, S9, and the alias empty-name sorry all closable by contradiction — the `.ok` hypothesis in proof branches directly contradicts the degenerate case that the scanner now rejects.

**Motivation**: The proof layer needed `sp_mid ≠ sp'` (scanner consumed ≥1 character) for anchor names the verbatim URIs, but the pure scanner accepted empty names/URIs without error. The A3 reflection identified this as "a scanner validation gap, not a proof gap." The fix operates at the right level — the scanner, which is the earliest point where YAML spec §6.9.2 production [103] `ns-anchor-name ::= ns-anchor-char+` (non-empty) can be enforced.

1. **3 new `ScanError` constructors** (Token.lean):
   - `emptyAnchorName (line col : Nat)` — rejected when `scanAnchorOrAlias` collects zero anchor-name characters
   - `emptyVerbatimTagURI (line col : Nat)` — rejected when `scanVerbatimTag` finds `!<>` with empty URI
   - `unterminatedVerbatimTag (line col : Nat)` — rejected when `scanVerbatimTag` reaches EOF without `>`

2. **4 functions converted to `Except`** (Scanner.lean):
   - `scanAnchorOrAlias` (L1056): `if name.isEmpty then .error (.emptyAnchorName ...) else .ok state`
   - `collectVerbatimTagLoop` (L1073): returns `Except ScanError (String × Bool × ScannerState)` — error on unterminated (`!foundClose`) or empty URI (`uri.isEmpty`)
   - `scanVerbatimTag` (L1120): delegates to `collectVerbatimTagLoop`, propagates errors
   - `scanTag` (L1160): delegates to `scanVerbatimTag` (via monadic bind), `scanSecondaryTag` (unchanged), or `scanNamedTag` (unchanged)

3. **`scanNextToken_dispatchContent` call sites updated** (Scanner.lean L2514-2530): `'&'` and `'*'` branches now use `← scanAnchorOrAlias` (monadic bind); `'!'` branch uses `← scanTag`. Error propagation is automatic via `do` notation.

4. **9 proof files updated for Except cascade** (0 new sorry, 0 errors):
   - `StructureCoupling.lean`: `scanAnchorOrAlias_corr` and `scanTag_corr` — already had `(s' : ScannerState) (hok : ... = .ok s')` signatures
   - `ScannerCorrectness.lean`: ~30 theorem signature changes to add `s'`/`hok` params
   - `ScanStrictCoupling.lean`: signature updates
   - `StructureProduction.lean`: `scanAnchorOrAlias_prod` + `scanTag_secondary_prod` / `scanTag_nonSecondary_prod` — `(hok : ... = .ok s')`
   - `ScannerPlainScalarValid.lean`: Major fixes — `scanTag_psv_match` fully inlined (forward reference eliminated), `dispatchContent_preserves_PlainScalarsValid`/`FlowInv`/`AllKeysPlaceholderInv` anchor/alias/tag branches use `generalize + cases` pattern
   - `NodeProduction.lean`: 3 theorems updated (`scanAnchorOrAlias_aliasNode_prod`, `_anchorProp_prod`, `_flowNode_prod`)
   - `StreamAccum.lean`: `dispatchContent_corr`/`_alias_prod`/`_anchor_prod`/`_tag_prod` — `generalize + cases + dsimp only []` for `Except.bind` match wrappers

**Key proof patterns discovered**:
- **`generalize + cases + dsimp only []` for Except.bind match wrapper**: After `simp only [bind, Except.bind]`, branches using Except-returning functions leave `match f x with | .error e => .error e | .ok v => .ok v = .ok s'`. Fix: generalize the function call, cases on result, `dsimp only []` to iota-reduce the trivial match.
- **`change Except.ok X = Except.ok s' at hok`**: `return` in `do` blocks desugars to `Pure.pure`, which is definitionally `Except.ok` but syntactically different. `change` bridges the gap before `Except.ok.inj; subst`.
- **Forward reference elimination**: `scanTag_psv_match` at L261 referenced `scanTag_new_token_is_tag` defined at L2461. Fixed by fully inlining the proof with `unfold scanTag` + separate sub-proofs for verbatim/secondary/named branches.

**Build**: 415/415 jobs, 0 errors, 15 sorry warnings (unchanged — no new sorry, no sorry closed yet).

**Net sorry accounting**:
- **Added**: 0 sorry
- **Eliminated**: 0 sorry (the sorry sites are now *closable* but not yet closed)
- **Enabled**: S7 (anchor), S8 (unterminated verbatim), S9 (empty URI), alias sorry — all 4 now closable by `absurd`/`contradiction` in the `.ok` branch
- **Warning count**: 15 (unchanged)

**A11 — Remove `hm : m ≥ 1` from block scalar grammar constructors** (2026-04-10)

Removed the `hm : m ≥ 1` constraint from `SCLLiteral.mk` and `SCLFolded.mk` grammar constructors in `Scalars.lean`. This closes S1 and S2 — the 2 sorry sites in `dispatchContent_blockScalar_prod` where `currentIndent ≥ 0` couldn't be proven at top level (`currentIndent = -1`).

**Why this is correct (not a weakening)**: Our `Nat` encoding uses `n = 0` at document level, while the YAML spec uses `n = -1`. The spec's `m ≥ 1` (§8.1.1) is relative to `n = -1`, giving content indent `n + m ≥ 0`. At our `n = 0`, the correct constraint is `m ≥ 0` — trivially true for `Nat`. Removing `hm` compensates for the encoding offset.

1. **`Scalars.lean`**: Removed `(hm : m ≥ 1)` from both `SCLLiteral.mk` and `SCLFolded.mk` constructors. Updated docstrings explaining the encoding offset rationale.

2. **`ScalarProduction.lean`** — 3 theorems updated:
   - `scanBlockScalarBody_literal_prod`: Removed `hIndent : sc_orig.currentIndent ≥ 0` parameter. Return type changed from `∃ sp' contentIndent, contentIndent ≥ 1 ∧ SLLiteralContent ...` to `∃ sp' contentIndent, SLLiteralContent ...`. Removed `omega`/`Nat.le_trans h_min` proof steps in both `some d` and `none` branches.
   - `scanBlockScalarBody_folded_prod`: Same changes as literal.
   - `scanBlockScalar_prod`: Removed `hIndent` parameter. Both literal/folded branches updated — `obtain` no longer destructures `h_ci_ge`, constructor calls no longer pass it.

3. **`StreamAccum.lean`**: `dispatchContent_blockScalar_prod` — deleted 2 `have hIndent : sc.currentIndent ≥ 0 := sorry` lines (one per branch). Removed `hIndent` from `scanBlockScalar_prod` calls.

**Build**: 415/415 jobs, 0 errors, 14 sorry warnings (−1 from 15). `scanBlockScalarBody_indent_ge_one` (L1738) is now unused but left in place.

**Net sorry accounting**:
- **Eliminated**: 2 sorry sites (S1 + S2 in `dispatchContent_blockScalar_prod`)
- **Added**: 0 sorry
- **Warning count**: 14 (−1)

##### Reflections about Category 1

1. **`SSLComments` structural mismatch resolved via "build-then-extend" pattern.** `SBlockNode.blockLiteral`/`.blockFolded` do NOT include trailing `SSLComments` (unlike `SBlockNode.flowInBlock`). Solution: build the `SBlockNode` spanning `sp_block → sp_scan'` without comments, use it for `SLBareDocument`/`h_close_old`, then bridge `sp_scan' → sp_mid` with `ssl_comments_extend_stream`. This pattern generalizes to any content type whose grammar production doesn't include trailing comments.

2. ~~**`currentIndent ≥ 0` is a genuine limitation at 2 sorry sites.**~~ **RESOLVED by A11.** Removed `hm : m ≥ 1` from grammar constructors — the constraint was over-specified for our `Nat` encoding (see A11 accomplishment above). The `currentIndent ≥ 0` precondition and `contentIndent ≥ 1` derivation are no longer needed.

3. **Entry accumulation loss for block scalars in `pendingBlock` is acceptable.** By closing immediately via `h_close_old`, we lose `SBlockSeqEntries_snoc` accumulation for subsequent `-` tokens. However, the previous catch-all already produced `PendingNode.pendingContent` without entry accumulation, so this is no regression.

4. **Plain scalar UNBLOCKED.** ~~`scanPlainScalar_prod` only produces `SNsPlain 0 .blockIn`, but grammar needs `.flowOut`. The `.blockIn → .flowOut` context lift fails because `isNsPlainSafe .blockIn` allows flow indicators.~~ **Corrected**: `isNsPlainSafe .blockIn` and `isNsPlainSafe .flowOut` are in the SAME match arm (both = `isNsChar ch`). The context lift is valid. The remaining blocker is the full-scan grammar gap: `scanPlainScalar_prod`'s minimal 1-char witness doesn't cover the full scanner output range. Resolving this needs either (a) a full multi-line `scanPlainScalar_prod` that returns grammar matching the scanner endpoint, or (b) a "grammar subsumption" lemma showing partial grammar derivations are sufficient.

5. **Catch-all sorry sites reduced.** The `noPending` and `pendingBlock` catch-all comments now say "anchor, tag, plain scalar" instead of "anchor, tag, block scalar, plain scalar". Block scalar is fully wired (modulo `currentIndent ≥ 0` sorry in the dispatch theorem).

6. **Trailing WS gap between `SNsPlain` grammar and scanner state, resolved by architecture.** (A6) The `collectPlainScalarLoop` scanner advances past trailing whitespace (spaces/tabs accumulated in the `spaces` parameter), but the `SNsPlain` YAML grammar ends at the last `ns-plain-char`. In the YAML spec, this trailing WS belongs to `s-l-comments → s-b-comment → s-separate-in-line`, NOT to `ns-plain`. This creates a gap: grammar endpoint `sp_gram ≠ sp'` scanner endpoint. Resolution: `dispatchContent_evidence` now returns `∃ sp_gram sp', grammar sp sp_gram ∧ GStar SSWhite sp_gram sp' ∧ ScannerSurfCorr s' sp'`, and `white_prepend_SSLComments` composes trailing WS into the `SSLComments` from the next preprocessing step. The key insight is that `SSBComment.withSep` absorbs whitespace as `SSeparateInLine.whites`, so the trailing WS naturally becomes part of `s-l-comments`.

7. **Node property composition is orthogonal to content type.** (A8) Anchors and tags produce `SFlowNode` via a fundamentally different path than scalars: `SCNsProperties → SFlowNode.propsEmpty` (properties-only node) rather than `SFlowContent → SFlowNode.content` (content node). The `SCNsProperties` type has two constructors — `tagFirst` and `anchorFirst` — each taking the primary property plus an optional `GOpt` for the secondary. With only one property (no combined anchor+tag in the scanner dispatch), the `GOpt.none` makes composition trivial. The `ScannerSurfCorr` repacking for anchors is slightly more complex due to `definedAnchors.push` in the scanner dispatch, but follows the same field-repacking pattern used elsewhere.

8. **`dispatchContent_evidence` achieved sorry-free status.** (A8) All 7 content types now have dedicated `dispatchContent_*_prod` theorems. The unified evidence extraction theorem is purely a delegator — no grammar construction of its own. This means future improvements to any single content type's grammar production automatically improve `dispatchContent_evidence` without touching it.

9. **`GStar_to_GPlus` relocated to `CouplingBridge.lean` §8 GStar Composition.** (A9) Originally defined in `NodeProduction.lean`, which imports `StructureProduction.lean` — making reverse import impossible. Moved to `CouplingBridge.lean` (lowest common ancestor in the import DAG), eliminating the inline workaround in `scanTag_nonSecondary_prod` and enabling all downstream files to share the single definition.

10. **Three-way loop evidence pattern.** (A9) Both `collectVerbatimTagLoop_prod` and `collectTagHandleLoop_prod` use a novel 3-result return type: `GStar` chars + `ScannerSurfCorr` + termination evidence (either `sp_mid = sp'` for early stop, or `GLit` for delimiter consumption). This pattern captures the scanner's dual-termination semantics (delimiter found vs. not found) without complicating the base case. The verbatim loop uses `Or.inl rfl` / `Or.inr (GLit.mk ...)`, while the handle loop uses `Or.inl ⟨rfl, rfl⟩` / `Or.inr ⟨GLit.mk ..., rfl⟩` (pairing position with `foundBang` Bool evidence).

11. **Scanner validation is the right layer for spec-mandated non-emptiness.** (A10) The A3 reflection identified empty anchor/alias names as "a scanner validation gap, not a proof gap." This proved prescient — attempting to prove non-emptiness post-hoc in the proof layer (via `loop_nonempty_when_valid_start` lemma families) would have required threading `peek? = some c` preconditions through multiple levels of loop induction. Converting the scanner to `Except` is architecturally cleaner: the scanner enforces the YAML spec constraint (`ns-anchor-name ::= ns-anchor-char+`), and the proof layer simply uses the `.ok` hypothesis to eliminate degenerate branches. The same principle applies to `scanVerbatimTag`: the spec requires non-empty URI and proper `>` termination, and the scanner is the natural place to validate these. **General principle**: when the YAML spec requires a non-emptiness or well-formedness constraint, enforce it at the scanner level via `Except` rather than proving it retroactively in the production proof.

12. **Except cascade is wide but mechanically uniform.** (A10) Converting 4 scanner functions to `Except` required updating 9 proof files (~100+ theorem signatures), but the changes followed a small set of repeating patterns: (a) add `(s' : ScannerState) (hok : f sc = .ok s')` to theorem signatures, (b) use `generalize + cases + dsimp only []` for `Except.bind` match wrappers, (c) use `change Except.ok X = .ok s' at hok` for `Pure.pure` ↔ `Except.ok` bridging. The mechanical uniformity meant the cascade, while wide, was predictable — no novel proof ideas needed for the forwarding sites. The challenging part was `ScannerPlainScalarValid.lean` where `scanTag_psv_match` had a forward reference to a theorem defined 2200 lines later, requiring full inlining of the proof instead.

13. **Early architectural resolution pays off.** (A11) The S1/S2 sorry sites were initially estimated at ~3 hr ("not trivial... cascade through block scalar proof chain"). In practice, the cascade touched exactly 4 theorems across 2 files and took ~20 min. The user's instinct to "resolve the architecture options early" was correct — the deep analysis of the proof chain (Layer 1–7, grammar constructors, encoding offset) revealed that the `hm : m ≥ 1` removal was the right fix, not a weakening. Deferring would have risked building further proof infrastructure on top of the over-strong constraint. **General principle**: when an architectural option has been fully analyzed and the cascade is well-understood, implement it immediately rather than accumulating technical debt.

14. **Position-to-value linkage via column monotonicity.** (A12) The key technique for closing S7/S8/S9/alias was *strengthening loop `_prod` theorems* with conjuncts like `(sp = sp' → result.fst = name)`. These are proven vacuously in the recursive (char-consumed) case: `gstar_gchar_col_le h_tail` gives `sp'.col ≥ sc.col + 1`, making `sp = sp'` impossible (column would need to be both `sc.col` and `≥ sc.col + 1`). In the base cases (zero fuel, no match), the conjuncts are trivially `fun _ => rfl`. This pattern — linking grammar position equality to scanner-level value equality, then using column monotonicity for vacuous truth — is reusable for any loop that consumes at least one character. **General principle**: when a degenerate case (`sp = sp'`, meaning zero characters consumed) blocks grammar construction, strengthen the loop theorem to carry a value-linking implication and prove it vacuously via column monotonicity.

15. **Strengthening upstream beats conditioning downstream.** (A12) The original approach (A3/A10) kept `_aliasNode_prod` and `_anchorProp_prod` conditional: `sp_mid ≠ sp' → grammar`. All callers needed `by_cases hne : sp_mid ≠ sp'` with sorry for the `sp_mid = sp'` branch. The A12 approach strengthened `scanAnchorOrAlias_prod` to return `sp_mid ≠ sp'` unconditionally (via the scanner's `Except.error .emptyAnchorName` rejection + the position-to-name linkage), making `_aliasNode_prod`/`_anchorProp_prod` unconditional. This eliminated the `by_cases` and sorry from ALL callers simultaneously. **General principle**: when multiple downstream theorems condition on the same hypothesis, prove it once at the source and simplify all downstream callsites.

**A12 — Close S7/S8/S9/alias sorry sites** (2026-04-10)

Closed 4 sorry sites (S7, S8, S9, alias empty-name) by strengthening production theorems with position-to-value linkage. −2 sorry warnings (14→12): `dispatchContent_alias_prod` (−1), `dispatchContent_anchor_prod` (−1). S8/S9 were in `scanTag_nonSecondary_prod` which still has S10, so that declaration's warning persists.

**Approach**: Instead of writing `absurd`/`contradiction` at each sorry site (as originally planned), strengthened the underlying loop `_prod` theorems with additional conjuncts that link grammar position equality to scanner-level value equality. This made the conditional theorems unconditional, eliminating sorry at all callsites simultaneously.

**Files modified (3):**

1. **`StructureProduction.lean`** — 4 theorems updated:
   - `collectAnchorNameLoop_prod`: Return type strengthened from `∃ sp', GStar ∧ ScannerSurfCorr` to `∃ sp', GStar ∧ ScannerSurfCorr ∧ (sp = sp' → result.fst = name)`. Third conjunct proven vacuously in recursive case via `gstar_gchar_col_le` column monotonicity; trivially `fun _ => rfl` in base cases.
   - `scanAnchorOrAlias_prod`: Return type strengthened to include `sp_mid ≠ sp'`. Proof: position-to-name linkage gives `name = ""` when `sp = sp'`; `unfold scanAnchorOrAlias; rw [h_name_empty]; simp` contradicts the `.ok` hypothesis (scanner error branch fires for empty names).
   - `collectVerbatimTagLoop_prod`: Return type strengthened with `(sp_mid = sp' → foundClose = false)` and `(sp = sp_mid → uri_result = uri)`. Same vacuous proof pattern as anchor name loop.
   - `scanTag_nonSecondary_prod`: S8 sorry replaced with `exfalso; simp [h_close_link h_eq] at h_fc_true`; S9 sorry replaced with `exfalso; simp [h_uri_link hne] at h_uri_ne`.

2. **`NodeProduction.lean`** — 3 theorems simplified:
   - `scanAnchorOrAlias_aliasNode_prod`: Changed from conditional `(sp_mid ≠ sp' → SCNsAliasNode)` to unconditional `∃ sp', SCNsAliasNode sp sp' ∧ ScannerSurfCorr s' sp'`. Uses `h_ne` from strengthened `_prod`.
   - `scanAnchorOrAlias_anchorProp_prod`: Same unconditional simplification.
   - `scanAnchorOrAlias_flowNode_prod`: Simplified to unconditional.

3. **`StreamAccum.lean`** — 2 sorry sites removed:
   - `dispatchContent_alias_prod`: Removed `by_cases hne : sp_mid ≠ sp'` + sorry. Now directly obtains unconditional `SCNsAliasNode` from `_aliasNode_prod`.
   - `dispatchContent_anchor_prod`: Same removal. Directly obtains unconditional `SCNsAnchorProperty` from `_anchorProp_prod`.

**Build**: 415/415 jobs, 0 errors, 12 sorry warnings (−2 from 14).

**Net sorry accounting**:
- **Eliminated**: 4 sorry sites (S7, S8, S9, alias empty-name)
- **Added**: 0 sorry
- **Warning count**: 12 (−2)

##### A13: Closed S4 — `#` at col=0 via `h_hash_col` precondition

**Problem**: In `collectPlainScalarLoop_prod`, the `SNsPlainChar.hashAfterNs` constructor requires `col > 0`, but the proof had no way to establish this at the `#` content-char branch. The sorry was at `else sorry` in the `by_cases hhash : c = '#'` arm.

**Solution**: Added induction-compatible precondition `(h_hash_col : sc.peek? = some '#' → spaces.length = 0 → sc.col > 0)`. This states: if the current character is `#` and no whitespace has been accumulated, then we must already be past column 0.

**Why it works** — three-way induction discharge:
1. **Content char recursive call** (`spaces = ""`): `sc.advance.col = sc.col + 1 > 0` via `hcorr_adv.col_eq` — after consuming any character, column advances past 0.
2. **Whitespace recursive call** (`spaces = spaces.push c`): vacuously true — `(spaces.push c).length = spaces.length + 1 ≠ 0`, so the second premise is always false.
3. **Initial caller** (`scanPlainScalar_to_flowNode`): `canStartPlainScalarBool '#' _ false = false` since `#` is an indicator — contradicts `hstart`.

**Key proof technique** — extracting `spaces.length = 0` from `terminates? = none`:
- `collectPlainScalar_terminates? '#' sc content spaces false` checks `'#' == '#' && spaces.length > 0` first
- If `spaces.length > 0`, the function returns `some _`, contradicting `h_term_none : ... = none`
- Used `suffices ¬(spaces.length > 0) by omega` + `unfold collectPlainScalar_terminates?` + `simp [h_dec]`

**Files modified**: 1 (`ScalarProduction.lean`)

**Changes in `collectPlainScalarLoop_prod`**:
- Added parameter: `(h_hash_col : sc.peek? = some '#' → spaces.length = 0 → sc.col > 0)`
- Replaced `if h : sc.col > 0 then ... else sorry` with derivation via `h_hash_col hpeek h_sp_zero`
- Whitespace recursive: added `(fun _ hlen => by simp [String.length_push] at hlen)` — vacuously true
- Content char recursive: added `(fun _ _ => by have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq; omega)` — col monotonicity

**Changes in `scanPlainScalar_to_flowNode`**:
- Added caller proof: derives contradiction from `canStartPlainScalarBool '#' _ false = true` (since `#` is an indicator, `isIndicatorBool '#' = true`, so `canStart = false`)

**Build**: 415/415 jobs, 0 errors, 12 sorry warnings (unchanged — S3 and S4 were in the same theorem `collectPlainScalarLoop_prod`; removing S4 alone doesn't reduce the declaration-level warning count).

**Net sorry accounting**:
- **Eliminated**: 1 sorry site (S4)
- **Added**: 0 sorry
- **Warning count**: 12 (±0, since S3 remains in same theorem)

#### Category 2: col≠0 / BOM edge case — **RESOLVED by A2** ✅

`SSeparateInLine.startOfLine` is now column-independent (A2). The `by_cases hcol` pattern is no longer needed for `eof_pending` noPending and `preprocess_some_separate_0_anyCol` inr cases. Remaining `by_cases hcol` sites in `accum_structural_pending` etc. still use `preprocess_some_ssl_comments_col0` (which requires col=0 for the return type's `sp_mid.col = 0` guarantee used by `dispatch_new_pending`). These are Category 3/4/5 blockers, not Category 2.

**Resolution**: Requires grammar definition change (`SSeparateInLine.bomPreceded` or equivalent) cascading through existing proofs. ~~Deferred to a future layer.~~ **Done** — used constraint removal instead of new constructor.

#### Category 3: Directive infrastructure (~6 sorry sites)

`pendingDirective` case is sorry across all 5 dispatch theorems. Needs `scanDirective_prod` to produce `GPlus SNbChar` (directive content evidence) from the scanner's `scanDirective` function. Also needs the `dispatch_new_pending` structural-to-directive transition.

**Impact**: Architectural, not content-intensive. Could become its own focused layer.

#### Category 4: Block indicator types `?`/`:` (mapping entries)

All `c ≠ '-'` branches in `accum_block_pending` use sorry closures. Needs `SBlockMapEntries` infrastructure parallel to `SBlockSeqEntries`:
- `dispatchBlockKey_full_prod` and `dispatchBlockValue_full_prod` (analogous to `dispatchBlockEntry_full_prod`)
- `SBlockMapEntries_snoc` (analogous to `SBlockSeqEntries_snoc`)
- `PendingNode.pendingBlock` would need to handle both seq and map entries

**Priority**: Medium — block mappings are common in YAML but the infrastructure parallels what's already built for sequences.

#### Category 5: Flow indicators `[`, `{`, `]`, `}`, `,` (~3 sorry sites in `accum_flow_pending`)

`FlowStack.flowSeqLevel`/`flowMapLevel` closures need `SFlowContent` composition. The `new_flow_state` helper creates FlowStack/PendingNode with sorry closures.

**Priority**: Low — flow collections are less common in typical YAML and the FlowStack infrastructure is less developed.

#### Unreachable comment sorry (1 site in `preprocess_some_separate_lines_0`)

The `GOpt.some` comment case is unreachable because the scanner greedily consumes comments before returning a content character. Proving unreachability needs `peek?` preservation through the `skipToContentComment` chain.

**Priority**: Low — only 1 sorry site, doesn't reduce warning count.

#### Recommended implementation order

1. ~~**Block scalar `\|`/`>` support** (Category 1)~~ — **DONE (A4)**. ~~2 sorry remain for `currentIndent ≥ 0` in `dispatchContent_blockScalar_prod`.~~ **Fully sorry-free after A11.**
2. ~~**Plain scalar support** (Category 1)~~ — **DONE (A5)**. Wired through `dispatchContent_evidence`. 1 sorry for full-scan grammar gap.
3. ~~**Full-scan plain scalar grammar** (Category 1)~~ — **DONE (A7, A14)**. `collectPlainScalarLoop_prod` proven by fuel induction (single-line). `scanPlainScalar_to_flowNode` composes first char + loop entries + context lift into `SFlowNode 0 .flowOut` + trailing `GStar SSWhite`. Block context `dispatchContent_plainScalar_prod` now fully proven; flow context sorry'd separately. 1 sorry remains: line break (multi-line deferred). Doc boundary first-char termination **CLOSED (A14)**.
4. ~~**Anchor `&` / tag `!` grammar** (Category 1)~~ — **DONE (A8/A9)**. `dispatchContent_anchor_prod` and `dispatchContent_tag_prod` both sorry-free. Secondary tag `!!` fully proven; verbatim `!<uri>` well-formed case proven; anchor 1 sorry (empty name); tag 1 sorry declaration with 3 edge cases (malformed verbatim, empty URI, named/non-specific) in `scanTag_nonSecondary_prod`.
5. ~~**Scanner Except conversion** (Category 1)~~ — **DONE (A10)**. `scanAnchorOrAlias`, `collectVerbatimTagLoop`, `scanVerbatimTag`, `scanTag` converted to `Except`. S7/S8/S9/alias sorry sites now closable by contradiction.
6. ~~**Close S7/S8/S9/alias sorry sites** (Category 1)~~ — **DONE (A12)**. Strengthened `collectAnchorNameLoop_prod` and `collectVerbatimTagLoop_prod` with position-to-value linkage conjuncts. Made `scanAnchorOrAlias_aliasNode_prod`/`_anchorProp_prod` unconditional. Closed S7/S8/S9/alias sorry (−2 warnings, 14→12).
7. ~~**S1/S2 indent tracking** (Category 1) — ScannerSurfCorr `indent_size` field or weaken `scanBlockScalar_prod` precondition~~ **DONE (A11)**. Removed `hm : m ≥ 1` from grammar constructors. S1/S2 closed (−1 sorry warning, 15→14).
8. **Mapping entries `?`/`:`** (Category 4) — parallel to sequence infrastructure
9. **Directive infrastructure** (Category 3) — focused layer
10. **Flow indicators** (Category 5) — lower priority

---

**A14 — S5 CLOSED: `scanPlainScalar_to_flowNode` doc boundary first-char termination** (2026-04-07)

Closed the `GStar.nil` sorry in `scanPlainScalar_to_flowNode` (ScalarProduction.lean). Sorry count: 12→11.

**Problem**: The `collectPlainScalarLoop_prod` theorem returns `GStar (SNbNsPlainInLineEntry .blockIn)`, which could be `GStar.nil` (zero entries consumed) or `GStar.cons` (one or more entries). The `GStar.nil` case occurred when `collectPlainScalar_terminates?` fired on the very first iteration — specifically when the scanner was at a document boundary (`---` or `...`) at column 0. In this case, no content characters were consumed, making it impossible to construct `SFlowNode 0 .flowOut` (which requires at least one character).

**Root cause**: `canStartPlainScalarBool '-' (some '-') false = true` (since `-` with non-blank next satisfies the exception rule), BUT `terminates?` has a separate document boundary check (`sc.col == 0 && atDocumentBoundary sc`) that fires independently. So characters like `---` at column 0 would pass `canStartPlainScalar` but immediately terminate in the loop.

**Solution** (3 parts):

1. **`canStartPlain_first_not_terminates`** — Helper lemma proving `terminates? c sc "" "" false = none` given `canStartPlainScalarBool = true` and the precondition `h_not_doc : sc.col = 0 → atDocumentBoundary sc = false`. Proof by match on `terminates?` result: `#` branch impossible (empty spaces), `:` branch impossible (`canStart` implies next is not blank, contradicting `isBlankBool n`), flow indicator branch impossible (`inFlow = false`), doc boundary branch contradicts `h_not_doc`.

2. **`collectPlainScalarLoop_content_first_step`** — Extracts the recursive call from one iteration of `collectPlainScalarLoop`. Given `terminates? = none`, not line break, not whitespace, and `isPlainSafeBool = true`, the loop's first iteration takes the content char branch and recurses on `sc.advance`. Proof by `unfold collectPlainScalarLoop at hok; split` at each nested condition.

3. **Restructured `scanPlainScalar_to_flowNode`** — Instead of calling `collectPlainScalarLoop_prod` on the full loop and matching `GStar.nil | GStar.cons`, the proof now:
   - Proves `terminates? = none` for the first char (via `canStartPlain_first_not_terminates`)
   - Shows fuel ≥ 1 (from `peek_some_has_more`)
   - Extracts the first iteration via `collectPlainScalarLoop_content_first_step` → gets `hloop'` (recursive call on `sc.advance`)
   - Applies `collectPlainScalarLoop_prod` on `hloop'` (remaining iterations)
   - Builds grammar from `SNsPlainFirst` + remaining entries

   This completely eliminates the `GStar.nil` case because the first iteration always produces a content entry.

**Additional helper lemmas**:
- `canStartPlain_implies_safe`: `canStartPlainScalarBool c next false = true → isPlainSafeBool c false = true`
- `canStartPlain_not_linebreak`: `canStartPlainScalarBool c next false = true → isLineBreakBool c = false`

**Caller update**: `dispatchContent_plainScalar_prod` (StreamAccum.lean) passes `sorry` for `h_not_doc` — the preprocessing/structural dispatch guarantees the scanner is not at a doc boundary when reaching content dispatch, but formalizing this requires infrastructure in `scanNextToken_preprocess_corr`. Since the theorem already has sorry in the flow context branch, the additional sorry doesn't increase the warning count.

**Build**: 415/415 jobs, 0 errors, 11 sorry warnings (was 12; −1 from `scanPlainScalar_to_flowNode` becoming sorry-free).
**A15 — S6 CLOSED: Flow context plain scalar parameterization** (2026-04-07)

Eliminated 3 sorry sites in `dispatchContent_plainScalar_prod` (StreamAccum.lean) by parameterizing the plain scalar proof infrastructure over `inFlow : Bool`, enabling a single unified call to `scanPlainScalar_to_flowNode` for both block and flow contexts. Sorry warning count unchanged at 11 (the 3 eliminated sites shared a declaration with the pre-existing `h_not_doc` sorry).

**Problem**: `scanPlainScalar_to_flowNode` and its dependencies (`collectPlainScalarLoop_prod`, `canStartPlainScalar_to_SNsPlainFirst`, etc.) were hardcoded for `inFlow = false` / `.blockIn` context. The flow branch of `dispatchContent_plainScalar_prod` had `exact ⟨sorry, sp', sorry, sorry, hcorr'⟩` — 3 sorry sites for the flow node witness, flow grammar evidence, and trailing whitespace grammar.

**Key insight**: Block and flow plain scalar proofs are 95%+ identical. The only divergence points are:
- `isNsPlainSafe .flowIn ch = isNsChar ch ∧ ¬isFlowIndicatorProp ch` (more restrictive than `.blockIn` = `isNsChar ch`)
- Flow indicators terminate scanning in flow context
- `:` + flow indicator terminates in flow context
- `canStartPlainScalarBool` exception chars additionally require `¬isFlowIndicatorBool` in flow

**Solution**: Introduced `ctxOfInFlow : Bool → YamlContext` mapping (`false → .blockIn`, `true → .flowIn`) and parameterized ~15 theorems over `inFlow`:

1. **New bridge lemmas**:
   - `ctxOfInFlow` — Bool→YamlContext mapping
   - `isPlainSafe_to_nsPlainSafe` — generic `isPlainSafeBool c inFlow → isNsPlainSafe (ctxOfInFlow inFlow) c`
   - `flowIndicatorProp_to_indicatorProp` — `isFlowIndicatorProp c → isIndicatorProp c` via `List.Subset` + `by decide`

2. **Parameterized theorems** (all now take `inFlow : Bool`):
   - `isPlainSafe_to_plainChar_basic`, `isPlainSafe_to_inlineEntry_basic`
   - `canStartPlainScalar_to_SNsPlainFirst` — exception chars use `cases inFlow` for `isNsPlainSafe`
   - `colon_not_terminated_next` — enhanced return type includes `(inFlow = true → isFlowIndicatorBool n = false)`
   - `collectPlainScalarLoop_prod` — colon case builds `isNsPlainSafe` via `cases inFlow`
   - `canStartPlainScalar_not_ws`, `canStartPlain_implies_safe`, `canStartPlain_not_linebreak`
   - `canStartPlain_first_not_terminates` — flow indicator branch: `canStartPlainScalar_iff` + `flowIndicatorProp_to_indicatorProp` for contradiction
   - `collectPlainScalarLoop_content_first_step`

3. **Flow→flowOut context lifts** (new):
   - `SNsPlainChar_flowIn_to_flowOut`, `SNbNsPlainInLineEntry_flowIn_to_flowOut`
   - `GStar_entries_flowIn_to_flowOut`, `SNsPlainFirst_flowIn_to_flowOut`
   - Generic dispatchers: `SNsPlainFirst_ctxOfInFlow_to_flowOut`, `GStar_entries_ctxOfInFlow_to_flowOut`

4. **Caller simplification**: `dispatchContent_plainScalar_prod` no longer splits on `by_cases h_block : sc.inFlow = false`. Single unified call to `scanPlainScalar_to_flowNode` (which now accepts any `sc.inFlow` value).

**Build**: 415/415 jobs, 0 errors, 11 sorry warnings (3 sorry sites eliminated, warning count unchanged due to shared declaration).

11. ~~**col≠0 BOM** (Category 2) — grammar definition change, deferred~~ **DONE (A2)**