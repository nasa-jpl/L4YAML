# YAML 1.2.2 Production Rule Cross-Reference

This document maps every YAML 1.2.2 grammar production to its corresponding
Lean4 definition in this project. It serves as the single source of truth
for spec coverage.

## Status Legend

| Symbol | Meaning |
|--------|---------|
| ✓ G | Specified in `Grammar.lean` (formal proposition) |
| ✓ P | Implemented in `Parser/*.lean` |
| ✓ GP | Both specified and implemented |
| ⊘ | Out of scope (intentionally not supported) |
| ◌ | TODO (planned but not yet implemented) |

## Chapter 5: Character Productions

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [1] | `c-printable` | ✓ G | `Grammar.isPrintable` |
| [2] | `nb-json` | ⊘ | JSON subset, not needed |
| [3] | `c-byte-order-mark` | ✓ P | `Document.skipBOM` |
| [4] | `c-sequence-entry` | ✓ P | `Block.blockSequenceItemsImpl` (char `-`) |
| [5] | `c-mapping-key` | ✓ P | `Block.blockMappingEntryImpl` (char `?`) |
| [6] | `c-mapping-value` | ✓ P | `Block.blockMappingEntryImpl` (char `:`) |
| [7] | `c-collect-entry` | ✓ P | `Flow.flowSequenceItemsImpl` (char `,`) |
| [8] | `c-sequence-start` | ✓ P | `Flow.flowSequenceImpl` (char `[`) |
| [9] | `c-sequence-end` | ✓ P | `Flow.flowSequenceImpl` (char `]`) |
| [10] | `c-mapping-start` | ✓ P | `Flow.flowMappingImpl` (char `{`) |
| [11] | `c-mapping-end` | ✓ P | `Flow.flowMappingImpl` (char `}`) |
| [12] | `c-comment` | ✓ P | `Combinators.comment` (char `#`) |
| [13] | `c-anchor` | ✓ P | `Anchor.parseAnchorPrefix` (char `&`) |
| [14] | `c-alias` | ✓ P | `Anchor.parseAlias` (char `*`) |
| [15] | `c-tag` | ✓ P | `Tag.parseTagPrefix` (char `!`) |
| [16] | `c-literal` | ✓ P | `Scalar.blockScalar` (char `\|`) |
| [17] | `c-folded` | ✓ P | `Scalar.blockScalar` (char `>`) |
| [18] | `c-single-quote` | ✓ P | `Scalar.singleQuotedScalar` (char `'`) |
| [19] | `c-double-quote` | ✓ P | `Scalar.doubleQuotedScalar` (char `"`) |
| [20] | `c-directive` | ✓ P | `Document.directive` (char `%`) |
| [21] | `c-reserved` | ⊘ | `@`, `` ` `` — rejected by indicator check |
| [22] | `c-indicator` | ✓ P | `Combinators.isIndicator` |
| [23] | `c-flow-indicator` | ✓ GP | `Grammar.isFlowIndicator`, `Combinators.isFlowIndicator` |
| [24] | `b-line-feed` | ✓ GP | `Grammar.isLineBreak`, `Combinators.isLineBreak` (char LF) |
| [25] | `b-carriage-return` | ✓ GP | `Grammar.isLineBreak`, `Combinators.isLineBreak` (char CR) |
| [26] | `b-char` | ✓ GP | `Grammar.isLineBreak`, `Combinators.isLineBreak` |
| [27] | `nb-char` | ✓ GP | `Grammar.isPrintable` ∧ ¬`isLineBreak` (implicit) |
| [28] | `b-break` | ✓ P | `Combinators.newline` (LF / CR / CRLF) |
| [29] | `b-as-line-feed` | ✓ P | `Combinators.newline` |
| [30] | `b-non-content` | ✓ P | `Combinators.newline` |
| [31] | `s-space` | ✓ GP | `Grammar.isIndentChar`, `Combinators.space` |
| [32] | `s-tab` | ✓ GP | `Grammar.isWhiteSpace` (char TAB) |
| [33] | `s-white` | ✓ GP | `Grammar.isWhiteSpace`, `Combinators.isWhiteSpace` |
| [34] | `ns-char` | ✓ GP | `Grammar.isPrintable` ∧ ¬`isWhiteSpace` (implicit) |
| [35] | `ns-dec-digit` | ✓ P | Used in `Scalar.escapeSequence` hex parsing |
| [36] | `ns-hex-digit` | ✓ P | `Scalar.escapeSequence` → `hexDigit` |
| [37] | `ns-ascii-letter` | ⊘ | Not used directly |
| [38] | `ns-word-char` | ✓ P | `Combinators.isAnchorChar` (superset) |
| [39] | `ns-uri-char` | ✓ P | `Tag.isTagChar` (subset) |
| [40] | `ns-tag-char` | ✓ P | `Tag.isTagChar` |
| [41] | `c-escape` | ✓ P | `Scalar.escapeSequence` (char `\`) |
| [42] | `ns-esc-null` | ✓ GP | `Grammar.resolveNamedEscape '0'`, `Scalar.escapeSequence` |
| [43] | `ns-esc-bell` | ✓ GP | `Grammar.resolveNamedEscape 'a'`, `Scalar.escapeSequence` |
| [44] | `ns-esc-backspace` | ✓ GP | `Grammar.resolveNamedEscape 'b'`, `Scalar.escapeSequence` |
| [45] | `ns-esc-horizontal-tab` | ✓ GP | `Grammar.resolveNamedEscape 't'`, `Scalar.escapeSequence` |
| [46] | `ns-esc-horizontal-tab` (literal) | ✓ GP | `Grammar.resolveNamedEscape '\t'`, `Scalar.escapeSequence` |
| [47] | `ns-esc-line-feed` | ✓ GP | `Grammar.resolveNamedEscape 'n'`, `Scalar.escapeSequence` |
| [48] | `ns-esc-vertical-tab` | ✓ GP | `Grammar.resolveNamedEscape 'v'`, `Scalar.escapeSequence` |
| [49] | `ns-esc-form-feed` | ✓ GP | `Grammar.resolveNamedEscape 'f'`, `Scalar.escapeSequence` |
| [50] | `ns-esc-carriage-return` | ✓ GP | `Grammar.resolveNamedEscape 'r'`, `Scalar.escapeSequence` |
| [51] | `ns-esc-escape` | ✓ GP | `Grammar.resolveNamedEscape 'e'`, `Scalar.escapeSequence` |
| [52] | `ns-esc-space` | ✓ GP | `Grammar.resolveNamedEscape ' '`, `Scalar.escapeSequence` |
| [53] | `ns-esc-double-quote` | ✓ GP | `Grammar.resolveNamedEscape '"'`, `Scalar.escapeSequence` |
| [54] | `ns-esc-slash` | ✓ GP | `Grammar.resolveNamedEscape '/'`, `Scalar.escapeSequence` |
| [55] | `ns-esc-backslash` | ✓ GP | `Grammar.resolveNamedEscape '\\\\'`, `Scalar.escapeSequence` |
| [56] | `ns-esc-next-line` | ✓ GP | `Grammar.resolveNamedEscape 'N'`, `Scalar.escapeSequence` |
| [57] | `ns-esc-non-breaking-space` | ✓ GP | `Grammar.resolveNamedEscape '_'`, `Scalar.escapeSequence` |
| [58] | `ns-esc-8-bit` | ✓ P | `Scalar.escapeSequence` → `unicodeEscape 2` |
| [59] | `ns-esc-16-bit` | ✓ P | `Scalar.escapeSequence` → `unicodeEscape 4` |
| [60] | `ns-esc-32-bit` | ✓ P | `Scalar.escapeSequence` → `unicodeEscape 8` |
| [61] | `c-ns-esc-char` | ✓ P | `Scalar.escapeSequence` (full production) |

## Chapter 6: Basic Structures

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [63] | `s-indent(n)` | ✓ GP | `Grammar.Indented`, `Combinators.consumeIndent` |
| [64] | `s-indent(<n)` | ✓ G | `Grammar.IndentedAtLeast` (complement) |
| [65] | `s-indent(≤n)` | ✓ G | `Grammar.IndentedAtLeast` (adjusted) |
| [66] | `s-separate-in-line` | ✓ P | `Combinators.skipHWhitespace` |
| [67] | `s-line-prefix(n,c)` | ✓ P | `Combinators.consumeIndent` + `skipHWhitespace` |
| [68] | `l-empty(n,c)` | ✓ P | `Scalar.blockScalarContent.blockScalarLine` (blank-line handling) |
| [69] | `b-l-trimmed(n,c)` | ✓ P | `Scalar.foldQuotedNewlines` (blank-line tracking) |
| [70] | `b-as-space` | ✓ P | `Scalar.foldQuotedNewlines` (single break → space) |
| [71] | `b-l-folded(n,c)` | ✓ P | `Scalar.foldQuotedNewlines`, `Scalar.processFolded` |
| [72] | `s-flow-folded(n)` | ✓ P | `Scalar.foldQuotedNewlines` |
| [73] | `s-flow-line-prefix(n)` | ✓ P | `Flow.flowWhitespace` |
| [74] | `l-comment` | ✓ P | `Combinators.comment` + `Combinators.newline` |
| [75] | `c-nb-comment-text` | ✓ P | `Combinators.comment` |
| [76] | `b-comment` | ✓ P | `Combinators.newline` (at end of comment) |
| [77] | `s-b-comment` | ✓ P | `Combinators.skipTrailing` |
| [78] | `l-comment` | ✓ P | `Combinators.skipBlankLines` (comment-only lines) |
| [79] | `s-l-comments` | ✓ P | `Combinators.skipTrailing` + `Combinators.skipBlankLines` |
| [80] | `s-separate(n,c)` | ✓ P | `Flow.flowWhitespace`, `Combinators.skipHWhitespace` |
| [81] | `s-separate-lines(n)` | ✓ P | `Combinators.skipToNextLine` + `Combinators.consumeIndent` |
| [82] | `l-directive` | ✓ P | `Document.directive` |
| [83] | `ns-reserved-directive` | ✓ P | `Document.directive` (unknown directive branch) |
| [84] | `ns-yaml-directive` | ✓ P | `Document.directive` (`"YAML"` branch) |
| [85] | `ns-yaml-version` | ✓ P | `Document.directive` (version parsing) |
| [86] | `ns-tag-directive` | ✓ P | `Document.directive` (`"TAG"` branch) |
| [87] | `c-tag-handle` | ✓ P | `Tag.parseTagPrefix` (handle parsing) |
| [88] | `c-primary-tag-handle` | ✓ P | `Tag.parseTagPrefix` (`!suffix` branch) |
| [89] | `c-secondary-tag-handle` | ✓ P | `Tag.parseTagPrefix` (`!!suffix` branch) |
| [90] | `c-named-tag-handle` | ✓ P | `Tag.parseTagPrefix` (`!handle!suffix` branch) |
| [91] | `ns-tag-prefix` | ✓ P | `Document.directive` (`"TAG"` branch) |
| [92] | `c-ns-local-tag-prefix` | ✓ P | `Tag.parseTagPrefix` (local tag) |
| [93] | `ns-global-tag-prefix` | ✓ P | `Tag.parseTagPrefix` (verbatim tag) |
| [94] | `c-ns-properties(n,c)` | ✓ P | `Block.dispatchByCharImpl` (`&`/`!` branches), `Flow.flowValueImpl` |
| [95] | `c-ns-tag-property` | ✓ P | `Tag.parseTagPrefix` |
| [96] | `c-verbatim-tag` | ✓ P | `Tag.parseTagPrefix` (`!<uri>` branch) |
| [97] | `c-ns-shorthand-tag` | ✓ P | `Tag.parseTagPrefix` (handle branches) |
| [98] | `c-non-specific-tag` | ✓ P | `Tag.parseTagPrefix` (bare `!` branch) |
| [99] | `c-ns-anchor-property` | ✓ P | `Anchor.parseAnchorPrefix` |
| [100] | `c-anchor` | ✓ P | `Anchor.parseAnchorPrefix` (char `&`) |
| [101] | `ns-anchor-name` | ✓ P | `Anchor.anchorName` |
| [102] | `ns-anchor-char` | ✓ P | `Combinators.isAnchorChar` |

## Chapter 7: Flow Style Productions

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [103] | `c-ns-alias-node` | ✓ P | `Anchor.parseAlias` |
| [104] | `e-scalar` | ✓ P | `YamlValue.null` (implicit empty scalar) |
| [105] | `e-node` | ✓ P | `YamlValue.null` (implicit empty node) |
| [106] | `ns-double-char` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` |
| [107] | `c-double-quoted(n,c)` | ✓ GP | `Grammar.ValidDoubleQuoted`, `Scalar.doubleQuotedScalar` |
| [108] | `nb-double-text(n,c)` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` |
| [109] | `nb-double-one-line` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` (single-line path) |
| [110] | `s-double-escaped(n)` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` (`\\` + newline) |
| [111] | `s-double-break(n)` | ✓ P | `Scalar.foldQuotedNewlines` |
| [112] | `nb-ns-double-in-line` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` |
| [113] | `s-double-next-line(n)` | ✓ P | `Scalar.foldQuotedNewlines` |
| [114] | `nb-double-multi-line(n)` | ✓ P | `Scalar.doubleQuotedScalar` (multi-line path) |
| [115] | `c-quoted-quote` | ✓ P | `Scalar.singleQuotedScalar.collectChars` (`''` → `'`) |
| [116] | `nb-single-char` | ✓ P | `Scalar.singleQuotedScalar.collectChars` |
| [117] | `ns-single-char` | ✓ P | `Scalar.singleQuotedScalar.collectChars` |
| [118] | `c-single-quoted(n,c)` | ✓ GP | `Grammar.ValidSingleQuoted`, `Scalar.singleQuotedScalar` |
| [119] | `nb-single-text(n,c)` | ✓ P | `Scalar.singleQuotedScalar.collectChars` |
| [120] | `nb-single-one-line` | ✓ P | `Scalar.singleQuotedScalar.collectChars` (single-line path) |
| [121] | `s-single-next-line(n)` | ✓ P | `Scalar.foldQuotedNewlines` |
| [122] | `nb-single-multi-line(n)` | ✓ P | `Scalar.singleQuotedScalar` (multi-line path) |
| [123] | `ns-plain-first(c)` | ✓ GP | `Grammar.canStartPlainScalar`, `Combinators.canStartPlainScalar` |
| [124] | `ns-plain-safe(c)` | ✓ P | `Scalar.isPlainSafe` |
| [125] | `ns-plain-safe-out` | ✓ P | `Scalar.isPlainSafe` (inFlow=false) |
| [126] | `ns-plain-safe-in` | ✓ P | `Scalar.isPlainSafe` (inFlow=true) |
| [127] | `ns-plain-char(c)` | ✓ P | `Scalar.plainScalarContent.collectPlain` |
| [128] | `ns-plain(n,c)` | ✓ GP | `Grammar.ValidPlainScalarBlock/Flow`, `Scalar.plainScalarContent` |
| [129] | `nb-ns-plain-in-line(c)` | ✓ P | `Scalar.plainScalarContent.collectPlain` |
| [130] | `ns-plain-one-line(c)` | ✓ P | `Scalar.plainScalarSingleLine` |
| [131] | `s-ns-plain-next-line(n,c)` | ✓ P | `Scalar.plainScalarContent.collectLines/collectFlowLines` |
| [132] | `ns-plain-multi-line(n,c)` | ✓ P | `Scalar.plainScalarContent` (multi-line path) |
| [133] | `in-flow(c)` | ✓ P | Flow context parameter `inFlow : Bool` throughout |
| [134] | `c-flow-sequence(n,c)` | ✓ GP | `Grammar.ValidNode.flowSeq`, `Flow.flowSequenceImpl` |
| [135] | `ns-s-flow-seq-entries(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` |
| [136] | `ns-flow-seq-entry(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` (per-item logic) |
| [137] | `c-flow-mapping(n,c)` | ✓ GP | `Grammar.ValidNode.flowMap`, `Flow.flowMappingImpl` |
| [138] | `ns-s-flow-map-entries(n,c)` | ✓ P | `Flow.flowMappingEntriesImpl` |
| [139] | `ns-flow-map-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` |
| [140] | `ns-flow-map-explicit-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (`?` branch) |
| [141] | `ns-flow-map-implicit-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (implicit key branch) |
| [142] | `ns-flow-map-yaml-key-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` |
| [143] | `c-ns-flow-map-separate-value(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (`:` parsing) |
| [144] | `c-ns-flow-map-json-key-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (JSON-like key handling) |
| [145] | `c-ns-flow-map-adjacent-value(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (adjacent `:` after JSON key) |
| [146] | `ns-flow-pair(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` (implicit single-pair mapping) |
| [147] | `ns-flow-pair-entry(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` |
| [148] | `ns-flow-pair-yaml-key-entry(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` (YAML key in pair) |
| [149] | `c-ns-flow-pair-json-key-entry(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` (JSON key in pair) |
| [150] | `ns-s-implicit-yaml-key(c)` | ✓ P | Block/Flow implicit key detection |
| [151] | `c-s-implicit-json-key(c)` | ✓ P | Block/Flow JSON-like key detection |
| [152] | `c-flow-json-node(n,c)` | ⊘ | Subsumed by `flowValueImpl` |
| [153] | `ns-flow-yaml-node(n,c)` | ✓ P | `Flow.flowValueImpl` |
| [154] | `c-flow-json-content(n,c)` | ✓ P | `Flow.flowValueImpl` (collection dispatch) |
| [155] | `ns-flow-content(n,c)` | ✓ P | `Flow.flowValueImpl` |
| [156] | `ns-flow-yaml-content(n,c)` | ✓ P | `Flow.flowScalar` |
| [157] | `ns-flow-node(n,c)` | ✓ P | `Flow.flowValueImpl` |

## Chapter 8: Block Style Productions

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [158] | `c-b-block-header(m,t)` | ✓ GP | `Grammar.isBlockScalarHeaderChar`, `Scalar.blockScalarHeader` |
| [159] | `c-indentation-indicator(m)` | ✓ GP | `Grammar.isBlockScalarHeaderChar` (digit `1`–`9`), `Scalar.blockScalarHeader` |
| [160] | `c-chomping-indicator(t)` | ✓ GP | `Grammar.ChompStyle`, `Scalar.blockScalarHeader` |
| [161] | `b-chomped-last(t)` | ✓ P | `Scalar.applyChomp` |
| [162] | `l-chomped-empty(n,t)` | ✓ P | `Scalar.applyChomp` |
| [163] | `l-strip-empty(n)` | ✓ P | `Scalar.applyChomp` (strip branch) |
| [164] | `l-keep-empty(n)` | ✓ P | `Scalar.applyChomp` (keep branch) |
| [165] | `l-trail-comments(n)` | ✓ P | `Scalar.blockScalarHeader` (trailing comment) |
| [166] | `l-literal-content(n,t)` | ✓ P | `Scalar.blockScalarContent` + `Scalar.processLiteral` |
| [167] | `l-nb-literal-text(n)` | ✓ P | `Scalar.blockScalarContent.blockScalarLine` |
| [168] | `b-nb-literal-next(n)` | ✓ P | `Scalar.blockScalarContent.collectLines` |
| [169] | `l-literal-content(n,t)` | ✓ P | `Scalar.blockScalarContent` |
| [170] | `c-l+literal(n)` | ✓ GP | `Grammar.ValidLiteralScalar`, `Scalar.blockScalar` (literal path) |
| [171] | `s-nb-folded-text(n)` | ✓ P | `Scalar.blockScalarContent.blockScalarLine` (folded) |
| [172] | `b-l-spaced(n)` | ✓ P | `Scalar.processFolded` (more-indented handling) |
| [173] | `s-b-folded(n,c)` | ✓ P | `Scalar.processFolded` |
| [174] | `l-folded-content(n,t)` | ✓ P | `Scalar.blockScalarContent` + `Scalar.processFolded` |
| [175] | `c-l+folded(n)` | ✓ GP | `Grammar.ValidFoldedScalar`, `Scalar.blockScalar` (folded path) |
| [176] | `s-l+block-in-block(n,c)` | ✓ P | `Block.blockValueImpl` |
| [177] | `s-l+block-scalar(n,c)` | ✓ P | `Scalar.blockScalar` |
| [178] | `s-l+block-collection(n,c)` | ✓ P | `Block.blockValueImpl` (collection dispatch) |
| [179] | `seq-spaces(n,c)` | ✓ P | `Block.blockValueImpl` (effectiveMinIndent) |
| [180] | `l+block-sequence(n)` | ✓ GP | `Grammar.ValidNode.blockSeq`, `Block.blockSequenceImpl` |
| [181] | `c-l-block-seq-entry(n)` | ✓ P | `Block.blockSequenceItemsImpl` |
| [182] | `s-l+block-indented(n,c)` | ✓ P | `Block.blockValueImpl`/`blockValueSameLineImpl` |
| [183] | `ns-l-compact-sequence(n)` | ✓ P | `Block.blockSequenceImpl` (compact notation) |
| [184] | `l+block-mapping(n)` | ✓ GP | `Grammar.ValidNode.blockMap`, `Block.blockMappingImpl` |
| [185] | `ns-l-block-map-entry(n)` | ✓ P | `Block.blockMappingEntryImpl` |
| [186] | `c-l-block-map-explicit-key(n)` | ✓ P | `Block.blockMappingEntryImpl` (`?` branch) |
| [187] | `l-block-map-explicit-value(n)` | ✓ P | `Block.blockMappingEntryImpl` (`:` after explicit key) |
| [188] | `ns-l-block-map-implicit-entry(n)` | ✓ P | `Block.blockMappingEntryImpl` (simple key branch) |
| [189] | `ns-s-block-map-implicit-key` | ✓ P | `Block.blockMappingKeyImpl` |
| [190] | `c-l-block-map-implicit-value(n)` | ✓ P | `Block.blockMappingEntryImpl` (`:` after simple key) |
| [191] | `ns-l-compact-mapping(n)` | ✓ P | `Block.blockMappingImpl` (compact notation) |
| [192] | `s-l+block-node(n,c)` | ✓ P | `Block.blockValueImpl` |
| [193] | `s-l+flow-in-block(n)` | ✓ P | `Block.dispatchByCharImpl` (flow collection dispatch) |
| [194] | `s-l+block-in-block(n,c)` | ✓ P | `Block.blockValueImpl` |
| [195] | `s-l+block-scalar(n,c)` | ✓ P | `Block.dispatchByCharImpl` (`\|`/`>` branches) |

## Chapter 9: Document Stream Productions

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [196] | `l-document-prefix` | ✓ P | `Document.document` (BOM + directives) |
| [197] | `c-directives-end` | ✓ P | `Document.documentStartMarker` (`---`) |
| [198] | `c-document-end` | ✓ P | `Document.documentEndMarker` (`...`) |
| [199] | `l-document-suffix` | ✓ P | `Document.documentEndMarker` + trailing |
| [200] | `c-forbidden` | ✓ GP | `Grammar.isCForbiddenPrefix`, `Scalar.foldQuotedNewlines` |
| [201] | `l-bare-document` | ✓ P | `Document.document` (bare document path) |
| [202] | `l-explicit-document` | ✓ P | `Document.document` (explicit document path) |
| [203] | `l-directive-document` | ✓ P | `Document.document` (directive + explicit) |
| [204] | `l-any-document` | ✓ P | `Document.document` |
| [205] | `l-yaml-stream` | ✓ GP | `Grammar.ValidStream`, `Document.yamlStream` |

## Coverage Summary

| Chapter | Total | ✓ GP | ✓ P | ✓ G | ⊘ | ◌ |
|---------|-------|------|-----|-----|---|---|
| 5: Characters | 61 | 25 | 33 | 1 | 2 | 0 |
| 6: Basic Structures | 40 | 1 | 39 | 0 | 0 | 0 |
| 7: Flow Styles | 55 | 6 | 48 | 0 | 1 | 0 |
| 8: Block Styles | 38 | 6 | 32 | 0 | 0 | 0 |
| 9: Documents | 10 | 2 | 8 | 0 | 0 | 0 |
| **Total** | **204** | **40** | **160** | **1** | **3** | **0** |

> **Note**: Production numbers in this table follow the YAML 1.2.2
> specification numbering. Some numbers are absent from the spec itself
> (gaps in the sequence). The [62] production (`c-ns-esc-char`) is listed
> as [61] above per the consolidated numbering in the spec document.
