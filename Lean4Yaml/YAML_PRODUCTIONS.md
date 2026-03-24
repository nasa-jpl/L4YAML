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
| ✓ P† | Implemented but with **known limitation** (see notes in Implementation column) |
| ⊘ | Out of scope (intentionally not supported) |
| ◌ | TODO (planned but not yet implemented) |

## Chapter 5: Character Productions

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [1](https://yaml.org/spec/1.2.2/#rule-c-printable) | `c-printable` | ✓ G | `Grammar.isPrintable` |
| [2](https://yaml.org/spec/1.2.2/#rule-nb-json) | `nb-json` | ⊘ | JSON subset, not needed |
| [3](https://yaml.org/spec/1.2.2/#rule-c-byte-order-mark) | `c-byte-order-mark` | ✓ P | `Document.skipBOM` |
| [4](https://yaml.org/spec/1.2.2/#rule-c-sequence-entry) | `c-sequence-entry` | ✓ P | `Block.blockSequenceItemsImpl` (char `-`) |
| [5](https://yaml.org/spec/1.2.2/#rule-c-mapping-key) | `c-mapping-key` | ✓ P | `Block.blockMappingEntryImpl` (char `?`) |
| [6](https://yaml.org/spec/1.2.2/#rule-c-mapping-value) | `c-mapping-value` | ✓ P | `Block.blockMappingEntryImpl` (char `:`) |
| [7](https://yaml.org/spec/1.2.2/#rule-c-collect-entry) | `c-collect-entry` | ✓ P | `Flow.flowSequenceItemsImpl` (char `,`) |
| [8](https://yaml.org/spec/1.2.2/#rule-c-sequence-start) | `c-sequence-start` | ✓ P | `Flow.flowSequenceImpl` (char `[`) |
| [9](https://yaml.org/spec/1.2.2/#rule-c-sequence-end) | `c-sequence-end` | ✓ P | `Flow.flowSequenceImpl` (char `]`) |
| [10](https://yaml.org/spec/1.2.2/#rule-c-mapping-start) | `c-mapping-start` | ✓ P | `Flow.flowMappingImpl` (char `{`) |
| [11](https://yaml.org/spec/1.2.2/#rule-c-mapping-end) | `c-mapping-end` | ✓ P | `Flow.flowMappingImpl` (char `}`) |
| [12](https://yaml.org/spec/1.2.2/#rule-c-comment) | `c-comment` | ✓ P | `Combinators.comment` (char `#`) |
| [13](https://yaml.org/spec/1.2.2/#rule-c-anchor) | `c-anchor` | ✓ P | `Anchor.parseAnchorPrefix` (char `&`) |
| [14](https://yaml.org/spec/1.2.2/#rule-c-alias) | `c-alias` | ✓ P | `Anchor.parseAlias` (char `*`) |
| [15](https://yaml.org/spec/1.2.2/#rule-c-tag) | `c-tag` | ✓ P | `Tag.parseTagPrefix` (char `!`) |
| [16](https://yaml.org/spec/1.2.2/#rule-c-literal) | `c-literal` | ✓ P | `Scalar.blockScalar` (char `\|`) |
| [17](https://yaml.org/spec/1.2.2/#rule-c-folded) | `c-folded` | ✓ P | `Scalar.blockScalar` (char `>`) |
| [18](https://yaml.org/spec/1.2.2/#rule-c-single-quote) | `c-single-quote` | ✓ P | `Scalar.singleQuotedScalar` (char `'`) |
| [19](https://yaml.org/spec/1.2.2/#rule-c-double-quote) | `c-double-quote` | ✓ P | `Scalar.doubleQuotedScalar` (char `"`) |
| [20](https://yaml.org/spec/1.2.2/#rule-c-directive) | `c-directive` | ✓ P | `Document.directive` (char `%`) |
| [21](https://yaml.org/spec/1.2.2/#rule-c-reserved) | `c-reserved` | ✓ P | `@`, `` ` `` — rejected by indicator check (`isIndicatorBool`) |
| [22](https://yaml.org/spec/1.2.2/#rule-c-indicator) | `c-indicator` | ✓ P | `Combinators.isIndicator` |
| [23](https://yaml.org/spec/1.2.2/#rule-c-flow-indicator) | `c-flow-indicator` | ✓ GP | `Grammar.isFlowIndicator`, `Combinators.isFlowIndicator` |
| [24](https://yaml.org/spec/1.2.2/#rule-b-line-feed) | `b-line-feed` | ✓ GP | `Grammar.isLineBreak`, `Combinators.isLineBreak` (char LF) |
| [25](https://yaml.org/spec/1.2.2/#rule-b-carriage-return) | `b-carriage-return` | ✓ GP | `Grammar.isLineBreak`, `Combinators.isLineBreak` (char CR) |
| [26](https://yaml.org/spec/1.2.2/#rule-b-char) | `b-char` | ✓ GP | `Grammar.isLineBreak`, `Combinators.isLineBreak` |
| [27](https://yaml.org/spec/1.2.2/#rule-nb-char) | `nb-char` | ✓ GP | `Grammar.isPrintable` ∧ ¬`isLineBreak` (implicit) |
| [28](https://yaml.org/spec/1.2.2/#rule-b-break) | `b-break` | ✓ P | `Combinators.newline` (LF / CR / CRLF) |
| [29](https://yaml.org/spec/1.2.2/#rule-b-as-line-feed) | `b-as-line-feed` | ✓ P | `Combinators.newline` |
| [30](https://yaml.org/spec/1.2.2/#rule-b-non-content) | `b-non-content` | ✓ P | `Combinators.newline` |
| [31](https://yaml.org/spec/1.2.2/#rule-s-space) | `s-space` | ✓ GP | `Grammar.isIndentChar`, `Combinators.space` |
| [32](https://yaml.org/spec/1.2.2/#rule-s-tab) | `s-tab` | ✓ GP | `Grammar.isWhiteSpace` (char TAB) |
| [33](https://yaml.org/spec/1.2.2/#rule-s-white) | `s-white` | ✓ GP | `Grammar.isWhiteSpace`, `Combinators.isWhiteSpace` |
| [34](https://yaml.org/spec/1.2.2/#rule-ns-char) | `ns-char` | ✓ GP | `Grammar.isPrintable` ∧ ¬`isWhiteSpace` (implicit) |
| [35](https://yaml.org/spec/1.2.2/#rule-ns-dec-digit) | `ns-dec-digit` | ✓ P | Used in `Scalar.escapeSequence` hex parsing |
| [36](https://yaml.org/spec/1.2.2/#rule-ns-hex-digit) | `ns-hex-digit` | ✓ P | `Scalar.escapeSequence` → `hexDigit` |
| [37](https://yaml.org/spec/1.2.2/#rule-ns-ascii-letter) | `ns-ascii-letter` | ✓ GP | `CharPredicates.isAsciiLetterBool/Prop` |
| [38](https://yaml.org/spec/1.2.2/#rule-ns-word-char) | `ns-word-char` | ✓ GP | `CharPredicates.isWordCharBool/Prop` |
| [39](https://yaml.org/spec/1.2.2/#rule-ns-uri-char) | `ns-uri-char` | ✓ GP | `CharPredicates.isUriCharBool/Prop` |
| [40](https://yaml.org/spec/1.2.2/#rule-ns-tag-char) | `ns-tag-char` | ✓ GP | `CharPredicates.isTagCharBool/Prop` |
| [41](https://yaml.org/spec/1.2.2/#rule-c-escape) | `c-escape` | ✓ P | `Scalar.escapeSequence` (char `\`) |
| [42](https://yaml.org/spec/1.2.2/#rule-ns-esc-null) | `ns-esc-null` | ✓ GP | `Grammar.resolveNamedEscape '0'`, `Scalar.escapeSequence` |
| [43](https://yaml.org/spec/1.2.2/#rule-ns-esc-bell) | `ns-esc-bell` | ✓ GP | `Grammar.resolveNamedEscape 'a'`, `Scalar.escapeSequence` |
| [44](https://yaml.org/spec/1.2.2/#rule-ns-esc-backspace) | `ns-esc-backspace` | ✓ GP | `Grammar.resolveNamedEscape 'b'`, `Scalar.escapeSequence` |
| [45](https://yaml.org/spec/1.2.2/#rule-ns-esc-horizontal-tab) | `ns-esc-horizontal-tab` | ✓ GP | `Grammar.resolveNamedEscape 't'`, `Scalar.escapeSequence` |
| [46](https://yaml.org/spec/1.2.2/#rule-ns-esc-horizontal-tab) | `ns-esc-horizontal-tab` (literal) | ✓ GP | `Grammar.resolveNamedEscape '\t'`, `Scalar.escapeSequence` |
| [47](https://yaml.org/spec/1.2.2/#rule-ns-esc-line-feed) | `ns-esc-line-feed` | ✓ GP | `Grammar.resolveNamedEscape 'n'`, `Scalar.escapeSequence` |
| [48](https://yaml.org/spec/1.2.2/#rule-ns-esc-vertical-tab) | `ns-esc-vertical-tab` | ✓ GP | `Grammar.resolveNamedEscape 'v'`, `Scalar.escapeSequence` |
| [49](https://yaml.org/spec/1.2.2/#rule-ns-esc-form-feed) | `ns-esc-form-feed` | ✓ GP | `Grammar.resolveNamedEscape 'f'`, `Scalar.escapeSequence` |
| [50](https://yaml.org/spec/1.2.2/#rule-ns-esc-carriage-return) | `ns-esc-carriage-return` | ✓ GP | `Grammar.resolveNamedEscape 'r'`, `Scalar.escapeSequence` |
| [51](https://yaml.org/spec/1.2.2/#rule-ns-esc-escape) | `ns-esc-escape` | ✓ GP | `Grammar.resolveNamedEscape 'e'`, `Scalar.escapeSequence` |
| [52](https://yaml.org/spec/1.2.2/#rule-ns-esc-space) | `ns-esc-space` | ✓ GP | `Grammar.resolveNamedEscape ' '`, `Scalar.escapeSequence` |
| [53](https://yaml.org/spec/1.2.2/#rule-ns-esc-double-quote) | `ns-esc-double-quote` | ✓ GP | `Grammar.resolveNamedEscape '"'`, `Scalar.escapeSequence` |
| [54](https://yaml.org/spec/1.2.2/#rule-ns-esc-slash) | `ns-esc-slash` | ✓ GP | `Grammar.resolveNamedEscape '/'`, `Scalar.escapeSequence` |
| [55](https://yaml.org/spec/1.2.2/#rule-ns-esc-backslash) | `ns-esc-backslash` | ✓ GP | `Grammar.resolveNamedEscape '\\\\'`, `Scalar.escapeSequence` |
| [56](https://yaml.org/spec/1.2.2/#rule-ns-esc-next-line) | `ns-esc-next-line` | ✓ GP | `Grammar.resolveNamedEscape 'N'`, `Scalar.escapeSequence` |
| [57](https://yaml.org/spec/1.2.2/#rule-ns-esc-non-breaking-space) | `ns-esc-non-breaking-space` | ✓ GP | `Grammar.resolveNamedEscape '_'`, `Scalar.escapeSequence` |
| [58](https://yaml.org/spec/1.2.2/#rule-ns-esc-8-bit) | `ns-esc-8-bit` | ✓ P | `Scalar.escapeSequence` → `unicodeEscape 2` |
| [59](https://yaml.org/spec/1.2.2/#rule-ns-esc-16-bit) | `ns-esc-16-bit` | ✓ P | `Scalar.escapeSequence` → `unicodeEscape 4` |
| [60](https://yaml.org/spec/1.2.2/#rule-ns-esc-32-bit) | `ns-esc-32-bit` | ✓ P | `Scalar.escapeSequence` → `unicodeEscape 8` |
| [61](https://yaml.org/spec/1.2.2/#rule-c-ns-esc-char) | `c-ns-esc-char` | ✓ P | `Scalar.escapeSequence` (full production) |

## Chapter 6: Basic Structures

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [63](https://yaml.org/spec/1.2.2/#rule-s-indent) | `s-indent(n)` | ✓ GP | `Grammar.Indented`, `Combinators.consumeIndent` |
| [64](https://yaml.org/spec/1.2.2/#rule-s-indent) | `s-indent(<n)` | ✓ G | `Grammar.IndentedAtLeast` (complement) |
| [65](https://yaml.org/spec/1.2.2/#rule-s-indent) | `s-indent(≤n)` | ✓ G | `Grammar.IndentedAtLeast` (adjusted) |
| [66](https://yaml.org/spec/1.2.2/#rule-s-separate-in-line) | `s-separate-in-line` | ✓ P | `Combinators.skipHWhitespace` |
| [67](https://yaml.org/spec/1.2.2/#rule-s-line-prefix) | `s-line-prefix(n,c)` | ✓ P | `Combinators.consumeIndent` + `skipHWhitespace` |
| [68](https://yaml.org/spec/1.2.2/#rule-l-empty) | `l-empty(n,c)` | ✓ P | `Scalar.blockScalarContent.blockScalarLine` (blank-line handling) |
| [69](https://yaml.org/spec/1.2.2/#rule-b-l-trimmed) | `b-l-trimmed(n,c)` | ✓ P | `Scalar.foldQuotedNewlines` (blank-line tracking) |
| [70](https://yaml.org/spec/1.2.2/#rule-b-as-space) | `b-as-space` | ✓ P | `Scalar.foldQuotedNewlines` (single break → space) |
| [71](https://yaml.org/spec/1.2.2/#rule-b-l-folded) | `b-l-folded(n,c)` | ✓ P | `Scalar.foldQuotedNewlines`, `Scalar.processFolded` |
| [72](https://yaml.org/spec/1.2.2/#rule-s-flow-folded) | `s-flow-folded(n)` | ✓ P | `Scalar.foldQuotedNewlines` |
| [73](https://yaml.org/spec/1.2.2/#rule-s-flow-line-prefix) | `s-flow-line-prefix(n)` | ✓ P | `Flow.flowWhitespace` |
| [74](https://yaml.org/spec/1.2.2/#rule-l-comment) | `l-comment` | ✓ P | `Combinators.comment` + `Combinators.newline` |
| [75](https://yaml.org/spec/1.2.2/#rule-c-nb-comment-text) | `c-nb-comment-text` | ✓ P† | `Combinators.comment` — **comment text discarded** (`dropMany`); Phase 8 will capture via `commentText` |
| [76](https://yaml.org/spec/1.2.2/#rule-b-comment) | `b-comment` | ✓ P | `Combinators.newline` (at end of comment) — structural, no text to capture |
| [77](https://yaml.org/spec/1.2.2/#rule-s-b-comment) | `s-b-comment` | ✓ P† | `Combinators.skipTrailing` — delegates to [75]; **comment text discarded** |
| [78](https://yaml.org/spec/1.2.2/#rule-l-comment) | `l-comment` | ✓ P† | `Combinators.skipBlankLines` (comment-only lines) — delegates to [75]; **comment text discarded** |
| [79](https://yaml.org/spec/1.2.2/#rule-s-l-comments) | `s-l-comments` | ✓ P† | `Combinators.skipTrailing` + `Combinators.skipBlankLines` — delegates to [75]; **comment text discarded** |
| [80](https://yaml.org/spec/1.2.2/#rule-s-separate) | `s-separate(n,c)` | ✓ P | `Flow.flowWhitespace`, `Combinators.skipHWhitespace` |
| [81](https://yaml.org/spec/1.2.2/#rule-s-separate-lines) | `s-separate-lines(n)` | ✓ P | `Combinators.skipToNextLine` + `Combinators.consumeIndent` |
| [82](https://yaml.org/spec/1.2.2/#rule-l-directive) | `l-directive` | ✓ P | `Document.directive` |
| [83](https://yaml.org/spec/1.2.2/#rule-ns-reserved-directive) | `ns-reserved-directive` | ✓ P | `Document.directive` (unknown directive branch) |
| [84](https://yaml.org/spec/1.2.2/#rule-ns-yaml-directive) | `ns-yaml-directive` | ✓ P | `Document.directive` (`"YAML"` branch) |
| [85](https://yaml.org/spec/1.2.2/#rule-ns-yaml-version) | `ns-yaml-version` | ✓ P | `Document.directive` (version parsing) |
| [86](https://yaml.org/spec/1.2.2/#rule-ns-tag-directive) | `ns-tag-directive` | ✓ P | `Document.directive` (`"TAG"` branch) |
| [87](https://yaml.org/spec/1.2.2/#rule-c-tag-handle) | `c-tag-handle` | ✓ P | `Tag.parseTagPrefix` (handle parsing) |
| [88](https://yaml.org/spec/1.2.2/#rule-c-primary-tag-handle) | `c-primary-tag-handle` | ✓ P | `Tag.parseTagPrefix` (`!suffix` branch) |
| [89](https://yaml.org/spec/1.2.2/#rule-c-secondary-tag-handle) | `c-secondary-tag-handle` | ✓ P | `Tag.parseTagPrefix` (`!!suffix` branch) |
| [90](https://yaml.org/spec/1.2.2/#rule-c-named-tag-handle) | `c-named-tag-handle` | ✓ P | `Tag.parseTagPrefix` (`!handle!suffix` branch) |
| [91](https://yaml.org/spec/1.2.2/#rule-ns-tag-prefix) | `ns-tag-prefix` | ✓ P | `Document.directive` (`"TAG"` branch) |
| [92](https://yaml.org/spec/1.2.2/#rule-c-ns-local-tag-prefix) | `c-ns-local-tag-prefix` | ✓ P | `Tag.parseTagPrefix` (local tag) |
| [93](https://yaml.org/spec/1.2.2/#rule-ns-global-tag-prefix) | `ns-global-tag-prefix` | ✓ P | `Tag.parseTagPrefix` (verbatim tag) |
| [94](https://yaml.org/spec/1.2.2/#rule-c-ns-properties) | `c-ns-properties(n,c)` | ✓ P | `Block.dispatchByCharImpl` (`&`/`!` branches), `Flow.flowValueImpl` |
| [95](https://yaml.org/spec/1.2.2/#rule-c-ns-tag-property) | `c-ns-tag-property` | ✓ P | `Tag.parseTagPrefix` |
| [96](https://yaml.org/spec/1.2.2/#rule-c-verbatim-tag) | `c-verbatim-tag` | ✓ P | `Tag.parseTagPrefix` (`!<uri>` branch) |
| [97](https://yaml.org/spec/1.2.2/#rule-c-ns-shorthand-tag) | `c-ns-shorthand-tag` | ✓ P | `Tag.parseTagPrefix` (handle branches) |
| [98](https://yaml.org/spec/1.2.2/#rule-c-non-specific-tag) | `c-non-specific-tag` | ✓ P | `Tag.parseTagPrefix` (bare `!` branch) |
| [99](https://yaml.org/spec/1.2.2/#rule-c-ns-anchor-property) | `c-ns-anchor-property` | ✓ P | `Anchor.parseAnchorPrefix` |
| [100](https://yaml.org/spec/1.2.2/#rule-c-anchor) | `c-anchor` | ✓ P | `Anchor.parseAnchorPrefix` (char `&`) |
| [101](https://yaml.org/spec/1.2.2/#rule-ns-anchor-name) | `ns-anchor-name` | ✓ P | `Anchor.anchorName` |
| [102](https://yaml.org/spec/1.2.2/#rule-ns-anchor-char) | `ns-anchor-char` | ✓ P | `Combinators.isAnchorChar` |

## Chapter 7: Flow Style Productions

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [103](https://yaml.org/spec/1.2.2/#rule-c-ns-alias-node) | `c-ns-alias-node` | ✓ P | `Anchor.parseAlias` |
| [104](https://yaml.org/spec/1.2.2/#rule-e-scalar) | `e-scalar` | ✓ P | `YamlValue.null` (implicit empty scalar) |
| [105](https://yaml.org/spec/1.2.2/#rule-e-node) | `e-node` | ✓ P | `YamlValue.null` (implicit empty node) |
| [106](https://yaml.org/spec/1.2.2/#rule-ns-double-char) | `ns-double-char` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` |
| [107](https://yaml.org/spec/1.2.2/#rule-c-double-quoted) | `c-double-quoted(n,c)` | ✓ GP | `Grammar.ValidDoubleQuoted`, `Scalar.doubleQuotedScalar` |
| [108](https://yaml.org/spec/1.2.2/#rule-nb-double-text) | `nb-double-text(n,c)` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` |
| [109](https://yaml.org/spec/1.2.2/#rule-nb-double-one-line) | `nb-double-one-line` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` (single-line path) |
| [110](https://yaml.org/spec/1.2.2/#rule-s-double-escaped) | `s-double-escaped(n)` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` (`\\` + newline) |
| [111](https://yaml.org/spec/1.2.2/#rule-s-double-break) | `s-double-break(n)` | ✓ P | `Scalar.foldQuotedNewlines` |
| [112](https://yaml.org/spec/1.2.2/#rule-nb-ns-double-in-line) | `nb-ns-double-in-line` | ✓ P | `Scalar.doubleQuotedScalar.collectChars` |
| [113](https://yaml.org/spec/1.2.2/#rule-s-double-next-line) | `s-double-next-line(n)` | ✓ P | `Scalar.foldQuotedNewlines` |
| [114](https://yaml.org/spec/1.2.2/#rule-nb-double-multi-line) | `nb-double-multi-line(n)` | ✓ P | `Scalar.doubleQuotedScalar` (multi-line path) |
| [115](https://yaml.org/spec/1.2.2/#rule-c-quoted-quote) | `c-quoted-quote` | ✓ P | `Scalar.singleQuotedScalar.collectChars` (`''` → `'`) |
| [116](https://yaml.org/spec/1.2.2/#rule-nb-single-char) | `nb-single-char` | ✓ P | `Scalar.singleQuotedScalar.collectChars` |
| [117](https://yaml.org/spec/1.2.2/#rule-ns-single-char) | `ns-single-char` | ✓ P | `Scalar.singleQuotedScalar.collectChars` |
| [118](https://yaml.org/spec/1.2.2/#rule-c-single-quoted) | `c-single-quoted(n,c)` | ✓ GP | `Grammar.ValidSingleQuoted`, `Scalar.singleQuotedScalar` |
| [119](https://yaml.org/spec/1.2.2/#rule-nb-single-text) | `nb-single-text(n,c)` | ✓ P | `Scalar.singleQuotedScalar.collectChars` |
| [120](https://yaml.org/spec/1.2.2/#rule-nb-single-one-line) | `nb-single-one-line` | ✓ P | `Scalar.singleQuotedScalar.collectChars` (single-line path) |
| [121](https://yaml.org/spec/1.2.2/#rule-s-single-next-line) | `s-single-next-line(n)` | ✓ P | `Scalar.foldQuotedNewlines` |
| [122](https://yaml.org/spec/1.2.2/#rule-nb-single-multi-line) | `nb-single-multi-line(n)` | ✓ P | `Scalar.singleQuotedScalar` (multi-line path) |
| [123](https://yaml.org/spec/1.2.2/#rule-ns-plain-first) | `ns-plain-first(c)` | ✓ GPS | `Grammar.canStartPlainScalar`, `Scanner.canStartPlainScalar`, `Combinators.canStartPlainScalar` |
| [124](https://yaml.org/spec/1.2.2/#rule-ns-plain-safe) | `ns-plain-safe(c)` | ✓ P | `Scalar.isPlainSafe` |
| [125](https://yaml.org/spec/1.2.2/#rule-ns-plain-safe-out) | `ns-plain-safe-out` | ✓ P | `Scalar.isPlainSafe` (inFlow=false) |
| [126](https://yaml.org/spec/1.2.2/#rule-ns-plain-safe-in) | `ns-plain-safe-in` | ✓ P | `Scalar.isPlainSafe` (inFlow=true) |
| [127](https://yaml.org/spec/1.2.2/#rule-ns-plain-char) | `ns-plain-char(c)` | ✓ P | `Scalar.plainScalarContent.collectPlain` |
| [128](https://yaml.org/spec/1.2.2/#rule-ns-plain) | `ns-plain(n,c)` | ✓ GP | `Grammar.ValidPlainScalarBlock/Flow`, `Scalar.plainScalarContent` |
| [129](https://yaml.org/spec/1.2.2/#rule-nb-ns-plain-in-line) | `nb-ns-plain-in-line(c)` | ✓ P | `Scalar.plainScalarContent.collectPlain` |
| [130](https://yaml.org/spec/1.2.2/#rule-ns-plain-one-line) | `ns-plain-one-line(c)` | ✓ P | `Scalar.plainScalarSingleLine` |
| [131](https://yaml.org/spec/1.2.2/#rule-s-ns-plain-next-line) | `s-ns-plain-next-line(n,c)` | ✓ P | `Scalar.plainScalarContent.collectLines/collectFlowLines` |
| [132](https://yaml.org/spec/1.2.2/#rule-ns-plain-multi-line) | `ns-plain-multi-line(n,c)` | ✓ P | `Scalar.plainScalarContent` (multi-line path) |
| [133](https://yaml.org/spec/1.2.2/#rule-in-flow) | `in-flow(c)` | ✓ P | Flow context parameter `inFlow : Bool` throughout |
| [134](https://yaml.org/spec/1.2.2/#rule-c-flow-sequence) | `c-flow-sequence(n,c)` | ✓ GP | `Grammar.ValidNode.flowSeq`, `Flow.flowSequenceImpl` |
| [135](https://yaml.org/spec/1.2.2/#rule-ns-s-flow-seq-entries) | `ns-s-flow-seq-entries(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` |
| [136](https://yaml.org/spec/1.2.2/#rule-ns-flow-seq-entry) | `ns-flow-seq-entry(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` (per-item logic) |
| [137](https://yaml.org/spec/1.2.2/#rule-c-flow-mapping) | `c-flow-mapping(n,c)` | ✓ GP | `Grammar.ValidNode.flowMap`, `Flow.flowMappingImpl` |
| [138](https://yaml.org/spec/1.2.2/#rule-ns-s-flow-map-entries) | `ns-s-flow-map-entries(n,c)` | ✓ P | `Flow.flowMappingEntriesImpl` |
| [139](https://yaml.org/spec/1.2.2/#rule-ns-flow-map-entry) | `ns-flow-map-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` |
| [140](https://yaml.org/spec/1.2.2/#rule-ns-flow-map-explicit-entry) | `ns-flow-map-explicit-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (`?` branch) |
| [141](https://yaml.org/spec/1.2.2/#rule-ns-flow-map-implicit-entry) | `ns-flow-map-implicit-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (implicit key branch) |
| [142](https://yaml.org/spec/1.2.2/#rule-ns-flow-map-yaml-key-entry) | `ns-flow-map-yaml-key-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` |
| [143](https://yaml.org/spec/1.2.2/#rule-c-ns-flow-map-separate-value) | `c-ns-flow-map-separate-value(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (`:` parsing) |
| [144](https://yaml.org/spec/1.2.2/#rule-c-ns-flow-map-json-key-entry) | `c-ns-flow-map-json-key-entry(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (JSON-like key handling) |
| [145](https://yaml.org/spec/1.2.2/#rule-c-ns-flow-map-adjacent-value) | `c-ns-flow-map-adjacent-value(n,c)` | ✓ P | `Flow.flowMappingEntryImpl` (adjacent `:` after JSON key) |
| [146](https://yaml.org/spec/1.2.2/#rule-ns-flow-pair) | `ns-flow-pair(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` (implicit single-pair mapping) |
| [147](https://yaml.org/spec/1.2.2/#rule-ns-flow-pair-entry) | `ns-flow-pair-entry(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` |
| [148](https://yaml.org/spec/1.2.2/#rule-ns-flow-pair-yaml-key-entry) | `ns-flow-pair-yaml-key-entry(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` (YAML key in pair) |
| [149](https://yaml.org/spec/1.2.2/#rule-c-ns-flow-pair-json-key-entry) | `c-ns-flow-pair-json-key-entry(n,c)` | ✓ P | `Flow.flowSequenceItemsImpl` (JSON key in pair) |
| [150](https://yaml.org/spec/1.2.2/#rule-ns-s-implicit-yaml-key) | `ns-s-implicit-yaml-key(c)` | ✓ P | Block/Flow implicit key detection |
| [151](https://yaml.org/spec/1.2.2/#rule-c-s-implicit-json-key) | `c-s-implicit-json-key(c)` | ✓ P | Block/Flow JSON-like key detection |
| [152](https://yaml.org/spec/1.2.2/#rule-c-flow-json-node) | `c-flow-json-node(n,c)` | ✓ P | `isJsonNodeToken` (JSON content detection for adjacent value) |
| [153](https://yaml.org/spec/1.2.2/#rule-ns-flow-yaml-node) | `ns-flow-yaml-node(n,c)` | ✓ P | `Flow.flowValueImpl` |
| [154](https://yaml.org/spec/1.2.2/#rule-c-flow-json-content) | `c-flow-json-content(n,c)` | ✓ P | `Flow.flowValueImpl` (collection dispatch) |
| [155](https://yaml.org/spec/1.2.2/#rule-ns-flow-content) | `ns-flow-content(n,c)` | ✓ P | `Flow.flowValueImpl` |
| [156](https://yaml.org/spec/1.2.2/#rule-ns-flow-yaml-content) | `ns-flow-yaml-content(n,c)` | ✓ P | `Flow.flowScalar` |
| [157](https://yaml.org/spec/1.2.2/#rule-ns-flow-node) | `ns-flow-node(n,c)` | ✓ P | `Flow.flowValueImpl` |

## Chapter 8: Block Style Productions

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [158](https://yaml.org/spec/1.2.2/#rule-c-b-block-header) | `c-b-block-header(m,t)` | ✓ GP | `Grammar.isBlockScalarHeaderChar`, `Scalar.blockScalarHeader` |
| [159](https://yaml.org/spec/1.2.2/#rule-c-indentation-indicator) | `c-indentation-indicator(m)` | ✓ GP | `Grammar.isBlockScalarHeaderChar` (digit `1`–`9`), `Scalar.blockScalarHeader` |
| [160](https://yaml.org/spec/1.2.2/#rule-c-chomping-indicator) | `c-chomping-indicator(t)` | ✓ GP | `Grammar.ChompStyle`, `Scalar.blockScalarHeader` |
| [161](https://yaml.org/spec/1.2.2/#rule-b-chomped-last) | `b-chomped-last(t)` | ✓ P | `Scalar.applyChomp` |
| [162](https://yaml.org/spec/1.2.2/#rule-l-chomped-empty) | `l-chomped-empty(n,t)` | ✓ P | `Scalar.applyChomp` |
| [163](https://yaml.org/spec/1.2.2/#rule-l-strip-empty) | `l-strip-empty(n)` | ✓ P | `Scalar.applyChomp` (strip branch) |
| [164](https://yaml.org/spec/1.2.2/#rule-l-keep-empty) | `l-keep-empty(n)` | ✓ P | `Scalar.applyChomp` (keep branch) |
| [165](https://yaml.org/spec/1.2.2/#rule-l-trail-comments) | `l-trail-comments(n)` | ✓ P | `Scalar.blockScalarHeader` (trailing comment) |
| [166](https://yaml.org/spec/1.2.2/#rule-l-literal-content) | `l-literal-content(n,t)` | ✓ P | `Scalar.blockScalarContent` + `Scalar.processLiteral` |
| [167](https://yaml.org/spec/1.2.2/#rule-l-nb-literal-text) | `l-nb-literal-text(n)` | ✓ P | `Scalar.blockScalarContent.blockScalarLine` |
| [168](https://yaml.org/spec/1.2.2/#rule-b-nb-literal-next) | `b-nb-literal-next(n)` | ✓ P | `Scalar.blockScalarContent.collectLines` |
| [169](https://yaml.org/spec/1.2.2/#rule-l-literal-content) | `l-literal-content(n,t)` | ✓ P | `Scalar.blockScalarContent` |
| [170](https://yaml.org/spec/1.2.2/#rule-c-l+literal) | `c-l+literal(n)` | ✓ GP | `Grammar.ValidLiteralScalar`, `Scalar.blockScalar` (literal path) |
| [171](https://yaml.org/spec/1.2.2/#rule-s-nb-folded-text) | `s-nb-folded-text(n)` | ✓ P | `Scalar.blockScalarContent.blockScalarLine` (folded) |
| [172](https://yaml.org/spec/1.2.2/#rule-b-l-spaced) | `b-l-spaced(n)` | ✓ P | `Scalar.processFolded` (more-indented handling) |
| [173](https://yaml.org/spec/1.2.2/#rule-s-b-folded) | `s-b-folded(n,c)` | ✓ P | `Scalar.processFolded` |
| [174](https://yaml.org/spec/1.2.2/#rule-l-folded-content) | `l-folded-content(n,t)` | ✓ P | `Scalar.blockScalarContent` + `Scalar.processFolded` |
| [175](https://yaml.org/spec/1.2.2/#rule-c-l+folded) | `c-l+folded(n)` | ✓ GP | `Grammar.ValidFoldedScalar`, `Scalar.blockScalar` (folded path) |
| [176](https://yaml.org/spec/1.2.2/#rule-s-l+block-in-block) | `s-l+block-in-block(n,c)` | ✓ P | `Block.blockValueImpl` |
| [177](https://yaml.org/spec/1.2.2/#rule-s-l+block-scalar) | `s-l+block-scalar(n,c)` | ✓ P | `Scalar.blockScalar` |
| [178](https://yaml.org/spec/1.2.2/#rule-s-l+block-collection) | `s-l+block-collection(n,c)` | ✓ P | `Block.blockValueImpl` (collection dispatch) |
| [179](https://yaml.org/spec/1.2.2/#rule-seq-spaces) | `seq-spaces(n,c)` | ✓ P | `Block.blockValueImpl` (effectiveMinIndent) |
| [180](https://yaml.org/spec/1.2.2/#rule-l+block-sequence) | `l+block-sequence(n)` | ✓ GP | `Grammar.ValidNode.blockSeq`, `Block.blockSequenceImpl` |
| [181](https://yaml.org/spec/1.2.2/#rule-c-l-block-seq-entry) | `c-l-block-seq-entry(n)` | ✓ P | `Block.blockSequenceItemsImpl` |
| [182](https://yaml.org/spec/1.2.2/#rule-s-l+block-indented) | `s-l+block-indented(n,c)` | ✓ P | `Block.blockValueImpl`/`blockValueSameLineImpl` |
| [183](https://yaml.org/spec/1.2.2/#rule-ns-l-compact-sequence) | `ns-l-compact-sequence(n)` | ✓ P | `Block.blockSequenceImpl` (compact notation) |
| [184](https://yaml.org/spec/1.2.2/#rule-l+block-mapping) | `l+block-mapping(n)` | ✓ GP | `Grammar.ValidNode.blockMap`, `Block.blockMappingImpl` |
| [185](https://yaml.org/spec/1.2.2/#rule-ns-l-block-map-entry) | `ns-l-block-map-entry(n)` | ✓ P | `Block.blockMappingEntryImpl` |
| [186](https://yaml.org/spec/1.2.2/#rule-c-l-block-map-explicit-key) | `c-l-block-map-explicit-key(n)` | ✓ P | `Block.blockMappingEntryImpl` (`?` branch) |
| [187](https://yaml.org/spec/1.2.2/#rule-l-block-map-explicit-value) | `l-block-map-explicit-value(n)` | ✓ P | `Block.blockMappingEntryImpl` (`:` after explicit key) |
| [188](https://yaml.org/spec/1.2.2/#rule-ns-l-block-map-implicit-entry) | `ns-l-block-map-implicit-entry(n)` | ✓ P | `Block.blockMappingEntryImpl` (simple key branch) |
| [189](https://yaml.org/spec/1.2.2/#rule-ns-s-block-map-implicit-key) | `ns-s-block-map-implicit-key` | ✓ P | `Block.blockMappingKeyImpl` |
| [190](https://yaml.org/spec/1.2.2/#rule-c-l-block-map-implicit-value) | `c-l-block-map-implicit-value(n)` | ✓ P | `Block.blockMappingEntryImpl` (`:` after simple key) |
| [191](https://yaml.org/spec/1.2.2/#rule-ns-l-compact-mapping) | `ns-l-compact-mapping(n)` | ✓ P | `Block.blockMappingImpl` (compact notation) |
| [192](https://yaml.org/spec/1.2.2/#rule-s-l+block-node) | `s-l+block-node(n,c)` | ✓ P | `Block.blockValueImpl` |
| [193](https://yaml.org/spec/1.2.2/#rule-s-l+flow-in-block) | `s-l+flow-in-block(n)` | ✓ P | `Block.dispatchByCharImpl` (flow collection dispatch) |
| [194](https://yaml.org/spec/1.2.2/#rule-s-l+block-in-block) | `s-l+block-in-block(n,c)` | ✓ P | `Block.blockValueImpl` |
| [195](https://yaml.org/spec/1.2.2/#rule-s-l+block-scalar) | `s-l+block-scalar(n,c)` | ✓ P | `Block.dispatchByCharImpl` (`\|`/`>` branches) |

## Chapter 9: Document Stream Productions

| # | Production | Status | Lean Definition(s) |
|---|-----------|--------|-------------------|
| [196](https://yaml.org/spec/1.2.2/#rule-l-document-prefix) | `l-document-prefix` | ✓ P | `Document.document` (BOM + directives) |
| [197](https://yaml.org/spec/1.2.2/#rule-c-directives-end) | `c-directives-end` | ✓ P | `Document.documentStartMarker` (`---`) |
| [198](https://yaml.org/spec/1.2.2/#rule-c-document-end) | `c-document-end` | ✓ P | `Document.documentEndMarker` (`...`) |
| [199](https://yaml.org/spec/1.2.2/#rule-l-document-suffix) | `l-document-suffix` | ✓ P | `Document.documentEndMarker` + trailing |
| [200](https://yaml.org/spec/1.2.2/#rule-c-forbidden) | `c-forbidden` | ✓ GP | `Grammar.isCForbiddenPrefix`, `Scalar.foldQuotedNewlines` |
| [201](https://yaml.org/spec/1.2.2/#rule-l-bare-document) | `l-bare-document` | ✓ P | `Document.document` (bare document path) |
| [202](https://yaml.org/spec/1.2.2/#rule-l-explicit-document) | `l-explicit-document` | ✓ P | `Document.document` (explicit document path) |
| [203](https://yaml.org/spec/1.2.2/#rule-l-directive-document) | `l-directive-document` | ✓ P | `Document.document` (directive + explicit) |
| [204](https://yaml.org/spec/1.2.2/#rule-l-any-document) | `l-any-document` | ✓ P | `Document.document` |
| [205](https://yaml.org/spec/1.2.2/#rule-l-yaml-stream) | `l-yaml-stream` | ✓ GP | `Grammar.ValidStream`, `Document.yamlStream` |

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

---

## Token–Grammar Layer Analysis (2026-02-26)

### Motivation

The YAML 1.2.2 specification defines all 205 productions as character-level
rules in a single PEG-like grammar. Unlike most programming language
specifications, there is **no explicit distinction between lexical
(tokenization) and syntactic (grammar) layers**. Every production — from
single-character classifications to full document streams — operates on raw
characters.

This design choice in the specification has a direct consequence for parser
implementations: **the parser must do character-level lookahead at grammar
decision points where a tokenizer would have already resolved the ambiguity.**

**Concrete example — the `detectMappingKeyImpl` false positive:**

Our parser's `detectMappingKeyImpl` (Block.lean line 1040) scans forward
through raw characters looking for `: ` (mapping value indicator) to determine
whether the current position starts a block mapping. This produces false
positives when `: ` appears inside a scalar value:

```yaml
# Parser incorrectly rejects this valid YAML:
b: x: y
# Error: "block mapping cannot start on the same line as a mapping value"
```

The scanner sees `b`, `: `, `x`, `: `, `y` as a flat character stream and
finds two `: ` occurrences. It cannot distinguish the first `: ` (which is a
mapping value indicator **token**) from the second `: ` (which is literal
content inside a plain scalar **token**).

With an explicit tokenization step, the tokenizer would produce:
```
KEY("b") VALUE SCALAR("x: y")
```
and the grammar rule would never see the `: ` inside the scalar.

This is not a YAML-specific problem — it's the classical motivation for
separating tokenization from parsing in compiler architecture. The YAML
specification's conflation of these layers makes every YAML parser
implementation prone to exactly this class of bugs.

> **Upstream observation.** The YAML 1.2.2 specification would benefit from
> explicitly differentiating token-level productions from grammar-level
> productions. The libyaml reference implementation already makes this
> distinction internally via its scanner/parser split. Formalizing it in
> the specification would help all implementations.

### Classification Criteria

We classify each YAML 1.2.2 production into one of three layers:

| Layer | Abbrev | Description |
|-------|--------|-------------|
| **Character class** | **C** | Defines a set of characters. Not a production in the traditional sense — a predicate on individual characters. Used by lexical productions. |
| **Lexical** | **L** | Defines how characters form **tokens**. Operates on the character stream, produces tokens. Includes indicator recognition, scalar content collection, escape resolution, whitespace/indentation handling, comment scanning, and directive parsing. |
| **Syntactic** | **S** | Defines how tokens form **valid YAML structures**. Operates on tokens (or would, with an explicit tokenizer), produces AST nodes. Includes collection nesting, node properties, document structure. |

**Context sensitivity.** YAML's lexer is inherently context-sensitive:
indentation level, flow/block context, and scalar style all affect
tokenization. This is why most YAML implementations (including ours) don't
have a clean lexer/parser split. The classification below describes the
*logical* layer each production belongs to, not necessarily the implementation
architecture.

### Chapter 5: Character Productions — Layer Classification

| # | Production | Layer | Rationale |
|---|-----------|-------|-----------|
| [1] | `c-printable` | C | Character set definition |
| [2] | `nb-json` | C | Character set definition |
| [3] | `c-byte-order-mark` | L | Produces BOM token |
| [4]–[6] | `c-sequence-entry`, `c-mapping-key`, `c-mapping-value` | L | Block indicator tokens (`-`, `?`, `:`) |
| [7] | `c-collect-entry` | L | Flow entry token (`,`) |
| [8]–[11] | `c-sequence-start/end`, `c-mapping-start/end` | L | Flow delimiter tokens (`[`, `]`, `{`, `}`) |
| [12] | `c-comment` | L | Comment introducer (`#`) |
| [13]–[15] | `c-anchor`, `c-alias`, `c-tag` | L | Node property token introducers (`&`, `*`, `!`) |
| [16]–[17] | `c-literal`, `c-folded` | L | Block scalar indicator tokens (`\|`, `>`) |
| [18]–[19] | `c-single-quote`, `c-double-quote` | L | Quoted scalar delimiters (`'`, `"`) |
| [20] | `c-directive` | L | Directive introducer (`%`) |
| [21] | `c-reserved` | L | Reserved indicators (`@`, `` ` ``) |
| [22]–[23] | `c-indicator`, `c-flow-indicator` | C | Character set definitions |
| [24]–[27] | `b-line-feed` through `nb-char` | C | Character set definitions |
| [28]–[30] | `b-break`, `b-as-line-feed`, `b-non-content` | L | Line break handling (within/between tokens) |
| [31]–[34] | `s-space` through `ns-char` | C | Character set definitions |
| [35]–[40] | `ns-dec-digit` through `ns-tag-char` | C | Character set definitions |
| [41] | `c-escape` | L | Escape introducer (`\`) — sub-token |
| [42]–[60] | `ns-esc-null` through `ns-esc-32-bit` | L | Individual escape sequences — sub-token rules within double-quoted scalar token |
| [61] | `c-ns-esc-char` | L | Escape sequence dispatch — sub-token |

**Summary:** 18 character classes (C), 43 lexical (L), 0 syntactic (S).

### Chapter 6: Basic Structures — Layer Classification

| # | Production | Layer | Rationale |
|---|-----------|-------|-----------|
| [63]–[65] | `s-indent(n)`, `s-indent(<n)`, `s-indent(≤n)` | L | Indentation consumption — generates virtual BLOCK-START/BLOCK-END tokens |
| [66]–[68] | `s-separate-in-line`, `s-line-prefix`, `l-empty` | L | Whitespace handling within/between tokens |
| [69]–[72] | `b-l-trimmed` through `s-flow-folded` | L | Line folding — sub-token processing within scalar content |
| [73] | `s-flow-line-prefix(n)` | L | Flow-context whitespace |
| [74]–[79] | `l-comment` through `s-l-comments` | L | Comment tokens |
| [80]–[81] | `s-separate`, `s-separate-lines` | L | Inter-token separation |
| [82]–[86] | `l-directive` through `ns-tag-directive` | L | Directive tokens (VERSION-DIRECTIVE, TAG-DIRECTIVE) |
| [87]–[93] | `c-tag-handle` through `ns-global-tag-prefix` | L | Sub-token rules within directive and tag tokens |
| [94] | `c-ns-properties(n,c)` | **S** | **Composes** TAG + ANCHOR tokens (either order). This is the first syntactic production. |
| [95]–[98] | `c-ns-tag-property` through `c-non-specific-tag` | L | Tag token formation |
| [99]–[102] | `c-ns-anchor-property` through `ns-anchor-char` | L | Anchor/alias token formation |

**Summary:** 0 character classes, 39 lexical (L), 1 syntactic (S).

### Chapter 7: Flow Style Productions — Layer Classification

| # | Production | Layer | Rationale |
|---|-----------|-------|-----------|
| [103] | `c-ns-alias-node` | **S** | Alias node — composes ALIAS token into AST node |
| [104]–[105] | `e-scalar`, `e-node` | **S** | Empty/implicit nodes in AST |
| [106] | `ns-double-char` | L | Character within double-quoted content — sub-token |
| [107] | `c-double-quoted(n,c)` | L | Complete double-quoted SCALAR token (open-quote + content + close-quote) |
| [108]–[114] | `nb-double-text` through `nb-double-multi-line` | L | Sub-token rules within double-quoted scalar |
| [115]–[117] | `c-quoted-quote` through `ns-single-char` | L | Sub-token rules within single-quoted scalar |
| [118] | `c-single-quoted(n,c)` | L | Complete single-quoted SCALAR token |
| [119]–[122] | `nb-single-text` through `nb-single-multi-line` | L | Sub-token rules within single-quoted scalar |
| [123] | `ns-plain-first(c)` | L | Plain scalar start detection |
| [124]–[127] | `ns-plain-safe` through `ns-plain-char` | L | Plain scalar character rules |
| [128] | `ns-plain(n,c)` | L | Complete plain SCALAR token |
| [129]–[132] | `nb-ns-plain-in-line` through `ns-plain-multi-line` | L | Sub-token rules within plain scalar |
| [133] | `in-flow(c)` | **S** | Context parameter — syntactic dispatch |
| [134] | `c-flow-sequence(n,c)` | **S** | Flow sequence structure: FLOW-SEQ-START + entries + FLOW-SEQ-END |
| [135]–[136] | `ns-s-flow-seq-entries`, `ns-flow-seq-entry` | **S** | Sequence entry composition |
| [137] | `c-flow-mapping(n,c)` | **S** | Flow mapping structure: FLOW-MAP-START + entries + FLOW-MAP-END |
| [138]–[145] | `ns-s-flow-map-entries` through `c-ns-flow-map-adjacent-value` | **S** | Mapping entry composition, key-value pairing |
| [146]–[151] | `ns-flow-pair` through `c-s-implicit-json-key` | **S** | Implicit key detection, single-pair entries |
| [152]–[157] | `c-flow-json-node` through `ns-flow-node` | **S** | Flow node composition (properties + content) |

**Summary:** 0 character classes, 27 lexical (L), 28 syntactic (S).

### Chapter 8: Block Style Productions — Layer Classification

| # | Production | Layer | Rationale |
|---|-----------|-------|-----------|
| [158]–[160] | `c-b-block-header`, `c-indentation-indicator`, `c-chomping-indicator` | L | Block scalar header token components |
| [161]–[165] | `b-chomped-last` through `l-trail-comments` | L | Block scalar content processing (chomp, trailing) |
| [166]–[169] | `l-literal-content` through `l-literal-content` | L | Literal block scalar content — SCALAR token |
| [170] | `c-l+literal(n)` | L | Complete literal SCALAR token (`\|` + header + content) |
| [171]–[174] | `s-nb-folded-text` through `l-folded-content` | L | Folded block scalar content — SCALAR token |
| [175] | `c-l+folded(n)` | L | Complete folded SCALAR token (`>` + header + content) |
| [176]–[179] | `s-l+block-in-block` through `seq-spaces` | **S** | Block node dispatch and context handling |
| [180] | `l+block-sequence(n)` | **S** | Block sequence structure (indentation-delimited) |
| [181]–[183] | `c-l-block-seq-entry` through `ns-l-compact-sequence` | **S** | Sequence entry and compact notation |
| [184] | `l+block-mapping(n)` | **S** | Block mapping structure (indentation-delimited) |
| [185]–[191] | `ns-l-block-map-entry` through `ns-l-compact-mapping` | **S** | Mapping entries, explicit/implicit keys, compact notation |
| [192]–[195] | `s-l+block-node` through `s-l+block-scalar` | **S** | Block node composition, flow-in-block |

**Summary:** 0 character classes, 18 lexical (L), 20 syntactic (S).

### Chapter 9: Document Stream Productions — Layer Classification

| # | Production | Layer | Rationale |
|---|-----------|-------|-----------|
| [196] | `l-document-prefix` | L | Document prefix handling (BOM + comments) |
| [197] | `c-directives-end` | L | DOCUMENT-START token (`---`) |
| [198] | `c-document-end` | L | DOCUMENT-END token (`...`) |
| [199] | `l-document-suffix` | L | Document suffix (DOCUMENT-END + trailing) |
| [200] | `c-forbidden` | L | Lexical constraint: `---`/`...` at column 0 terminates scalars |
| [201]–[204] | `l-bare-document` through `l-any-document` | **S** | Document structure composition |
| [205] | `l-yaml-stream` | **S** | Top-level stream: sequence of documents |

**Summary:** 0 character classes, 5 lexical (L), 5 syntactic (S).

### Aggregate Layer Distribution

| Layer | Ch.5 | Ch.6 | Ch.7 | Ch.8 | Ch.9 | **Total** | **%** |
|-------|------|------|------|------|------|-----------|-------|
| **C** Character class | 18 | 0 | 0 | 0 | 0 | **18** | 8.8% |
| **L** Lexical/Token | 43 | 39 | 27 | 18 | 5 | **132** | 64.4% |
| **S** Syntactic/Grammar | 0 | 1 | 28 | 20 | 5 | **54** | 26.3% |
| **Total** | 61 | 40 | 55 | 38 | 10 | **205** | |

**Key observation:** Nearly two-thirds (64.4%) of YAML 1.2.2 productions are
lexical — they define how characters form tokens. Only about a quarter (26.3%)
are syntactic. The spec presents all 205 as a single flat grammar, but the
natural layering is overwhelmingly lexical.

### Proposed YAML Token Types

Based on the layer analysis, the following token types cover all lexical
productions. This follows the libyaml scanner model (`yaml_token_type_e`)
which already makes this distinction internally.

```lean
/-- YAML 1.2.2 Token types.
    Based on the layer analysis of all 205 spec productions.
    Follows the libyaml scanner model (yaml_token_type_e).

    Productions [1]–[40] (character classes) are predicates on Char,
    not tokens. Productions [41]–[200] (lexical) produce these tokens.
    Productions [94], [103]–[105], [133]–[157], [176]–[195], [201]–[205]
    (syntactic) compose tokens into the AST. -/
inductive YamlToken where
  -- Stream boundary markers (implicit — no character representation)
  | streamStart                          -- beginning of input
  | streamEnd                            -- end of input

  -- Directive tokens (§6.8, productions [82]–[93])
  | versionDirective (major minor : Nat) -- %YAML 1.2
  | tagDirective (handle prefix : String) -- %TAG !handle! prefix

  -- Document markers (§9.1.2, productions [197]–[198])
  | documentStart                        -- ---
  | documentEnd                          -- ...

  -- Block structure tokens (implicit — generated by indentation changes)
  -- These have NO character representation in the input.  The scanner
  -- generates them by tracking an indentation stack, analogous to
  -- Python's INDENT/DEDENT tokens.
  | blockSequenceStart                   -- indentation increase before `-`
  | blockMappingStart                    -- indentation increase before key
  | blockEnd                             -- indentation decrease

  -- Block indicator tokens (§5.3, productions [4]–[6])
  | blockEntry                           -- `-` + whitespace/break
  | key                                  -- `?` + whitespace/break
  | value                                -- `:` + whitespace/break

  -- Flow indicator tokens (§5.3, productions [7]–[11])
  | flowSequenceStart                    -- [
  | flowSequenceEnd                      -- ]
  | flowMappingStart                     -- {
  | flowMappingEnd                       -- }
  | flowEntry                            -- ,

  -- Node property tokens (§6.9, productions [95]–[102])
  | anchor (name : String)               -- &name
  | alias (name : String)                -- *name
  | tag (handle suffix : String)         -- !tag, !!type, !<uri>

  -- Scalar tokens (§7.3, §8.1, productions [107]–[175])
  -- Content is fully resolved: escapes expanded, lines folded, chomp applied.
  | scalar (value : String) (style : ScalarStyle)

  -- Whitespace tokens (when preserved)
  | comment (text : String)              -- # text (§6.6, productions [74]–[79])

/-- Scalar presentation style, carried with SCALAR tokens. -/
inductive ScalarStyle where
  | plain | singleQuoted | doubleQuoted | literal | folded
```

**Virtual tokens.** Three token types — `blockSequenceStart`,
`blockMappingStart`, and `blockEnd` — have no character representation in the
input. They are generated by the scanner based on indentation changes,
analogous to Python's `INDENT`/`DEDENT` tokens. This is the primary source of
YAML's lexer complexity: the scanner must maintain an indentation stack to
generate these tokens correctly.

**Scalar resolution.** The SCALAR token carries fully-resolved content:
escape sequences expanded, line folding applied, chomp style applied. This
means all of productions [41]–[61] (escapes), [69]–[72] (folding),
[106]–[132] (scalar content rules), and [158]–[175] (block scalar processing)
are internal to the scanner's scalar tokenization logic.

### Architectural Implications for Our Parser

#### Current architecture (single-pass, character-level)

```
Character Stream ──→ [ Combined Parser ] ──→ YamlValue AST
                     (Block.lean, Flow.lean, Scalar.lean, Document.lean)
```

All 205 productions are implemented as interleaved character-level parsers.
Grammar-level decisions (e.g., "is this a mapping value indicator?") require
character-level lookahead (`detectMappingKeyImpl`) that scans through content
that should have already been tokenized.

#### Proposed architecture (two-pass, token-level)

```
Character Stream ──→ [ Scanner/Tokenizer ] ──→ Token Stream ──→ [ Grammar Parser ] ──→ YamlValue AST
                     (132 lexical productions)                   (54 syntactic productions)
```

**Scanner responsibilities (L layer):**
- Character classification (18 C-layer predicates)
- Indicator recognition ([4]–[21])
- Scalar content collection and resolution ([107]–[175])
- Escape sequence processing ([41]–[61])
- Line folding ([69]–[72])
- Comment scanning ([74]–[79])
- Directive parsing ([82]–[93])
- Indentation tracking → virtual BLOCK-START/BLOCK-END generation
- Implicit key detection (currently `detectMappingKeyImpl`)
- `c-forbidden` detection ([200]) — terminates scalars at `---`/`...`

**Grammar parser responsibilities (S layer):**
- Flow collection nesting ([134]–[157])
- Block collection nesting ([176]–[195])
- Node property attachment ([94])
- Document structure ([201]–[205])
- Empty node insertion ([104]–[105])

#### Why this fixes the `detectMappingKeyImpl` problem

With a tokenizer, the input `b: x: y` would be scanned as:

```
BLOCK-MAPPING-START  KEY  SCALAR("b")  VALUE  SCALAR("x: y")  BLOCK-END
```

The scanner recognizes that `b` is followed by `: ` (mapping value indicator),
so `b` becomes a SCALAR token and `: ` becomes a VALUE token. The remaining
`x: y` is then collected as a plain scalar — the `: ` inside it is **not** at
the top level, so it's literal content, not a value indicator.

The grammar parser never sees raw `: ` characters — it sees VALUE tokens.
There is no ambiguity to resolve at the grammar level.

#### YAML's context-sensitive scanning

Unlike most languages, YAML's scanner is context-sensitive. The same character
sequence may tokenize differently depending on:

1. **Indentation level** — determines block structure boundaries
2. **Flow/block context** — plain scalars terminate at `,`, `]`, `}` in flow
3. **Scalar style** — inside `"..."`, `: ` is literal content
4. **Key position** — implicit keys have a 1024-character limit (§7.4)

This means the scanner cannot be a simple regex-based lexer. It must maintain
state (indentation stack, flow level, key position). libyaml's scanner
(`scanner.c`, ~2800 lines) is roughly 3× the size of its parser (`parser.c`,
~900 lines), reflecting the complexity distribution.

#### Impact on verification proofs

Introducing an explicit tokenization layer would affect the proof architecture:

| Proof area | Current state | Impact |
|------------|--------------|--------|
| **Character classification** (`CharClass.lean`) | 8 theorems on char predicates | **Unchanged** — C-layer predicates are independent |
| **Escape resolution** (`EscapeResolution.lean`) | 16 + 9 + 7 theorems | **Moves to scanner proofs** — escape resolution becomes a scanner property |
| **Block scalar contracts** (`BlockScalarContracts.lean`) | 14 + 10 + 2 theorems | **Moves to scanner proofs** — block scalar processing is entirely lexical |
| **Fold newlines** (`FoldNewlines.lean`) | 10 + 8 + 16 theorems | **Moves to scanner proofs** — fold processing is sub-token |
| **Round-trip** (`RoundTrip.lean`) | 58 theorems + 63 guards | **Restructured** — emit/parse correspondence becomes emit/scan + scan/parse |
| **Per-parser specs** (`PerParserSpecs.lean`) | 46 theorems | **Split** — scalar specs move to scanner, collection specs stay in parser |
| **Fuel sufficiency** (`FuelSufficiency.lean`) | 35 theorems | **Split** — scanner and parser each need independent fuel/termination proofs |
| **Completeness** (`Completeness.lean`, `Composition.lean`) | 21 + 21 theorems | **Restructured** — composition proofs bridge scanner↔parser via token stream |
| **Suite guards** (`SuiteGuards/*.lean`) | 351 guards | **Unchanged** — end-to-end; scanner+parser compose transparently |

**Estimated proof impact:** ~40% of existing proofs (escape, fold, block scalar,
scalar per-parser specs) move cleanly into the scanner proof layer with minimal
rewriting — they already reason about character-level operations. ~30% (round-trip,
composition, fuel) require restructuring into two-layer proofs. ~30% (char class,
document contracts, suite guards) are unaffected.

The net effect is **more proofs, but simpler proofs**: each layer's properties
are stated and proved independently, then composed. This mirrors the
compounding pattern observed in Phases 3–5 where layered specifications made
each subsequent proof phase easier.

---

## Boundary Test Coverage Gap Report (v0.2.13.5)

Cross-reference of indent-dependent productions against dedicated boundary tests.
See `Tests/ProductionCoverage.lean` for the compile-time analysis.

### Summary

| Metric | Count |
|--------|-------|
| Total indent-dependent productions | 44 |
| Key productions analyzed | 14 |
| Fully covered (under + over + tab) | 5 |
| Zero boundary tests | 5 |
| Missing under-indent tests | 5 |
| Missing over-indent tests | 8 |
| Missing tab-injection tests | 9 |

### Fully Covered Productions ✓

| # | Production | Under | Over | Tab | Test Source |
|---|-----------|-------|------|-----|-------------|
| [63] | `s-indent(n)` | ✓ | ✓ | ✓ | Adversarial §1-§2, Mutation indent±1 |
| [170] | `c-l+literal(n)` | ✓ | ✓ | ✓ | Adversarial §6, DumpRoundTrip |
| [175] | `c-l+folded(n)` | ✓ | ✓ | ✓ | Adversarial §6, DumpRoundTrip |
| [180] | `l+block-sequence(n)` | ✓ | ✓ | ✓ | Adversarial §3, Mutation, Property |
| [184] | `l+block-mapping(n)` | ✓ | ✓ | ✓ | Adversarial §4, ExplicitKey, Mutation |

### Partially Covered Productions

| # | Production | Under | Over | Tab | Coverage Notes |
|---|-----------|-------|------|-----|---------------|
| [71] | `b-l-folded(n,c)` | ✓ | — | — | Adversarial §6 folded under-indent only |
| [158] | `c-b-block-header(m,t)` | ✓ | — | — | yaml-test-suite `header` (23), Adversarial §6 |
| [187] | `l-block-map-explicit-value(n)` | ✓ | ✓ | — | Adversarial §7, ExplicitKeyTests §21 |
| [193] | `s-l+flow-in-block(n)` | ✓ | — | — | Adversarial §5, ExplicitKeyTests §23 |

### Zero Boundary Test Productions (gap targets)

| # | Production | Implicit Coverage |
|---|-----------|------------------|
| [67] | `s-line-prefix(n,c)` | Multi-line scalar continuation tests |
| [68] | `l-empty(n,c)` | yaml-test-suite literal/folded/whitespace (122) |
| [72] | `s-flow-folded(n)` | yaml-test-suite double (32), PropertyTests |
| [80] | `s-separate(n,c)` | Pervasive in all yaml-test-suite tests |
| [179] | `seq-spaces(n,c)` | Nested block sequence tests (implicit) |

### `@[yaml_spec]` Annotation Coverage

| File | Annotations | Layer |
|------|------------|-------|
| `Scanner.lean` | 46 | C + L layers |
| `CharPredicates.lean` | 7 | C layer |
| `Grammar.lean` | 9 | S layer (formal specs) |
| `TokenParser.lean` | 13 | S layer (parser functions) |
| **Total** | **75** | |
