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
| [21](https://yaml.org/spec/1.2.2/#rule-c-reserved) | `c-reserved` | ⊘ | `@`, `` ` `` — rejected by indicator check |
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
| [37](https://yaml.org/spec/1.2.2/#rule-ns-ascii-letter) | `ns-ascii-letter` | ⊘ | Not used directly |
| [38](https://yaml.org/spec/1.2.2/#rule-ns-word-char) | `ns-word-char` | ✓ P | `Combinators.isAnchorChar` (superset) |
| [39](https://yaml.org/spec/1.2.2/#rule-ns-uri-char) | `ns-uri-char` | ✓ P | `Tag.isTagChar` (subset) |
| [40](https://yaml.org/spec/1.2.2/#rule-ns-tag-char) | `ns-tag-char` | ✓ P | `Tag.isTagChar` |
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
| [75](https://yaml.org/spec/1.2.2/#rule-c-nb-comment-text) | `c-nb-comment-text` | ✓ P | `Combinators.comment` |
| [76](https://yaml.org/spec/1.2.2/#rule-b-comment) | `b-comment` | ✓ P | `Combinators.newline` (at end of comment) |
| [77](https://yaml.org/spec/1.2.2/#rule-s-b-comment) | `s-b-comment` | ✓ P | `Combinators.skipTrailing` |
| [78](https://yaml.org/spec/1.2.2/#rule-l-comment) | `l-comment` | ✓ P | `Combinators.skipBlankLines` (comment-only lines) |
| [79](https://yaml.org/spec/1.2.2/#rule-s-l-comments) | `s-l-comments` | ✓ P | `Combinators.skipTrailing` + `Combinators.skipBlankLines` |
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
| [123](https://yaml.org/spec/1.2.2/#rule-ns-plain-first) | `ns-plain-first(c)` | ✓ GP | `Grammar.canStartPlainScalar`, `Combinators.canStartPlainScalar` |
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
| [152](https://yaml.org/spec/1.2.2/#rule-c-flow-json-node) | `c-flow-json-node(n,c)` | ⊘ | Subsumed by `flowValueImpl` |
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
