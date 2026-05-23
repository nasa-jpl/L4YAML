import L4YAML.Parser.Composition
import L4YAML.Parser.IndexedComposition

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Indexed-vs-legacy parser parity guards (Phase 3 Step 6f.0)

Byte-equality checks between the legacy `TokenParser.parseYaml*`
functions and the indexed `TokenParser.Indexed.parseYaml*Ix`
twins introduced in Phase 3 Step 6f.1.

Each `#guard` exercises one parser path. Failing guards block the
Step 6f cutover: the indexed pipeline must agree with the legacy
pipeline byte-for-byte on every input these tests cover before
the cutover commit can flip the canonical symbols.

## Background

Step 6e wired `scanIx` directly into `parseStreamIx`, hypothesising
that the indexed parser's `validNextToken` predicate would absorb
the placeholder-skip step that legacy's `scanFiltered` performs.
That hypothesis was wrong (Reflection 97, retracted in Step 6f.0):
`validNextToken` *permits* `.placeholder` but does not *consume* it,
so the unfiltered stream caused `parseNodeContent` to fall through
its `_` arm and emit empty scalars for plain root content. The
investigation also surfaced two related state-management gaps in
the indexed scanner that this harness pins down:

- `scanFlowEntryIx` accidentally called `scanValuePrepareIx`,
  overwriting `.placeholder` slots with `.key` tokens at `,`
  boundaries in flow collections.
- `skipToContentS` failed to set `simpleKeyAllowed := true` and
  `needIndentCheck := true` on newline crossings, so multi-line
  block mappings and nested block sequences mis-scanned.

The harness covers the symptoms each fix addresses.
-/

namespace L4YAML.Parity.Indexed

open L4YAML
open L4YAML.TokenParser
open L4YAML.TokenParser.Indexed

/-- Single-document parity: legacy and indexed must agree on the
    composed `YamlValue` (or the same `ScanError`). -/
@[inline] def single (s : String) : Bool :=
  parseYamlSingle s == parseYamlSingleIx s

/-- Multi-document parity: legacy and indexed must agree on the
    `Array YamlDocument` (or the same `ScanError`). -/
@[inline] def docs (s : String) : Bool :=
  parseYaml s == parseYamlIx s

/-! ### Empty + primitives -/
#guard single ""
#guard single "abc"
#guard single "42"
#guard single "true"
#guard single "false"
#guard single "null"

/-! ### Quoted scalars -/
#guard single "\"abc\""
#guard single "'abc'"
#guard single "\"a b c\""
#guard single "'it''s'"

/-! ### Block sequences -/
#guard single "- a"
#guard single "- a\n- b\n"
#guard single "- 1\n- 2\n- 3"

/-! ### Block mappings -/
#guard single "a: b"
#guard single "a: 1\nb: 2"
#guard single "key:\n  nested: value"

/-! ### Flow collections -/
#guard single "[]"
#guard single "[1]"
#guard single "[1, 2]"
#guard single "[1, 2, 3]"
#guard single "{}"
#guard single "{a: 1}"
#guard single "{a: 1, b: 2}"
#guard single "[[1, 2], [3, 4]]"
#guard single "{a: [1, 2], b: {c: 3}}"

/-! ### Mixed nested -/
#guard single "- [1, 2]\n- [3, 4]\n"
#guard single "list:\n  - a\n  - b\n"

/-! ### Nested block sequences (regression for indent-unwind /
    `needIndentCheck` on newline crossing) -/
#guard single "-\n  - a\n  - b\n-\n  - c"

/-! ### Anchors and aliases -/
#guard single "&a 1\n"
#guard single "[&a 1, *a]"

/-! ### Tags -/
#guard single "!!str 42"

/-! ### Block scalars -/
#guard single "|\n  line1\n  line2\n"
#guard single ">\n  line1\n  line2\n"

/-! ### Comments + whitespace -/
#guard single "# leading\nabc"
#guard single "a: b  # trailing"
#guard single "   abc   "
#guard single "abc\n"

/-! ### Multi-document streams -/
#guard docs "1\n---\n2\n"
#guard docs "---\nfoo\n...\n---\nbar\n"
#guard docs "%YAML 1.2\n---\n42"

end L4YAML.Parity.Indexed
