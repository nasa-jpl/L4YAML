module

public import L4YAML.Parser.Composition

public meta import L4YAML.Parser.Composition
public import L4YAML.Parser.IndexedComposition

public meta import L4YAML.Parser.IndexedComposition
@[expose] public section Blanket

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

/-- Both pipelines succeeded with the same value, or both failed with the
    same error. Matched by hand rather than compared with `==` on the
    `Except`: `BEq YamlValue`, `BEq YamlDocument` and `BEq ScanError` all
    exist, but core provides no `BEq (Except ε α)`, and an orphan instance
    for it does not belong in a test file. -/
@[inline] def agree {α : Type} [BEq α] (a b : Except ScanError α) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error e₁, .error e₂ => e₁ == e₂
  | _, _ => false

/-- Single-document parity: legacy and indexed must agree on the
    composed `YamlValue` (or the same `ScanError`). -/
@[inline] def single (s : String) : Bool :=
  agree (parseYamlSingle s) (parseYamlSingleIx s)

/-- Multi-document parity: legacy and indexed must agree on the
    `Array YamlDocument` (or the same `ScanError`). -/
@[inline] def docs (s : String) : Bool :=
  agree (parseYaml s) (parseYamlIx s)

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

/-! ### Block scalars

The two root-level cases below were the whole of this section until
2026-08-05, and between them they missed all three divergences recorded
in DOCS.md § Indexed-pipeline parity gap: `|` skips the fold pass (so D1
and D2 could not fire) and a scalar that ends the document never exposes
the simple-key reset (D3). The cross-product below is the regression
set: `|`/`>` × chomp × context × {last, followed by another entry}. -/
#guard single "|\n  line1\n  line2\n"
#guard single ">\n  line1\n  line2\n"

/-! #### Chomping (D1: the folded pass must re-emit the chomped tail) -/
#guard single "a: |\n  x\n"
#guard single "a: |-\n  x\n"
#guard single "a: |+\n  x\n\n"
#guard single "a: >\n  x\n"
#guard single "a: >-\n  x\n"
#guard single "a: >+\n  x\n\n"
#guard single ">\n  x\n\n\n"
#guard single ">-\n  x\n\n\n"
#guard single ">+\n  x\n\n\n"
#guard single ">\n"
#guard single ">\n\n"
#guard single "|\n"

/-! #### Folding: more-indented lines keep their breaks (D2 — `s-white`,
    so a **tab**-led line counts, not only a space-led one) -/
#guard single ">\n  a\n   b\n  c\n"
#guard single ">\n  a\n  \tb\n  c\n"
#guard single ">\n  a\n  b\n\n  c\n"
#guard single ">\n  a\n\n\n  b\n"

/-! #### Followed by another entry (D3 — the scalar's post-state must
    clear the pending simple key and re-allow one) -/
#guard single "a: |\n  x\nb: 1\n"
#guard single "a: >\n  x\nb: 1\n"
#guard single "a: |\n  x\n\nb: 1\n"
#guard single "- |\n  x\n- 2\n"
#guard single "- >\n  x\n- 2\n"
#guard single "a:\n  b: |\n    x\n  c: 2\n"
#guard single "a: |\n  x\nb: |\n  y\n"
#guard single "a: |\n  x\n# comment\nb: 1\n"

/-! #### Explicit indentation indicator + document boundaries -/
#guard single "a: |2\n    x\n"
#guard single "a: >2\n    x\n"
#guard docs "|\n  x\n---\n|\n  y\n"
#guard docs "a: |\n  x\n---\nb: 2\n"

/-! #### Block scalar ending a *nested* collection, sibling follows (D5)

The D3 row above (`- |\n  x\n- 2`) has the scalar directly under the
sequence entry, so no indent pops between the scalar and the sibling
`-`. When the scalar instead ends a mapping nested *inside* the entry,
the next `-` needs a `blockEnd` first — the block scalar consumes its
terminating line breaks inside the cursor-level recogniser, so the
dispatcher must set `needIndentCheck` itself (RZT7, KK5P complex4). -/
#guard docs "- k: 1\n  c: |\n    x\n- k: 2\n"
#guard docs "- k: 1\n  c: >\n    x\n- k: 2\n"
#guard single "a:\n  b: |\n    x\nc: 2\n"
#guard single "? >\n  a\n:\n"

/-! #### Zero-indented block scalar at top level (`currentIndent = -1`;
    the indent floor is 0, not 1 — DK3J, FP8R) and `%` as block-scalar
    content on a zero-indented line (M7A3, W4TN: must not be scanned
    as a directive) -/
#guard docs "--- >\nline1\nline2\n"
#guard docs "--- |\nline1\n# not a comment\nline3\n"
#guard docs "--- |\n%PERCENT\n"
#guard single "a: |1\n x\n"

/-! #### Scanner strictness (plan item 7): the 15 invalid inputs the
    twin accepted until the legacy error checks were transcribed.
    `agree` requires the *same* `ScanError` from both pipelines.

    Families: tab as indentation (4EJS, Y79Y/000, Y79Y/003, DK95/01),
    block-scalar auto-detect validation (5LLU, S98Z, W9L4 — §8.1.3),
    document marker inside a multiline quoted scalar (5TRB, RXY3,
    9MQT/01 — §9.1.2), comment without preceding whitespace (9JBA,
    CVW2, SU5Z — §6.6 [75]), `#` glued to a block-scalar header
    (X4QW — §6.7 [76]), under-indented quoted continuation (QB6E). -/
#guard docs "---\na:\n\tb:\n\t\tc: value\n"
#guard single "foo: |\n\t\nbar: 1\n"
#guard single "- [\n\tfoo,\n foo\n ]\n"
#guard single "foo: \"bar\n\tbaz\"\n"
#guard single "block scalar: >\n \n  \n   \n invalid\n"
#guard single "empty block scalar: >\n \n  \n   \n # comment\n"
#guard docs "---\nblock scalar: |\n     \n  more spaces at the beginning\n  are invalid\n"
#guard docs "---\n\"\n---\n\"\n"
#guard docs "---\n'\n...\n'\n"
#guard docs "--- \"a\n... x\nb\"\n"
#guard docs "---\n[ a, b, c, ]#invalid\n"
#guard docs "---\n[ a, b, c,#invalid\n]\n"
#guard single "key: \"value\"# invalid comment\n"
#guard single "block: ># comment\n  scalar\n"
#guard docs "---\nquoted: \"a\nb\nc\"\n"

/-! #### Strictness must not over-reach: legal shapes at the same
    boundaries (tabs as separation, comments with proper whitespace,
    properly indented continuations) stay accepted by both. -/
#guard single "a:\tb\n"
#guard single "a: b\t# c\n"
#guard single "key: \"value\" # comment\n"
#guard single "- [\n foo,\n foo\n ]\n"
#guard single "quoted: \"a\n  b\"\n"
#guard single "a: \"x\n \ty\"\n"
#guard single "block: > # comment\n  scalar\n"
#guard single "a: |\n \n  x\n"

/-! ### Escaped trailing white char across a double-quoted fold (B2, DE56)

The six inputs of `Tests/Reflections/EscapedTrailingTab.lean`. An escaped
tab (`\t`, `\<TAB>`) before a line break is `ns-double-char` content and
survives the fold; a bare literal tab is `s-white` layout and is trimmed.
The legacy fix threads a `protectedLen` boundary through
`collectDoubleQuotedLoop`; `collectDoubleQuotedLoopIx` carries its own
copy, so these rows keep the two from drifting. `single` only says the
pipelines agree, so `ixContent` additionally pins what the indexed
pipeline keeps. -/

/-- The content of the scalar `parseYamlSingleIx` composes, if any. -/
def ixContent (s : String) : Option String :=
  match parseYamlSingleIx s with
  | .ok (.scalar sc) => some sc.content
  | _ => none

#guard single "\"1 trailing\\t\n    tab\"\n"
#guard single "\"2 trailing\\t  \n    tab\"\n"
#guard single "\"3 trailing\\\t\n    tab\"\n"
#guard single "\"4 trailing\\\t  \n    tab\"\n"
#guard single "\"5 trailing\t\n    tab\"\n"
#guard single "\"6 trailing\t  \n    tab\"\n"

#guard ixContent "\"1 trailing\\t\n    tab\"\n" == some "1 trailing\t tab"
#guard ixContent "\"2 trailing\\t  \n    tab\"\n" == some "2 trailing\t tab"
#guard ixContent "\"3 trailing\\\t\n    tab\"\n" == some "3 trailing\t tab"
#guard ixContent "\"4 trailing\\\t  \n    tab\"\n" == some "4 trailing\t tab"
#guard ixContent "\"5 trailing\t\n    tab\"\n" == some "5 trailing tab"
#guard ixContent "\"6 trailing\t  \n    tab\"\n" == some "6 trailing tab"

/-! ### Comments + whitespace -/
#guard single "# leading\nabc"
#guard single "a: b  # trailing"
#guard single "   abc   "
#guard single "abc\n"

/-! ### Multi-document streams -/
#guard docs "1\n---\n2\n"
#guard docs "---\nfoo\n...\n---\nbar\n"
#guard docs "%YAML 1.2\n---\n42"

/-! ### Directive strictness (Fix B, grammar-completeness Phase 1)

Both scanners must agree on the orphan-directive flip set — directives
with no following `---` are errors ([209]) — and on the surviving
boundary shapes (blank/comment gaps before `---`, `%` as mid-document
plain-scalar content, valid `%TAG` documents). -/
#guard docs "%YAML 1.2\nfoo"
#guard docs "%TAG !e! tag:x\nfoo: bar"
#guard docs "%FOO bar\na: b"
#guard docs "a\n...\n%YAML 1.2\n"
#guard docs "a\n...\n%YAML 1.2\n...\n"
#guard docs "a\n...\n%YAML 1.2\nb"
#guard docs "a\n...\n%YAML 1.2\n---\nb"
#guard docs "%TAG !e! tag:example.com,2000:app/\n---\n!e!foo bar"
#guard docs "%YAML 1.2\n\t\n---\nx"
#guard docs "%YAML 1.2\n# comment\n---\nx"
#guard docs "---\nscalar\n%YAML 1.2\n"
#guard docs "%YAML 1.2 trailing\n---\nx"
#guard docs "%YAML .2\n---\nx"

end L4YAML.Parity.Indexed

end Blanket
