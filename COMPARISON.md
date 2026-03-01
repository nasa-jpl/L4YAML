# Comparison: lean4-yaml-verified (Lean 4) vs YAML-PP (Perl 5)

Strategic opportunities to simplify and strengthen the Lean YAML 1.2.2 parser,
informed by the Perl YAML-PP implementation that achieves 100 % correctness
on the [yaml-test-suite](https://github.com/yaml/yaml-test-suite).

---

## 1  Architectures at a Glance

| Aspect | YAML-PP | lean4-yaml-verified |
|--------|---------|---------------------|
| **Pipeline** | Reader → Lexer → Grammar-table FSM → Callbacks → Events → Constructor | String → Scanner (L-layer) → Tokens → TokenParser (S-layer) → AST |
| **Disambiguation** | 42-state grammar table with multi-token lookahead via nested hash trees | Indentation stack + retroactive KEY insertion in scanner; zero lookahead in token parser |
| **Scalar resolution** | Lexer delegates to specialised fetch methods; rendering in separate `Render.pm` | Scanner resolves escapes, line folding, and chomp in a single pass (`scanBlockScalar`, `scanDoubleQuoted`, …) |
| **Formal verification** | None | 650+ theorems, 708 `#guard` compile-time checks, 0 `sorry` / 0 axiom / 0 `partial def` |
| **Test-suite score** | 100 % of full yaml-test-suite | 100 % of YAML 1.2.2 test IDs (225/225); YAML 1.3 out of scope |

Both architectures separate character-level scanning from structural parsing,
but the boundary falls in different places:

* **YAML-PP:** The *Lexer* (`Lexer.pm`, 963 lines) produces coarse tokens
  (`PLAIN`, `QUOTED`, `COLON`, `DASH`, `WS`, `EOL`, …).
  All structural disambiguation — "Is this a scalar or a mapping key?"
  "Is this an implicit mapping inside a flow sequence?" — is resolved by the
  *grammar table* (`Grammar.pm`, 2 151 lines, auto-generated from
  `etc/grammar.yaml`).

* **lean4-yaml-verified:** The *Scanner* (`Scanner.lean`, ~1 200 lines)
  produces fine-grained tokens, including virtual `blockSequenceStart`,
  `blockMappingStart`, and `blockEnd` tokens generated from indentation
  tracking, plus retroactively inserted `KEY` tokens for implicit keys.
  The *TokenParser* (`TokenParser.lean`, ~520 lines) therefore sees an
  unambiguous token stream and requires only single-token dispatch — no
  lookahead, no backtracking.

Both designs achieve the same goal of token-level disambiguation for the
grammar layer.  Each makes different trade-offs that the sections below
explore.

---

## 2  Strategic Opportunities

### 2.1  Declarative Grammar Table as Specification Artefact

**Perl insight.**
YAML-PP defines its grammar in a readable YAML file
(`etc/grammar.yaml`, 759 lines, 42 named states) and auto-generates the
Perl hash table via `etc/generate-grammar.pl`.  Every legal token-sequence
has an *explicit path* through the table.  Adding a feature means adding
table rows; correctness is auditable by inspection.

**Lean opportunity.**
`Grammar.lean` (698 lines) already provides a formal specification layer —
`ValidNode`, `ValidPlainScalarBlock`, etc. — but it operates at the *value*
level, not the *token-sequence* level.  There is no artefact that enumerates
all legal token dispatches of the scanner's `scanNextToken` or the parser's
`parseNode`.

A **`TokenGrammar.lean`** module could define a decision table:

```
State × TokenKind → Action (Consume | Transition | Return | Error)
```

Benefits:
- Makes every parse path *provably exhaustive* (every `(state, token)` pair
  is covered or explicitly errored).
- A `Decidable` instance on the table enables `#guard`-style completeness
  checks: "for all token kinds, the table has an entry."
- Aligns with the YAML-PP insight that *specification = grammar table*.

**Effort:** Medium.  The token parser already has a simple dispatch; this
would lift it into a table that can be machine-checked for completeness
without changing runtime behaviour.

---

### 2.2  Folded Block Scalar: Adopt the 4-State Machine

**Perl insight.**
`Render.pm` implements folded block scalar rendering (`>`) with a 4-state
machine whose states are `START`, `CONTENT`, `EMPTY`, `MORE`:

```perl
my $type = $line eq ''      ? 'EMPTY'
         : $line =~ m/\A[ \t]/ ? 'MORE'
         :                        'CONTENT';
```

The `MORE` state handles "more-indented" lines — lines whose content starts
with a space or tab *after* the base indentation has been stripped.  YAML
1.2.2 §8.2.1 specifies:

> *"Folding does not apply to line breaks surrounding text lines that
> contain leading white space.  Note that such a more-indented line may
> consist only of such leading white space."*

This is codified in productions [171]–[175]:
- `[171] s-nb-folded-text(n)` — normal content lines (fold newlines → spaces)
- `[172] l-nb-folded-lines(n)` — consecutive folded-text lines joined by spaces
- `[173] s-nb-spaced-text(n)` — "more-indented" lines (preserve newlines)
- `[174] l-nb-spaced-lines(n)` — consecutive spaced-text lines preserve literal newlines
- `[175] l-nb-same-lines(n)` — dispatches between folded-lines and spaced-lines

The 4-state transitions:

| Previous → Current | Action | Spec production |
|--------------------|--------|-----------------|
| `CONTENT → CONTENT` | Append space (fold) | `l-nb-folded-lines` [172] |
| `CONTENT → EMPTY` | Append `\n` | `b-chomped-last` boundary |
| `CONTENT → MORE` | Append `\n` | Transition from [172] to [174] |
| `MORE → CONTENT` | Append `\n` | Transition from [174] to [172] |
| `MORE → MORE` | Append `\n` | `l-nb-spaced-lines` [174] |
| `MORE → EMPTY` | Reclassify as `MORE`, append `\n` | Empty line within spaced block |
| `EMPTY → CONTENT` | Append `\n` | Resume folding region |
| `EMPTY → EMPTY` | Append `\n` | Consecutive blank lines |
| `EMPTY → MORE` | Append `\n` | Blank line before spaced block |
| `START → EMPTY` | Append `\n`, stay `START` | Leading blank lines (§8.1.1.2) |

**Lean current approach.**
`Scanner.lean`'s `foldBlockContent` operates on the raw `List Char` with a
single `Bool` (`prevWasNewline`) and pattern-matches only on newline
sequences:

```lean
go : List Char → String → Bool → String
  | '\n' :: '\n' :: rest, acc, _ => go ('\n' :: rest) (acc.push '\n') true
  | '\n' :: rest, acc, prevWasNewline =>
      if prevWasNewline then go rest (acc.push '\n') false
      else match rest with
        | [] => acc
        | '\n' :: _ => go rest (acc.push '\n') true
        | _ => go rest (acc.push ' ') false
  | c :: rest, acc, _ => go rest (acc.push c) false
```

This encodes ~3 effective states and makes fold/preserve decisions based
solely on whether newlines are consecutive.  It does **not** classify lines
as `CONTENT` vs `MORE` based on whether the first non-indent character is a
whitespace character.

**Why this matters.**  Consider this folded block scalar:

```yaml
>
  normal line
   more-indented line
   also more-indented
  back to normal
```

After base-indent stripping (2 spaces), the raw lines are:
```
normal line\n more-indented line\n also more-indented\nback to normal\n
```

The correct result per §8.2.1:
```
normal line\n more-indented line\n also more-indented\nback to normal\n
```

Note the newline between "normal line" and " more-indented" is preserved
(not folded to a space), because the line starting with ` more-indented`
has leading whitespace — it's a *spaced-text* line.  Likewise, the newline
between " also more-indented" and "back to normal" is preserved.

The current `foldBlockContent` would fold the newline between "normal line"
and " more-indented line" into a space, because it sees a single `\n`
followed by a non-newline character (the space) and applies `go rest
(acc.push ' ') false`.  It does not check whether that non-newline
character is a space.

**How the Perl version avoids this.**  In YAML-PP, the Lexer's
`fetch_block` strips exactly `contentIndent` spaces from each line during
collection — the same as the Lean scanner's content collection loop.  But
then `Render.pm`'s `render_block_scalar` inspects the *remaining* content
of each line: if it starts with `[ \t]` (i.e., the line had *more* leading
whitespace than `contentIndent`), it's classified as `MORE`.  The
transition table above then ensures that newlines adjacent to `MORE` lines
are never folded.

The Lean scanner's content collection loop *also* preserves extra leading
whitespace beyond `contentIndent` (the `nb-char+` loop simply copies all
characters until linebreak).  So the raw content string already contains
the leading spaces that distinguish `MORE` from `CONTENT`.  The missing
piece is that `foldBlockContent` doesn't look at them.

**Opportunity.**
Replace the 3-state `Bool` fold with an explicit 4-state `FoldState`
inductive that classifies each post-indent segment:

```lean
inductive FoldState | start | content | empty | more

private def classifyLine (line : List Char) : LineType :=
  match line with
  | [] => .empty
  | c :: _ => if c == ' ' || c == '\t' then .more else .content
```

Benefits:
- Matches productions [171]–[175] directly — each state corresponds to a
  named production.
- Makes the fold logic *independently provable* against the spec.
- Eliminates the risk of folding newlines adjacent to more-indented lines.
- The `FoldNewlines.lean` proof module can be strengthened to prove the
  `CONTENT→MORE` and `MORE→CONTENT` transitions preserve the spec invariant.

**Risk assessment.**
The current implementation may pass all yaml-test-suite tests if the test
suite happens not to exercise the `CONTENT → MORE` transition with specific
newline folding.  However, the YAML 1.2.2 spec is unambiguous: this is a
correctness issue, not an edge case.  The Perl implementation's 4-state
machine is the standard approach used by all conforming parsers (libyaml,
SnakeYAML, ruamel.yaml).

**Effort:** Low.  `foldBlockContent` is 12 lines; the 4-state version
would be ~25–30 lines.  Existing `#guard` tests and `FoldNewlines.lean`
proofs would validate the change.

---

### 2.3  Edge-Case Catalog from YAML-PP's Seven-Year Fix History

**Perl insight.**
YAML-PP's `Changes` file documents **50+ specific edge cases** fixed across
35 releases from 2018 to 2025.  These represent failure modes discovered by
running against the yaml-test-suite, user bug reports, and cross-parser
comparison.  Each fix is a concrete instance where an earlier version of
a working parser produced the wrong result — precisely the kind of input
that stresses parsing logic.

The edge cases cluster into five categories, each with a distinct failure
mechanism:

#### Category 1: Plain scalar boundary ambiguity

| Edge case | YAML-PP fix | Failure mechanism |
|-----------|-------------|-------------------|
| Scalar ending with colons: `foo::` | v0.037 | `:` without following whitespace is a valid `ns-plain-char` — terminating too early truncates content |
| Scalar starting with `?` or `:` followed by non-space | v0.007 | `ns-plain-first` allows `-?:` if followed by `ns-plain-safe` |
| Scalar containing `# ` where `#` is preceded by non-space | — | `#` is only a comment after whitespace (§6.7) |

*Why these matter for Lean:* `scanPlainScalar` in `Scanner.lean` handles
these correctly but they are not systematically tested as named edge cases.
A regression in the `: ` / `# ` termination logic would silently truncate
scalars.

#### Category 2: Flow context nesting and implicit keys

| Edge case | YAML-PP fix | Failure mechanism |
|-----------|-------------|-------------------|
| Implicit mappings in flow sequences: `[a, b: c, d]` | v0.029 | Must insert implicit mapping around `b: c` inside sequence |
| Adjacent flow values: `{"foo":23}` (no space after `:`) | v0.010 | `:` immediately after quoted scalar is a value indicator in flow |
| Empty values with properties: `[&foo, bar]` | v0.028 | Anchor on empty entry must emit empty scalar |
| Multiple `?` in flow mappings forbidden | v0.030 | Flow context disallows consecutive explicit keys |
| EOL enforcement after flow context closes | v0.030 | Content after `]`/`}` on same line is invalid |
| Nested flow: `[[{a: [1]}]]` | v0.010 | Flow level counter must be integer (not boolean) |

*Why these matter for Lean:* The scanner's `flowLevel : Nat` counter and
the token parser's `parseFlowSequence`/`parseFlowMapping` handle these, but
deeply nested combinations (flow-in-flow, implicit-key-in-flow-sequence)
are the most common source of parser regressions.  Each combination should
be a named `#guard` test.

#### Category 3: Block scalar edge cases

| Edge case | YAML-PP fix | Failure mechanism |
|-----------|-------------|-------------------|
| Empty folded block with trailing linebreaks | v0.034 | Chomp logic for zero-content `>` scalar |
| Explicit indent: only single digit (1–9) | v0.031 | Multi-digit or `0` in header must be rejected |
| Folded block with more-indented lines | v0.008 | See §2.2 above |
| Block scalar followed by comment | v0.031 | Comment after header requires preceding whitespace |

*Why these matter for Lean:* `scanBlockScalar` is 140 lines with
header → indent-detect → collect → chomp → fold stages.  Each stage has
its own failure modes.  The empty-folded-with-trailing-linebreaks case
exercises the interaction between chomp and fold: clip/strip must remove
trailing newlines *before* fold classifies empty lines.

#### Category 4: Directive and document lifecycle

| Edge case | YAML-PP fix | Failure mechanism |
|-----------|-------------|-------------------|
| Directive without document-start marker | v0.030 | `%YAML 1.2` without `---` is an error at EOF |
| Comments at end of directives | v0.031 | `%YAML 1.2 # comment` must be accepted |
| Word boundary after `%YAML` | v0.031 | `%YAML1.2` (no space) must be rejected |
| Duplicate `%YAML` directives | — | Second `%YAML` in same directive block is an error |

*Why these matter for Lean:* The scanner tracks 5 boolean flags
(`allowDirectives`, `seenYamlDirective`, `directivesPresent`,
`documentEverStarted`, `needIndentCheck`) for document lifecycle.
Interactions between these flags are subtle — e.g., `directivesPresent &&
!documentEverStarted` at EOF must throw `directiveWithoutDocument`.

#### Category 5: Tab handling

| Edge case | YAML-PP fix | Failure mechanism |
|-----------|-------------|-------------------|
| Tab indentation forbidden in block mode | v0.031 | §6.1: tabs must not be used in indentation |
| Tabs allowed after structural indicators | v0.031 | `- \tvalue` — tab after `-` is `s-separate-in-line` |
| Tab-started lines in flow context | v0.008 | Flow context has no indentation requirement |
| Tabs between directive elements | v0.031 | `%TAG\t!!\ttag:...` — tabs as separation in directives |

*Why these matter for Lean:* `skipToContent` implements a 60-line 3-way
tab check (below indent/above indent/flow context).  The probe-ahead logic
(peek past tabs to classify what follows) is a common source of
off-by-one errors.

**Opportunity.**
Create a `Tests/EdgeCaseCatalog.lean` module with systematically named
`#guard` tests for each category:

```lean
-- Category 1: Plain scalar boundaries
#guard parseYamlSingle "foo::" == .ok (.scalar ⟨"foo::", .plain⟩)
#guard parseYamlSingle "a #b" == .ok (.scalar ⟨"a #b", .plain⟩)

-- Category 2: Flow nesting
#guard parseYamlSingle "[a, b: c, d]" == .ok (.sequence .flow #[...])

-- Category 3: Block scalar edge cases
#guard parseYamlSingle ">\n" == .ok (.scalar ⟨"", .folded⟩)

-- Category 4: Directive lifecycle
#guard (parseYaml "%YAML 1.2").isError == true  -- no document start

-- Category 5: Tab handling
#guard (parseYaml "\t- a").isError == true       -- tab as indentation
```

Where the test already exists in `SuiteGuards/`, cross-reference it with a
comment.  Where it doesn't, add the guard.  This creates an auditable
mapping from "known parser failure mode" to "compile-time checked".

The value of this catalog is not just test coverage — it's *organizational*.
The yaml-test-suite tests are named by opaque IDs (`229Q`, `6BFJ`, etc.).
An edge-case catalog organized by failure mechanism makes it possible to
ask: "Do we have coverage for all known plain-scalar boundary failures?"
and get an answer by reading one file.

**Effort:** Low–Medium.  Most cases are 1–3 line `#guard` expressions.
The YAML-PP `Changes` file provides the complete inventory.

---

### 2.4  Simplify Tab Validation in `skipToContent`

**Perl insight.**
YAML-PP's lexer splits each line into `(spaces, content, eol)` using a
single regex:

```perl
$line =~ m/\A( *)([^\r\n]*)([\r\n]|\z)/
```

Tabs are handled by a simple rule: if a line starts with a tab character
in block mode, it's an error.  Tabs after the indentation region (within
content) are allowed.

**Lean current approach.**
`Scanner.lean`'s `skipToContent` (lines ~314–375) implements a multi-branch
probe:

1. Consume spaces.
2. If at a tab: peek ahead to classify — Is the tab within the indent
   region (`col ≤ currentIndent`)?  Is it followed by `#` (comment)?
   Is it followed by a linebreak?  Is it within flow context?
3. Branch accordingly: error, skip, or treat as separation whitespace.

This 60-line function handles 5+ sub-cases with nested conditionals.

**Opportunity.**
Separate the concerns into two phases:

1. **`consumeIndent`:** Consume only spaces (matching `s-indent(n)` [63]).
   Count how many spaces were consumed.
2. **`validateTabsAndSkip`:** If the next character is a tab and we're
   still within the indent region, error.  Otherwise, skip remaining
   whitespace (spaces + tabs) as `s-separate-in-line` [66].

This mirrors the Perl approach (separate indent from content) and makes
each function's contract trivial to state: `consumeIndent` touches only
spaces; `validateTabsAndSkip` handles the rest.

**Effort:** Low.  The logic doesn't change; it's a restructuring that
makes the invariant clearer for proofs in `ScannerIndent.lean`.

---

### 2.5  Tighten `Grammar.lean` Scalar Specifications

**Perl insight.**
YAML-PP's lexer uses precise regexes for plain scalar characters:

```perl
$RE_PLAIN_START = "[^$RE_INDICATOR_CHARS\\s]|[\\-?:]\\S";
$RE_PLAIN_END   = "[^\\s:#]|:[^\\s]|\\s+(?=[^\\s#])";
$RE_PLAIN_WORDS = "(?::+$RE_PLAIN_END|$RE_PLAIN_START)...";
```

Every character constraint from §7.3.3 (`ns-plain-first`, `ns-plain-char`,
`ns-plain-safe`) is encoded as a regex character class.

**Lean current approach.**
`Grammar.lean`'s `ValidPlainScalarBlock` requires only `content.length > 0`.
It does not encode `ns-plain-first` or `ns-plain-char` character constraints.
The gap between "the parser accepted this string" and "the grammar says this
string is valid" is bridged by implementation correctness, not specification.

**Opportunity.**
Add character-level predicates to `Grammar.lean`:

```lean
def isNsPlainFirst (c : Char) : Bool := ...    -- §7.3.3 [126]
def isNsPlainSafe (c : Char) (ctx : Context) : Bool := ...  -- [128]–[129]
def isNsPlainChar (c : Char) (ctx : Context) : Bool := ...  -- [130]
```

Then strengthen:

```lean
def ValidPlainScalarBlock (content : String) : Prop :=
  content.length > 0
  ∧ isNsPlainFirst content[0]!
  ∧ ∀ i, content[i]! matches nsPlainChar or permitted colon/hash context
```

This enables tight soundness proofs: `parseYaml s = .ok v → ValidYaml s v`
can check that every accepted scalar satisfies the character constraints.

Note: the character predicates already exist in `Scanner.lean` as
`canStartPlainScalar` and `isPlainSafe`.  The work is lifting them into
`Grammar.lean` as `Prop`-level definitions and adjusting proofs.

**Effort:** Medium.

---

### 2.6  Flow/Block Separation as Distinct Scanner Paths

**Perl insight.**
YAML-PP has **completely separate grammar states** for flow and block
contexts.  Flow sequences have 11 dedicated states (`FLOWSEQ`, `FLOWSEQ_NEXT`,
`FLOWSEQ_MAYBE_KEY`, `NEWFLOWSEQ`, `NEWFLOWSEQ_ANCHOR`, …).
Flow mappings have 11 more.  Block parsing has its own set.
There is zero state sharing between flow and block branches.

**Lean current approach.**
`TokenParser.lean` has distinct functions for flow and block parsing
(`parseFlowSequence` vs `parseBlockSequence`), which is good.
However, the scanner uses a single `inFlow : Bool` flag in a shared code
path for many operations (`scanValue`, `scanPlainScalar`, `skipToContent`).

**Opportunity.**
For proof clarity, consider factoring `scanPlainScalar` into explicit
flow/block variants:

```lean
def scanPlainScalarBlock (s : ScannerState) : ... := ...
def scanPlainScalarFlow  (s : ScannerState) : ... := ...
```

This would:
- Eliminate `if s.inFlow then` branches from hot paths.
- Make each function's preconditions trivial (`inFlow = true` or
  `inFlow = false`).
- Enable per-context proofs without case-splitting on the flow flag.

The YAML-PP architecture shows that flow and block contexts are
*different enough* to justify separate code paths, even at the cost of
some duplication.

**Effort:** Medium.  The scanner functions that branch on `inFlow` would
be split.  Tests and proofs reference the public `parseYaml` API and would
not need changes.

---

### 2.7  `SimpleKeyState` Retroactive Insertion — Consider Marker Tokens

**Perl insight.**
YAML-PP doesn't use retroactive token insertion.  Instead, the grammar
table's `NODETYPE_SCALAR_OR_MAP` state uses 1-token lookahead: after
consuming a `PLAIN` or `QUOTED` token, it checks if `COLON` follows.
If yes, it's a mapping key; if no, it's a scalar.  The disambiguation
happens at grammar-rule time, not lexer time.

**Lean current approach.**
`Scanner.lean`'s `scanValue` retroactively inserts `KEY` and
`blockMappingStart` tokens at a saved position via `insertAt` when `:`
is encountered.  This mutates the token array after the fact, which
complicates reasoning about scanner invariants (the token at index `i`
may shift to `i+2` after an `insertAt` elsewhere).

**Assessment.**
The current approach has a clear *benefit*: the token parser has exactly
zero lookahead.  Moving implicit-key resolution to the token parser would
require 1-token lookahead (peek for `:` after scalar).  Given that the
scanner proofs (`ScannerProofs.lean`, 53 theorems) are already more
complex than the parser proofs, **the current design is likely correct to
keep**.

However, if scanner proof complexity becomes a bottleneck, a middle ground
exists: emit a `potentialKey` marker token at the candidate position, and
let the token parser consume or discard it based on whether `:` follows.
This avoids retroactive array mutation while keeping lookahead to 1 token
in the parser.

**Effort:** Medium-High.  Would require coordinated changes to Scanner,
Token, and TokenParser.  **Recommended only if scanner proofs become
unmanageable.**

---

### 2.8  Indentation Unwinding — Emit Empty Scalars for Missing Values

**Perl insight.**
YAML-PP's `remove_nodes` function, which pops the indent stack on dedent,
explicitly emits **empty scalar events** for missing mapping values.
For example:

```yaml
a:
b: 1
```

When unwinding from `a:`'s indent level (where no value was provided),
YAML-PP emits `=VAL :` (empty scalar) before `-MAP`.

**Lean current approach.**
`Scanner.lean`'s `unwindIndents` emits `blockEnd` tokens but does not
emit empty scalars.  The token parser's `parseBlockMapping` handles missing
values by returning `YamlValue.scalar ⟨"", .plain, ...⟩` when no value
token follows `VALUE`.

**Assessment.**
Both approaches produce correct output.  The Perl approach puts the
responsibility in the scanner; the Lean approach puts it in the parser.
The Lean approach is *arguably cleaner* because the scanner stays
token-oriented (it doesn't know about "values") and the parser makes
semantic decisions.

**No change recommended.** The current Lean design is sound.

---

## 3  What NOT to Change

The Perl comparison reveals areas where the Lean implementation is already
structurally superior.  Attempting to "port" YAML-PP patterns in these
areas would be counter-productive.

### 3.1  Node Property Handling

**Lean:** `parseNodeProperties` in `TokenParser.lean` is an 18-line loop
that checks for `anchor` or `tag` tokens up to 2 times, handling both
orderings (anchor-then-tag, tag-then-anchor) naturally.

**YAML-PP:** Requires 5 dedicated grammar states (`FULLNODE`,
`FULLNODE_ANCHOR`, `FULLNODE_TAG`, `FULLNODE_TAG_ANCHOR`,
`FULLMAPVALUE_INLINE`) with ~75 table entries to encode the same
permutations.

The Lean approach is more compact, equally correct, and easier to prove
properties about (the `for _ in [:2]` loop has a trivial termination proof).
Do not add states or complicate this.

### 3.2  Error Model

**Lean:** `ScanError` is a 16-constructor ADT with structured data (line,
column, character, counts).  Error propagation uses `Except ScanError`.
Pattern-matching on errors is exhaustive; every error path is visible in
the type.

**YAML-PP:** Uses Perl's `croak` (throw-and-unwind) with string formatting.
The `Exception.pm` class provides structured fields, but errors are runtime
objects, not compile-time-checked variants.

The Lean error model is provably exhaustive and enables proofs about error
conditions (e.g., "if the input contains a tab in indentation position,
`scan` returns `ScanError.tabInIndentation`").  Do not weaken this to
string-based errors.

### 3.3  Termination Guarantees

**Lean:** Every loop uses `for _ in [:fuel]` with fuel derived from
`inputEnd - offset`.  The `scan` function's top-level loop uses
`fuel * 4` to account for tokens that don't advance the offset.  There
are no `partial def`s in the project (the 6 `partial def`s in lean4-parser
are in the dependency, not in this codebase).

**YAML-PP:** No termination proof.  Perl's control flow (regex backtracking,
unbounded `while` loops) could theoretically diverge on malformed input.

The fuel-bounded approach is a core value proposition of the verified parser.
Do not replace it with `partial def`s for "simplicity."

### 3.4  Scanner/Parser Boundary

**Lean:** Clean 132/54 production split aligned with the YAML 1.2.2 spec's
own layer classification (see `YAML_PRODUCTIONS.md`).  The scanner handles
all L-layer (lexical) productions; the token parser handles all S-layer
(syntactic) productions.

**YAML-PP:** The boundary between Lexer and Grammar is less clean.  The
lexer does some syntactic work (e.g., block scalar rendering in
`Render.pm`), and the grammar table handles some lexical concerns
(e.g., `CONTEXT` pseudo-token that re-enters the lexer).

The Lean boundary is spec-aligned and proof-friendly.  Do not blur it.

### 3.5  Zero-Lookahead Token Parser

**Lean:** The token parser dispatches on exactly one token.  Every
`match ps.peek?` has a single pattern per branch.  There is no
backtracking, no try-catch, no state save/restore.

**YAML-PP:** The grammar table's nested hash structure encodes multi-token
lookahead (peek at next token, then the one after, etc.).  States like
`FLOWSEQ_MAYBE_KEY` exist solely for disambiguation.

The Lean token parser is simpler, faster, and easier to verify.  This
simplicity is a direct consequence of pushing disambiguation into the
scanner.  Do not add lookahead to the token parser.

### 3.6  Verification Infrastructure

650+ theorems, 708 `#guard` compile-time checks, 0 `sorry`, 0 axiom,
0 `partial def` — no YAML parser in any language has this level of
formal assurance.  The proof modules (`Soundness.lean`, `Completeness.lean`,
`RoundTrip.lean`, `BlockScalarContracts.lean`, etc.) represent thousands
of hours of work.  Any proposed simplification must be evaluated against
its impact on existing proofs.

---

## 4  Priority Matrix

| # | Opportunity | Impact | Effort | Priority |
|---|-------------|--------|--------|----------|
| 2.2 | 4-state folded block scalar machine | Correctness risk | Low | **High** |
| 2.3 | Edge-case catalog from YAML-PP changelog | Test coverage | Low–Med | **High** |
| 2.5 | Tighten `Grammar.lean` scalar specs | Proof strength | Medium | **Medium** |
| 2.4 | Simplify tab validation | Proof clarity | Low | **Medium** |
| 2.1 | Declarative token grammar table | Completeness proof | Medium | **Medium** |
| 2.6 | Flow/block scanner separation | Proof clarity | Medium | **Low** |
| 2.7 | Marker tokens for implicit keys | Proof simplicity | Med–High | **Low** |
| 2.8 | Empty scalars in scanner | — | — | **No change** |

---

## 5  Summary

YAML-PP achieves 100 % correctness through *explicit enumeration*: a
grammar table that names every legal token sequence, a 4-state fold machine
that classifies every content line, and 7 years of edge-case fixes encoded
in test expectations.

lean4-yaml-verified achieves correctness through *formal structure*: a
clean scanner/parser split, fuel-bounded total functions, 650+ machine-
checked theorems, and compile-time `#guard` enforcement.

The highest-value transfer from Perl to Lean is not architectural — both
architectures are sound — but *informational*:

1. **The 4-state fold machine** (§2.2) encodes a spec distinction
   (`s-nb-folded-text` [171] vs `s-nb-spaced-text` [173]) that should be
   explicit in the Lean implementation.  The current 3-state `Bool`-based
   fold in `foldBlockContent` does not distinguish normal content lines from
   more-indented lines, risking incorrect folding of newlines adjacent to
   spaced-text blocks.  The fix is ~15 additional lines of code with a
   clear 1-to-1 mapping to YAML 1.2.2 §8.2.1 productions.  This is not an
   edge case — it is a structural divergence from the spec that happens to
   be masked when test inputs don't exercise the `CONTENT → MORE`
   transition.  The Perl impl's 4-state machine (`START`/`CONTENT`/`EMPTY`/
   `MORE`) with its `$line =~ /^\s/` classification is the standard
   approach and should be adopted.

2. **The edge-case catalog** (§2.3) captures 50+ failure modes discovered
   across 35 releases of a production parser, organized into 5 categories
   (plain scalar boundaries, flow nesting, block scalar rendering,
   directive lifecycle, tab handling).  Each entry represents a real-world
   input that broke a working parser.  Translating this catalog into
   `#guard` tests creates a systematic regression shield that goes beyond
   the yaml-test-suite's coverage — it targets the specific *parser
   implementation patterns* that fail, not just the *YAML features* that
   exist.  The organizational value is as important as the test value:
   grouping guards by failure mechanism (not by opaque test-suite ID) makes
   it possible to audit coverage of an entire failure class at a glance.

3. **The "do not change" list** (§3) is as important as the opportunities.
   The Lean parser's 18-line property handling, structured error ADT,
   fuel-bounded termination, spec-aligned layer split, and zero-lookahead
   token parser are *already better* than their YAML-PP counterparts.
   Porting YAML-PP patterns in these areas would add complexity without
   improving correctness or provability.  The comparison confirms that the
   Lean architecture's core design decisions are sound — the improvements
   are at the *detail* level (fold machine, character specifications, test
   coverage), not the *structural* level.  Recognizing what is already
   right prevents the kind of over-engineering where a "simplification"
   inspired by another implementation actually introduces new proof
   obligations, additional states, or weaker invariants.  The six areas
   called out in §3 should be treated as load-bearing — changes there
   require justification beyond "the Perl version does it differently."

Together, these three improvements would close the remaining gap between
"the parser passes all tests" and "the parser is provably correct against
the YAML 1.2.2 specification."
