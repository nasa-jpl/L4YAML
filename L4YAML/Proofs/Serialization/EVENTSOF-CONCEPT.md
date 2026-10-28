# `eventsOf` — concept note for Step 5a(iii)

Status: proposal, 2026-10-23; §7 item 1 landed the same day as `EventsOf.lean`
(defaults of §6 taken).  §6 lists the decisions it asks for.  Defaults are stated so that work can start if no
objection is raised.

## 1. The obligation

The corrected capstone 7.7 is

```lean
theorem parse_iff_grammar (input : String) :
    (∃ docs, parseYaml input = .ok docs)
      ↔ ExactSurfaceLanguage input ∧ SerializationWellFormed input
```

`SerializationWellFormed` exists today over a **trace** (`List Event`,
`SerializationWellFormed.lean`), not over the input.  Step 5a(iii) owes the
connection `eventsOf : String → List Event`, so that the capstone's second
conjunct reads `SerializationWellFormed (eventsOf input)`.  Three constraints
on it are already on record:

- **N1, non-circular.**  No call into `Scanner`, `IndexedScanner`,
  `TokenParser` or `compose`.  The right-hand side of the capstone must mean
  something without the left-hand side (package README, "what is not proved").
- **N2, exact.**  `*`, `&`, `!`, `%TAG`, `---` and `...` inside a quoted
  scalar, a comment, a block-scalar body or the interior of a plain scalar are
  not events (DOCS.md, 5a(iii): "the extraction is not independent of the
  surface work").
- **N3, two-way.**  The forward direction must *produce* the trace of an
  accepted input; the converse must *consume* a well-formed trace while
  rebuilding a scanner/parser run from an exact derivation.

## 2. A function over derivations is not available

Every surface relation is `SurfPos → SurfPos → Prop`.  A derivation of
`SLYamlStream sp sp'` lives in `Prop`, so Lean cannot eliminate it into a
`List Event`: "`eventsOf` over the exact surface derivation" cannot be a
function of the derivation.  The honest shapes are:

| | shape | price | what it buys |
|---|---|---|---|
| A | event-annotated grammar `SLYamlStreamE : SurfPos → SurfPos → List Event → Prop`, one twin per production | ~50 productions duplicated, two grammars kept in step forever | nothing B does not |
| B | a **lexical skeleton** relation `Skeleton : String → List Seg → Prop` plus an executable `eventsOfSegs : List Seg → List Event` | one new inductive over *segments*, reusing the existing surface relations as its side conditions | the trace is a function of a witness that is a plain list |
| C | fold the skeleton into `ExactSurfaceLanguage` itself (`∃ segs, ExactDerivation input segs`) | ties 5a(ii) and 5a(iii) into one definition | removes one ∃ at the cost of coupling the two open steps |
| D | an executable **reference lexer** `refLex : String → Option (List Seg)` beside B, with `refLex_sound` / `refLex_complete` against `Skeleton` | ~600 lines of spec-shaped code + two proofs | `eventsOf` becomes the function the plan names, and the capstone's right-hand side becomes **decidable** |

Proposal: **B as the specification, D as its executable twin.**  A is rejected
for its N×N price; C is rejected because 5a(ii) is row 19's work under another
name and must stay separable.

## 3. The skeleton (B)

```lean
inductive Seg where
  | anchor   (name : String)      -- `&name`, SCNsAnchorProperty
  | alias    (name : String)      -- `*name`, SCNsAliasNode
  | tagUse   (handle : String)    -- `!h!suffix`, SCNsTagProperty.named; `!suffix` and `!!suffix` carry the builtin handles
  | tagDecl  (handle : String)    -- `%TAG !h! prefix`, the narrowed SLDirective of 5a(ii)
  | docStart (directives : List Seg.Directive)   -- the directive group and its `---` (SLDirectiveDocument); `[]` for a bare `---`
  | docEnd                        -- `...`, SCDocumentEnd
  | opaque   (chars : List Char)  -- a quoted scalar, a comment, a block-scalar body, a plain-scalar interior
  | other    (chars : List Char)  -- indicators, whitespace, breaks, indentation, everything else

def eventsOfSegs : List Seg → List Event   -- anchor ↦ defineAnchor, alias ↦ useAlias, tagUse ↦ useTag, docEnd ↦ endDocument; opaque/other ↦ nothing
                                           -- docStart ds ↦ beginDocument :: (ds.filterMap tagDecl).map declareTag
```

A `%TAG` directive precedes its document's `---` lexically but belongs to that
document semantically: `WellFormedFrom` resets `Env.tagHandles` on
`beginDocument`, so emitting `declareTag` at the directive's own position would
be wiped before the first `useTag` (`%TAG !h! tag:example.com,2026:⏎--- !h!item
value` must be well-formed).  The directive group is therefore part of the
`docStart` segment and its declarations are emitted **after** `beginDocument`,
matching the order `RuntimeScopes.documentEvents` already fixes and proves
necessary.  `tagDecl` is consequently not a top-level `Seg` constructor.  Probe
set for this corner: two successive directive documents, a bare document after
`...`, a `%TAG` with no `---` (refused by `ExactSurfaceLanguage`, not by the
trace).

`Skeleton input segs` says: the segments concatenate to `input.toList`, no two
`other` segments are adjacent and no `other` segment is empty (so the
partition of non-event text is canonical: maximal runs), each
event segment is derivable by its surface relation **at the column the
concatenation puts it at**, each `opaque` segment is derivable by one of
`SCDoubleQuoted`, `SCSingleQuoted`, `SLComment`/`SCNbCommentText`,
`SCLLiteral`/`SCLFolded`'s body relations or a plain-scalar interior, and no
event lexeme starts inside an `other` segment.  The name/handle carried by an
event segment is the one the source recognisers in `SourceEvents.lean`
already read (`anchorEventAt`, `namedTagUseAt`, `namedTagDeclarationAt`),
whose exactness against the surface relations is proved there
(`alias_use_source_exact`, `named_tag_use_source_exact`, …) — those lemmas
become the side conditions of `Skeleton`'s constructors rather than theorems
about it.

Then

```lean
def SerializationWellFormedInput (input : String) : Prop :=
  ∃ segs, Skeleton input segs ∧ SerializationWellFormed (eventsOfSegs segs)
```

and the capstone's second conjunct is this predicate (renamed to
`SerializationWellFormed input` once the trace-level one is namespaced).

## 4. The uniqueness lemma is on the path whatever the quantifier

Forward direction (`parseYaml ok → ∃ segs, …`): the scanner's own token array
is a skeleton — `skeleton_of_scan : scanFiltered input = .ok ts →
Skeleton input (segsOfTokens ts)` — and its trace is well-formed by the two
guard bridges already proved (`scanner_alias_guard_exact`,
`parser_tag_guard_exact`, `SourceEvents.lean` §"Composition").  No uniqueness
needed.

Converse (`ExactSurfaceLanguage ∧ ∃ segs, … → parseYaml ok`): the converse
proof rebuilds the scanner run from the exact derivation, whose skeleton is
`segs'`; the well-formedness hypothesis is about some `segs`.  Closing the gap
needs

```lean
lemma skeleton_unique :
    Skeleton input segs → Skeleton input segs' → eventsOfSegs segs = eventsOfSegs segs'
```

— stated on the **trace**, which is what the converse consumes, not on the
segment lists: even with canonical `other` runs, two skeletons may still differ
in how they split an `opaque` region (a quoted scalar is one segment, a comment
another, but the grammar does not fix the boundary between a plain scalar's
interior and the whitespace after it), and list equality would then be false
for a reason the trace does not care about.  The content of the lemma is
*the exact surface grammar is lexically unambiguous about where its event
lexemes are* — and it is needed
under `∀` too (then the forward direction needs it instead).  This is a real
theorem about YAML 1.2.2 as narrowed by 5a(ii); it is **false** today for
`InYamlLanguage` (`scannerDrop` derives everything) and becomes provable only
after Row 12 and row 19 land.  D's `refLex_complete` *is* this lemma in
executable clothing, which is the second reason to build D: the uniqueness
proof is a determinism proof about a total function on `List Char`, not an
induction over two derivations.

## 5. Decisions already taken elsewhere that this inherits

- **Anchor timing.**  `AnchorTiming.lean` separates the normative commit (at
  node start, YAML §3.2.2.2) from L4YAML's current commit (at node
  completion).  `eventsOfSegs` emits `defineAnchor` at the `&` lexeme, i.e.
  **normative**; `&x [*x]` is well-formed.  This agrees with 5a(iv)'s runtime
  repair (in progress) and disagrees with the base-branch parser until it
  lands — the forward direction is stated against the repaired parser.
- **Document scope.**  `Env.reset` fires on `beginDocument` and `endDocument`
  only, i.e. on explicit `---` / `...`.  A bare document has no event of its
  own; two bare documents cannot be adjacent without a marker, so no anchor
  leaks between documents without a reset.
- **Scope of `SerializationWellFormed`.**  Exactly the two state-dependent
  rejection families of `ErrorCensus.lean` (`undefinedAlias`,
  `undeclaredTagHandle`).  `duplicateYamlDirective`, `directiveAfterContent`,
  `directiveWithoutDocument`, `directiveTrailingContent`, `invalidBareDocument`
  stay in `ExactSurfaceLanguage` (5a(ii)'s worklist), where they are shape,
  not state.

## 6. Open questions (defaults in bold)

1. Quantifier in `SerializationWellFormedInput`: **`∃ segs`** (forward
   direction free; `skeleton_unique` paid by the converse) or `∀ segs`?
2. Build D (`refLex`) now, beside B? **Yes** — it makes the capstone's
   right-hand side decidable, so the whole statement can be censused against
   the yaml-test-suite and `Tests/` corpora with `#guard` before any proof is
   attempted (Rule 2 at the capstone level), and it carries `skeleton_unique`.
3. `Seg.tagUse` for the builtin handles `!` and `!!`: emit `useTag "!"` /
   `useTag "!!"` (always allowed, `BuiltinTagHandle`) or no event? **Emit** —
   it keeps `eventsOfSegs` a homomorphism and `TagHandleAllowed` already
   admits them.
4. The verbatim tag `!<…>` and the tag suffix/URI characters: `opaque`
   (**default**) or a dedicated segment?
5. Anchor names may contain `*` and `!` (`ns-anchor-char` excludes only flow
   indicators and white space), and plain scalars may contain `&`, `*`, `!`
   after their first character.  Those are N2's hard cases; `Skeleton`'s
   `other`/`opaque` conditions must say that an event lexeme is recognised
   only at a node-property / node-start position.  **Carry a `Ctx` argument
   (block/flow, after-indicator) in the skeleton**, mirroring the scanner's
   dispatch, or reject the input shape?  Default: carry it.
6. Positions: should segments carry a `(line, col)` for later correspondence
   with the parser's error positions?  **No** for 7.7; columns are recomputed
   from the concatenation.
7. Module placement: `L4YAML/Proofs/Serialization/EventsOf.lean` (B) and
   `RefLex.lean` (D), both `module`, both in the serialization package's
   closure, moving the three closure-census pins once each.  **Yes.**

## 7. What lands first

1. `EventsOf.lean`: `Seg`, `Skeleton`, `eventsOfSegs`,
   `SerializationWellFormedInput`, the `Skeleton` constructors' side
   conditions discharged by `SourceEvents.lean`'s exactness lemmas, and ≥ 30
   Rule-2 instantiations (`&x [*x]`, `"&x"`, `# *x`, `a*b`, `&a*b`, `|⏎ *x`,
   `--- &x 1⏎--- *x`, `a: &x 1⏎...⏎b: *x`, `!h!x` with and without `%TAG`).
2. `RefLex.lean`: the lexer, `refLex_sound`, `refLex_canonical` (its output
   satisfies the maximal-run condition), the `#guard` census of
   `(refLex input).map eventsOfSegs` against `parseYaml`'s verdict on the two
   corpora (every disagreement recorded, none papered over).
3. `skeleton_of_scan` (forward half of N3), then `refLex_complete` — stated as
   `Skeleton input segs → ∃ segs', refLex input = some segs' ∧ eventsOfSegs segs' = eventsOfSegs segs`,
   which is `skeleton_unique` in executable clothing — after Row 12 / row 19.

## 8. `refLex_sound` — proof plan (slice 3)

Target: `refLex input = some segs → Skeleton 0 input.toList segs`.  The
decidable side conditions of `SegAt`/`Skeleton` are pinned on a 58-input grid
in `Tests/Guards/Proofs/RefLexShape.lean` (its first run refuted the directive
arm; see that file's header).  What remains is the `Prop` half, arm by arm:

| `Seg` arm | `SegAt` obligation | discharged by |
|---|---|---|
| `anchor`/`alias` | `PendingAnchorWitness`/`AliasEventWitness` + `Maximal` | `SourceEvents` bridge `isAnchorCharBool c = true ↔ isNsAnchorChar c` (`SourceEvents.lean:247`) lifted over `spanWhile`; `Maximal` is the span's stop condition |
| `tagUse` | `SCNsTagProperty` + `handleOf` + `Maximal` | the three `SCNsTagProperty` constructors (verbatim / shorthand / non-specific) over the maximal `isTagCharBool` run |
| `docStart`/`docEnd` | `SCDirectivesEnd`/`SCDocumentEnd` at col 0, `SLDirective` per directive line | constructors are literal; `SLDirective` needs `[79] s-l-comments` for the absorbed blank/comment lines, which `commentLines` consumes exactly |
| `other` | `chars ≠ [] ∧ noEventLexeme` | the arm's own guard; the `flush` discipline gives non-adjacency |
| `opaque` | `OpaqueAt` = full `SCDoubleQuoted`/`SCSingleQuoted`/`SLComment`/`SCLLiteral`/`SCLFolded`/`SNsPlain*` | **open — see below** |

### The `opaque` arm decides the shape of slice 3

`OpaqueAt` demands the real surface scalar relations, not a lexical
approximation.  Proving them for `RefLex`'s private `quoted`/`blockBody`/`plain`
would re-derive the leaf production lemmas that already exist for the scanner's
own functions: `scanDoubleQuoted_prod`, `scanSingleQuoted_prod`,
`scanBlockScalar_prod` (`ScalarProduction.lean`) each conclude
`∃ sp', ⟨relation⟩ sp sp' ∧ ScannerSurfCorr s' sp'` from `ScannerSurfCorr sc sp`
and `scanX sc = .ok s'`.

Decision (default, per §6's rule): **re-base `refLex` on byte offsets over the
original `String` and let the `opaque` arms call the scanner leaf functions on a
positioned `ScannerState`** (`{ ScannerState.mk' input with offset, col }`;
`ScannerSurfCorr` holds by `initial_corr`'s argument shifted to the suffix).
Then `OpaqueAt` is the `*_prod` conclusion and `refLex_sound` reduces to a loop
invariant `ScannerSurfCorr sc ⟨rest, col⟩ → Skeleton col rest (loop …)`.

This does not make the capstone circular: `Skeleton`, `eventsOfSegs` and
`SerializationWellFormedInput` stay independent of `Scanner`; only the executable
witness-finder reuses scanner code, and its soundness is to the independent
relation.  Cost: the `RefLex.lean` rewrite (after #57 lands, not on it) and a
re-run of the two censuses, which must not move.

Rejected: (a) widen `OpaqueAt` to a lexical span — would make
`SerializationWellFormedInput` true on inputs with no surface derivation (the
false-theorem direction); (b) prove `OpaqueAt` for the private lexers — the
double-quoted body alone (`[106]`–`[110]`, escapes, folding) is the largest
single proof in `ScalarProduction.lean`.

Open: the leaf functions read `sc.indents` (block-scalar floor) and `inFlow`;
the positioned state carries the sentinel stack, so `scanBlockScalar` runs at
floor −1.  The census must show this agrees with `parseYaml` on `- |⏎x` and
`a: |⏎  x⏎b: y` before the plan is executed.

Measured (scratch, positioned `ScannerState` with the sentinel stack only):
`scanBlockScalar` on `a: |⏎  x⏎b: y` stops at offset 9 (before `b`) and on
`- |⏎  x⏎- y` at 8 — both as the real scanner does — but on `- |⏎x⏎` it
consumes the whole input (offset 6) while `parseYaml` refuses it: at floor −1
a column-0 line is body, at the real floor 0 it is not.  So slice 3 must give
the positioned state the enclosing block indent (the `-`/`:` column `refLex`
already walks past), not the bare sentinel; `- |⏎x` and `- |⏎*x` go into the
census either way.

## 9. Correction to §8: `refLex` is not on the capstone's path

Writing the §8 rewrite exposed two facts that change the plan.

1. `scanPlainScalar_prod` (and its flow twin `scanPlainScalar_to_flowNode_flowIn`)
   conclude `SNsPlain … sp sp_gram ∧ GStar SSWhite sp_gram sp' ∧ ScannerSurfCorr s' sp'`:
   the scanner consumes trailing white that the grammar span excludes, and
   `sp_gram` is not an executable output.  No executable lexer, private or
   scanner-backed, can emit an `opaque` segment whose text is exactly the
   plain scalar's grammar span.
2. The forward surface capstone already exists: `parse_strict_proof`
   (`DocumentProduction.lean`) gets `InYamlLanguage input` from
   `scanLoop_grammar_prod`, i.e. every successful scan already carries a
   surface derivation per token (`*_prod` lemma per token kind).

Consequence: `SerializationWellFormedInput` is an `∃ segs`, so the capstone's
**forward** serialization conjunct needs a *witness*, not a *decision
procedure* — and the witness can be built in the proof from the `*_prod`
conclusions (using `sp_gram`, which the proof has even though no program does).
The **backward** direction needs trace uniqueness (§4) plus "the parser's
alias/tag checks compute `checkFrom` over the same trace", neither of which
mentions `refLex`.  `refLex` therefore stays what slice 2 made it: the census
instrument that keeps `SerializationWellFormedInput` honest against
`parseYaml`.  The §8 rewrite is dropped; the two divergence rows pinned in
`RefLexCensus.lean` are census debt, not proof debt.

### The path, restated

| # | lemma | file | depends on |
|---|---|---|---|
| S1 | `OpaqueAt` admits trailing white: `R sp sp_mid ∧ GStar SSWhite sp_mid sp'` (trailing white carries no event lexeme) | `EventsOf.lean` | — |
| S2 | `tokenEvents : Array (Positioned YamlToken) → List Event` — `.anchor`/`.alias`/`.tag`/`.documentStart`(+directives)/`.documentEnd` in stream order; executable, no `Prop` | new `TokenEvents.lean` | — |
| S3 | `scan_skeleton : scan input = .ok tokens → ∃ segs, Skeleton 0 input.toList segs ∧ eventsOfSegs segs = tokenEvents tokens`. **Inherited S3 obligations** (named by S5 slice 1, `ParseCheckFrom.lean`; each is a scanner-output fact S5 takes as a premise or absorbs in its conclusion): (a) `TagUsesShaped tokens` — every `.tag h _` the scanner emits has `h ∈ {"", "!", "!!"}` or `isNamedHandle h` (`Scanner/NodeProperties.lean`); (b) `DirectivesClosed tokens` — a directive run is followed by a directive or `.documentStart` (`directiveWithoutDocument` is refused); (c) `streamEnd`-last — `tokens[tokens.size-1].val = .streamEnd` and nothing follows it, so S5's consumed prefix is the whole array (`TokenGrammar`'s `j + 1 = ts.size`); (d) no-progress exit unreachable — the scanner never emits a `StuckAt` token (bare `key`/`value`/`blockEnd`/`flowEntry`/… or `- -` at a document start) where `parseStreamLoop` would stop early (`TG.stream_doc`'s `i < m`). With (a)–(d), `parse_ok_checkFrom` yields `checkFrom {} (tokenEvents tokens) = true` on the full array. | new module | per-token `*_prod` lemmas; a loop invariant over `scanLoop` |
| S4 | `skeleton_trace_unique : Skeleton 0 cs segs₁ → Skeleton 0 cs segs₂ → eventsOfSegs segs₁ = eventsOfSegs segs₂` | `EventsOf.lean` | `Maximal`, canonical `other` runs, `OpaqueAt` spans determined by their first char |
| S5 | `parse_ok_checkFrom : parseYaml input = .ok docs → checkFrom {} (tokenEvents tokens) = true` and its converse under `InYamlLanguage`. **S5(→) landed** (slice 1): `parseStream_ok_checkFrom`/`parse_ok_checkFrom` in `ParseCheckFrom.lean` — the parser's anchor/tag guards compose to `checkFrom {}` on the consumed token prefix `ts.extract 0 k`, under the scanner-shape premises `TagUsesShaped` (tag-use handles are `""`/`!`/`!!`/`!w+!`) and `DirectivesClosed` (a directive run ends at `---`); `k = ts.size` once the scanner side supplies `streamEnd`-last (S3's territory; the four token-level gaps the premises exist for are pinned in `Tests/AdversarialInstantiation.lean` Priority 50). S5(←) = slice 2, not started. | `ParseCheckFrom.lean` | `ParseState.declareAnchor`/`declaredIndex`, the tag-handle table, `parseStreamLoop`'s document reset; bridges `parser_alias_guard_exact`/`parser_tag_guard_exact` |

Forward conjunct = S3 + S5(→) + `checkFrom` ↔ `WellFormedFrom`.
Backward = S4 + S5(←) + the surface direction.

### Open questions (defaults in bold)

1. S3's loop invariant rides `scanLoop`, whose grammar invariant lives in
   `StreamAccum.lean` (Row 12's file).  **Default: a separate module with its
   own induction over `scanLoop`, importing StreamAccum's per-step `*_prod`
   lemmas and not editing it**; if the per-step lemmas do not expose the token
   just pushed, the alternative is one extra conjunct in Row 12's invariant,
   negotiated with that stream after item 344.
2. Trailing white (S1): relax `OpaqueAt`, **or** let the skeleton emit the
   white as an `other` run.  **Default: relax `OpaqueAt`** — one `GStar SSWhite`
   conjunct, no change to `Skeleton`, no change to the census (white has no
   event lexeme either way).
3. S4 needs `opaque` spans to be determined by their opening character and
   position (a `"` opens exactly one double-quoted span, a `#` one comment,
   …).  Plain scalars break this unless their span is pinned: **default: S4 is
   stated on traces, and the plain disjunct contributes no events whatever its
   span**, so the proof only needs "no event lexeme starts inside any admissible
   plain span", which `noEventLexeme`'s node-start discipline gives.
4. Does `refLex` keep a role?  **Default: census only** (slice 2 as merged plus
   the pinned divergence rows); no `refLex_sound`.

### Order

S1 (small), S2 (small, with a census column `tokenEvents tokens =? eventsOf input`
on the agreeing rows), S4 (the hard pure lemma, independent of everything
else), then S3 and S5 once question 1 is settled.

## 10. S4 is false on the lexical skeleton — measured, and what it means

Rule 2 before stating `skeleton_trace_unique`.  Input `[a &x, *x]`:

| skeleton | trace | `checkFrom {}` |
|---|---|---|
| `other "["`, `opaque "a &x"`, `other ", "`, `alias x`, `other "]"` | `[useAlias x]` | false |
| `other "[a "`, `anchor x`, `other ", "`, `alias x`, `other "]"` | `[defineAnchor x, useAlias x]` | **true** |

Both satisfy every decidable side condition of `SegAt`/`Skeleton` (checked with
`RefLexShape.shape`); the `Prop` half of the first is `SNsPlainOneLine .flowIn`
on `a &x`, which the parser confirms (`parseYaml "[a &x]"` succeeds — `&` is an
`ns-plain-char`); the second needs only `SCNsAnchorProperty`, which is lexical.
`scan "[a &x, *x]"` refuses (alias before its anchor), the input is in the
surface language, and the second skeleton makes `SerializationWellFormedInput`
true.  So with the `∃` quantifier the capstone's `←` direction is false on this
input, and with `∀` its `→` direction is false on `&x [a &y, *y]`-style inputs
where only a spurious reading is ill-formed.  Uniqueness (§4) was indeed the
load-bearing lemma, and it does not hold.

### Why it cannot be repaired lexically

Whether `&x` is a property or plain content is decided by *node-start*: after
`[`, `,`, `- `, `: `, `? `, a property, or at line start — but at line start
only when the line is **not** a continuation of a plain scalar, which depends on
its indentation against the enclosing block indent `n`.  `n` is a parameter of
the surface grammar, not of the text.  A relation that tracks it is a relational
copy of the scanner's indent stack: the thing §1 ruled out as circular.

### Options

1. **Event-annotated grammar** (recommended).  A second inductive family
   `TraceOf : SurfPos → SurfPos → List Event → Prop` for the event-bearing
   productions only (`c-ns-properties`, `c-ns-alias-node`, `l-directive-document`,
   `l-document-suffix`, and the node/stream productions that contain them), with
   each other production reused by reference.  `eventsOf` becomes
   `∃ ev, TraceOf ⟨input.toList, 0⟩ ⟨[], _⟩ ev`; uniqueness is
   `TraceOf sp sp' ev₁ → TraceOf sp sp' ev₂ → ev₁ = ev₂`, proven by structural
   induction *if* the annotated productions are deterministic at every choice
   point that affects events — the only such points are property-vs-plain and
   alias-vs-plain, both fixed by `ns-plain-first` excluding `&`, `*`, `!`.
   S3 becomes: `scan input = .ok tokens → TraceOf … (tokenEvents tokens)`,
   threaded through the same `*_prod` lemmas that build the surface derivation
   (Row 12's loop invariant gains one conjunct, or a sibling module re-walks it).
   `Skeleton`/`refLex`/`RefLexCensus` remain as the executable census; they lose
   their proof role.
2. Skeleton with node-start and an indent stack: the relational scanner.  Not
   circular by the letter (no `Scanner` import) but by construction; rejected.
3. RHS over the scanner's own trace (`SerializationWellFormed (tokenEvents tokens)`
   for `scan input = .ok tokens`): circular by the letter; rejected.

### What stays

S1 (`OpaqueAt` trailing white) and S2 (`tokenEvents`) are unaffected — S2 is the
trace every option compares against.  S4 as stated in §9 is withdrawn; its
replacement is `traceOf_unique` under option 1.  The census rows in
`TokenEventsCensus` already pin that `scan` refuses the three inputs whose
lexical skeleton admits a spurious well-formed reading.

### Questions

1. Option 1 — proceed?  (Default **yes**; the first slice is the `TraceOf`
   family for `c-ns-properties`/`c-ns-alias-node` and the flow-node productions,
   with `traceOf_unique` on that fragment and a census against `tokenEvents`.)
2. Where does S3's extra conjunct live — Row 12's invariant or a sibling
   module?  Same question as §9 Q1; unchanged default (sibling module).

### Sizing option 1 (measured on the tree)

The node grammar is one `mutual` block of 18 inductives (`Surface/Node.lean`,
560 lines); documents and streams are 10 more (`Surface/Document.lean`, 356
lines); `SCNsProperties`/`SCNsAliasNode` occur in 9 constructors of the block.
Events can occur inside every container, so the annotated family is a copy of
both files with a `List Event` index and `++` at every sequencing point
(~900 lines, mechanical; the scalar productions are reused by reference).

`traceOf_unique` is then a statement about the *grammar*, not the text: at
every split that can move an event lexeme between "property/alias" and "plain
content" the grammar must have exactly one choice.  In `[a &x, *x]` it does —
a second flow entry needs a `,` before it, so `&x` cannot start a node — and
that is the whole reason the lexical skeleton fails where the grammar does not.
The proof is a mutual induction with an inversion per production; its cost is
dominated by the plain-scalar boundary lemmas (`SNsPlainMultiLine` vs a
following property at line start, `s-separate` vs plain white).  Estimate:
the copy and its census in one slice; uniqueness over the flow fragment in a
second; the block fragment (multi-line plain continuation) is the long pole.

The alternative is to weaken the capstone to the forward direction plus a
backward direction conditioned on trace uniqueness as a hypothesis — honest,
cheaper, and it names the remaining obligation precisely.  That is a choice
for the owner (question 3).

3. Weaken 7.7's `←` to carry `traceOf_unique` as a hypothesis until the block
   fragment is proven?  (Default **no** — state it unconditionally and let the
   closure log carry the block-fragment item.)
   **DECIDED 2026-10-25 by the owner: no, the default.**  7.7's `←` is stated
   unconditionally; no interim `parse_iff_grammar_of_unique` twin enters the
   capstone table.  `traceOf_unique` is proved by fragment where it belongs —
   flow (`tFlowNode_unique`, in progress) then block — and until the block
   fragment lands there is simply no checked biconditional, which the closure
   log carries as an open item rather than the statement carrying it as a
   premise.  The owner's stated reason: nothing is to be added that is not real
   (no residue predicate, no second weaker capstone).

### Slice 1 landed (option 1)

`TraceOf/Leaves.lean` (combinators `TSeq`/`TSeq3`/`TAlt`/`TStar`/`TPlus`/`TOpt`,
`Lift`, leaf traces as functions of the consumed span: `propEvents`,
`aliasEvents`, `tagEvents`), `TraceOf/Node.lean` (generated by
`scripts/gen_traceof.py` from `Surface/Node.lean` — all 18 members of the
mutual block are event-bearing), `TraceOf/Document.lean` (hand-written: the
`beginDocument`-before-`declareTag` order, `...` = `endDocument`, no
`scannerDrop`).  `TraceOf input ev` and `TraceWellFormed input := ∀ ev,
TraceOf input ev → SerializationWellFormed ev` — `∀`, so an out-of-language
input is vacuous (the surface conjunct rejects it) and an in-language input
has, once `traceOf_unique` is proven, exactly one trace to check.  Next:
`traceOf_unique` over the flow fragment.

### Slice 2 landed (flow fragment)

`TraceOf/UniqueFlow.lean` proves `tFlowNode_unique` and the same-end uniqueness of
every member of the flow fragment (`TFlowContent`, `TCFlowJsonNode`,
`TCFlowJsonContent`, `TFlowSequence`, `TFlowMapping`, `TCNsProperties` and the
leaves).  The invariant is span determinism under the flow follow-set, proved by
strong induction on the remaining input length over all eight members at once;
the leaf facts are maximal separators, anchors, aliases and tags, self-delimiting
quoted scalars, and plain scalars (one-line and multi-line flow continuation)
maximal before a flow stop.  Two honest residues, both forced by the grammar
rather than the proof: entries and entry lists are not prefix-free (inside
`[a:b]` the span `a:` is the plain node `a:` or the key `a` with an empty value —
the same trace `[]`, but a different split, so the induction cannot align the two
derivations' intermediate positions without the follow; the unconditional
same-end statement for entries is neither proved nor refuted), so
`tFlowSeqEntry_unique`/`tFlowMapEntry_unique` carry the
entry follow (`EFollow`: optional separator then `,` `]` `}`) and the entry-list
lemmas carry the closing bracket (`CloseStop`), which the enclosing collection
always supplies.  The block fragment is what remains for `traceOf_unique`: block
collections and the block-scalar headers are self-delimiting, but multi-line
plain continuation (`SNsPlainMultiLine` in `blockIn`/`blockOut`) against a
property, a `- `/`? `/`: ` indicator or a less-indented line at the start of the
next line is the open boundary lemma, and the block follow-set (`b-l-folded`
then indentation) replaces `FStop`.

### Slice 3 stopped (block/document fragment): refuted, not proved

The Rule-2 grid for the block/document fragment was built BEFORE any proof, and
two of its pairs have two derivations of the same span with DIFFERENT traces,
so `traceOf_unique` is false as stated and no `UniqueBlock.lean` exists.  Both
pairs are elaborated as term-level derivations in
`Tests/Guards/Proofs/TraceOfBlockAmbiguity.lean` (`traceOf_unique_refuted`,
`traceOf_literalA`/`traceOf_literalB`):

1. `a⏎&x` — trace `[]` (one bare document whose plain scalar `a &x` folds over
   the break: `[69]` grants the continuation line indent 0 at `n = 0`) or
   `[defineAnchor x]` (bare document `a`, then `TLYamlStream.implicitContinue`
   opens a SECOND bare document `&x`).  The parser takes the first reading
   (`=VAL :a &x`, one document): grammar laxity, and exactly action row 19 —
   `implicitContinue` requires no `l-document-suffix+` and takes any document,
   the union of `[211]`'s two alternatives rather than either.  The §10 long
   pole (multi-line plain continuation vs a property at the start of the next
   line) is therefore not merely hard: at `n = 0` it is AMBIGUOUS, and the
   disjointness lemma cannot exist until the document layer is `[211]`-exact.
2. `a: |⏎   x⏎  &x b: *x` — trace `[]` (autodetected `m = 0`, content indent 1:
   both following lines are literal text, their extra spaces `nb-char`s) or
   `[defineAnchor x, useAlias x]` (`m = 2`, content indent 3: the third line is
   under-indented, so the content ends and `[173]`'s trailing
   `GOpt (SIndentLe n)` — meant for a partial indent at EOF, but not confined
   to EOF — swallows its two spaces; `TBlockMapEntries 0` resumes with the
   entry `&x b: *x`).  This refutes same-end uniqueness of `TBlockNode`
   itself.  The parser refuses the input (and its event-free cousin
   `a: |⏎   x⏎  y: z`): neither reading, scanner/grammar disagreement, the
   grammar the lax side.

Both repairs are Surface edits: `[211]` explicit-only continuation (row 19,
whose constructor DOCS records as StreamAccum-load-bearing and last to pay),
and `[173]`'s tail confined to EOF.  The second alone does not close pair 2:
with the tail removed the `m = 2` reading re-enters through pair 1's hole as a
bare document `  &x b: *x` at indent 2.  Until both land, the honest statement
of 7.7's ← has no `traceOf_unique` behind it; nothing in the flow fragment
(slice 2) is affected, and the leaf/trace machinery of slices 1–2 is reused
unchanged by the refutation terms.

**`[173]` half landed.**  `SLLiteralContent`'s partial-indent tail is now
`GOpt (fun a b => SIndentLe n a b ∧ b.chars = [])`: a partial indent is the
scalar's only at end of input; a partially indented line followed by content
is left to the enclosing collection (`l-chomped-empty` has no such line).  The
scanner agreed everywhere but one corner — `collectBlockScalarLoop` ended a
scalar AFTER the indent of a line whose first character is not an `nb-char`;
it now stops at that line's start (the parse is refused at that character
either way).  `BlockStopOk.badChar` carries a non-empty run (`GPlus`), and the
`TBlockNode`-level half of pair 2 (two entries in one mapping; its refutation lemma is gone) is CLOSED: the
`m = 2` reading no longer fits in one mapping.  Pair 2 survives exactly as
predicted — as two bare documents through `implicitContinue` (`readTwoDocs`) —
so `traceOf_unique` stays refuted until `[211]` is explicit-only.
