# Reaching 100% on the event and JSON axes — assessment

*What it would take for L4YAML to match `test.event` on all 402 tests and `in.json`
on every valid test, and what that touches in the parser, the grammar
formalization, and the proofs.*

Generated 2026-07-02 · baseline: **event 362/402**, **json 240/279 valid**
(see [YAML_MATRIX_COMPARISON.md](YAML_MATRIX_COMPARISON.md)).

**Progress:** J1 + A + A′/B1/B3/E + C1/C3 + D + C2 + B2 + J2 applied 2026-07-02 → **event 402/402**
(+40, **100%**), **json 279/279 valid** (+39, **100%**). See [Status log](#status-log). **The matrix
is closed** — the scorer's only remaining entries are the 3 phantom rejects (error tests shipping a
stale `in.json`, correctly rejected).

*(2026-07-31 note: the "pre-existing `EmitterScannability` sorries" that the build logs below
repeatedly set aside — the NonAllScalarLocality workstream, then the only open proof frontier —
were themselves closed on 2026-07-04; the library has been sorry-free since. See
[Blueprint/04-capstones.md](Blueprint/04-capstones.md), the proof-status SSOT.)*

---

## Bottom line

* *(Original baseline framing; current standing is in **Progress** above —
  after J1/A/A′/B1/B3/E/C1/C3/D/C2/B2/J2 **both axes are at 100%**: event **402/402** and
  json **279/279 valid**. No genuine diff remains.)*
  **40 event diffs and 39 JSON diffs remain. Every one is a *content* or
  *structure* defect in the scanner/parser — none is a spurious accept/reject.**
  L4YAML still parses every test with the correct success/failure verdict.
* **Two reframings of the reported numbers:**
  * The "42 JSON fails" include **3 that are not L4YAML's fault** (`9MQT/01`,
    `DK95/01`, `DK95/06`). These are *error tests* (`fail: true`) that also ship a
    stale `in.json`; L4YAML correctly rejects them. `scripts/matrix_score.py`'s
    JSON branch doesn't skip error tests, so it over-counts. Genuine JSON
    denominator is **279 valid tests, 39 diffs**.
  * **33 of the 39 JSON diffs are the same defects as the event diffs** (a wrong
    folded scalar string is wrong in JSON too). Fix the scanner and they clear on
    both axes at once. Only **6 JSON diffs are JSON-specific**.
* **The proofs are almost entirely out of the way.** L4YAML's proofs certify
  *structural* correctness — the scanner/parser terminate, advance monotonically,
  are well-bracketed, preserve state fields, and emit grammatically-valid tokens —
  **not** the exact folded *content* of a scalar. So changing the folding output
  mostly cannot break a proof (there is no proof to break). The flip side, stated
  honestly: **after these fixes the content behaviour is still unverified** unless
  new content-level theorems are added. That is optional and separable from
  reaching 100% on the matrix.
* **Only three of the ~twelve fixes carry real cost.** The rest are one-to-few-line
  scanner/emitter tweaks with zero proof impact.

---

## The defects, grouped by root cause

| # | Root cause | Tests (event) | Also JSON | Fix site | Proof impact | Effort |
|---|---|---|---|---|---|---|
| **A** ✅ | Folded `>` clip scalar drops its trailing `\n` | 21 | most | `Scanner/Scalar.lean` `foldBlockContent` EOF case | **6 guards updated**† | XS |
| **A′** ✅ | Folded folding mishandles blank / tab-led "more-indented" lines | MJS9, R4YG | yes | `foldBlockContent` `isMore` + blank-run logic | **structural**‡ | S |
| **B1** ✅ | Double-quoted: tab-containing blank line folds to space not `\n` | 5GBF | yes | `foldQuotedNewlinesLoop` (`skipSpaces`→tab-aware) | **structural + grammar**‡ | XS |
| **B2** ✅ | Double-quoted: an *escaped* trailing tab is trimmed as whitespace | DE56/00–03 | yes | `collectDoubleQuotedLoop` (thread a `protectedLen` boundary — **not** `trimTrailingWS`) | **~13 lemmas re-generalized**¶ | **M** |
| **B3** ✅ | Plain: continuation-line leading tab / tab-blank line not folded | HS5T, NB6Z, UV7Q | yes | `collectPlainScalar_handleBlockLineBreak`, `skipBlankLinesLoop` | **structural + grammar**‡ | S |
| **C1** ✅ | Lone `...` / comment-only tail emits a spurious empty document | HWV9, QT73, M7A3 | yes | `parseStreamLoop` **and** `Events.parseStreamMarkedLoop` | **5 runtime `parseStreamLoop` lemmas**§ | S |
| **C2** ✅ | Empty node with a tag/anchor opens a *sequence* that swallows siblings | FH7J, PW8X | (event-only) | `parseNode`/`parseNodeContent` (derive `isSeqEntry` — **not** `hadProps`, see log) | **6 lemmas re-proven**∥ | **M** |
| **C3** ✅ | Explicit collection-key entry split into two empty-half pairs | V9D5 | (event-only) | `parseBlockMappingEntryValue` retroactive-`key` skip | **5 runtime BEV lemmas**§ + 1 test | XS |
| **D** ✅ | Tag suffix percent-escape (`%21`→`!`) not decoded | 6CK3 | no (value unaffected) | `Events.resolveTagForEvent` (emitter-side) | **none** (emitter-side) ✓ | XS |
| **E** ✅ | Literal `\|` keep/clip on trailing-whitespace-only lines | JEF9/02, L24T/01 | yes | `scanBlockScalarBody` chomp of blank tail | **structural**‡ | S |
| **J1** ✅ | JSON ignores explicit core tags: `!!int 42`→`"42"` not `42` | — | 2AUY 33X3 74H7 F2C7 L94M | `Output/Json.lean` `scalarType` | **none** (Json.lean unproven) | XS |
| **J2** ✅ | Alias to a *re-defined* anchor resolves to the wrong occurrence | — | 3GZX | `Spec/Types.lean` `resolveAliasesOrdered` (new, compose-only; `resolveAliases` kept for `addAnchor`) | **R595/R604 guarded + new C1 joint induction**# | **M** |

XS = a few lines · S = one function · M = design change and/or re-proof.

---

## Why the proofs barely move (the key finding)

We audited every proof file that references the functions to be changed. The
folding/chomping lemmas are **structural, not content-pinning**:

* `foldBlockContent` is referenced in **one** proof file
  (`Proofs/Scanner/IndexedScalar.lean`), and only in trivial cases
  (`foldBlockContent_empty`, empty accumulator). Its exact string is never
  asserted.
* `scanBlockScalarBody`, `collectBlockScalarLoop`, `foldQuotedNewlines` appear in
  ~6 files (`ScalarCoupling`, `ScannerCorrectness`, `ScalarProduction`,
  `ScannerBound`, `FilteredGrowth`, `BlockScalarContracts`) — every lemma is
  about offset monotonicity, token count (`…_adds_one_token`), state-field
  preservation (`…_preserves_simpleKey`), bound invariants (`…_BoundInv`), or a
  grammar-production *witness* (`…_folded_prod`). **None inspects the folded
  characters.**
* The one exact-content family, `foldQuotedNewlinesIx_result_form`, pins only that
  the fold output is *either* `" "` *or* `replicate n '\n'`. The B1 fix changes
  *which* branch fires, not the output *shape*, so that lemma is preserved.

Consequence: **A, A′, B1, B3, E, C1, C3, D, J1 all land with zero proof
maintenance.** † *Correction (A, done):* this audit covered `L4YAML/Proofs/` but
not `Tests/Guards/Proofs/`, whose executable `#guard` checks **do** pin exact
scanner output. A broke 6 such guards — all encoding the *old, buggy*
folded-clip value (missing the trailing `\n`); each was updated to the
spec-correct value, which strengthens rather than weakens them. Expect the same
class of guard updates for A′, B1, B3, E. The `@[yaml_spec …]` production tags on these functions stay valid —
the fixes make the implementations *more* faithful to productions [165]–[169]
(chomping) and [177] (`b-as-line-feed`), so spec fidelity improves rather than
regresses. **No change to the grammar formalization (`Spec/Grammar.lean`,
`Spec/CharPredicates.lean`) is required** — these are implementation-correctness
fixes, not missing productions.

‡ *Correction (A′/B1/B3/E, done):* the "zero proof maintenance" call was **wrong**
for these four — they broke **structural** proofs (not `#guard`s, and not content
lemmas). The real predictor of proof breakage is **not** "content vs structure of
the spec" but **whether the fix changes the definitional shape that proofs
`unfold` and pattern-match on**:

* **B1, B3** replaced a `skipSpaces` call with `skipWhitespace` (a *different
  function*) inside `foldQuotedNewlinesLoop` / `skipBlankLinesLoop`, and threaded
  a separation-`skipWhitespace` into `collectPlainScalar_handleBlockLineBreak`.
  Every structural lemma that unfolds those and rewrites with
  `skipSpaces_preserves_X` / `_offset_ge` / `_corr` / `_BoundInv` then failed on
  the new head symbol. Fixed mechanically by swapping in the `skipWhitespace_*`
  companions (which already existed) across **~40 lemmas in 6 files**:
  `ScannerCorrectness` (4 field-preservation families × 2 loops + offsets + 4
  `rw` chains), `ScannerBound`, `ScalarCoupling`, `ScannerPlainScalarValid`,
  `EmitterScannability/ScanSteps` (dp/indents/ek families). All are
  offset-monotonicity / state-field-preservation / position-correspondence
  lemmas — none inspects the folded characters, so each swap is a rename, not a
  re-proof.
* **B1, B3 also broke a *grammar-witness* proof** (`ScalarProduction`,
  `foldQuotedNewlinesLoop_prod` / `skipBlankLinesLoop_prod` /
  `handleBlockLineBreak_prod`): the tab-aware scan yields `GStar SSWhite` where
  the old proof had `SIndent`. Since a `spaces+tab` run is only a valid
  `l-empty(n)` for `n ≤ #spaces`, the *parametric-n* `foldQuotedNewlinesLoop_prod`
  is no longer true ∀n — but its **sole caller uses n = 0**, and `SLEmpty 0`
  accepts any white run, so it was specialised to `0` and re-proved via a new
  `gstar_sswhite_to_flowlineprefix0` bridge. (This is the one non-mechanical
  proof edit.)
* **A′, E** changed only local shape (`isMore := c == ' ' || c == '\t'`; an
  EOF `let rawContent' := if … then …push '\n' else …` that keeps the returned
  *state* component syntactically identical) — the `let`-into-string form was
  chosen specifically so the state-field proofs see an unchanged `.snd` and need
  no edits. E's `collectBlockScalarLoop` EOF-newline also flipped one
  `native_decide` round-trip theorem (`roundtrip_newline`), which drove the fix
  to only add the implicit `\n` for a *whitespace-only* trailing line (matching
  libfyaml/pyyaml/ruamel and keeping the dumper faithful).

**Net:** full `lake build` is green (0 errors; the only warnings are the
pre-existing `EmitterScannability` sorries), no `#guard` broke this round, and all
12 runtime suites still pass. But the projection "one-to-few-line tweaks, zero
proof impact" understated the cost: **B1/B3 in particular are XS/S in *source* but
touched ~7 proof files.** The remaining scanner fixes (B2) should budget for the
same `skipSpaces→skipWhitespace`-class structural churn if they change which
whitespace primitive a scanned span uses.

§ *Correction (C1/C3, done):* the "none break" call was wrong a **third** time —
same lesson (definitional-shape change, not spec content). Both fixes touched the
`do`-block shape that structural proofs `unfold` + `split` on:

* **C1** added a `| some .documentEnd => …` arm to `parseStreamLoop` (a §9.2 [205]
  `l-document-suffix`, consumed without emitting a doc). Every runtime proof that
  `unfold`s `parseStreamLoop` and case-splits on `ps.peek?` gained an unhandled
  case: `parseStreamLoop_docs_from_parseDocument` (`ParserWellBehaved`),
  `parseStreamLoop_wfa` (`ParserWfaProofs`), `parseStreamLoop_aliases_resolve`
  (`ParserAnchorProofs`), `parseStreamLoop_preserves_head` +
  `parseStreamLoop_first_doc_from_entry` (`ContentFidelity`), and
  `parseStreamLoop_single_doc` (`ScanChainGrowth`). The first three take a
  one-line `documentEnd` bullet (skip ⇒ apply the IH with the same accumulator,
  anchors/tokens preserved through `tryConsume .documentEnd`). The last three are
  **entry-shape** lemmas ("the first doc came from `parseDocument` at the entry")
  that go *false* for a leading bare `...`, so they needed a
  `peek? ≠ some .documentEnd` guard threaded from their callers (all emitter
  output, whose pos-1 token is a flow opener). `Events.parseStreamMarkedLoop` has
  **no** proofs (emitter-only), so the C1 dual site's second half is proof-free.
* **C3** was applied as a *retroactive-`key` skip*: for `? <key>` whose key is a
  block/flow collection, the scanner inserts a `key` marker right before the `:`
  value marker (which opens a new line), and the parser was reading `? key` and
  `: value` as two empty-half entries. The fix skips a `key` that is *immediately
  followed by* `value` (mirrors `parseFlowMappingValue`'s existing flow handling).
  Crucially it was placed **in the `consumed = false` else branch**, leaving the
  `tryConsume .value` prefix and the whole `consumed = true` path byte-identical —
  so only each lemma's short else-tail moved: `parseBlockMappingEntryValue`'s
  `_ag`/`_aar` (`ParserNodeProofs`), `_wb`/`_pos_mono` (`ParserWellBehaved`),
  `_wfa`/`_tok` (`ParserWfaProofs`). The skip is `tryConsume .key` (not `advance`)
  so the same `tryConsume_*` companions discharge tokens/flow-nesting/anchors.
* **The C3 guard is behaviourally exact, verified against reference parsers.** The
  same retroactive-`key` token pattern appears for *both* V9D5
  (`? earth: blue` / `: moon: white`, must merge) and `? {a: 1}` / `: value` (also
  must merge). cpp / nimyaml / dotnet-yamldotnet all emit **one** `key → value`
  pair for each, so the merge is correct in both cases — one `ExplicitKeyTests`
  expectation that pinned the *old* two-entry split was spec-incorrect and was
  updated (§8.2.2 [189]: `?`/`:` at aligned indent = one explicit entry, flow or
  block key alike).
* **Indexed twins untouched (deliberate).**
  `L4YAML.TokenParser.Indexed.{parseStreamLoop,parseBlockMappingEntryValue}` are a
  separate proof-only parser (`TokenParserIx.lean`), so the `Indexed*` proof files
  did **not** break. Per precedent they stay untouched — **but they now model the
  old C1/C3 behaviour**, so the eventual Phase-3 cutover (indexed twin *replaces*
  the runtime parser) must port these two fixes and re-prove the indexed lemmas.

∥ *Correction (C2, done):* the proposed **`hadProps` gate was semantically wrong** —
it regressed `57H4` and `SKE5` (both spec examples), where a node's tag/anchor
legitimately decorates a *same-indent* block sequence that is the node's content.
Both regressions are **map values**; both targets (FH7J/PW8X) are **sequence
entries** — `hadProps` is true for all four, so it cannot discriminate. The real
signal is the parser **context** (§8.2.1 `c` = BLOCK-IN vs BLOCK-OUT): the token
*before* the node is `blockEntry` for a sequence entry, `value`/`key` for a map
value/key. `parseNode` derives `isSeqEntry := (ps.tokens[prePropPos-1] == blockEntry)`
from `ps` and passes it to `parseNodeContent`; the empty-scalar branch fires **only**
when `isSeqEntry`. Deriving it *internally* keeps `parseNode`'s signature intact, so
the `ParseNode{AG,AAR,WFA,WB,PosMono}` invariant theorems were untouched — only the
6 lemmas that `unfold parseNodeContent` gained the extra `Bool` and its empty-scalar
sub-case (`parseNodeContent_ag`/`_aar`/`_wfa`/`_wb`/`_pos_mono`; the emitter
`parseNode_emitter_advances`'s blockEntry case closed via the folded
`parseNodeContent_pos_mono` + `omega`). The 6 lemmas the original write-up predicted
were the right count — but the discriminator was not, and only a **birth probe on the
four real inputs** caught it (`Tests/Reflections/EmptyNodePropsSeqEntry.lean`;
[[feedback-inhabitation-debt-validate-target-defs]]). The `Indexed*` twin still models
the old behaviour and must port this on the Phase-3 cutover.

¶ *Correction (B2, done):* the "none (structural only)" proof-impact call was **wrong** — B2 was
the campaign's **largest** proof churn, for a structural reason the "content vs structure" heuristic
misses. Distinguishing an escaped trailing tab (content, keep) from a literal one (layout, trim)
needs *carried state* — a `protectedLen` boundary marking the last `ns-double-char` — because by
fold time both are a bare `'\t'`. No signature-free trick works (no marker codepoint is safe: `\u`/
`\U` escapes can inject *any* codepoint). So `collectDoubleQuotedLoop` **gained a parameter**, and
even though the value is defaulted to 0 (every real entry starts there) and the trim output is
*byte-identical* for non-escaped-tab inputs, the parameter broke **~13 inducting lemmas across 7
files** (`ScannerCorrectness` ×5 — tokens/simpleKey/simpleKeyStack/flowLevel/offset_ge;
`ScanSteps` ×3 — dp/indents/ek; `ScannerPlainScalarValid` flowLevel; `ScalarCoupling` `_corr`;
`ScalarProduction` `_prod`; `ScannerBound` `_BoundInv`; `EscapeProperties` `_escapeString_succeeds`).
The repair is **uniform and mechanical**: wrap each goal in `∀ p` and add `p` to `generalizing`, so
the IH covers the recursive call's shifted boundary; the lemma's *external* statement (and therefore
**all ~60 application sites**) is unchanged because it fixes `p = 0`. Two shape variants:
*intro-style* (hypothesis `intro`-duced) re-quantifies the result in the wrapper; *hparam-style*
(hypothesis is a signature binder) must `clear` it first — else `induction fuel` reverts the
signature hyp and pollutes the IH. `_escapeString_succeeds` inducts on the char list, not fuel, but
takes the same `∀ p` wrapper (its `escapeString` input has no folds, so the pinned content value is
`p`-independent). The `Indexed*` twin (`collectDoubleQuotedLoopIx`) is a **separate** function and
was untouched; it lags B2 and must port on the Phase-3 cutover.

# *Correction (J2, done):* "R604 at risk" under-scoped it — order-aware resolution is an
*architectural* change to `compose`, but the cheap repair was **additive**: a new
`YamlValue.resolveAliasesOrdered` (environment-threading, in-document-order walk) used **only** by
`YamlDocument.compose`, with the old global `resolveAliases` kept for `ParseState.addAnchor` — so
R603, `resolveAliases_scalar`, and every parser-side WFA lemma survive **verbatim**. What did move:
(i) **R595/R604** (+ their scalar corollaries) gained an `anchorFree` guard and ride a new bridge,
`resolveAliasesOrdered_of_anchorFree` — on an anchor-free tree the environment never grows, every
alias falls back to the old first-match table lookup, so ordered ≡ old from the empty env; emitter
output is always anchor-free, and both all-scalar use sites discharge the guard from R601/R608's
`anchor := none` pins. (ii) The **C1 grammability bridge** `compose_grammable` needed a genuinely
new induction (`compose_value_grammable_ordered`) with a **JOINT** conclusion — resolved value
grammable ∧ threaded env `WellFormedEnv` — because bindings made inside an earlier sibling are
consumed by later siblings; the bind edge is discharged by the case's own grammability conjunct
lifted by `adaptForFlowContext_grammable_forall`, plus two new strip/adapt algebra lemmas
(`stripAnchors_stripAnchors` idempotence, `adaptForFlowContext_stripAnchors` commutation).
(iii) The compose outer-shape lemmas re-prove **unconditionally** over the ordered walk.
(iv) The compose family's axiom profiles gained `Classical.choice` (the ordered walk's equation
lemmas carry it) — 6 reflection `#guard_msgs` audits refreshed; no `sorryAx` anywhere.

---

## The three fixes that cost something (C2 ✅, B2 ✅, J2 ✅ — all done)

### C2 — empty tagged/anchored node opens a phantom sequence (FH7J, PW8X) — **done 2026-07-02, see [Status log](#status-log)**
`- !!str` (empty scalar carrying `!!str`) followed by more `-` entries is parsed as
an empty **sequence** nesting the siblings. In `parseNodeContent`, a node property
followed by a `blockEntry` token routes to `parseImplicitBlockSequence` instead of
yielding an empty scalar.

**The `hadProps` fix proposed here was wrong** — it regresses `57H4` (Spec Example
8.22, *Block Collection Nodes*) and `SKE5` (*Anchor before a zero-indented
sequence*), where a node's properties legitimately tag/anchor a *same-indent* block
sequence that IS its content. Those inputs have properties too, so `hadProps`
cannot separate them from FH7J/PW8X. The distinguisher is the parser **context**
(§8.2.1 BLOCK-IN vs BLOCK-OUT): a node reached from a sequence entry is preceded by
a `blockEntry` token; a mapping value by a `value` token. The landed fix derives
`isSeqEntry := (ps.tokens[prePropPos-1] == blockEntry)` in `parseNode` and passes it
to `parseNodeContent`; only in the sequence-entry context does a following
`blockEntry` yield the empty scalar. Deriving the flag *inside* `parseNode` keeps
its signature unchanged, so the `ParseNode*` **invariant** theorems did not need
generalizing — only the 6 lemmas that `unfold parseNodeContent` gained the extra
`isSeqEntry` parameter and its empty-scalar sub-case (`parseNodeContent_ag`/`_aar`/
`_wfa`/`_wb`/`_pos_mono`, plus the emitter `parseNode_emitter_advances`).

### J2 — alias to a re-defined anchor (3GZX) — **done 2026-07-02, see [Status log](#status-log)**
When an anchor name is defined twice, `*name` must bind to the **most recent
definition preceding the alias** (§7.1). `resolveAliases` ran as a final pass over
the full anchor array with `Array.findSome?` (first match), so both aliases in 3GZX
resolved to the *first* `Foo`; the second should be `Bar`. Note the trap: a naive
"search from the end" (global last-wins) fixes the *second* alias but **regresses
the first** (`Second occurrence` legitimately wants `Foo`). Correct behaviour is
*position-relative* — no global table can serve two aliases that need different
values for the same name. The landed fix is **additive**: a new
`resolveAliasesOrdered` walks the tree in document order threading a binding
environment (a node's anchor binds *after* its own content, cleaned exactly like
`addAnchor`; aliases look up most-recent-first with the old first-match table as
fallback), and only `YamlDocument.compose` (+ the bounded runtime twin
`resolveAliasesLimited`) switched to it — `addAnchor` keeps the old
`resolveAliases`, so single-definition documents are byte-identical and the
parser-side proofs survive verbatim. R604 (with R595) was indeed the casualty —
restated with an `anchorFree` guard over a new ordered≡old bridge — and the C1
grammability bridge needed a new joint induction; see the # correction above.
R603 (`resolveAliases_empty`) and `WellFormedAnchors` survive as predicted.

### B2 — escaped trailing tab in a double-quoted scalar (DE56/00–03) — **done 2026-07-02, see [Status log](#status-log)**
`"…trailing\t\n  tab"` — the `\t` escape produces a real tab that
`trimTrailingWS` then strips as if it were layout whitespace, because by fold time
the escaped/literal distinction is lost. The landed fix threads a `protectedLen`
boundary through `collectDoubleQuotedLoop` (the position after the last
`ns-double-char` = last non-white *or* escaped-white char); the fold trims only the
unescaped white run past it. **The proof cost was the campaign's largest, not "none"**
— adding the parameter broke ~13 inducting lemmas across 7 files, all repaired by a
uniform `∀ p` generalization (external statements unchanged, so ~60 application sites
untouched); see the ¶ correction above.

---

## Honest caveats about "verified"

1. **Structural ≠ semantic.** L4YAML's proofs establish that the parser accepts
   exactly the grammatical inputs and is well-behaved; they do **not** currently
   certify that a folded/chomped scalar equals the spec's folding *result*. That is
   precisely why these content bugs coexist with "formally verified." Reaching 100%
   on the matrix does not require touching that gap — but it also does not *close*
   it. Certifying the fixes themselves (new theorems: `foldBlockContent` equals the
   §8.1.3 folding relation, `resolveAliasesOrdered` respects a §7.1 anchor-scope relation) is a
   worthwhile but **separate** proof effort.
2. **Dual emitter path.** The event stream is produced by `Events.parseStreamMarkedLoop`,
   a deliberate mirror of `TokenParser.parseStreamLoop`. The C1 document-model fix
   must be applied in **both** places or the event and JSON axes will disagree.
3. **Scorer fix (free).** Make `scripts/matrix_score.py`'s JSON branch skip dirs
   with an `error` file (as the event branch effectively does via `err-ok`). That
   alone moves the reported JSON number from 240/282 to the true 240/279 and drops
   the 3 phantom "rejects."
   **Done — but with err-ok semantics, not the skip variant proposed here:** the
   landed scorer counts an error test as correct iff the processor rejects it
   (`err-ok` in `scripts/matrix_score.py`, on the JSON axis too), so the JSON
   denominator stays **282** (279 valid + 3 correctly-rejected error tests).
   That is why [YAML_MATRIX_COMPARISON.md](YAML_MATRIX_COMPARISON.md) reports
   **282/282** while this document says 279/279 valid — same measurement,
   stronger denominator. Do not re-implement the skip variant.

---

## Recommended order

1. **J1** ✅ and **D** ✅ *(both done — see [Status log](#status-log))* — isolated,
   emitter-only, zero proof impact. J1 cleared 5 JSON diffs and D cleared 6CK3
   (+1 event) exactly as projected. **D is the one fix where the "zero proof
   impact" call was finally correct**: `Output/Events.lean` is imported only by the
   event exe / scorer / one reflection probe — never by the runtime parser or
   scanner path — so an emitter-side change *cannot* reach a `L4YAML/Proofs/`
   lemma. Contrast A′/B1/B3/E/C1/C3, all of which changed *parser/scanner*
   definitional shape and broke structural proofs.
2. **A** ✅ *(done — see [Status log](#status-log))* — the `foldBlockContent` EOF
   case. Biggest single lever: cleared exactly 21 event diffs (+21) and 18 JSON
   twins (+18), zero regressions. Not quite the projected one-liner: a `FoldState`
   guard was needed so all-blank clip scalars stay empty (K858), and 6
   `Tests/Guards/Proofs` `#guard`s were updated.
3. **A′, B1, B3, E** ✅ *(done — see [Status log](#status-log))* — the remaining
   scanner whitespace/tab folding tweaks. Cleared exactly 8 event diffs (+8) and
   8 JSON twins (+8), zero regressions. **Not** zero proof impact: XS/S in source
   but ~7 proof files of structural + one grammar-witness maintenance (see the
   ‡ correction above).
4. **C1, C3** ✅ *(done — see [Status log](#status-log))* — document-model and
   complex-mapping structure. Cleared exactly HWV9/M7A3/QT73 (C1) + V9D5 (C3) on
   both axes, zero regressions. **Not** proof-free (the "no proof breakage" call
   was wrong again): C1's new `parseStreamLoop` arm broke 5 runtime lemmas and C3's
   shape change broke 5 more — all mechanical (see the § note below).
5. **C2** ✅ *(done — see [Status log](#status-log))* — empty-node/sequence. Cleared
   FH7J + PW8X (+2 event), zero regressions. The proposed `hadProps` gate was
   **wrong** (regressed 57H4/SKE5); the landed fix keys on a derived `isSeqEntry`
   context flag. 6 lemmas re-proven, mechanical.
6. **B2** ✅ *(done — see [Status log](#status-log))* — escaped trailing whitespace.
   Cleared DE56/00–03 (+4 event, +4 JSON), zero regressions, **event now 402/402**.
   The projected "none (structural only)" proof cost was wrong — it was the campaign's
   *largest*: a threaded `protectedLen` parameter broke ~13 inducting lemmas across 7
   files, all repaired by a uniform `∀ p` generalization (see the ¶ correction).
7. **J2** ✅ *(done — see [Status log](#status-log))* — order-aware alias resolution.
   Cleared 3GZX (+1 JSON), zero regressions, **json now 279/279**. Landed as an
   *additive* `resolveAliasesOrdered` used only by `compose` (old `resolveAliases`
   kept for `addAnchor`); R595/R604 restated behind an `anchorFree` guard + bridge,
   and the C1 grammability bridge re-proven as a joint env-threading induction
   (see the # correction).

After 1–7 **both axes are 100%**: event **402/402** and json **279/279 valid**.
The matrix is closed; the only scorer residue is the 3 phantom rejects
(stale `in.json` on error tests — a scorer artifact, not an L4YAML defect).

---

## Status log

### J1 — explicit core tags in JSON (done 2026-07-02)

**Change.** `Output/Json.lean`: added `normalizeTag`, which expands a stored tag
to the full-URI form `resolveScalar` matches on — shorthand `!!int` →
`tag:yaml.org,2002:int` and verbatim `!<uri>` → `uri` — and applied it in
`scalarType` before `resolveScalar`. Root cause was that the composed parser
keeps the two default core handles in shorthand form (`Parser.State.resolveTag`,
"default secondary" keeps `!!` + suffix), which `resolveScalar` didn't recognize,
so `!!int 42` fell through to a string. Local tags (`!foo`) and already-resolved
URIs pass through unchanged; unknown tags still map to `str` in `resolveScalar`.

**Result.** JSON axis **240 → 245 valid** (of 279). The exact five projected
tests cleared — 2AUY, 33X3, 74H7, F2C7, L94M — with **no regressions** (diff
39 → 34; the 3 phantom "rejects" are the unrelated error-test scorer artifacts).
Event axis unchanged (JSON-only defect).

**Proofs.** None broken. `Output.Json` is imported only by the `l4yaml-json`
emitter exe (`Tests/EmitJson.lean`); no file under `L4YAML/Proofs/` references it.
Full `lake build` succeeds (833 jobs) — the entire proof set **replays from cache**
(no proof recompiled), and the only warnings are the pre-existing `sorry`s in
`EmitterScannability` (the NonAllScalarLocality workstream), untouched by this
change. Confirms the assessment's "zero proof impact / Json.lean unproven" call.

Remaining 34 JSON diffs: 3GZX (J2), DE56/00–03 (B2), 5GBF (B1), HS5T/NB6Z/UV7Q
(B3), HWV9/QT73/M7A3 (C1), MJS9/R4YG (A′), JEF9/02 & L24T/01 (E), and the
folded/plain scalar-content set (A/A′/B3) — all as classified above.

### A — folded clip trailing newline (done 2026-07-02)

**Change.** `Scanner/Scalar.lean`, `foldBlockContent`'s end-of-input case. For
**folded** scalars the fold pass runs *after* chomping (`scanBlockScalarBody`:
`if isLiteral then content else foldBlockContent content`), so the chomped
trailing `\n` run (strip→0, clip→1, keep→N) was already correct — but the old EOF
case `| [], acc, _, _ => acc` **dropped** it, undoing the chomp for every folded
scalar. (Literal scalars skip the fold, which is why the bug was folded-only.)
Fix: re-emit the pending trailing newline(s) at EOF.

**The one-liner needed a guard (K858).** Naively emitting `pending` regressed
`K858`: `clip: >` over a *blank* line must yield `""`, but chomp hands
`foldBlockContent` a lone `"\n"` and the naive fix echoed it back as `"\n"`. The
`FoldState` machine already distinguishes this: `start` means no content char was
ever seen (body was all blank lines), so the EOF case now splits —
`| [], acc, .start, _ => acc` (all-blank clip/strip stays empty) and
`| [], acc, _, pending => appendNewlines acc pending` (content-bearing → keep the
chomped tail). This cannot regress a folded-*keep*-empty test: the baseline
already produced `""` there, and the guard matches that.

**Result.** Event **362 → 383** (+21), JSON **245 → 263 valid** (of 279, +18),
**zero regressions** on either axis (verified by diffing the full pre/post fail
sets, not just counts). The 21 event tests cleared: 4Q9F 4QFQ 5BVJ 6VJK 735Y 7T8X
96L6 B3HG DK3J F6MC FP8R G992 HMK4 KK5P M5C3 MZX3 P2AD RZP5 TS54 XW4D Z67P (18 of
them also carry an `in.json` twin, cleared too). K858 — briefly regressed by the
naive form — passes with the guard.

**Proofs.** Full `lake build` green (833 jobs); no file under `L4YAML/Proofs/`
broke (the folding lemmas are structural, exactly as the audit found). **But** the
"zero proof impact" call had a blind spot: `Tests/Guards/Proofs/` holds executable
`#guard` checks that pin *exact* folded output, and 6 of them encoded the old,
buggy value (folded clip without its trailing `\n`). All 6 were updated to the
spec-correct value (strengthening, not weakening, the guard):
`ScannerContracts.lean` (1), `ScannerScalar.lean` (4), `ScannerDispatch.lean` (1).
The literal-scalar guards alongside them already carried their trailing `\n`, so
only the folded expectations moved. All 12 runtime test suites still pass
(scannertests 32, scannerspecexamples 132, specexamples 132, dumproundtrip 117,
rawparsetests 29, tests 10, flowtests 88, validationtests 84, explicitkeytests
149, adversarialtests 154, mutationtests 45, propertytests 124). The only build
warnings remain the pre-existing `EmitterScannability` sorries (NonAllScalar
Locality), untouched.

Remaining 16 genuine JSON diffs (of 279): 3GZX (J2), DE56/00–03 (B2), 5GBF (B1),
HS5T/NB6Z/UV7Q (B3), HWV9/QT73/M7A3 (C1), MJS9/R4YG (A′), JEF9/02 & L24T/01 (E).
Remaining 19 event diffs: those same root causes plus FH7J/PW8X (C2), 6CK3 (D),
V9D5 (C3). Next in the recommended order: **D** (6CK3, emitter-side tag
percent-decode) and the **A′/B1/B3/E** scanner whitespace/tab folding tweaks.

### A′, B1, B3, E — scanner whitespace/tab folding (done 2026-07-02)

**Changes** (all in `Scanner/Scalar.lean`).
* **A′** (MJS9, R4YG) — `foldBlockContent`: `isMore := c == ' '` → `c == ' ' ||
  c == '\t'` in both the line-boundary classifier and the `.start` case. After
  the content indent is stripped, a *tab*-led line is more-indented too [173], so
  the line breaks around it stay literal instead of folding to a space.
* **B1** (5GBF) — `foldQuotedNewlinesLoop`: the blank-line emptiness probe
  `skipSpaces` → `skipWhitespace` (spaces *and* tabs), so a `   \t`-style line in
  a double-quoted scalar counts as an `l-empty` line (→ `\n`) rather than folding
  to a space.
* **B3** (HS5T, NB6Z, UV7Q) — `skipBlankLinesLoop` probe `skipSpaces` →
  `skipWhitespace` (tab-only lines are blank), **and** in
  `collectPlainScalar_handleBlockLineBreak` the under-indent test stays
  `skipSpaces` (indentation is spaces only §6.1) but a trailing
  `skipWhitespace` was added past the indent so a leading continuation-line tab
  is stripped as `s-separate-in-line` [66] rather than kept as content.
* **E** (JEF9/02, L24T/01) — `scanBlockScalarBody`/`collectBlockScalarLoop`:
  EOF now acts as an implicit final `b-break` (`b-chomped-last(t)` [165]) so a
  block scalar whose file ends without a newline still chomps correctly. Two
  sites: (i) `autoDetectBlockScalarIndent`'s EOF branch folds the final
  whitespace-only line's column into `maxWSCol` (fixes JEF9/02's indent
  auto-detect); (ii) the two `collectBlockScalarLoop` EOF exits append `\n` — the
  fully-indented-blank exit guarded on `spacesConsumed > 0`, the content-line
  exit guarded on the collected line being **whitespace-only**. That second guard
  is load-bearing: reference parsers (libfyaml/pyyaml/ruamel) do *not* add a
  trailing `\n` to a real content line at EOF, and doing so would break the
  dumper round-trip (`roundtrip_newline`); a whitespace-only trailing line (as in
  L24T/01) *does* keep its `\n`.

**Result.** Event **383 → 391** (+8), JSON **263 → 271 valid** (of 279, +8),
**zero regressions** on either axis (verified by diffing the full pre/post fail
sets). Cleared, both axes: 5GBF HS5T JEF9/02 L24T/01 MJS9 NB6Z R4YG UV7Q.
Remaining 11 event diffs: 6CK3 (D), DE56/00–03 (B2), FH7J/PW8X (C2),
HWV9/M7A3/QT73 (C1), V9D5 (C3). Remaining 8 genuine JSON diffs: 3GZX (J2),
DE56/00–03 (B2), HWV9/M7A3/QT73 (C1) — plus the 3 phantom error-test rejects.

**Proofs.** These were **not** zero-impact (correcting the ‡ note above). Full
`lake build` is green (0 errors; only the pre-existing `EmitterScannability`
sorries) after fixing ~40 structural lemmas across **6 files** plus one
grammar-witness proof: `ScannerCorrectness` (offset-monotonicity + tokens/
simpleKey/simpleKeyStack/flowLevel preservation over the two loops, 4 `rw`
chains, `collectBlockScalarLoop` state shape kept identical via a `let`-into-
string form), `ScannerBound` (`_BoundInv`), `ScalarCoupling` (`_corr` via the
existing `skipWhitespace_corr`), `ScannerPlainScalarValid` (flowLevel),
`EmitterScannability/ScanSteps` (dp/indents/ek), and `ScalarProduction`
(`foldQuotedNewlinesLoop_prod` specialised n→0 + new
`gstar_sswhite_to_flowlineprefix0`). All 12 runtime suites still pass
(dumproundtrip 117/117 included). No `#guard` broke this round.

### C1, C3 — document-suffix + explicit collection-key (done 2026-07-02)

**Changes.**
* **C1** (HWV9, QT73, M7A3) — a bare `...` with no preceding content is an §9.2
  [205] `l-document-suffix`, not an empty document. Added a
  `| some .documentEnd => tryConsume .documentEnd; recurse (.afterDocumentEnd)`
  arm to **both** `TokenParser.parseStreamLoop` **and**
  `Events.parseStreamMarkedLoop` (the dual site), so a leading/interstitial `...`
  is consumed without emitting a phantom `+DOC =VAL: -DOC`. Explicit empty
  documents (`--- ...`) are untouched — their loop peek is `.documentStart`, which
  still routes through `parseDocument`.
* **C3** (V9D5) — an explicit `? <collection-key>` entry was split into two
  empty-half pairs (`{key}→null`, `null→{value}`) because the scanner inserts a
  retroactive `key` marker before the `:` value marker. `parseBlockMappingEntryValue`
  now skips a `key` that is *immediately followed by* `value` (in the
  `consumed = false` branch, guarded via `peekNext?`), keeping the entry a single
  `? key : value` pair. New two-token lookahead `ParseState.peekNext?`.

**Result.** Event **391 → 395** (+4), JSON **271 → 274 valid** (of 279, +3),
**zero regressions** (full pre/post fail-set diff). Cleared: HWV9, M7A3, QT73
(C1, both axes) + V9D5 (C3, event-only). Remaining **7 event** diffs: 6CK3 (D),
DE56/00–03 (B2), FH7J/PW8X (C2). Remaining **5 genuine JSON** diffs: 3GZX (J2),
DE56/00–03 (B2) — plus the 3 phantom error-test rejects.

**Proofs.** Green `lake build` (0 errors; only the pre-existing
`EmitterScannability` sorries) after fixing **10 runtime lemmas across 5 files**
(see the § note above): C1 broke 5 `parseStreamLoop` lemmas (`ParserWellBehaved`,
`ParserWfaProofs`, `ParserAnchorProofs`, `ContentFidelity` ×2, `ScanChainGrowth`);
C3 broke 5 `parseBlockMappingEntryValue` lemmas (`ParserNodeProofs` ×2,
`ParserWellBehaved` ×2, `ParserWfaProofs` ×2 — the else-branch placement kept the
`consumed = true` proofs untouched). Three of the C1 entry-shape lemmas + the one
`single_doc` lemma needed a `peek? ≠ documentEnd` guard threaded to their callers
(incl. the `ValueRecoveryPosition` reflection demo, `by native_decide` on real
tokens). The `Indexed*` twins were **not** touched (separate proof-only parser;
they now lag the runtime on C1/C3 — flagged for the Phase-3 cutover). All 12
runtime suites pass; one spec-incorrect `ExplicitKeyTests` expectation
(`? {a: 1}` / `: value`) was corrected to the reference-parser-confirmed single
pair (149/149).

### D — tag suffix percent-decode (done 2026-07-02)

**Change.** `Output/Events.lean`: added `percentDecodeTag` (a byte-level
`%HH`→byte loop over the tag's UTF-8, re-validated with `String.fromUTF8?`, so
multi-byte escapes like `%E2%9C%93`→✓ round-trip and a malformed `%`/`%ZZ` stays
literal) and routed the three *shorthand-resolved* arms of `resolveTagForEvent`
through it. Root cause: under `%TAG !e! tag:example.com,2000:app/`, the tag
`!e!tag%21` resolves (in `Parser.State.resolveTag`) to
`tag:example.com,2000:app/tag%21`, and the emitter printed the `%21` verbatim; §6.8
requires the tag suffix's percent escapes decoded (`%21`→`!`). The **verbatim
`!<uri>` arm is deliberately *not* decoded** — verbatim tags are taken literally
per §6.8.1 (`resolve_verbatim_not_decoded` in the probe pins this boundary).

**Result.** Event **395 → 396** (+1: 6CK3), JSON unchanged at **274/279 valid**
(6CK3 has no JSON twin — tags don't appear in JSON; "value unaffected" as
projected). **Zero regressions** (exact pre/post fail-set diff: event fails went
from `{6CK3, DE56×4, FH7J, PW8X}` to `{DE56×4, FH7J, PW8X}`, nothing added).
Remaining **6 event** diffs: DE56/00–03 (B2), FH7J/PW8X (C2). Remaining **5
genuine JSON** diffs: 3GZX (J2), DE56/00–03 (B2) — plus the 3 phantom rejects.

**Proofs.** Genuinely **zero** — the "zero proof impact" call was finally correct
(first time in this campaign). `Output/Events.lean` is imported only by the event
exe, the in-repo scorer, and the new reflection probe — never by the runtime
parser/scanner path — so no `L4YAML/Proofs/` lemma can see the change. Full
`lake build` green (834/834; only the pre-existing NonAllScalarLocality sorries).

**Inhabitation probe.** Per the inhabitation-debt discipline (a new `def` is
validated as *well-formed*, never as *doing what it should*), the birth probe
lands in `Tests/Reflections/EmitterTagPercentDecode.lean` (indexed in
`Tests/Reflections.lean`): rule-1 birth checks on `%21`/multi-byte; rule-2
boundary checks on lone-`%`/`%ZZ`/`%25` and the verbatim non-decode arm; each
`resolveTagForEvent` arm enumerated; and a **rule-5 grounded end-to-end** pin of
the full event stream from the byte-for-byte 6CK3 input through the real
`streamToEvents` pipeline (so the decode is verified where `%TAG` expansion
actually produces it). Axiom-audited (`[propext, Classical.choice, Quot.sound,
…native_decide.ax]`, no `sorryAx`).

**Known limitation (documented, not test-affecting).** The emitter decodes the
*whole* resolved URI, not just the suffix, because prefix/suffix boundary is lost
after `resolveTag` concatenates them. A `%TAG` prefix legitimately containing a
`%HH` (an `ns-global-tag-prefix` per §6.8.2.2, where escapes are *not* decoded)
would be over-decoded. No test-suite case exercises this; if one appears, move the
decode to `resolveTag`, where the suffix is still distinct (at some parser-proof
cost). `percentDecodeTag` leaves malformed `%` sequences untouched, minimizing
blast radius.

### C2 — empty tagged/anchored node opens a phantom sequence (done 2026-07-02)

**Change.** `Parser/TokenParser.lean`: `parseNode` derives
`isSeqEntry := (ps.tokens[prePropPos-1].val == blockEntry)` (guarded on
`prePropPos > 0`) and passes it to `parseNodeContent`; the `blockEntry` content arm
now returns an **empty scalar** (carrying the node's props) when `isSeqEntry`, and
opens the implicit sequence otherwise. Root cause: `- !!str` / `- &a` as a *sequence
entry* followed by a sibling `-` at the same indent was routed to
`parseImplicitBlockSequence`, which swallowed all the siblings into one nested
sequence (FH7J collapsed 3 entries → 1; PW8X 6 → 1).

**The discriminator matters — the obvious one is wrong.** The write-up's proposed
`hadProps` gate regresses `57H4` (Spec Example 8.22) and `SKE5` ("anchor before a
zero-indented sequence"): there the properties decorate a *same-indent* block
sequence that IS the node's content, and both inputs have properties, so `hadProps`
can't tell them from FH7J/PW8X. The two `#guard`s in `Tests/Guards/Proofs/
SuiteGuards/Advanced.lean` for 57H4/SKE5 turned red the instant the `hadProps`
version compiled — the fastest possible refutation. The correct signal is the parser
**context** (§8.2.1 `c`): sequence entries are preceded by a `blockEntry` token, map
values by a `value` token (verified by dumping the token streams — they are otherwise
locally identical at the decision point).

**Result.** Event **396 → 398** (+2: FH7J, PW8X), JSON unchanged at **274/279 valid**
(both have empty `in.json` — event-only, as projected). **Zero regressions** (exact
fail-set diff: event fails went `{DE56×4, FH7J, PW8X}` → `{DE56×4}`, nothing added;
JSON unchanged). FH7J and PW8X now emit the **byte-for-byte** expected event streams.
Remaining **4 event** diffs: DE56/00–03 (B2). Remaining **5 genuine JSON** diffs:
3GZX (J2), DE56/00–03 (B2) — plus the 3 phantom rejects.

**Proofs.** 6 lemmas re-proven, all mechanical; the ∥ note has the full account.
Deriving `isSeqEntry` inside `parseNode` (rather than threading a parameter through
the mutual recursion) kept `parseNode`'s signature — and therefore every
`ParseNode*` invariant theorem and all its call sites — untouched. Only the lemmas
that `unfold parseNodeContent` gained the extra `Bool`: `parseNodeContent_ag`/`_aar`
(`ParserNodeProofs`), `_wfa` (`ParserWfaProofs`), `_wb`/`_pos_mono` +
`parseNode_emitter_advances` (`ParserWellBehaved`). The direct
`parseNodeContent … {}` uses in the flow/emitter acceptance proofs
(`FlowParserAcceptance`, `EmitterScannability`, `ContentFidelity`,
`NonAllScalarLocality`) were generalized over the flag (`∀ b, … b = …`) since their
peek is bracket/scalar (isSeqEntry-independent). Full `lake build` green (834/834;
only the pre-existing NonAllScalarLocality sorries).

**Inhabitation probe.** `Tests/Reflections/EmptyNodePropsSeqEntry.lean` (indexed):
rule-5 grounded pins of the full FH7J/PW8X event streams (the two POSITIVE cases),
plus rule-2 **boundary** pins of 57H4/SKE5's full streams carrying `+SEQ <tag>` /
`+SEQ &anchor` on the *collection* — so a regression to the empty-scalar reading
(which would emit `=VAL <…> :`) is caught. This probe is exactly the artifact the
inhabitation-debt discipline calls for: the `hadProps` branch *type-checked*, and
only exercising the four real inputs proved it did the wrong thing. Axiom-audited
(`[propext, Classical.choice, Quot.sound, …native_decide.ax]`, no `sorryAx`).

**Indexed twin.** `TokenParserIx.parseNodeContent` is unchanged (still models the old
behaviour); the Phase-3 cutover must port this fix.

### B2 — escaped trailing tab in a double-quoted scalar (done 2026-07-02)

**Change.** `Scanner/Scalar.lean`: `collectDoubleQuotedLoop` gained a
`protectedLen : Nat := 0` parameter — the count of leading `content` chars a fold must
**not** trim, i.e. the position after the last `ns-double-char` (a non-white char *or* an
**escaped** white char, `ns-esc-tab`/`ns-esc-space` [62]). The line-break branch now trims
only the *unescaped* white run past `protectedLen` (`content.toList.take protectedLen`
replaces `trimTrailingWS content`); the escape branch protects its pushed char
(`protectedLen := content'.length`), a literal space/tab leaves it (stays trimmable), and a
folded space stays trimmable while folded line-feeds are protected. Root cause: an escaped
`\t`/`\<TAB>` decodes to a real tab that, by fold time, is indistinguishable from a literal
trailing tab, so `trimTrailingWS` stripped it (DE56/00–03 lost `…trailing<TAB>`). §7.3.1:
an escaped tab is content (`ns-double-char`), a bare trailing tab is layout (`s-white`,
dropped by `s-flow-folded` [74]).

**Why a parameter was unavoidable.** The distinction requires *carried state* — it can't be
recomputed from `content` alone at the fold, and no in-band marker is safe (a `\u`/`\U`
escape can inject any codepoint, so any sentinel could collide with real content). Threading
`protectedLen` is the minimal such state.

**Result.** Event **398 → 402** (+4: DE56/00, /01, /02, /03 — **100%, 402/402**), JSON
**274 → 278 valid** (of 279, +4: the same four twins). **Zero regressions** (exact pre/post
fail-set diff: event fails went `{DE56×4}` → `{}`; json genuine fails `{3GZX, DE56×4}` →
`{3GZX}`). DE56/04–05 (bare literal trailing tabs) still trim, unchanged. Only **1 genuine
JSON diff** remains: 3GZX (J2). All 12 runtime suites pass with identical counts
(scannertests 32, specexamples 132, scannerspecexamples 132, dumproundtrip 117, …).

**Proofs.** **Not** zero-impact — the *largest* churn of the campaign (¶ correction). The new
parameter broke **~13 inducting lemmas across 7 files**, all repaired **mechanically** by the
same `∀ p` generalization: wrap the goal in `suffices H : ∀ (p : Nat) …`, add `p` to
`generalizing`, bump the IH applications (`ih … _ … h`). Because the wrapper fixes `p = 0` (the
default every real entry uses) the lemmas' **external statements are unchanged**, so their
**~60 application sites needed no edits**. Files: `ScannerCorrectness` (tokens / simpleKey /
simpleKeyStack / flowLevel / offset_ge), `ScanSteps` (dp / indents / ek),
`ScannerPlainScalarValid` (flowLevel), `ScalarCoupling` (`_corr`), `ScalarProduction`
(`_prod`), `ScannerBound` (`_BoundInv`), `EscapeProperties` (`_escapeString_succeeds`). Two
mechanical gotchas: (i) *hparam-style* lemmas (hypothesis is a signature binder) must `clear`
it before the fresh `intro`, or `induction fuel` reverts it and pollutes the IH (the
intro-style ones don't); (ii) the generalized `p` lands **first** in the IH, so non-`_`
applications prepend a `_`. Full `lake build` green (835 jobs; only the pre-existing
NonAllScalarLocality sorries at `EmitterScannability` 957/1072).

**Inhabitation probe.** `Tests/Reflections/EscapedTrailingTab.lean` (indexed in
`Tests/Reflections.lean`): rule-5 grounded pins of the full DE56/00–03 event streams (the four
POSITIVE cases, each carrying the kept `\t`), plus rule-2 **boundary** pins of DE56/04–05 (bare
literal tabs whose streams have NO `\t` — so a regression to "keep every trailing tab" is
caught). The escaped/literal pair (`\t` vs `\<TAB>` vs bare `<TAB>`) is exactly the distinction
that `type-checks` under any bookkeeping but is only *validated* on real bytes. Axiom-audited
(`[propext, Classical.choice, Quot.sound, …native_decide.ax]`, no `sorryAx`).

**Indexed twin.** `collectDoubleQuotedLoopIx` (`Scanner/IndexedScanner.lean`) is a separate
function and was untouched; it lags B2 and must port on the Phase-3 cutover.

### J2 — order-aware alias resolution (done 2026-07-02) — **the matrix is closed**

**Change.** `Spec/Types.lean`: new `YamlValue.resolveAliasesOrdered (v) (anchors) (env := [])`
— an in-document-order walk threading a binding environment, most recent first. A node's anchor
binds *after* its own content is resolved (so an alias never sees the node it sits inside), and
bound values are cleaned exactly like `ParseState.addAnchor` cleans stored anchors
(`stripAnchors` then `adaptForFlowContext`). An alias takes the most recent env binding; with no
preceding in-tree definition it falls back to the parse-time table with the **old first-match
lookup** (degenerate/cyclic docs unchanged — and moot, since the parser already rejects forward
aliases at parse time, §7.1). `YamlDocument.compose` switched to the ordered walk; a new
`YamlValue.anchorFree` predicate supports the proof bridge. `Config/Limits.lean`:
`resolveAliasesLimited` (the bounded runtime twin used by `composeLimited`) threads the same
environment, keeping its node-count/cycle/expansion accounting. **`ParseState.addAnchor` keeps
the old `resolveAliases`** — the additive-parallel-function architecture is what confined the
proof churn (see the # correction): for any single-definition document the two disciplines
agree (the fallback covers it), so only rebinding documents change behaviour.

**Result.** JSON **278 → 279 valid** (of 279, +1: 3GZX — **100%**). Event unchanged at
**402/402** (`compose` never runs on the event axis; aliases emit as `=ALI` from the
serialization tree). **Zero regressions** — the scorer's fail set is now exactly the 3 phantom
rejects (`9MQT/01`, `DK95/01`, `DK95/06`, stale `in.json` on error tests). Rebinding resolves
per §7.1 across mapping pairs, sequence items, and out of nested siblings
(`{"a":1,"b":1,"c":2,"d":2}`, `[1,1,2,2]`, and the nested-escape pin in the probe). All runtime
suites pass with identical counts (scannertests 32, specexamples 132, scannerspecexamples 132,
dumproundtrip 117, rawparsetests 29, tests 10, flowtests 88, validationtests 84,
explicitkeytests 149, adversarialtests 154, mutationtests 45, propertytests 124), plus
limittests **43/43** — the env-threaded `resolveAliasesLimited` preserves the billion-laughs
accounting — and adversarialinstantiation 2441, productioncoverage 728.

**Proofs.** The predicted R604 risk was real but under-scoped; the full repair (# correction):
R595/R604 + scalar corollaries gained an `anchorFree` guard over the new bridge
`resolveAliasesOrdered_of_anchorFree` (ordered ≡ old from the empty env on anchor-free trees;
both all-scalar use sites in `EmitterScannability` discharge the guard from R601/R608's
`anchor := none` pins); `compose_grammable` (C1) re-proven via
`compose_value_grammable_ordered`, a Scannable-induction with a **JOINT** conclusion
(`Grammable` ∧ `WellFormedEnv`, the env generalized) whose bind edge reuses the case's own
grammability conjunct lifted by `adaptForFlowContext_grammable_forall`; new supporting algebra
`stripAnchors_stripAnchors` / `adaptForFlowContext_stripAnchors`; compose outer-shape lemmas
re-proven unconditionally; `compose_scalar_content(-Ix)` re-routed through
`resolveAliasesOrdered_fst_scalar(-Ix)`. R603 and `WellFormedAnchors` survived verbatim as
predicted. Compose-family axiom profiles gained `Classical.choice` (ordered walk equation
lemmas); 6 reflection `#guard_msgs` audits refreshed — no `sorryAx`. Full `lake build` green
(837 jobs; only the 5 pre-existing Front-B sorries).

**Inhabitation probe.** `Tests/Reflections/OrderAwareAlias.lean` (indexed in
`Tests/Reflections.lean`): the env plumbing *type-checks* under first-wins, last-wins, and
positional lookup alike, so the pins bracket the fix from both sides — 3GZX's full JSON
(`Second occurrence` pins `Foo` = NOT last-wins, `Reuse anchor` pins `Bar` = NOT first-wins),
a minimal rebind mapping, sequence-item threading (`goList`), nested-binding escape (the
joint-conclusion motivation made concrete), plus rule-2 boundary pins: 3GZX's **event** stream
byte-identical (both `=ALI` survive) and a forward alias still parse-rejected. Axiom-audited
(`[propext, Classical.choice, Quot.sound, …native_decide.ax]`, no `sorryAx`).

**Indexed twin.** None lagging from J2: `IndexedComposition` shares `YamlDocument.compose`
(fix inherited), and `ParseStateIx.addAnchor` keeps the old `resolveAliases` just like the flat
parser. The Phase-3 cutover debt remains C1/C2/B2 (+ earlier scanner fixes) only.
