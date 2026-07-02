# Reaching 100% on the event and JSON axes — assessment

*What it would take for L4YAML to match `test.event` on all 402 tests and `in.json`
on every valid test, and what that touches in the parser, the grammar
formalization, and the proofs.*

Generated 2026-07-02 · baseline: **event 362/402**, **json 240/279 valid**
(see [YAML_MATRIX_COMPARISON.md](YAML_MATRIX_COMPARISON.md)).

---

## Bottom line

* **40 event diffs and 39 JSON diffs remain. Every one is a *content* or
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
| **A** | Folded `>` clip scalar drops its trailing `\n` | 21 | most | `Scanner/Scalar.lean` `foldBlockContent` EOF case | **none** | XS |
| **A′** | Folded folding mishandles blank / tab-led "more-indented" lines | MJS9, R4YG | yes | `foldBlockContent` `isMore` + blank-run logic | **none** | S |
| **B1** | Double-quoted: tab-containing blank line folds to space not `\n` | 5GBF | yes | `foldQuotedNewlinesLoop` (`skipSpaces`→tab-aware) | **none** (output form preserved) | XS |
| **B2** | Double-quoted: an *escaped* trailing tab is trimmed as whitespace | DE56/00–03 | yes | `collectDoubleQuotedLoop`/`trimTrailingWS` | none (structural only) | **M** |
| **B3** | Plain: continuation-line leading tab / tab-blank line not folded | HS5T, NB6Z, UV7Q | yes | `collectPlainScalar_handleBlockLineBreak`, `skipBlankLinesLoop` | **none** | S |
| **C1** | Lone `...` / comment-only tail emits a spurious empty document | HWV9, QT73, M7A3 | yes | `parseStreamLoop` **and** `Events.parseStreamMarkedLoop` | **none break** | S |
| **C2** | Empty node with a tag/anchor opens a *sequence* that swallows siblings | FH7J, PW8X | (event-only) | `parseNodeContent` (thread `hadProps`) | **breaks 6 lemmas, re-prove** | **M** |
| **C3** | Explicit complex mapping emits spurious empty `=VAL :` pairs | V9D5 | (event-only) | `parseBlockMappingEntryValue` add `.value` arm | **none break** | XS |
| **D** | Tag suffix percent-escape (`%21`→`!`) not decoded | 6CK3 | no (value unaffected) | `Events.resolveTagForEvent` (emitter-side) | **none** (emitter-side) | XS |
| **E** | Literal `\|` keep/clip on trailing-whitespace-only lines | JEF9/02, L24T/01 | yes | `scanBlockScalarBody` chomp of blank tail | **none** | S |
| **J1** | JSON ignores explicit core tags: `!!int 42`→`"42"` not `42` | — | 2AUY 33X3 74H7 F2C7 L94M | `Output/Json.lean` `scalarType` | **none** (Json.lean unproven) | XS |
| **J2** | Alias to a *re-defined* anchor resolves to the wrong occurrence | — | 3GZX | `Spec/Types.lean` `resolveAliases` (order-aware) | **R604 characterization at risk** | **M** |

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
maintenance.** The `@[yaml_spec …]` production tags on these functions stay valid —
the fixes make the implementations *more* faithful to productions [165]–[169]
(chomping) and [177] (`b-as-line-feed`), so spec fidelity improves rather than
regresses. **No change to the grammar formalization (`Spec/Grammar.lean`,
`Spec/CharPredicates.lean`) is required** — these are implementation-correctness
fixes, not missing productions.

---

## The three fixes that cost something

### C2 — empty tagged/anchored node opens a phantom sequence (FH7J, PW8X)
`- !!str` (empty scalar carrying `!!str`) followed by more `-` entries is parsed as
an empty **sequence** nesting the siblings. In `parseNodeContent`, a node property
followed by a `blockEntry` token routes to `parseImplicitBlockSequence` instead of
yielding an empty scalar. Fix: thread a `hadProps : Bool` and, when properties were
present, return the empty scalar. This **breaks and requires re-proving**
`parseNodeContent_ag`/`_aar` and transitively `parseBlockSequence(Loop)_ag`/`_aar`
in `Proofs/Parser/ParserNodeProofs.lean` (the anchor-growth and
alias-resolution invariants over the changed branch). The top-level
`parseNode_ag_all` structure survives; only the sub-lemmas need updating. Est.
medium — the invariants are monotone, so re-proof is mechanical, not novel.

### J2 — alias to a re-defined anchor (3GZX)
When an anchor name is defined twice, `*name` must bind to the **most recent
definition preceding the alias**. `resolveAliases` runs as a final pass over the
full anchor array with `Array.findSome?` (first match), so both aliases in 3GZX
resolve to the *first* `Foo`; the second should be `Bar`. Note the trap: a naive
"search from the end" (global last-wins) fixes the *second* alias but **regresses
the first** (`Second occurrence` legitimately wants `Foo`). Correct behaviour is
*position-relative*: each alias resolves against the definitions in scope at its
own document position. That turns `resolveAliases` from a pure pointwise map into
an order-aware traversal, which puts **R604 (`compose_map_pairs_pointwise`, the
"resolution = pointwise map" characterization) at risk** and needs re-statement.
R603 (`resolveAliases_empty`) and `WellFormedAnchors` are agnostic and survive.
Est. medium — the only defect with genuine *formalization* impact.

### B2 — escaped trailing tab in a double-quoted scalar (DE56/00–03)
`"…trailing\t\n  tab"` — the `\t` escape produces a real tab that
`trimTrailingWS` then strips as if it were layout whitespace, because by fold time
the escaped/literal distinction is lost. The fix must protect escaped trailing
whitespace from the fold-time trim (e.g. track a "last char was escaped" boundary
or defer trimming to only *unescaped* run). Contained in `collectDoubleQuotedLoop`;
its proofs are structural (`_corr`, `_preserves_tokens`, `_BoundInv`) so they hold,
but the logic itself is fiddlier than the other scanner tweaks. Est. medium-impl.

---

## Honest caveats about "verified"

1. **Structural ≠ semantic.** L4YAML's proofs establish that the parser accepts
   exactly the grammatical inputs and is well-behaved; they do **not** currently
   certify that a folded/chomped scalar equals the spec's folding *result*. That is
   precisely why these content bugs coexist with "formally verified." Reaching 100%
   on the matrix does not require touching that gap — but it also does not *close*
   it. Certifying the fixes themselves (new theorems: `foldBlockContent` equals the
   §8.1.3 folding relation, `resolveAliases` respects §7.1 anchor scope) is a
   worthwhile but **separate** proof effort.
2. **Dual emitter path.** The event stream is produced by `Events.parseStreamMarkedLoop`,
   a deliberate mirror of `TokenParser.parseStreamLoop`. The C1 document-model fix
   must be applied in **both** places or the event and JSON axes will disagree.
3. **Scorer fix (free).** Make `scripts/matrix_score.py`'s JSON branch skip dirs
   with an `error` file (as the event branch effectively does via `err-ok`). That
   alone moves the reported JSON number from 240/282 to the true 240/279 and drops
   the 3 phantom "rejects."

---

## Recommended order

1. **J1** (JSON tags) and **D** (tag percent-decode) — isolated, emitter-only,
   zero proof impact. J1 alone clears 5 JSON diffs.
2. **A** — the `foldBlockContent` EOF one-liner. Biggest single lever: ~21 event
   diffs and most of their JSON twins. Zero proof impact.
3. **A′, B1, B3, E** — the remaining scanner whitespace/tab folding tweaks. Zero
   proof impact; clears the bulk of what's left on both axes.
4. **C1, C3** — document-model and complex-mapping structure. Small, no proof
   breakage (remember the C1 dual site).
5. **C2** — empty-node/sequence; budget for re-proving the `ParserNodeProofs`
   sub-lemmas.
6. **B2, J2** — the two fiddly ones (escaped trailing whitespace; order-aware alias
   resolution with R604 restatement).

After 1–5, both axes should sit at ~99% (all but B2's 4 DE56 variants and J2's
3GZX). Steps 6 close the last two root causes for a genuine 402/402 event and
279/279 JSON.
