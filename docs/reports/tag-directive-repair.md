# A missing YAML requirement, a checked obstruction, and a working repair

## Decision for review

The unchanged integration library admits duplicate TAG declarations that
YAML 1.2.2 §6.8.2 forbids. Its actual event projection loses a required
distinction, and its existing token-completeness theorem requires the
offending scanner output to be accepted. A token-parser repair therefore
needs a corresponding correction to the admitted token contract.

This branch demonstrates that correction through both runtime parsers and
the existing token-completeness consumer. It is a bounded repair of directive
uniqueness. Source-level Group 7.7 remains open.

Primary normative source: <https://yaml.org/spec/1.2.2/#682-tag-directives>.
The independently reviewable formal interpretation is at most one explicit
TAG declaration per handle per document, regardless of prefix.

## Exact source and evidence lineage

- Integration parent: `14eb6dbab845d2ac61f171a9ed61906d3f9ffb2f`.
- Original production subtree: `4197c0b6f2fb369e9806ca486d38aef87b077c81`.
- Unchanged-source admission proof:
  [27035085](https://github.com/metalogiclabs/L4YAML/commit/27035085b745750874699c347d61f0db97f9f732),
  [TagDirectiveCompleteness.lean](https://github.com/metalogiclabs/L4YAML/blob/27035085b745750874699c347d61f0db97f9f732/Tests/Guards/Proofs/TagDirectiveCompleteness.lean).
  Fresh [Actions 44813470858](https://github.com/metalogiclabs/L4YAML/actions/runs/44813470858)
  passed all 66 targeted jobs with standard-three axiom profiles.
- Original source/trace capstone obstruction:
  [bf6563fb](https://github.com/metalogiclabs/L4YAML/commit/bf6563fb22f2d140633468884f380304129c9ddb).
- Separate corrected-research positive witness for `a\n*x`:
  [1a72d1c5](https://github.com/metalogiclabs/L4YAML/commit/1a72d1c54c03de568481f82489ccc8623119e016),
  [successful run 44809611172](https://github.com/metalogiclabs/L4YAML/actions/runs/44809611172).

The alias-ambiguity proof, its corrected positive witness, and this directive
repair have distinct source boundaries. They are not a claim that all source
grammar corrections have been integrated on this branch.

## What the unchanged-source theorem establishes

The exact single declaration is `%TAG ! !x\n--- a` (15 bytes). The duplicate is
`%TAG ! !x\n%TAG ! !x\n--- a` (25 bytes). Here `\n` denotes an actual LF;
neither source has a trailing newline.

The decisive unchanged-source kernel acceptance proof concerns
`TokenParser.parseYaml` and its actual classic scanner.
Both inputs project to `[beginDocument]`, while the parser retains handle
lists `[["!"]]` and `[["!", "!"]]`. The second violates uniqueness.

The unchanged-source proof establishes `TokenGrammar` and `TokenStateOk`
for the duplicate's actual scanner output and consumes the production
`parseStream_accepts` lemma. It also proves that no replacement token parser
can retain those original completeness premises while rejecting this stream
or universally enforcing the independently extracted token requirement.

This is a valid theorem about an insufficient admitted language. A scanner-only
repair could instead narrow which arrays reach a permissive raw-token parser;
the checked obstruction does not prohibit that alternative architecture.

## The repaired requirement and its real consumers

| Boundary | Change | Evidence |
|---|---|---|
| Explicit runtime directives | `TagDirectiveHandles` retains every handle; `TagDirectivesUnique` is `List.Nodup` | Both document preparations check it before handle registration |
| Classic and indexed runtime | Repeated handles return `.duplicateTagDirective` | Public API controls and universal successful-result proofs |
| Independent token grammar | `TG.document` requires `DirectiveHandlesUnique ts i d` on the full directive span | The grammar checker checks the same condition |
| Token collector correspondence | Exact equality of the independently projected handles and the actual collected list | Extended `dirLoop` and `parseDirectives_ok` |
| Existing reverse consumer | `prepare_ok` derives the runtime guard from the token grammar; `parseStream_accepts` compiles | No parser-success or guard-success assumption introduced |
| Existing forward consumer | `prepareDocumentState_cf` and the serialization proof retain their conclusions for successes | The rejected branch is impossible under the successful-parse hypothesis |

The independent token projection does not call the parser or use the
serialization checker. Primary, secondary and named handles all count;
prefixes do not. A fresh document has a fresh directive span, so legal
later-document redeclaration remains available.

`TokenStateOk` and `tokenEvents` are unchanged. This avoids assigning
directive validity to an abstraction that erases the relevant declarations.
The global exact-source certificate must eventually supply the strengthened
token premise; that obligation is now documented at Group 7.7.

## Universal guarantees and executable controls

`TagDirectiveSoundness.lean` and `TagDirectiveSoundnessIx.lean` prove that
every document returned by the classic/indexed stream parsers and their
raw/composed source APIs has a duplicate-free explicit directive-handle list.
These quantify over all inputs and successful results, without scanner
correctness or grammar assumptions. Every decisive axiom is within
`propext`, `Classical.choice`, and `Quot.sound`.

These are guarantees about retained directives in returned documents.
A universal theorem about every directive occurrence in arbitrary source
text would additionally require the appropriate source-retention bridge.

The independent executable oracle covers 13 positive controls, four explicit
duplicate controls, and 128 pairs generated from primary/secondary/named
handles, two prefixes, and same-document versus separate-document scope.
Each is checked through six public APIs: raw, composed and comment-preserving
variants of both classic and indexed pipelines. Invalid duplicate cases must
report the dedicated error. Controls preserve a single builtin override,
distinct handles, repeated tag uses, later-document reuse, anchor rebinding,
self-reference and the intended `a\n*x` plain scalar acceptance.

The earlier duplicate case was not removed from the evidence. Its parser
expectation is corrected in the adversarial suite, and its disagreement with
the narrower serialization checker is explicitly retained in
`TokenEventExtractors.lean` alongside token-grammar rejection.

## Qualification and remaining obligations

The dedicated qualification workflow binds commit/tree identities, prints
the actual consumer and successful-result axiom profiles, builds the library
and affected proofs, and runs the adversarial suite. Exact hosted results are
recorded in SYNTHESIS and the associated Actions run.

The local adversarial executable passed **62,403/62,403 checks**. The affected
`TokenGrammarProbes` guard also passed against the updated grammar. This is
targeted library, consumer and regression qualification, not a claim that all
default census/documentation gates or FFI bindings were qualified.

This branch does not repair the source/annotated `implicitContinue` rules,
retire `scannerDrop`, repair the four dependent source-stream routes, prove
global source-to-token correspondence, or close Group 7.7. It does not claim
FFI-specific qualification or validation by a separately implemented kernel.

The natural review decision is whether this explicit requirement allocation
and paired runtime/token-contract repair should be adopted before continuing
the global proof. Existing checked proofs remain valid on their pinned trees.
