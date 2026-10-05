# Serialization state proof package

Contributed by Heath Sanchez, Metalogic Labs ([MathGraph.org](https://mathgraph.org)).
This package was independently developed against
`nasa-jpl/L4YAML@326e4bdfd599fa74e7601bdd84632845a3353ccb` and has since been
rebased and requalified against the current `fix-a-grammar-completeness`
history.

`SerializationWellFormed.lean` specifies document-scoped events for anchor
definition, alias use, custom tag-handle declaration, and tag-handle use. The
independent checker agrees with the declarative relation for every event list.
The remaining modules relate individual source and surface witnesses to those
events and prove the corresponding scanner/parser guard, document reset, and
node-finalization properties, including bridges to the executable
`parseNodeProperties` and alias `parseNode` decisions. `ErrorCensus.lean` classifies the current
state-dependent rejection constructors. `Census.lean` contains quiet fixed executable
controls (`#guard`, no `#eval`); generalized claims are Lean proofs.

`ExecutableBoundary.lean` proves the factorization selected for the load
capstone: `parseYaml` accepts an input exactly when `scanFiltered` succeeds and
`parseStream` succeeds on the resulting token stream. Composition is total and
does not change the accepted input language.

The complete independent input-to-event-trace correspondence and the intended
`parseYaml` acceptance iff exact surface language and serialization validity
theorem are not proved here. The scanner currently performs alias-environment
checks while tokenizing, and the parser commits collection anchors only after
their contents finish. Reusing either executable stage to define the input
predicate would make the correspondence circular. Surface exactness and a
non-circular whole-input traversal therefore remain separate
grammar-completeness work.

Original handoff: [MathGraph source and evidence map](https://github.com/metalogiclabs/mathgraph/blob/72f3de86517f9516e92ce0432b380f54bb8a2021/experiments/l4yaml-serialization/HANDOFF.md).
Original verification: [MathGraph Actions run 36471883837](https://github.com/metalogiclabs/mathgraph/actions/runs/36471883837).

## Reading order

1. `SerializationWellFormed.lean` defines the event environment, declarative
   relation, executable checker, and minimum-sufficient-state results.
2. `CommitTrace.lean` and `AnchorTiming.lean` isolate the normative-YAML versus
   current-L4YAML anchor-order separator. `CommitNode` is intentionally only a
   minimal witness language for this ordering question, not a YAML AST.
3. `SourceEvents.lean` and `SurfaceEvents.lean` connect source and surface
   witnesses to the event semantics.
4. `AnchorRuntime.lean` and `RuntimeScopes.lean` attach the model to actual
   parser/scanner state transitions and document scope.
5. `ErrorCensus.lean` and `Census.lean` provide the exhaustive error-layer
   classification and fixed executable controls.
6. `ExecutableBoundary.lean` states the currently proved whole-input
   factorization and its exact residual.

## Anchor policies and the open runtime repair

`CommitTrace.yamlNodeEvents` and `SurfaceEvents.yamlCommitAnchor` model YAML
1.2.2 anchor commitment at node start, before descendants. They admit the
self-descendant example `&x [*x]`; §§3.2.1.3, 3.2.2.2, and 7.1 do not forbid it.
`CommitTrace.l4yamlNodeEvents` and `SurfaceEvents.l4yamlCommitPendingAnchor`
model the current L4YAML completion boundary, which rejects that example.
`AnchorTiming.anchor_commit_order_separator` and
`CommitTrace.yaml_current_l4yaml_anchor_separator` identify the mismatch.
The executable bridges describe **current L4YAML**, not normative YAML
conformance. The [maintainer's open repair note](https://github.com/nasa-jpl/L4YAML/pull/1#issuecomment-5984913868)
is the authority for the pending runtime change; this package does not apply it.

## Document directives and API constraints

`RuntimeScopes.documentEvents` emits `beginDocument` before a document's
preceding `%TAG` directive events and then its content. The event is a semantic
scope-start, not the lexical position of `---`. A kernel-checked separator
shows that resetting after `%TAG` loses the handle. This pins a requirement
for the still-open whole-input extraction; it does not implement that traversal.

`ErrorCensus.resource_guards_not_serialization` classifies errors; it proves
no reachability claim. `multipleDocuments` applies to `parseYamlSingle*`.
The executable factorization remains about `parseYaml`; a future
single-document API capstone would owe a separate API/resource conjunct.

## Qualification

The package is imported by `L4YAML.lean`, so default builds and
`tools/CollectStats.lean` include it. All new Lean files carry the uniform
repository header; non-capstone declarations use `lemma`, and namespaces
mirror module paths.

Run `bash scripts/check-serialization-proofs.sh` to build the focused package,
observe every `#print axioms` site freshly, validate both deliberate-sorry
signals, reject all axioms outside `propext`, `Classical.choice`, `Quot.sound`,
and pin the exact headline profiles. This gate is part of `test-coverage.yml`
on `fix-a-grammar-completeness`, `main`, and `master`, without path filters.
The existing self-hosted workflow owns the build; the separate path-scoped
hosted workflow is removed.

Local review qualification (5 October 2026 NZDT, Lean 4.34.0): the focused
package built at 37/37; the import-closed `L4YAML` target built successfully
at 241 jobs; all 45 axiom observations passed the exact-profile audit; all
four repository static gates passed. Five targeted validator mutants were
rejected. Removing the executable parser's tag guard made
`parser_tag_guard_runtime` fail; after restoring it, both the audit and full
library build passed again. No runtime source change is part of this revision.
These are local results, not a claim that upstream CI has run this revision.
