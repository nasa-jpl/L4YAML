# Serialization state proof package

Contributed by Heath Sanchez, Metalogic Labs ([MathGraph.org](https://mathgraph.org)).
This package was independently developed against
`nasa-jpl/L4YAML@326e4bdfd599fa74e7601bdd84632845a3353ccb`.

`SerializationWellFormed.lean` specifies document-scoped events for anchor
definition, alias use, custom tag-handle declaration, and tag-handle use. The
independent checker agrees with the declarative relation for every event list.
The remaining modules relate individual source and surface witnesses to those
events and prove the corresponding scanner/parser guard, document reset, and
node-finalization properties. `ErrorCensus.lean` classifies the current
state-dependent rejection constructors. `Census.lean` contains fixed executable
controls; generalized claims are Lean proofs.

The complete input-to-event-trace correspondence and the intended
`parseYaml` acceptance iff exact surface language and serialization validity
theorem are not proved here. Surface exactness remains part of the separate
grammar-completeness work.

Original handoff: [MathGraph source and evidence map](https://github.com/metalogiclabs/mathgraph/blob/72f3de86517f9516e92ce0432b380f54bb8a2021/experiments/l4yaml-serialization/HANDOFF.md).
Original verification: [MathGraph Actions run 36471883837](https://github.com/metalogiclabs/mathgraph/actions/runs/36471883837).
