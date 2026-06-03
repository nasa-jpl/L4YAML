import Tests.Reflections.ProducerGuardedTrap
import Tests.Reflections.ConverseForwardAsymmetry
import Tests.Reflections.ReductionByImport
import Tests.Reflections.ParametricAssemblerExtraction
import Tests.Reflections.ConvergentReduction
import Tests.Reflections.RecursiveDeliverableProjectToFlat
import Tests.Reflections.ConsumerJointBeforeProducer
import Tests.Reflections.AdditiveParallelType
import Tests.Reflections.UniversalPackagingJoint
import Tests.Reflections.ProjectionFamilyCompletion
import Tests.Reflections.ProducerDualOfConsumer

/-!
# Reflections — runnable proof-engineering demonstrations

This library collects the self-contained (core Lean, no `L4YAML` import) runnable
illustrations of the proof-engineering principles documented as numbered *Reflections* in
`Blueprint/08-initiative-4-intrinsic-foundations.md`.  They are kept separate from the
behavioural L4YAML test suites (parsing/emitting/round-trip) because they assert *methodology*,
not library behaviour: each is a toy model whose `#guard`/`#guard_msgs`/`#eval`/`by decide`
checks fail the build if the principle's positive/negative witnesses ever drift.

Each module names the Blueprint Reflection it illustrates:
* `ProducerGuardedTrap`                  — Reflection 218 (the producer-guarded-quantifier trap)
* `ConverseForwardAsymmetry`             — Reflection 219 (converse/forward invariant asymmetry)
* `ReductionByImport`                    — Reflection 225 (reduction by import — retype, not shrink)
* `ParametricAssemblerExtraction`        — Reflections 226 + 228 (parametric assembler extraction)
* `ConvergentReduction`                  — Reflection 227 (convergence corollary of reduction-by-import)
* `RecursiveDeliverableProjectToFlat`    — Reflections 234 + 235 (recursive deliverable, project-to-flat-first; single-level descent step)
* `ConsumerJointBeforeProducer`          — Reflection 231 (+ 232 / 237 / 241) (build the consumer joint before the producer; faithful mirror)
* `AdditiveParallelType`                 — Reflection 242 (land a forced deliverable refinement as an additive parallel type, never a shared edit; a dedicated type internalizes the guard)
* `UniversalPackagingJoint`              — Reflection 243 (universal packaging is its own consumer joint — the field/joint hypothesis gap IS the producer's deliverable type; build the assembler before the producer)
* `ProjectionFamilyCompletion`           — Reflection 244 (complete a newly-added deliverable type's projection family before the producer walks it — the omitted projection is the locate's navigation invariant, a verbatim mirror of the sibling's; projections track STORED fields, not desired properties)
* `ProducerDualOfConsumer`               — Reflections 245 + 246 + 247 + 248 (the producer's per-level assembler is the constructive dual of the consumer joint — same positional bridge, opposite direction, constructor vs. eliminator; its symmetric MIRROR transports the plumbing verbatim but sheds at the constructor exactly the field the additive parallel type projects instead of stores: seq `SEntry.seq` stores `WB`, map `MEntry.map` omits-and-projects it; the BUNDLE assembler `bundleLocatedSeq`/`bundleLocatedMap` lifts the field-level dual to the consumer's bundled deliverable `SLocated`/`MLocated` — only the recursive `entry` field is non-trivial, the rest are window-guard pass-throughs, and the map bundle threads one extra stored primitive `keyF` the entry producer never supplies; and R248 — that storage asymmetry is SCALE-FREE: the same projected-vs-stored mechanism SHRINKS the entry constructor and GROWS the bundle, opposite signs, witnessed by `wb_recovered` (post-hoc projection at the shrunk constructor) vs `mlocated_key` (the grown-in stored field projected back out))
-/
