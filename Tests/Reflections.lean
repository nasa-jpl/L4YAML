import Tests.Reflections.ProducerGuardedTrap
import Tests.Reflections.ConverseForwardAsymmetry
import Tests.Reflections.ReductionByImport
import Tests.Reflections.ParametricAssemblerExtraction
import Tests.Reflections.ConvergentReduction
import Tests.Reflections.RecursiveDeliverableProjectToFlat
import Tests.Reflections.ConsumerJointBeforeProducer
import Tests.Reflections.AdditiveParallelType

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
-/
