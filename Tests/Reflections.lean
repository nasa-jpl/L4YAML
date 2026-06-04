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
import Tests.Reflections.EmitProducerStrengthening
import Tests.Reflections.StoredVsProjectedRecursionEdge
import Tests.Reflections.FreeProjectionInvariant

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
* `EmitProducerStrengthening`            — Reflections 249 + 250 (the emit-producer strengthening is itself a consumer-joint-before-producer move at the emit boundary — key the assembler on a SUPERSET per-item predicate carrying the recursive deliverable (`RecEntry`, unrecoverable from the flat `FlatEntry`, witnessed by `flatentry_aa` + `not_recentry_aa`); and the recursive producer is a verbatim mirror of the flat one over ONE shared induction, only the leaf constructor swapped — `buildRecBody` is `buildFlatBody` with `RecBody.single/.cons` for `FlatBody.single/.cons`, `recbody_to_flatbody` projecting rec ⟹ flat. **R250 map layer**: the same strengthening mirrored across a SECOND axis (seq→map) — `RecPair` REUSES `RecEntry` verbatim for both key and value slots (predicate reuse), `buildRecMapBody` is `buildFlatMapBody` with the leaf swapped AND `buildRecBody` with the per-item predicate swapped (the two-axis mirror), and `recpair_len_floor` (`3 ≤ length`) is the load-bearing map-side scaffolding the seq body lacks — keep it, mirror the same-axis parent not the other-axis sibling)
* `ProducerDualOfConsumer`               — Reflections 245 + 246 + 247 + 248 (the producer's per-level assembler is the constructive dual of the consumer joint — same positional bridge, opposite direction, constructor vs. eliminator; its symmetric MIRROR transports the plumbing verbatim but sheds at the constructor exactly the field the additive parallel type projects instead of stores: seq `SEntry.seq` stores `WB`, map `MEntry.map` omits-and-projects it; the BUNDLE assembler `bundleLocatedSeq`/`bundleLocatedMap` lifts the field-level dual to the consumer's bundled deliverable `SLocated`/`MLocated` — only the recursive `entry` field is non-trivial, the rest are window-guard pass-throughs, and the map bundle threads one extra stored primitive `keyF` the entry producer never supplies; and R248 — that storage asymmetry is SCALE-FREE: the same projected-vs-stored mechanism SHRINKS the entry constructor and GROWS the bundle, opposite signs, witnessed by `wb_recovered` (post-hoc projection at the shrunk constructor) vs `mlocated_key` (the grown-in stored field projected back out))
* `FreeProjectionInvariant`              — Reflections 253 + 254 (a consumer-bundle field that is definitionally a CONJUNCT of a property the recursive deliverable already PROJECTS to is a FREE field, not a threaded obligation — read the deliverable's projection family before deciding what the recursion threads: `WB l := balance l = 0 ∧ ∀ i, 0 ≤ balance (l.take i)`, the recursive `Rec` projects to `WB` (`Rec.toWB`, `wrap` case = `WB_wrap`), so the bundle `Located`'s `dyck` field is `(Rec.toWB h).2` for free — `located_of_rec` takes only the `wt : WT` hypothesis and no `h_dyck`; the CONTRAST is `WT` (typed bracket matching), which `Rec` does NOT project to — `rec_mismatched : Rec [os,a,cm]` holds yet `not_wt_mismatched : ¬ WT [os,a,cm]`, so `dyck_mismatched_free` is still derivable but no `Located [os,a,cm]` is — the R244 stored-vs-projected split surfacing at the locate's invariant SET rather than a constructor's fields. **R254**: the one invariant with no local projection (`WT`) is recovered all the same — *non-locally*, from the OUTER window's `WT` via a subrange interface `WTsub` (the toy of `WellTyped_subrange`) whose two side conditions are the window's *free* balance + Dyck off `Rec.toWB`; the outer assembler `located_of_rec_outer` (toy of `seqLocated_of_recseqbody_outer`) threads ONE outer `WT`, recovers the window's `wt` through `WTsub`, and takes no per-window `WT` and no `dyck` — only the structural `Rec`; `wtsub_concrete`/`located_window_via_outer` witness it on `{ { a } } ⊃ { a }`, so Dyck is free LOCALLY and `WT` is free NON-LOCALLY, neither threaded per window)
* `StoredVsProjectedRecursionEdge`       — Reflections 251 + 252 (a recursive-deliverable inductive's STORAGE choices set the PRODUCER's recursion graph — `Entry.seq` stores the recursive `Body interior` so the producer's `seq` case recurses (`buildEntry` → `buildBody`), while `Entry.map` projects only the flat `bal interior = 0` so the producer's `map` case is a LEAF (`buildEntry` → `bal_emitList`, never `buildBody`), severing the recursion edge; witnessed by `mapLeaf` (a flat leaf builder for the projecting member, with no `seqLeaf` counterpart) and by `built_map_empty : Entry [om,cm]` (the projecting member accepts an interior with NO `Body`, even though `not_body_nil` shows `Body []` is uninhabited and the storing member therefore needs a dedicated `seqEmpty`); the producer targeting only projecting members is strictly smaller and dependency-light — a single self-contained induction — and in a producer family the projection severs the cross-producer edge, ordering the family. **R252**: the *dependent* member's IH is dead — `KeyEntry e := Entry e ∧ bal e = 0` (a saved-key-style twin deliverable) is built by the *non-recursive* `buildKeyEntry := ⟨buildEntry v, bal_emit v⟩`, which routes the recursive `Entry` part to the BASE sibling `buildEntry` and the extra flat fact to `bal_emit`, never calling itself — so the base carries the family's only live self-recursion and each dependent consumes it as a black box; `key_projects_to_entry` recovers the base `Entry` back out)
-/
