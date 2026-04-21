# L4YAML Blueprint

A top-down specification of L4YAML: what it **is**, what it **guarantees**,
and how those guarantees decompose into modules and theorems.

This blueprint was introduced on 2026-04-21 after a bottom-up proof
effort (`parser_fuel_mono_succ` and related `_mono_zero` theorems)
exposed that the repository was accumulating theorems without a
top-down anchor. Specifically:

- `parseBlockSequence_mono_zero` (and siblings) turned out to be
  **unsound as stated** — the statement was written by analogy with
  flow-sequence monotonicity without reference to a caller's need.
- The enclosing `parser_fuel_mono_succ` machinery (~500 LoC, 24
  sub-theorems, 28 `sorry`s) was built to unlock **one** downstream
  call site, and its two documented consumer wrappers
  (`parseNode_fuel_mono_succ`, `parseSinglePairMapping_fuel_mono_succ`)
  have **zero** callers outside their own definitions.
- The companion adversarial-instantiation suite (1,827 lines, 7
  priorities) does **not** exercise any of the 24 fuel-monotonicity
  parts; its "Priority 7 audit" only covers a lifted helper.

The purpose of this blueprint is to make the proof effort
**goal-driven** rather than **accumulation-driven**: every lemma
should justify itself by traceable use in a capstone theorem, and
every capstone theorem should be declared *before* its proof is
attempted.

## How to read this blueprint

Read in order on first visit:

1. [`01-terminology.md`](01-terminology.md) — what the domain words
   mean in L4YAML. Establishes shared vocabulary.
2. [`02-architecture.md`](02-architecture.md) — the pipeline, data
   flow, and module boundaries.
3. [`03-code-organization.md`](03-code-organization.md) — proposed
   folder layout (code first; proofs to follow).
4. [`04-capstones.md`](04-capstones.md) — the complete list of
   capstone theorems, grouped by guarantee category, with current
   status (✅ proved / ⏳ planned / 🚧 partial / ❓ unsound /
   🗑 deletion candidate).
5. [`05-current-state.md`](05-current-state.md) — honest accounting
   of where we are: sorry count, deletion candidates, claims that
   need reconciling against reality (`Overview.lean` says "Zero
   `sorry`" — that is aspirational; actual grep shows ~100).
6. [`06-discipline.md`](06-discipline.md) — the discipline going
   forward: blueprint-first theorem proposals, adversarial
   instantiation before proof, sorry policy.

## Relationship to existing documentation

This blueprint **does not replace** the Verso-based manual at
[`doc/Doc/L4YAML/`](../doc/Doc/L4YAML/). That manual is a
published-audience document. This blueprint is an **internal
working document** that drives the proof backlog. Eventually
(per point (b) of the pivot conversation), the blueprint may be
refactored using `verso-blueprint` so that capstones can be
cross-linked with their Lean definitions directly; until then,
markdown is the medium.

## Relationship to existing plan docs

[`../PARSER_WELLBEHAVED_PLAN.md`](../PARSER_WELLBEHAVED_PLAN.md),
[`../EMITTER_SCANNABILITY_PLAN.md`](../EMITTER_SCANNABILITY_PLAN.md),
and similar plan documents at the repository root are **tactical**
plans tied to specific proof files. The blueprint is **strategic**:
it says *which properties matter* and *why*, from which the tactical
plans derive. When a tactical plan's premise no longer aligns with
the blueprint (as happened with `parser_fuel_mono_succ`), the
blueprint wins.

## Contributor workflow

Before proposing a new theorem:

1. Locate (or add) a capstone in [`04-capstones.md`](04-capstones.md)
   that needs this theorem as a dependency.
2. Add the theorem's statement to the relevant module's section in
   that file *before* attempting the proof.
3. Add an adversarial-instantiation test that would refute the
   statement if false, *before* attempting the proof.
4. Prove it; update status in [`05-current-state.md`](05-current-state.md).

This sequence catches statement errors at step 3 (cheap) rather
than step 4 (expensive).
