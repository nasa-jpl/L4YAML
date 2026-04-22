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

## Recommended work plan

The blueprint as written (2026-04-21) is a *description* of the
target state. This section lays out the concrete initiatives that
move the repository toward it. Two initiatives run in parallel: a
**code reorganization** driven by
[`03-code-organization.md`](03-code-organization.md), and a
**mechanical capstone verification** that cross-checks
[`04-capstones.md`](04-capstones.md) against the actual Lean
dependency graph.

### Initiative 1 — Code reorganization

Goal: make every terminology entry in
[`01-terminology.md`](01-terminology.md) findable in ≤ 2 clicks
from the top of `L4YAML/`. Four phases; each phase is one PR,
each PR ends on a green build.

**Phase 1 — Non-code moves (risk: low) ✅ done 2026-04-21**

Landed as `ad12e204` (12 top-level files into
`Spec/`, `Parser/`, `Output/`, `Config/`, `FFI/`, `Token/`,
`Scanner/`) and `573fa76e` (Phase 1b — `Schema.lean` and
`Surface.lean` moved into their folders as
`Schema/Schema.lean` / `Surface/Surface.lean` for symmetry).

- **Tooling used**: `git mv` for each file; one `sed` pass over
  `^import L4YAML.Foo$` for imports; `lake build` gate.
- **Scripts**:
  [`scripts/refactor-phase-1.sh`](../scripts/refactor-phase-1.sh),
  [`scripts/refactor-phase-1b.sh`](../scripts/refactor-phase-1b.sh)
  — reversible via commit revert.
- **Acceptance**: `lake build` passes 429/429 with only the
  expected baseline sorry warnings; smoke tests green.
- **Blast radius (observed)**: ~110 files touched across `L4YAML/`,
  `Tests/`, `L4YAML.lean`, `gen-suite-guards.py`. `L4YAML.FGM` and
  the Doc/Verso files had no direct imports of the moved modules
  and did not need updates.

**Phase 2 — Scanner split (risk: medium)**

Break monolithic [`L4YAML/Scanner/Scanner.lean`](../L4YAML/Scanner/Scanner.lean)
(~920 LoC) into the submodules referenced in
[`doc/Doc/L4YAML/Architecture.lean:140`](../doc/Doc/L4YAML/Architecture.lean#L140)
— `Scanner/Whitespace.lean`, `Scanner/Scalar.lean`,
`Scanner/Indent.lean`, `Scanner/SimpleKey.lean`,
`Scanner/Document.lean`, `Scanner/State.lean`. Keep
`Scanner/Scanner.lean` as the dispatch/umbrella.

- **Acceptance**: build green; the existing
  [`Tests/ScannerTests/`](../Tests/ScannerTests/) suite passes;
  `Architecture.lean` no longer promises files that don't exist.

**Phase 3 — Parser split (risk: medium)**

Extract `Parser/State.lean` (ParseState + helpers),
`Parser/Fuel.lean` (fuel abstractions, `4*N+4` default),
`Parser/Composition.lean` (`parseYaml`, `parseYamlRaw`, `compose`)
from [`L4YAML/Parser/TokenParser.lean`](../L4YAML/Parser/TokenParser.lean).
The mutually-recursive block stays together in `TokenParser.lean`.

- **Acceptance**: build green; `Tests/RawParseTests/`,
  `Tests/FlowTests/`, `Tests/ExplicitKeyTests/` pass.

**Phase 4 — Proofs reorganization (risk: low per-cluster)**

Move [`L4YAML/Proofs/*.lean`](../L4YAML/Proofs/) into the
subfolders outlined in
[`03-code-organization.md`](03-code-organization.md) (Scanner/,
Parser/, Schema/, Output/, RoundTrip/, Coupling/, Production/,
Foundation/). One cluster per PR; each leaves build green.

- **Ordering**: do Foundation/ first (low-level utilities, few
  inbound references), then the cluster-specific folders in
  order of coupling (Scanner/ before Parser/ before Composition.lean).
- **Acceptance**: every PR leaves `lake build` green; the
  capstone-regeneration pipeline from Initiative 2 still
  produces the same dependency graph before and after.

**Overall exit criterion for Initiative 1**: `Architecture.lean`
can be regenerated from the actual folder layout instead of
hand-maintained; no top-level `.lean` file in `L4YAML/` besides
the `L4YAML.lean` umbrella (i.e. the repo-root library entry
point that re-exports submodules) — every other file lives inside
a role-named folder.

---

### Initiative 2 — Mechanical capstone verification

Goal: compare the human-written [`04-capstones.md`](04-capstones.md)
against Lean's actual dependency DAG. Catch three classes of drift:

- **Proved capstones that depend on `sorry`** (status should be
  🚧, not ✅).
- **Theorems claimed as capstones that no one actually uses**
  (deletion or downgrade candidates).
- **Proved theorems reachable from multiple capstones that are
  missing from the blueprint** (missing capstones).

**Available tooling** (surveyed 2026-04-21):

| Tool | Repo | Toolchain | Fit |
| ---- | ---- | --------- | --- |
| `theoremgraph` | [`L4YAML.FGM`](../../L4YAML.FGM) (sibling checkout) | Lean 4.30.0-rc1 — matches L4YAML (4.30.0-rc2) closely | **Best fit now.** Already works. Supports `--list`, `--dot`, `--chain`, `--coverage`. Consumes `@[key_theorem "desc"]` attribute (from FGM). |
| `importGraph` | [`leanprover-community/import-graph`](https://github.com/leanprover-community/import-graph), pinned v4.29.0 in L4YAML's lakefile | Already imported | Module-level only; doesn't give theorem-level DAG directly but has the Lean APIs we'd need. |
| `DocVerificationBridge` | `doc-verification-bridge.ghe/DocVerificationBridge` | Lean ≤ 4.29.0 | **Not directly usable yet** — toolchain mismatch (L4YAML is on 4.30.0-rc2). Worth adopting later for the Four-Category Ontology classification. See Phase D. |
| `FGM.KeyTheorem` | [`FGM`](../../FGM) (sibling checkout) | Matches `L4YAML.FGM` | Source of the `@[key_theorem]` attribute. |
| Ad-hoc Lean script using `ConstantInfo.getUsedConstants` | — | any | Fallback if the above fall over. |

**Current coverage**:
[`L4YAML.FGM/KeyTheoremAnnotations.lean`](../../L4YAML.FGM/KeyTheoremAnnotations.lean)
tags only **6 theorems** with `@[key_theorem]`. The blueprint
lists ~45 capstones across 8 groups. The 39-theorem gap is the
immediate tagging backlog.

**Phase A — Tag all capstones (risk: low)**

Extend
[`KeyTheoremAnnotations.lean`](../../L4YAML.FGM/KeyTheoremAnnotations.lean)
with one `attribute [key_theorem "..."] ...` line per ✅ capstone
in [`04-capstones.md`](04-capstones.md). Groups 1–8.

- **Acceptance**: `lake build -p L4YAML.FGM` passes;
  `lake exe theoremgraph --list` outputs ≥ 45 theorem names
  (matches the blueprint count for ✅ rows).
- **Status source-of-truth**: the attribute text is authoritative
  for the theorem's public description; the blueprint mirrors it.

**Phase B — Diff tool (risk: low)**

Add a `scripts/check-capstones.py` (or `.sh`) that:

1. Runs `lake exe theoremgraph --list` and parses the output into
   a set of `{theorem_name, description}`.
2. Parses [`04-capstones.md`](04-capstones.md) for rows of the
   form `| # | `\`theorem_name\`` | module | status |`.
3. Prints the **set difference** in both directions:
   - **In blueprint, not in theoremgraph**: missing `@[key_theorem]`
     attribute.
   - **In theoremgraph, not in blueprint**: missing from blueprint
     or added without a blueprint entry.
4. Exit non-zero if either difference is non-empty.

- **Integration**: run in CI; `make check-blueprint` target; link
  from [`06-discipline.md`](06-discipline.md) Rule 4.
- **Acceptance**: PR adding a theorem either updates the blueprint
  and the annotation, or fails CI.

**Phase C — Sorry-reachability audit (risk: medium)**

For each capstone in
[`04-capstones.md`](04-capstones.md), use
`lake exe theoremgraph --dot <name>` to extract the dependency
DAG, then check whether any transitive dependency contains
`sorry`. Downgrade status from ✅ to 🚧 for any capstone that does.

- **Tooling choices**:
  - Simplest: run `theoremgraph --dot` per capstone, grep each
    output for dependency names that also show up in
    [`05-current-state.md`](05-current-state.md)'s sorry table.
  - Better: extend `theoremgraph` with a `--reaches-sorry` mode
    that classifies capstones as "kernel-checked" vs
    "transitively-conditional-on-sorry".
- **Acceptance**: the ✅ rows in [`04-capstones.md`](04-capstones.md)
  are the minimal set whose proofs are kernel-checked without
  `sorry` in any dependency. This catches the silent drift where
  a capstone's proof is green but a helper it depends on has
  regressed to `sorry`.

**Phase D — DocVerificationBridge integration (risk: high, defer)**

Adopt DocVerificationBridge's Four-Category Ontology once the
toolchain mismatch is resolved. Two routes:

- Wait for DocVerificationBridge to support 4.30.0+ (watch
  [`Experiments/ExperimentsCore.lean:maxSupportedVersion`](../../doc-verification-bridge.ghe/Experiments/Experiments/ExperimentsCore.lean)).
- Or: temporarily branch L4YAML to 4.29.0 for one analysis run,
  record the classification output as a baseline, then rebase
  forward. Only worth doing if the ontology gives us something
  `theoremgraph` doesn't.

The Four-Category value proposition for L4YAML: cleanly separates
**spec-side** (Grammar, Surface, Production — "mathematical
abstractions") from **impl-side** (Scanner, Parser, Emitter —
"computational operations") with **coupling theorems** as the
ontological glue. That mirrors the trust-boundary structure in
[`02-architecture.md`](02-architecture.md). So integration is
valuable long-term, but not blocking.

**Overall exit criterion for Initiative 2**: a CI job runs on
every PR, asserts that every ✅ capstone in the blueprint has
(a) a matching `@[key_theorem]` attribute, (b) a kernel-checked
proof with no `sorry` in its transitive dependency tree, and
(c) a dependency graph that's a subset of other capstones +
acknowledged infrastructure. A failing job points at which of
the three checks broke.

---

### Sequencing

Initiative 2 Phase A (tag all capstones) should go **first** —
it's low-risk, it unlocks the diff tool (Phase B) that catches
drift during Initiative 1's moves, and it validates the
[`04-capstones.md`](04-capstones.md) inventory while the blueprint
is still fresh in memory. Initiative 1 Phase 1 (folder moves) can
run in parallel once Phase A is in place, since the capstone
names don't change during folder moves.

Concrete 1-week target:

1. Day 1–2: Initiative 2 Phase A (tag the remaining ~39
   capstones).
2. Day 2: Initiative 2 Phase B (diff script, wire into CI).
3. Day 3: Run Phase B against current state; reconcile any
   mismatch between blueprint and attributes.
4. Day 4: Initiative 2 Phase C (sorry-reachability audit); update
   ✅/🚧 statuses in [`04-capstones.md`](04-capstones.md).
5. Day 5: Start Initiative 1 Phase 1.
6. Following weeks: Initiative 1 Phases 2, 3, 4 as separate PRs.

Initiative 2 Phase D (DocVerificationBridge) is deferred — revisit
once DVB supports 4.30.0 or after 1–3 land and the rest of the
blueprint is stable.
