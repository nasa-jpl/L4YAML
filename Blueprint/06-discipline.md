# Discipline

The methodology going forward. These rules exist because we learned
(on 2026-04-21) that without them, the proof corpus accumulates
dead infrastructure and false theorems. Enforce them.

## Rule 1 — No new theorem without a traceable capstone

Every new top-level proof (`lemma` or `theorem` — see Rule 7 for
which keyword) must be **justified by traceable use**
(transitively) in a capstone listed in
[`04-capstones.md`](04-capstones.md). Before proposing a new
one:

1. **Find the capstone** it's supposed to feed. Name it. Write the
   intended chain: "proves *X* → used by *Y* → used by capstone *Z*."
2. If there is no capstone it feeds, **add a capstone first**, and
   justify *that* with a user-visible guarantee.
3. If neither can be done, the theorem is scaffolding for scaffolding.
   **Don't add it.**

Reason: `parser_fuel_mono_succ` was added without this check. Its
~500 LoC and 28 `sorry`s exist to support two wrappers, both of
which have zero external callers. That's a ~1,000-hour write-off.

## Rule 2 — Adversarial instantiation before proof

For every **new** theorem or lemma, add an adversarial-instantiation test
that would **refute** it if false, **before** attempting the proof.

- The test lives in
  [`Tests/AdversarialInstantiation.lean`](../Tests/AdversarialInstantiation.lean)
  under the priority bucket matching the capstone it feeds.
- The test must exercise the theorem on inputs that (a) cover
  the `∀` scope, (b) include boundary cases — `fuel = 0, 1, 2`,
  `items.size = 0, 1`, empty and non-empty values, all token types.
- The test reports `failed-hypothesis` (vacuous arms),
  `theorem-holds` (both sides agree), and `theorem-refuted` (a
  concrete `(hypothesis, conclusion)` pair where the conclusion
  failed). `theorem-refuted` is a **hard build failure**.

Reason: a 5-minute refutation check would have caught
`parseBlockSequence_mono_zero` before days of analysis. The
counterexample is `ps.advance.peek? = some .blockEntry` with two
consecutive block entries — a trivial input the test suite would
generate by brute-force enumeration.

### What an adversarial test looks like

Example sketch for `ParseBlockSequence_succ 0`:

```lean
private def testParseBlockSequenceSucc0 (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "ParseBlockSequence_succ 0"
  for inputs in adversarialBlockSeqInputs do
    -- adversarialBlockSeqInputs should enumerate short token arrays
    -- with a blockSequenceStart prefix: empty tail, one blockEntry,
    -- two blockEntries, blockEntry+scalar, blockEntry+blockEnd, etc.
    let ps : ParseState := { tokens := inputs, pos := 0 }
    let r1 := parseBlockSequence ps 1
    let r2 := parseBlockSequence ps 2
    match r1, r2 with
    | .ok v1, .ok v2 =>
      check state s!"succ 0: fuel=1 ok and fuel=2 ok with same result"
        (v1 == v2)
    | .ok _, .error _ =>
      check state s!"succ 0: fuel=1 ok but fuel=2 error — REFUTED"
        false
    | .error _, _ => pure ()  -- vacuous hypothesis
```

This would have printed "REFUTED" on the very first two-blockEntry
input.

## Rule 3 — Sorry policy

The library is `sorry`-free (since 2026-07-04), and this is
**CI-enforced**, not aspirational:
[`test-coverage.yml`](../.github/workflows/test-coverage.yml) runs a
kernel-accurate assertion (via `collect-stats`, which walks the
compiled environment with `Lean.collectAxioms`) that there are
**0 theorems with transitive `sorry` and 0 custom axioms**, and
[`L4YAML/Capstones.lean`](../L4YAML/Capstones.lean)'s
`#assert_capstone_axioms` independently hard-fails the build if any
capstone acquires a `sorryAx` dependency. (The lone `sorry` under
`Tests/` is the deliberate demonstration in
`Tests/Reflections/IllusorySorryFree.lean`, outside the library
environment.) Consequences:

- A `sorry` **cannot land on the default branch** — it is a build
  failure. A `sorry` may exist only on a WIP branch, and only
  against a declaration listed in
  [`04-capstones.md`](04-capstones.md); it must be discharged before
  merge.
- A `sorry` in a **helper lemma** (not a capstone) is not allowed.
  If the helper proof is hard, the capstone's plan (the open ones
  today live in
  [`DOCS.md` § The Plan](../DOCS.md#the-plan-open-work): the
  grammar-completeness plan and the merge-semantics plan) should list
  the helper as a dependency, and the helper should be promoted to
  capstone-track status before being `sorry`'d.
- A `sorry` in any declaration that has **0 external callers** is an
  immediate deletion candidate, not a proof TODO.

Reason: `sorry`s in unused helpers are silent proof-debt — they
don't break the build locally; they just accumulate. The 2026-07-04
closure (see [`04-capstones.md`](04-capstones.md), the proof-status
SSOT) converted this policy from a target into an enforced
invariant.

## Rule 4 — One source of truth per claim

For every public-facing metric or guarantee:

- **One primary location** declares it (source of truth).
- **Everywhere else** links to or quotes that location, and says so
  explicitly.

Examples:

- Sorry count: primary = [`04-capstones.md`](04-capstones.md) (its
  Status snapshot; `sorry`-free since 2026-07-04, CI-asserted per
  Rule 3). The Verso manual computes its own count
  live from [`Stats.lean`](../doc/Doc/L4YAML/Stats.lean); the two
  should agree.
- Capstone list: primary = [`04-capstones.md`](04-capstones.md)
  (prose), held in sync with two mirrors:
  - **In-repo machine gate**: the `@[capstone]` attribute on each
    capstone declaration, with the tagged set and per-capstone axiom
    profiles pinned by `#guard_msgs` in
    [`L4YAML/Capstones.lean`](../L4YAML/Capstones.lean), plus
    [`scripts/capstones.txt`](../scripts/capstones.txt) driving
    [`scripts/check-theorem-keyword.sh`](../scripts/check-theorem-keyword.sh)
    (Rule 7).
  - **External mirror**:
    [`L4YAML.FGM/KeyTheoremCatalogue.lean`](../../L4YAML.FGM/KeyTheoremCatalogue.lean)
    for consumption by compiled tooling. **Gate**: `lake exe check-capstones`
    (run in L4YAML.FGM CI via
    [`generate-graphs.yml`](../../L4YAML.FGM/.github/workflows/generate-graphs.yml))
    fails the PR if catalogue and blueprint drift.

  So a PR that adds, renames, or retires a capstone must update all
  of: [`04-capstones.md`](04-capstones.md), the `@[capstone]` tag +
  the `Capstones.lean` pins, `scripts/capstones.txt`, and the FGM
  catalogue — `Verification.lean` should continue to either link or
  mirror, not diverge.
- Architecture pipeline: primary =
  [`02-architecture.md`](02-architecture.md). `Architecture.lean`
  should mirror.

Reason: we caught one discrepancy already (Overview's "Zero sorry"
vs. ~100 actual). Others probably exist.

## Rule 5 — When a plan conflicts with the blueprint, the blueprint wins

The repository keeps its tactical plans and rationale consolidated in
[`DOCS.md`](../DOCS.md) (since 2026-08-01: topic sections plus
"The Plan" collecting all open work — grammar completeness, merge
semantics, the security backlog). These are
*tactical* — tied to concrete files. Closed campaign logs are
**deleted** once
their surviving content is folded into this Blueprint (history stays
in git; the 2026-08-01 purge is the precedent).

If a plan calls for a theorem that the blueprint says is
unreachable from a capstone (Rule 1), **stop the plan**, not the
blueprint. Update the plan document with an audit-note ending; if
the blueprint is wrong, argue to change the blueprint first.

Reason: the retired `PARSER_WELLBEHAVED_PLAN.md` (deleted
2026-08-01, in git history) Step 1 called for 24 proofs, 6 of which
were unsound. The plan was authoritative at the time; had the
blueprint existed and demanded justification-by-capstone, the
unsoundness would have surfaced at plan time instead of mid-proof.

## Rule 6 — Verify before recommending from memory

(This is a Claude-specific rule; included here because it applies
to the user's AI-assisted workflow.)

When a memory or past plan says "theorem X exists at line Y doing
Z", before recommending action based on it: `grep` for it. If the
memory's claim doesn't match the current file, trust the file.

Reason: the memory system is frozen at write time. A plan from
2026-04-19 that says "Part 11 was audited via Priority 7" was only
approximately true (it referred to the helper, not the main
theorem). A verifying grep would have caught this.

## Rule 7 — The `theorem` keyword is reserved for capstones

Since 2026-07-31 (commit `ae33568f`), the `theorem` keyword is a
**marker**: it may be used only by the `@[capstone]`-tagged
blueprint capstones (currently 25 declarations; see
[`04-capstones.md`](04-capstones.md)). **Every other proof is
written with `lemma`** (~4,975 declarations), a synonym command
provided by [`L4YAML/Init.lean`](../L4YAML/Init.lean), the project
prelude imported by every library module. So `grep '^theorem '`
over `L4YAML/` now answers "what does the library guarantee?" —
the keyword itself carries Rule 1's traceability.

- **Whitelist**: [`scripts/capstones.txt`](../scripts/capstones.txt)
  — 19 named `file:decl` entries (some short names appear twice,
  once for the classic and once for the indexed twin) plus the
  `SIndent_*`/`GChar_*` wildcard families.
- **Gates**:
  [`scripts/check-theorem-keyword.sh`](../scripts/check-theorem-keyword.sh)
  fails CI on any non-whitelisted `theorem` in `L4YAML/`;
  [`scripts/check-import-closure.sh`](../scripts/check-import-closure.sh)
  ensures no module dodges the gates by dropping out of the import
  closure; and
  [`scripts/check-reflection-index.sh`](../scripts/check-reflection-index.sh)
  holds the *narrative* half of `Tests/Reflections.lean` to its own
  claims — every bullet listed by the sub-theme it sits under, every
  listed number backed by a bullet, no number claimed twice, blocks
  ascending. Added 2026-08-11: the import gate proves a demo *builds*,
  which says nothing about whether a reader can find it, and twelve
  reflections had drifted into a sub-theme whose list never mentioned
  them while a thirteenth sat between two headings, belonging to
  neither.
- **Registry**: the `@[capstone]`-tagged set and each capstone's
  axiom profile (18 `pure`, 7 `native`) are pinned by `#guard_msgs`
  in [`L4YAML/Capstones.lean`](../L4YAML/Capstones.lean) — silently
  gaining or losing a capstone, or a capstone silently acquiring a
  `native_decide` dependency, fails the build.

Promoting a proof to `theorem` therefore requires the full capstone
path: justify it under Rule 1, add it to
[`04-capstones.md`](04-capstones.md), tag it `@[capstone]`, and
update the `Capstones.lean` pins + `scripts/capstones.txt` (and the
FGM catalogue, per Rule 4).

## Rule 8 — No ghost index on the accumulation invariant

Added 2026-10-21 (DOCS item 331), when row 12's two open forks (items 320
and 325) turned out to be one question. Every index a carrier of the
accumulation invariant introduces — a parameter, a constructor field, a
quantifier inside a field's statement — must be one of three things:

1. **a surface position** (`SurfPos`, or a predicate on positions): the
   correspondence is the theorem;
2. **an obligation** (a `Prop`: a continuation, a route, a fact about the
   state): the induction hypothesis;
3. **a projection of the scanner state**, `f sc` for the `ScannerState`
   the carrier is about — the kinds index is `sc.flowStack` (9b(i)), the
   frame lists are `sc.indents` above a floor, the frame tail is
   `FrameTail.ofToken` of the last real token.

When a proof needs a fact that none of the three gives, **the scanner is
incomplete**: add the field to `ScannerState` (and its indexed twin), make
the scanner *read* it, and prove the projection — as `explicitKeyCol`
(item 48), `explicitKeyStack` (item 98), `docStartLine` (item 299) and
`definedAnchors` were added. What the rule forbids is the fourth option:
a proof-side datum or disjunct carried beside the data the scanner
already holds — a `List Nat` that mirrors the indent stack without its
kinds, an `Option ScannerState` snapshot of the open-time state, a
`∨ <stack-shape fact>` on a park's alternative. Such a datum needs a
transport lemma per step (the `DispatchPrice`/`ParkGapWidth` ladders are
what that costs), and it hides a missing field: the scalar `?` register
was one (item 326 found it dead under an open outer `?`; item 331 found
the over-refusal that follows, `?⏎  ? y⏎  : z⏎: w: x`).

- **Gate**:
  [`Tests/Guards/Proofs/GhostIndexCensus.lean`](../Tests/Guards/Proofs/GhostIndexCensus.lean)
  walks the carriers' telescopes, constructor fields and nested `∃`/`∀`
  binders and pins, per carrier, the binders by class — `surface`, `state`,
  `prop`, `scalar`, `snapshot` (an `Option ScannerState`), `ghost` (a
  `List Nat`, an `Array Bool`, a `FrameTail`) — and the full `ghost` +
  `snapshot` list. The carriers are read off the environment (every
  `Prop`-valued declaration of `StreamAccum`, plus `ScannerSurfCorr`), so a
  new predicate cannot escape it. Baseline at item 331: 52 carriers, 9
  snapshot indices, 73 ghost binders. **The list may only shrink**: a row leaves it when its
  carrier is re-indexed by a projection or a new field; a re-pin that adds
  a row is a Rule 8 violation and the PR must say which of the three
  classes the new index belongs to instead.
- **Not covered**: `scalar` binders (`Nat`, `Bool`, `Char`, contexts, token
  arrays). Most are grammar parameters (`n`, `c`) or pinned to the state by
  an inequality (`n ≤ minContentIndentOf sc`); the census lists their counts
  so a growth there is visible, but does not name them.

## Rule 9 — Scripts are written in Lean, not Python

Added 2026-11-01 (owner's ruling). Every script this repository runs —
a CI gate, a pricing or flip instrument, a census reader, a docs
navigator, a report generator — is a Lean program (a `lean_exe` under
`Scripts/`, or a Lake `script` in `lakefile.lean`), invoked through
`lake exe <name>` / `lake run <name>`. The shell wrappers in `scripts/*.sh`
may stay as entry points and may compose Lean executables with `git`,
`lake` and coreutils; they may not call `python3`.

Why. The instruments are the campaign's memory (Rule 6, §9, §10): a
number an item quotes is only as reliable as the program that re-derives
it, and today those programs live in a language the build never checks,
with their own re-implementations of what Lean already knows — which
line is a declaration opener (`flip_census.py`'s `OPENER` regex), which
lines are imports (the `public import`/`meta import` regression that read
the migrated library as empty on 2026-10-17), what a module's dependents
are (`drop_sweep.py` and `DropDependents.lean` are two implementations
of one walk). A Lean script reads the environment instead of grepping
its text, elaborates under the same toolchain the proofs use, and is
built and type-checked by `lake build` like everything else.

What the rule requires:

1. **No new `scripts/*.py`.** A new instrument is a Lean program; a
   change to an existing Python instrument that is more than a one-line
   fix converts it first (see the plan in
   [`09-scripts-in-lean.md`](09-scripts-in-lean.md)).
2. **Read the environment, not the text, when the question is about
   declarations** — openers, imports, dependents, binders, axioms. Text
   reading is for what Lean does not see: docstrings (`GateVocabulary`),
   `DOCS.md`, build logs.
3. **An instrument that edits library source** (a flip) states what it
   patches, builds, and restores the bytes it read, printing both
   checksums — the protocol `.devin/skills/l4yaml-price-instruments`
   describes, now enforced by one shared `Scripts.Flip` library rather
   than re-typed per script.
4. **Python stays where it is the product**, not a script: the `l4yaml`
   package under `python/` and its tests (`python/tests/`,
   `Tests/test_python_ffi.py`) are the FFI binding this project ships.
5. **Third-party tooling with no Lean counterpart** (PDF rasterisation,
   the docker-driven processor matrix) is called as an external
   program from a Lean or shell driver; the logic around it — what to
   compare, how to score, what to write — is Lean. Exceptions are
   listed, with their reason, in the plan's §4; an unlisted `.py` is a
   Rule 9 violation.

- **Gate**: `scripts/check-scripts-lean.sh` (plan §3, phase 0) fails
  when a `.py` exists under `scripts/` that is not on the plan's
  conversion ledger, or when a `.sh` or workflow step invokes `python3`
  outside the ledger's listed exceptions. The ledger may only shrink.

## Checklist before merging a new lemma or theorem

Contributor self-check:

- [ ] The theorem's capstone is identified and named in the PR.
- [ ] The capstone is listed in
      [`04-capstones.md`](04-capstones.md) (or this PR adds it).
- [ ] An adversarial-instantiation test exists in
      [`Tests/AdversarialInstantiation.lean`](../Tests/AdversarialInstantiation.lean)
      that would refute the theorem if false.
- [ ] The test runs under `lake test` and reports no refutations.
- [ ] The proof is complete (no `sorry` — Rule 3's CI gate rejects
      any `sorry` on the default branch); work in progress stays on
      a WIP branch, listed in [`04-capstones.md`](04-capstones.md)
      with a tracking issue.
- [ ] The declaration uses `lemma` unless it is `@[capstone]`-tagged
      (Rule 7).
- [ ] No new declaration has zero external callers after this PR.

## Process for retiring theorems

When deleting a theorem (per the "Decomposition: what is *not* a
capstone" list in [`04-capstones.md`](04-capstones.md)):

1. Grep confirms **zero external callers**. For a whole subtree, the
   stronger machine check is the `unified-dep-table` sweep that
   justified the `parser_fuel_mono_succ` deletion — reproducible as:

   ```sh
   # From the repo root, with DocVerificationBridge built on a
   # matching toolchain:
   lake env /path/to/DocVerificationBridge/.lake/build/bin/unified-dep-table \
     fresh --namespace L4YAML.Proofs.ParserWellBehaved \
           --external-only --proof-dep-workers 4 \
           --output dep-parser-wellbehaved.md \
           L4YAML
   ```

   (`--external-only` lists out-of-namespace callers; an empty table
   is the deletion licence.)
2. PR description states the removal and links to the blueprint
   rationale ("per Blueprint/04-capstones.md, Decomposition: what
   is *not* a capstone").
3. If the theorem appeared in `Verification.lean` or any other
   published doc, remove the reference in the same PR.
4. If a downstream memory referenced the theorem, flag it for
   invalidation (the user can clear stale memory entries manually).

Deleting scaffolding is proof-work. Count it as such.
