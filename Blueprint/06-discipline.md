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
  If the helper proof is hard, the capstone's plan doc (the open
  ones today:
  [`GRAMMAR_COMPLETENESS_PLAN.md`](../GRAMMAR_COMPLETENESS_PLAN.md),
  [`YAML_MERGE.md`](../YAML_MERGE.md)) should list the helper as a
  dependency, and the helper should be promoted to capstone-track
  status before being `sorry`'d.
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

The repository keeps tactical plan and rationale docs at the root
(today: `GRAMMAR_COMPLETENESS_PLAN.md`, `YAML_MERGE.md`,
`SPEC-GAP-ANALYSIS.md`;
see [`DOCS.md`](../DOCS.md) for the index). These are *tactical* —
tied to concrete files. Closed campaign logs are **deleted** once
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
  closure.
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
