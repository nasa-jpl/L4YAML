# Discipline

The methodology going forward. These rules exist because we learned
(on 2026-04-21) that without them, the proof corpus accumulates
dead infrastructure and false theorems. Enforce them.

## Rule 1 — No new theorem without a traceable capstone

Every new top-level theorem must be **justified by traceable use**
(transitively) in a capstone listed in
[`04-capstones.md`](04-capstones.md). Before proposing a new
theorem:

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

For every **new** theorem, add an adversarial-instantiation test
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

The current codebase has ~90–100 active `sorry`s. The policy going
forward:

- A **new `sorry`** is allowed only if the theorem is listed in
  [`04-capstones.md`](04-capstones.md) with status 🚧 or ⏳ **and** a
  WIP branch is open against it.
- A `sorry` in a **helper lemma** (not a capstone) is not allowed.
  If the helper proof is hard, the capstone's plan doc (e.g.
  [`PARSER_WELLBEHAVED_PLAN.md`](../PARSER_WELLBEHAVED_PLAN.md))
  should list the helper as a dependency, and the helper should be
  promoted to capstone-track status before being `sorry`'d.
- A `sorry` in any theorem that has **0 external callers** is an
  immediate deletion candidate, not a proof TODO.

Reason: `sorry`s in unused helpers are silent proof-debt. They
don't break builds; they don't surface in CI; they just accumulate.

## Rule 4 — One source of truth per claim

For every public-facing metric or guarantee:

- **One primary location** declares it (source of truth).
- **Everywhere else** links to or quotes that location, and says so
  explicitly.

Examples:

- Sorry count: primary = [`05-current-state.md`](05-current-state.md).
  Overview.lean should either link there or include the same number.
- Capstone list: primary = [`04-capstones.md`](04-capstones.md),
  mirrored by
  [`L4YAML.FGM/KeyTheoremCatalogue.lean`](../../L4YAML.FGM/KeyTheoremCatalogue.lean)
  for consumption by compiled tooling. **Gate**: `lake exe check-capstones`
  (run in L4YAML.FGM CI via
  [`generate-graphs.yml`](../../L4YAML.FGM/.github/workflows/generate-graphs.yml))
  fails the PR if the two drift. So a PR that adds, renames, or
  retires a ✅ capstone must update both places — `Verification.lean`
  should continue to either link or mirror, not diverge.
- Architecture pipeline: primary =
  [`02-architecture.md`](02-architecture.md). `Architecture.lean`
  should mirror.

Reason: we caught one discrepancy already (Overview's "Zero sorry"
vs. ~100 actual). Others probably exist.

## Rule 5 — When a plan conflicts with the blueprint, the blueprint wins

The repository has several plan docs at the root
(`PARSER_WELLBEHAVED_PLAN.md`, `EMITTER_SCANNABILITY_PLAN.md`,
`SPEC-GAP-ANALYSIS.md`, `DUPLICATE_KEYS.md`, etc.). These are
*tactical* — tied to concrete files.

If a plan calls for a theorem that the blueprint says is
unreachable from a capstone (Rule 1), **stop the plan**, not the
blueprint. Update the plan document with an audit-note ending; if
the blueprint is wrong, argue to change the blueprint first.

Reason: `PARSER_WELLBEHAVED_PLAN.md` Step 1 called for 24 proofs, 6
of which are unsound. The plan was authoritative at the time; had
the blueprint existed and demanded justification-by-capstone, the
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

## Checklist before merging a new theorem

Contributor self-check:

- [ ] The theorem's capstone is identified and named in the PR.
- [ ] The capstone is listed in
      [`04-capstones.md`](04-capstones.md) (or this PR adds it).
- [ ] An adversarial-instantiation test exists in
      [`Tests/AdversarialInstantiation.lean`](../Tests/AdversarialInstantiation.lean)
      that would refute the theorem if false.
- [ ] The test runs under `lake test` and reports no refutations.
- [ ] The theorem is proved (no `sorry`), or is explicitly listed
      as 🚧/⏳ in [`04-capstones.md`](04-capstones.md) with a
      tracking issue.
- [ ] No new theorem has zero external callers after this PR.

## Process for retiring theorems

When deleting a theorem (per deletion candidates in
[`05-current-state.md`](05-current-state.md)):

1. Grep confirms **zero external callers**.
2. PR description states the removal and links to the blueprint
   rationale ("per Blueprint/05-current-state.md, Group A").
3. If the theorem appeared in `Verification.lean` or any other
   published doc, remove the reference in the same PR.
4. If a downstream memory referenced the theorem, flag it for
   invalidation (the user can clear stale memory entries manually).

Deleting scaffolding is proof-work. Count it as such.
