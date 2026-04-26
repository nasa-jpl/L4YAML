# Auto-Generated Equation-Lemma Collisions

**Status**: open issue, separate from Initiative 3.  Not blocking
`lake build L4YAML` (each module compiles independently); breaks
environment-merging tools (`lake exe graph --to L4YAML`,
`#check`-after-import-everything style scripts).

**Filed by**: principal verifier, after a `lake exe graph --to L4YAML`
run aborted with a duplicate-declaration error for
`L4YAML.Scanner.ScannerState.emit.eq_1`, claimed by both
`L4YAML.Proofs.Coupling.StructureCoupling` and
`L4YAML.Proofs.Scanner.ScannerProofs`.

## Background — what generates the collision

Lean 4 lazily realises auto-generated equation lemmas (`<def>.eq_<n>`,
`<def>._eq_<n>`, `<def>.match_<n>`, `<def>._match_<n>`) at the first
call site that needs them — typically `simp [<def>]`, `simp only
[<def>]`, or `unfold <def>` followed by `split` or rewriting on the
unfolded term.

The realisation mechanism (`realizeConst`) memoises into the *current*
module's environment.  Two modules that

1. independently force the same equation lemma, *and*
2. don't transitively import each other,

each end up with their own copy of `<def>.eq_<n>` in their `.olean`.
The per-module `lake build` succeeds because each compilation only
sees one of the two copies.  Tools that merge the full transitive
import-environment (env-graph dumps, whole-program `Environment`
walks, IDE multi-root sessions) refuse the merged environment as
ill-formed.

## Current incident

Both `L4YAML/Proofs/Coupling/StructureCoupling.lean` and
`L4YAML/Proofs/Scanner/ScannerProofs.lean` contain `simp
[ScannerState.emit]` / `simp only [ScannerState.emit]` calls; the
modules are import-disjoint (neither transitively imports the other).
Each forces `ScannerState.emit.eq_1` to be realised, and the resulting
two copies collide at env-merge time.

As of `feature/append-only @ 71a86eee` the collision **does not
currently reproduce** — `lake exe graph --to L4YAML
import_graph.dot` succeeds.  But the generating pattern (independent
`simp [<def>]` calls in import-disjoint modules) is still present at
~465 unique sites across `L4YAML/Proofs/`, so the bug is latent rather
than fixed.  Touching the import graph (adding a new submodule,
inverting an import edge) is enough to trigger it.

## Three remediation tracks

Filed as one document, three independent work items.  They compose:
(1) catches recurrences, (2) prevents new ones, (3) audits what's
already there.

### Track 1 — CI collision detection

Add `lake exe graph --to L4YAML import_graph.dot` (or equivalent
env-merging command) as a CI step in `.github/workflows/`.  The graph
command transitively imports every module and merges the resulting
environment; any auto-generated equation-lemma collision aborts the
run with a clear error pointing at the colliding name and its two
claimants.

**Cost**: minutes — one job step + artifact upload of the .dot file
(handy independently for documentation).
**Catches**: any future collision the moment it lands, including
collisions in lemmas we don't think to lift.
**Doesn't catch**: collisions that only manifest when an external
consumer (FFI sample, downstream library) performs the env merge.

### Track 2 — Named `@[simp]` lemma promotion

For every definition routinely simp'd via `simp [<def>]`, define a
named `theorem <def>_def : <def> args = <body> := rfl` (or its
`@[simp]` variant) immediately after `<def>`'s definition.  Migrate
call sites from `simp [<def>]` to `simp [<def>_def]`.  Now only one
module (the one that hosts `<def>_def`) realises any equation-flavour
constant; downstream `simp [<def>_def]` calls reuse the realised
lemma via the import graph instead of re-realising it.

This also has secondary benefits independent of the collision bug:

* The lemma is named, so `set_option trace.Meta.Tactic.simp.rewrite`
  output is greppable.
* The lemma's RHS is what the proof author actually wants — `rfl`-form,
  no `match`-of-the-internal-encoding artefacts.
* Refactoring `<def>`'s body forces a one-line update to `<def>_def`
  rather than silent drift in 30 simp call sites.

**Scope**: the survey on `feature/append-only` shows ~465 `simp [<L4YAML
def>]` and ~410 `unfold <L4YAML def>` sites in `L4YAML/Proofs/`.  Not
all need lifting — the most-called definitions deliver most of the
benefit.  Suggested ranked target list (highest fan-in first,
informal):

| Definition | Approx call sites | Why high-priority |
|---|---|---|
| `ScannerState.emit` | many | the actual reproducer |
| `ScannerState.advance` | many | dual to emit; same shape |
| `saveSimpleKey` | ~30 | mutated by Initiative 3, churn-prone |
| `scanValuePrepare` | ~20 | same |
| `unwindIndents` | ~15 | unfold-heavy |
| `pushMappingIndent` / `pushSequenceIndent` | ~15 each | unfold-heavy |
| `lastTokenVal?` | ~10 | post-cutover one-liner |

A reasonable tactic: lift the top 10 names; that should remove ~60% of
realisation traffic.  Re-survey after; lift more if the audit tool
(track 3) still flags collisions.

**Cost**: incremental.  Per definition: 1 named lemma + a
search/replace across `L4YAML/Proofs/` for `simp [<name>]` →
`simp [<name>_def]`.  ~30 minutes per high-fan-in definition.

### Track 3 — Constants audit tool

A small Lean-side tool that:

1. Imports the full `L4YAML` library (so its `Environment` contains
   every realisation).
2. Walks `Environment.constants`, filters to names matching
   `<base>.eq_<n>` / `._eq_<n>` / `.match_<n>` / `._match_<n>` /
   `._eq.<...>` / etc.
3. For each such name, asks each contributing `.olean` whether it
   contains the constant.
4. Reports any name found in more than one contributing `.olean` *with
   a non-trivial body* (i.e. discounting `realizeConst`-cache shims
   that are intentionally cross-module).

Output: a report mapping `<colliding constant name> → [list of
.oleans claiming it]`.  Run periodically; treat any non-empty output
as actionable.

**Cost**: medium — needs Lean import-graph knowledge + careful
filtering (auto-generated names that legitimately appear in many
modules vs. genuine collisions).  Maybe 1–2 days of focused work.
**Useful for**: progress reporting on track 2 (does lifting `emit_def`
actually drop the realisation count?).  Catching collisions in
constants we don't have a `simp` site for in `L4YAML/Proofs/` (e.g.
something realised through a `decide` chain).

## Recommended sequencing

1. **Track 1 first** (cheap, catches recurrences immediately).  Pin
   the .dot artefact in CI; if the build ever turns red on env-merge,
   we hear about it before anyone hits it manually.
2. **Track 2 opportunistically** when touching the affected modules.
   Don't make it a big-bang refactor; lift the top N as the call
   sites come up in normal work.
3. **Track 3 last** — only if track 1's binary "merge-ok / merge-bad"
   signal stops being granular enough to drive track 2's prioritisation.

Tracks 1 and 2 individually unblock the user-visible failure mode
(`lake exe graph` working again).  Track 3 is the principled
preventative — useful but not on the critical path.

## Filing notes

- Originally surfaced 2026-04-26 by the principal verifier in the
  context of an Initiative 3 review — separated out so it doesn't
  drag the J.2/J.3 schedule.
- Live reproducer (currently green): `lake exe graph --to L4YAML
  /tmp/L4YAML.dot`.  Re-run after any non-trivial proof corpus
  refactor; if it goes red, this issue moves from "latent" to
  "active".
- Closing criterion: track 1 in place; track 2 lifts at least the
  ScannerState.emit / advance / saveSimpleKey / scanValuePrepare set;
  track 3 either implemented and reporting clean, or explicitly
  deferred with rationale.
