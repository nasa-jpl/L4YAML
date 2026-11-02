---
name: l4yaml-build-and-gates
description: Build L4YAML correctly (full vs library-only), read a red build, re-pin the closure censuses a new module or deletion moves, run the text gates, test suites and axiom census an item must report. Use when a build is red, a Tests/Guards pin moved, a module was added or deleted, or before declaring an item green.
---

# Build and gates

## Build

```bash
lake build > /tmp/build.log 2>&1; echo "exit=$?"     # the exit code is the oracle (§1)
grep -c '^⚠' /tmp/build.log                          # standing warnings (items quote the count)
grep -n '^✖\|error:' /tmp/build.log | head           # first red module
```

- `lake build` = library + every `lean_lib «Tests.*»` + exes (~1260 jobs).
  `lake build L4YAML` compiles the library only and **skips the guards and
  censuses**; use it for a fast inner loop, never as the green signal.
- Lean stops at the first failing module.  Several moved pins surface one
  per build; fix, rebuild, repeat.
- A `Prop` destructuring failure makes the elaborator skip every construction
  behind it, so the first red build after a statement change **undercounts**
  (§7).  Fix destructurings first, then count.

## Pins that move when the module graph changes

Adding or deleting a library module moves closure censuses; only a full build
runs them:

| Guard | Field |
|---|---|
| `Tests/Guards/Proofs/FreeSurfaceCensus.lean` | `expectedClosure` (`modulesSeen=N`) |
| `Tests/Guards/Proofs/DropDependents.lean` | `expectedClosure` |
| `Tests/Guards/Proofs/ParkBill.lean` | `expectedClosure` |

Many other guards pin counts by name (`rg -n 'expected[A-Za-z]* *=' Tests/Guards/Proofs`).
Re-pin with the **cause** in the item; a pin that moved for a reason you
cannot name is a finding, not a chore.

A new `Tests/Reflections/*.lean` must be imported from `Tests/Reflections.lean`
or it is not built (`lake run check-import-closure` catches it).

## Gates (what an item reports)

```bash
lake run check-theorem-keyword        # `theorem` only on scripts/capstones.txt entries
lake run check-import-closure         # no orphan modules (reads .olean headers; builds the roots first)
lake run check-reflection-index       # reflections index narrative matches its bullets
lake run check-closure-log            # DOCS.md items ascend / dated / gaps declared
lake run check-serialization-proofs   # serialization hygiene: axiom profiles of every #print axioms site, sorry control
lake run check-gate-vocab             # gate names cited in prose resolve (reads .olean headers via LEAN_PATH)
lake run check-scripts-lean           # Rule 9: scripts/**/*.py and inline python3 sites are on scripts/scripts-ledger.txt (shrink-only pin)
lake run run-all-tests                # every test exe, collects failures
lake exe suiterunner                  # matrix triple pass/fail/skip
lake exe eventscore                   # event axis
```

CI (`.github/workflows/test-coverage.yml`) runs on a self-hosted runner that
can queue indefinitely; run the battery locally and quote it.

## Axiom census

For every declaration an item touched:

```lean
-- L4YAML/Scratch/NNN-axioms.lean (gitignored)
import L4YAML.Proofs.Production.StreamAccum
#print axioms L4YAML.Proofs.Production.theName
```
```bash
lake env lean L4YAML/Scratch/NNN-axioms.lean
```
Acceptable: `propext`, `Classical.choice`, `Quot.sound`, plus per-call-site
`Lean.ofReduceBool` from `native_decide`.  `sorryAx` or any custom axiom is a
failure even when the build is green (§8).  Some scripts delete
`L4YAML/Scratch`; write the probe immediately before reading it (§9).

## Module-system facts (Lean 4.35)

- `requiresModuleSystem := true` on `L4YAML`: every library file starts with
  `module`; use `public import` for what downstream needs, `public section` /
  `@[expose]` for definitions proofs must unfold.
- Tests that reflect or evaluate need both `import` and `meta import`;
  `meta initialize` for handlers to run in importers; a `main` in a module
  file is `public def main`.
- Legacy (non-`module`) files live only in test libraries with
  `allowNonModules`; do not add a new one.
