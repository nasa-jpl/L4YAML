# AGENTS.md — working in L4YAML

Orientation for any coding agent (and new human contributor) doing proof
work here.  It points at the sources of truth and states the working rules
the history cites; it does not duplicate them.  Task-shaped recipes live in
[`.devin/skills/`](.devin/skills/README.md).

## 1. Where truth lives (read these, in this order)

| Question | Source of truth | Do not |
|---|---|---|
| What is this project, how do I build/test it, what is next at the project level | [`README.md`](README.md) (its **Next steps**) | restate its metrics elsewhere |
| Which theorems are capstones and their status / axiom profile | [`Blueprint/04-capstones.md`](Blueprint/04-capstones.md) — machine-parsed | add a theorem without a row here |
| The rules of proof work | [`Blueprint/06-discipline.md`](Blueprint/06-discipline.md) (Rules 1–9) | invent a parallel rule set |
| What the active campaign is doing *right now* | `DOCS.md` → Row 12 closure log: `scripts/docs_nav.py next` and `remaining` | read DOCS.md top to bottom (45k lines) |
| Which YAML productions are covered | [`L4YAML/YAML_PRODUCTIONS.md`](L4YAML/YAML_PRODUCTIONS.md) — machine-checked by `Tests/ProductionCoverage.lean` | edit by hand without the check |
| Vocabulary of the pipeline | [`Blueprint/01-terminology.md`](Blueprint/01-terminology.md); campaign vocabulary in §6 below | |
| Lessons from closed proof episodes | [`Blueprint/08-init4.md`](Blueprint/08-init4.md) (digest of `Tests/Reflections/*`) | |

Navigating the history: `python3 scripts/docs_nav.py toc | items --last 10 |
item N | next | remaining | steps | grep REGEX | section PREFIX`.  Every item
of the closure log is `### Item N (YYYY-MM-DD)`; the latest item's `**NEXT —`
paragraph is the mandate for the next piece of work.

## 2. The rules in one screen

From `Blueprint/06-discipline.md` (binding; the file wins over this summary):

1. **No theorem without a capstone.**  Name the capstone and the dependency
   chain before stating a lemma.  No capstone → add one first.
2. **Adversarial instantiation before proof.**  Instantiate the statement on
   fuel 0/1/2, empty/singleton/nested inputs, every relevant token kind,
   first/middle/last positions, in `Tests/AdversarialInstantiation.lean`.
   A refutation is a build failure, by design.
3. **No `sorry` on the closed path.**  CI fails on `sorryAx`; so does a
   custom axiom.  Judge a declaration by `#print axioms`, not by a green build.
4. **One source of truth per claim** (table above).
5. **Blueprint beats plan.**  When `DOCS.md` and `Blueprint/` disagree, the
   blueprint wins and the plan is corrected where it lives.
6. **Verify before recommending from memory.**  Grep the tree; names and
   counts in this repo move daily.
7. **`theorem` is reserved for `@[capstone]`** (listed in
   `scripts/capstones.txt`, gated by `scripts/check-theorem-keyword.sh`);
   everything else is `lemma`.
8. **No ghost index on the accumulation invariant** — every index a
   carrier introduces is a surface position, an obligation, or a projection
   of the scanner state; a fourth kind means the scanner is incomplete.
9. **Scripts are Lean, not Python.**  A new instrument or gate is a
   `lean_exe` (run via `lake exe`); no new `scripts/*.py`.  The conversion
   of the existing ones is planned in `Blueprint/09-scripts-in-lean.md`.

Working rules the closure log cites by section number (they were a private
checklist; restated here so the citations resolve):

- **§1 — the build is the oracle.**  A grep that found nothing proves
  nothing; a count is taken off a build or a `#guard`, never off a search.
- **§3 — read what is already pinned before measuring.**  Many counts are
  already `expected… = "…"` strings in `Tests/Guards/Proofs/*`; read them
  first, then measure only what is not pinned.
- **§5 — correct a docstring where it lives**, not in the log that noticed it.
- **§7 — a pin on a `Prop` is vacuous.**  Proof irrelevance makes "which
  disjunct was taken" unobservable; pin reachability of the informative side
  (a constructed witness), and beware the green-signal error where a
  destructuring failure hides every construction behind it.
- **§8 — judge by axiom profile.**  `sorryAx`-free is necessary, not
  sufficient; a clean profile also does not say the *statement* is worth
  proving (a conclusion `Or.inr trivial` would prove is not an obligation).
- **§9 — ask how many readings a number was taken over.**  A number taken
  once, from a log a later step overwrote, is not a reading.
- **§10 — re-run the census on *this* tree before spending.**  Pins from the
  previous item are a prediction, not a fact, until the build repeats them.

## 3. Build and gates

```bash
lake build                       # full: library + every guard/census library + exes (~1260 jobs)
lake build L4YAML                # library only — does NOT run Tests.Guards or the censuses
lake build L4YAML Tests.Guards   # library + compile-time guards
lake build > /tmp/build.log 2>&1; echo "exit=$?"   # capture the exit code itself, never via a pipe
```

Facts that cost people time:

- Lean stops at the first failing module, so a change that moves several pins
  surfaces them **one build at a time**.  Budget for it.
- Adding a library module bumps closure censuses:
  `Tests/Guards/Proofs/FreeSurfaceCensus.lean` (`modulesSeen`),
  `DropDependents.lean`, `ParkBill.lean` (`expectedClosure`).  Only a full
  `lake build` runs them.
- `lake exe scripts-repin /tmp/build.log` rewrites every `def expected… :=`
  pin the log reports as moved (`expected:`/`got:` pairs) to the value the
  build counted; `--check` only reports.  One run is a floor — rebuild and
  re-run until nothing moves — and read each change: a pin is a decision.
- `lakefile.lean` sets `requiresModuleSystem := true` for `L4YAML`: every
  library file starts with `module`; test libraries that still hold legacy
  files opt out with `allowNonModules`.
- The toolchain is pinned in `lean-toolchain`.  Do not bump it or a dependency
  pin without the owner's go-ahead.
- Pricing/flip instruments (`lake exe scripts-flip scripts/flips/*.json`,
  `scripts/*_price.py`, `scripts/flip_*.py`) edit library files in place and
  rebuild; never run one concurrently with `lake build`, and confirm the
  file is restored (they print the content hash / md5 both sides).
  They are Python today and are being converted to Lean under Rule 9
  (`Blueprint/09-scripts-in-lean.md`); do not add a new `.py`.

The gates an item reports green, in the order they are cheap:

```bash
scripts/check-theorem-keyword.sh     # Rule 7
scripts/check-import-closure.sh      # no orphan modules
scripts/check-reflection-index.sh    # every Tests/Reflections/* is indexed
scripts/check-closure-log.sh         # DOCS.md items ascend, dated, gaps declared
scripts/check-serialization-proofs.sh
python3 scripts/gate_vocab.py        # gate names in prose resolve (pin: Tests/Guards/Proofs/GateVocabulary.lean)
scripts/check-scripts-lean.sh        # Rule 9: every scripts/*.py and inline python3 site is on scripts/scripts-ledger.txt; the ledger only shrinks
scripts/run-all-tests.sh             # every test exe; collects failures
lake exe suiterunner                 # matrix; items quote pass/fail/skip
lake exe eventscore                  # event-axis score
```

Axiom census of every declaration an item touched (`#print axioms` in a
scratch file, or the `Tests/Guards/Proofs/*Axiom*` guards): the standard
three (`propext`, `Classical.choice`, `Quot.sound`) plus per-call-site
`native_decide` axioms are the only acceptable output.

## 4. The item protocol (how one unit of campaign work is recorded)

Each `### Item N (date)` in the Row 12 log has the same shape; keep it.

1. **Headline** in bold: what moved, and one of *PRICED* (measured, no code),
   *PAID* (obligation discharged), *BUILT/landed*, or *"no build"* for a
   docs-only item.
2. **The mandate.**  Quote the previous item's `**NEXT —`.  If you are
   departing from it, say so and why.
3. **Predictions first.**  P1…Pn with the number each predicts, *before* the
   instrument runs; later a *Predictions, scored* table marks each HELD or
   REFUTED and says what the refutation taught.
4. **The reading.**  What the instrument/build said, by producer/consumer.
5. **Gates.**  Which pins moved, in which guard file, and *why* (cause, not
   just old→new).  Full-build job count, warning count, suiterunner triple,
   gates passing, axiom census.
6. **`**NEXT —` …**  One paragraph: the next step, named by its Row 12 step
   number where it has one.

Keep `scripts/check-closure-log.sh` green: numbers ascend by one, dates do not
regress, a skipped number is declared in `scripts/check_closure_log.py`.

Commit subjects follow the log: `feat(row 12): step 12.3.3 — …`,
`docs(row 12): item 299 — …`, `test(guards): re-pin … after …`,
`proof(schema): …`, `fix(scanner): …`.

## 5. Git

- Branches and PRs go to **`nasa-jpl/L4YAML`** directly (since 2026-10-21);
  the `Open-MBEE/L4YAML` fork is retired for new work.
- The active integration branch is **`fix-a-grammar-completeness`**: branch
  from it, open PRs against it.  `main` is release-only.
- One item or one fix per PR, not stacked.  Review findings become follow-up
  PRs; never leave a fix half-pushed.
- Branch names `<type>/<slug>` (`feature/`, `fix/`, `docs/`, `test/`,
  `chore/`), no timestamps or identifiers.

## 6. Campaign vocabulary (Row 12 / β.5)

Working glosses, read off the log; the log is authoritative where they differ.
Pipeline terms (scanner, token, composition, indexed twin, …) are in
`Blueprint/01-terminology.md`.

| Term | Gloss |
|---|---|
| **arm** | One branch of a dispatcher's or proof's case split (one constructor, one class of input).  Items retire arms one at a time. |
| **park** | A pending node on the parser's stack that a later key or close lands on (e.g. the compact `?` entry, a block mapping awaiting its value). |
| **landing** | The position (line/column/break) at which a token lands relative to the awaited park. |
| **frame** | A fact about an enclosing indentation level carried through a proof (`ks`, the frame list); *frameless* = `ks = []`. |
| **ride** | A lemma application that lets a fact pass through a step on a frame (`drop_ride`, `slot_ride`); spending `dropClose` on a ride is what β.5 removes. |
| **slot / floor** | The slot a value is dispatched into (`ParkSlot`, `h_vslot`) and the indentation floor a dispatch is read against. |
| **route** | A lemma that establishes where a key lands (`rootMapRoute_or_refused`, `…F` = the resume twin). |
| **escape** | `block_dispatch_deferred` — the fallback that defers a dispatch; "emptying the escape's domain" (step 12.3) means proving every input that reached it takes a named arm instead. |
| **carrier / payload** | A premise added to a lemma to carry a fact from a producer to the consumers that refute or spend it; a payload is the fact it carries. |
| **punt** | A `KeyPackPunt` reason: a producer declining to build a key pack, naming why (`dedent`, `noKeyContext`, …).  Items delete punt reasons by paying them. |
| **producer / consumer** | The lemma that constructs a fact (`entryKeyPack_of_dispatch`) and the ones that destructure it (the two `:` consumers). |
| **price / PRICED / PAID** | Measure the cost of a change before making it (by instrument), then discharge it.  "Price before proving." |
| **STARVED** | A class of inputs for which no premise supplies the fact a proof needs; the deletion cannot proceed until a carrier feeds it. |
| **census / pin** | A `Tests/Guards/Proofs/*` file that `#guard`s a count or string (`expectedClosure = "…"`); a pin is one such expected value.  Moving a pin is instrument debt, not proof debt. |
| **flip** | A spec (`scripts/flips/*.json`, run by `lake exe scripts-flip`; older ones are still `scripts/flip_*.py`) that simulates a deletion by editing the source, rebuilding to a fixpoint, and classifying what breaks (sorried / restated / deleted / pins). |
| **instrument / gate** | A script that re-derives a number so an item never quotes a recollection; a gate is an instrument CI runs. |
| **reach / roster** | Whether an input can reach an arm (REACHED is the most a sweep can say) and the enumerated set of arms/applications an item accounts for. |
| **mandate / NEXT** | The previous item's closing `**NEXT —` paragraph, which the current item must answer. |
