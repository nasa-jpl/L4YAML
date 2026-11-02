# Scripts in Lean — Rule 9's conversion plan

Status: PLAN, defaults RULED (2026-11-01, owner: "ok with the defaults" —
every §6 default below is the decision). Governs the conversion of every
`scripts/*.py` to Lean under [`06-discipline.md`](06-discipline.md) Rule 9.
Phase 0 (the gate) is DONE (#196); each later phase lands as its own PR
and ticks its rows in §5. Work order (§3): phase 0 → 2.1 → 3.1 → 3.2 → phase 1 → the
rest; R12 holds its next flip until 3.1 lands (Q6).

Inventory basis: `scripts/` on `fix-a-grammar-completeness` at the merge of
PR #191 — **78 Python files, 13 176 lines**, plus 11 shell wrappers. Counts
and callers below were read off that tree (`grep`, `git log`); they are a
reading, not a pin, until phase 0's gate pins them.

## 1. What the scripts are

Four classes, by what they read and what they are allowed to write:

| Class | Reads | Writes | Count / lines | Examples |
|---|---|---|---|---|
| **G — gates** (CI or pre-push) | tree text, build logs | nothing (exit code) | 6 / 866 | `check_import_closure.py`, `check_reflection_index.py`, `check_closure_log.py`, `rename_lemma.py --check` (Rule 7), `check-serialization-axioms.py`, `gate_vocab.py` |
| **I — reusable instruments** | tree, environment dump, build log | pins (`repin.py`), stdout | 8 / 1 851 | `flip_census.py`, `pack_flip_census.py`, `residue_classes.py`, `repin.py`, `docs_nav.py`, `ledger_diff.py`, `drop_sweep.py`, `gen_traceof.py` |
| **F — one-shot flips / prices** | one library file at a revision | the library file (patched, then restored) | 58 / 9 115 | `flip_*.py` ×39, `*_price.py` ×15 (`ride_`, `close_`, `carrier_`, `wire_`, `transport_`, `coordinate_`, `arm_`, `inline_class_`, `punt_reason_`, `park_top_`, `vslot_top_`, `mv_slot_top_`, `open_map_`, `park_nic0_`, `landing_nic0_`), `beta5_arms.py`, `narrow_conclusion.py`, `pay_chain_optional.py`, `decline_all_optional.py` |
| **R — reports / publishing** | test results, Verso HTML, the yaml-test-suite, the spec grammar | HTML, PDF, JSON, stdout | 6 / 1 344 | `matrix_score.py`, `cross-lang-compare.py`, `generate-test-reports.py`, `html-to-pdf.py`, `svg-objects.py`, `verify_yaml_spec_annotations.py` |

Shape they share. Fifty-nine of the 78 (class F, plus `pack_flip_census.py`)
are the same program with different constants: **patch one file by
anchored string replacement → `lake build L4YAML` → resolve each error to
its enclosing declaration → classify (sorried / restated / deleted /
gate-site / pin) → restore the bytes and print both checksums**. The
differences among them are the anchors (`OLD`/`NEW` text), the base
revision (`--rev`), and whether a round is repeated to a fixpoint. The
resolve-to-declaration step is `flip_census.py` (116 lines), imported or
re-typed by the rest.

What they need from the host that Lean does not provide natively:

| Need | Scripts | Lean answer |
|---|---|---|
| run `lake build` / `git show` / `git diff` and read exit + output | all F, I | `IO.Process.output` (already used by `Tests/SuiteRunner/Main.lean`, `Tests/Main/Runner.lean`) |
| regular expressions (193 uses) | G, I, F | none in core; see Q1 — `Std.Internal.Parsec`/hand parsers for the fixed shapes (`file:line:col: error:`, `def expected… := "…"`, `### Item N (date)`), or read the environment and have no text to parse |
| md5 of a file | F | `hashlib` → `IO.Process.output "md5sum"` or Lean's `String.hash`/a byte hash — any stable digest printed both sides suffices |
| URL fetch | `verify_yaml_spec_annotations.py` | `curl` from the driver, or vendor the grammar file (Q4) |
| HTML → PDF (WeasyPrint), SVG rewriting (`xml.etree`) | `html-to-pdf.py`, `svg-objects.py` | no Lean counterpart; exception or external program (Q3) |
| docker-driven processor matrix, thread pool | `matrix_score.py` | `IO.Process` + `Task` |
| `signal`, `importlib` (self-reload) | `docs_nav.py`, `beta5_arms.py` | not needed in a compiled exe |

## 2. Target shape

```
Scripts/                      -- lean_lib Scripts (allowNonModules := false; `module` headers)
  Lean/Decl.lean              -- opener/binder/import reading OFF THE ENVIRONMENT (Lean.Environment)
  Lean/BuildLog.lean          -- `file:line:col: error:` parser (both lake orderings), resolve to decl
  Flip/Patch.lean             -- anchored replace (count == 1 or refuse), checksum, restore
  Flip/Round.lean             -- build → census → sorry the breakages → rebuild, to a fixpoint
  Flip/Report.lean            -- sorried / restated / deleted / gate-site / pin, per producer/consumer
  Git.lean                    -- `git show REV:path`, `git diff --quiet REV -- L4YAML :!path`
  Docs/ClosureLog.lean        -- DOCS.md item index (what docs_nav.py and check_closure_log.py share)
  Pins.lean                   -- `def expected… :=` reader/writer (repin.py)
  Main/<name>.lean            -- one `main` per lean_exe
lakefile.lean                 -- lean_exe scripts-check-import-closure, scripts-repin, scripts-flip, …
scripts/*.sh                  -- unchanged names; body becomes `exec lake exe <name> "$@"`
                              -- until phase 4.5 replaces each with a Lake `script` (`lake run <name>`, Q7)
```

Rules for the port, so the Lean versions are better instruments, not
transliterations:

- **Declaration questions are answered from the environment — where one
  can be loaded.** `check_import_closure.py` documents why it does NOT
  load one: merging the full Proofs environment trips a duplicate
  equation-lemma error (its docstring, and the CI comment it cites), and
  `drop_sweep.py` documents the second obstacle — the executable entry
  points each define a root `main`, so two of them in one environment is
  an import error. A port therefore does not start from
  `Lean.importModules` over everything. Strategy, in order: (i) read the
  import *graph* without elaborating — each `.olean`'s header
  (`Lean.readModuleData` → `header.imports`) lists its imports exactly as
  the module system resolved them, no regex and no environment merge; the
  closure walk is over headers, roots as today (`L4YAML` + the four
  emitter exes). The **candidate set stays the on-disk inventory** of
  `L4YAML/**/*.lean`, exactly as the Python gate has it: an orphan has no
  `.olean` after a default-target build (nothing imports it, so nothing
  builds it), so a header-only inventory could never see it. The gate
  therefore reports three classes, each a failure: *orphan* (a source
  file not in the header-reachable closure), *missing header* (a source
  file whose `.olean` is absent — unbuilt, so unverifiable), and *stale
  header* (an `.olean` older than its source, which could carry an
  import list the source no longer has). Reachable-but-stale is a
  failure, not a pass. (ii) only where a question needs constants (binders,
  axioms, dependents) load one closure at a time, as `DropDependents` and
  `drop_sweep.py`'s per-entry-point probes already do. Phase 1.1 first
  reproduces the duplicate equation-lemma failure with a scratch
  `importModules` over the Proofs roots on the current toolchain and
  records the result in the PR; if it no longer reproduces, (i) is still
  the port (cheaper, and immune to it); if it does, (i) is the only port.
  `flip_census`'s "enclosing declaration" is a build-log question: the
  error site is in a file that failed to elaborate, so there is no
  environment for it — the port keeps the text scan for openers, as a
  tested function (`#guard` rows taken from the Python `OPENER` cases),
  and uses `declRangeExt` only when the module did build.
- **One flip library, data-driven flips.** A class-F instrument becomes a
  *flip spec* — file, base revision, list of `(anchor, replacement)` —
  consumed by one `lake exe scripts-flip SPEC.lean|SPEC.json`. The 58
  scripts collapse to 58 specs; the protocol (anchor count, checksum
  both sides, never beside a build, `--rev`, `--keep`) is written once.
- **A gate's `.sh` name does not change** until phase 4.5. CI and the
  skills call `scripts/check-import-closure.sh`; its body changes to
  `lake exe`. The portable entry point is `lake run <name>` (Q7): bash
  is the last non-portable layer, and Lake runs the same on Linux, macOS
  and Windows.
- **Every converted script is pinned where the Python was.** The guard
  files that quote a script's reading (e.g. `GateVocabulary.lean` ↔
  `gate_vocab.py`) are re-pointed at the Lean exe in the same PR; the
  reading must not move (§9: a port that changes a number has found a
  bug in one side — say which).
- **Python is deleted in the PR that lands its replacement**, after one
  paired run shows identical output on the current tree (the port's
  Rule 2: same input, same classification, same count).

## 3. Phases

Each phase is one or a few PRs off `fix-a-grammar-completeness`, one
script family per PR, following the item protocol where an instrument's
reading is quoted (predict the Lean reading = the Python reading, then
score it).

**Phase 0 — the rule's gate (1 PR, no conversion). DONE — #196.**
`scripts/check-scripts-lean.sh` + `scripts/scripts-ledger.txt`: the ledger
lists every `.py` under `scripts/` with its class and status
(`todo | lean:<exe> | exception:<reason>`); the gate fails on a `.py` not
in the ledger, on a ledger row for a file that no longer exists, and on a
`python3` call in `scripts/*.sh` or `.github/workflows/*.yml` whose target
is not an `exception` row. **Inline Python** — `python3 -c "…"`,
`python3 - <<'EOF'`, `python3 - "$ARG" <<'EOF'` — has no target file. The
ledger tracks **invocations, one row per invocation line**, keyed by the
command text with whitespace collapsed (`inline:<file>:<command-prefix>`),
so a line that moves is the same row and a line that is edited is a new
one; the gate prints the current line numbers beside each row. Identical
commands in one file share a key — the two `import weasyprint` probes in
each file do — so the check is a **multiset** equality, not a set one:
for every key, the number of ledger rows with that key must equal the
number of invocation lines with it (a row short or a row over both fail);
the ledger writes the duplicate as two rows (or one row with `×2`, which
the reader expands), and the gate prints `×n @ lines [a, b]`. Off the
tree at the #191 merge there are **seven**: four in
`.github/workflows/test-coverage.yml` — the two `python3 -c "import
weasyprint"` probes (install step, before and after `pip install`), the
`stats.json` proof-hygiene heredoc, the release-asset JSON lookup — and
three in `scripts/generate-all.sh` — the two `import weasyprint` probes
and the same hygiene heredoc. `python3 -m pytest …` over
`Tests/test_python_ffi.py` and `python/tests/` is the shipped binding's
test run (§4, product, not a script) and `python3 -m pip install
weasyprint` is Q3's tool install; the gate recognises `-m pytest` on
those two paths and `-m pip install weasyprint` as covered by their §4
rows and needs no inline rows for them. Phase 1 replaces the two
hygiene heredocs with one Lean exe over `stats.json` (`Lean.Json`, ~20
lines) and the asset lookup with `gh api --jq` (a JSON field read, no
logic; wrappers may use coreutils and `gh`); the four `import weasyprint`
probes become `weasyprint --version` under Q3 (§4). An inline row is
removed when its command is gone. Added to the gate battery (AGENTS §3,
the skills). The ledger may only shrink. *This gate is itself a shell
wrapper around a Lean exe (`Scripts/Main/CheckScriptsLedger.lean`) — the
first Lean script, and the proof the shape works.*

**Phase 1 — class G, the gates (6 scripts, ~5 PRs).** Order by what
breaks CI if wrong, cheapest first:
1. `check_import_closure.py` → `scripts-check-import-closure` (environment
   read; drops the import regex for good).
2. `check_reflection_index.py` → `scripts-check-reflection-index`.
3. `check_closure_log.py` + `docs_nav.py` → one `Scripts/Docs/ClosureLog.lean`
   with two exes (`scripts-check-closure-log`, `scripts-docs-nav`); they
   share the item parser today by duplication.
4. `rename_lemma.py` → `scripts-theorem-keyword` (`--check` is the Rule 7
   gate; the rename mode is kept as `--rewrite`).
5. `check-serialization-axioms.py` → read inside
   `scripts/check-serialization-proofs.sh`'s Lean exe.
6. `gate_vocab.py` → `scripts-gate-vocab`; it already shells out to an
   environment dump — in Lean the dump *is* the environment.

**Phase 2 — class I, the shared instruments (8 scripts, ~4 PRs).**
1. `flip_census.py` + `repin.py` → `Scripts/Lean/BuildLog.lean`,
   `Scripts/Pins.lean`, exes `scripts-flip-census`, `scripts-repin`. These
   two are the core every later phase reuses; land them before any class-F
   port.
2. `pack_flip_census.py` + `residue_classes.py` → `scripts-pack-census`
   (PACK-FLIP / PACK-RESIDUE / RESIDUE-CLASSES as three subcommands of
   one exe; the `∃`-index classing reads binders from the environment,
   which `GhostIndexCensus.lean` already does — one implementation).
3. `drop_sweep.py` → `scripts-drop-sweep`, **not retired**: the walk
   (`Tests.Guards.DropDependents.census`) is already Lean and shared, but
   the sweep is the WIDE reading — every `L4YAML.*`/`Tests.*` module with
   an olean in one environment, plus the executable entry points probed
   one at a time against their own closures (two root `main`s cannot
   share an environment) — and `DropDependents.lean` pins that wide
   reading as its fifth pin (item 238). Retiring the script would leave
   that pin without a producer. The exe keeps both probes and the
   `--quick` mode, generates the per-closure scratch modules under
   `L4YAML/Scratch/` and removes them as today, and must reproduce the
   current `D= S= R= T=` reading before the Python is deleted.
4. `ledger_diff.py` → `scripts-ledger-diff` (the escaped-pipe table parser
   is 40 lines; port with its two regression cases from PRs #125/#126 as
   `#guard`s). `gen_traceof.py` → `scripts-gen-traceof` (reads
   `Surface/Node.lean`'s mutual block; in Lean, read the syntax tree, not
   the text).

**Phase 3 — class F, the flips (58 scripts, ~6 PRs).**
1. `Scripts/Flip/*` and `lake exe scripts-flip`: one PR, validated by
   re-running the **two most recent** flips (`flip_colon_chain.py`,
   item 417; `flip_kslote_domain.py`, item 416) as specs at their `--rev`
   and matching the Python's declaration count and classification
   (`errors=4 decls=2` for 416's base is the known reading).
2. Specs for the flips whose readings are **still cited as live
   instruments** by an open NEXT or a ledger snapshot: `flip_210.py`,
   `flip_211_stage1.py` (the `[211]` price, 10 decls / 25 sites),
   `flip_beta5.py`/`beta5_arms.py` (`FIX-PIN`, `ARM-PIN`),
   `punt_reason_price.py`, `flip_inl_declines.py`. Each spec's first run
   must reproduce the number the ledger quotes.
3. The remaining 47 one-shot flips and prices (items 205–415, 6 538 lines): **Q2 decides**
   whether they are converted to specs (mechanical: the anchors are the
   data) or frozen — moved to `scripts/attic/` with their reading in
   `DOCS.md` as the record and listed as `exception:historical` in the
   ledger. Default if the owner is quiet: convert the anchors to specs in
   batches of ~10 per PR (the spec is smaller than the script), delete
   the `.py`.
4. `narrow_conclusion.py`, `pay_chain_optional.py`,
   `decline_all_optional.py`: source transforms over `StreamAccum.lean`
   → `scripts-restate` subcommands on `Scripts/Flip/Patch.lean`.

**Phase 4 — class R, reports and publishing (6 scripts, ~4 PRs).**
1. `cross-lang-compare.py`, `generate-test-reports.py` → extend
   `Tests/SuiteRunner/HtmlReport.lean`, which already renders HTML in
   Lean; the four-backend comparison is a table over suiterunner's JSON.
2. `matrix_score.py` → `scripts-matrix-score`: the scorer is pure (event
   and JSON normalisation), the docker calls are `IO.Process`; `Task` for
   the pool. The JSON-stream decoder is the one piece of real parsing;
   `Lean.Json` reads one value, loop it.
3. `verify_yaml_spec_annotations.py` → `scripts-verify-spec-annotations`,
   with the grammar file fetched by `curl` in the `.sh` or vendored (Q4).
4. `svg-objects.py`, `html-to-pdf.py` → **Q3**: WeasyPrint has no Lean
   counterpart. Options: (a) `exception:weasyprint` for `html-to-pdf.py`
   only, with `svg-objects.py` ported (it is an HTML rewrite, 71 lines);
   (b) replace the pair with a `.sh` driving `weasyprint` CLI directly and
   a Lean exe for the TOC/SVG rewriting; (c) drop the PDF from CI.
5. **Portable wrappers (Q7).** Every `scripts/*.sh` that only runs a
   `lean_exe` becomes a Lake `script` block in `lakefile.lean` —
   `script check-scripts-lean (args) do … IO.Process.spawn … lake exe
   scripts-check-ledger …` — invoked as `lake run check-scripts-lean`
   on Linux, macOS and Windows; `lake run` lists them. CI and the skills
   switch to `lake run`; the `.sh` files are deleted in the same PR
   (one per gate family). This is not Q5 reopened: the exes stay
   compiled under `Scripts/`; the `script` block is a few lines that
   spawns one, so there is nothing to re-elaborate. Wrappers that do
   more than run an exe (`generate-all.sh`, the WeasyPrint step) are
   ported to `IO.Process` in the same block or left as the ruled Q3
   `.sh`, stated per file in the PR. `uv` is used only where Python is
   the product — the `python/` binding and its pytest run — never as a
   launcher for a gate or instrument.

**Phase 5 — retire the Python toolchain from the proof lane.** When the
ledger holds only `exception` rows: remove the CI venv steps that exist
for the scripts (the `python/` package tests keep theirs), update
`.devin/skills/l4yaml-price-instruments/SKILL.md` and
`l4yaml-build-and-gates` to the `lake exe` names, and move Rule 9's gate
from "ledger may only shrink" to "ledger holds exceptions only".

**Work order (the one sequence contributors follow; the status line at
the top repeats it):** phase 0 → 2.1 → 3.1 → 3.2 → phase 1 → 2.2–2.4 →
phase 4 → 3.3 → 3.4 → phase 5. Phase 2.1 and 3.1 come before the CI
gates because Row 12 blocks on them (Q6): the next item's flip needs the
flip exe, and every item needs `repin`/`flip_census`. Phase 1 is next
because it removes Python from CI; it does not block an item.

## 4. Exceptions (proposed; the ledger is the record)

| File | Why it may stay non-Lean | Until |
|---|---|---|
| `python/**`, `python/tests/**`, `Tests/test_python_ffi.py`, `Tests/conftest.py`, `Tests/tryparse_python.py` | the shipped Python binding and its tests — a product, not a script | — |
| `scripts/html-to-pdf.py` + the `python3 -c "import weasyprint"` probes | WeasyPrint rasterisation (Q3: ruled — the CLI route). The probe must keep checking that WeasyPrint can *start*, not merely that a binary exists: `import weasyprint` today fails when Pango/cairo are missing and that is what makes the PDF step skip with a warning instead of failing the job; the replacement is `weasyprint --version` (or `weasyprint --info`), which imports the package and so loads the native libraries, under the same "skip PDF with a warning on failure" branch — never `command -v weasyprint`. | phase 4.4 |
| `scripts/attic/*.py` (if Q2 = freeze) | historical readings already recorded in DOCS.md; never run again | — |

## 5. Ledger (phase 0 turns this into `scripts/scripts-ledger.txt`)

| Script | Class | Lines | Born | Callers | Target | Status |
|---|---|---|---|---|---|---|
| check_import_closure.py | G | 104 | 07-31 | check-import-closure.sh (CI) | scripts-check-import-closure | todo |
| check_reflection_index.py | G | 148 | 08-11 | check-reflection-index.sh (CI) | scripts-check-reflection-index | todo |
| check_closure_log.py | G | 143 | 09-27 | check-closure-log.sh (CI) | scripts-check-closure-log | todo |
| rename_lemma.py | G | 220 | 08-01 | check-theorem-keyword.sh (CI) | scripts-theorem-keyword | todo |
| check-serialization-axioms.py | G | 44 | 10-05 | check-serialization-proofs.sh (CI) | (inside that gate's exe) | todo |
| gate_vocab.py | G | 207 | 09-25 | battery; GateVocabulary.lean | scripts-gate-vocab | todo |
| repin.py | I (also `--check`) | 223 | 10-23 | every item | scripts-repin | todo |
| flip_census.py | I | 116 | 10-18 | every flip | scripts-flip-census | todo |
| pack_flip_census.py | I | 400 | 10-20 | every Row 12 item (PACK) | scripts-pack-census | todo |
| residue_classes.py | I | 123 | 10-30 | Row 12 items ≥ 403 | scripts-pack-census classes | todo |
| docs_nav.py | I | 339 | 10-20 | AGENTS §1, skills | scripts-docs-nav | todo |
| ledger_diff.py | I | 226 | 10-26 | ledgers/README | scripts-ledger-diff | todo |
| drop_sweep.py | I | 229 | 09-22 | skills; DropDependents.lean's wide pin | scripts-drop-sweep | todo |
| inline ×7: test-coverage.yml — `import weasyprint` probe ×2, hygiene heredoc, release-asset lookup; generate-all.sh — `import weasyprint` probe ×2, hygiene heredoc | G/R | ~30 | — | CI, generate-all.sh | hygiene ×2 → one Lean `stats.json` exe; asset lookup → `gh api --jq`; probes ×4 → `weasyprint --version` (Q3) | todo |
| gen_traceof.py | I | 195 | 10-23 | TraceOf regeneration | scripts-gen-traceof | todo |
| flip_colon_chain.py, flip_kslote_domain.py | F (live, items 417/416) | 138, 85 | 11-01 | items | flip specs (phase 3.1 validation) | todo |
| flip_210.py, flip_211_stage1.py | F (live, `[211]`) | 138, 86 | 09-21, 10-27 | ledger snapshots | flip specs | todo |
| flip_beta5.py, beta5_arms.py | F (live pins FIX-PIN/ARM-PIN) | 623, 297 | 09-25 | skills | flip specs | todo |
| punt_reason_price.py, flip_inl_declines.py | F (live) | 510, 72 | 09-19, 10-31 | items 211, 415 | flip specs | todo |
| narrow_conclusion.py, pay_chain_optional.py, decline_all_optional.py | F (transforms) | 241, 140, 247 | 09-20 | skills | scripts-restate | todo |
| 47 remaining `flip_*.py` / `*_price.py` (items 205–415) | F (one-shot) | 6 538 | 09-18 … 10-31 | DOCS.md items only | specs or attic (Q2) | todo |
| matrix_score.py | R | 264 | 07-01 | README, CI | scripts-matrix-score | todo |
| cross-lang-compare.py | R | 93 | 10-17 | CI, generate-all.sh | HtmlReport.lean | todo |
| generate-test-reports.py | R | 201 | 04-09 | CI, generate-all.sh | HtmlReport.lean | todo |
| verify_yaml_spec_annotations.py | R | 301 | 03-29 | manual | scripts-verify-spec-annotations | todo |
| svg-objects.py | R | 71 | 09-05 | CI, generate-all.sh | scripts-svg-objects / Q3 | todo |
| html-to-pdf.py | R | 414 | 04-09 | CI, generate-all.sh | exception or Q3 | todo |

## 6. Questions for the owner (all ruled 2026-11-01: the stated default of each)

1. **Regular expressions.** Core Lean has none. Options: (a) hand parsers
   per fixed shape (the build-log line, the pin line, the item header —
   four shapes cover the gates and instruments); (b) depend on a Lean regex
   package (a new `require`, which Rule "ask before bumping pins" covers);
   (c) read the environment so there is no text to parse (preferred where
   the question is about declarations). Default: (a) + (c), no new dependency.
2. **The 47 one-shot flips.** Convert each to a flip spec (mechanical,
   ~10 per PR, the anchors are the data) or freeze them in `scripts/attic/`
   as `exception:historical` with DOCS.md as the record? Converting keeps
   every reading re-derivable (§9); freezing saves ~5 PRs. Default:
   convert.
3. **PDF.** Keep `html-to-pdf.py` as the one `exception:weasyprint`, or
   replace with the `weasyprint` CLI driven from `.sh` plus a Lean exe for
   the TOC/SVG rewriting, or drop the PDF build? Default: the CLI route (b)
   — no Python logic, one external program.
4. **Spec grammar fetch.** `verify_yaml_spec_annotations.py` downloads
   `yaml-spec-1.2.yaml` at run time. Vendor the file (reproducible,
   licence to check) or `curl` in the wrapper? Default: vendor.
5. **Where do the exes live.** `Scripts/` as a new top-level `lean_lib`
   with one `lean_exe` per script (compiled, fast, type-checked by the
   full build — adds ~30 jobs to the 1342), or Lake `script` blocks in
   `lakefile.lean` (interpreted, no build cost, but every run re-elaborates
   and the lakefile grows by thousands of lines)? Default: `Scripts/` +
   `lean_exe`, `.sh` wrappers unchanged.
6. **Phase 0 timing vs Row 12.** The gate blocks new `.py`; R12 writes one
   `flip_<item>.py` per item today. Land phase 0 and 3.1 before R12's next
   flip (so item 418's price is the first Lean spec), or let R12 keep
   writing Python until 3.1 lands and convert those too? Default: phase 0
   + 2.1 + 3.1 first, R12 holds its next flip until then.
7. **Portable invocation (ruled 2026-11-01: option 1).** The `.sh`
   wrappers are bash, so nothing here runs on Windows. Options: (1) Lake
   `script` blocks, `lake run <name>` — no bash, no Python, one
   toolchain, consistent with Rule 9; (2) a `uv`-managed `pyproject.toml`
   with console-script entry points that exec `lake exe …` — portable,
   but a Python launcher under every gate, which is what Rule 9 removes.
   Ruled: (1); `uv` only for `python/` (§4). Lands as phase 4.5, after
   3.1/3.2, because the Row 12 instruments come first (Q6); the `.sh`
   names hold until then.
