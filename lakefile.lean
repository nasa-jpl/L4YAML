import Lake
open Lake DSL

/-- Link CTranslate2 into L4YAML binaries only on explicit request
    (`lake build -Kleancopilot=on`) — needed only if an exe/dynlib of THIS package
    imports LeanCopilot. Interactive `suggest_tactics` in the editor does NOT need
    it (LeanCopilot's own precompiled module dynlibs carry the FFI); linking it
    unconditionally gives every exe a runtime dependency on libctranslate2.so.4
    (+ GLIBCXX_3.4.30 via the pixi env), breaking them outside `pixi run`. Only
    meaningful when LeanCopilot is enabled — see the gated `require` below. -/
def leanCopilotLinkArgs : Array String :=
  if (get_config? leancopilot).isSome then
    #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
  else
    #[]

package L4YAML where
  version := v!"0.7.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  moreLinkArgs := leanCopilotLinkArgs

-- LeanCopilot is required only when the `L4YAML_LEANCOPILOT` environment variable is
-- set, which `pixi.toml`'s `[activation.env]` does automatically. So it is available
-- inside the pixi env (interactive proving, `pixi run`) but absent in CI, which never
-- activates pixi and thus resolves a clean, toolchain-matched dependency set (no
-- LeanCopilot / aesop / batteries pulled in one Lean minor ahead of this project's
-- pin). See README.md → "LeanCopilot". We gate on an env var, not a `-K` flag, because
-- the VS Code Lean extension forwards `lean4.serverArgs` to `lean --server` after
-- lake's `--` (so `-K` never reaches lake config) while the server does inherit the
-- process environment. `unsafeBaseIO` reads the var at configuration time (`meta if`
-- needs a pure `Bool`; the `(← IO.getEnv …)` form does not elaborate); Lake caches the
-- config, so toggling it takes `lake -R` / a server restart to re-read.
meta if (unsafeBaseIO (IO.getEnv "L4YAML_LEANCOPILOT")).isSome then
require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.35.0"

require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "v4.35.0"

require DocGen4 from git
  "https://github.com/leanprover/doc-gen4.git" @ "v4.35.0"


@[default_target]
lean_lib L4YAML where
  -- Ratchet: every file of this library carries a `module` header (242/242), and
  -- this makes Lake refuse a new one that does not.  It reports on the IMPORTER
  -- side too, so the test libraries that still hold legacy census files opt out
  -- with `allowNonModules` below -- see TODO/l4yaml-module-system.md for why those
  -- 48 files stay legacy.
  requiresModuleSystem := true

@[default_target]
lean_lib «Tests.Guards» where
  roots := #[`Tests.Guards]
  -- Importer-side opt-out, scoped to the libraries that still hold legacy census
  -- files on purpose: a body-reading census cannot take a `module` header without
  -- `import all` of every module it walks (TODO/l4yaml-module-system.md).  Set per
  -- library, NOT on the package: on the package it also exempts `lean_lib L4YAML`
  -- from its own `requiresModuleSystem`, which a positive control caught --
  -- a genuine legacy library file then built with no complaint at all.
  allowNonModules := true

-- Item 219's census module, made a library of its own at item 220 so that
-- later censuses can IMPORT its predicates and its walk.  Its runnable entry
-- point is `Tests.DeclineReachMain`; a module carrying a root-level `main`
-- cannot be imported.
@[default_target]
lean_lib «Tests.DeclineReachCensus» where
  roots := #[`Tests.DeclineReachCensus]
  allowNonModules := true

-- Item 220's census, likewise a library: `Tests.Guards.Proofs.DeclineArmLattice`
-- imports it, and its entry point is `Tests.DeclineArmMain`.
@[default_target]
lean_lib «Tests.DeclineArmCensus» where
  roots := #[`Tests.DeclineArmCensus]

-- Item 221's census, likewise a library: `Tests.Guards.Proofs.DeclineArmInvariants`
-- imports it, and its entry point is `Tests.DeclineCornerMain`.
@[default_target]
lean_lib «Tests.DeclineCornerCensus» where
  roots := #[`Tests.DeclineCornerCensus]

-- Runnable proof-engineering demonstrations (one per Blueprint Reflection) — kept
-- as a single library, separate from the behavioural L4YAML test suites. See
-- Tests/Reflections.lean for the index.
@[default_target]
lean_lib «Tests.Reflections» where
  roots := #[`Tests.Reflections]

lean_lib «Tests.VerifiedResult» where
  roots := #[`Tests.VerifiedResult]

lean_lib «Tests.SuiteRunner.Meta» where
  roots := #[`Tests.SuiteRunner.Meta]

lean_lib «Tests.SuiteRunner.HtmlReport» where
  roots := #[`Tests.SuiteRunner.HtmlReport]

lean_lib «Tests.Main» where
  roots := #[`Tests.Main]

lean_lib Demo

lean_exe tests where
  root := `Tests.Main.Runner

lean_exe demo where
  root := `Demo.Runner

@[default_target]
lean_exe suiterunner where
  root := `Tests.SuiteRunner.Main

@[default_target]
lean_exe tryparse where
  root := `Tests.TryParse

@[default_target]
lean_exe «l4yaml-event» where
  root := `Tests.EmitEvents

@[default_target]
lean_exe «l4yaml-json» where
  root := `Tests.EmitJson

@[default_target]
lean_exe «l4yaml-event-ix» where
  root := `Tests.EmitEventsIx

@[default_target]
lean_exe «l4yaml-json-ix» where
  root := `Tests.EmitJsonIx

@[default_target]
lean_exe eventscore where
  root := `Tests.SuiteRunner.EventScore

@[default_target]
lean_exe tryscan where
  root := `Tests.TryScan

-- l4yaml-fmt: whitespace-only column aligner for block-mapping values
-- (see L4YAML/Output/Align.lean).
@[default_target]
lean_exe «l4yaml-fmt» where
  root := `Tests.L4YamlFmt

-- aligntest: golden/idempotence/token-shape tests for l4yaml-fmt (Tests/align).
@[default_target]
lean_exe aligntest where
  root := `Tests.AlignTest

-- Item 219: the DECLINE-REACH census (controls + enumerated domain always; the
-- 402-leaf corpus half when the yaml-test-suite data directory is passed).
@[default_target]
lean_exe declinereach where
  root := `Tests.DeclineReachMain

-- Item 220: the ARM census (the row x park matrix, the synthetic-state
-- lattice, and one alphabet per residual zero; the corpus when a data
-- directory is passed).
@[default_target]
lean_exe declinearm where
  root := `Tests.DeclineArmMain

-- Item 221: the MINIMAL-ZERO search — the six-atom histogram over the walk,
-- and for each of item 220's five residual containments the smallest
-- sub-conjunction of its separator profile that still reads zero.
@[default_target]
lean_exe declinecorner where
  root := `Tests.DeclineCornerMain

@[default_target]
lean_exe tryroundtrip where
  root := `Tests.TryRoundTrip

@[default_target]
lean_exe trydump where
  root := `Tests.TryDump

@[default_target]
lean_exe queryresults where
  root := `Tests.QueryResults


lean_lib «Tests.PropertyTests» where
  roots := #[`Tests.PropertyTests]

@[default_target]
lean_exe propertytests where
  root := `Tests.PropertyTests.Runner


lean_lib «Tests.MutationSuiteTests» where
  roots := #[`Tests.MutationSuiteTests]

@[default_target]
lean_exe mutationtests where
  root := `Tests.MutationSuiteTests.Runner


lean_lib «Tests.AdversarialInstantiation» where
  roots := #[`Tests.AdversarialInstantiation]

@[default_target]
lean_exe adversarialinstantiation where
  root := `Tests.AdversarialInstantiation.Runner


lean_lib «Tests.AdversarialGrammarTests» where
  roots := #[`Tests.AdversarialGrammarTests]

@[default_target]
lean_exe adversarialtests where
  root := `Tests.AdversarialGrammarTests.Runner


lean_lib «Tests.ExplicitKeyTests» where
  roots := #[`Tests.ExplicitKeyTests]

@[default_target]
lean_exe explicitkeytests where
  root := `Tests.ExplicitKeyTests.Runner


lean_lib «Tests.FlowTests» where
  roots := #[`Tests.FlowTests]

@[default_target]
lean_exe flowtests where
  root := `Tests.FlowTests.Runner


lean_lib «Tests.ValidationTests» where
  roots := #[`Tests.ValidationTests]

@[default_target]
lean_exe validationtests where
  root := `Tests.ValidationTests.Runner


lean_lib «Tests.LimitTests» where
  roots := #[`Tests.LimitTests]

lean_exe limittests where
  root := `Tests.LimitTests.Runner


@[default_target]
lean_exe flowregressioncheck where
  root := `Tests.FlowRegressionCheck

@[default_target]
lean_exe errorstagediag where
  root := `Tests.ErrorStageDiag

@[default_target]
lean_exe scalarstagediag where
  root := `Tests.ScalarStageDiag


lean_lib «Tests.DumpRoundTrip» where
  roots := #[`Tests.DumpRoundTrip]

@[default_target]
lean_exe dumproundtrip where
  root := `Tests.DumpRoundTrip.Runner


lean_lib «Tests.RawParseTests» where
  roots := #[`Tests.RawParseTests]

@[default_target]
lean_exe rawparsetests where
  root := `Tests.RawParseTests.Runner


lean_lib «Tests.SpecExamples» where
  roots := #[`Tests.SpecExamples]

@[default_target]
lean_exe specexamples where
  root := `Tests.SpecExamples.Runner


lean_exe extractSpecExamples where
  root := `ExtractSpecExamples
  srcDir := "tools"

lean_exe «collect-stats» where
  root := `CollectStats
  srcDir := "tools"


lean_lib «Tests.SchemaDump» where
  roots := #[`Tests.SchemaDump]

@[default_target]
lean_exe schemadump where
  root := `Tests.SchemaDump.Runner

-- A `module` consumer of the library that derives `FromYaml`/`ToYaml` on
-- private-named types through a plain `public import L4YAML`.
lean_lib «Tests.DerivingConsumer» where
  roots := #[`Tests.DerivingConsumer]

@[default_target]
lean_exe derivingconsumer where
  root := `Tests.DerivingConsumer.Runner


lean_lib «Tests.ScannerTests» where
  roots := #[`Tests.ScannerTests]

@[default_target]
lean_exe scannertests where
  root := `Tests.ScannerTests.Runner


lean_lib «Tests.ScannerSpecExamples» where
  roots := #[`Tests.ScannerSpecExamples]

@[default_target]
lean_exe scannerspecexamples where
  root := `Tests.ScannerSpecExamples.Runner


lean_lib «Tests.ProductionCoverage» where
  roots := #[`Tests.ProductionCoverage]

@[default_target]
lean_exe productioncoverage where
  root := `Tests.ProductionCoverage.Runner


-- Rule 9 (Blueprint/06-discipline.md): scripts are Lean.  `Scripts` holds the
-- pure halves (parsers, checks, with their `#guard` rows); each `lean_exe
-- scripts-*` is one `Scripts/Main/*.lean` driver that scripts/*.sh wraps.
-- Plan and ledger: Blueprint/09-scripts-in-lean.md, scripts/scripts-ledger.txt.
@[default_target]
lean_lib Scripts where
  requiresModuleSystem := true

-- Phase 0: the ledger gate behind `lake run check-scripts-lean`.
@[default_target]
lean_exe «scripts-check-ledger» where
  root := `Scripts.Main.CheckScriptsLedger

-- Phase 2.1: flip_census.py and repin.py.
@[default_target]
lean_exe «scripts-flip-census» where
  root := `Scripts.Main.FlipCensus

@[default_target]
lean_exe «scripts-repin» where
  root := `Scripts.Main.Repin

-- Phase 3.1: the shared flip library behind the flip_*.py scripts.
@[default_target]
lean_exe «scripts-flip» where
  root := `Scripts.Main.Flip

-- Phase 1: the class-G gates (`lake run check-…`).
@[default_target]
lean_exe «scripts-theorem-keyword» where
  root := `Scripts.Main.TheoremKeyword

@[default_target]
lean_exe «scripts-check-import-closure» where
  root := `Scripts.Main.CheckImportClosure
  supportInterpreter := true

@[default_target]
lean_exe «scripts-check-reflection-index» where
  root := `Scripts.Main.CheckReflectionIndex

@[default_target]
lean_exe «scripts-check-closure-log» where
  root := `Scripts.Main.CheckClosureLog

/-! Phase 4.5 (Rule 9, Q7): portable entry points — `lake run <name>` replaces the
bash wrappers that only run a `lean_exe`; same on Linux, macOS and Windows. -/

/-- A gate behind `lake run <name> [-- ARGS]`: `lake build <exe> <prereqs>`, then run
`.lake/build/bin/<exe>` with `-C <repo root>` (unless the caller passes
`-C`/`--root`), `fixed` first, then ARGS; the exit status is the exe's (2 when
the build fails).  `lake run name -- ARGS` forwards the `--`, dropped here. -/
def runGateExe (root : System.FilePath) (exe : String) (fixed : Array String)
    (args : List String) (prereqs : Array String := #[]) : IO UInt32 := do
  let build ← IO.Process.output { cmd := "lake", args := #["build", exe] ++ prereqs, cwd := some root }
  if build.exitCode != 0 then
    IO.eprintln build.stdout; IO.eprintln build.stderr
    IO.eprintln s!"lake run: lake build {exe} {" ".intercalate prereqs.toList} failed"
    return 2
  let args := if args.headD "" == "--" then args.drop 1 else args
  let hasRoot := args.any fun a => a == "-C" || a == "--root"
  let argv := (if hasRoot then #[] else #["-C", root.toString]) ++ fixed ++ args.toArray
  let child ← IO.Process.spawn { cmd := (root / ".lake" / "build" / "bin" / exe).toString, args := argv }
  child.wait

/-- The Rule 9 ledger gate: `lake run check-scripts-lean [-- ARGS]`
(`scripts/check-scripts-lean.sh` before 4.5). -/
script «check-scripts-lean» (args) do
  runGateExe (← getWorkspace).root.dir "scripts-check-ledger" #[] args

/-- Rule 7: `theorem` only on `scripts/capstones.txt` entries
(`scripts/check-theorem-keyword.sh` before phase 1). -/
script «check-theorem-keyword» (args) do
  runGateExe (← getWorkspace).root.dir "scripts-theorem-keyword" #["--check", "L4YAML"] args

/-- No orphan `L4YAML/**` module, every `Tests/Reflections/*` indexed
(`scripts/check-import-closure.sh` before phase 1).  Reads `.olean` headers,
so the default-target roots are built first (a no-op when up to date). -/
script «check-import-closure» (args) do
  runGateExe (← getWorkspace).root.dir "scripts-check-import-closure" #[] args
    #["L4YAML", "l4yaml-event", "l4yaml-json", "l4yaml-event-ix", "l4yaml-json-ix"]

/-- The Reflections index's narrative half matches its bullets
(`scripts/check-reflection-index.sh` before phase 1). -/
script «check-reflection-index» (args) do
  runGateExe (← getWorkspace).root.dir "scripts-check-reflection-index" #[] args

/-- DOCS.md closure-log items ascend, dated, gaps declared
(`scripts/check-closure-log.sh` before phase 1). -/
script «check-closure-log» (args) do
  runGateExe (← getWorkspace).root.dir "scripts-check-closure-log" #[] args

/-- Every test exe, output captured under OUT (default `docs`), failures
collected: `lake run run-all-tests [-- OUT]` (`scripts/run-all-tests.sh`
before 4.5). Exit 1 when any suite or the suiterunner HTML report failed. -/
script «run-all-tests» (args) do
  let ws ← getWorkspace
  let root := ws.root.dir
  let args := if args.headD "" == "--" then args.drop 1 else args
  let outArg : System.FilePath := args.headD "docs"
  let out := if outArg.isAbsolute then outArg else root / outArg
  IO.FS.createDirAll out
  let bin := root / ".lake" / "build" / "bin"
  let suites : Array (String × String) := #[
    ("unit-tests", "tests"), ("demo", "demo"), ("explicitkeytests", "explicitkeytests"),
    ("flowtests", "flowtests"), ("validationtests", "validationtests"), ("dumproundtrip", "dumproundtrip"),
    ("rawparsetests", "rawparsetests"), ("specexamples", "specexamples"), ("schemadump", "schemadump"),
    ("derivingconsumer", "derivingconsumer"), ("scannertests", "scannertests"),
    ("scannerspecexamples", "scannerspecexamples"), ("adversarialtests", "adversarialtests"),
    ("mutationtests", "mutationtests"), ("propertytests", "propertytests"),
    ("productioncoverage", "productioncoverage"), ("limittests", "limittests"),
    ("flowregressioncheck", "flowregressioncheck"), ("errorstagediag", "errorstagediag"),
    ("scalarstagediag", "scalarstagediag"), ("aligntest", "aligntest")]
  let mut failed : Array String := #[]
  for (name, exe) in suites do
    IO.println s!"=== Running: {name} ==="
    let r ← try
        IO.Process.output { cmd := (bin / exe).toString, cwd := some root }
      catch e => pure { exitCode := 127, stdout := "", stderr := s!"{e}\n" }
    let text := r.stdout ++ r.stderr
    IO.print text
    IO.FS.writeFile (out / s!"{name}.txt") (s!"=== {name} ===\n" ++ text)
    if r.exitCode != 0 then failed := failed.push name
    IO.println ""
  IO.println "=== Generating HTML coverage reports ==="
  let h ← try
      IO.Process.output { cmd := (bin / "suiterunner").toString, args := #["--html", out.toString ++ "/"], cwd := some root }
    catch e => pure { exitCode := 127, stdout := "", stderr := s!"{e}\n" }
  IO.print h.stdout; IO.eprint h.stderr
  IO.FS.writeFile (out / "coverage-console.txt") h.stdout
  if h.exitCode != 0 then failed := failed.push "suiterunner-html"
  let verified := suites.extract 0 17   -- the 17 verified suites, unit-tests … limittests
  let mut all := ""
  for (name, _) in verified do
    all := all ++ (← IO.FS.readFile (out / s!"{name}.txt"))
  IO.FS.writeFile (out / "all-verified-tests.txt") all
  if !failed.isEmpty then
    IO.eprintln s!"=== FAILED suites ({failed.size}): {" ".intercalate failed.toList} ==="
    return 1
  IO.println s!"=== All Lean test suites complete. Results in {out}/ ==="
  return 0
