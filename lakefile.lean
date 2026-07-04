import Lake
open Lake DSL

/-- Link CTranslate2 into L4YAML binaries only on explicit request
    (`lake build -Kleancopilot=on`) — needed only if an exe/dynlib of THIS package
    imports LeanCopilot. Interactive `suggest_tactics` in the editor does NOT need
    it (LeanCopilot's own precompiled module dynlibs carry the FFI); linking it
    unconditionally gives every exe a runtime dependency on libctranslate2.so.4
    (+ GLIBCXX_3.4.30 via the pixi env), breaking them outside `pixi run`. -/
def leanCopilotLinkArgs : Array String :=
  if (get_config? leancopilot).isSome then
    #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
  else
    #[]

package L4YAML where
  version := v!"0.5.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  moreLinkArgs := leanCopilotLinkArgs

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.31.0"

require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "v4.31.0"

require DocGen4 from git
  "https://github.com/leanprover/doc-gen4.git" @ "v4.31.0"


@[default_target]
lean_lib L4YAML

@[default_target]
lean_lib «Tests.Guards» where
  roots := #[`Tests.Guards]

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
lean_exe eventscore where
  root := `Tests.SuiteRunner.EventScore

@[default_target]
lean_exe tryscan where
  root := `Tests.TryScan

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
