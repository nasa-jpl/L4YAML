/-
  Doc.L4YAML.StatsData — embedded `stats.json` payload for `:::statsTable`.

  GENERATED FILE — regenerate with `lake exe collect-stats --emit-lean`
  (repo root). The COMMITTED version is a deliberate placeholder (`none`):
  the at-a-glance table renders every cell as "?" so a fresh clone builds
  the docs hermetically without running collect-stats first.

  CI regenerates this file (workspace-only, never committed back) after
  the test suites and right before the doc build, so the published site
  always embeds the current run's stats. Because `StatsTable` IMPORTS
  this module instead of reading `docs/reports/stats.json` at elaboration
  time, the dependency is visible to Lake: a content change re-elaborates
  exactly the importing `Doc.*` modules — no IO at elaboration, no hidden
  staleness if `.lake` caching is ever enabled.
-/

namespace Doc.L4YAML.StatsData

/-- Compact `stats.json` payload embedded at generation time;
    `none` in the committed placeholder (every table cell renders "?"). -/
def statsJson? : Option String := some "{\"build_jobs\":null,\"env\":{\"axioms\":0,\"custom_axiom_names\":[],\"theorems\":9145,\"theorems_with_custom_axiom\":0,\"theorems_with_direct_sorry\":0,\"theorems_with_transitive_sorry\":0},\"generated_at_ms\":4158185817,\"schema_version\":2,\"spec_examples\":{\"passed\":132,\"total\":132},\"static\":{\"library\":{\"axioms\":0,\"guards\":10,\"lean_files\":242,\"lemmas\":7158,\"lines\":250032,\"partial_defs\":8,\"theorems\":52,\"theorems_plus_lemmas\":7210},\"proofs\":{\"axioms\":0,\"guards\":7,\"lean_files\":174,\"lemmas\":6958,\"lines\":223402,\"partial_defs\":0,\"theorems\":46,\"theorems_plus_lemmas\":7004},\"tests\":{\"axioms\":3,\"guards\":7600,\"lean_files\":671,\"lemmas\":200,\"lines\":147127,\"partial_defs\":152,\"theorems\":2623,\"theorems_plus_lemmas\":2823}},\"test_suites\":{\"suite_count\":15,\"suites\":[{\"name\":\"unit-tests\",\"passed\":10,\"total\":10},{\"name\":\"explicit-key-tests\",\"passed\":149,\"total\":149},{\"name\":\"flow-tests\",\"passed\":88,\"total\":88},{\"name\":\"validation-tests\",\"passed\":84,\"total\":84},{\"name\":\"dump-roundtrip\",\"passed\":117,\"total\":117},{\"name\":\"raw-parse-tests\",\"passed\":29,\"total\":29},{\"name\":\"scanner-tests\",\"passed\":55,\"total\":55},{\"name\":\"scanner-spec-examples\",\"passed\":132,\"total\":132},{\"name\":\"adversarial-tests\",\"passed\":159,\"total\":159},{\"name\":\"mutation-tests\",\"passed\":45,\"total\":45},{\"name\":\"property-tests\",\"passed\":124,\"total\":124},{\"name\":\"production-coverage\",\"passed\":838,\"total\":838},{\"name\":\"limit-tests\",\"passed\":43,\"total\":43},{\"name\":\"schema-dump\",\"passed\":68,\"total\":68},{\"name\":\"demo\",\"passed\":7,\"total\":7}],\"total_passed\":1948,\"total_tests\":1948},\"yaml_test_suite\":{\"applicable\":358,\"correct\":358,\"correctRate\":100,\"expectedFail\":95,\"failed\":0,\"passed\":263,\"skipped\":48,\"timeout\":0,\"total\":406,\"unexpectedPass\":0}}"

end Doc.L4YAML.StatsData
