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
def statsJson? : Option String := none

end Doc.L4YAML.StatsData
