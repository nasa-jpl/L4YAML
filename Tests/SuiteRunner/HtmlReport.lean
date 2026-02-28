import Lean.Data.Json
import Tests.SuiteRunner.Meta
import Tests.VerifiedResult

/-!
# HTML Coverage Report Generator

Generates interactive HTML coverage reports for yaml-test-suite results,
with filtering by stage/outcome, sortable tables, and summary statistics.

Adapted from lean4-yaml's TestCoverageReport.lean for lean4-yaml-verified.
-/

namespace Tests.SuiteRunner

/-- GitHub blob base URL for source file links. -/
def repoSourceUrl : String :=
  "https://github.jpl.nasa.gov/pass/lean4-yaml-verified/blob/main/"

/-- yaml-test-suite source file URL base (public GitHub). -/
def yamlTestSuiteUrl : String :=
  "https://github.com/yaml/yaml-test-suite/blob/main/src/"

/-! ## Test Result Data for Reports -/

/-- Outcome of a single test case for reporting purposes. -/
inductive TestOutcome where
  | pass              -- parsed successfully (expected to pass)
  | fail              -- parse error (expected to pass)
  | expectedFail      -- parse error (expected to fail) → correct
  | unexpectedPass    -- parsed successfully (expected to fail) → incorrect
  | skip (reason : String)
  | timeout           -- timed out (possible infinite loop)
  deriving Repr, BEq

/-- A test result with its case and outcome. -/
structure ReportResult where
  testCase : TestCase
  outcome : TestOutcome
  errorMsg : Option String := none
  deriving Repr

/-- Summary statistics for a group of results. -/
structure CoverageStats where
  total : Nat
  applicable : Nat
  passed : Nat
  failed : Nat
  expectedFail : Nat
  unexpectedPass : Nat
  skipped : Nat
  timeout : Nat
  deriving Repr

def CoverageStats.fromResults (results : Array ReportResult) : CoverageStats :=
  let passed := results.filter (fun r => r.outcome == .pass) |>.size
  let failed := results.filter (fun r => r.outcome == .fail) |>.size
  let expectedFail := results.filter (fun r => r.outcome == .expectedFail) |>.size
  let unexpectedPass := results.filter (fun r => r.outcome == .unexpectedPass) |>.size
  let skipped := results.filter (fun r => match r.outcome with | .skip _ => true | _ => false) |>.size
  let timeout := results.filter (fun r => r.outcome == .timeout) |>.size
  { total := results.size
    applicable := results.size - skipped
    passed := passed
    failed := failed
    expectedFail := expectedFail
    unexpectedPass := unexpectedPass
    skipped := skipped
    timeout := timeout }

def CoverageStats.correctCount (s : CoverageStats) : Nat :=
  s.passed + s.expectedFail

def CoverageStats.successRate (s : CoverageStats) : Float :=
  if s.applicable == 0 then 0.0
  else (s.correctCount.toFloat / s.applicable.toFloat) * 100.0

/-- Format a percentage to 1 decimal place.  Returns e.g. "75.4" or "100.0". -/
private def formatPct (pct : Float) : String :=
  -- Multiply by 10, round, then format as "integer.digit"
  let scaled := (pct * 10.0 + 0.5).floor.toUInt64.toNat
  let whole := scaled / 10
  let frac  := scaled % 10
  s!"{whole}.{frac}"

/-! ## JSON Summary — Lean.Data.Json serialization -/

open Lean in
instance : ToJson TestOutcome where
  toJson
    | .pass           => "pass"
    | .fail           => "fail"
    | .expectedFail   => "expected-fail"
    | .unexpectedPass => "unexpected-pass"
    | .skip _         => "skip"
    | .timeout        => "timeout"

open Lean in
instance : ToJson Stage where
  toJson
    | .scalar   => "scalar"
    | .flow     => "flow"
    | .block    => "block"
    | .document => "document"
    | .advanced => "advanced"
    | .error    => "error"
    | .all      => "all"

/-- Convert a ratio to a `JsonNumber` with fixed decimal precision.
    `ratioPercent num denom scale` computes `(num / denom) × 100`
    with `scale` decimal digits (default 6). -/
private def ratioPercent (num denom : Nat) (scale : Nat := 1) : Lean.JsonNumber :=
  if denom == 0 then { mantissa := 0, exponent := scale }
  else { mantissa := (num * 100 * (10 ^ scale) / denom : Nat), exponent := scale }

open Lean in
instance : ToJson CoverageStats where
  toJson s := Json.mkObj [
    ("total",          toJson s.total),
    ("applicable",     toJson s.applicable),
    ("passed",         toJson s.passed),
    ("failed",         toJson s.failed),
    ("expectedFail",   toJson s.expectedFail),
    ("unexpectedPass", toJson s.unexpectedPass),
    ("skipped",        toJson s.skipped),
    ("timeout",        toJson s.timeout),
    ("correct",        toJson s.correctCount),
    ("correctRate",    Json.num (ratioPercent s.correctCount s.applicable))
  ]

/-- JSON-serializable per-test entry. -/
structure JsonTestEntry where
  id      : String
  name    : String
  stage   : Stage
  outcome : TestOutcome
  error   : Option String := none
  deriving Lean.ToJson

/-- JSON-serializable verified-suite summary row. -/
structure JsonVerifiedSuite where
  label   : String
  passed  : Nat
  total   : Nat
  allPass : Bool
  deriving Lean.ToJson

/-- JSON-serializable verified section (aggregate + per-suite). -/
structure JsonVerifiedSection where
  totalPassed : Nat
  totalTests  : Nat
  suites      : Array JsonVerifiedSuite
  deriving Lean.ToJson

/-- Standard 2-space-indented JSON pretty printer.
    Lean's built-in `Json.pretty` uses `Format` (width-based line breaking)
    which produces non-standard indentation.  This gives conventional output
    suitable for `jq`, `python -m json.tool`, etc. -/
private partial def jsonPretty (j : Lean.Json) (indent : Nat := 0) : String :=
  let pad  := "".pushn ' ' (indent * 2)
  let pad1 := "".pushn ' ' ((indent + 1) * 2)
  match j with
  | .null   => "null"
  | .bool b => if b then "true" else "false"
  | .num n  => toString n
  | .str s  => Lean.Json.renderString s
  | .arr items =>
    if items.isEmpty then "[]"
    else
      let elems := items.toList.map fun v => pad1 ++ jsonPretty v (indent + 1)
      "[\n" ++ String.intercalate ",\n" elems ++ "\n" ++ pad ++ "]"
  | .obj fields =>
    if fields.isEmpty then "{}"
    else
      let entries := fields.toList.map fun (k, v) =>
        pad1 ++ Lean.Json.renderString k ++ ": " ++ jsonPretty v (indent + 1)
      "{\n" ++ String.intercalate ",\n" entries ++ "\n" ++ pad ++ "}"

/-- Generate a machine-readable JSON summary of test results.
    Includes per-stage breakdown, per-test outcomes, and verified suite totals.
    Designed to be consumed by CI scripts, documentation updaters, and analysis
    tools. -/
def generateJsonSummary (results : Array ReportResult) (dateStamp : String)
    (verifiedSuites : Option (Array Tests.VerifiedSuiteResult) := none) : String :=
  open Lean in
  -- Per-stage stats
  let stages : List Stage := [.scalar, .flow, .block, .document, .advanced, .error]
  let stageFields := stages.map fun stage =>
    let stageResults := results.filter (fun r => r.testCase.stage == stage)
    (toString stage, toJson (CoverageStats.fromResults stageResults))
  -- Per-test entries
  let testEntries := results.map fun r =>
    toJson ({ id      := r.testCase.id
              name    := r.testCase.name
              stage   := r.testCase.stage
              outcome := r.outcome
              error   := r.errorMsg : JsonTestEntry })
  -- Optional verified section
  let verifiedField := match verifiedSuites with
    | some suites =>
      let totalPassed := suites.foldl (fun acc s => acc + s.passed) 0
      let totalTests  := suites.foldl (fun acc s => acc + s.total) 0
      let jsonSuites  := suites.map fun s =>
        ({ label := s.label, passed := s.passed,
           total := s.total, allPass := s.allPass : JsonVerifiedSuite })
      [("verified", toJson ({ totalPassed, totalTests,
                              suites := jsonSuites : JsonVerifiedSection }))]
    | none => []
  -- Assemble top-level object
  let root := Json.mkObj <|
    [ ("date",    toJson dateStamp),
      ("overall", toJson (CoverageStats.fromResults results)),
      ("stages",  Json.mkObj stageFields),
      ("tests",   Json.arr testEntries) ] ++ verifiedField
  jsonPretty root

/-! ## Verified Test Suites — types from Tests.VerifiedResult -/

-- Re-exported from Tests.VerifiedResult:
-- VerifiedOutcome, VerifiedTestCase, VerifiedSuiteResult

/-! ## HTML Helpers -/

private def escapeHtml (s : String) : String :=
  s.replace "&" "&amp;"
   |>.replace "<" "&lt;"
   |>.replace ">" "&gt;"
   |>.replace "\"" "&quot;"
   |>.replace "'" "&#39;"

private def outcomeClass : TestOutcome → String
  | .pass => "pass"
  | .fail => "fail"
  | .expectedFail => "expected-fail"
  | .unexpectedPass => "unexpected-pass"
  | .skip _ => "skip"
  | .timeout => "timeout"

private def outcomeBadge : TestOutcome → String
  | .pass => "<span class=\"badge badge-pass\">Pass</span>"
  | .fail => "<span class=\"badge badge-fail\">Fail</span>"
  | .expectedFail => "<span class=\"badge badge-expected-fail\">Expected Fail</span>"
  | .unexpectedPass => "<span class=\"badge badge-unexpected-pass\">Unexpected Pass</span>"
  | .skip reason => s!"<span class=\"badge badge-skip\" title=\"{escapeHtml reason}\">Skip</span>"
  | .timeout => "<span class=\"badge badge-timeout\">Timeout</span>"

/-! ## CSS -/

private def reportCss : String :=
  "    :root {
      --color-pass: #4CAF50;
      --color-fail: #f44336;
      --color-expected-fail: #2196F3;
      --color-unexpected-pass: #ff9800;
      --color-skip: #9e9e9e;
      --color-timeout: #9c27b0;
    }
    * { box-sizing: border-box; }
    body {
      font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
      margin: 0; padding: 20px; background: #f5f5f5;
    }
    .container {
      max-width: 1400px; margin: 0 auto; background: white;
      padding: 30px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); border-radius: 8px;
    }
    h1 { color: #333; border-bottom: 3px solid var(--color-pass); padding-bottom: 10px; margin-top: 0; }
    h2 { color: #4CAF50; margin-top: 30px; }
    h3 { color: #555; }
    .subtitle { color: #666; font-size: 16px; margin-bottom: 30px; }

    /* Stats grid */
    .stats {
      display: grid; grid-template-columns: repeat(auto-fit, minmax(160px, 1fr));
      gap: 15px; margin: 25px 0;
    }
    .stat-box {
      color: white; padding: 20px; border-radius: 8px; text-align: center;
      box-shadow: 0 4px 6px rgba(0,0,0,0.1);
    }
    .stat-box h3 { margin: 0 0 8px 0; font-size: 13px; opacity: 0.9; color: white; }
    .stat-box .number { font-size: 32px; font-weight: bold; }
    .stat-box .pct { font-size: 14px; margin-top: 4px; opacity: 0.9; }
    .stat-total { background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); }
    .stat-pass { background: linear-gradient(135deg, #4CAF50 0%, #45a049 100%); }
    .stat-fail { background: linear-gradient(135deg, #f44336 0%, #d32f2f 100%); }
    .stat-expected { background: linear-gradient(135deg, #2196F3 0%, #1976D2 100%); }
    .stat-unexpected { background: linear-gradient(135deg, #ff9800 0%, #f57c00 100%); }
    .stat-skip { background: linear-gradient(135deg, #9e9e9e 0%, #757575 100%); }
    .stat-timeout { background: linear-gradient(135deg, #9c27b0 0%, #7b1fa2 100%); }
    .stat-correct { background: linear-gradient(135deg, #00bcd4 0%, #0097a7 100%); }

    /* Stage breakdown cards */
    .stage-cards {
      display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr));
      gap: 15px; margin: 20px 0;
    }
    .stage-card {
      background: #f8f9fa; padding: 18px; border-radius: 6px;
      border-left: 4px solid var(--color-pass);
    }
    .stage-card-name { font-weight: 600; font-size: 16px; color: #333; margin-bottom: 8px; }
    .stage-card-stats { color: #666; font-size: 14px; }
    .stage-bar {
      height: 8px; background: #e0e0e0; border-radius: 4px; margin-top: 10px; overflow: hidden;
      display: flex;
    }
    .stage-bar-fill {
      height: 100%; background: var(--color-pass); border-radius: 4px;
      transition: width 0.3s ease;
    }
    .stage-bar-segment {
      height: 100%; min-width: 4px; transition: flex-grow 0.3s ease;
    }
    .stage-bar-segment:first-child { border-radius: 4px 0 0 4px; }
    .stage-bar-segment:last-child { border-radius: 0 4px 4px 0; }
    .stage-bar-segment:only-child { border-radius: 4px; }

    /* Filters */
    .filters {
      background: #f8f9fa; padding: 15px; border-radius: 6px;
      margin: 20px 0; display: flex; gap: 20px; flex-wrap: wrap; align-items: center;
    }
    .filter-group { display: flex; align-items: center; gap: 8px; }
    .filter-group label { font-weight: 600; color: #555; font-size: 14px; }
    .filter-btn {
      padding: 6px 14px; border: 2px solid #ddd; background: white;
      border-radius: 4px; cursor: pointer; transition: all 0.2s; font-size: 13px;
    }
    .filter-btn:hover { border-color: #4CAF50; }
    .filter-btn.active { background: #4CAF50; color: white; border-color: #4CAF50; }
    select {
      padding: 6px 12px; border: 2px solid #ddd; border-radius: 4px; font-size: 13px;
    }
    .search-input {
      padding: 6px 12px; border: 2px solid #ddd; border-radius: 4px;
      font-size: 13px; width: 200px;
    }
    .search-input:focus { border-color: #4CAF50; outline: none; }

    /* Table */
    table {
      width: 100%; border-collapse: collapse; margin: 20px 0;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    th {
      background: #4CAF50; color: white; padding: 10px 12px; text-align: left;
      font-weight: 600; position: sticky; top: 0; cursor: pointer;
      user-select: none; font-size: 13px;
    }
    th:hover { background: #45a049; }
    th .sort-arrow { margin-left: 4px; opacity: 0.5; }
    th.sorted .sort-arrow { opacity: 1; }
    td { padding: 8px 12px; border-bottom: 1px solid #e0e0e0; font-size: 13px; }
    tr:hover { background: #f5f5f5; }
    tr.hidden { display: none; }

    /* Badges */
    .badge {
      display: inline-block; padding: 3px 10px; border-radius: 12px;
      font-size: 11px; font-weight: 600; color: white;
    }
    .badge-pass { background: var(--color-pass); }
    .badge-fail { background: var(--color-fail); }
    .badge-expected-fail { background: var(--color-expected-fail); }
    .badge-unexpected-pass { background: var(--color-unexpected-pass); }
    .badge-skip { background: var(--color-skip); }
    .badge-timeout { background: var(--color-timeout); }

    /* Test ID links */
    .test-id-link {
      color: #1565C0; text-decoration: none; font-family: 'Courier New', monospace; font-weight: 600;
    }
    .test-id-link:hover { text-decoration: underline; }

    /* Tags */
    .tag {
      display: inline-block; background: #e3f2fd; color: #1565C0;
      padding: 2px 8px; border-radius: 10px; font-size: 11px;
      margin: 1px 2px; white-space: nowrap;
    }

    /* Error message */
    .error-msg {
      color: #d32f2f; font-size: 11px; font-family: 'Courier New', monospace;
      max-width: 400px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
    }
    .error-msg:hover { white-space: normal; word-break: break-all; }

    /* Navigation */
    .nav-link {
      display: inline-block; margin-bottom: 20px; color: #2196F3;
      text-decoration: none; font-size: 14px;
    }
    .nav-link:hover { text-decoration: underline; }

    /* Footer */
    footer {
      margin-top: 40px; text-align: center; color: #999; font-size: 13px;
      border-top: 1px solid #e0e0e0; padding-top: 20px;
    }
    footer a { color: #2196F3; text-decoration: none; }
    footer a:hover { text-decoration: underline; }

    /* Responsive */
    @media (max-width: 768px) {
      body { padding: 10px; }
      .container { padding: 15px; }
      .filters { flex-direction: column; gap: 10px; }
      .stats { grid-template-columns: repeat(2, 1fr); }
    }
"

/-! ## JavaScript -/

private def reportJs : String :=
  "
    // State
    let currentOutcomeFilter = 'all';
    let currentStageFilter = 'all';
    let currentSearchText = '';
    let sortColumn = 0;
    let sortAscending = true;

    // Filter by outcome
    function filterByOutcome(outcome) {
      currentOutcomeFilter = outcome;
      document.querySelectorAll('.filter-outcome .filter-btn').forEach(btn => btn.classList.remove('active'));
      event.target.classList.add('active');
      applyFilters();
    }

    // Filter by stage
    function filterByStage(stage) {
      currentStageFilter = stage;
      applyFilters();
    }

    // Search
    function searchTests(text) {
      currentSearchText = text.toLowerCase();
      applyFilters();
    }

    // Apply all filters
    function applyFilters() {
      const rows = document.querySelectorAll('.test-row');
      let visible = 0;
      rows.forEach(row => {
        const outcome = row.dataset.outcome;
        const stage = row.dataset.stage;
        const search = row.dataset.search;

        const outcomeMatch = currentOutcomeFilter === 'all' || outcome === currentOutcomeFilter;
        const stageMatch = currentStageFilter === 'all' || stage === currentStageFilter;
        const searchMatch = currentSearchText === '' || search.includes(currentSearchText);

        if (outcomeMatch && stageMatch && searchMatch) {
          row.classList.remove('hidden');
          visible++;
        } else {
          row.classList.add('hidden');
        }
      });
      document.getElementById('visibleCount').textContent = visible;
    }

    // Sort table
    function sortTable(colIdx) {
      const table = document.getElementById('testTable');
      const tbody = table.querySelector('tbody');
      const rows = Array.from(tbody.querySelectorAll('.test-row'));

      if (sortColumn === colIdx) {
        sortAscending = !sortAscending;
      } else {
        sortColumn = colIdx;
        sortAscending = true;
      }

      // Update header arrows
      table.querySelectorAll('th').forEach((th, i) => {
        th.classList.remove('sorted');
        const arrow = th.querySelector('.sort-arrow');
        if (arrow) arrow.textContent = '↕';
      });
      const th = table.querySelectorAll('th')[colIdx];
      th.classList.add('sorted');
      const arrow = th.querySelector('.sort-arrow');
      if (arrow) arrow.textContent = sortAscending ? '↑' : '↓';

      rows.sort((a, b) => {
        let aVal = a.children[colIdx]?.textContent.trim() || '';
        let bVal = b.children[colIdx]?.textContent.trim() || '';
        // Try numeric sort
        const aNum = parseFloat(aVal);
        const bNum = parseFloat(bVal);
        if (!isNaN(aNum) && !isNaN(bNum)) {
          return sortAscending ? aNum - bNum : bNum - aNum;
        }
        return sortAscending ? aVal.localeCompare(bVal) : bVal.localeCompare(aVal);
      });

      rows.forEach(row => tbody.appendChild(row));
    }
  "

/-! ## Report Generation -/

/-- Generate the stats boxes HTML. -/
private def generateStatsHtml (stats : CoverageStats) : String :=
  let pctStr := formatPct stats.successRate
  String.join [
    "  <div class=\"stats\">\n",
    s!"    <div class=\"stat-box stat-total\"><h3>Unique Tests</h3><div class=\"number\">{stats.total}</div></div>\n",
    s!"    <div class=\"stat-box stat-pass\"><h3>Passed</h3><div class=\"number\">{stats.passed}</div></div>\n",
    s!"    <div class=\"stat-box stat-fail\"><h3>Failed</h3><div class=\"number\">{stats.failed}</div></div>\n",
    s!"    <div class=\"stat-box stat-expected\"><h3>Expected Fail</h3><div class=\"number\">{stats.expectedFail}</div></div>\n",
    s!"    <div class=\"stat-box stat-unexpected\"><h3>Unexpected Pass</h3><div class=\"number\">{stats.unexpectedPass}</div></div>\n",
    s!"    <div class=\"stat-box stat-skip\"><h3>Skipped (1.3)</h3><div class=\"number\">{stats.skipped}</div></div>\n",
    s!"    <div class=\"stat-box stat-timeout\"><h3>Timeout</h3><div class=\"number\">{stats.timeout}</div></div>\n",
    s!"    <div class=\"stat-box stat-correct\"><h3>Correct</h3><div class=\"number\">{stats.correctCount}/{stats.applicable}</div><div class=\"pct\">({pctStr}%)</div></div>\n",
    "  </div>\n"
  ]

/-- Generate a multi-segment bar for a stage, one segment per non-zero category.
    Each segment uses `flex: count 0 0px` for proportional sizing with `min-width: 4px`
    guaranteeing visibility even for count=1 categories. -/
private def generateStageBarSegments (stats : CoverageStats) : String :=
  -- Display order: pass (green), expected-fail (blue), fail (red),
  --   unexpected-pass (orange), skip (gray), timeout (purple)
  let categories : Array (String × String × Nat) := #[
    ("pass",            "var(--color-pass)",            stats.passed),
    ("expected fail",   "var(--color-expected-fail)",    stats.expectedFail),
    ("fail",            "var(--color-fail)",             stats.failed),
    ("unexpected pass", "var(--color-unexpected-pass)",  stats.unexpectedPass),
    ("skip",            "var(--color-skip)",             stats.skipped),
    ("timeout",         "var(--color-timeout)",          stats.timeout)
  ]
  let segments := categories.filter (fun (_, _, n) => n > 0)
  let html := segments.map fun (label, color, count) =>
    s!"<div class=\"stage-bar-segment\" style=\"flex: {count} 0 0px; background: {color}\" title=\"{count} {label}\"></div>"
  String.join html.toList

/-- Generate stage breakdown cards. -/
private def generateStageCardsHtml (results : Array ReportResult) : String :=
  let stages : Array Stage := #[.scalar, .flow, .block, .document, .advanced, .error]
  let cards := stages.map fun stage =>
    let stageResults := results.filter (fun r => r.testCase.stage == stage)
    let stats := CoverageStats.fromResults stageResults
    let pct := if stats.applicable == 0 then 0.0
               else (stats.correctCount.toFloat / stats.applicable.toFloat) * 100.0
    let pctStr := formatPct pct
    let barSegments := generateStageBarSegments stats
    let skipNote := if stats.skipped > 0 then s!" · {stats.skipped} YAML 1.3 skipped" else ""
    s!"    <div class=\"stage-card\">\n" ++
    s!"      <div class=\"stage-card-name\">{stage}</div>\n" ++
    s!"      <div class=\"stage-card-stats\">{stats.correctCount}/{stats.applicable} correct ({pctStr}%) · {stats.passed} pass, {stats.failed} fail, {stats.expectedFail} exp-fail, {stats.unexpectedPass} unexp-pass{skipNote}, {stats.timeout} timeout</div>\n" ++
    s!"      <div class=\"stage-bar\">{barSegments}</div>\n" ++
    s!"    </div>\n"
  String.join [
    "  <h3>Coverage by Stage</h3>\n",
    "  <div class=\"stage-cards\">\n",
    String.join cards.toList,
    "  </div>\n"
  ]

/-- Generate the filter bar. -/
private def generateFiltersHtml (totalCount : Nat) : String :=
  String.join [
    "  <div class=\"filters\">\n",
    "    <div class=\"filter-group filter-outcome\">\n",
    "      <label>Outcome:</label>\n",
    "      <button class=\"filter-btn active\" onclick=\"filterByOutcome('all')\">All</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByOutcome('pass')\">Pass</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByOutcome('fail')\">Fail</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByOutcome('expected-fail')\">Exp Fail</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByOutcome('unexpected-pass')\">Unexp Pass</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByOutcome('skip')\">Skip</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByOutcome('timeout')\">Timeout</button>\n",
    "    </div>\n",
    "    <div class=\"filter-group\">\n",
    "      <label>Stage:</label>\n",
    "      <select onchange=\"filterByStage(this.value)\">\n",
    "        <option value=\"all\">All Stages</option>\n",
    "        <option value=\"scalar\">Scalar</option>\n",
    "        <option value=\"flow\">Flow</option>\n",
    "        <option value=\"block\">Block</option>\n",
    "        <option value=\"document\">Document</option>\n",
    "        <option value=\"advanced\">Advanced</option>\n",
    "        <option value=\"error\">Error</option>\n",
    "      </select>\n",
    "    </div>\n",
    "    <div class=\"filter-group\">\n",
    "      <label>Search:</label>\n",
    "      <input type=\"text\" class=\"search-input\" placeholder=\"ID, name, or tag...\" oninput=\"searchTests(this.value)\">\n",
    "    </div>\n",
    s!"    <div class=\"filter-group\"><span>Showing <strong id=\"visibleCount\">{totalCount}</strong> of {totalCount}</span></div>\n",
    "  </div>\n"
  ]

/-- Generate a single test row. -/
private def generateTestRow (r : ReportResult) : String :=
  let tc := r.testCase
  let oc := outcomeClass r.outcome
  let badge := outcomeBadge r.outcome
  let tagsHtml := String.join (tc.tags.map fun tag =>
    s!"<span class=\"tag\">{escapeHtml tag}</span>")
  let errorHtml := match r.errorMsg with
    | some msg => s!"<span class=\"error-msg\" title=\"{escapeHtml msg}\">{escapeHtml msg}</span>"
    | none => ""
  let searchText := s!"{tc.id.toLower} {tc.name.toLower} {String.intercalate " " tc.tags |>.toLower}"
  let stageStr := s!"{tc.stage}"
  let idLink := s!"<a href=\"{yamlTestSuiteUrl}{escapeHtml tc.id}.yaml\" target=\"_blank\" class=\"test-id-link\" title=\"View {escapeHtml tc.id} source in yaml-test-suite\">{escapeHtml tc.id}</a>"
  s!"      <tr class=\"test-row\" data-outcome=\"{oc}\" data-stage=\"{stageStr}\" data-search=\"{escapeHtml searchText}\">\n" ++
  s!"        <td>{idLink}</td>\n" ++
  s!"        <td>{escapeHtml tc.name}</td>\n" ++
  s!"        <td>{stageStr}</td>\n" ++
  s!"        <td>{badge}</td>\n" ++
  s!"        <td>{tagsHtml}</td>\n" ++
  s!"        <td>{errorHtml}</td>\n" ++
  s!"      </tr>\n"

/-- Generate the full test table. -/
private def generateTableHtml (results : Array ReportResult) : String :=
  let rows := String.join (results.toList.map generateTestRow)
  String.join [
    "  <table id=\"testTable\">\n",
    "    <thead>\n",
    "      <tr>\n",
    "        <th onclick=\"sortTable(0)\">ID <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(1)\">Name <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(2)\">Stage <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(3)\">Outcome <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(4)\">Tags <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(5)\">Error <span class=\"sort-arrow\">↕</span></th>\n",
    "      </tr>\n",
    "    </thead>\n",
    "    <tbody>\n",
    rows,
    "    </tbody>\n",
    "  </table>\n"
  ]

/-- Generate a complete standalone HTML report page. -/
def generateHtmlReport (results : Array ReportResult)
    (title : String := "yaml-test-suite Coverage — lean4-yaml-verified")
    (navLink : Option (String × String) := none) : String :=
  let stats := CoverageStats.fromResults results
  let navHtml := match navLink with
    | some (href, label) => s!"  <a href=\"{href}\" class=\"nav-link\">← {label}</a>\n"
    | none => ""
  String.join [
    "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n",
    "  <meta charset=\"UTF-8\">\n",
    "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n",
    s!"  <title>{escapeHtml title}</title>\n",
    "  <style>\n", reportCss, "  </style>\n",
    "</head>\n<body>\n",
    "<div class=\"container\">\n",
    navHtml,
    s!"  <h1>{escapeHtml title}</h1>\n",
    "  <p class=\"subtitle\">YAML 1.2.2 parser compliance against the official yaml-test-suite</p>\n",
    generateStatsHtml stats,
    generateStageCardsHtml results,
    generateFiltersHtml results.size,
    generateTableHtml results,
    "  <footer>\n",
    "    Generated by <a href=\"https://github.com/yaml/yaml-test-suite\">yaml-test-suite</a> runner · Lean 4\n",
    "  </footer>\n",
    "</div>\n\n",
    "<script>\n", reportJs, "</script>\n",
    "</body>\n</html>\n"
  ]

/-- Generate a stage-filtered HTML report. -/

def generateStageReport (results : Array ReportResult) (stage : Stage) : String :=
  let filtered := results.filter (fun r => r.testCase.stage == stage)
  generateHtmlReport filtered
    (title := s!"{stage} Tests — lean4-yaml-verified")
    (navLink := some ("index.html", "Back to Coverage Index"))

/-- Generate the index page linking to all reports. -/
def generateIndexHtml (results : Array ReportResult)
    (verifiedSuites : Option (Array Tests.VerifiedSuiteResult) := none) : String :=
  let stats := CoverageStats.fromResults results
  let pctStr := formatPct stats.successRate

  -- Per-stage summary for the index
  let stages : Array Stage := #[.scalar, .flow, .block, .document, .advanced, .error]
  let stageRows := String.join (stages.toList.map fun stage =>
    let sr := results.filter (fun r => r.testCase.stage == stage)
    let ss := CoverageStats.fromResults sr
    let sp := if ss.applicable == 0 then "0.0"
              else formatPct ((ss.correctCount.toFloat / ss.applicable.toFloat) * 100.0)
    let skipNote := if ss.skipped > 0 then s!" · {ss.skipped} YAML 1.3 skipped" else ""
    s!"              <div class=\"link-box\">\n" ++
    s!"                <a href=\"coverage-{stage}.html\">{stage}</a>\n" ++
    s!"                <div class=\"description\">{ss.correctCount}/{ss.applicable} correct ({sp}%){skipNote}</div>\n" ++
    s!"              </div>\n")

  String.join [
    "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n",
    "  <meta charset=\"UTF-8\">\n",
    "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n",
    "  <title>lean4-yaml-verified Test Coverage</title>\n",
    "  <style>\n",
    "    body { font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; margin: 40px; background: #f5f5f5; }\n",
    "    .container { max-width: 1000px; margin: 0 auto; background: white; padding: 40px; box-shadow: 0 2px 10px rgba(0,0,0,0.1); border-radius: 8px; }\n",
    "    h1 { color: #333; border-bottom: 3px solid #4CAF50; padding-bottom: 10px; }\n",
    "    h2 { color: #555; margin-top: 30px; }\n",
    "    .summary { background: #e8f5e9; padding: 20px; border-radius: 6px; margin: 20px 0; border-left: 4px solid #4CAF50; }\n",
    "    .summary h3 { margin-top: 0; color: #2e7d32; }\n",
    "    .summary pre { margin: 0; font-family: 'Courier New', monospace; font-size: 14px; white-space: pre-wrap; }\n",
    "    .links { display: grid; grid-template-columns: repeat(auto-fit, minmax(220px, 1fr)); gap: 15px; margin: 25px 0; }\n",
    "    .link-box { background: #f5f5f5; padding: 20px; border-radius: 6px; text-align: center; transition: all 0.2s; border: 2px solid #e0e0e0; }\n",
    "    .link-box:hover { transform: translateY(-2px); box-shadow: 0 4px 8px rgba(0,0,0,0.2); border-color: #4CAF50; }\n",
    "    .link-box a { text-decoration: none; color: #2196F3; font-weight: 600; font-size: 16px; }\n",
    "    .link-box a:hover { color: #1565C0; }\n",
    "    .description { color: #666; font-size: 13px; margin-top: 8px; }\n",
    "    footer { margin-top: 40px; text-align: center; color: #999; font-size: 13px; border-top: 1px solid #e0e0e0; padding-top: 20px; }\n",
    "    footer a { color: #2196F3; text-decoration: none; }\n",
    "  </style>\n",
    "</head>\n<body>\n",
    "<div class=\"container\">\n",
    "  <h1>lean4-yaml-verified Test Coverage</h1>\n",
    "  <p style=\"color: #666; font-size: 16px;\">YAML 1.2.2 verified parser · Lean 4</p>\n\n",
    "  <div class=\"summary\">\n",
    "    <h3>yaml-test-suite Compliance</h3>\n",
    "    <pre>\n",
    s!"Total unique tests:      {stats.total}\n",
    s!"Applicable (YAML 1.2.2): {stats.applicable}  <span style=\"color:#999\">({stats.skipped} skipped — YAML 1.3 specific)</span>\n",
    s!"Passed:                  {stats.passed}\n",
    s!"Failed:                  {stats.failed}\n",
    s!"Expected fail:           {stats.expectedFail}\n",
    s!"Unexpected pass:         {stats.unexpectedPass}\n",
    s!"Timeout:                 {stats.timeout}\n",
    s!"\nCorrect: {stats.correctCount}/{stats.applicable} ({pctStr}%)\n",
    "    </pre>\n",
    "  </div>\n\n",
    "  <h2>Reports</h2>\n",
    "  <div class=\"links\">\n",
    "    <div class=\"link-box\">\n",
    "      <a href=\"coverage-all.html\">Full Coverage Report</a>\n",
    s!"      <div class=\"description\">All {stats.total} unique test cases with filtering &amp; sorting</div>\n",
    "    </div>\n",
    "  </div>\n\n",
    "  <h2>Coverage by Stage</h2>\n",
    "  <div class=\"links\">\n",
    stageRows,
    "  </div>\n\n",
    -- Verified Tests section
    match verifiedSuites with
    | some suites =>
      let totalPassed := suites.foldl (fun acc s => acc + s.passed) 0
      let totalTests := suites.foldl (fun acc s => acc + s.total) 0
      let allPass := suites.all (fun s => s.allPass)
      let borderColor := if allPass then "#4CAF50" else "#f44336"
      let bgColor := if allPass then "#e8f5e9" else "#ffebee"
      let statusIcon := if allPass then "✓" else "✗"
      let suiteRows := String.join (suites.toList.map fun suite =>
        let icon := if suite.allPass then "✓" else "✗"
        let color := if suite.allPass then "#4CAF50" else "#f44336"
        s!"    <tr><td><a href=\"{repoSourceUrl}{escapeHtml suite.sourceFile}\" target=\"_blank\" style=\"color:#2196F3;text-decoration:none\">{escapeHtml suite.label}</a></td>" ++
        s!"<td style=\"color:{color};font-weight:bold\">{icon} {suite.passed}/{suite.total}</td></tr>\n")
      String.join [
        s!"  <h2>Verified Tests</h2>\n",
        s!"  <div class=\"summary\" style=\"border-left-color:{borderColor};background:{bgColor}\">\n",
        s!"    <h3 style=\"color:{borderColor}\">{statusIcon} Internal Verified Test Suites ({totalPassed}/{totalTests})</h3>\n",
        s!"    <table style=\"width:100%;border-collapse:collapse;font-family:'Courier New',monospace;font-size:14px;\">\n",
        suiteRows,
        s!"    <tr style=\"border-top:2px solid #ccc;font-weight:bold\">" ++
        s!"<td>Total</td><td>{totalPassed}/{totalTests}</td></tr>\n",
        "    </table>\n",
        "  </div>\n",
        "  <div class=\"links\">\n",
        "    <div class=\"link-box\">\n",
        "      <a href=\"verified-tests.html\">Verified Tests Detail</a>\n",
        s!"      <div class=\"description\">{totalPassed}/{totalTests} tests across {suites.size} suites</div>\n",
        "    </div>\n",
        "  </div>\n\n"
      ]
    | none => "",
    "  <footer>\n",
    "    Generated by <a href=\"https://github.com/yaml/yaml-test-suite\">yaml-test-suite</a> runner · Lean 4\n",
    "  </footer>\n",
    "</div>\n",
    "</body>\n</html>\n"
  ]

/-- Generate the verified tests detail HTML page from structured test results. -/
def generateVerifiedTestsHtml (suites : Array Tests.VerifiedSuiteResult) : String :=
  let totalPassed := suites.foldl (fun acc s => acc + s.passed) 0
  let totalTests := suites.foldl (fun acc s => acc + s.total) 0
  let totalFailed := totalTests - totalPassed
  let allPass := suites.all (fun s => s.allPass)
  let statusEmoji := if allPass then "✅" else "❌"

  -- Stat cards
  let statCards := String.join [
    "  <div class=\"stats\">\n",
    s!"    <div class=\"stat-box stat-total\"><h3>Total</h3><div class=\"number\">{totalTests}</div></div>\n",
    s!"    <div class=\"stat-box stat-pass\"><h3>Passed</h3><div class=\"number\">{totalPassed}</div></div>\n",
    s!"    <div class=\"stat-box stat-fail\"><h3>Failed</h3><div class=\"number\">{totalFailed}</div></div>\n",
    s!"    <div class=\"stat-box stat-suites\"><h3>Suites</h3><div class=\"number\">{suites.size}</div></div>\n",
    "  </div>\n"
  ]

  -- Per-suite breakdown cards
  let suiteCards := String.join (suites.toList.map fun suite =>
    let pct := if suite.total == 0 then "0.0"
               else formatPct (suite.passed.toFloat / suite.total.toFloat * 100.0)
    let borderColor := if suite.allPass then "var(--color-pass)" else "var(--color-fail)"
    s!"    <div class=\"stage-card\" style=\"border-left-color:{borderColor}\">\n" ++
    s!"      <div class=\"stage-card-name\">{escapeHtml suite.label}</div>\n" ++
    s!"      <div class=\"stage-card-stats\">{suite.passed}/{suite.total} passed ({pct}%)</div>\n" ++
    s!"      <div class=\"stage-bar\"><div class=\"stage-bar-fill\" style=\"width: {pct}%\"></div></div>\n" ++
    s!"      <div class=\"stage-card-source\"><a href=\"{repoSourceUrl}{escapeHtml suite.sourceFile}\" target=\"_blank\" class=\"source-link\">📄 {escapeHtml suite.sourceFile}</a></div>\n" ++
    s!"    </div>\n")

  -- Suite dropdown options
  let suiteOptions := String.join (suites.toList.map fun suite =>
    s!"        <option value=\"{escapeHtml suite.name}\">{escapeHtml suite.label}</option>\n")

  -- Table rows — one per VerifiedTestCase
  let tableRows := String.join (suites.toList.map fun suite =>
    String.join (suite.tests.toList.map fun tc =>
      let outcomeClass := if tc.outcome.isPass then "pass" else "fail"
      let badgeClass := if tc.outcome.isPass then "badge-pass" else "badge-fail"
      let badgeLabel := if tc.outcome.isPass then "Pass" else "Fail"
      let errorCell := match tc.outcome with
        | .pass => ""
        | .fail msg =>
          if msg.isEmpty then ""
          else s!"<span class=\"error-msg\" title=\"{escapeHtml msg}\">{escapeHtml msg}</span>"
      let lineAnchor := if tc.sourceLine > 0 then s!"#L{tc.sourceLine}" else ""
      let searchData := (s!"{suite.name} {tc.category} {tc.name}").toLower
      s!"      <tr class=\"test-row\" data-outcome=\"{outcomeClass}\" data-suite=\"{escapeHtml suite.name}\" data-search=\"{escapeHtml searchData}\">\n" ++
      s!"        <td><a href=\"{repoSourceUrl}{escapeHtml suite.sourceFile}{lineAnchor}\" target=\"_blank\" class=\"source-link\">{escapeHtml suite.label}</a></td>\n" ++
      s!"        <td>{escapeHtml tc.category}</td>\n" ++
      s!"        <td>{escapeHtml tc.name}</td>\n" ++
      s!"        <td><span class=\"badge {badgeClass}\">{badgeLabel}</span></td>\n" ++
      s!"        <td>{errorCell}</td>\n" ++
      s!"      </tr>\n"))

  -- JavaScript
  let js := String.join [
    "    let currentOutcomeFilter = 'all';\n",
    "    let currentSuiteFilter = 'all';\n",
    "    let currentSearchText = '';\n",
    "    let sortColumn = 0;\n",
    "    let sortAscending = true;\n\n",
    "    function filterByOutcome(outcome) {\n",
    "      currentOutcomeFilter = outcome;\n",
    "      document.querySelectorAll('.filter-outcome .filter-btn').forEach(btn => btn.classList.remove('active'));\n",
    "      event.target.classList.add('active');\n",
    "      applyFilters();\n",
    "    }\n\n",
    "    function filterBySuite(suite) {\n",
    "      currentSuiteFilter = suite;\n",
    "      applyFilters();\n",
    "    }\n\n",
    "    function searchTests(text) {\n",
    "      currentSearchText = text.toLowerCase();\n",
    "      applyFilters();\n",
    "    }\n\n",
    "    function applyFilters() {\n",
    "      const rows = document.querySelectorAll('.test-row');\n",
    "      let visible = 0;\n",
    "      rows.forEach(row => {\n",
    "        const outcome = row.dataset.outcome;\n",
    "        const suite = row.dataset.suite;\n",
    "        const search = row.dataset.search;\n",
    "        const outcomeMatch = currentOutcomeFilter === 'all' || outcome === currentOutcomeFilter;\n",
    "        const suiteMatch = currentSuiteFilter === 'all' || suite === currentSuiteFilter;\n",
    "        const searchMatch = currentSearchText === '' || search.includes(currentSearchText);\n",
    "        if (outcomeMatch && suiteMatch && searchMatch) {\n",
    "          row.classList.remove('hidden');\n",
    "          visible++;\n",
    "        } else {\n",
    "          row.classList.add('hidden');\n",
    "        }\n",
    "      });\n",
    "      document.getElementById('visibleCount').textContent = visible;\n",
    "    }\n\n",
    "    function sortTable(colIdx) {\n",
    "      const table = document.getElementById('testTable');\n",
    "      const tbody = table.querySelector('tbody');\n",
    "      const rows = Array.from(tbody.querySelectorAll('.test-row'));\n",
    "      if (sortColumn === colIdx) { sortAscending = !sortAscending; }\n",
    "      else { sortColumn = colIdx; sortAscending = true; }\n",
    "      table.querySelectorAll('th').forEach((th, i) => {\n",
    "        th.classList.remove('sorted');\n",
    "        const arrow = th.querySelector('.sort-arrow');\n",
    "        if (arrow) arrow.textContent = '↕';\n",
    "      });\n",
    "      const th = table.querySelectorAll('th')[colIdx];\n",
    "      th.classList.add('sorted');\n",
    "      const arrow = th.querySelector('.sort-arrow');\n",
    "      if (arrow) arrow.textContent = sortAscending ? '↑' : '↓';\n",
    "      rows.sort((a, b) => {\n",
    "        let aVal = a.children[colIdx]?.textContent.trim() || '';\n",
    "        let bVal = b.children[colIdx]?.textContent.trim() || '';\n",
    "        return sortAscending ? aVal.localeCompare(bVal) : bVal.localeCompare(aVal);\n",
    "      });\n",
    "      rows.forEach(row => tbody.appendChild(row));\n",
    "    }\n"
  ]

  String.join [
    "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n",
    "  <meta charset=\"UTF-8\">\n",
    "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n",
    "  <title>Verified Tests — lean4-yaml-verified</title>\n",
    "  <style>\n",
    "    :root { --color-pass: #4CAF50; --color-fail: #f44336; }\n",
    "    * { box-sizing: border-box; }\n",
    "    body { font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; margin: 0; padding: 20px; background: #f5f5f5; }\n",
    "    .container { max-width: 1400px; margin: 0 auto; background: white; padding: 30px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); border-radius: 8px; }\n",
    "    h1 { color: #333; border-bottom: 3px solid var(--color-pass); padding-bottom: 10px; margin-top: 0; }\n",
    "    h3 { color: #555; }\n",
    "    .subtitle { color: #666; font-size: 16px; margin-bottom: 30px; }\n",
    "    .stats { display: grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr)); gap: 15px; margin: 25px 0; }\n",
    "    .stat-box { color: white; padding: 20px; border-radius: 8px; text-align: center; box-shadow: 0 4px 6px rgba(0,0,0,0.1); }\n",
    "    .stat-box h3 { margin: 0 0 8px 0; font-size: 13px; opacity: 0.9; color: white; }\n",
    "    .stat-box .number { font-size: 32px; font-weight: bold; }\n",
    "    .stat-total { background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); }\n",
    "    .stat-pass { background: linear-gradient(135deg, #4CAF50 0%, #45a049 100%); }\n",
    "    .stat-fail { background: linear-gradient(135deg, #f44336 0%, #d32f2f 100%); }\n",
    "    .stat-suites { background: linear-gradient(135deg, #00bcd4 0%, #0097a7 100%); }\n",
    "    .stage-cards { display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); gap: 15px; margin: 20px 0; }\n",
    "    .stage-card { background: #f8f9fa; padding: 18px; border-radius: 6px; border-left: 4px solid var(--color-pass); }\n",
    "    .stage-card-name { font-weight: 600; font-size: 16px; color: #333; margin-bottom: 8px; }\n",
    "    .stage-card-stats { color: #666; font-size: 14px; }\n",
    "    .stage-card-source { margin-top: 8px; font-size: 12px; }\n",
    "    .source-link { color: #2196F3; text-decoration: none; font-family: 'Courier New', monospace; }\n",
    "    .source-link:hover { text-decoration: underline; }\n",
    "    .stage-bar { height: 8px; background: #e0e0e0; border-radius: 4px; margin-top: 10px; overflow: hidden; }\n",
    "    .stage-bar-fill { height: 100%; background: var(--color-pass); border-radius: 4px; transition: width 0.3s ease; }\n",
    "    .filters { background: #f8f9fa; padding: 15px; border-radius: 6px; margin: 20px 0; display: flex; gap: 20px; flex-wrap: wrap; align-items: center; }\n",
    "    .filter-group { display: flex; align-items: center; gap: 8px; }\n",
    "    .filter-group label { font-weight: 600; color: #555; font-size: 14px; }\n",
    "    .filter-btn { padding: 6px 14px; border: 2px solid #ddd; background: white; border-radius: 4px; cursor: pointer; transition: all 0.2s; font-size: 13px; }\n",
    "    .filter-btn:hover { border-color: #4CAF50; }\n",
    "    .filter-btn.active { background: #4CAF50; color: white; border-color: #4CAF50; }\n",
    "    select { padding: 6px 12px; border: 2px solid #ddd; border-radius: 4px; font-size: 13px; }\n",
    "    .search-input { padding: 6px 12px; border: 2px solid #ddd; border-radius: 4px; font-size: 13px; width: 200px; }\n",
    "    .search-input:focus { border-color: #4CAF50; outline: none; }\n",
    "    table { width: 100%; border-collapse: collapse; margin: 20px 0; box-shadow: 0 2px 4px rgba(0,0,0,0.1); }\n",
    "    th { background: #4CAF50; color: white; padding: 10px 12px; text-align: left; font-weight: 600; position: sticky; top: 0; cursor: pointer; user-select: none; font-size: 13px; }\n",
    "    th:hover { background: #45a049; }\n",
    "    th .sort-arrow { margin-left: 4px; opacity: 0.5; }\n",
    "    th.sorted .sort-arrow { opacity: 1; }\n",
    "    td { padding: 8px 12px; border-bottom: 1px solid #e0e0e0; font-size: 13px; }\n",
    "    tr:hover { background: #f5f5f5; }\n",
    "    tr.hidden { display: none; }\n",
    "    .badge { display: inline-block; padding: 3px 10px; border-radius: 12px; font-size: 11px; font-weight: 600; color: white; }\n",
    "    .badge-pass { background: var(--color-pass); }\n",
    "    .badge-fail { background: var(--color-fail); }\n",
    "    .error-msg { color: #d32f2f; font-size: 11px; font-family: 'Courier New', monospace; max-width: 400px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; display: inline-block; }\n",
    "    .error-msg:hover { white-space: normal; word-break: break-all; }\n",
    "    .nav-link { display: inline-block; margin-bottom: 20px; color: #2196F3; text-decoration: none; font-size: 14px; }\n",
    "    .nav-link:hover { text-decoration: underline; }\n",
    "    footer { margin-top: 40px; text-align: center; color: #999; font-size: 13px; border-top: 1px solid #e0e0e0; padding-top: 20px; }\n",
    "    footer a { color: #2196F3; text-decoration: none; }\n",
    "    @media (max-width: 768px) { body { padding: 10px; } .container { padding: 15px; } .filters { flex-direction: column; gap: 10px; } .stats { grid-template-columns: repeat(2, 1fr); } }\n",
    "  </style>\n",
    "</head>\n<body>\n",
    "<div class=\"container\">\n",
    "  <a href=\"index.html\" class=\"nav-link\">← Back to Coverage Index</a>\n",
    s!"  <h1>{statusEmoji} Verified Tests</h1>\n",
    "  <p class=\"subtitle\">Unit tests, parser tests, verification tests, and string lemma tests — all must pass.</p>\n\n",
    statCards,
    "  <h3>Suites</h3>\n",
    "  <div class=\"stage-cards\">\n",
    suiteCards,
    "  </div>\n\n",
    "  <div class=\"filters\">\n",
    "    <div class=\"filter-group filter-outcome\">\n",
    "      <label>Outcome:</label>\n",
    "      <button class=\"filter-btn active\" onclick=\"filterByOutcome('all')\">All</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByOutcome('pass')\">Pass</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByOutcome('fail')\">Fail</button>\n",
    "    </div>\n",
    "    <div class=\"filter-group\">\n",
    "      <label>Suite:</label>\n",
    "      <select onchange=\"filterBySuite(this.value)\">\n",
    "        <option value=\"all\">All Suites</option>\n",
    suiteOptions,
    "      </select>\n",
    "    </div>\n",
    "    <div class=\"filter-group\">\n",
    "      <label>Search:</label>\n",
    "      <input type=\"text\" class=\"search-input\" placeholder=\"Category, test name...\" oninput=\"searchTests(this.value)\">\n",
    "    </div>\n",
    s!"    <div class=\"filter-group\"><span>Showing <strong id=\"visibleCount\">{totalTests}</strong> of {totalTests}</span></div>\n",
    "  </div>\n\n",
    "  <table id=\"testTable\">\n",
    "    <thead>\n",
    "      <tr>\n",
    "        <th onclick=\"sortTable(0)\">Suite <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(1)\">Category <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(2)\">Test <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(3)\">Outcome <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(4)\">Error <span class=\"sort-arrow\">↕</span></th>\n",
    "      </tr>\n",
    "    </thead>\n",
    "    <tbody>\n",
    tableRows,
    "    </tbody>\n",
    "  </table>\n\n",
    "  <footer>\n",
    "    Generated by <a href=\"https://github.com/yaml/yaml-test-suite\">yaml-test-suite</a> runner · Lean 4\n",
    "  </footer>\n",
    "</div>\n\n",
    "<script>\n", js, "</script>\n",
    "</body>\n</html>\n"
  ]

/-- Write all HTML reports to a directory. -/
def writeReports (results : Array ReportResult) (outDir : String)
    (verifiedSuites : Option (Array Tests.VerifiedSuiteResult) := none) : IO Unit := do
  -- Normalize: strip trailing slash
  let dir := if outDir.endsWith "/" then (outDir.toRawSubstring.dropRight 1).toString else outDir
  -- Ensure output directory exists
  IO.FS.createDirAll dir

  -- Write index
  let indexHtml := generateIndexHtml results (verifiedSuites := verifiedSuites)
  IO.FS.writeFile s!"{dir}/index.html" indexHtml
  IO.println s!"  wrote {dir}/index.html"

  -- Write full report
  let fullHtml := generateHtmlReport results
    (navLink := some ("index.html", "Back to Coverage Index"))
  IO.FS.writeFile s!"{dir}/coverage-all.html" fullHtml
  IO.println s!"  wrote {dir}/coverage-all.html"

  -- Write per-stage reports
  let stages : Array Stage := #[.scalar, .flow, .block, .document, .advanced, .error]
  for stage in stages do
    let html := generateStageReport results stage
    IO.FS.writeFile s!"{dir}/coverage-{stage}.html" html
    IO.println s!"  wrote {dir}/coverage-{stage}.html"

  -- Write verified tests detail page
  match verifiedSuites with
  | some suites =>
    let html := generateVerifiedTestsHtml suites
    IO.FS.writeFile s!"{dir}/verified-tests.html" html
    IO.println s!"  wrote {dir}/verified-tests.html"
  | none => pure ()

  -- Write machine-readable JSON summary
  let dateResult ← IO.Process.output { cmd := "date", args := #["+%Y-%m-%dT%H:%M:%S%z"] }
  let dateStr := dateResult.stdout.trimAscii.toString
  let json := generateJsonSummary results dateStr (verifiedSuites := verifiedSuites)
  IO.FS.writeFile s!"{dir}/coverage-summary.json" json
  IO.println s!"  wrote {dir}/coverage-summary.json"

  IO.println s!"\nHTML reports written to {dir}/"

end Tests.SuiteRunner
