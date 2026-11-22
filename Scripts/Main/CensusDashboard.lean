module

public import Scripts.Census.Dashboard
public import Scripts.Docs.Nav

@[expose] public section Blanket

/-!
# scripts-census-dashboard — `lake run census-dashboard [-- -C ROOT] [--check] [--md FILE] [--diff REF]`

DOCS item 514.  Every directed census — a pinned count the campaign drives to zero or up to a bound —
with its current reading (read off the `def expected… :=` literals under `Tests/Guards/Proofs/`, the
same values every full build checks against the environment), its goal, the distance left and what
moves it; then every pinned reading that has no target.  `--check` exits 1 when a roster row names a
pin or field the guards no longer hold.  `--md FILE` writes the report as Markdown as well.
-/

open Scripts.Census.Dashboard

namespace Scripts.Main.CensusDashboard

def usage : String := "usage: lake run census-dashboard -- [-C ROOT] [--check] [--md FILE] [--no-readings]
  -C ROOT         checkout root (default: the current directory)
  --check         exit 1 when a roster row resolves to no pin / field (the CI form)
  --md FILE       also write the report to FILE
  --no-readings   omit the `readings without a target` section
  --diff REF      report only the pins that moved against git REF (e.g. origin/fix-a-grammar-completeness):
                  directed fields with goal distance before → after and a verdict, then population readings
  -h, --help      this text"

structure Opts where
  root : String := "."
  check : Bool := false
  md : Option String := none
  readings : Bool := true
  diff : Option String := none

def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--" :: rest, o => parseOpts rest o
  | "-C" :: r :: rest, o => parseOpts rest { o with root := r }
  | "--check" :: rest, o => parseOpts rest { o with check := true }
  | "--md" :: f :: rest, o => parseOpts rest { o with md := some f }
  | "--no-readings" :: rest, o => parseOpts rest { o with readings := false }
  | "--diff" :: r :: rest, o => parseOpts rest { o with diff := some r }
  | a :: _, _ => .error s!"unknown argument `{a}`\n{usage}"

def guardsDir : System.FilePath := "Tests" / "Guards" / "Proofs"

/-- Every `Tests/Guards/Proofs/*.lean`, by name. -/
def guardFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← (root / guardsDir).readDir
  let files := entries.filterMap fun e =>
    if e.fileName.endsWith ".lean" then some e.path else none
  return files.qsort (fun a b => a.toString < b.toString)

/-- The Rule 9 ledger as a pin: `rows=<todo + exception> pin=<its own # open: N>`. -/
def ledgerPin (root : System.FilePath) : IO (Option Pin) := do
  let path := root / "scripts" / "scripts-ledger.txt"
  if !(← path.pathExists) then return none
  match Scripts.Ledger.parseLedger (← IO.FS.readFile path) with
  | .error _ => return none
  | .ok l => return some { census := "scripts-ledger", name := "open", literal := s!"rows={l.openCount} pin={l.pin}" }

/-- `ref` names a commit (`git rev-parse --verify`); a mistyped or unfetched ref is an error, not an empty base. -/
def refExists (root : System.FilePath) (ref : String) : IO Bool := do
  let r ← IO.Process.output { cmd := "git", args := #["rev-parse", "--verify", "--quiet", s!"{ref}^\{commit}"], cwd := some root }
  return r.exitCode == 0

/-- The guard file `path` (relative to `root`) as it stands at git `ref`; `none` when `ref` has no such file. -/
def fileAt (root : System.FilePath) (ref : String) (rel : String) : IO (Option String) := do
  let r ← IO.Process.output { cmd := "git", args := #["show", s!"{ref}:{rel}"], cwd := some root }
  return if r.exitCode == 0 then some r.stdout else none

/-- Every pin of every `Tests/Guards/Proofs/*.lean` at git `ref` (the files this tree has; a file `ref`
    holds and this tree deleted is reported by `git diff --stat`, not here). -/
def pinsAt (root : System.FilePath) (ref : String) : IO (Array Pin) := do
  let mut pins : Array Pin := #[]
  for f in ← guardFiles root do
    let stem := f.fileStem.getD ""
    if let some text ← fileAt root ref s!"Tests/Guards/Proofs/{f.fileName.getD ""}" then
      pins := pins ++ readPins stem text
  return pins

def shortHead (root : System.FilePath) : IO String := do
  let r ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short", "HEAD"], cwd := some root }
  return if r.exitCode == 0 then r.stdout.trimAscii.toString else "?"

/-- The latest closure-log item and its NEXT paragraph (the mandate), off `DOCS.md`. -/
def mandate (root : System.FilePath) : IO (Array String) := do
  let path := root / "DOCS.md"
  if !(← path.pathExists) then return #[]
  let lines := ((← IO.FS.readFile path).splitOn "\n").toArray
  let items := Scripts.Docs.Nav.findItems lines
  let some it := items.back? | return #[]
  let next := (Scripts.Docs.Nav.nextParagraph lines it).getD #[]
  let text := Scripts.Docs.Nav.collapseWs ((" ".intercalate next.toList).replace "**NEXT —**" "")
  return #[s!"latest item: {it.label} ({it.date})", s!"mandate: {Scripts.Docs.Nav.truncate text 400}"]

def run (args : List String) : IO UInt32 := do
  if args.any (fun a => a == "-h" || a == "--help") then IO.println usage; return 0
  let o ← match parseOpts args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let root : System.FilePath := o.root
  let mut pins : Array Pin := #[]
  for f in ← guardFiles root do
    let stem := f.fileStem.getD ""
    pins := pins ++ readPins stem (← IO.FS.readFile f)
  if let some p ← ledgerPin root then pins := pins.push p
  let (rows, errs) := resolveAll pins
  let mut out : Array String := #[]
  if let some ref := o.diff then
    if !(← refExists root ref) then
      IO.eprintln s!"CENSUS-DASHBOARD: `{ref}` is not a commit here (mistyped, or not fetched)"
      return 2
    if o.check && !errs.isEmpty then
      for e in errs do IO.eprintln s!"- {e}"
      IO.eprintln s!"CENSUS-DASHBOARD: {errs.size} roster row(s) resolve to no pin / field — fix the roster in Scripts/Census/Dashboard.lean"
      return 1
    let base ← pinsAt root ref
    let cur := pins.filter (·.census != "scripts-ledger")  -- synthesized from the live ledger only; not a pin `git show` can read
    let moves := renderMoves ref (directedMoves base cur) (directedUnresolved base cur) (populationMoves base cur)
    let report := "\n".intercalate moves.toList ++ "\n"
    IO.print report
    if let some f := o.md then
      IO.FS.writeFile f report
      IO.eprintln s!"wrote {f}"
    return 0
  out := out.push s!"# Census dashboard — tree `{← shortHead root}`"
  out := out.push ""
  out := out ++ (← mandate root)
  out := out.push s!"pins read: {pins.size} ({(pins.map (·.census)).toList.eraseDups.length} censuses)"
  out := out.push ""
  out := out.push "## Directed censuses — how far each is from its goal, and what moves it"
  out := out.push ""
  out := out.push "`left` is `|now − goal|`; `move` is what the guard enforces (a shrink-only pin that rises needs the owner's word); `status` HOLD is a reading kept at its goal by a gate."
  out := out.push ""
  out := out ++ renderRows rows
  out := out.push ""
  out := out.push s!"**Totals:** {totals rows}"
  if !errs.isEmpty then
    out := out.push ""
    out := out.push s!"## Roster rows that do not resolve ({errs.size})"
    out := out.push ""
    for e in errs do out := out.push s!"- {e}"
  if o.readings then
    out := out.push ""
    out := out.push "## Readings without a target"
    out := out.push ""
    out := out.push "Pinned counts the roster gives no direction: snapshots (term sizes, thread lengths, the rows of a walk) and prices. A count here that the campaign drives somewhere belongs on the roster (`Scripts/Census/Dashboard.lean`)."
    out := out.push ""
    out := out ++ renderReadings pins
  let report := "\n".intercalate out.toList ++ "\n"
  IO.print report
  if let some f := o.md then
    IO.FS.writeFile f report
    IO.eprintln s!"wrote {f}"
  if o.check then
    if !errs.isEmpty then
      IO.eprintln s!"CENSUS-DASHBOARD: {errs.size} roster row(s) resolve to no pin / field — fix the roster in Scripts/Census/Dashboard.lean"
      return 1
    IO.eprintln s!"CENSUS-DASHBOARD: roster resolves ({rows.size} rows)"
  return 0

end Scripts.Main.CensusDashboard

public def main (args : List String) : IO UInt32 := Scripts.Main.CensusDashboard.run args
