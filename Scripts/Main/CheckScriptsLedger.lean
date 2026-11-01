module

public import Scripts.Ledger

@[expose] public section Blanket

/-!
# scripts-check-ledger — the Rule 9 gate

```
lake exe scripts-check-ledger [-C ROOT] [-l LEDGER] [-v] [--version] [-h]
```

Reads `scripts/scripts-ledger.txt`, walks `scripts/**/*.py`, scans
`scripts/*.sh` and `.github/workflows/*.yml` for `python`/`python3`
invocations and `lakefile.lean` for `lean_exe` names, and runs
`Scripts.Ledger.check`.  Exit 0 with one summary line when green; exit 1
with one line per violation otherwise.

What is gated today, and what is not.  Every row is `todo` at phase 0 of
`Blueprint/09-scripts-in-lean.md` and every wrapper still calls Python:
a `python3 scripts/x.py` call whose row is `todo` or `exception:*` is
allowed; one whose row is `lean:*` (ported — the file must be deleted
with the port) or absent fails.  `python3 -m <module>` runs pass only when
plan §4 covers them (`-m pytest` over the shipped binding's tests, `-m pip
install weasyprint`); any other module run fails.  Growth is what the
gate refuses: a `.py` with no row, an inline `python3 -c` / `python3 -`
invocation line with no `inline:<file>:<command prefix>` row (one row per
invocation line; the gate prints the current line numbers beside the
inline rows), or more open rows than the `# open:` pin.
-/

open Scripts.Ledger

namespace Scripts.CheckScriptsLedger

def version : String := "scripts-check-ledger 0.1.0 (L4YAML Rule 9 gate)"

def usage : String :=
"usage: lake exe scripts-check-ledger [options]

Rule 9 gate: every scripts/**/*.py and every inline python3 invocation in
scripts/*.sh and .github/workflows/*.yml is on scripts/scripts-ledger.txt,
ported rows are deleted, and the open-row count equals the `# open:` pin.

options:
  -C, --root DIR      repository root (default: .)
  -l, --ledger FILE   ledger path, relative to the root
                      (default: scripts/scripts-ledger.txt)
  -v, --verbose       list every python invocation found
  -V, --version       print the version and exit
  -h, --help          print this help and exit

exit status: 0 green, 1 violations, 2 usage or I/O error."

structure Options where
  root : String := "."
  ledger : String := "scripts/scripts-ledger.txt"
  verbose : Bool := false
  deriving Repr

inductive Parsed where
  | run (o : Options)
  | help
  | version
  | bad (msg : String)

def parseArgs : List String → Options → Parsed
  | [], o => .run o
  | ("-h" :: _), _ | ("--help" :: _), _ => .help
  | ("-V" :: _), _ | ("--version" :: _), _ => .version
  | ("-v" :: rest), o | ("--verbose" :: rest), o => parseArgs rest { o with verbose := true }
  | ("-C" :: d :: rest), o | ("--root" :: d :: rest), o => parseArgs rest { o with root := d }
  | ("-l" :: f :: rest), o | ("--ledger" :: f :: rest), o => parseArgs rest { o with ledger := f }
  | (a :: _), _ => .bad s!"unknown argument `{a}`"

/-- All files under `dir` (recursively) with extension `ext`, as paths
relative to `root`, sorted. -/
def filesUnder (root dir : String) (ext : String) (recursive : Bool) : IO (Array String) := do
  let base : System.FilePath := root
  let d := base / dir
  if !(← d.isDir) then return #[]
  let paths ←
    if recursive then d.walkDir
    else pure ((← d.readDir).map (·.path))
  let mut out : Array String := #[]
  for p in paths do
    if p.extension == some ext then
      -- strip the root prefix so the key reads `scripts/x.py`
      let s := p.toString
      let prefix_ := (base / "").toString
      let rel := if s.startsWith prefix_ then String.ofList (s.toList.drop prefix_.length) else s
      out := out.push rel
  return out.qsort (· < ·)

def readText (root rel : String) : IO String :=
  IO.FS.readFile ((root : System.FilePath) / rel)

def collect (o : Options) : IO Inventory := do
  let pyFiles ← filesUnder o.root "scripts" "py" true
  let shFiles ← filesUnder o.root "scripts" "sh" false
  let ymlFiles := (← filesUnder o.root ".github/workflows" "yml" false)
    ++ (← filesUnder o.root ".github/workflows" "yaml" false)
  let mut sites : Array Site := #[]
  for f in shFiles ++ ymlFiles do
    sites := sites ++ sitesOfText f (← readText o.root f)
  let exes := leanExesOfText (← readText o.root "lakefile.lean")
  return { pyFiles, sites, exes }

def PyCall.describe : PyCall → String
  | .script p => s!"script {p}"
  | .inline c => s!"inline `{c}`"
  | .moduleRun c => s!"module `{c}`"
  | .none => "none"

def run (o : Options) : IO UInt32 := do
  let text ← try readText o.root o.ledger
    catch e => do
      IO.eprintln s!"scripts-check-ledger: cannot read {o.ledger}: {e}"
      return 2
  let ledger ← match parseLedger text with
    | .ok l => pure l
    | .error e => do
      IO.eprintln s!"scripts-check-ledger: {o.ledger}: {e}"
      return 2
  let inv ← collect o
  if o.verbose then
    for s in inv.sites do
      IO.println s!"  {s.file}:{s.line}: {PyCall.describe s.call}"
  let errs := check ledger inv
  let c := counts ledger inv
  let inlineKeys := ledger.rows.foldl (fun (acc : Array String) r =>
    if r.isInline && !acc.contains r.key then acc.push r.key else acc) #[]
  for k in inlineKeys do
    let n := (ledger.rows.filter (·.key == k)).size
    let mult := if n == 1 then "" else s!" ×{n}"
    IO.println s!"  {k}{mult} @ line {inv.inlineLines k |>.toList}"
  if errs.isEmpty then
    IO.println s!"scripts-check-ledger: OK — {c.render}"
    return 0
  else
    for e in errs do IO.eprintln s!"scripts-check-ledger: FAIL: {e}"
    IO.eprintln s!"scripts-check-ledger: {errs.size} violation(s) — {c.render}"
    return 1

end Scripts.CheckScriptsLedger

open Scripts.CheckScriptsLedger in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-check-ledger: {m}\n{usage}"; return 2
  | .run o => run o
