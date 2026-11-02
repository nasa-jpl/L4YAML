module

public import Scripts.Ledger.Diff

/-!
# `lake run ledger-diff` — diff two `parse_iff_grammar` ledger snapshots

The port of `scripts/ledger_diff.py` (Rule 9 phase 2).  The readings are
`Scripts.Ledger.Diff`; this is the IO: the two files (or the two newest
`YYYY-MM-DD.md` in `Blueprint/ledgers/parse_iff_grammar` with `--latest`), the
report on stdout and, with `--out`, in a file; the Python's cell-count warnings
on stderr.

exit status: 0 report printed; 1 a snapshot unreadable, fewer than two snapshots in
the series, or `--out` unwritable; 2 usage.
-/

namespace Scripts.LedgerDiff

open Scripts.Ledger.Diff

def version : String := "scripts-ledger-diff 1.0 (Rule 9 phase 2)"

def usage : String := "usage: lake run ledger-diff -- OLD.md NEW.md [options]
       lake run ledger-diff -- --latest [options]

Diff two parse_iff_grammar ledger snapshots: instruments whose value moved
(with a numeric delta when both parse), table rows whose cells changed (old ->
new, cell by cell), rows added or removed.  The report is Markdown on stdout.

options:
  -l, --latest      diff the two newest YYYY-MM-DD.md in Blueprint/ledgers/parse_iff_grammar
  -o, --out FILE    also write the report to FILE
  -C, --root ROOT   repository root for --latest (default: the current directory)
  -h, --help        this message
  -V, --version     version"

structure Opts where
  root : System.FilePath := "."
  latest : Bool := false
  out : Option String := none
  positional : Array String := #[]

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg; pure code

partial def parseOpts (args : List String) (o : Opts) : Except String Opts :=
  match args with
  | [] => pure o
  | "--" :: t => pure { o with positional := o.positional ++ t.toArray }
  | "-l" :: t | "--latest" :: t => parseOpts t { o with latest := true }
  | "-o" :: v :: t | "--out" :: v :: t => parseOpts t { o with out := some v }
  | "-C" :: v :: t | "--root" :: v :: t => parseOpts t { o with root := v }
  | a :: t =>
    if a.startsWith "-" && a.length > 1 then throw s!"unknown option '{a}'"
    else parseOpts t { o with positional := o.positional.push a }

def series : System.FilePath := "Blueprint" / "ledgers" / "parse_iff_grammar"

/-- `^\d{4}-\d{2}-\d{2}\.md$` -/
def isSnapshotName (n : String) : Bool :=
  let cs := n.toList
  cs.length == 13 && (List.range 13).all fun i =>
    let c := cs[i]!
    if i == 4 || i == 7 then c == '-'
    else if i == 10 then c == '.'
    else if i == 11 then c == 'm'
    else if i == 12 then c == 'd'
    else c.isDigit

#guard isSnapshotName "2026-10-29.md"
#guard !isSnapshotName "2026-10-29.md~"
#guard !isSnapshotName "README.md"

def pickLatest (root : System.FilePath) : IO (Except String (System.FilePath × System.FilePath)) := do
  let dir := root / series
  let names := (← dir.readDir).map (·.fileName) |>.filter isSnapshotName
  let names := names.qsort (· < ·)
  if names.size < 2 then return .error s!"need two snapshots in {dir}, found {names.size}"
  return .ok (dir / names[names.size - 2]!, dir / names[names.size - 1]!)

def run (args : List String) : IO UInt32 := do
  let pre := args.takeWhile (· != "--")
  if pre.contains "-h" || pre.contains "--help" then IO.println usage; return 0
  if pre.contains "-V" || pre.contains "--version" then IO.println version; return 0
  let o ← match parseOpts args {} with
    | .ok o => pure o
    | .error e => return ← die s!"{e}\n{usage}" 2
  let pair : Except String (System.FilePath × System.FilePath) ←
    if o.latest then pickLatest o.root
    else match o.positional with
      | #[a, b] => pure (.ok (a, b))
      | _ => return ← die s!"give OLD NEW or --latest\n{usage}" 2
  let (oldP, newP) ← match pair with
    | .ok p => pure p
    | .error e => return ← die e
  let read (p : System.FilePath) : IO (Except String String) :=
    (do pure (.ok (← IO.FS.readFile p))) <|> pure (.error s!"cannot read {p}")
  let oldT ← match ← read oldP with | .ok t => pure t | .error e => return ← die e
  let newT ← match ← read newP with | .ok t => pure t | .error e => return ← die e
  let oldName := oldP.fileName.getD oldP.toString
  let newName := newP.fileName.getD newP.toString
  let (old, w1) := parse oldName oldT
  let (new, w2) := parse newName newT
  for w in w1 ++ w2 do IO.eprintln w
  let text := "\n".intercalate (report oldName newName old new).toList
  IO.println text
  if let some f := o.out then
    try IO.FS.writeFile f (text ++ "\n")
    catch e => return ← die s!"cannot write {f}: {e}"
  return 0

end Scripts.LedgerDiff

public def main (args : List String) : IO UInt32 := Scripts.LedgerDiff.run args
