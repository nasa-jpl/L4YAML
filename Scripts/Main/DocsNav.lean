module

public import Scripts.Docs.Nav

/-!
# scripts-docs-nav — `lake run docs-nav -- <cmd> [options]`

Formerly `scripts/docs_nav.py`.  Navigate DOCS.md without paging it; the
slice an agent needs, read-only.  Line numbers are 1-based and match `sed -n`.
-/

open Scripts.Docs.Nav Scripts.Lean

def usage : String := "usage: lake run docs-nav -- [-C ROOT] <cmd> [options]

    toc                          top-level sections with line numbers
    items [--since N] [--last K] one line per closure-log item
    item N [--lines]             the full entry for item N (N may carry a suffix: 67a)
    next [N]                     the NEXT (mandate) paragraph of item N (default: the latest item)
    remaining [--lines]          open work: the six-step rows not yet done, then the
                                 dated \"REMAINING, in order\" dependency chain
    steps [--lines]              the Row 12 six-step table and next-actions table
    grep REGEX [-i]              items whose body matches, with hit counts
    section PREFIX [--lines]     a `## ` section by heading prefix

  --lines / -l   prefix each line with its DOCS.md line number
  --width / -w N headline truncation width (default 100)
  -i, --ignore-case   (grep) fold case
  -C ROOT        checkout root (default: the current directory); reads ROOT/DOCS.md
  --             end of options (a grep pattern that starts with `-` goes after it)
  -h, --help     this text;  --version"

structure Opts where
  root : String := "."
  lines : Bool := false
  width : Nat := 100
  since : Option Nat := none
  last : Option Nat := none
  icase : Bool := false
  positional : Array String := #[]

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg; pure code

partial def parseOpts (args : List String) (o : Opts) : Except String Opts :=
  let nat (k v : String) (f : Nat → Opts) : Except String Opts :=
    match v.toNat? with | some n => pure (f n) | none => throw s!"{k} expects an integer, got '{v}'"
  match args with
  | [] => pure o
  | "--" :: t => pure { o with positional := o.positional ++ t.toArray }
  | "-C" :: v :: t | "--root" :: v :: t => parseOpts t { o with root := v }
  | "-l" :: t | "--lines" :: t => parseOpts t { o with lines := true }
  | "-i" :: t | "--ignore-case" :: t => parseOpts t { o with icase := true }
  | "-w" :: v :: t | "--width" :: v :: t => nat "--width" v (fun n => { o with width := n }) >>= parseOpts t
  | "--since" :: v :: t => nat "--since" v (fun n => { o with since := some n }) >>= parseOpts t
  | "--last" :: v :: t => nat "--last" v (fun n => { o with last := some n }) >>= parseOpts t
  | a :: t =>
    if a.startsWith "-" && a.length > 1 && (o.positional[0]?.getD "") != "grep" then throw s!"unknown option '{a}'"
    else parseOpts t { o with positional := o.positional.push a }

def printAll (ls : Array String) : IO Unit := do
  let out ← IO.getStdout
  for l in ls do out.putStrLn l

def run (o : Opts) : IO UInt32 := do
  let cmd := o.positional[0]!
  let arg? := o.positional[1]?
  let docs : System.FilePath := o.root / "DOCS.md"
  if !(← docs.pathExists) then return ← die s!"DOCS.md not found at {docs} (pass -C ROOT)" 2
  let text := ((← IO.FS.readFile docs).replace "\r\n" "\n").replace "\r" "\n"
  let lines := (text.splitOn "\n").toArray
  let lines := if lines.size > 0 && lines[lines.size-1]! == "" then lines.pop else lines
  let emitE (r : Except String (Array String)) : IO UInt32 := do
    match r with | .ok ls => printAll ls; pure 0 | .error e => die e
  match cmd with
  | "toc" => printAll (cmdToc lines); pure 0
  | "items" => printAll (cmdItems lines o.since o.last o.width); pure 0
  | "item" =>
    let some n := arg? | die "item: missing N" 2
    emitE (do let it ← lookup (findItems lines) n; pure (emit lines it.start it.end_ o.lines))
  | "next" => emitE (cmdNext lines arg?)
  | "remaining" => emitE (cmdRemaining lines o.lines o.width)
  | "steps" => emitE (cmdSteps lines o.lines)
  | "grep" =>
    let some pat := arg? | die "grep: missing REGEX" 2
    match Regex.compile pat with
    | .error e => die s!"grep: bad pattern '{pat}': {e}" 2
    | .ok rx =>
      let (out, total) := cmdGrep lines rx o.icase o.width
      printAll out
      IO.eprintln s!"# {total} matching lines"
      pure 0
  | "section" =>
    let some p := arg? | die "section: missing PREFIX" 2
    emitE (cmdSection lines p o.lines)
  | c => die s!"unknown command '{c}'\n{usage}" 2

public def main (args : List String) : IO UInt32 := do
  let args := if args.headD "" == "--" then args.drop 1 else args
  if args.isEmpty then IO.println usage; return 2
  let opts := args.takeWhile (· != "--")
  if opts.contains "-h" || opts.contains "--help" then IO.println usage; return 0
  if opts.contains "--version" then IO.println "scripts-docs-nav 1.0 (Rule 9 phase 2)"; return 0
  match parseOpts args {} with
  | .error e => die s!"{e}\n{usage}" 2
  | .ok o => if o.positional.isEmpty then die usage 2 else run o
