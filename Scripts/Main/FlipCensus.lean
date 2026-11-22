module

public import Scripts.Lean.BuildLog

@[expose] public section Blanket

/-!
# scripts-flip-census — error sites of a build log, resolved to declarations

```
lake exe scripts-flip-census [BUILD.log [REPO_ROOT]] [-h] [-V]
```

The port of `scripts/flip_census.py`: reads a `lake build` log (a file, or
stdin when no file is given), resolves each `file:line:col: error:` site to
the enclosing declaration or gate command (`Scripts.Lean.BuildLog`), and
prints the Python's report byte for byte — the sites, the DISTINCT
declarations keyed by `(file, kind, name)`, the files, and the
`TALLY declarations=… gate-sites=… sites=… files=…` line that prices a flip.
A single run reports a FLOOR (a failing module blocks its dependents).
-/

open Scripts.Lean.BuildLog

namespace Scripts.FlipCensus

def version : String := "scripts-flip-census 0.1.0 (L4YAML Rule 9 port of flip_census.py)"

def usage : String :=
"usage: lake exe scripts-flip-census [BUILD.log [REPO_ROOT]]

Resolve every `file:line:col: error:` (either lake ordering) in BUILD.log
(stdin when omitted) to its enclosing declaration, read off the source
under REPO_ROOT (default: .).  Gate sites (#guard/#eval/#guard_msgs/
#check/#print/#reduce) are their own class, not billed to the preceding
def.  One run is a FLOOR: sorry the breakages, rebuild, re-run.

  -V, --version   print the version and exit
  -h, --help      print this help and exit

exit status: 0 (report printed), 2 usage or I/O error."

/-- One resolved site: file (as logged), line, owner, message head. -/
structure ResolvedSite where
  rel : String
  line : Nat
  owner : Option Owner
  msg40 : String
  deriving Repr, Inhabited

/-- Python `str.splitlines()` on the file contents, for the line table. -/
def splitLines (s : String) : Array String :=
  -- `splitlines` also splits on \r, \v, \f, \x1c-\x1e, \x85, \u2028, \u2029; Lean
  -- sources in this tree carry only \n, so \n (with a trailing \r dropped) is read.
  let parts := (s.splitOn "\n").map fun l => if l.endsWith "\r" then String.ofList l.toList.dropLast else l
  -- a trailing newline does not open a last empty line
  let arr := parts.toArray
  if arr.size > 0 && arr.back! == "" then arr.pop else arr

#guard splitLines "a\nb\n" == #["a", "b"]
#guard splitLines "a\nb" == #["a", "b"]
#guard splitLines "" == #[]

/-- Python's `repr` of a `str` for the `files:` line: single quotes unless
the text has a `'` and no `"`. -/
def pyRepr (s : String) : String :=
  if s.any (· == '\'') && !s.any (· == '"') then s!"\"{s}\"" else s!"'{s}'"

def pyReprList (xs : List String) : String :=
  "[" ++ ", ".intercalate (xs.map pyRepr) ++ "]"

#guard pyReprList ["MarkedColsDomain.lean"] == "['MarkedColsDomain.lean']"
#guard pyReprList [] == "[]"

def pyListNat (xs : List Nat) : String :=
  "[" ++ ", ".intercalate (xs.map toString) ++ "]"

def take40 (s : String) : String := String.ofList (s.toList.take 40)

structure Key where
  rel : String
  kind : String
  name : String
  deriving DecidableEq, Repr, Inhabited

/-- `OrderedDict.setdefault` over `(rel, kind, name)`: first-seen order, lines appended. -/
def distinctOf (sites : Array ResolvedSite) : Array (Key × Array Nat) := Id.run do
  let mut out : Array (Key × Array Nat) := #[]
  for s in sites do
    match s.owner with
    | none => pure ()
    | some o =>
      let k : Key := ⟨s.rel, o.kind, o.name⟩
      match out.findIdx? (·.1 == k) with
      | some i => out := out.modify i fun (k, ls) => (k, ls.push s.line)
      | none => out := out.push (k, #[s.line])
  return out

/-- `sorted(set(lines))`. -/
def sortedSet (xs : Array Nat) : List Nat :=
  (xs.foldl (fun (acc : Array Nat) x => if acc.contains x then acc else acc.push x) #[]).qsort (· < ·) |>.toList

/-- The report, as the Python prints it. -/
def report (sites : Array ResolvedSite) : String := Id.run do
  let mut out : Array String := #[]
  out := out.push s!"=== {sites.size} error sites, resolved to the enclosing declaration ==="
  for s in sites do
    let shown := match s.owner with
      | some o => s!"{o.kind} {o.name}"
      | none => "<no enclosing declaration>"
    out := out.push s!"  {s.rel}:{s.line}  {shown}   [{s.msg40}]"
  let distinct := distinctOf sites
  out := out.push ""
  out := out.push s!"=== {distinct.size} DISTINCT declarations broken (the number that prices the work) ==="
  for (k, ls) in distinct do
    out := out.push s!"  {k.kind} {k.name}  ({baseName k.rel}, lines {pyListNat (sortedSet ls)})"
  -- files: sorted set of basenames of the distinct keys
  let files := (distinct.foldl (fun (acc : Array String) (k, _) =>
      let b := baseName k.rel
      if acc.contains b then acc else acc.push b) #[]).qsort (· < ·) |>.toList
  let cmds := distinct.filter fun (k, _) => (commandOf ("#" ++ String.ofList (k.kind.toList.dropWhile (· == '#')))).isSome
  let decls := distinct.size - cmds.size
  out := out.push ""
  out := out.push s!"files: {files.length}  {pyReprList files}"
  out := out.push s!"TALLY declarations={decls} gate-sites={cmds.size} sites={sites.size} files={files.length}"
  if !cmds.isEmpty then
    out := out.push "  gate sites are NOT declarations to repair; they are pins to re-decide:"
    for (k, _) in cmds do
      out := out.push s!"    {k.kind} {k.name}  ({baseName k.rel})"
  return "\n".intercalate out.toList ++ "\n"

/-- Resolve the sites of a log against the tree under `root`; files that
cannot be read resolve to no owner (Python's `OSError → (None, None)`). -/
def resolve (root : System.FilePath) (log : String) : IO (Array ResolvedSite) := do
  let mut out : Array ResolvedSite := #[]
  let mut cache : Array (String × Option (Array String)) := #[]
  for raw in log.splitOn "\n" do
    match parseErr raw with
    | none => pure ()
    | some e =>
      let lines ← match cache.find? (·.1 == e.file) with
        | some (_, l) => pure l
        | none => do
          let l ← (do
            let t ← IO.FS.readFile (root / e.file)
            pure (some (splitLines t))) <|> pure none
          cache := cache.push (e.file, l)
          pure l
      let owner := match lines with
        | none => none
        | some ls => enclosing (baseName e.file) ls e.line
      out := out.push ⟨e.file, e.line, owner, take40 e.msg⟩
  return out

inductive Parsed where
  | help | version
  | run (log : Option String) (root : String)
  | bad (msg : String)

def parseArgs : List String → Parsed
  | [] => .run none "."
  | ["-h"] | ["--help"] => .help
  | ["-V"] | ["--version"] => .version
  | args =>
    match args.find? fun a => a.startsWith "-" with
    | some a => .bad s!"unknown option `{a}`"
    | none =>
      match args with
      | [log] => .run (some log) "."
      | [log, root] => .run (some log) root
      | a :: _ => .bad s!"too many arguments at `{a}`"
      | [] => .run none "."

end Scripts.FlipCensus

open Scripts.FlipCensus in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-flip-census: {m}\n{usage}"; return 2
  | .run log root =>
    let text ← try
        match log with
        | some p => IO.FS.readFile p
        | none => (← IO.getStdin).readToEnd
      catch e =>
        IO.eprintln s!"scripts-flip-census: cannot read {log.getD "stdin"}: {e}"
        return 2
    let sites ← resolve root text
    IO.print (report sites)
    return 0
