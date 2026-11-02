module

public import Scripts.Pins

@[expose] public section Blanket

/-!
# scripts-repin — rewrite moved `def expected… :=` pins from one build log

```
lake exe scripts-repin BUILD.log [REPO_ROOT] [-c|--check] [-h] [-V]
```

The port of `scripts/repin.py`.  For every `expected:`/`got:` block in the
log it finds the `throwError` whose title matches, the `def expected… : T :=`
it names, and rewrites the literal to what the build reported
(`Scripts.Pins`).  `--check` reports and writes nothing.  One run is a
FLOOR — rebuild and re-run until nothing moves — and read each change: a
pin is a decision, the exe only does the typing.  Output and exit status
are the Python's: 0 when something was re-pinned or nothing was skipped,
1 when only skips, 2 usage.
-/

open Scripts.Pins

namespace Scripts.Repin

def version : String := "scripts-repin 0.1.0 (L4YAML Rule 9 port of repin.py)"

def usage : String :=
"usage: lake exe scripts-repin BUILD.log [REPO_ROOT] [options]

Re-derive the census pins (`def expected… :=`) from one `lake build` log:
each `expected:`/`got:` block names its guard's pin, which is rewritten to
the value the build counted.  One run is a FLOOR: rebuild and re-run until
the log reports no moved pin, then read every change.  A pin whose literal
carries comments between its entries is `skipped` for a hand edit.

options:
  -c, --check     report what would move; write nothing
  -V, --version   print the version and exit
  -h, --help      print this help and exit

exit status: 0 re-pinned (or nothing skipped), 1 only skips, 2 usage or I/O."

structure Options where
  log : String
  root : String := "."
  check : Bool := false

inductive Parsed where
  | help | version
  | run (o : Options)
  | bad (msg : String)

def parseArgs (args : List String) : Parsed :=
  if args.isEmpty || args.contains "-h" || args.contains "--help" then .help
  else if args.contains "-V" || args.contains "--version" then .version
  else
    let check := args.contains "--check" || args.contains "-c"
    let positional := args.filter fun a => !a.startsWith "-"
    match positional with
    | [log] => .run { log, check }
    | [log, root] => .run { log, root, check }
    | [] => .bad "BUILD.log is required"
    | _ :: _ :: a :: _ => .bad s!"too many arguments at `{a}`"

/-- Python `repr` of a `str`: single quotes unless the text has a `'` and no `"`. -/
def pyRepr (s : String) : String :=
  if s.any (· == '\'') && !s.any (· == '"') then s!"\"{s}\"" else s!"'{s}'"

/-- One edit: `(pin name, expected, got, where)`. -/
structure Edit where
  name : String
  expected : String
  got : String
  where_ : String
  deriving Repr, Inhabited

structure Report where
  where_ : String
  name : String
  ty : String
  expected : String
  got : String
  flagged : Bool
  deriving Repr, Inhabited

def run (o : Options) : IO UInt32 := do
  let log ← try IO.FS.readFile o.log
    catch e => do IO.eprintln s!"scripts-repin: cannot read {o.log}: {e}"; return 2
  let root : System.FilePath := o.root
  -- edits per path, in first-seen order
  let mut edits : Array (String × Array Edit) := #[]
  let mut skipped : Array String := #[]
  for (file, line, body) in readBlocks log do
    let msg := "\n".intercalate body.toList
    match fieldAfter? "expected:" msg, fieldAfter? "got:" msg with
    | some exp, some got =>
      let path := root / file
      if !(← path.pathExists) then
        skipped := skipped.push s!"{file}:{line}: file not found under {o.root}"
        continue
      let src ← IO.FS.readFile path
      let names := pinNamesFor src body[0]!
      match names with
      | [name] =>
        let e : Edit := ⟨name, exp, got, s!"{file}:{line}"⟩
        match edits.findIdx? (·.1 == path.toString) with
        | some i => edits := edits.modify i fun (p, es) => (p, es.push e)
        | none => edits := edits.push (path.toString, #[e])
      | _ =>
        skipped := skipped.push s!"{file}:{line}: {pyRepr body[0]!} matches {names.length} throw sites {names}"
    | _, _ => pure ()
  let mut report : Array Report := #[]
  for (path, pins) in edits do
    let mut lines := ((← IO.FS.readFile path).splitOn "\n").toArray
    for e in pins do
      match defSpan lines e.name with
      | none => skipped := skipped.push s!"{e.where_}: no `def {e.name} : … :=` found"
      | some sp =>
        if sp.annotated then
          skipped := skipped.push s!"{e.where_}: `{e.name}` carries comments inside its literal; re-pin it by hand"
          continue
        let oldBody := pyStrip (sp.head.same ++ "\n" ++
          "\n".intercalate ((lines.extract (sp.start + 1 + sp.comments.size) sp.stop).toList))
        match render sp.head.ty e.got oldBody with
        | none => skipped := skipped.push s!"{e.where_}: not a list literal: {pyRepr (pyStrip e.got)}"
        | some (newText, flagged) =>
          lines := splice lines sp newText
          report := report.push ⟨e.where_, e.name, sp.head.ty, e.expected, e.got, flagged⟩
    if !o.check then
      IO.FS.writeFile path ("\n".intercalate lines.toList)
  for r in report do
    let tag := if r.flagged then "  CHECK" else ""
    let verb := if o.check then "would re-pin" else "re-pinned"
    IO.println s!"{verb} {r.where_} {r.name} : {r.ty}{tag}\n    was {r.expected}\n    now {r.got}"
  for s in skipped do IO.println s!"skipped {s}"
  if report.isEmpty && skipped.isEmpty then IO.println "no moved pin in the log"
  return if !report.isEmpty || skipped.isEmpty then 0 else 1

end Scripts.Repin

open Scripts.Repin in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .help => IO.println usage; return (if args.isEmpty then 2 else 0)
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-repin: {m}\n{usage}"; return 2
  | .run o => run o
