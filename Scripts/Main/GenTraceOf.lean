module

public import Scripts.TraceOf.Gen
public import Lean.Parser.Module
public import Lean.Elab.Import
public import Lean.Util.Path

/-!
# `lake run gen-traceof` — regenerate `TraceOf/Node.lean` from `Surface/Node.lean`

The port of `scripts/gen_traceof.py` (Rule 9 phase 2).  The mutual block is read off
the syntax tree, not the text: the file is parsed with Lean's own parser in the
environment its header imports (so `@[yaml_spec …]` and every notation parse), and
each `inductive` / constructor / premise is a node with a source span.  The twin
block is then `Scripts.TraceOf.Gen` — the Python's rewriting, pinned by its
`#guard` rows — printed to stdout as the Python printed it.

exit status: 0 generated (or `--check` agrees); 1 the source does not parse or import,
no mutual block, `--check` differs, or `-o` unwritable; 2 usage.
-/

namespace Scripts.GenTraceOf

open Lean Parser Elab
open Scripts.TraceOf.Gen

def version : String := "scripts-gen-traceof 1.0 (Rule 9 phase 2)"

def usage : String := "usage: lake run gen-traceof [-- options]

Regenerate L4YAML/Proofs/Serialization/TraceOf/Node.lean, the event-annotated
twin of L4YAML/Surface/Node.lean's mutual block, on stdout.

options:
  -o, --out FILE    write the module to FILE instead of stdout
  -k, --check       compare with the checked-in TraceOf/Node.lean; exit 1 if it differs
  -r, --report      list the mutual inductives, the bearing closure and ctor counts
  -C, --root ROOT   repository root (default: the current directory)
  -h, --help        this message
  -V, --version     version"

structure Opts where
  root : System.FilePath := "."
  out : Option String := none
  check : Bool := false
  report : Bool := false

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg; pure code

partial def parseOpts (args : List String) (o : Opts) : Except String Opts :=
  match args with
  | [] => pure o
  | "-o" :: v :: t | "--out" :: v :: t => parseOpts t { o with out := some v }
  | "-k" :: t | "--check" :: t => parseOpts t { o with check := true }
  | "-r" :: t | "--report" :: t => parseOpts t { o with report := true }
  | "-C" :: v :: t | "--root" :: v :: t => parseOpts t { o with root := v }
  | a :: _ => throw s!"unknown argument '{a}'"

def source : System.FilePath := "L4YAML" / "Surface" / "Node.lean"
def target : System.FilePath := "L4YAML" / "Proofs" / "Serialization" / "TraceOf" / "Node.lean"

def span (text : String) (stx : Syntax) : String :=
  match stx.getPos?, stx.getTailPos? with
  | some a, some b => (Substring.Raw.mk text a b).toString
  | _, _ => ""

/-- The Python's premise text: the source span, comments removed, stripped. -/
def termText (text : String) (stx : Syntax) : String :=
  (stripComments (span text stx)).trimAscii.toString

partial def arrows (t : Syntax) : List Syntax :=
  if t.isOfKind ``Term.arrow then t[0] :: arrows t[2] else [t]

/-- `ctor`: `[0] doc? [1] "|" [2] modifiers [3] name [4] optDeclSig ([0] binders, [1] [typeSpec ":" type])`. -/
def readCtor (text : String) (ct : Syntax) : Except String Ctor := do
  let name := ct[3].getId.toString
  let sig := ct[4]
  let bs := sig[0].getArgs
  let binders := match bs[0]?.bind (·.getPos?), bs.back?.bind (·.getTailPos?) with
    | some a, some b => (Substring.Raw.mk text a b).toString
    | _, _ => ""
  let ty := sig[1][0][1]
  if ty.isMissing then throw s!"constructor {name}: no type"
  let parts := (arrows ty).map (termText text)
  return { name, binders, premises := (parts.dropLast).toArray, concl := parts.getLast! }

/-- `inductive`: `[1] declId [2] optDeclSig [3] "where" [4] ctors`. -/
def readInd (text : String) (decl : Syntax) : Except String (Option Ind) := do
  let ind := decl[1]
  if !ind.isOfKind ``Command.inductive then return none
  let name := ind[1][0].getId.toString
  let sig := termText text ind[2][1][0][1]
  let ctors ← ind[4].getArgs.toList.mapM (readCtor text)
  return some { name, sig, ctors := ctors.toArray }

def readBlock (text : String) (cmds : Array Syntax) : Except String (Array Ind) := do
  let some m := cmds.find? (·.isOfKind ``Command.mutual) | throw "no mutual block"
  let inds ← m[1].getArgs.toList.filterMapM (readInd text)
  return inds.toArray

unsafe def run (args : List String) : IO UInt32 := do
  if args.contains "-h" || args.contains "--help" then IO.println usage; return 0
  if args.contains "-V" || args.contains "--version" then IO.println version; return 0
  let args := if args.headD "" == "--" then args.drop 1 else args
  let o ← match parseOpts args {} with
    | .ok o => pure o
    | .error e => return ← die s!"{e}\n{usage}" 2
  let root ← IO.FS.realPath o.root
  let src := root / source
  if !(← src.pathExists) then return ← die s!"{src} not found (pass -C ROOT)"
  let text ← IO.FS.readFile src
  enableInitializersExecution
  -- the toolchain is the repository's (elan reads `lean-toolchain` from the cwd), so ask from `root`
  let r ← IO.Process.output { cmd := "lean", args := #["--print-prefix"], cwd := some root }
  if r.exitCode != 0 then return ← die s!"lean --print-prefix failed in {root}: {r.stderr}"
  initSearchPath (System.FilePath.mk r.stdout.trimAscii.toString) [root / ".lake" / "build" / "lib" / "lean"]
  let ictx := mkInputContext text src.toString
  let (hdr, st, msgs) ← parseHeader ictx
  let (env, msgs) ← processHeader hdr {} msgs ictx
  if msgs.hasErrors then
    for m in msgs.toList do IO.eprint (← m.toString)
    return ← die s!"{source}: its imports did not load (build L4YAML first)"
  let cmds ← try testParseModuleAux env ictx st msgs #[]
    catch e => return ← die s!"{source}: {e}"
  let inds ← match readBlock text cmds with
    | .ok i => pure i
    | .error e => return ← die s!"{source}: {e}"
  if o.report then
    for l in report inds do IO.println l
    return 0
  let gen := render inds
  if o.check then
    let cur ← try IO.FS.readFile (root / target) catch _ => pure ""
    if cur == gen then IO.println s!"gen-traceof: {target} agrees with {source}"; return 0
    return ← die s!"gen-traceof: {target} differs from what {source} generates — rerun `lake run gen-traceof -- -o {target}`"
  match o.out with
  | some f =>
    try IO.FS.writeFile f gen catch e => return ← die s!"cannot write {f}: {e}"
    IO.println s!"gen-traceof: wrote {f}"
  | none => IO.print gen
  return 0

end Scripts.GenTraceOf

public unsafe def main (args : List String) : IO UInt32 := Scripts.GenTraceOf.run args
