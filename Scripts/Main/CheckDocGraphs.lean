module

@[expose] public section Blanket

/-!
# `scripts-check-doc-graphs` — every graph the Verso doc embeds is in the tree

```
lake run check-doc-graphs       -- or: lake exe scripts-check-doc-graphs [-C ROOT] [--strict]
```

`doc/Doc/**/*.lean` embeds images as `![…](graphs/<path>.svg)`, resolved against
`doc/Doc/L4YAML/graphs/` (staged once at the site root by `Doc/Main.lean`'s
`extraFilesHtml`).  The theorem dependency graphs are committed there, refreshed from
L4YAML.FGM's `theoremgraph`; `import-graph.svg` alone is rendered by CI (`lake exe
graph` + `dot`) just before the doc builds.  Verso does not fail on a missing image,
so this gate does: a reference with no file is a broken `<img>` on the published
site.  `--strict` also requires the CI-rendered graphs (run it after that step).
-/

namespace Scripts.CheckDocGraphs

def version : String := "scripts-check-doc-graphs 1.0 (doc graph references gate)"

def usage : String :=
"usage: lake exe scripts-check-doc-graphs [options]

Doc graphs gate: every `graphs/<path>` an image reference under doc/Doc/ names
exists under doc/Doc/L4YAML/graphs/.

options:
  -C, --root DIR      repository root (default: .)
  --strict            also require the graphs CI renders (import-graph.svg)
  -V, --version       print the version and exit
  -h, --help          print this help and exit

exit status: 0 green, 1 missing graphs, 2 usage or I/O error."

def docDir : System.FilePath := "doc" / "Doc"
def graphsDir : System.FilePath := docDir / "L4YAML" / "graphs"

/-- Graphs the workflow renders in place rather than committing. -/
def ciRendered : List String := ["import-graph.svg"]

structure Ref where
  file : String
  line : Nat
  path : String
  deriving Repr

/-- Every `](graphs/…)` on one line, in order. -/
partial def refsIn (line : String) : List String :=
  let marker := "](graphs/"
  let rec go (s : String) (acc : List String) : List String :=
    match s.splitOn marker with
    | _ :: rest :: more =>
      let tail := marker.intercalate (rest :: more)
      let path := (tail.takeWhile (fun c => c != ')' && c != ' ')).toString
      go (tail.drop path.length).toString (if path.isEmpty then acc else acc ++ [path])
    | _ => acc
  go line []

def collect (root : System.FilePath) : IO (Array Ref) := do
  let files ← (root / docDir).walkDir
  let mut out : Array Ref := #[]
  for f in files.qsort (fun a b => a.toString < b.toString) do
    if f.extension != some "lean" then continue
    let text ← IO.FS.readFile f
    let rel := (f.toString.drop (root.toString.length + 1)).toString
    let mut n := 0
    for l in text.splitOn "\n" do
      n := n + 1
      for p in refsIn l do
        out := out.push { file := rel, line := n, path := p }
  return out

def run (root : String) (strict : Bool) : IO UInt32 := do
  let rootP : System.FilePath := root
  unless ← (rootP / graphsDir).isDir do
    IO.eprintln s!"scripts-check-doc-graphs: {graphsDir} is not a directory"; return 2
  let refs ← collect rootP
  let mut missing := 0
  let mut generated := 0
  let mut seen : List String := []
  for r in refs do
    if seen.contains r.path then continue
    seen := r.path :: seen
    let present ← (rootP / graphsDir / r.path).pathExists
    if present then continue
    if !strict && ciRendered.contains r.path then
      generated := generated + 1
      IO.println s!"ci-rendered: graphs/{r.path} ({r.file}:{r.line})"
    else
      missing := missing + 1
      IO.println s!"missing: graphs/{r.path} ({r.file}:{r.line})"
  IO.println s!"doc graphs: refs={refs.size} distinct={seen.length} ci-rendered={generated} missing={missing}"
  return if missing == 0 then 0 else 1

inductive Parsed where
  | run (root : String) (strict : Bool)
  | help
  | version
  | bad (msg : String)

def parseArgs : List String → String → Bool → Parsed
  | [], r, s => .run r s
  | ("-h" :: _), _, _ | ("--help" :: _), _, _ => .help
  | ("-V" :: _), _, _ | ("--version" :: _), _, _ => .version
  | ("-C" :: d :: rest), _, s | ("--root" :: d :: rest), _, s => parseArgs rest d s
  | ("--strict" :: rest), r, _ => parseArgs rest r true
  | (a :: _), _, _ => .bad s!"unknown argument `{a}`"

end Scripts.CheckDocGraphs

open Scripts.CheckDocGraphs in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args "." false with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-check-doc-graphs: {m}\n{usage}"; return 2
  | .run r s => run r s
