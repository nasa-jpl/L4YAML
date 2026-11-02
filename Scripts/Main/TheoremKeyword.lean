module

public import Scripts.Lean.TheoremKeyword

@[expose] public section Blanket

/-!
# scripts-theorem-keyword — Rule 7's `theorem` keyword tool

```
lake run check-theorem-keyword        -- = lake exe scripts-theorem-keyword --check L4YAML
lake exe scripts-theorem-keyword (--check | --stats | --rewrite) [-w WHITELIST] [-C ROOT] ROOT...
```

Formerly `scripts/rename_lemma.py` (`--apply` is `--rewrite` here).  `--check`
exits 1 listing every `theorem` site whose `file:name` is not on the whitelist;
`--stats` counts sites; `--rewrite` turns the non-whitelisted sites into `lemma`
in place.  Messages are the Python's.
-/

open Scripts.Lean.TheoremKeyword

namespace Scripts.TheoremKeyword

def version : String := "scripts-theorem-keyword 0.1.0 (L4YAML Rule 7 tool)"

def usage : String :=
"usage: lake exe scripts-theorem-keyword (--check | --stats | --rewrite) [options] ROOT...

Rule 7: the `theorem` keyword is reserved for the @[capstone] declarations
listed in the whitelist (`relative/path.lean:name`, `#` comments, trailing
`*` = prefix wildcard); every other proof is a `lemma`.  ROOT is a .lean
file or a directory scanned recursively.

modes (exactly one):
  -c, --check         exit 1 listing every non-whitelisted `theorem` site
  -s, --stats         count `theorem` sites (whitelisted vs other)
  -r, --rewrite       rewrite non-whitelisted `theorem` -> `lemma` in place

options:
  -w, --whitelist F   whitelist file, relative to the root (default: scripts/capstones.txt)
  -C, --root DIR      repository root (default: .)
  -V, --version       print the version and exit
  -h, --help          print this help and exit

exit status: 0 green, 1 violations (--check), 2 usage or I/O error."

inductive Mode where | check | stats | rewrite
  deriving BEq, Repr

structure Options where
  mode : Option Mode := none
  whitelist : String := "scripts/capstones.txt"
  root : String := "."
  roots : Array String := #[]

inductive Parsed where
  | run (o : Options)
  | help
  | version
  | bad (msg : String)

def setMode (o : Options) (m : Mode) : Except String Options :=
  match o.mode with
  | some _ => .error "exactly one of --check, --stats, --rewrite"
  | none => .ok { o with mode := some m }

def parseArgs : List String → Options → Parsed
  | [], o =>
    if o.mode.isNone then .bad "one of --check, --stats, --rewrite is required"
    else if o.roots.isEmpty then .bad "at least one ROOT (file or directory) is required"
    else .run o
  | ("-h" :: _), _ | ("--help" :: _), _ => .help
  | ("-V" :: _), _ | ("--version" :: _), _ => .version
  | ("-c" :: rest), o | ("--check" :: rest), o => mode rest o .check
  | ("-s" :: rest), o | ("--stats" :: rest), o => mode rest o .stats
  | ("-r" :: rest), o | ("--rewrite" :: rest), o => mode rest o .rewrite
  | ("-w" :: f :: rest), o | ("--whitelist" :: f :: rest), o => parseArgs rest { o with whitelist := f }
  | ("-C" :: d :: rest), o | ("--root" :: d :: rest), o => parseArgs rest { o with root := d }
  | (a :: rest), o =>
    if a.startsWith "-" then .bad s!"unknown argument `{a}`"
    else parseArgs rest { o with roots := o.roots.push a }
where
  mode (rest : List String) (o : Options) (m : Mode) : Parsed :=
    match setMode o m with
    | .ok o => parseArgs rest o
    | .error e => .bad e

/-- `.lean` files under `root/r` (sorted, recursive) or `root/r` itself when it is a file;
returned relative to `root` with `/` separators. -/
def leanFiles (root r : String) : IO (Array String) := do
  let base : System.FilePath := root
  let p := base / r
  let paths ← if (← p.isDir) then p.walkDir else pure #[p]
  let prefix_ := (base / "").toString
  let strip (s : String) : String :=
    if s.startsWith prefix_ then String.ofList (s.toList.drop prefix_.length) else s
  let out := paths.filterMap fun q =>
    if q.extension == some "lean" then some (strip q.toString) else none
  return out.qsort (· < ·)

def run (o : Options) : IO UInt32 := do
  let wlPath : System.FilePath := (o.root : System.FilePath) / o.whitelist
  let wl ← try pure (parseWhitelist (← IO.FS.readFile wlPath))
    catch e => do IO.eprintln s!"scripts-theorem-keyword: cannot read {o.whitelist}: {e}"; return 2
  let mut files : Array String := #[]
  for r in o.roots do files := files ++ (← leanFiles o.root r)
  let mut kept := 0
  let mut renamed := 0
  let mut violations : Array (String × Nat × String) := #[]
  for rel in files do
    let text ← IO.FS.readFile ((o.root : System.FilePath) / rel)
    let mut edits : Array Nat := #[]
    for site in sites text do
      if allowed wl rel site.name then kept := kept + 1
      else
        violations := violations.push (rel, site.line, site.name)
        edits := edits.push site.offset
    if o.mode == some .rewrite && !edits.isEmpty then
      IO.FS.writeFile ((o.root : System.FilePath) / rel) (rewriteAt text edits)
      renamed := renamed + edits.size
  match o.mode with
  | some .stats =>
    IO.println s!"theorem keyword sites: {kept + violations.size} (whitelisted: {kept}, other: {violations.size}) in {files.size} files"
    return 0
  | some .check =>
    if violations.isEmpty then
      IO.println s!"OK: all {kept} `theorem` sites are whitelisted capstones"
      return 0
    for (rel, line, name) in violations do
      IO.println s!"{rel}:{line}: non-capstone `theorem {name}` (use `lemma`, or whitelist in {o.whitelist})"
    IO.eprintln s!"error: {violations.size} non-capstone `theorem` sites"
    return 1
  | _ =>
    IO.println s!"renamed {renamed} `theorem` sites to `lemma`; kept {kept} capstones"
    return 0

end Scripts.TheoremKeyword

open Scripts.TheoremKeyword in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-theorem-keyword: {m}\n{usage}"; return 2
  | .run o => run o
