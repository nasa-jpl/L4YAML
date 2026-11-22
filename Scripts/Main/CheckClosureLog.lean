module

public import Scripts.Docs.ClosureLog

@[expose] public section Blanket

/-!
# scripts-check-closure-log — the closure-log order gate

```
lake run check-closure-log            -- or: lake exe scripts-check-closure-log [-C ROOT] [-f DOCS]
```

`DOCS.md`'s β.5 closure log must ascend by `(item number, letter)`, must
not regress in date, and must declare every gap (`Scripts.Docs.ClosureLog.declaredGaps`)
with the anchor documenting it elsewhere.  Formerly `scripts/check_closure_log.py`;
the messages are unchanged.
-/

open Scripts.Docs.ClosureLog

namespace Scripts.CheckClosureLog

def version : String := "scripts-check-closure-log 0.1.0 (L4YAML closure-log gate)"

def usage : String :=
"usage: lake exe scripts-check-closure-log [options]

Closure-log gate: DOCS.md's `### Item N (YYYY-MM-DD)` entries parse, ascend
strictly by (number, letter), do not regress in date, and every missing
number is declared (Scripts/Docs/ClosureLog.lean, `declaredGaps`) with an
anchor that is a heading of DOCS.md.

options:
  -C, --root DIR      repository root (default: .)
  -f, --file PATH     the log, relative to the root (default: DOCS.md)
  -V, --version       print the version and exit
  -h, --help          print this help and exit

exit status: 0 green, 1 violations, 2 usage, missing file or no entries."

structure Options where
  root : String := "."
  file : String := "DOCS.md"

inductive Parsed where
  | run (o : Options)
  | help
  | version
  | bad (msg : String)

def parseArgs : List String → Options → Parsed
  | [], o => .run o
  | ("-h" :: _), _ | ("--help" :: _), _ => .help
  | ("-V" :: _), _ | ("--version" :: _), _ => .version
  | ("-C" :: d :: rest), o | ("--root" :: d :: rest), o => parseArgs rest { o with root := d }
  | ("-f" :: f :: rest), o | ("--file" :: f :: rest), o => parseArgs rest { o with file := f }
  | (a :: _), _ => .bad s!"unknown argument `{a}`"

def run (o : Options) : IO UInt32 := do
  let path : System.FilePath := (o.root : System.FilePath) / o.file
  if !(← path.pathExists) then
    IO.println s!"{o.file}: not found (run from the repository root)"
    return 2
  let (code, lines) := gate (← IO.FS.readFile path)
  for l in lines do IO.println l
  return code

end Scripts.CheckClosureLog

open Scripts.CheckClosureLog in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-check-closure-log: {m}\n{usage}"; return 2
  | .run o => run o
