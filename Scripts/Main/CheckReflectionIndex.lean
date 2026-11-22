module

public import Scripts.Docs.ReflectionIndex

@[expose] public section Blanket

/-!
# scripts-check-reflection-index — the Reflections narrative-index gate

```
lake run check-reflection-index       -- or: lake exe scripts-check-reflection-index [-C ROOT]
```

Formerly `scripts/check_reflection_index.py`; see `Scripts.Docs.ReflectionIndex`.
-/

open Scripts.Docs.ReflectionIndex

namespace Scripts.CheckReflectionIndex

def version : String := "scripts-check-reflection-index 0.1.0 (L4YAML Reflections index gate)"

def usage : String :=
"usage: lake exe scripts-check-reflection-index [options]

Reflections index gate: in Tests/Reflections.lean every bullet's module is
imported, every bullet's Reflection numbers are listed by its sub-theme,
every listed number has a bullet, no number is claimed twice, blocks ascend.

options:
  -C, --root DIR      repository root (default: .)
  -V, --version       print the version and exit
  -h, --help          print this help and exit

exit status: 0 green, 1 problems, 2 usage or I/O error."

inductive Parsed where
  | run (root : String)
  | help
  | version
  | bad (msg : String)

def parseArgs : List String → String → Parsed
  | [], r => .run r
  | ("-h" :: _), _ | ("--help" :: _), _ => .help
  | ("-V" :: _), _ | ("--version" :: _), _ => .version
  | ("-C" :: d :: rest), _ | ("--root" :: d :: rest), _ => parseArgs rest d
  | (a :: _), _ => .bad s!"unknown argument `{a}`"

def run (root : String) : IO UInt32 := do
  let text ← try IO.FS.readFile ((root : System.FilePath) / index)
    catch e => do IO.eprintln s!"scripts-check-reflection-index: cannot read {index}: {e}"; return 2
  let (code, lines) := gate text
  for l in lines do IO.println l
  return code

end Scripts.CheckReflectionIndex

open Scripts.CheckReflectionIndex in
public def main (args : List String) : IO UInt32 := do
  match parseArgs args "." with
  | .help => IO.println usage; return 0
  | .version => IO.println version; return 0
  | .bad m => IO.eprintln s!"scripts-check-reflection-index: {m}\n{usage}"; return 2
  | .run r => run r
