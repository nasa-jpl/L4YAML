module

@[expose] public section Blanket

/-!
# Scripts.Git — the two git calls a flip at a revision needs

`showAt root rev path` reads `rev:path`; `othersDiffer root rev lib paths` is
`git diff --quiet REV -- LIB :!PATH…` against the WORKING TREE (uncommitted
edits count), the refusal every `--rev` flip documents: a build would read a
mixed tree if any other library file differed between REV and the checkout.
-/

namespace Scripts.Git

def run (root : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args, cwd := some root }

/-- `git show REV:PATH`, or the stderr line when git refuses. -/
def showAt (root : System.FilePath) (rev path : String) : IO (Except String String) := do
  let o ← run root #["show", s!"{rev}:{path}"]
  return if o.exitCode == 0 then .ok o.stdout else .error o.stderr.trimAscii.toString

/-- Does any file under `lib` other than `paths` differ between `rev` and the
working tree?  (`git diff --quiet REV -- LIB :!P…`; exit 1 = differs.) -/
def othersDiffer (root : System.FilePath) (rev lib : String) (paths : List String) : IO Bool := do
  let o ← run root (#["diff", "--quiet", rev, "--", lib] ++ (paths.map fun p => s!":!{p}").toArray)
  return o.exitCode != 0

end Scripts.Git
