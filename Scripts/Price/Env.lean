module

public import Scripts.Punt.Price
public import Scripts.Flip.Patch
meta import Scripts.Punt.Price

/-!
# Scripts.Price.Env — one `lake env lean` run over a patched copy of a library file

Shared by `lake run punt-price` and `lake run price`: write the patched lines over the
target, run `lake env lean TARGET` from the repository root, restore the original bytes
and hand back Lean's stdout+stderr — unless Lean exited nonzero without reporting a single
error location in the target (Lake or the toolchain failed before elaborating the file), or
reported one in the target's import header (a dependency's `.olean` missing or stale, so the
probe never elaborated): both are errors, never a reading.  The original is first copied to `TARGET<suffix>`
(each Python's backup name), so an interrupted run leaves a recoverable copy beside the
source; a run refuses to start while one exists, and it is removed only after the restored
bytes are verified.  Both digests go to stderr (Rule 9), stdout stays the Python's.
-/

namespace Scripts.Price.Env

public section

/-- `^TARGET:(\d+):(\d+): error` → the line, for every such line of the log. -/
def targetErrorLines (target out : String) : List Nat :=
  (out.splitOn "\n").filterMap fun l => do
    let pre := target ++ ":"
    guard (l.startsWith pre)
    let rest := (Scripts.Punt.Price.drop l pre.length).toList
    let d1 := rest.takeWhile Char.isDigit
    guard !d1.isEmpty
    let rest := rest.drop d1.length
    guard (rest.head? == some ':')
    let d2 := (rest.drop 1).takeWhile Char.isDigit
    guard !d2.isEmpty
    guard ((String.ofList ((rest.drop 1).drop d2.length)).startsWith ": error")
    return (String.ofList d1).toNat!

#guard targetErrorLines "a/b.lean" "x\na/b.lean:12:4: error: boom\na/b.lean:3:0: error: y\n" == [12, 3]
#guard targetErrorLines "a/b.lean" "error: failed to load Lean configuration\n" == []
#guard targetErrorLines "a/b.lean" "a/b.lean:12:4: warning: unused\n" == []
#guard targetErrorLines "a/b.lean" "other/b.lean:12:4: error: boom\n" == []

/-- Lean reached the target and reported a location in it.  A nonzero exit WITHOUT one is
    Lake or the toolchain failing before (or instead of) elaborating the file — not a zero
    price. -/
def hasTargetError (target out : String) : Bool := !(targetErrorLines target out).isEmpty

/-- `module` / `[public|private|meta] import …` at the start of a line. -/
def isHeaderLine (l : String) : Bool :=
  let ws := (l.splitOn " ").filter (· != "")
  match ws with
  | "module" :: _ => true
  | "import" :: _ => true
  | "public" :: "meta" :: "import" :: _ => true
  | w :: "import" :: _ => w == "public" || w == "private" || w == "meta"
  | _ => false

/-- The 1-based line of the file's last `module` / `import` line (0 if none): an error at or
    above it is an import that did not load (a dependency's `.olean` missing or stale), after
    which nothing the probe reports is a reading. -/
def headerEnd (lines : Array String) : Nat := Id.run do
  let mut last := 0
  for i in [0:lines.size] do
    if isHeaderLine lines[i]! then last := i + 1
  return last

#guard headerEnd #["module", "", "public import A.B", "meta import C", "", "namespace X", "import_tax := 1"] == 4
#guard headerEnd #["lemma a : True := trivial"] == 0
#guard isHeaderLine "public meta import A"

/-- `L4YAML/Proofs/Production/StreamAccum.lean` → `L4YAML.Proofs.Production.StreamAccum`. -/
def moduleOf (target : String) : String :=
  let t := if target.endsWith ".lean" then Scripts.Punt.Price.take target (target.length - 5) else target
  String.map (fun c => if c == '/' then '.' else c) t

#guard moduleOf "L4YAML/Proofs/Production/StreamAccum.lean" == "L4YAML.Proofs.Production.StreamAccum"

/-- A wide (`lake build`) log shows the patched module was reached: a `Built M` / `Building M`
    / `Replayed M` record for it (`M (`, `M:` or end of line after the name). -/
def reachedModule (target out : String) : Bool :=
  let m := moduleOf target
  (out.splitOn "\n").any fun l =>
    ["Built ", "Building ", "Replayed "].any fun kw =>
      let parts := l.splitOn (kw ++ m)
      parts.length > 1 && ((parts.drop 1).head!.isEmpty || (parts.drop 1).head!.startsWith " " || (parts.drop 1).head!.startsWith ":")

#guard reachedModule "L4YAML/Proofs/Production/StreamAccum.lean" "✔ [3/9] Built L4YAML.Proofs.Production.StreamAccum (12s)\n"
#guard reachedModule "L4YAML/Proofs/Production/StreamAccum.lean" "✖ [3/9] Building L4YAML.Proofs.Production.StreamAccum\n"
#guard !reachedModule "L4YAML/Proofs/Production/StreamAccum.lean" "✔ [3/9] Built L4YAML.Proofs.Production.StreamAccumX (1s)\n"
#guard !reachedModule "L4YAML/Proofs/Production/StreamAccum.lean" "error: Tests/X.lean:12:3: boom\n"

/-- The last `n` lines of a log, for a diagnostic. -/
def tailLines (out : String) (n : Nat) : String :=
  let ls := (out.splitOn "\n").filter (· != "")
  "\n".intercalate (ls.drop (ls.length - min n ls.length))

/-- `lake build MODULE` on the pristine tree, before anything is patched: Lake's content hashes
    are the freshness oracle, so afterwards the module's `.olean*` describe the source the probes
    read (`Scripts.Lean.DeclRanges` maps error lines onto its declaration ranges).  Up to date in
    seconds; a stale module is rebuilt; a failure is a failure, not a reading. -/
def ensureBuilt (root : System.FilePath) (target : String) : IO (Except String Unit) := do
  let r ← IO.Process.output { cmd := "lake", args := #["build", moduleOf target], cwd := some root }
  if r.exitCode != 0 then
    return .error s!"lake build {moduleOf target} exited {r.exitCode} on the pristine tree — nothing below is a reading until the library builds:\n{tailLines (r.stdout ++ r.stderr) 20}"
  return .ok ()

/-- `lake env lean TARGET` (or, with `wide`, `lake build`) over the patched copy → Lean's exit
    code and its stdout+stderr. -/
def leanOn (root : System.FilePath) (target : String) (suffix : String)
    (original : String) (patched : Array String) (wide : Bool := false) : IO (Except String (UInt32 × String)) := do
  let path := root / target
  let backup := System.FilePath.mk (path.toString ++ suffix)
  if ← backup.pathExists then
    return .error s!"{backup} exists: an earlier run was interrupted, so {target} may be the patched copy; inspect it, restore from the backup, delete the backup, then re-run"
  let before := Scripts.Flip.Patch.digest original.toUTF8
  IO.eprintln s!"digest before  {target}  {before}"
  IO.FS.writeFile backup original
  let res ← try
    IO.FS.writeFile path ("\n".intercalate patched.toList)
    let args := if wide then #["build"] else #["env", "lean", target]
    let r ← IO.Process.output { cmd := "lake", args, cwd := some root }
    let out := r.stdout ++ r.stderr
    let locs := targetErrorLines target out
    if wide then
      if r.exitCode == 0 || !locs.isEmpty || reachedModule target out then pure (.ok (r.exitCode, out))
      else pure (.error s!"lake build exited {r.exitCode} without reaching {target} (no `Built`/`Building` line for its module and no error location in it) — an unrelated failure, not a reading:\n{tailLines out 20}")
    else if r.exitCode != 0 && locs.isEmpty then
      pure (.error s!"lake env lean {target} exited {r.exitCode} without an error location in {target} — not a reading (Lake or the toolchain failed before elaborating the file):\n{tailLines out 20}")
    else if locs.any (· ≤ headerEnd patched) then
      pure (.error s!"lake env lean {target}: an error in the file's import header (line {(locs.filter (· ≤ headerEnd patched)).head!}) — a dependency did not load, so nothing below it is a reading; build the library first (`lake build L4YAML`):\n{tailLines out 20}")
    else pure (.ok (r.exitCode, out))
  catch e => pure (.error s!"{e}")
  IO.FS.writeFile path original
  let after := Scripts.Flip.Patch.digest (← IO.FS.readBinFile path)
  IO.eprintln s!"digest after   {target}  {after}"
  if after != before then
    return .error s!"{target} was not restored (backup kept at {backup}); fix the source before trusting anything else"
  IO.FS.removeFile backup
  return res

end

end Scripts.Price.Env
