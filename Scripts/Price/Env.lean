module

public import Scripts.Punt.Price
public import Scripts.Flip.Patch
meta import Scripts.Punt.Price

/-!
# Scripts.Price.Env — one `lake env lean` run over a patched copy of a library file

Shared by `lake run punt-price` and `lake run price`: write the patched lines over the
target, run `lake env lean TARGET` from the repository root, restore the original bytes
and hand back Lean's stdout+stderr — unless Lean exited nonzero without reporting a single
error location in the target (Lake or the toolchain failed before elaborating the file): that
is an error, never a zero price.  The original is first copied to `TARGET<suffix>`
(each Python's backup name), so an interrupted run leaves a recoverable copy beside the
source; a run refuses to start while one exists, and it is removed only after the restored
bytes are verified.  Both digests go to stderr (Rule 9), stdout stays the Python's.
-/

namespace Scripts.Price.Env

public section

/-- `^TARGET:(\d+):(\d+): error` on some line: Lean reached the target and reported a
    location in it.  A nonzero exit WITHOUT one is Lake or the toolchain failing before (or
    instead of) elaborating the file — not a zero price. -/
def hasTargetError (target out : String) : Bool :=
  (out.splitOn "\n").any fun l =>
    let pre := target ++ ":"
    l.startsWith pre &&
      let rest := (Scripts.Punt.Price.drop l pre.length).toList
      let d1 := rest.takeWhile Char.isDigit
      let rest := rest.drop d1.length
      !d1.isEmpty && rest.head? == some ':' &&
        let d2 := (rest.drop 1).takeWhile Char.isDigit
        !d2.isEmpty && (String.ofList ((rest.drop 1).drop d2.length)).startsWith ": error"

#guard hasTargetError "a/b.lean" "x\na/b.lean:12:4: error: boom\n"
#guard !hasTargetError "a/b.lean" "error: failed to load Lean configuration\n"
#guard !hasTargetError "a/b.lean" "a/b.lean:12:4: warning: unused\n"
#guard !hasTargetError "a/b.lean" "other/b.lean:12:4: error: boom\n"

/-- The last `n` lines of a log, for a diagnostic. -/
def tailLines (out : String) (n : Nat) : String :=
  let ls := (out.splitOn "\n").filter (· != "")
  "\n".intercalate (ls.drop (ls.length - min n ls.length))

def leanOn (root : System.FilePath) (target : String) (suffix : String)
    (original : String) (patched : Array String) : IO (Except String String) := do
  let path := root / target
  let backup := System.FilePath.mk (path.toString ++ suffix)
  if ← backup.pathExists then
    return .error s!"{backup} exists: an earlier run was interrupted, so {target} may be the patched copy; inspect it, restore from the backup, delete the backup, then re-run"
  let before := Scripts.Flip.Patch.digest original.toUTF8
  IO.eprintln s!"digest before  {target}  {before}"
  IO.FS.writeFile backup original
  let res ← try
    IO.FS.writeFile path ("\n".intercalate patched.toList)
    let r ← IO.Process.output { cmd := "lake", args := #["env", "lean", target], cwd := some root }
    let out := r.stdout ++ r.stderr
    if r.exitCode != 0 && !hasTargetError target out then
      pure (.error s!"lake env lean {target} exited {r.exitCode} without an error location in {target} — not a reading (Lake or the toolchain failed before elaborating the file):\n{tailLines out 20}")
    else pure (.ok out)
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
