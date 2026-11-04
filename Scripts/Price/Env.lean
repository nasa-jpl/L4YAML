module

public import Scripts.Punt.Price
public import Scripts.Flip.Patch

/-!
# Scripts.Price.Env — one `lake env lean` run over a patched copy of a library file

Shared by `lake run punt-price` and `lake run price`: write the patched lines over the
target, run `lake env lean TARGET` from the repository root, restore the original bytes
and hand back Lean's stdout+stderr.  The original is first copied to `TARGET<suffix>`
(each Python's backup name), so an interrupted run leaves a recoverable copy beside the
source; a run refuses to start while one exists, and it is removed only after the restored
bytes are verified.  Both digests go to stderr (Rule 9), stdout stays the Python's.
-/

namespace Scripts.Price.Env

public section

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
    pure (.ok (r.stdout ++ r.stderr))
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
