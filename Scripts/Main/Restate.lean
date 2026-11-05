module

public import Scripts.Restate.Shadow
public import Scripts.Restate.Narrow
public import Scripts.Restate.Probes
public import Scripts.Flip.Patch

/-!
# `scripts-restate` — `lake run restate -- decline-all-optional | pay-chain-optional | narrow-conclusion …`

Rule 9 phase 3.3's last three instruments, the StreamAccum restate trio of items 226–228
(`decline_all_optional.py`, `pay_chain_optional.py`, `narrow_conclusion.py`): source
transforms over a proof module that let `lake build` price an obligation.  Each builds
first (a probe reads `.olean`s, not sources), edits the module in place behind a backup
copy (`<file>.lean.item22N-backup`, the Python's name), builds the module, restores the
bytes (content digests on stderr) and rebuilds so no later probe reads the experiment.
The reports are the Pythons', line for line.  Never run one beside a `lake build`.

exit status: 0 the module built under the transform (narrow: report printed); 1 the
baseline build failed, the roster probe printed no rows, the backup already exists, the
file was not restored, or (decline/pay) the transformed module did not build; 2 usage.
-/

namespace Scripts.Restate.Main

open Scripts.Restate
open Scripts.Restate.Shadow (Row rowsOf shadow)

def version : String := "scripts-restate 1.0 (Rule 9 phase 3.3, items 226–228)"

def usage : String := "usage: scripts-restate [-C ROOT] COMMAND …

  decline-all-optional [--patch-only PATH]
      decline EVERY optional-context premise of StreamAccum at once (item 226): roster off
      the environment, `have b : T := Or.inr trivial` under each lemma's `:= by`, one build
      (was scripts/decline_all_optional.py)
  pay-chain-optional [--patch-only PATH]
      PAY every optional premise whose left disjunct is vacuous (item 227): the `chain` rows
      of the roster, witness `Or.inl ⟨[], by simp⟩` (was scripts/pay_chain_optional.py)
  narrow-conclusion MODULE NAME… [--all] [--deep] [--patch-only PATH]
      narrow each named declaration's conclusion `∨ True` to `∨ False` and price it by
      compiler errors (item 228); MODULE is FlowKeyLift | StreamAccum |
      PreprocessIndentStable; --all narrows every name at once (one build), --deep also
      narrows the `∨ True` motives in the proof body (was scripts/narrow_conclusion.py)

  --patch-only PATH   write the transformed module to PATH instead of building (the
                      source is not touched); narrow-conclusion needs --all or one name
  -C, --root ROOT     the checkout to work in (default: the cwd)
  -h, --help / -V, --version"

def streamAccumRel : String := "L4YAML/Proofs/Production/StreamAccum.lean"
def streamAccumMod : String := "L4YAML.Proofs.Production.StreamAccum"
def scratchRel : String := "L4YAML/Scratch"

def modules : List (String × String × String) := [
  ("FlowKeyLift", "L4YAML/Proofs/Production/FlowKeyLift.lean", "L4YAML.Proofs.Production.FlowKeyLift"),
  ("StreamAccum", streamAccumRel, streamAccumMod),
  ("PreprocessIndentStable", "L4YAML/Proofs/Scanner/PreprocessIndentStable.lean", "L4YAML.Proofs.Scanner.PreprocessIndentStable")]

def lake (root : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "lake", args, cwd := some root }

def splitLines (s : String) : Array String := (s.splitOn "\n").toArray
def joinLines (ls : Array String) : String := "\n".intercalate ls.toList

/-- The probe written under `L4YAML/Scratch/`, elaborated with `lake env lean`, removed
    (and the directory too, when this run created it and left it empty). -/
def roster (root : System.FilePath) (name src : String) : IO (Except String (Array Row)) := do
  let dir := root / scratchRel
  let existed ← dir.isDir
  IO.FS.createDirAll dir
  let probe := dir / name
  if ← probe.pathExists then
    return .error s!"{scratchRel}/{name} exists; refusing to overwrite it"
  IO.FS.writeFile probe src
  let out ← try
      let r ← lake root #["env", "lean", s!"{scratchRel}/{name}"]
      pure (r.stdout ++ r.stderr)
    finally
      try IO.FS.removeFile probe catch _ => pure ()
      unless existed do
        try
          if (← dir.readDir).isEmpty then IO.FS.removeDir dir
        catch _ => pure ()
  let rows := rowsOf out
  if rows.isEmpty then return .error s!"no roster rows; probe output was:\n{out}"
  return .ok rows

/-- The Lake-rendered Lean error lines of a build log, and the linter's unreferenced count. -/
def reading (log : String) : List String × Nat :=
  ((log.splitOn "\n").filter isErrorLine, countSub log "is not explicitly referenced")

/-- `shutil.copy(SRC, backup)` … `finally: shutil.copy(backup, SRC); backup.unlink()`, with
    the digests on stderr and a refusal when a backup from an interrupted run is present. -/
def withBackup (root : System.FilePath) (rel suffix : String)
    (body : ByteArray → IO UInt32) : IO UInt32 := do
  let path := root / rel
  let backup := System.FilePath.mk (path.toString ++ suffix)
  if ← backup.pathExists then
    IO.eprintln s!"{backup} exists: an earlier run was interrupted, so {rel} may be the transformed copy; inspect it, restore from the backup, delete the backup, then re-run"
    return 1
  let original ← IO.FS.readBinFile path
  let before := Scripts.Flip.Patch.digest original
  IO.eprintln s!"digest before  {rel}  {before}"
  IO.FS.writeBinFile backup original
  let code ← try body original
    catch e => IO.eprintln s!"{e}"; pure (1 : UInt32)
  IO.FS.writeBinFile path original
  let after := Scripts.Flip.Patch.digest (← IO.FS.readBinFile path)
  IO.eprintln s!"digest after   {rel}  {after}"
  if after != before then
    IO.eprintln s!"{rel} was not restored (backup kept at {backup}); fix the source before trusting anything else"
    return 1
  IO.FS.removeFile backup
  return code

def printSkipped (skipped : List (String × Nat)) : IO Unit := do
  for (why, k) in skipped.mergeSort (fun a b => a.1 ≤ b.1) do
    IO.println s!"  skipped {padLeft (toString k) 4}  {why}"

/-- items 226 / 227: the shadowing run. -/
def shadowRun (root : System.FilePath) (patchOnly : Option String) (probeName probeSrc : String)
    (header : Array Row → String) (keep : Row → Bool) (witness verb suffix errorsTitle : String) : IO UInt32 := do
  IO.println "building first (a probe reads oleans, not sources)..."
  if (← lake root #["build"]).exitCode != 0 then
    IO.eprintln "baseline build failed; refusing to measure"; return 1
  let rows ← match ← roster root probeName probeSrc with
    | .ok rows => pure rows
    | .error e => IO.eprintln e; return 1
  let path := root / streamAccumRel
  if let some out := patchOnly then
    let original ← IO.FS.readBinFile path
    let res := shadow (splitLines (String.fromUTF8! original)) rows witness keep
    IO.println (header rows)
    printSkipped res.skipped
    IO.println s!"  {verb} {res.shadowed}"
    IO.FS.writeFile out (joinLines res.lines)
    IO.eprintln s!"patch-only: transformed module written to {out}; {streamAccumRel} untouched"
    return 0
  withBackup root streamAccumRel suffix fun original => do
    let res := shadow (splitLines (String.fromUTF8! original)) rows witness keep
    IO.println (header rows)
    printSkipped res.skipped
    IO.println s!"  {verb} {res.shadowed}"
    IO.FS.writeFile path (joinLines res.lines)
    let r ← lake root #["build", streamAccumMod]
    let log := r.stdout ++ r.stderr
    let (errs, unref) := reading log
    let ok := r.exitCode == 0 && errs.isEmpty
    IO.println s!"build      {if ok then "OK" else "FAILED"}  errors={errs.length}"
    IO.println s!"linter     {unref} binders reported unreferenced"
    unless ok do
      IO.println errorsTitle
      for e in errs do IO.println e
    -- the Python restores, announces, and rebuilds in its `finally`
    IO.FS.writeBinFile path original
    IO.println "restored; rebuilding so no later probe reads this experiment..."
    discard <| lake root #["build"]
    return if ok then 0 else 1

def declineAllOptional (root : System.FilePath) (patchOnly : Option String) : IO UInt32 :=
  shadowRun root patchOnly "OptionalRoster.lean" Probes.optionalRoster
    (fun rows => s!"roster {rows.size} optional binders") (fun _ => true)
    "Or.inr trivial" "SHADOWED" ".item226-backup" "--- first errors ---"

def isChain (r : Row) : Bool := r.size ≥ 5 && r[4]! == "chain"

def payChainOptional (root : System.FilePath) (patchOnly : Option String) : IO UInt32 :=
  shadowRun root patchOnly "ChainRoster.lean" Probes.chainRoster
    (fun rows => s!"roster {rows.size} optional binders, {(rows.filter isChain).size} with a vacuous LEFT disjunct")
    isChain "Or.inl ⟨[], by simp⟩" "PAID" ".item227-backup" "--- errors ---"

/-- item 228. -/
def narrowConclusion (root : System.FilePath) (patchOnly : Option String) (args : List String) : IO UInt32 := do
  let all := args.contains "--all"
  let deep := args.contains "--deep"
  let positional := args.filter fun a => a != "--all" && a != "--deep"
  let modName :: names := positional
    | IO.eprintln "usage: lake run restate -- narrow-conclusion MODULE NAME… [--all] [--deep]"; return 2
  let some (_, rel, modl) := modules.find? (·.1 == modName)
    | IO.eprintln s!"narrow-conclusion: argument module: invalid choice: '{modName}' (choose from {", ".intercalate (modules.map (·.1))})"; return 2
  if names.isEmpty then
    IO.eprintln "usage: lake run restate -- narrow-conclusion MODULE NAME… [--all] [--deep]"; return 2
  let groups := if all then [names] else names.map ([·])
  let path := root / rel
  let runGroup (src : Array String) (g : List String) : IO (Option (Array String × String)) := do
    let (lines, done, skipped, extra) ←
      if deep then
        let (lines, hits, skipped) := Narrow.narrowDeep src g
        pure (lines, (hits.filter (·.2 > 0)).map (·.1), skipped, " ".intercalate (hits.map fun (k, v) => s!"{k}:{v}"))
      else
        let (lines, done, skipped) := Narrow.narrow src g
        pure (lines, done, skipped, "")
    for (nm, why) in skipped do IO.println s!"  SKIP  {padRight nm 44} {why}"
    if done.isEmpty then return none
    let tag := if done.length > 1 then ",".intercalate done else done.head!
    return some (lines, s!"  PRICE {padRight tag 44} errors=ERRS  {extra}")
  if let some out := patchOnly then
    if groups.length != 1 then
      IO.eprintln "narrow-conclusion --patch-only: one group only (use --all or a single NAME)"; return 2
    let src := splitLines (String.fromUTF8! (← IO.FS.readBinFile path))
    match ← runGroup src groups.head! with
    | none => IO.eprintln "patch-only: nothing narrowed"; return 1
    | some (lines, _) =>
      IO.FS.writeFile out (joinLines lines)
      IO.eprintln s!"patch-only: transformed module written to {out}; {rel} untouched"
      return 0
  if (← lake root #["build", modl]).exitCode != 0 then
    IO.eprintln "baseline build failed; refusing to measure"; return 1
  withBackup root rel ".item228-backup" fun original => do
    let src := splitLines (String.fromUTF8! original)
    for g in groups do
      IO.FS.writeBinFile path original
      let some (lines, priceLine) ← runGroup src g | continue
      IO.FS.writeFile path (joinLines lines)
      let r ← lake root #["build", modl]
      let (errs, _) := reading (r.stdout ++ r.stderr)
      IO.println (priceLine.replace "errors=ERRS" s!"errors={errs.length}")
      for e in errs do IO.println s!"          {String.ofList ((strip e).toList.take 160)}"
    IO.FS.writeBinFile path original
    discard <| lake root #["build", modl]
    return 0

def cli (args : List String) : IO UInt32 := do
  let mut root : System.FilePath := "."
  let mut patchOnly : Option String := none
  let mut rest : Array String := #[]
  let mut it := args
  while true do
    match it with
    | [] => break
    | "-h" :: _ | "--help" :: _ => IO.println usage; return 0
    | "-V" :: _ | "--version" :: _ => IO.println version; return 0
    | "-C" :: r :: more | "--root" :: r :: more => root := r; it := more
    | "--patch-only" :: p :: more => patchOnly := some p; it := more
    | a :: more => rest := rest.push a; it := more
  match rest.toList with
  | ["decline-all-optional"] => declineAllOptional root patchOnly
  | ["pay-chain-optional"] => payChainOptional root patchOnly
  | "narrow-conclusion" :: as => narrowConclusion root patchOnly as
  | c :: _ => IO.eprintln s!"scripts-restate: unknown command or arguments '{c}'\n{usage}"; return 2
  | [] => IO.eprintln usage; return 2

end Scripts.Restate.Main

public def main (args : List String) : IO UInt32 := Scripts.Restate.Main.cli args
