module

public import Lean.Elab.Import
public import Lean.Elab.Frontend
public import Scripts.Path.CapstonePath
public import Scripts.Pack.Residue

@[expose] public section Blanket

/-!
# `lake run capstone-path [-- -C ROOT] [--check]` — the `∨ True` positions ON / OFF the capstone's path

DOCS item 439 ((ω-path)).  Loads the built environment of `DocumentProduction` (the capstones
that import `StreamAccum`), reads the `∨ True` audit's pinned tables off
`Tests/Guards/Proofs/OrTrueAudit.lean`, classes every position with
`Scripts.Path.CapstonePath.classify` and prints the summary, the ON roster by family and the
OFF residue by class.  `--check` compares the summary with the guard's pin
(`Tests/Guards/Proofs/CapstonePathAudit.lean`, `expectedSummary`) and exits 1 when it moved.
-/

open Lean
open Scripts.Path.CapstonePath
open Scripts.Pack.Residue (leanList)

namespace Scripts.Main.CapstonePath

def auditFile := "Tests/Guards/Proofs/OrTrueAudit.lean"
def guardFile := "Tests/Guards/Proofs/CapstonePathAudit.lean"

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg; return code

/-- The literal of `def NAME : String :=` on the line after the head. -/
def pinString? (text name : String) : Option String := do
  let after ← (text.splitOn s!"def {name} : String :=")[1]?
  let t := after.trimAscii.toString
  let '"' :: body := t.toList | none
  some (String.ofList (body.takeWhile (· != '"')))

unsafe def run (args : List String) : IO UInt32 := do
  let args := if args.headD "" == "--" then args.drop 1 else args
  let root := match args.dropWhile (· != "-C") with
    | _ :: r :: _ => r
    | _ => "."
  let check := args.contains "--check"
  let probe := args.contains "--probe"
  let root ← IO.FS.realPath root
  let audit ← IO.FS.readFile (root / auditFile)
  let some positions := leanList audit "expectedPositions" | return ← die s!"{auditFile}: expectedPositions not found"
  let some supply := leanList audit "expectedSupply" | return ← die s!"{auditFile}: expectedSupply not found"
  let some consumers := leanList audit "expectedConsumers" | return ← die s!"{auditFile}: expectedConsumers not found"
  enableInitializersExecution
  let r ← IO.Process.output { cmd := "lean", args := #["--print-prefix"], cwd := some root }
  if r.exitCode != 0 then return ← die s!"lean --print-prefix failed in {root}: {r.stderr}"
  initSearchPath (System.FilePath.mk r.stdout.trimAscii.toString) [root / ".lake" / "build" / "lib" / "lean"]
  let text := "import L4YAML.Proofs.Production.DocumentProduction\n"
  let ictx := Parser.mkInputContext text "<capstone-path>"
  let (hdr, _, msgs) ← Parser.parseHeader ictx
  let (env, msgs) ← Elab.processHeader hdr {} msgs ictx
  if msgs.hasErrors then
    for m in msgs.toList do IO.eprint (← m.toString)
    return ← die "the capstones did not load (build L4YAML.Proofs.Production.DocumentProduction first)"
  let reached := reach env roots
  let shown := shownSet reached
  let consumed := (roots.foldl (fun acc n => acc ++ (rawRefs env n).toList) [])
    |>.filter (fun n => (`L4YAML.Proofs.StreamAccum).isPrefixOf n) |>.eraseDups
    |>.map (fun n => (privateToUserName n).toString.drop "L4YAML.Proofs.StreamAccum.".length |>.toString)
  let keys : Std.HashSet String := positions.foldl (fun acc l => match parsePos l with
    | some p => acc.insert s!"{p.decl}{p.site}" | none => acc) {}
  let drop : Std.HashSet Name := Std.HashSet.ofList (dropSet.filter env.contains)
  let decls := reached.toArray.filter fun n => saNs.isPrefixOf n || (`L4YAML.Proofs.PreprocessIndentStable).isPrefixOf n
  let trace := args.contains "--trace"
  if trace then IO.eprintln s!"trace: imported; reached={reached.size}; walking {decls.size} decls"
  let w ← if trace then do
      let rets := retsOf decls keys
      let mut w : Walk := {}
      for n in decls do
        let t0 ← IO.monoMsNow
        if (args.contains "--only") && !(args.contains (shownName n)) then continue
        IO.eprintln s!"trace: > {shownName n}"; (← IO.getStderr).flush
        let dbgName := match args.dropWhile (· != "--dump") with | _ :: d :: _ => some d.toName | _ => none
        w := walkDecl env drop keys rets { w with budget := 5000000, dbgName := dbgName } n
        let dt := (← IO.monoMsNow) - t0
        if dt > 200 || true then IO.eprintln s!"trace: {shownName n} {dt}ms steps={w.steps} level={w.levelSteps} refs={w.refSteps} arms={w.arms.size} relays={w.relays.size}"
      pure w
    else pure (walkAll env drop keys decls)
  let cs := classify shown positions.toList supply.toList consumers.toList w.arms w.relays
  let (saR, saT) := moduleReach env reached `L4YAML.Proofs.StreamAccum
  let summ := summary cs consumed saR saT w.unrooted.size ++ s!" arms={w.arms.size} relays={w.relays.size} drop-set={drop.size}/{dropSet.length}"
  IO.println s!"CAPSTONE-PATH {summ}"
  IO.println s!"reached constants: {reached.size}"
  IO.println "ON by family:"
  for f in families cs do IO.println s!"  {f}"
  if probe then
    let mut touched := 0
    let mut w' := w
    for n in decls do
      let (b, w'') := (touchesDrop env drop n).run w'
      w' := w''
      if b then touched := touched + 1
    IO.println s!"probe: walked={decls.size} closure-touches-drop={touched} arms by class: drop={(w.arms.filter (·.cls == "drop")).size} via={(w.arms.filter (·.cls == "via")).size} relay={(w.arms.filter (·.cls == "relay")).size} honest={(w.arms.filter (·.cls == "honest")).size}"
    for ctor in [`L4YAML.Proofs.StreamAccum.PendingNode.pendingContent, `L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock] do
      match ctorFields env ctor with
      | some (np, fs) => IO.println s!"probe: ctor {ctor} params={np} fields={fs.map (·.1)}"
      | none => IO.println s!"probe: ctor {ctor} not a constructor"
    IO.println s!"probe: keys sample: {(keys.toList.filter (·.startsWith "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent")).take 6}"
    IO.println s!"probe: labelled minors={w.labelled} matchers inlined={w.matchersInlined} opaque={w.matchersOpaque} labelled={w.matchersLabelled}"
    let cs := w.casings.toArray.qsort (fun a b => a.2 > b.2)
    for (n, k) in cs.extract 0 25 do IO.println s!"probe: casing {n} ×{k}"
    IO.println s!"probe: unrooted Or-casings={w.unrooted.size}"
    for l in w.unrooted do IO.println s!"  {l}"
    IO.println "probe: arms"
    for a in w.arms do IO.println s!"  {shownName a.consumer} ← {a.root} {a.cls} {a.witness}"
    IO.println "probe: relays"
    for r in w.relays do IO.println s!"  {shownName r.consumer}: {r.src} → {r.dst}"
  for l in w.dbg do IO.println s!"dbg: {l}"
  IO.println "OFF residue:"
  for c in cs.filter (·.cls.startsWith "off-") do IO.println s!"  {c.line}"
  if check then
    let guard ← IO.FS.readFile (root / guardFile)
    match pinString? guard "expectedSummary" with
    | none => return ← die s!"{guardFile}: expectedSummary not found"
    | some pin =>
      if pin != summ then
        return ← die s!"capstone-path: the summary moved\nexpected: {pin}\ngot:      {summ}"
      IO.println "OK: capstone-path summary agrees with the guard's pin"
  return 0

end Scripts.Main.CapstonePath

public unsafe def main (args : List String) : IO UInt32 := Scripts.Main.CapstonePath.run args
