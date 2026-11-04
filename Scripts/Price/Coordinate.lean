module

public import Scripts.Price.Arm
meta import Scripts.Price.Arm

/-! # Scripts.Price.Coordinate — `coordinate_price.py` (item 271): the bridge, the arms' identity, the arity flip -/

namespace Scripts.Price.Coordinate

open Scripts.Price.Pin
open Scripts.Price.Attribute (stableSort)
open Scripts.Punt.Price (padLeft padRight)

public section

def arms : List String := Scripts.Price.Arm.arms
def ident (arm : String) : String :=
  if arm == "pendingProps" then "h_col0_p" else if arm == "pendingBlock" then "h_col59" else "h_col0_mv"
def floorH (arm : String) : String :=
  if arm == "pendingProps" then "h_floor_p" else if arm == "pendingBlock" then "h_floor_old" else "h_floor_mv"
def colTerm (arm : String) : String :=
  if arm == "pendingProps" then "Nat.ne_of_gt h_col0_p"
  else if arm == "pendingBlock" then "h_col59 ▸ Nat.succ_ne_zero n_old" else "Nat.ne_of_gt h_col0_mv"
def leTy : String := "(s_prep.col : Int) ≤ sc.currentIndent"
def colTy : String := "sp_scan.col ≠ 0"
def floorTy : String := "s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1"

/-- `bridge_rows(arm)`: `(name, type, named derivation)`. -/
def bridgeRows (arm : String) : List (String × String × Option String) :=
  [("le", leTy, some s!"exact underRunEnd_col_le_currentIndent {floorH arm} h_col02 hj h_ind h_end hcorr_prep"),
   ("park_col_ne0", colTy, some s!"exact {colTerm arm}"),
   ("floor", floorTy, some s!"exact h_landed_ur ({colTerm arm}) h_noflow_prep")]

def probeName : String := "_probe271"
def identTac (owner : String) : String := s!"exact (fun _ => trivial) {ident owner}"

def patched (pristine : Array String) (li : Nat) (ty tac : String) : Array String :=
  Scripts.Price.Attribute.replaceLine pristine li (Scripts.Price.Arm.withProbe pristine[li]! ty (some tac) probeName)

def bridgeLine (verdict arm name : String) : String := s!"  {verdict}  {padRight arm 16} {name}"
def identLine (ok : Bool) (arm owner : String) : String :=
  s!"  {if ok then "yes" else "no "} site={padRight arm 16} binder={ident owner} ({owner})"

def concl : String := "        ∃ sp_mid, SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧"
def ret : String := "          Or.inr ⟨sp_mid, h_ssl_col.1, h_ssl_col.2.1, h_ur, h_ltsl,"
def armPat : String := "      ⟨sp_mid2, _h_ssl2, h_col02, h_ur, h_ltsl2, h_landed_ur, h_ska_ur⟩"
def floorHead : String := "lemma preprocess_some_separate_at_floor (n : Nat) (sc : ScannerState)"
def dummyConcl : String := "        ∃ sp_mid, SSLComments sp sp_mid ∧ 0 = 0 ∧ sp_mid.col = 0 ∧"
def dummyRet : String := "          Or.inr ⟨sp_mid, h_ssl_col.1, rfl, h_ssl_col.2.1, h_ur, h_ltsl,"
def armPatRepaired : String := "      ⟨sp_mid2, _h_ssl2, _, h_col02, h_ur, h_ltsl2, h_landed_ur, h_ska_ur⟩"

def allOf (lines : Array String) (needle : String) : Array Nat :=
  (Array.range lines.size).filter fun i => lines[i]! == needle

/-- `_floor_half`: the occurrence of `needle` that sits after `preprocess_some_separate_at_floor`'s head. -/
def floorHalf (lines : Array String) (needle : String) (expect : Nat := 1) : Except String Nat := do
  let hits := allOf lines needle
  if hits.size != expect then throw s!"AssertionError: expected {expect} of {repr needle}, got {hits.size}"
  let heads := (Array.range lines.size).filter fun i => lines[i]!.startsWith floorHead
  if heads.size != 1 then throw s!"AssertionError: expected one {repr floorHead}, got {heads.size}"
  let after := hits.filter (· > heads[0]!)
  if after.size != 1 then throw s!"AssertionError: {repr needle}: {after.size} hits after the head"
  return after[0]!

def patchSplit (lines : Array String) (repair : Bool := false) : Except String (Array String) := do
  let mut out := lines
  out := out.set! (← floorHalf out concl 2) dummyConcl
  out := out.set! (← floorHalf out ret) dummyRet
  if repair then
    let pats := allOf out armPat
    if pats.size != 3 then throw s!"AssertionError: expected 3 arm patterns, got {pats.size}"
    for i in pats do out := out.set! i armPatRepaired
  return out

/-- `run_split`'s reading: `(by_decl rows, count, sorted names)`. -/
def splitReading (patched : Array String) (out : String) : Except String (Array String × Nat × Array String) := do
  let raw := (Scripts.Price.Attribute.errorLines out).qsort (· < ·)
  if raw.isEmpty then throw "split: the flip broke nothing -- it did not apply"
  let decls := byDeclLines patched raw
  return (declRows decls, decls.size, (decls.map (·.1)).qsort (· < ·))

/-- `run_wide`'s reading over a `lake build` log: rows, failed modules, `(count, sorted files)`. -/
def wideReading (exitCode : UInt32) (out : String) : Except String (Array String × Nat × Array String) := do
  let mut hits : Array (String × Array Nat) := #[]
  let mut unrepaired := 0
  for l in out.splitOn "\n" do
    if let some (p, n) := errLoc? l then
      if p.endsWith self then unrepaired := unrepaired + 1
      else hits := Scripts.Price.Attribute.addTo hits p n
  if unrepaired > 0 then
    throw s!"wide: the repair did not take -- the module still fails ({unrepaired} sites), so nothing downstream was built"
  if exitCode == 0 then
    throw "wide: the tree BUILT under the flip -- so either the probe did not apply or no consumer was reached.  A green build here is not a census of zero."
  if hits.isEmpty then
    throw "wide: the build failed and no location parsed -- the diagnostic pattern does not match this driver's output, so the census is absent rather than zero."
  let sorted := hits.qsort (·.1 < ·.1)
  let rows := sorted.map fun (f, ls) => s!"  {padLeft (toString ls.size) 3}  {f}"
  let failed := (out.splitOn "\n").filterMap fun l =>
    if (Scripts.Price.Attribute.lstrip l).startsWith "✖" then
      let parts := l.splitOn "Building "
      if parts.length > 1 then some s!"       failed module: {String.ofList (((parts.drop 1).head!).toList.takeWhile (· != ' '))}" else none
    else none
  return (rows ++ failed, sorted.size, sorted.map (·.1))

def gotLine (grid : Array (String × String × Bool)) (cells : Array (String × String × String)) (lib : Nat) : String := Id.run do
  let bad := arms.flatMap fun a => arms.filterMap fun o =>
    match grid.find? fun (x, y, _) => x == a && y == o with
    | some (_, _, ok) => if ok != (a == o) then some s!"{a}/{o}" else none
    | none => none
  let identS := if bad.isEmpty then "diagonal" else "BROKEN:" ++ ",".intercalate bad
  let mut s := s!"arms={",".intercalate arms} ident={identS}"
  for (n, _, _) in bridgeRows arms.head! do
    let per := String.join (arms.map fun a => ((cells.find? fun (x, y, _) => x == a && y == n).map (·.2.2)).getD "")
    s := s ++ s!" {n}={per}"
  return s ++ s!" lib={lib}"

#guard bridgeLine "P" "pendingProps" "le" == "  P  pendingProps     le"
#guard identLine false "pendingBlock" "pendingProps" == "  no  site=pendingBlock     binder=h_col0_p (pendingProps)"
#guard (patchSplit #[concl, floorHead, "x", concl, ret]).toOption == some #[concl, floorHead, "x", dummyConcl, dummyRet]
#guard (patchSplit #[floorHead, concl, ret]).toOption == none
#guard (wideReading 0 "").toOption == none
#guard (wideReading 1 "error: Tests/A.lean:3:1: x\nerror: Tests/A.lean:9:1: y\n✖ [2/3] Building Tests.A\n").toOption ==
  some (#["    2  Tests/A.lean", "       failed module: Tests.A"], 1, #["Tests/A.lean"])
#guard (wideReading 1 "error: L4YAML/Proofs/Production/StreamAccum.lean:3:1: x\n").toOption == none
#guard gotLine (arms.toArray.flatMap fun a => arms.toArray.map fun o => (a, o, a == o))
  #[("pendingProps", "le", "P"), ("pendingBlock", "le", "O"), ("pendingMapValue", "le", "B")] 4 ==
  "arms=pendingProps,pendingBlock,pendingMapValue ident=diagonal le=POB park_col_ne0= floor= lib=4"

end

end Scripts.Price.Coordinate
