module

public import Scripts.Price.Attribute
meta import Scripts.Price.Attribute

/-!
# Scripts.Price.ParkTop — `park_top_price.py` (item 205): the park-TOP carrier by rings

`ring1` adds `h_park_top : sc.currentIndent ≤ (n : Int)` to `pendingBlock` (item 204's
number); `all` asks it of every block-context park at once (the transitive closure's
floor); one park's name asks how many sites BUILD that constructor (item 208).
-/

namespace Scripts.Price.ParkTop

open Scripts.Price.Attribute

public section

/-- Constructor ↦ the park-position variable its signature binds; `pendingDirective` is
    excluded (the flow-context park reaches no block dispatch). -/
def parks : List (String × String) :=
  [("noPending", "sp"), ("pendingContent", "sp_scan"), ("pendingProps", "sp_scan"),
   ("pendingDocEnd", "sp_scan"), ("pendingDocStart", "sp_scan"), ("pendingFlow", "sp_scan"),
   ("pendingBlockContent", "sp_scan"), ("pendingMapValue", "sp_scan")]

def probeLine : String := "  -- PARK-TOP PROBE (scripts/park_top_price.py)"

def modes : List String := ["ring1", "all"] ++ parks.map (·.1) ++ ["pendingBlock"]

def usageModes : String := "ring1|all|" ++ "|".intercalate (sortedStrs (parks.map (·.1) ++ ["pendingBlock"]).toArray).toList

/-- `apply_probe(lines, which)` → the patched lines and `sorted(targets)`. -/
def applyProbe (lines : Array String) (which : String) : Except String (Array String × Array String) := do
  let spans := constructorSpans lines
  let targets : List (String × String) :=
    if which == "ring1" then [("pendingBlock", "n")]
    else if which == "all" then parks ++ [("pendingBlock", "n")]
    else [(which, if which == "pendingBlock" then "n" else (parks.lookup which).getD "n")]
  let mut withSpan : Array ((String × String) × Nat) := #[]
  for t in targets do
    match spans.find? (·.1 == t.1) with
    | some (_, s) => withSpan := withSpan.push (t, s)
    | none => throw s!"KeyError: {t.1}"
  let mut out := lines
  for ((name, var), concl) in stableSort withSpan (fun a b => b.2 < a.2) do
    let _ := name
    let bound := if var == "n" then "(n : Int)" else s!"({var}.col : Int)"
    out ← spliceSig out (concl - 1) probeLine s!"      (h_park_top : sc.currentIndent ≤ {bound}) :"
  return (out, sortedStrs (targets.map (·.1)).toArray)

/-- The constructor-application anchors: the first probed name on each line that is not
    preceded by `--`. -/
def anchors (patched : Array String) (names : Array String) : Array Anchor := Id.run do
  let mut out : Array Anchor := #[]
  for i in [0:patched.size] do
    let line := patched[i]!
    if let some n := names.find? (fun n => uncommentedBefore line s!"PendingNode.{n}") then
      out := out.push (i + 1, n)
  return out

def report (patched : Array String) (names : Array String) (log : String) : Array String := Id.run do
  let census := errorLines log
  let (groups, unanchored) := anchorErrors (anchors patched names) (sortedNat census)
  let decls := byDecl patched groups unanchored
  let mut out : Array String := #["", s!"raw error sites: {census.size}",
    s!"applications:    {groups.size + unanchored.size}   <- the producer census",
    s!"declarations:    {decls.size}", ""]
  out := out ++ declLines decls
  let casc := cascades groups
  if !casc.isEmpty then
    out := out.push "" |>.push s!"collapsed cascades ({cascadeCount groups} errors were not producers):"
    for ((aline, name), hits) in casc do
      out := out.push s!"  L{aline}  PendingNode.{name}  <- errors at {joinNats hits}"
  if !unanchored.isEmpty then
    out := out.push "" |>.push s!"UNANCHORED ({unanchored.size}): no constructor literal precedes these, so they are counted one-for-one and the total is a CEILING:"
    for raw in unanchored do out := out.push s!"  L{raw}  in {enclosingDecl patched raw}"
  if census.isEmpty then out := out.push "  (none -- the carrier is already discharged everywhere)"
  return out

private def sample : Array String := #[
  "inductive PendingNode : Prop where",
  "  | noPending (sp_start : SurfPos)",
  "      (h : True) :",
  "      PendingNode sc []",
  "  | pendingBlock (sp_start : SurfPos) (n : Nat)",
  "      (h : True) :",
  "      PendingNode sc [n]",
  "lemma a : True := by",
  "  exact PendingNode.pendingBlock x 0 (by trivial)",
  "lemma b : True := by",
  "  exact (PendingNode.noPending x (by trivial))"]

#guard (applyProbe sample "ring1").toOption.map (·.2) == some #["pendingBlock"]
#guard (applyProbe sample "ring1").toOption.map (·.1.size) == some 13
#guard (applyProbe sample "ring1").toOption.map (fun p => p.1[5]!) == some "      (h : True)"
#guard (applyProbe sample "ring1").toOption.map (fun p => p.1[7]!) == some "      (h_park_top : sc.currentIndent ≤ (n : Int)) :"
#guard (applyProbe sample "noPending").toOption.map (fun p => p.1[4]!) == some "      (h_park_top : sc.currentIndent ≤ (sp.col : Int)) :"
#guard (applyProbe sample "pendingFlow").toOption == none
#guard anchors sample #["noPending", "pendingBlock"] == #[(9, "pendingBlock"), (11, "noPending")]
#guard report sample #["pendingBlock"] "L4YAML/Proofs/Production/StreamAccum.lean:9:10: error: x\nL4YAML/Proofs/Production/StreamAccum.lean:9:30: error: y\nL4YAML/Proofs/Production/StreamAccum.lean:2:1: error: z\n" ==
  #["", "raw error sites: 2", "applications:    2   <- the producer census", "declarations:    2", "",
    "    1  <file scope>", "    1  a", "",
    "UNANCHORED (1): no constructor literal precedes these, so they are counted one-for-one and the total is a CEILING:",
    "  L2  in <file scope>"]
#guard report sample #["pendingBlock"] "" == #["", "raw error sites: 0", "applications:    0   <- the producer census", "declarations:    0", "", "  (none -- the carrier is already discharged everywhere)"]

end

end Scripts.Price.ParkTop
