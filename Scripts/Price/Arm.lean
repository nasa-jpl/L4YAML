module

public import Scripts.Price.Pin
meta import Scripts.Price.Pin
public import Scripts.Lean.Md5
meta import Scripts.Lean.Md5

/-! # Scripts.Price.Arm — `arm_price.py` (item 270): what each `drop_ride` arm HOLDS, premise by premise -/

namespace Scripts.Price.Arm

open Scripts.Price.Pin
open Scripts.Price.Attribute (strip lstrip)
open Scripts.Punt.Price (padRight take)

public section

def spend : String := "exact slot_ride"
def arms : List String := ["pendingProps", "pendingBlock", "pendingMapValue"]
/-- `(name, type, tactic)`; `none` = `assumption`. -/
def premises : List (String × String × Option String) :=
  [("hok", "scanNextToken_preprocess sc = .ok (some (s_prep, c))", none),
   ("base", "IndentStackBase.SentinelBase sc", none),
   ("le", "(s_prep.col : Int) ≤ sc.currentIndent", none),
   ("floor", "s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1", none),
   ("noflow_prep", "s_prep.inFlow = false", none),
   ("park_col_ne0", "sp_scan.col ≠ 0", none),
   ("gate_gp", "True", some "exact (fun _ => trivial) gp"),
   ("sibling_floor_prep", "True", some "exact (fun _ => trivial) h_floor_prep")]

/-- `spend_lines`: the 0-based index of each `exact slot_ride` / `· exact slot_ride`. -/
def spendLines (lines : Array String) : Array Nat :=
  (Array.range lines.size).filter fun i =>
    let s := strip lines[i]!
    s.startsWith spend || s.startsWith ("· " ++ spend)

/-- `with_probe(line, ty, tac)`: the `have` sharing the spend's tactic block. -/
def withProbe (line ty : String) (tac : Option String) (name : String := "_probe270") : Array String :=
  let indent := take line (line.length - (lstrip line).length)
  let have_ := s!"have {name} : {ty} := by {tac.getD "assumption"}"
  let s := strip line
  if s.startsWith "· " then #[s!"{indent}· {have_}", s!"{indent}  {Scripts.Punt.Price.drop s 2}"]
  else #[s!"{indent}{have_}", line]

def patched (pristine : Array String) (li : Nat) (ty : String) (tac : Option String) : Array String :=
  Scripts.Price.Attribute.replaceLine pristine li (withProbe pristine[li]! ty tac)

def rowLine (paid : Bool) (arm name : String) : String :=
  s!"{if paid then "PAID" else "OWED"}  {padRight arm 16} {name}"

/-- The first output line naming the probe or `assumption`, as the Python prints it. -/
def firstDiag (out : String) : Option String :=
  ((out.splitOn "\n").find? fun l => (l.splitOn "_probe270").length > 1 || (l.splitOn "assumption").length > 1).map
    fun l => s!"      {take (strip l) 140}"

def md5Line (name before after : String) : String :=
  s!"md5 {name}  before {before}  after {after}  {if before == after then "==" else "!! DIFFERS"}"

/-- `ARMTABLE cells=… paid=… owed=… <premise>=P/O per arm`. -/
def tableLine (rows : Array (String × String × Bool)) : String := Id.run do
  let paid := (rows.filter (·.2.2)).size
  let mut got := s!"cells={rows.size} paid={paid} owed={rows.size - paid}"
  for (name, _, _) in premises do
    let per := String.join ((rows.filter (·.2.1 == name)).toList.map fun (_, _, p) => if p then "P" else "O")
    got := got ++ s!" {name}={per}"
  return "ARMTABLE " ++ got

#guard spendLines #["  exact slot_ride", "  · exact slot_ride", "  exact slot_ride2", "  x"] == #[0, 1, 2]
#guard withProbe "    exact slot_ride" "T" none == #["    have _probe270 : T := by assumption", "    exact slot_ride"]
#guard withProbe "    · exact slot_ride" "T" (some "exact gp") == #["    · have _probe270 : T := by exact gp", "      exact slot_ride"]
#guard rowLine true "pendingProps" "hok" == "PAID  pendingProps     hok"
#guard firstDiag "a\nx: error: unsolved goals _probe270 here\n" == some "      x: error: unsolved goals _probe270 here"
#guard tableLine #[("a", "hok", true), ("b", "hok", false), ("a", "le", false)] == "ARMTABLE cells=3 paid=1 owed=2 hok=PO base= le=O floor= noflow_prep= park_col_ne0= gate_gp= sibling_floor_prep="
#guard md5Line "S.lean" "x" "x" == "md5 S.lean  before x  after x  =="

end

end Scripts.Price.Arm
