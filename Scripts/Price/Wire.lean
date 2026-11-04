module

public import Scripts.Price.Pin
meta import Scripts.Price.Pin

/-! # Scripts.Price.Wire — `wire_price.py` (item 268): the WIRING of the carrier, by producers -/

namespace Scripts.Price.Wire

open Scripts.Price.Pin
open Scripts.Price.Attribute (rstrip)
open Scripts.Punt.Price (padLeft padRight)

public section

def gateofHead : String := "def GateOf : Option ScannerState → Prop"
def gateofNone : String := "  | none => True"
def gateofSome : String := "  | some sc0 => danglingNodePos? sc0 = none ∧ sc0.simpleKeyAllowed = false"
def gateofHead2 : String := "def GateOf : Option ScannerState → Nat → Prop"
def gateofNone2 : String := "  | none, _ => True"
def gateofSome2 : String := "  | some sc0, _ => danglingNodePos? sc0 = none ∧ sc0.simpleKeyAllowed = false"
def anchorArm : String := "  | some sc0, s, d => ParkChoice sc0 s d ∧ ParkFloor sc0 s d"
def anchorArm2 : String := "  | some sc0, s, d => ParkChoice sc0 s d ∧ ParkFloor sc0 s d ∧ ParkSlot sc0 s d"
def routeField : String := "  value : GateOf g → ∀ sp_ne sp_mid, SFlowContent n .flowOut sp_br sp_ne →"
def routeField2 : String := "  value : GateOf g → 0 = 0 → ∀ sp_ne sp_mid, SFlowContent n .flowOut sp_br sp_ne →"
def eofHead : String := "lemma scanNextToken_none_stream (sc : ScannerState)"
def hyp : String := "    (h_wire268 : True → sc.indents = sc.indents ∧ 0 = 0)"
def probes : List String := ["gate", "anchor", "route", "eof"]
def usage : String := "usage: wire_price.py [" ++ "|".intercalate probes ++ "|all] [--wide]"

def applyProbe (lines : Array String) (which : String) : Except String (Array String) := do
  if which == "gate" then
    let i ← indexOf lines gateofHead
    if !(i + 2 < lines.size && rstrip lines[i + 1]! == gateofNone && rstrip lines[i + 2]! == gateofSome) then
      throw s!"AssertionError: `GateOf`'s arms are not {repr gateofNone} / {repr gateofSome} under its head (line {i + 1})"
    return (lines.set! i gateofHead2).set! (i + 1) gateofNone2 |>.set! (i + 2) gateofSome2
  else if which == "anchor" then return lines.set! (← indexOf lines anchorArm) anchorArm2
  else if which == "route" then return lines.set! (← indexOf lines routeField) routeField2
  else if which == "eof" then return insertAfter lines (← indexOf lines eofHead) hyp
  else throw s!"AssertionError: {which}"

def reading (which : String) (owner : Nat → String) (out : String) :
    Except String (Array Nat × Array (String × Array Nat) × Array String) := do
  let (raw, away) := splitErrors out
  if raw.isEmpty && away.isEmpty then throw s!"{which}: the probe broke nothing -- it did not apply"
  return (raw, byDeclLines owner raw, away)

def verboseLines (which : String) (raw : Array Nat) (decls : Array (String × Array Nat)) (away : Array String) : Array String :=
  #[s!"probe {which}: {raw.size} error sites in {decls.size} declarations", ""] ++ declRows decls ++
    (if away.isEmpty then #[] else #["", s!"  files outside the module: {", ".intercalate away.toList}"])

def allRow (p : String) (n d : Nat) (names : Array String) (away : Array String) : String :=
  s!"{padRight p 7} errors={padLeft (toString n) 3}  declarations={padLeft (toString d) 2}  {", ".intercalate names.toList}" ++
    (if away.isEmpty then "" else s!"   | outside: {away.size} files")

def names (decls : Array (String × Array Nat)) : Array String := (decls.map (·.1)).qsort (· < ·)

private def sample : Array String := #["  | none => True", gateofHead, gateofNone, gateofSome, "x", eofHead, "    (h : True) :"]
#guard (applyProbe sample "gate").toOption == some #["  | none => True", gateofHead2, gateofNone2, gateofSome2, "x", eofHead, "    (h : True) :"]
#guard (applyProbe #[gateofHead, "  | other", gateofSome] "gate").toOption == none
#guard (applyProbe sample "eof").toOption == some #["  | none => True", gateofHead, gateofNone, gateofSome, "x", eofHead, hyp, "    (h : True) :"]
#guard (applyProbe sample "anchor").toOption == none
#guard verboseLines "eof" #[6] #[("scanNextToken_none_stream", #[6])] #["Tests/A.lean"] ==
  #["probe eof: 1 error sites in 1 declarations", "", "    1  scanNextToken_none_stream", "", "  files outside the module: Tests/A.lean"]
#guard allRow "eof" 1 1 #["a"] #["T", "U"] == "eof     errors=  1  declarations= 1  a   | outside: 2 files"

end

end Scripts.Price.Wire
