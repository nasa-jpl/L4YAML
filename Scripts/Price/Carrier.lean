module

public import Scripts.Price.Pin
meta import Scripts.Price.Pin

/-! # Scripts.Price.Carrier — `carrier_price.py` (items 266/267): the BUILT carrier by producers -/

namespace Scripts.Price.Carrier

open Scripts.Price.Pin
open Scripts.Punt.Price (padLeft padRight)

public section

def coreStruct : String := "structure ParkCore (sc0 s : ScannerState) (d : Nat) : Prop where"
def slotStruct : String := "structure ParkSlot (sc0 s : ScannerState) (d : Nat) : Prop extends ParkCore sc0 s d where"
def field : String := "  probe267 : sc0.indents.size = sc0.indents.size"
def propField : String := "  parkProp : ∃ k, prevRealIdx? sc0.tokens sc0.tokens.size = some k ∧"
def propRenamed : String := "  parkProp267 : ∃ k, prevRealIdx? sc0.tokens sc0.tokens.size = some k ∧"
def consumer : String := "lemma accum_flow_open_depth0 (sc : ScannerState)"
def gate : String := "lemma propsPark_open_gate {sc s_prep s' : ScannerState} {sp_scan : SurfPos} {c : Char}"
def hyp : String := "    (h_carrier_266 : True → sc.indents = sc.indents ∧ 0 = 0)"
def probes : List String := ["core", "slot", "prop", "consumer", "gate"]
def usage : String := "usage: carrier_price.py [" ++ "|".intercalate probes ++ "|all]"

def applyProbe (lines : Array String) (which : String) : Except String (Array String) := do
  if which == "core" || which == "slot" then
    let i ← indexOf lines (if which == "core" then coreStruct else slotStruct)
    return insertAfter lines i field
  else if which == "prop" then
    let i ← indexOf lines propField
    return lines.set! i propRenamed
  else if which == "consumer" || which == "gate" then
    let i ← indexOf lines (if which == "consumer" then consumer else gate)
    return insertAfter lines i hyp
  else throw s!"AssertionError: {which}"

/-- `(raw error lines, by_decl)` or the Python's `SystemExit`. -/
def reading (which : String) (patched : Array String) (out : String) :
    Except String (Array Nat × Array (String × Array Nat)) := do
  let raw := (Scripts.Price.Attribute.errorLines out).qsort (· < ·)
  if raw.isEmpty then throw s!"{which}: the probe broke nothing -- it did not apply"
  return (raw, byDeclLines patched raw)

def verboseLines (which : String) (raw : Array Nat) (decls : Array (String × Array Nat)) : Array String :=
  #[s!"probe {which}: {raw.size} error sites in {decls.size} declarations", ""] ++ declRows decls

def allRow (p : String) (n d : Nat) (names : Array String) : String :=
  s!"{padRight p 9} errors={padLeft (toString n) 3}  declarations={padLeft (toString d) 2}  {", ".intercalate names.toList}"

def names (decls : Array (String × Array Nat)) : Array String := (decls.map (·.1)).qsort (· < ·)

private def sample : Array String := #[coreStruct, "  a : True", slotStruct, "  b : True", "lemma x : True := trivial"]
#guard (applyProbe sample "core").toOption == some #[coreStruct, field, "  a : True", slotStruct, "  b : True", "lemma x : True := trivial"]
#guard (applyProbe sample "prop").toOption == none
#guard (reading "core" sample "").toOption == none
#guard (reading "core" sample "L4YAML/Proofs/Production/StreamAccum.lean:5:1: error: a\nL4YAML/Proofs/Production/StreamAccum.lean:2:1: error: b\n").toOption.map (·.1) == some #[2, 5]
#guard verboseLines "core" #[2, 5] #[("ParkCore", #[2]), ("x", #[5])] == #["probe core: 2 error sites in 2 declarations", "", "    1  ParkCore", "    1  x"]
#guard allRow "core" 7 3 #["a", "b"] == "core      errors=  7  declarations= 3  a, b"

end

end Scripts.Price.Carrier
