module

public import Scripts.Price.Transport
meta import Scripts.Price.Transport

/-! # Scripts.Price.Ride — `ride_price.py` (item 273): what each arm can build with the ring paid; the ride, carrier and transport flips -/

namespace Scripts.Price.Ride

open Scripts.Price.Pin
open Scripts.Price.Coordinate (arms)
open Scripts.Price.Transport (payTac)
open Scripts.Punt.Price (padLeft padRight)

public section

def probeName : String := "_probe273"

def floorTerm : String := "exact ⟨KeyFloor.cleared h_opsk, fun i hlo hhi => absurd hhi (by omega)⟩"
def propTy (state : String) : String :=
  s!"∃ k, prevRealIdx? {state}.tokens {state}.tokens.size = some k ∧ {state}.tokens[k]!.val.isNodeProperty = true"
def propTerm (arm : String) : Option String :=
  if arm == "pendingProps" then
    some "exact (propsPark_prevReal_prop h_real_p h_run h_anchor_p h_tag_p).imp (fun k hk => ⟨hk.1, hk.2.1⟩)"
  else none

/-- `rows(arm)`: `(name, type, named derivation or none)`, in report order. -/
def rows (arm : String) : List (String × String × Option String) :=
  [("slot", "ParkSlot s_prep s' 0", some (payTac arm)),
   ("floor", "ParkFloor s_prep s' 0", some floorTerm),
   ("prop_sc", propTy "sc", propTerm arm),
   ("prop", propTy "s_prep", propTerm arm),
   ("gated", "FlowBaseAnchor (some s_prep) s' 0",
    some s!"refine ⟨Or.inr ?_, ⟨KeyFloor.cleared h_opsk, fun i hlo hhi => absurd hhi (by omega)⟩⟩; {payTac arm}")]
def rowNames : List String := (rows arms.head!).map (·.1)

def rideHead : String := "  have drop_ride : s_prep.simpleKey.possible = true →"
def rideTy : String := "      ∃ sp_gram' sp_block' sp_flow' sp_scan',"
def rideBody : String := "    ⟨sp_block, sp_block, sp_open, sp_open, h_stream_block, BlockStack.nil _,"
def anchorArm : String := "  | some sc0, s, d => ParkChoice sc0 s d ∧ ParkFloor sc0 s d"
def carrier (which : String) : String :=
  if which == "add" then "  | some sc0, s, d => ParkAnchor sc0 s d ∧ ParkFloor sc0 s d ∧ ParkSlot sc0 s d"
  else if which == "swap" then "  | some sc0, s, d => ParkSlot sc0 s d ∧ ParkFloor sc0 s d"
  else "  | some sc0, s, d => ParkAnchor sc0 s d ∧ ParkFloor sc0 s d"
def transportF : String := "    (f : ∀ sc0, ParkChoice sc0 s d → ParkFloor sc0 s d →"
def transportF2 : String := "    (f : ∀ sc0, 0 = 0 → ParkChoice sc0 s d → ParkFloor sc0 s d →"

def carriers : List String := ["add", "swap", "anchor"]

/-- `patch_flip`: one edit that fails on arity. -/
def patchFlip (lines : Array String) (which : String) : Except String (Array String) := do
  if which == "ride" then
    let i ← indexOf lines rideHead
    if !(i + 1 < lines.size && lines[i + 1]! == rideTy) then
      throw s!"AssertionError: the ride's type does not start where it did: {repr (lines.getD (i + 1) "")}"
    let out := lines.set! (i + 1) ("      0 = 0 → " ++ Scripts.Price.Attribute.strip rideTy)
    return out.set! (← indexOf out rideBody) ("    fun _ => " ++ Scripts.Price.Attribute.strip rideBody)
  else if which == "transport" then
    return lines.set! (← indexOf lines transportF) transportF2
  else if carriers.contains which then
    return lines.set! (← indexOf lines anchorArm) (carrier which)
  else throw s!"unknown flip '{which}'"

def armErr (out : String) : String :=
  "arm: the paid module does not elaborate:\n" ++
    "\n".intercalate ((out.splitOn "\n").filter fun l => (l.splitOn ": error").length > 1)

def gotLine (cells : Array (String × String × String)) (ride : Nat × Nat) (carrierN : Array (String × Nat × Nat)) (tr : Nat × Nat) : String := Id.run do
  let mut s := ""
  for n in rowNames do
    let per := String.join (arms.map fun a => ((cells.find? fun (x, y, _) => x == a && y == n).map (·.2.2)).getD "")
    s := s ++ s!"{n}={per} "
  s := s ++ s!"ride={ride.1}/{ride.2}"
  for v in carriers do
    let (c, d) := ((carrierN.find? (·.1 == v)).map (·.2)).getD (0, 0)
    s := s ++ s!" {v}={c}/{d}"
  return s ++ s!" transport={tr.1}/{tr.2}"

#guard gotLine #[("pendingProps", "slot", "P"), ("pendingBlock", "slot", "B"), ("pendingMapValue", "slot", "O")] (4, 2)
  #[("add", 3, 1), ("swap", 5, 2), ("anchor", 1, 1)] (7, 3) ==
  "slot=PBO floor= prop_sc= prop= gated= ride=4/2 add=3/1 swap=5/2 anchor=1/1 transport=7/3"

#guard (patchFlip #[rideHead, rideTy, "x", rideBody] "ride").toOption ==
  some #[rideHead, "      0 = 0 → ∃ sp_gram' sp_block' sp_flow' sp_scan',", "x",
    "    fun _ => ⟨sp_block, sp_block, sp_open, sp_open, h_stream_block, BlockStack.nil _,"]
#guard (patchFlip #[rideHead, "y", rideBody] "ride").toOption == none
#guard (patchFlip #[anchorArm] "swap").toOption == some #["  | some sc0, s, d => ParkSlot sc0 s d ∧ ParkFloor sc0 s d"]
#guard (patchFlip #[transportF] "transport").toOption == some #[transportF2]
#guard (patchFlip #[anchorArm] "bogus").toOption == none
#guard rowNames == ["slot", "floor", "prop_sc", "prop", "gated"]
#guard (rows "pendingBlock").map (fun (_, _, t) => t.isSome) == [true, true, false, false, true]

end

end Scripts.Price.Ride
