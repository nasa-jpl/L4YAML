module

public import Scripts.Price.Coordinate
meta import Scripts.Price.Coordinate

/-! # Scripts.Price.Transport — `transport_price.py` (item 272): the open token's position through the arms -/

namespace Scripts.Price.Transport

open Scripts.Price.Pin
open Scripts.Price.Coordinate (arms ident floorH colTerm allOf)
open Scripts.Punt.Price (padLeft padRight)

public section

def probeName : String := "_probe272"

def sourceTerm (arm : String) : String :=
  s!"underRunEnd_landing_on_stack h_preprocess h_base {floorH arm} h_col02 hj h_ind h_end hcorr_prep (h_landed_ur ({colTerm arm}) h_noflow_prep)"
def memTy : String := "(s_prep.indents.any fun e => e.column == (s_prep.col : Int)) = true"
def hcolTy : String :=
  "∀ p : Positioned YamlToken, s'.tokens = s_prep.tokens.push p → p.val.isFlowOpen = true → (s_prep.indents.any fun e => e.column == (p.pos.col : Int)) = true"
def posTy : String :=
  "∀ p : Positioned YamlToken, s'.tokens = s_prep.tokens.push p → p.val.isFlowOpen = true → p.pos.col = s_prep.col"
def genesisTy : String := s!"({posTy}) → ParkSlot s_prep s' 0"
def openTok (arm : String) : Option (String × String × String) :=
  if arm == "pendingProps" then some ("p_br", "h_br_tok", "h_br_open") else none
def hrun (arm : String) : String :=
  if arm == "pendingProps" then
    "(slotRun_of_dn h_slot_p h_dn (h_ska_ur (Nat.ne_of_gt h_col0_p) h_noflow_prep) h_floor_p hj h_base h_preprocess)"
  else if arm == "pendingBlock" then "(slotRun_of_offer h_offer_b h_preprocess)"
  else "(slotRun_of_offer h_offer_mv h_preprocess)"

def genesisTac (arm : String) (ringed : Bool := true) : String :=
  let (intro, p_, tok, op) := match openTok arm with
    | none => (if ringed then "obtain ⟨p, htok, hop, -⟩ := h_optok; " else "obtain ⟨p, htok, hop⟩ := h_optok; ", "p", "htok", "hop")
    | some (p_, tok, op) => ("", p_, tok, op)
  s!"intro hpos; {intro}refine ParkSlot.ofOpen {tok} {op} h_ind' h_noflow_prep ?_ {hrun arm}; rw [hpos {p_} {tok} {op}]; exact {sourceTerm arm}"

def rows (arm : String) (ringed : Bool := true) : List (String × String × String) :=
  [("source", memTy, s!"exact {sourceTerm arm}"),
   ("hcol", hcolTy, s!"exact fun p _ _ => {sourceTerm arm}"),
   ("genesis", genesisTy, genesisTac arm ringed)]

def optok : String := "        p.pos.col = s_prep.col)"
def optok2 : String := "        p.pos.col = s_prep.col ∧ 0 = 0)"
def kpkg : String := "      FlowBaseAnchor g s' 0 →"
def kpkg2 : String := "      FlowBaseAnchor g s' 0 → 0 = 0 →"
def kpkgFun : String := "    fun g n _ _ h_st h_mk h_kp hfl h_anch h_b =>"
def kpkgFun2 : String := "    fun g n _ _ h_st h_mk h_kp hfl h_anch _ h_b =>"

def ringed (lines : Array String) : Bool := (allOf lines optok).size == 1

def patchFlip (lines : Array String) (which : String) : Except String (Array String) := do
  if which == "optok" then
    return lines.set! (← indexOf lines optok) optok2
  else
    let out := lines.set! (← indexOf lines kpkg) kpkg2
    return out.set! (← indexOf out kpkgFun) kpkgFun2

/-- `run_flip`'s reading: by-decl rows, `(raw count, sorted decl names)`. -/
def flipReading (which : String) (patched : Array String) (out : String) : Except String (Array String × Nat × Array String) := do
  let raw := (Scripts.Price.Attribute.errorLines out).qsort (· < ·)
  if raw.isEmpty then throw s!"{which}: the flip broke nothing -- it did not apply"
  let decls := byDeclLines patched raw
  return (declRows decls, raw.size, (decls.map (·.1)).qsort (· < ·))

/-- `run_wide`'s reading: rows (inside count first), `(inside, hits)`. -/
def wideReading (which : String) (exitCode : UInt32) (out : String) : Except String (Array String × Nat × Array (String × Array Nat)) := do
  let mut hits : Array (String × Array Nat) := #[]
  let mut inside := 0
  for l in out.splitOn "\n" do
    if let some (p, n) := errLoc? l then
      if p.endsWith "Proofs/Production/StreamAccum.lean" then inside := inside + 1
      else hits := Scripts.Price.Attribute.addTo hits p n
  if exitCode == 0 then throw s!"wide/{which}: the tree BUILT under the flip -- a green build here is not a census of zero."
  if hits.isEmpty && inside == 0 then
    throw s!"wide/{which}: the build failed and no location parsed -- the census is absent rather than zero."
  let sorted := hits.qsort (·.1 < ·.1)
  return (#[s!"  {padLeft (toString inside) 3}  (inside the edited module)"] ++
    sorted.map (fun (f, ls) => s!"  {padLeft (toString ls.size) 3}  {f}"), inside, sorted)

def optokReal0 : String := "      s'.tokens = s_prep.tokens.push p ∧ p.val.isFlowOpen = true ∧"
def optokReal1 : String := optok
def propsObtain : String := "    obtain ⟨p_br, h_br_tok, h_br_open⟩ := h_optok"
def propsObtain2 : String := "    obtain ⟨p_br, h_br_tok, h_br_open, _h_br_pos⟩ := h_optok"
def callsite (k : String) : String := s!"⟨_, by rw [scanFlow{k}Start_tokens, allowDirectives_update_tokens], rfl⟩"
def callsite2a (k : String) : String := s!"⟨_, by rw [scanFlow{k}Start_tokens, allowDirectives_update_tokens], rfl,"
def callsite2b : String := "by rw [allowDirectives_update_currentPos]; rfl⟩"

/-- `patch_pay`: item 272's ring PAID; unchanged on a tree that already carries it (item 285). -/
def patchPay (lines : Array String) : Except String (Array String) := do
  if ringed lines then return lines
  let mut out := lines
  let head := Scripts.Punt.Price.take optokReal0 (optokReal0.length - 2) ++ ")"
  let i ← indexOf out head
  out := (out.set! i optokReal0).insertIdx! (i + 1) optokReal1
  out := out.set! (← indexOf out propsObtain) propsObtain2
  for k in ["Sequence", "Mapping"] do
    let want := callsite k
    let hits := (Array.range out.size).filter fun j => Scripts.Price.Attribute.strip out[j]! == want
    if hits.size != 1 then throw s!"AssertionError: expected one {k} call site, got {hits.size}"
    let j := hits[0]!
    let l := out[j]!
    let ind := Scripts.Punt.Price.take l (l.length - (Scripts.Price.Attribute.lstrip l).length)
    out := Scripts.Price.Attribute.replaceLine out j #[ind ++ callsite2a k, ind ++ "  " ++ callsite2b]
  return out

def payTac (arm : String) : String :=
  let (intro, tok, op, pos) := match openTok arm with
    | none => ("obtain ⟨p, htok, hop, hpos⟩ := h_optok; ", "htok", "hop", "hpos")
    | some (_, tok, op) => ("", tok, op, "_h_br_pos")
  s!"{intro}refine ParkSlot.ofOpen {tok} {op} h_ind' h_noflow_prep ?_ {hrun arm}; rw [{pos}]; exact {sourceTerm arm}"
def payTy : String := "ParkSlot s_prep s' 0"
def payLine (v arm : String) : String := s!"  {v}  {padRight arm 16} ParkSlot (ring paid)"

def rideAnchor : String := "  have drop_ride : s_prep.simpleKey.possible = true →"
def rideTac (binder : String) : String := s!"exact (fun _ => trivial) {binder}"
def rideLine (ok : Bool) (arm : String) : String := s!"  {if ok then "yes" else "no "} {ident arm} ({arm}) at the ride"
def rideControl (ok : Bool) : String := s!"  {if ok then "yes" else "no "} h_base (control) at the ride"
def rideControlErr : String :=
  "ride: the CONTROL failed -- a hypothesis of the declaration is invisible at the ride, so the probe is measuring its own insertion and not the scope."

def cellLine (v arm name : String) : String := s!"  {v}  {padRight arm 16} {name}"

def gotLine (cells : Array (String × String × String)) (optokN : Nat) (pay : Array (String × String)) (frames ride : Nat) : String := Id.run do
  let mut s := ""
  for (n, _, _) in rows arms.head! do
    let per := String.join (arms.map fun a => ((cells.find? fun (x, y, _) => x == a && y == n).map (·.2.2)).getD "")
    s := s ++ s!"{n}={per} "
  s := s ++ s!"optok={optokN} pay=" ++ String.join (arms.map fun a => ((pay.find? (·.1 == a)).map (·.2)).getD "")
  return s ++ s!" frames={frames} ride={ride}/{arms.length}"

#guard (patchFlip #["a", optok, "b"] "optok").toOption == some #["a", optok2, "b"]
#guard (patchFlip #[optok, optok] "optok").toOption == none
#guard (patchFlip #[kpkg, "x", kpkgFun] "frames").toOption == some #[kpkg2, "x", kpkgFun2]
#guard (wideReading "optok" 1 "error: L4YAML/Proofs/Production/StreamAccum.lean:3:1: x\nTests/B.lean:4:2: error: y\n").toOption ==
  some (#["    1  (inside the edited module)", "    1  Tests/B.lean"], 1, #[("Tests/B.lean", #[4])])
#guard (wideReading "optok" 0 "").toOption == none
#guard (patchPay #[optok]).toOption == some #[optok]
#guard (patchPay #["      s'.tokens = s_prep.tokens.push p ∧ p.val.isFlowOpen = true)", propsObtain,
    "  " ++ callsite "Sequence", "    " ++ callsite "Mapping"]).toOption ==
  some #[optokReal0, optokReal1, propsObtain2, "  " ++ callsite2a "Sequence", "    " ++ callsite2b,
    "    " ++ callsite2a "Mapping", "      " ++ callsite2b]
#guard genesisTac "pendingBlock" false |>.startsWith "intro hpos; obtain ⟨p, htok, hop⟩ := h_optok; refine ParkSlot.ofOpen htok hop"
#guard genesisTac "pendingProps" |>.startsWith "intro hpos; refine ParkSlot.ofOpen h_br_tok h_br_open"
#guard gotLine #[("pendingProps", "source", "P"), ("pendingBlock", "source", "O"), ("pendingMapValue", "source", "B")] 5
  #[("pendingProps", "P"), ("pendingBlock", "B"), ("pendingMapValue", "B")] 2 3 ==
  "source=POB hcol= genesis= optok=5 pay=PBB frames=2 ride=3/3"

end

end Scripts.Price.Transport
