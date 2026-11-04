module

public import Scripts.Price.Pin
meta import Scripts.Price.Pin

/-! # Scripts.Price.Close — `close_price.py` (item 274): what the frame's CLOSE can pay for a reshaped carrier

The five probes are ONE insertion (ten `private lemma`s, each row and its `by assumption` twin)
before `probeAnchor` and ONE elaboration; `name` states a premise on `FlowBaseAnchor.gate` /
`gate_of_close`; `flip` is the arity census of the wrapped premise (`gate`, `close`), a rename
(`apps`) and a second verdict under `PendingNode.pendingContent` (`closable`); `wide` is the
wrapped premise over the tree.  Pin: `expectedClosePrice` (backslash-continued literal). -/

namespace Scripts.Price.Close

open Scripts.Punt.Price (take drop padLeft)
open Scripts.Price.Attribute (strip)
open Scripts.Price.Pin

public section

def probeAnchor : String := "/-! ### The `[96]` park's reading, relayed to its own RIDES (item 165)"

def closeReadings : String :=
  "    (hpre : ∀ j, j < s_bc.tokens.size → s_cl.tokens[j]! = s_bc.tokens[j]!)\n" ++
  "    (hind : s_cl.indents = s_bc.indents)\n" ++
  "    (hflow : s_cl.inFlow = false)\n" ++
  "    (hlast : prevRealIdx? s_cl.tokens s_cl.tokens.size = some s_bc.tokens.size)\n" ++
  "    (hclose : s_cl.tokens[s_bc.tokens.size]!.val.isFlowClose = true)\n" ++
  "    (hnd : danglingNodePos? s_cl = none)"

def nonoffer : String :=
  "    (hst : propsRunStart s_cl.tokens sc0.tokens.size = sc0.tokens.size)\n" ++
  "    (hoff : ∀ j, prevRealIdx? s_cl.tokens sc0.tokens.size = some j →\n" ++
  "      s_cl.tokens[j]!.val.offersNodeSlot = false)"

def offer : String :=
  "    (hoff : ∃ j, prevRealIdx? s_cl.tokens\n" ++
  "        (propsRunStart s_cl.tokens sc0.tokens.size) = some j ∧\n" ++
  "      s_cl.tokens[j]!.val.offersNodeSlot = true)"

def floorRead : String := "    (hui : underIndentedFlowValuePos? s_cl = none)"

def fires (hst hoff : String) : String :=
  s!"have hf := h.dangling_fires hpre hind hflow hlast hclose {hst} {hoff}; rw [hnd] at hf; simp at hf"
def under (ui : String) : String :=
  s!"have hf := h.underIndented_eq hpre hind hflow hlast hclose hoff; rw [{ui}] at hf; simp at hf"

/-- `(row, carrier, extra premises, the named derivation)`. -/
def rows : List (String × String × Option String × String) :=
  [("anchor", "ParkAnchor", none,
    "exact ⟨((h.dangling_eq hpre hind hflow hlast hclose).symm).trans hnd, h.parkSka⟩"),
   ("bare", "ParkSlot", none, fires "(by assumption)" "(by assumption)"),
   ("nonoffer", "ParkSlot", some nonoffer, fires "hst" "hoff"),
   ("offer", "ParkSlot", some offer, under "(by assumption : underIndentedFlowValuePos? s_cl = none)"),
   ("floor", "ParkSlot", some (offer ++ "\n" ++ floorRead), under "hui")]

def rowNames : List String := rows.map (·.1)

/-- The ten lemmas of the insertion: `(name, lines)`, a blank line after each (the Python's
    `"\n".join` of chunks that each end in `\n`). -/
def chunks : Array (String × Array String) := Id.run do
  let mut out := #[]
  for (row, carrier, extra, tac) in rows do
    for (kind, body) in [("probe", tac), ("null", "assumption")] do
      let prem := [s!"    (h : {carrier} sc0 s_bc 0)", closeReadings] ++ (match extra with | some e => [e] | none => [])
      let premLines := (("\n".intercalate prem).splitOn "\n").toArray
      let last := premLines.size - 1
      let premLines := premLines.set! last (premLines[last]! ++ " : GateOf (some sc0) := by")
      out := out.push (s!"_{kind}274_{row}",
        #[s!"private lemma _{kind}274_{row} \{sc0 s_bc s_cl : ScannerState}"] ++ premLines ++ #[s!"  {body}", ""])
  return out

def probeBlock : Array String := chunks.foldl (· ++ ·.2) #[]

/-- The lemma of the block owning 1-based `line`, the block having been inserted before 0-based
    index `pos` (so its first line is `pos + 1`). -/
def ownerInBlock (pos line : Nat) : Option String := Id.run do
  let mut start := pos + 1
  for (name, ls) in chunks do
    if start ≤ line && line < start + ls.size then return some name
    start := start + ls.size
  return none

#guard probeBlock.size == 10 * 1 + (chunks.foldl (· + ·.2.size) 0 - 10)
#guard (chunks.map (·.1)).toList.take 3 == ["_probe274_anchor", "_null274_anchor", "_probe274_bare"]
#guard chunks[0]!.2[0]! == "private lemma _probe274_anchor {sc0 s_bc s_cl : ScannerState}"
#guard chunks[0]!.2[7]! == "    (hnd : danglingNodePos? s_cl = none) : GateOf (some sc0) := by"
#guard chunks[0]!.2[8]! == "  exact ⟨((h.dangling_eq hpre hind hflow hlast hclose).symm).trans hnd, h.parkSka⟩"
#guard chunks[0]!.2.size == 10 && chunks[0]!.2[9]! == ""
#guard ownerInBlock 100 101 == some "_probe274_anchor"
#guard ownerInBlock 100 (100 + 10 + 1) == some "_null274_anchor"
#guard ownerInBlock 100 100 == none

def patchProbe (lines : Array String) : Except String (Nat × Array String) := do
  let i ← indexOf lines probeAnchor
  return (i, (lines.extract 0 i) ++ probeBlock ++ (lines.extract i lines.size))

def cellLine (cell row : String) : String := s!"  {cell}  {row}"

-- naming, at the spend
def gateHead : String := "lemma FlowBaseAnchor.gate {g : Option ScannerState} {s_bc s_cl : ScannerState}"
def closeHead : String := "lemma FlowBaseAnchor.gate_of_close {g : Option ScannerState} {s_bc s_cl : ScannerState}"
def pendingHead : String := "  | pendingContent (sp_start sp_block sp_scan : SurfPos)"
def closable : String := "        underIndentedFlowValuePos? sc = none → ∀ sp_mid,"
def closable2 : String := "        underIndentedFlowValuePos? sc = none → 0 = 0 → ∀ sp_mid,"
def closeRename : String := (closeHead.splitOn "gate_of_close").foldl (fun acc p => if acc == "" then p else acc ++ "gate_of_close_x" ++ p) ""
def barePrem : String := "    (hst : propsRunStart s_cl.tokens sc0.tokens.size = sc0.tokens.size)"
def wrapPrem : String := "    (hst : ∀ sc0, g = some sc0 → propsRunStart s_cl.tokens sc0.tokens.size = sc0.tokens.size)"

#guard closeRename == "lemma FlowBaseAnchor.gate_of_close_x {g : Option ScannerState} {s_bc s_cl : ScannerState}"

def patchPrem (lines : Array String) (head prem : String) : Except String (Array String) := do
  return insertAfter lines (← indexOf lines head) prem

def patchRename (lines : Array String) : Except String (Array String) := do
  return lines.set! (← indexOf lines closeHead) closeRename

def patchClosable (lines : Array String) : Except String (Array String) := do
  let i ← indexOf lines pendingHead
  let hits := (Array.range 24).filterMap fun k => if i + k < lines.size && lines[i + k]! == closable then some (i + k) else none
  if hits.size != 1 then throw s!"AssertionError: expected one {repr closable} under `pendingContent`, found {hits.size}"
  return lines.set! hits[0]! closable2

/-- `UNKNOWN = lean\.unknownIdentifier.*`sc0`: a naming refusal, not an arity one. -/
def isNamed (err : String) : Bool :=
  match err.splitOn "lean.unknownIdentifier" with
  | _ :: rest => (("".intercalate rest).splitOn "`sc0").length > 1
  | [] => false

#guard isNamed "L4YAML/Proofs/Production/StreamAccum.lean:3:4: error(lean.unknownIdentifier): Unknown identifier `sc0.tokens`"
#guard !isNamed "L4YAML/Proofs/Production/StreamAccum.lean:3:4: error: application type mismatch sc0"

def headName (head : String) : String := ((head.splitOn " ").drop 1).headD ""

def nameLine (named : Bool) (head : String) (errs : Array String) : String :=
  s!"  {if named then "O" else "B"}  {headName head}" ++ (if errs.isEmpty then "" else "  " ++ take errs[0]! 110)

#guard headName gateHead == "FlowBaseAnchor.gate"

/-- `run_flip`'s rows: `  {n:3d}  {decl}  @ {lines}` sorted `(-len, name)`. -/
def flipRows (decls : Array (String × Array Nat)) : Array String :=
  decls.map fun (d, hs) => s!"  {padLeft (toString hs.size) 3}  {d}  @ {", ".intercalate (hs.toList.map toString)}"

def wideReading (exitCode : UInt32) (out : String) : Except String (Array String × Nat) := do
  let mut hits : Array (String × Array Nat) := #[]
  let mut inside := 0
  for l in out.splitOn "\n" do
    if let some (p, n) := errLoc? l then
      if p.endsWith "Proofs/Production/StreamAccum.lean" then inside := inside + 1
      else hits := Scripts.Price.Attribute.addTo hits p n
  if exitCode == 0 then throw "wide: the tree BUILT under the flip -- a green build here is not a census of zero."
  if hits.isEmpty && inside == 0 then
    throw "wide: the build failed and no location parsed -- the census is absent rather than zero."
  let sorted := hits.qsort (·.1 < ·.1)
  return (#[s!"  {padLeft (toString inside) 3}  (inside the edited module)"] ++
    sorted.map (fun (f, ls) => s!"  {padLeft (toString ls.size) 3}  {f}"), inside)

/-- `CLOSE-PRICE`'s payload. -/
def gotLine (cells : Array (String × String)) (name wrap : Array String)
    (flips : Array (String × Nat × Array String)) (apps : Nat) : String :=
  " ".intercalate (rowNames.map fun n => s!"{n}=" ++ ((cells.find? (·.1 == n)).map (·.2)).getD "")
  ++ " name=" ++ String.join name.toList ++ " wrap=" ++ String.join wrap.toList
  ++ String.join (["gate", "close", "closable"].map fun t =>
      match flips.find? (·.1 == t) with | some (_, n, ds) => s!" {t}={n}/{ds.size}" | none => s!" {t}=")
  ++ s!" apps={apps}"

#guard gotLine #[("anchor", "B"), ("bare", "O"), ("nonoffer", "B"), ("offer", "O"), ("floor", "B")] #["O", "O"] #["B", "B"]
  #[("gate", 1, #["a"]), ("close", 4, #["b"]), ("closable", 20, #["c", "d", "e", "f", "g"])] 2 ==
  "anchor=B bare=O nonoffer=B offer=O floor=B name=OO wrap=BB gate=1/1 close=4/1 closable=20/5 apps=2"

def modes : List String := ["probe", "name", "flip", "all", "wide"]

end

end Scripts.Price.Close
