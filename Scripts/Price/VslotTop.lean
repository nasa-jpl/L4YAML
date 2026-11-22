module

public import Scripts.Price.Attribute
meta import Scripts.Price.Attribute

/-!
# Scripts.Price.VslotTop — `vslot_top_price.py` (item 208): the SLOT-TOP conjunct

Adds `sc.currentIndent ≤ (nv : Int) ∧` inside `accum_block_on_closeThenBlock`'s `h_vslot`
and counts the PAYERS (errors outside the consumer, anchored on the nearest preceding
`h_vslot` mention).
-/

namespace Scripts.Price.VslotTop

open Scripts.Price.Attribute

public section

def anchor : String := "    (h_vslot : (∃ (nv : Nat) (sp_a : SurfPos), SLYamlStream sp_start sp_a ∧"
def probeLines : Array String :=
  #["      -- SLOT-TOP PROBE (scripts/vslot_top_price.py)", "      sc.currentIndent ≤ (nv : Int) ∧"]
def consumer : String := "accum_block_on_closeThenBlock"
def headline : String := s!"probe: slot-top conjunct on {consumer}'s h_vslot"

def applyProbe (lines : Array String) : Except String (Array String) := do
  let idx := (Array.range lines.size).filter fun i => lines[i]! == anchor
  if idx.size != 1 then throw s!"AssertionError: anchor matched {idx.size} lines, expected 1"
  return replaceLine lines idx[0]! (#[anchor] ++ probeLines)

def anchors (patched : Array String) : Array Anchor :=
  (Array.range patched.size).filterMap fun i =>
    if (patched[i]!.splitOn "h_vslot").length > 1 then some (i + 1, "") else none

def report (patched : Array String) (log : String) : Array String := Id.run do
  let census := errorLines log
  let payers := census.filter fun r => enclosingDecl patched r != consumer
  let consumers := census.filter fun r => enclosingDecl patched r == consumer
  let (groups, unanchored) := anchorErrors (anchors patched) (sortedNat payers)
  let decls := byDecl patched groups unanchored
  let mut out : Array String := #["", s!"raw error sites: {census.size}",
    s!"  in {consumer} (the CONSUMER reading the conjunct, not a producer): {consumers.size}",
    s!"  outside it (raw):                                    {payers.size}",
    "", s!"PAYERS: {groups.size + unanchored.size}   <- the conjunct's price",
    s!"declarations: {decls.size}", ""]
  for (d, hs) in decls do
    out := out.push s!"  {Scripts.Punt.Price.padLeft (toString hs.size) 3}  {d}   (L{", L".intercalate ((sortedNat hs).toList.map toString)})"
  let casc := cascades groups
  if !casc.isEmpty then
    out := out.push "" |>.push s!"collapsed cascades ({cascadeCount groups} errors were not payers):"
    for ((a, _), hits) in casc do
      out := out.push s!"  L{a}  {Scripts.Punt.Price.take (strip patched[a - 1]!) 64}"
      out := out.push s!"        <- errors at {joinNats hits}"
  if !unanchored.isEmpty then
    out := out.push "" |>.push s!"UNANCHORED ({unanchored.size}): no `h_vslot` mention precedes these, so they count one-for-one and the total is a CEILING:"
    for raw in unanchored do out := out.push s!"  L{raw}  in {enclosingDecl patched raw}"
  if payers.isEmpty then out := out.push "  (none -- every caller punts, and the conjunct is free)"
  return out

private def sample : Array String := #[
  "lemma accum_block_on_closeThenBlock",
  anchor,
  "      x) :",
  "  by simp",
  "lemma caller : True := by",
  "  exact f (h_vslot := by trivial)",
  "  done"]

#guard (applyProbe sample).toOption.map (·.size) == some 9
#guard (applyProbe #["x"]).toOption == none
#guard anchors sample == #[(2, ""), (6, "")]
#guard report sample "L4YAML/Proofs/Production/StreamAccum.lean:3:1: error: a\nL4YAML/Proofs/Production/StreamAccum.lean:7:1: error: b\nL4YAML/Proofs/Production/StreamAccum.lean:6:1: error: c\n" ==
  #["", "raw error sites: 3",
    "  in accum_block_on_closeThenBlock (the CONSUMER reading the conjunct, not a producer): 1",
    "  outside it (raw):                                    2",
    "", "PAYERS: 1   <- the conjunct's price", "declarations: 1", "",
    "    1  caller   (L6)", "",
    "collapsed cascades (1 errors were not payers):",
    "  L6  exact f (h_vslot := by trivial)", "        <- errors at 6, 7"]

end

end Scripts.Price.VslotTop
