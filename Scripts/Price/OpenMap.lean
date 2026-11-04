module

public import Scripts.Price.Attribute
meta import Scripts.Price.Attribute

/-!
# Scripts.Price.OpenMap — `open_map_price.py` (item 209): the DISPATCH-FLOOR ring

Adds `h_disp_floor : s_prep.currentIndent ≤ (s_prep.col : Int)` to the six `*_open_map`
producers (or the ones named) and counts their CALLERS: each error anchored on the nearest
preceding application of a probed lemma, by declaration and by probed lemma.
-/

namespace Scripts.Price.OpenMap

open Scripts.Price.Attribute

public section

def lemmas : List String :=
  ["colon_open_map", "question_open_map", "colon_open_map_explicit",
   "compact_open_map", "colon_open_map_implicit", "colon_open_map_props"]
def probeLine : String := "    -- DISPATCH-FLOOR PROBE (scripts/open_map_price.py)"
def field : String := "    (h_disp_floor : s_prep.currentIndent ≤ (s_prep.col : Int)) :"

/-- `^(?:private )?lemma (\w+)[ {(]` → the lemma's name. -/
def lemmaHead? (line : String) : Option String := do
  let rest := if line.startsWith "private " then Scripts.Punt.Price.drop line 8 else line
  guard (rest.startsWith "lemma ")
  let name := String.ofList ((Scripts.Punt.Price.drop rest 6).toList.takeWhile Scripts.Punt.Price.isWordChar)
  guard !name.isEmpty
  guard ((Scripts.Punt.Price.drop rest (6 + name.length)).toList.head?.any fun c => c == ' ' || c == '{' || c == '(')
  return name

#guard lemmaHead? "lemma colon_open_map {x} :" == some "colon_open_map"
#guard lemmaHead? "private lemma foo (x) :" == some "foo"
#guard lemmaHead? "lemma foo :" == some "foo"
#guard lemmaHead? "lemma foo:" == none

/-- `sig_end(lines, start)`: the first line at or below `start` ending in `) :` (within 400). -/
def sigEnd (lines : Array String) (start : Nat) : Except String Nat := do
  for j in [start:start + 400] do
    if j < lines.size && (rstrip lines[j]!).endsWith ") :" then return j
  throw s!"AssertionError: no signature end below line {start + 1}"

def applyProbe (lines : Array String) (names : List String) : Except String (Array String) := do
  let mut starts : Array (String × Nat) := #[]
  for i in [0:lines.size] do
    if let some n := lemmaHead? lines[i]! then
      if names.contains n then
        starts := match starts.findIdx? (·.1 == n) with
          | some k => starts.set! k (n, i)
          | none => starts.push (n, i)
  let missing := names.filter fun n => (starts.find? (·.1 == n)).isNone
  if !missing.isEmpty then throw s!"AssertionError: not found: {missing}"
  let mut out := lines
  let ordered := stableSort (names.toArray.map fun n => (n, (starts.find? (·.1 == n)).get!.2)) fun a b => b.2 < a.2
  for (_, start) in ordered do
    let e ← sigEnd out start
    out ← spliceSig out e probeLine field
  return out

def anchors (patched : Array String) (names : List String) : Array Anchor := Id.run do
  let mut out : Array Anchor := #[]
  for i in [0:patched.size] do
    let line := patched[i]!
    let isLemma := line.startsWith "lemma " || line.startsWith "private lemma "
    if !isLemma then
      if let some n := names.find? (fun n => hasWord line n && uncommentedBefore line n) then
        out := out.push (i + 1, n)
  return out

def headline (names : List String) : String :=
  s!"probe: dispatch floor on {names.length} lemma(s) -> {", ".intercalate names}"

def report (patched : Array String) (names : List String) (log : String) : Array String := Id.run do
  let census := sortedNat (errorLines log)
  let (groups, unanchored) := anchorErrors (anchors patched names) census
  let decls := byDecl patched groups unanchored
  let mut out : Array String := #["", s!"raw error sites: {census.size}",
    s!"applications:    {groups.size + unanchored.size}   <- the RING",
    s!"declarations:    {decls.size}", ""]
  out := out ++ declLines decls
  out := out.push "" |>.push "by probed lemma (which producer each caller feeds):"
  for n in names do
    let k := (groups.filter fun ((_, m), _) => m == n).size
    out := out.push s!"  {Scripts.Punt.Price.padLeft (toString k) 3}  {n}"
  let casc := cascades groups
  if !casc.isEmpty then
    out := out.push "" |>.push s!"collapsed cascades ({cascadeCount groups} errors were not callers):"
    for ((aline, name), hits) in casc do
      out := out.push s!"  L{aline}  {name}  <- errors at {joinNats hits}"
  if !unanchored.isEmpty then
    out := out.push "" |>.push s!"UNANCHORED ({unanchored.size}): no application literal precedes these, so they count one-for-one and the total is a CEILING:"
    for raw in unanchored do out := out.push s!"  L{raw}  in {enclosingDecl patched raw}"
  if census.isEmpty then out := out.push "  (none -- every caller already holds the floor)"
  return out

private def sample : Array String := #[
  "lemma colon_open_map (x : Nat)",
  "    (h : True) :",
  "    True := by trivial",
  "lemma caller : True := by",
  "  have := colon_open_map 0 trivial  -- colon_open_map",
  "  exact (colon_open_map_props 1)"]

#guard (applyProbe sample ["colon_open_map"]).toOption == some #[
  "lemma colon_open_map (x : Nat)", "    (h : True)", probeLine, field,
  "    True := by trivial", "lemma caller : True := by",
  "  have := colon_open_map 0 trivial  -- colon_open_map", "  exact (colon_open_map_props 1)"]
#guard (applyProbe sample ["compact_open_map"]).toOption == none
#guard anchors sample ["colon_open_map", "colon_open_map_props"] == #[(5, "colon_open_map"), (6, "colon_open_map_props")]
#guard report sample ["colon_open_map"] "L4YAML/Proofs/Production/StreamAccum.lean:5:3: error: a\n" ==
  #["", "raw error sites: 1", "applications:    1   <- the RING", "declarations:    1", "",
    "    1  caller", "", "by probed lemma (which producer each caller feeds):", "    1  colon_open_map"]

end

end Scripts.Price.OpenMap
