module

public import Scripts.Punt.Price
meta import Scripts.Punt.Price

/-!
# Scripts.Price.Attribute — the shared reading behind the six `*_price.py` of items 205–210

`park_top_price.py`, `vslot_top_price.py`, `mv_slot_top_price.py`, `open_map_price.py`,
`park_nic0_price.py` and `landing_nic0_price.py` all took one reading: patch a probe
(a field, a conjunct, a binder) into `L4YAML/Proofs/Production/StreamAccum.lean`, run
`lake env lean` on the file, collect the error lines, anchor each on the nearest
preceding APPLICATION of the probed constructor or lemma (an error is not a producer: a
constructor application whose arguments are `by` blocks reports one failure per broken
block), and count anchors by enclosing declaration, printing every collapsed cascade and
every unanchored error so the collapse is checkable.  This module is that reading as pure
functions of the patched lines and of Lean's output, with each Python idiom named
(`sorted(census)`, `prior[-1]`, `{n:3d}`, `sorted(..., key=(-len, name))`).  The probes
and the per-script report wording are `Scripts.Price.<Script>`; the IO is
`Scripts.Price.Env` and `Scripts.Main.Price`.
-/

namespace Scripts.Price.Attribute

open Scripts.Punt.Price (target isWordChar padLeft padRight take drop errorLoc?)

public section

def strip (s : String) : String := Scripts.Punt.Price.strip s
def lstrip (s : String) : String := Scripts.Punt.Price.lstrip s
def rstrip (s : String) : String := Scripts.Punt.Price.rstrip s

/-- `^(?:private )?(?:lemma|theorem|def) (\w+)` — these six scripts' declaration regex
    (no `abbrev`, unlike `punt_reason_price.py`'s). -/
def declHead? (line : String) : Option String :=
  let rest := if line.startsWith "private " then drop line 8 else line
  ["lemma ", "theorem ", "def "].findSome? fun kw =>
    if rest.startsWith kw then
      let name := String.ofList ((drop rest kw.length).toList.takeWhile isWordChar)
      if name.isEmpty then none else some name
    else none

#guard declHead? "lemma foo_bar (x : Nat) :" == some "foo_bar"
#guard declHead? "private def FrameTail.ofToken" == some "FrameTail"
#guard declHead? "def frameTokenVal? (t : Token)" == some "frameTokenVal"
#guard declHead? "abbrev Foo := Nat" == none
#guard declHead? "  lemma indented" == none

/-- `enclosing_decl(lines, lineno)`: the last declaration head among the first `lineno`
    lines (1-based `lineno` inclusive), else `<file scope>`. -/
def enclosingDecl (lines : Array String) (lineno : Nat) : String := Id.run do
  let mut decl := "<file scope>"
  for i in [0:min lineno lines.size] do
    if let some n := declHead? lines[i]! then decl := n
  return decl

#guard enclosingDecl #["lemma a :", "  x", "def b :=", "  y"] 2 == "a"
#guard enclosingDecl #["lemma a :", "  x", "def b :=", "  y"] 3 == "b"
#guard enclosingDecl #["  x", "lemma a :"] 1 == "<file scope>"

/-- The error LINE numbers of `lake env lean`'s output, unique, in first-seen order —
    the Python's `census = {}` / `setdefault`. -/
def errorLines (out : String) : Array Nat :=
  (out.splitOn "\n").foldl (init := #[]) fun acc l =>
    match errorLoc? l with
    | some (n, _) => if acc.contains n then acc else acc.push n
    | none => acc

#guard errorLines "a\nL4YAML/Proofs/Production/StreamAccum.lean:9:2: error: a\nL4YAML/Proofs/Production/StreamAccum.lean:4:7: error: b\nL4YAML/Proofs/Production/StreamAccum.lean:9:5: error: c\n" == #[9, 4]

/-- `sorted(census)`. -/
def sortedNat (xs : Array Nat) : Array Nat := xs.qsort (· < ·)

/-- A stable sort (Python's `sorted` is stable; `Array.qsort` is not). -/
def stableSort {α : Type} (xs : Array α) (lt : α → α → Bool) : Array α :=
  xs.insertionSort lt

#guard stableSort #[(2, "b"), (1, "a"), (2, "a"), (1, "b")] (fun x y => x.1 < y.1) == #[(1, "a"), (1, "b"), (2, "b"), (2, "a")]

/-- `(-len(hits), key)` ordering of a `str → list` census. -/
def byCountThenName {α : Type} (a b : String × Array α) : Bool :=
  b.2.size < a.2.size || (a.2.size == b.2.size && a.1 < b.1)

/-- An anchor: a 1-based line and the label the report prints for it. -/
abbrev Anchor := Nat × String

/-- The attribution of every error line to `prior[-1]`, the last anchor at or before it:
    `groups` in insertion order over the given `census` order (each key once, its hits in
    that order), `unanchored` the errors no anchor precedes. -/
def anchorErrors (anchors : Array Anchor) (census : Array Nat) :
    Array (Anchor × Array Nat) × Array Nat := Id.run do
  let mut groups : Array (Anchor × Array Nat) := #[]
  let mut unanchored : Array Nat := #[]
  for raw in census do
    let prior := anchors.filter (·.1 ≤ raw)
    match prior.back? with
    | none => unanchored := unanchored.push raw
    | some a =>
      match groups.findIdx? (·.1 == a) with
      | some i => groups := groups.modify i fun (k, hs) => (k, hs.push raw)
      | none => groups := groups.push (a, #[raw])
  return (groups, unanchored)

#guard anchorErrors #[(3, "A"), (7, "B")] #[2, 4, 5, 9] == (#[((3, "A"), #[4, 5]), ((7, "B"), #[9])], #[2])

/-- `{a: h for a, h in groups.items() if len(h) > 1}` sorted by anchor. -/
def cascades (groups : Array (Anchor × Array Nat)) : Array (Anchor × Array Nat) :=
  stableSort (groups.filter (·.2.size > 1)) fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 < b.1.2)

def cascadeCount (groups : Array (Anchor × Array Nat)) : Nat :=
  (groups.filter (·.2.size > 1)).foldl (· + ·.2.size - 1) 0

#guard cascadeCount #[((3, "A"), #[4, 5, 6]), ((7, "B"), #[9])] == 2

/-- `", ".join(str(h) for h in hits)`. -/
def joinNats (hs : Array Nat) : String := ", ".intercalate (hs.toList.map toString)
/-- `", ".join(f"L{x}" for x in lns)`. -/
def joinL (hs : Array Nat) : String := ", ".intercalate (hs.toList.map fun h => s!"L{h}")

/-- An insertion-ordered `decl ↦ values` census. -/
def addTo {α : Type} (c : Array (String × Array α)) (k : String) (v : α) : Array (String × Array α) :=
  match c.findIdx? (·.1 == k) with
  | some i => c.modify i fun (k, vs) => (k, vs.push v)
  | none => c.push (k, #[v])

/-- `by_decl`: each group under its anchor's declaration, then each unanchored error
    under its own declaration, one entry per group / error. -/
def byDecl (lines : Array String) (groups : Array (Anchor × Array Nat)) (unanchored : Array Nat) :
    Array (String × Array Nat) := Id.run do
  let mut c : Array (String × Array Nat) := #[]
  for ((aline, _), _) in groups do c := addTo c (enclosingDecl lines aline) aline
  for raw in unanchored do c := addTo c (enclosingDecl lines raw) raw
  return stableSort c byCountThenName

/-- `  {len:3d}  {decl}` for each declaration. -/
def declLines (c : Array (String × Array Nat)) : Array String :=
  c.map fun (d, hs) => s!"  {padLeft (toString hs.size) 3}  {d}"

/-- `"--" not in line.split(needle)[0]`: no comment opener before the first occurrence. -/
def uncommentedBefore (line needle : String) : Bool :=
  match line.splitOn needle with
  | pre :: _ :: _ => !(pre.splitOn "--").length > 1
  | _ => false

#guard uncommentedBefore "  PendingNode.noPending x" "PendingNode.noPending"
#guard !uncommentedBefore "  -- PendingNode.noPending x" "PendingNode.noPending"
#guard !uncommentedBefore "  other" "PendingNode.noPending"

/-- `re.search(rf"\b{name}\b", line)`: some occurrence with non-word chars (or ends) around. -/
def hasWord (line word : String) : Bool := Id.run do
  let cs := line.toList.toArray
  let ws := word.toList.toArray
  if ws.isEmpty then return false
  for i in [0:cs.size] do
    if i + ws.size ≤ cs.size && (Array.range ws.size).all (fun k => cs[i + k]! == ws[k]!) then
      let before := if i == 0 then true else !isWordChar cs[i - 1]!
      let after := if i + ws.size == cs.size then true else !isWordChar cs[i + ws.size]!
      if before && after then return true
  return false

#guard hasWord "  (colon_open_map sp)" "colon_open_map"
#guard !hasWord "  (colon_open_map_props sp)" "colon_open_map"
#guard hasWord "x colon_open_map_props colon_open_map" "colon_open_map"

/-- `line.lstrip().startswith("--")`. -/
def isComment (line : String) : Bool := (lstrip line).startsWith "--"

/-- `len(line) - len(line.lstrip())`. -/
def indentOf (line : String) : Nat := line.length - (lstrip line).length

/-- `^  \| (\w+) \(sp_start` → the constructor name. -/
def ctorHead? (line : String) : Option String := do
  guard (line.startsWith "  | ")
  let name := String.ofList ((drop line 4).toList.takeWhile isWordChar)
  guard !name.isEmpty
  guard ((drop line (4 + name.length)).startsWith " (sp_start")
  return name

#guard ctorHead? "  | pendingFlow (sp_start sp_X sp_scan : SurfPos)" == some "pendingFlow"
#guard ctorHead? "  | pendingFlow : Foo" == none

/-- `constructor_spans(lines)`: each `PendingNode` constructor ↦ the 0-based index of its
    conclusion line (`PendingNode sc …`), in constructor order. -/
def constructorSpans (lines : Array String) : Array (String × Nat) := Id.run do
  let mut spans : Array (String × Nat) := #[]
  let mut current : Option String := none
  for i in [0:lines.size] do
    let line := lines[i]!
    match ctorHead? line with
    | some n => current := some n
    | none =>
      if let some c := current then
        if (strip line).startsWith "PendingNode sc " then
          spans := spans.push (c, i); current := none
  return spans

#guard constructorSpans #["inductive PendingNode", "  | noPending (sp_start : SurfPos)", "      (h : True) :", "      PendingNode sc []", "  | pendingFlow (sp_start sp_X : SurfPos) :", "      PendingNode sc [x]"] == #[("noPending", 3), ("pendingFlow", 5)]

/-- `out[sig].rstrip()[:-2].rstrip()` after `assert … .endswith(") :")`: the signature's
    last line with its ` :` removed. -/
def openSig (line : String) : Except String String :=
  let r := rstrip line
  if r.endsWith ") :" then .ok (rstrip (take r (r.length - 2)))
  else .error s!"AssertionError: {line}"

#guard (openSig "      (h_x : True) :  ").toOption == some "      (h_x : True)"
#guard (openSig "      (h_x : True)").toOption == none

/-- Replace line `i` by `[openSig lines[i], probe, field]`. -/
def spliceSig (lines : Array String) (i : Nat) (probe field : String) : Except String (Array String) := do
  let head ← openSig lines[i]!
  return (lines.extract 0 i) ++ #[head, probe, field] ++ (lines.extract (i + 1) lines.size)

#guard (spliceSig #["a", "  (h : T) :", "  C"] 1 "  -- P" "  (f : F) :").toOption == some #["a", "  (h : T)", "  -- P", "  (f : F) :", "  C"]

/-- Replace line `i` by `new` lines. -/
def replaceLine (lines : Array String) (i : Nat) (new : Array String) : Array String :=
  (lines.extract 0 i) ++ new ++ (lines.extract (i + 1) lines.size)

/-- `sorted(names)` by code point. -/
def sortedStrs (xs : Array String) : Array String := xs.qsort (· < ·)

/-- `sorted(targets, key=lambda n: -span[n])`: bottom-most first, so earlier splices do
    not move later indices. -/
def bottomUp (ts : Array (String × Nat)) : Array (String × Nat) :=
  stableSort ts fun a b => b.2 < a.2

end

end Scripts.Price.Attribute
