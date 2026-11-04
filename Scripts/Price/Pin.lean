module

public import Scripts.Price.Attribute
meta import Scripts.Price.Attribute
public import Scripts.Punt.Price
meta import Scripts.Punt.Price

/-!
# Scripts.Price.Pin — what `carrier_price.py`, `wire_price.py` and `arm_price.py` share

The items 266–270 instruments: an exact-one anchor (`_index`), the error lines grouped by
the declaration owning them (off the module's declaration ranges, not a header regex), `lake build` / `lake env lean` error
locations split into the module's own lines and other files, and the two readers of the
`expected…` literals in `Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean` (the regex one,
and `arm_price.py`'s character scan that honours a `\`⏎ continuation).
-/

namespace Scripts.Price.Pin

open Scripts.Punt.Price (take drop padLeft padRight isWordChar)
open Scripts.Price.Attribute (rstrip strip lstrip stableSort)

public section

def pin : String := "Tests/Guards/Proofs/ScannerFlowOpenUnderRun.lean"
def self : String := "Proofs/Production/StreamAccum.lean"

/-- `_index(lines, needle)`: the one line whose `rstrip()` is `needle`. -/
def indexOf (lines : Array String) (needle : String) : Except String Nat := do
  let hits := (Array.range lines.size).filter fun i => rstrip lines[i]! == needle
  if hits.size != 1 then throw s!"AssertionError: expected exactly one {repr needle}, found {hits.size}"
  return hits[0]!

#guard (indexOf #["a", "b  ", "c"] "b").toOption == some 1
#guard (indexOf #["a", "b", "b"] "b").toOption == none

def insertAfter (lines : Array String) (i : Nat) (l : String) : Array String :=
  (lines.extract 0 (i + 1)) ++ #[l] ++ (lines.extract (i + 1) lines.size)

#guard insertAfter #["a", "b"] 0 "x" == #["a", "x", "b"]

/-- `by_decl`: the error lines grouped by the declaration owning each (`owner`, read off the
    module's declaration ranges — `Scripts.Lean.DeclRanges`), sorted `(-len, name)`. -/
def byDeclLines (owner : Nat → String) (raw : Array Nat) : Array (String × Array Nat) := Id.run do
  let mut c : Array (String × Array Nat) := #[]
  for r in raw do c := Scripts.Price.Attribute.addTo c (owner r) r
  return stableSort c Scripts.Price.Attribute.byCountThenName

#guard byDeclLines (fun l => if l < 10 then "a" else "b") #[3, 12, 5] == #[("a", #[3, 5]), ("b", #[12])]

def declRows (c : Array (String × Array Nat)) : Array String :=
  c.map fun (d, hs) => s!"  {padLeft (toString hs.size) 3}  {d}"

def isPathChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '/' || c == '-'

/-- `^error: (P\.lean):(\d+):(\d+): ` (Lake) or `^(P\.lean):(\d+):(\d+): error` (Lean) →
    `(path, line)`. -/
def errLoc? (line : String) : Option (String × Nat) := do
  let lakeForm := line.startsWith "error: "
  let rest := if lakeForm then drop line 7 else line
  let cs := rest.toList
  let path := cs.takeWhile isPathChar
  guard ((String.ofList path).endsWith ".lean")
  let cs := cs.drop path.length
  guard (cs.head? == some ':')
  let d1 := (cs.drop 1).takeWhile Char.isDigit
  guard !d1.isEmpty
  let cs := (cs.drop 1).drop d1.length
  guard (cs.head? == some ':')
  let d2 := (cs.drop 1).takeWhile Char.isDigit
  guard !d2.isEmpty
  let tail := String.ofList ((cs.drop 1).drop d2.length)
  guard (if lakeForm then tail.startsWith ": " else tail.startsWith ": error")
  return (String.ofList path, (String.ofList d1).toNat!)

#guard errLoc? "error: ./././L4YAML/Proofs/Production/StreamAccum.lean:12:3: boom" == some ("./././L4YAML/Proofs/Production/StreamAccum.lean", 12)
#guard errLoc? "L4YAML/Proofs/Production/StreamAccum.lean:12:3: error: boom" == some ("L4YAML/Proofs/Production/StreamAccum.lean", 12)
#guard errLoc? "L4YAML/Proofs/Production/StreamAccum.lean:12:3: warning: x" == none
#guard errLoc? "✔ [1/2] Built X" == none

/-- The module's own error lines (sorted, unique) and the other files (sorted, unique). -/
def splitErrors (out : String) : Array Nat × Array String := Id.run do
  let mut raw : Array Nat := #[]
  let mut away : Array String := #[]
  for l in out.splitOn "\n" do
    if let some (p, n) := errLoc? l then
      if p.endsWith self then
        if !raw.contains n then raw := raw.push n
      else
        if !away.contains p then away := away.push p
  return (raw.qsort (· < ·), away.qsort (· < ·))

#guard splitErrors "L4YAML/Proofs/Production/StreamAccum.lean:9:1: error: a\nerror: Tests/X.lean:3:1: b\nL4YAML/Proofs/Production/StreamAccum.lean:4:1: error: c\n" == (#[4, 9], #["Tests/X.lean"])

/-- `def NAME : String :=\s*\n?\s*"([^"]*)"` → the literal. -/
def expectedLiteral? (src name : String) : Option String := do
  let parts := src.splitOn s!"def {name} : String :="
  guard (parts.length > 1)
  let rest := (parts.drop 1).head!
  let cs := rest.toList
  let ws := cs.takeWhile fun c => c == ' ' || c == '\t'
  let cs := cs.drop ws.length
  let cs := if cs.head? == some '\n' then cs.drop 1 else cs
  let cs := cs.dropWhile fun c => c == ' ' || c == '\t'
  guard (cs.head? == some '"')
  return String.ofList ((cs.drop 1).takeWhile (· != '"'))

#guard expectedLiteral? "x\ndef expectedWirePrice : String := \"gate=49 anchor=2\"\n" "expectedWirePrice" == some "gate=49 anchor=2"
#guard expectedLiteral? "def expectedCarrierPrice : String :=\n  \"core=7 slot=7\"\n" "expectedCarrierPrice" == some "core=7 slot=7"
#guard expectedLiteral? "def other : String := \"x\"" "expectedWirePrice" == none

/-- `arm_price.py`'s `read_pin`: the literal after `def NAME : String :=`, scanned character by
    character; a backslash swallows itself and the whitespace after it. -/
private partial def scanLiteral : List Char → List Char → Option (List Char)
  | [], _ => none
  | '"' :: _, acc => some acc.reverse
  | '\\' :: t, acc => scanLiteral (t.dropWhile fun c => c == ' ' || c == '\t' || c == '\n') acc
  | c :: t, acc => scanLiteral t (c :: acc)

def expectedScanned? (src name : String) : Option String := do
  let parts := src.splitOn s!"def {name} : String :="
  guard (parts.length > 1)
  let cs := ((parts.drop 1).head!).toList
  let cs := cs.dropWhile (· != '"')
  guard (cs.head? == some '"')
  return String.ofList (← scanLiteral (cs.drop 1) [])

#guard expectedScanned? "def expectedArmTable : String :=\n  \"cells=24 paid=10 \\\n    owed=14\"\n" "expectedArmTable" == some "cells=24 paid=10 owed=14"
#guard expectedScanned? "def expectedArmTable : String :=\n  \"open" "expectedArmTable" == none

/-- The pin verdict lines shared by the three scripts' `all` mode. -/
def pinVerdict (label : String) (want : Option String) (got : String) : Array String × UInt32 :=
  match want with
  | none => (#[s!"no pin in {pin}"], 1)
  | some w => if w != got then (#[s!"{label}-PIN DISAGREES", s!"  Lean:   {w}", s!"  script: {got}"], 1)
              else (#[s!"{label}-PIN agrees with {pin}"], 0)

end

end Scripts.Price.Pin
