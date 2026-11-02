module

@[expose] public section Blanket

/-!
# Scripts.Flip.Patch — anchored replacement, the pure half of a flip

A flip spec names a file at a revision and a list of `(anchor, replacement)`
pairs.  Each anchor must occur exactly `count` times (one, unless the spec
says otherwise) in the text it is applied to, or the run refuses before
touching the tree — the protocol every `scripts/flip_*.py` wrote by hand
(`if t.count(old) != 1: sys.exit(...)`).  Patches apply in order, each to the
output of the previous one, as the Python's sequential `str.replace` did.
-/

namespace Scripts.Flip.Patch

/-- One anchored replacement.  `old`/`new` are the exact text (the spec gives
them as arrays of lines joined with `\n`). -/
structure Patch where
  name : String
  old : String
  new : String
  count : Nat := 1
  deriving Repr, Inhabited, BEq

/-- Non-overlapping occurrences of `pat` in `s` (Python `str.count`); 0 when
`pat` is empty, where Python would count positions. -/
def countOccurrences (s pat : String) : Nat :=
  if pat.isEmpty then 0 else ((s.splitOn pat).length - 1)

#guard countOccurrences "abcabc" "abc" == 2
#guard countOccurrences "aaaa" "aa" == 2          -- non-overlapping, as str.count
#guard countOccurrences "abc" "x" == 0
#guard countOccurrences "abc" "" == 0

/-- Python `str.replace(old, new)` for a non-empty `old`. -/
def replaceAll (s old new : String) : String :=
  if old.isEmpty then s else new.intercalate (s.splitOn old)

#guard replaceAll "a-b-c" "-" "+" == "a+b+c"
#guard replaceAll "abc" "x" "y" == "abc"

/-- Apply one patch; refuse with the anchor count and the head of the anchor. -/
def apply1 (t : String) (p : Patch) : Except String String :=
  let n := countOccurrences t p.old
  if n != p.count then
    .error s!"anchor count {n} != {p.count} for {p.name}:\n{p.old.take 90}"
  else .ok (replaceAll t p.old p.new)

/-- Apply the patches in order. -/
def applyAll (t : String) : List Patch → Except String String
  | [] => .ok t
  | p :: ps => do applyAll (← apply1 t p) ps

#guard (applyAll "def a := 1\ndef b := 2\n" [⟨"A", "def a := 1", "def a := 10", 1⟩, ⟨"B", "def b := 2", "def b := 20", 1⟩]).toOption
  == some "def a := 10\ndef b := 20\n"
#guard (applyAll "x x" [⟨"X", "x", "y", 1⟩]).isOk == false      -- 2 ≠ 1: refused
#guard (applyAll "x x" [⟨"X", "x", "y", 2⟩]).toOption == some "y y"
#guard (applyAll "abc" [⟨"M", "zzz", "y", 1⟩]).isOk == false    -- 0 ≠ 1: refused
#guard (applyAll "ab" [⟨"A", "a", "b", 1⟩, ⟨"B", "b", "c", 1⟩]).isOk == false  -- sequential: "bb" has 2 b's

/-- A 64-bit content hash printed both sides of a run (the Python printed md5;
core Lean has no MD5, and restoration is judged by byte equality, not the hash). -/
def digest (b : ByteArray) : String :=
  let h := hash b.data
  let hex := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - hex.length) ++ hex

#guard (digest "abc".toUTF8).length == 16
#guard digest "abc".toUTF8 == digest "abc".toUTF8
#guard digest "abc".toUTF8 != digest "abd".toUTF8

end Scripts.Flip.Patch
