module

/-!
# Byte-level scanning shared by the HTML instruments (`svg-objects`, `html-to-pdf`)

The two Python scripts these replace worked with `re` over `str`; every delimiter
they looked for is ASCII, so the Lean ports scan the page's UTF-8 bytes and cut
slices at those ASCII delimiters (always a valid UTF-8 boundary).  Character
classes are Python's ASCII readings of `\s`, `\w`, `\d`, with any non-ASCII byte
counted as a word character (`\w` is Unicode-aware in `re`).
-/

namespace Scripts.Html

@[expose] public section

def ch (c : Char) : UInt8 := c.toUInt8
def lower8 (x : UInt8) : UInt8 := if 65 ≤ x && x ≤ 90 then x + 32 else x
/-- `\s` on ASCII: space, tab, LF, CR, FF, VT. -/
def isSpace8 (x : UInt8) : Bool :=
  x == 32 || x == 9 || x == 10 || x == 13 || x == 12 || x == 11
def isDigit8 (x : UInt8) : Bool := 48 ≤ x && x ≤ 57
def isAlpha8 (x : UInt8) : Bool := (65 ≤ x && x ≤ 90) || (97 ≤ x && x ≤ 122)
/-- `\w`: ASCII alphanumerics and `_`, plus every non-ASCII byte. -/
def isWord8 (x : UInt8) : Bool := isDigit8 x || isAlpha8 x || x == 95 || x ≥ 128

def sliceStr (cs : ByteArray) (a b : Nat) : String := String.fromUTF8! (cs.extract a b)

partial def skipWhile8 (cs : ByteArray) (p : UInt8 → Bool) (i : Nat) : Nat :=
  if i < cs.size && p cs[i]! then skipWhile8 cs p (i + 1) else i

/-- `pat` (ASCII) occurs at `i`; `icase` compares ASCII letters case-insensitively. -/
def matchesAt (cs : ByteArray) (i : Nat) (pat : String) (icase := false) : Bool :=
  let ps := pat.toUTF8
  i + ps.size ≤ cs.size && (List.range ps.size).all fun k =>
    if icase then lower8 cs[i + k]! == lower8 ps[k]! else cs[i + k]! == ps[k]!

/-- First position `≥ i` where `pat` occurs. -/
partial def findFrom (cs : ByteArray) (i : Nat) (pat : String) (icase := false) : Option Nat :=
  if i + pat.utf8ByteSize > cs.size then none
  else if matchesAt cs i pat icase then some i
  else findFrom cs (i + 1) pat icase

/-- Python's `Path.read_text()` newline translation: CRLF and a lone CR read as LF. -/
partial def universalNewlines (b : ByteArray) : ByteArray :=
  if skipWhile8 b (· != 13) 0 ≥ b.size then b else go 0 ByteArray.empty
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ b.size then out
    else
      let x := b[i]!
      if x == 13 then
        let out := out.push 10
        if i + 1 < b.size && b[i + 1]! == 10 then go (i + 2) out else go (i + 1) out
      else go (i + 1) (out.push x)

/-- `str(Path(s))`: trailing and doubled separators and `.` components dropped. -/
def pyPath (s : String) : String :=
  let abs := s.startsWith "/"
  let parts := (s.splitOn "/").filter fun c => !c.isEmpty && c != "."
  let body := "/".intercalate parts
  if abs then "/" ++ body else if body.isEmpty then "." else body

/-- `str(Path(s).parent)`. -/
def pyParent (s : String) : String :=
  let p := pyPath s
  match p.splitOn "/" with
  | [_] => if p.startsWith "/" then "/" else "."
  | parts =>
    let d := "/".intercalate (parts.dropLast)
    if d.isEmpty then "/" else d

/-- `n.strip(".")`. -/
def stripDots (n : String) : String :=
  String.ofList (((n.toList.dropWhile (· == '.')).reverse.dropWhile (· == '.')).reverse)

/-- `Path.__lt__`: component lists compared lexicographically. -/
partial def ltComps : List String → List String → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltComps as bs

#guard pyPath "doc/_out/html-multi/" == "doc/_out/html-multi"
#guard pyPath "./x//y" == "x/y"
#guard pyPath "." == "."
#guard stripDots "..3.2.." == "3.2"
#guard pyParent "doc/_out/html-single/index.html" == "doc/_out/html-single"
#guard pyParent "index.html" == "."
#guard pyParent "/index.html" == "/"
#guard String.fromUTF8! (universalNewlines "a\r\nb\rc\n".toUTF8) == "a\nb\nc\n"
#guard ltComps ["a", "b.html"] ["a-b.html"] == true
#guard matchesAt "<IMG src".toUTF8 0 "<img" (icase := true) == true
#guard findFrom "xx</ScRiPt>".toUTF8 0 "</script" (icase := true) == some 2

end

end Scripts.Html
