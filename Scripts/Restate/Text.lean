module

/-!
# `Scripts.Restate.Text` — the line-and-character helpers the restate instruments share

`decline_all_optional.py`, `pay_chain_optional.py` and `narrow_conclusion.py` edited a
proof module as a list of lines and character columns (`str.find`, slices, `rstrip`,
`" ".join(s.split())`); these are those operations, so the Lean edits land on the same
bytes.  Lines are `Array Char` while an edit is computed and `String` at the boundary.
-/

namespace Scripts.Restate

@[expose] public section

/-- `s[: s.find("--")]` — the text before the first `--`. -/
def stripComment (s : String) : String :=
  match s.splitOn "--" with
  | h :: _ :: _ => h
  | _ => s

/-- `s.strip()`. -/
def strip (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

def rstrip (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse

/-- `" ".join(s.split())`. -/
def collapseWs (s : String) : String :=
  " ".intercalate (words s.toList [] [])
where
  words : List Char → List Char → List String → List String
    | [], [], acc => acc.reverse
    | [], w, acc => (String.ofList w.reverse :: acc).reverse
    | c :: cs, w, acc =>
      if c.isWhitespace then words cs [] (if w.isEmpty then acc else String.ofList w.reverse :: acc)
      else words cs (c :: w) acc

/-- `line.find(pat, from)` on character arrays. -/
partial def findSub (l pat : Array Char) (from_ : Nat := 0) : Option Nat :=
  if from_ + pat.size > l.size then none
  else if (List.range pat.size).all (fun k => l[from_ + k]! == pat[k]!) then some from_
  else findSub l pat (from_ + 1)

/-- `line.rfind(pat)`. -/
def rfindSub (l pat : Array Char) : Option Nat :=
  (List.range (l.size + 1)).reverse.findSome? fun i =>
    if i + pat.size ≤ l.size && (List.range pat.size).all (fun k => l[i + k]! == pat[k]!) then some i else none

def chars (s : String) : Array Char := s.toList.toArray
def ofChars (a : Array Char) : String := String.ofList a.toList
def slice (a : Array Char) (lo hi : Nat) : String := ofChars (a.extract lo hi)

/-- `s.count(pat)` — non-overlapping. -/
partial def countSub (s pat : String) (acc : Nat := 0) : Nat :=
  if pat.isEmpty then acc else
  match findSub (chars s) (chars pat) with
  | none => acc
  | some i => countSub (slice (chars s) (i + pat.length) (chars s).size) pat (acc + 1)

/-- `^(?:private )?(?:lemma|theorem) ([A-Za-z_][A-Za-z0-9_'!?]*)` (with `.` in the name
    when `allowDot`, `narrow_conclusion.py`'s variant). -/
def declHead? (allowDot : Bool) (l : String) : Option String :=
  let rest := if l.startsWith "private " then l.drop 8 |>.toString else l
  let afterKw :=
    if rest.startsWith "lemma " then some (rest.drop 6 |>.toString)
    else if rest.startsWith "theorem " then some (rest.drop 8 |>.toString)
    else none
  afterKw.bind fun r =>
    let cs := r.toList
    match cs with
    | c :: _ =>
      if c.isAlpha || c == '_' then
        some (String.ofList (cs.takeWhile fun ch =>
          ch.isAlphanum || ch == '_' || ch == '\'' || ch == '!' || ch == '?' || (allowDot && ch == '.')))
      else none
    | [] => none

/-- `{name: first line}` over the file. -/
def declLines (allowDot : Bool) (lines : Array String) : List (String × Nat) :=
  (lines.toList.zipIdx).foldl (init := []) fun acc (l, i) =>
    match declHead? allowDot l with
    | some nm => if acc.any (·.1 == nm) then acc else acc ++ [(nm, i)]
    | none => acc

def lookup (at_ : List (String × Nat)) (k : String) : Option Nat :=
  (at_.find? (·.1 == k)).map (·.2)

/-- A `.lean:LINE:COL: ` location at or after column `i`. -/
partial def hasErrorLoc (a : Array Char) (i : Nat) : Bool :=
  match findSub a (chars ".lean:") i with
  | none => false
  | some p =>
    let j := p + 6
    let d1 := (a.extract j a.size).toList.takeWhile Char.isDigit |>.length
    if d1 > 0 && j + d1 < a.size && a[j + d1]! == ':' then
      let k := j + d1 + 1
      let d2 := (a.extract k a.size).toList.takeWhile Char.isDigit |>.length
      if d2 > 0 && k + d2 + 1 < a.size && a[k + d2]! == ':' && a[k + d2 + 1]! == ' ' then true
      else hasErrorLoc a (p + 1)
    else hasErrorLoc a (p + 1)

/-- `^error: .*\.lean:\d+:\d+: ` — a Lake-rendered Lean diagnostic. -/
def isErrorLine (l : String) : Bool :=
  l.startsWith "error: " && hasErrorLoc (chars l) 0

/-- Python's `f"{s:<w}"`. -/
def padRight (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - s.length) ' ')
/-- Python's `f"{n:>w}"`. -/
def padLeft (s : String) (w : Nat) : String := String.ofList (List.replicate (w - s.length) ' ') ++ s

#guard stripComment "a ∨ True -- comment -- more" == "a ∨ True "
#guard stripComment "no comment" == "no comment"
#guard rstrip "  x := by  \t" == "  x := by"
#guard strip "  x := by  \t" == "x := by"
#guard collapseWs "  a   b\n c " == "a b c"
#guard findSub (chars "ab(h : X)") (chars "(h : ") == some 2
#guard rfindSub (chars "x ∨ True ∨ True") (chars "∨ True") == some 9
#guard countSub "∨ True, ∨ True ∨ Truex" "∨ True" == 3
#guard declHead? false "lemma foo_bar' (x : Nat)" == some "foo_bar'"
#guard declHead? false "private theorem IndentFloor.transport :" == some "IndentFloor"
#guard declHead? true "private theorem IndentFloor.transport :" == some "IndentFloor.transport"
#guard declHead? false "lemma (x : Nat)" == none
#guard declHead? false "  lemma indented" == none
#guard declLines false #["lemma a", "def b", "lemma a", "lemma c"] == [("a", 0), ("c", 3)]
#guard isErrorLine "error: ./././L4YAML/Proofs/Production/StreamAccum.lean:12:3: unsolved goals" == true
#guard isErrorLine "error: Lean exited with code 1" == false
#guard isErrorLine "L4YAML/Foo.lean:12:3: error: x" == false
#guard isErrorLine "error: foo.lean:1:2:x" == false
#guard padRight "ab" 4 == "ab  "
#guard padLeft "7" 4 == "   7"

end

end Scripts.Restate
