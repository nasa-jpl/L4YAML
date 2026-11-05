module

public import Scripts.Restate.Text
meta import Scripts.Restate.Text

/-!
# `Scripts.Spec.Annotations` — `@[yaml_spec]` annotations against `yaml-spec-1.2.yaml`
(was `scripts/verify_yaml_spec_annotations.py`)

The grammar file (yaml/yaml-grammar) names every production of YAML 1.2 as `:NNN: name`;
the library's `@[yaml_spec "section" NNN "name"]` attributes cite them.  This module is
the pure half of the check: the spec's `number → name` table (`^:(\d{3}):\s+(\S+)`), the
annotations of a Lean line (`yaml_spec\s+"…"(?:\s+(\d+)\s+"…")?`), the Python's name
normalisation (`s-indent(≤n)` / `s-indent(<n)` are the spec's `s-indent-le` / `-lt`; the
spec's `seq-spaces` is the YAML 1.2.2 text's `seq-space`; parameter lists stripped), and
the three diagnostics — NAME MISMATCHES, UNKNOWN RULES, COVERAGE — worded as the Python
printed them.
-/

namespace Scripts.Spec

open Scripts.Restate (chars findSub padLeft)

@[expose] public section

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == '\x0b'

/-- `:NNN: name` at the start of a line → `(NNN, name)`. -/
def specRule? (line : String) : Option (Nat × String) :=
  let cs := line.toList
  match cs with
  | ':' :: a :: b :: c :: ':' :: rest =>
    if a.isDigit && b.isDigit && c.isDigit then
      let afterWs := rest.dropWhile isWs
      if afterWs.length < rest.length && !afterWs.isEmpty then
        some (String.toNat! (String.ofList [a, b, c]), String.ofList (afterWs.takeWhile (!isWs ·)))
      else none
    else none
  | _ => none

/-- `parse_spec`: the table, later rows winning. -/
def parseSpec (text : String) : Array (Nat × String) :=
  (text.splitOn "\n").foldl (init := #[]) fun acc l =>
    match specRule? l with
    | some (n, name) =>
      if acc.any (·.1 == n) then acc.map (fun r => if r.1 == n then (n, name) else r) else acc.push (n, name)
    | none => acc

def specName? (spec : Array (Nat × String)) (n : Nat) : Option String :=
  (spec.find? (·.1 == n)).map (·.2)

structure Annotation where
  file : String
  line : Nat
  section_ : String
  ruleNum : Option Nat
  ruleName : Option String
  deriving Repr, BEq

/-- `LEAN_ANNOT_RE.finditer(line)`: every `yaml_spec "S"` with its optional `N "name"`. -/
partial def annotationsOfLine (file : String) (lineNo : Nat) (line : String) : List Annotation :=
  go (chars line) 0 []
where
  quoted (a : Array Char) (i : Nat) : Option (String × Nat) :=
    if i < a.size && a[i]! == '"' then
      let j := (List.range (a.size - i - 1)).find? (fun k => a[i + 1 + k]! == '"') |>.map (· + i + 1)
      match j with
      | some j => if j > i + 1 then some (String.ofList (a.extract (i + 1) j).toList, j + 1) else none
      | none => none
    else none
  skipWs (a : Array Char) (i : Nat) : Nat :=
    if i < a.size && isWs a[i]! then skipWs a (i + 1) else i
  go (a : Array Char) (i : Nat) (acc : List Annotation) : List Annotation :=
    match findSub a (chars "yaml_spec") i with
    | none => acc.reverse
    | some p =>
      let q := skipWs a (p + 9)
      if q == p + 9 then go a (p + 1) acc else
      match quoted a q with
      | none => go a (p + 1) acc
      | some (sec, e) =>
        let r := skipWs a e
        let digitsEnd := (List.range (a.size - r)).find? (fun k => !(a[r + k]!).isDigit) |>.map (· + r) |>.getD a.size
        let opt :=
          if r > e && digitsEnd > r then
            let s := skipWs a digitsEnd
            if s > digitsEnd then
              match quoted a s with
              | some (name, e2) => some (String.toNat! (String.ofList (a.extract r digitsEnd).toList), name, e2)
              | none => none
            else none
          else none
        match opt with
        | some (n, name, e2) => go a e2 ({ file, line := lineNo, section_ := sec, ruleNum := some n, ruleName := some name } :: acc)
        | none => go a e ({ file, line := lineNo, section_ := sec, ruleNum := none, ruleName := none } :: acc)

/-- `re.sub(r"\(.*\)$", "", name)`: from the first `(` to a `)` that ends the name. -/
def normaliseLeanName (name : String) : String :=
  if name.endsWith ")" then
    match name.toList.findIdx? (· == '(') with
    | some i => String.ofList (name.toList.take i)
    | none => name
  else name

def namesMatch (leanName specName : String) : Bool :=
  let ln := normaliseLeanName leanName
  if ln == specName then true
  else if leanName == "s-indent(≤n)" then specName == "s-indent-le"
  else if leanName == "s-indent(<n)" then specName == "s-indent-lt"
  else if specName == "seq-spaces" then ln == "seq-space"
  else false

/-- Python's `f"{n:3d}"`. -/
def pad3 (n : Nat) : String := padLeft (toString n) 3

structure Report where
  mismatches : List String
  unknown : List String
  uncovered : List String
  deriving Repr

def verify (spec : Array (Nat × String)) (anns : List Annotation) : Report := Id.run do
  let maxRule := spec.foldl (fun m r => max m r.1) 0
  let mut mismatches := []
  let mut unknown := []
  let mut covered : List Nat := []
  for ann in anns do
    let some num := ann.ruleNum | continue
    match specName? spec num with
    | none =>
      unknown := unknown ++ [s!"  [{pad3 num}] \"{ann.ruleName.getD "None"}\" — not in spec (1–{maxRule})  @ {ann.file}:{ann.line}"]
    | some sn =>
      unless covered.contains num do covered := covered ++ [num]
      if let some ln := ann.ruleName then
        unless namesMatch ln sn do
          mismatches := mismatches ++ [s!"  [{pad3 num}] lean=\"{ln}\"  spec=\"{sn}\"  @ {ann.file}:{ann.line}"]
  let sorted := (spec.toList.map (·.1)).mergeSort (· ≤ ·)
  let uncovered := sorted.filterMap fun n =>
    if covered.contains n then none else some s!"  [{pad3 n}] {(specName? spec n).getD ""}"
  return { mismatches, unknown, uncovered }

/-- `f"{u / n * 100:.1f}"` on the exact ratio, half to even. -/
def pct1 (u n : Nat) : String :=
  if n == 0 then "0.0" else
  let num := u * 1000
  let q := num / n
  let r := num % n
  let tenths := if 2 * r > n || (2 * r == n && q % 2 == 1) then q + 1 else q
  s!"{tenths / 10}.{tenths % 10}"

#guard specRule? ":063: s-indent" == some (63, "s-indent")
#guard specRule? ":063:s-indent" == none
#guard specRule? "  :063: s-indent" == none
#guard specRule? ":63: x" == none
#guard parseSpec ":001: a\n:002: b\n#:003: c\n:001: a2\n" == #[(1, "a2"), (2, "b")]
#guard annotationsOfLine "f" 3 "@[yaml_spec \"5.4\" 24 \"b-line-feed\"] def x" ==
  [{ file := "f", line := 3, section_ := "5.4", ruleNum := some 24, ruleName := some "b-line-feed" }]
#guard annotationsOfLine "f" 1 "yaml_spec \"8.1\" -- yaml_spec \"8.2\" 007 \"c\"" ==
  [{ file := "f", line := 1, section_ := "8.1", ruleNum := none, ruleName := none },
   { file := "f", line := 1, section_ := "8.2", ruleNum := some 7, ruleName := some "c" }]
#guard annotationsOfLine "f" 1 "yaml_spec \"8.1\" 12 x" ==
  [{ file := "f", line := 1, section_ := "8.1", ruleNum := none, ruleName := none }]
#guard annotationsOfLine "f" 1 "yaml_spec\"8.1\"" == []
#guard normaliseLeanName "s-indent(n)" == "s-indent"
#guard normaliseLeanName "c-l+block-map(n)(x)" == "c-l+block-map"
#guard normaliseLeanName "a(b)c" == "a(b)c"
#guard namesMatch "s-indent(≤n)" "s-indent-le" && namesMatch "s-indent(<n)" "s-indent-lt"
#guard namesMatch "seq-space(n,c)" "seq-spaces" && namesMatch "s-indent(≤n)" "s-indent" && !namesMatch "s-indent(≤n)" "s-indent-lt" && !namesMatch "x(n)" "y"
#guard pct1 211 211 == "100.0" && pct1 1 3 == "33.3" && pct1 2 3 == "66.7" && pct1 1 8 == "12.5" && pct1 0 5 == "0.0"
#guard (verify #[(1, "a"), (2, "b")] [{ file := "f", line := 2, section_ := "s", ruleNum := some 1, ruleName := some "a(n)" },
    { file := "f", line := 4, section_ := "s", ruleNum := some 9, ruleName := some "z" },
    { file := "g", line := 1, section_ := "s", ruleNum := some 2, ruleName := some "bb" }]).mismatches
  == ["  [  2] lean=\"bb\"  spec=\"b\"  @ g:1"]
#guard (verify #[(1, "a"), (2, "b")] [{ file := "f", line := 4, section_ := "s", ruleNum := some 9, ruleName := some "z" }]).unknown
  == ["  [  9] \"z\" — not in spec (1–2)  @ f:4"]
#guard (verify #[(1, "a"), (2, "b")] [{ file := "f", line := 4, section_ := "s", ruleNum := some 2, ruleName := none }]).uncovered
  == ["  [  1] a"]

end

end Scripts.Spec
