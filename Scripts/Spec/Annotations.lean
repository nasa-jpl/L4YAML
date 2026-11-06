module

public import Scripts.Restate.Text
meta import Scripts.Restate.Text

/-!
# `Scripts.Spec.Annotations` — `@[yaml_spec]` references against `yaml-spec-1.2.yaml`
(was `scripts/verify_yaml_spec_annotations.py`)

The grammar file (yaml/yaml-grammar) names every production of YAML 1.2 as `:NNN: name`;
the library's `@[yaml_spec "section" NNN "name"]` attributes cite them.  This module is
the pure half of the check: the spec's `number → name` table (`^:(\d{3}):\s+(\S+)`), the
Python's name normalisation (`s-indent(≤n)` / `s-indent(<n)` are the spec's `s-indent-le` /
`-lt`; the spec's `seq-spaces` is the YAML 1.2.2 text's `seq-space`; parameter lists
stripped), and the three diagnostics — NAME MISMATCHES, UNKNOWN RULES, COVERAGE — worded
as the Python printed them.  The references themselves come from the environment
(`Scripts.Spec.Env`: the `yamlSpecExt` entries of the built `.olean`s), not from the text
the Python scanned; a diagnostic names the declaration carrying the reference.
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

/-- One `@[yaml_spec …]` reference: the module's source file (relative to the checkout), the
    declaration it is attached to and the line that declaration's name is on (none when the
    module only annotated a declaration of another module), and the reference's fields. -/
structure Annotation where
  file : String
  decl : String
  line : Option Nat
  section_ : String
  ruleNum : Option Nat
  ruleName : Option String
  deriving Repr, BEq

/-- Where a diagnostic points: `file:line decl`, or `file decl` without a line. -/
def Annotation.at (a : Annotation) : String :=
  match a.line with
  | some l => s!"{a.file}:{l} {a.decl}"
  | none => s!"{a.file} {a.decl}"

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
      unknown := unknown ++ [s!"  [{pad3 num}] \"{ann.ruleName.getD "None"}\" — not in spec (1–{maxRule})  @ {ann.at}"]
    | some sn =>
      unless covered.contains num do covered := covered ++ [num]
      if let some ln := ann.ruleName then
        unless namesMatch ln sn do
          mismatches := mismatches ++ [s!"  [{pad3 num}] lean=\"{ln}\"  spec=\"{sn}\"  @ {ann.at}"]
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
#guard normaliseLeanName "s-indent(n)" == "s-indent"
#guard normaliseLeanName "c-l+block-map(n)(x)" == "c-l+block-map"
#guard normaliseLeanName "a(b)c" == "a(b)c"
#guard namesMatch "s-indent(≤n)" "s-indent-le" && namesMatch "s-indent(<n)" "s-indent-lt"
#guard namesMatch "seq-space(n,c)" "seq-spaces" && namesMatch "s-indent(≤n)" "s-indent" && !namesMatch "s-indent(≤n)" "s-indent-lt" && !namesMatch "x(n)" "y"
#guard pct1 211 211 == "100.0" && pct1 1 3 == "33.3" && pct1 2 3 == "66.7" && pct1 1 8 == "12.5" && pct1 0 5 == "0.0"
#guard (Annotation.at { file := "f", decl := "T.x", line := some 2, section_ := "s", ruleNum := none, ruleName := none }) == "f:2 T.x"
#guard (Annotation.at { file := "f", decl := "T.x", line := none, section_ := "s", ruleNum := none, ruleName := none }) == "f T.x"
#guard (verify #[(1, "a"), (2, "b")] [{ file := "f", decl := "x", line := some 2, section_ := "s", ruleNum := some 1, ruleName := some "a(n)" },
    { file := "f", decl := "y", line := some 4, section_ := "s", ruleNum := some 9, ruleName := some "z" },
    { file := "g", decl := "T.c", line := none, section_ := "s", ruleNum := some 2, ruleName := some "bb" }]).mismatches
  == ["  [  2] lean=\"bb\"  spec=\"b\"  @ g T.c"]
#guard (verify #[(1, "a"), (2, "b")] [{ file := "f", decl := "y", line := some 4, section_ := "s", ruleNum := some 9, ruleName := some "z" }]).unknown
  == ["  [  9] \"z\" — not in spec (1–2)  @ f:4 y"]
#guard (verify #[(1, "a"), (2, "b")] [{ file := "f", decl := "y", line := some 4, section_ := "s", ruleNum := some 2, ruleName := none }]).uncovered
  == ["  [  1] a"]

end

end Scripts.Spec
