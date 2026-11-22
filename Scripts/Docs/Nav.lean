module

public import Scripts.Docs.ClosureLog
public import Scripts.Lean.Regex
meta import Scripts.Docs.ClosureLog
meta import Scripts.Lean.Regex

@[expose] public section Blanket

/-!
# Scripts.Docs.Nav — navigate DOCS.md without paging it (the pure half of `docs-nav`)

Formerly `scripts/docs_nav.py`.  `DOCS.md` is a 45k-line consolidated history;
the Row 12 closure log alone holds hundreds of dated items.  These functions
compute the slices `lake run docs-nav -- <cmd>` prints: the item index (every
`### Item N[a] (YYYY-MM-DD)` heading, each item ending at the next heading, at
`### REMAINING, in order`, or at the next document-level `## ` section), the
headline of an item (first sentence of its opening bold paragraph), the
`**NEXT —` mandate paragraph with the list paragraphs that continue it, the
six-step table rows, and the `## ` sections.  Line numbers are 1-based and
match `sed -n`.  Output text is the Python's, byte for byte.
-/

namespace Scripts.Docs.Nav

open Scripts.Lean

def remainingHeading : String := "### REMAINING, in order"
def nextActionsHeading : String := "### Next actions, in order"
def sixStepsHeading : String := "#### Row 12 — the six steps that finish it"

structure Item where
  number : Nat
  suffix : String
  date : String
  start : Nat      -- 1-based line of the heading
  end_ : Nat       -- exclusive, 1-based
  deriving Repr, BEq, Inhabited

def Item.label (it : Item) : String := s!"{it.number}{it.suffix}"

/-- Lines `start … end_-1` (1-based), the heading included. -/
def Item.body (it : Item) (lines : Array String) : Array String :=
  lines.extract (it.start - 1) (it.end_ - 1)

def rstrip (s : String) : String := String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse
def strip (s : String) : String := s.trimAscii.toString

/-- `^### Item (\d+)([a-z]?) \((\d{4}-\d{2}-\d{2})\)\s*$` — single spaces, unlike the
gate's looser heading parser. -/
def itemHeading? (line : String) : Option (Nat × String × String) := do
  let (n, letter, rest) ← ClosureLog.parseHeading line
  guard (line.startsWith s!"### Item {n}{letter} (")
  let d ← ClosureLog.dateOf rest
  guard (rest == s!" ({d})" || (rest.startsWith s!" ({d})" && (strip ((rest.drop (d.length + 3)).toString)).isEmpty))
  pure (n, letter, d)

/-- `^## (?!§)(.+?)\s*$`: a document-level section heading (`## §n` live inside items). -/
def isDocH2 (line : String) : Bool :=
  line.startsWith "## " && !(line.startsWith "## §") && !(strip (line.drop 3).toString).isEmpty

/-- `^## (.+?)\s*$` → the title, stripped. -/
def anyH2? (line : String) : Option String :=
  if line.startsWith "## " then
    let t := rstrip (line.drop 3).toString
    if t.isEmpty then none else some t
  else none

def findItems (lines : Array String) : Array Item := Id.run do
  let mut items : Array Item := #[]
  for h : i in [0:lines.size] do
    if let some (n, letter, d) := itemHeading? lines[i] then
      items := items.push { number := n, suffix := letter, date := d, start := i + 1, end_ := lines.size + 1 }
  for i in [0:items.size] do
    if i + 1 < items.size then
      items := items.modify i fun it => { it with end_ := items[i+1]!.start }
  for i in [0:items.size] do
    let it := items[i]!
    let mut e := it.end_
    for j in [it.start:it.end_ - 1] do
      let l := lines[j]!
      if l == remainingHeading || isDocH2 l then e := j + 1; break
    items := items.set! i { it with end_ := e }
  return items

def collapseWs (s : String) : String :=
  " ".intercalate ((s.splitOn " ").filter (· != "")) |> fun t =>
    " ".intercalate ((t.replace "\t" " " |>.replace "\n" " " |>.splitOn " ").filter (· != ""))

/-- Python: truncate to `width` chars with `…`. -/
def truncate (s : String) (width : Nat) : String :=
  if s.length ≤ width then s else String.ofList (s.toList.take (width - 1)) ++ "…"

/-- First sentence of the item's opening bold paragraph. -/
def headline (lines : Array String) (it : Item) (width : Nat) : String := Id.run do
  let mut para : Array String := #[]
  for line in (it.body lines).extract 1 (it.body lines).size do
    if (strip line).isEmpty then
      if !para.isEmpty then break
    else para := para.push (strip line)
  let text := " ".intercalate para.toList
  let text := if text.startsWith "**" then
      let inner := (text.drop 2).toString
      match (inner.splitOn "**") with
      | first :: _ :: _ => first
      | _ => text
    else text
  return truncate (collapseWs text) width

def paragraphs (block : Array String) : Array (Array String) := Id.run do
  let mut out : Array (Array String) := #[]
  let mut cur : Array String := #[]
  for line in block do
    if !(strip line).isEmpty then cur := cur.push line
    else if !cur.isEmpty then out := out.push cur; cur := #[]
  if !cur.isEmpty then out := out.push cur
  return out

/-- `^\*\*NEXT\b` -/
def isNextPara (l : String) : Bool :=
  l.startsWith "**NEXT" && !((l.drop 6).toString.toList.headD ' ' |> fun c => c.isAlphanum || c == '_')

def isMandatePara (l : String) : Bool :=
  l.startsWith "**The mandate" && !((l.drop 13).toString.toList.headD ' ' |> fun c => c.isAlphanum || c == '_')

/-- `^\s*(?:[-*•]|\d+[.)])\s` -/
def isListLine (l : String) : Bool :=
  let cs := l.toList.dropWhile Char.isWhitespace
  match cs with
  | c :: d :: _ => if c == '-' || c == '*' || c == '•' then d.isWhitespace else
      let ds := cs.takeWhile Char.isDigit
      !ds.isEmpty && (match cs.drop ds.length with | p :: w :: _ => (p == '.' || p == ')') && w.isWhitespace | _ => false)
  | _ => false

/-- The `**NEXT` paragraph with the list paragraphs that continue it. -/
def nextParagraph (lines : Array String) (it : Item) : Option (Array String) := Id.run do
  let paras := paragraphs (it.body lines)
  for k in [0:paras.size] do
    let para := paras[k]!
    if isNextPara para[0]! then
      let mut out := para
      for cont in paras.extract (k + 1) paras.size do
        if !isListLine cont[0]! then break
        out := out.push ""
        out := out ++ cont
      return some out
  return none

def mandateParagraph (lines : Array String) (it : Item) : Option (Array String) :=
  (paragraphs (it.body lines)).find? fun p => isMandatePara p[0]!

/-- Lines `start … end-1`, numbered as `i:line` when asked. -/
def emit (lines : Array String) (start end_ : Nat) (numbered : Bool) : Array String :=
  (List.range (end_ - start)).toArray.map fun k =>
    let i := start + k
    if numbered then s!"{i}:{lines[i-1]!}" else lines[i-1]!

def lookup (items : Array Item) (label : String) : Except String Item :=
  match items.find? (·.label == label) with
  | some it => .ok it
  | none => .error s!"no item {label} (have {items[0]!.label}–{items[items.size-1]!.label})"

/-- `[start, end)` of the block beginning at the exact `heading` line. -/
def headingBlock (lines : Array String) (heading : String) (stop : String → Bool) : Except String (Nat × Nat) := do
  let some idx := lines.findIdx? (· == heading) | throw s!"heading not found: '{heading}'"
  let start := idx + 1
  let mut e := lines.size + 1
  for i in [start:lines.size] do
    if stop lines[i]! then e := i + 1; break
  return (start, e)

def padLeft (s : String) (w : Nat) : String := String.ofList (List.replicate (w - s.length) ' ') ++ s
def padRight (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - s.length) ' ')

def cmdToc (lines : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [0:lines.size] do
    let l := lines[i]!
    if isDocH2 l || l == remainingHeading || l == nextActionsHeading || l == sixStepsHeading then
      out := out.push s!"{padLeft (toString (i+1)) 6}  {l}"
  let items := findItems lines
  if !items.isEmpty then
    let f := items[0]!; let la := items[items.size-1]!
    out := out.push s!"        ({items.size} closure-log items, {f.label}–{la.label}, lines {f.start}–{la.end_ - 1})"
  return out

def itemLine (lines : Array String) (it : Item) (width : Nat) : String :=
  s!"{padLeft it.label 5}  {it.date}  L{padRight (toString it.start) 6} {headline lines it width}"

def cmdItems (lines : Array String) (since last : Option Nat) (width : Nat) : Array String :=
  let items := findItems lines
  let items := match since with | some n => items.filter (fun it : Item => it.number ≥ n) | none => items
  let items := match last with | some k => items.extract (items.size - min k items.size) items.size | none => items
  items.map (itemLine lines · width)

def cmdNext (lines : Array String) (n : Option String) : Except String (Array String) := do
  let items := findItems lines
  let it ← match n with | none => pure items[items.size-1]! | some l => lookup items l
  let mut out := #[s!"# item {it.label} ({it.date}), DOCS.md:{it.start}"]
  if let some para := nextParagraph lines it then return out ++ para
  out := out.push s!"(item {it.label} records no **NEXT —** paragraph; older items state what came next in prose)"
  let idx := (items.findIdx? (· == it)).getD 0
  if idx + 1 < items.size then
    let f := items[idx+1]!
    if let some m := mandateParagraph lines f then
      return out.push s!"# what item {f.label} ({f.date}, DOCS.md:{f.start}) took as its mandate:" ++ m
    return out.push s!"# read `item {it.label}` and the opening of `item {f.label}` (DOCS.md:{f.start})"
  return out.push s!"# read `item {it.label}`"

/-- `^\| \*\*(12(?:\.\d+)*)\*\* \| ` → the step -/
def stepOf? (l : String) : Option String := do
  guard (l.startsWith "| **12")
  let rest := (l.drop 4).toString.toList
  let step := rest.takeWhile fun c => c.isDigit || c == '.'
  guard (step.head? == some '1')
  let s := String.ofList step
  guard (((s.splitOn ".").all fun p => !p.isEmpty && p.all Char.isDigit) && (s.splitOn ".").head! == "12")
  guard ((String.ofList (rest.drop step.length)).startsWith "** | ")
  pure s

/-- `(line, step, state, what)` for every row of the six-step table. -/
def stepRows (lines : Array String) : Except String (Array (Nat × String × String × String)) := do
  let (start, e) ← headingBlock lines sixStepsHeading (·.startsWith "#")
  let mut rows := #[]
  for i in [start:e-1] do
    let l := lines[i]!
    if let some step := stepOf? l then
      let inner := strip l
      let inner := (if inner.startsWith "|" then (inner.drop 1).toString else inner)
      let inner := (if inner.endsWith "|" then (inner.dropEnd 1).toString else inner)
      let cells := (inner.splitOn " | ").map strip
      if cells.length ≥ 3 then rows := rows.push (i + 1, step, cells[2]!, cells[1]!)
  return rows

def boldHead? (s : String) : Option String :=
  if s.startsWith "**" then
    match ((s.drop 2).toString.splitOn "**") with
    | first :: _ :: _ => some first
    | _ => none
  else none

def cmdRemaining (lines : Array String) (numbered : Bool) (width : Nat) : Except String (Array String) := do
  let items := findItems lines
  let rows ← stepRows lines
  let openRows := rows.filter fun (_, _, state, _) => !state.startsWith "✅"
  let tableLine := ((lines.findIdx? (· == sixStepsHeading)).getD 0) + 1
  let mut out := #[s!"# open steps of Row 12 (the six-step table, DOCS.md:{tableLine}; `steps` prints it whole):"]
  for (_, step, state, what) in openRows do
    out := out.push s!"{padLeft step 8}  {String.ofList (state.toList.take width)}"
    out := out.push s!"          {match boldHead? what with | some h => h | none => String.ofList (what.toList.take width)}"
  if openRows.isEmpty then out := out.push "          (every row is ✅ done)"
  let la := items[items.size-1]!
  out := out.push s!"# latest mandate: `next` (item {la.label}, {la.date})"
  let (s1, e1) ← headingBlock lines nextActionsHeading (·.startsWith "#")
  out := out.push s!"# what blocks what today (DOCS.md:{s1}):"
  out := out ++ emit lines s1 e1 numbered
  let (s2, e2) ← headingBlock lines remainingHeading fun l => (itemHeading? l).isSome || isDocH2 l
  let before := items.filter (·.start < s2)
  let after := items.filter (·.start > s2)
  let mut where_ := s!"DOCS.md:{s2}"
  if !before.isEmpty && !after.isEmpty then
    where_ := where_ ++ s!", written between items {before[before.size-1]!.label} and {after[0]!.label} ({after[0]!.date})"
  out := out.push s!"# the dependency chain, as recorded at {where_};"
  out := out.push "# its item ranges stop there — the rows above are the current state:"
  return out ++ emit lines s2 e2 numbered

def cmdSteps (lines : Array String) (numbered : Bool) : Except String (Array String) := do
  let mut out := #[]
  for h in [nextActionsHeading, sixStepsHeading] do
    let (s, e) ← headingBlock lines h (·.startsWith "#")
    out := out ++ emit lines s e numbered
  return out

/-- `(stdout lines, total matching lines)` -/
def cmdGrep (lines : Array String) (rx : List (List Regex.Node)) (icase : Bool) (width : Nat) : Array String × Nat := Id.run do
  let mut out := #[]
  let mut total := 0
  for it in findItems lines do
    let hits := ((it.body lines).filter (Regex.search rx · icase)).size
    if hits > 0 then
      total := total + hits
      out := out.push s!"{padLeft it.label 5}  {it.date}  L{padRight (toString it.start) 6} {padLeft (toString hits) 3}  {headline lines it width}"
  return (out, total)

def cmdSection (lines : Array String) (prefix_ : String) (numbered : Bool) : Except String (Array String) := do
  let want := prefix_.toLower
  for i in [0:lines.size] do
    if let some title := anyH2? lines[i]! then
      if title.toLower.startsWith want then
        let mut e := lines.size + 1
        for j in [i+1:lines.size] do
          if lines[j]!.startsWith "# " || lines[j]!.startsWith "## " then e := j + 1; break
        return emit lines (i + 1) e numbered
  throw s!"no `## ` section starts with '{prefix_}'; see `toc`"

#guard itemHeading? "### Item 419 (2026-10-31)" == some (419, "", "2026-10-31")
#guard itemHeading? "### Item 67a (2026-09-01)  " == some (67, "a", "2026-09-01")
#guard itemHeading? "###  Item 419 (2026-10-31)" == none && itemHeading? "### Item 419 — x (2026-10-31)" == none
#guard isDocH2 "## Contents" && !isDocH2 "## §3 Gates" && !isDocH2 "### x" && !isDocH2 "## "
#guard isListLine "  - a" && isListLine "1. a" && isListLine "12) b" && !isListLine "-a" && !isListLine "1 a" && isListLine "• x"
#guard isNextPara "**NEXT —** x" && !isNextPara "**NEXTS" && isMandatePara "**The mandate.**"
#guard stepOf? "| **12.3.3** | what | ✅ done |" == some "12.3.3" && stepOf? "| **13** | x | y |" == none && stepOf? "| **12** | x |" == some "12"
private def doc : Array String := #["# T", "", "## Contents", "x", "## Row 12", "### Item 1 (2026-01-01)", "", "**First.** More", "", "**NEXT —** do it", "", "- a", "- b", "", "prose", "### Item 2 (2026-01-02)", "", "**Second** sentence", "## After", "tail"]
#guard (findItems doc).map (fun it => (it.label, it.start, it.end_)) == #[("1", 6, 16), ("2", 16, 19)]
#guard headline doc (findItems doc)[0]! 100 == "First." && headline doc (findItems doc)[1]! 4 == "Sec…"
#guard nextParagraph doc (findItems doc)[0]! == some #["**NEXT —** do it", "", "- a", "- b"]
#guard cmdToc doc == #["     3  ## Contents", "     5  ## Row 12", "    19  ## After", "        (2 closure-log items, 1–2, lines 6–18)"]
#guard cmdItems doc none (some 1) 100 == #["    2  2026-01-02  L16     Second"]
#guard (cmdSection doc "row" false).toOption == some #["## Row 12", "### Item 1 (2026-01-01)", "", "**First.** More", "", "**NEXT —** do it", "", "- a", "- b", "", "prose", "### Item 2 (2026-01-02)", "", "**Second** sentence"]
#guard (cmdNext doc (some "2")).toOption == some #["# item 2 (2026-01-02), DOCS.md:16", "(item 2 records no **NEXT —** paragraph; older items state what came next in prose)", "# read `item 2`"]
#guard (cmdGrep doc (Regex.compile "a").toOption.get! false 100).2 == 1 && (cmdGrep doc (Regex.compile "[A-Z]").toOption.get! false 100).2 == 5

end Scripts.Docs.Nav
