module

@[expose] public section Blanket

/-!
# Scripts.Docs.ClosureLog — the β.5 closure log's item index

`DOCS.md`'s "Row 12 — β.5 closure log" is a flat run of `### Item N (DATE)`
entries that readers and later entries navigate by number.  This module is
the item parser both the gate (`scripts-check-closure-log`, formerly
`scripts/check_closure_log.py`) and, when it is ported, `docs_nav.py` read
the log through, and the gate's five checks as pure functions over the parsed
entries (each a hard failure):

1. headings parse — every `### Item N …` heading carries a number and a
   trailing `(YYYY-MM-DD)` date;
2. numbers ascend strictly by `(number, letter)` (`Item 67a` orders after
   `Item 67`); a repeated key is two entries claiming one item;
3. dates do not regress;
4. gaps are declared — a missing number is in `declaredGaps` with an anchor
   that resolves to a real heading of `DOCS.md`;
5. the declaration does not rot — every declared gap is still absent and
   inside the log's range.

The messages are the Python gate's, byte for byte, so the two readings diff
empty on the same `DOCS.md`.
-/

namespace Scripts.Docs.ClosureLog

/-- Item numbers with no `### Item N` entry in the closure log, each mapped
to the `DOCS.md` anchor that documents it instead.  A runtime-repair item is
written up under the defect it fixed, not as a closure-log row.
(Row 12 step 1, the frame-list retyping, is written up on its own branch;
drop its row when that entry lands.) -/
def declaredGaps : List (Nat × String) :=
  [(18, "surrogate-hex-escapes-decoded-to-nul")]

/-- One `### Item N[a] (DATE)` heading. -/
structure Entry where
  line : Nat
  number : Nat
  letter : String
  date : String
  deriving Repr, BEq, Inhabited

def Entry.key (e : Entry) : Nat × String := (e.number, e.letter)
def Entry.name (e : Entry) : String := s!"{e.number}{e.letter}"

/-- `(number, letter)` order: `67 < 67a < 68`. -/
def keyLt (a b : Nat × String) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def isDigit (c : Char) : Bool := c.isDigit

/-- `###` + spaces + `Item` + spaces + digits + optional lowercase letter + word
boundary; returns `(number, letter, rest)`.  Python: `^###\s+Item\s+(\d+)([a-z]?)\b(.*)$`. -/
def parseHeading (line : String) : Option (Nat × String × String) := do
  let cs := line.toList
  guard (cs.take 3 == ['#', '#', '#'])
  let cs := cs.drop 3
  guard (cs.headD ' ' |>.isWhitespace)
  let cs := cs.dropWhile Char.isWhitespace
  guard (cs.take 4 == "Item".toList)
  let cs := cs.drop 4
  guard (cs.headD ' ' |>.isWhitespace)
  let cs := cs.dropWhile Char.isWhitespace
  let digits := cs.takeWhile isDigit
  guard (!digits.isEmpty)
  let cs := cs.drop digits.length
  let (letter, cs) :=
    match cs with
    | c :: rest => if c.isLower && c.isAlpha then ([c], rest) else ([], cs)
    | [] => ([], [])
  -- `\b`: the char after the match must not be a word char (or there is none)
  guard (cs.head?.all fun c => !(c.isAlphanum || c == '_'))
  pure (String.toNat! (String.ofList digits), String.ofList letter, String.ofList cs)

/-- Python: `\((\d{4}-\d{2}-\d{2})\)\s*$` on the heading's rest. -/
def dateOf (rest : String) : Option String :=
  let t := rest.toList.reverse.dropWhile Char.isWhitespace |>.reverse
  let n := t.length
  if n < 12 then none else
  let tail := t.drop (n - 12)
  let inner := (tail.drop 1).take 10
  let shape := ((List.range 10).zip inner).all fun (i, c) => if i == 4 || i == 7 then c == '-' else c.isDigit
  if t.getD (n - 12) ' ' == '(' && t.getLast? == some ')' && shape
  then some (String.ofList inner) else none

/-- Python's `\w` (Unicode word character), approximated without a Unicode
database: ASCII alphanumerics and `_`, plus every non-ASCII code point outside
the punctuation and symbol blocks that occur in this repository's headings
(Latin-1 symbols U+0080–U+00BF, `×` `÷`, General Punctuation through
Miscellaneous Symbols and Arrows U+2000–U+2BFF, CJK punctuation U+3000–U+303F).
So `β` is a word character and `—`, `§`, `→` are not, as in Python. -/
def isWordChar (c : Char) : Bool :=
  let v := c.val
  if v < 0x80 then c.isAlphanum || c == '_'
  else !(v ≤ 0xBF || v == 0xD7 || v == 0xF7 || (0x2000 ≤ v && v ≤ 0x2BFF) || (0x3000 ≤ v && v ≤ 0x303F))

/-- GitHub's heading-anchor slug: lowercase, punctuation dropped, spaces to `-`.
Python: `re.sub(r"[^\w\s-]", "", title.strip().lower()).replace(" ", "-")`
(`.lower()` is ASCII here; the headings this gate resolves are ASCII). -/
def slug (title : String) : String :=
  let t := title.trimAscii.toString.toLower
  String.ofList <| t.toList.filterMap fun c =>
    if c == ' ' then some '-'
    else if isWordChar c || c.isWhitespace || c == '-' then some c
    else none

/-- Anchors of every `#` heading line (any level). -/
def anchorsOf (lines : Array String) : Array String :=
  lines.filterMap fun ln =>
    if ln.startsWith "#" then some (slug ((ln.toList.dropWhile (· == '#')) |> String.ofList)) else none

structure Parsed where
  entries : Array Entry := #[]
  errors : Array String := #[]

/-- Check 1 over every line; `entries` in file order. -/
def parseLog (lines : Array String) : Parsed := Id.run do
  let mut p : Parsed := {}
  let mut lineno := 0
  for ln in lines do
    lineno := lineno + 1
    match parseHeading ln with
    | none => pure ()
    | some (number, letter, rest) =>
      match dateOf rest with
      | none =>
        let msg := s!"DOCS.md:{lineno}: item {number}{letter} — heading has no trailing (YYYY-MM-DD) date"
        p := { p with errors := p.errors.push msg }
      | some d =>
        p := { p with entries := p.entries.push { line := lineno, number, letter, date := d } }
  return p

/-- Checks 2–5.  Returns the error lines in the Python's order. -/
def checkEntries (entries : Array Entry) (anchors : Array String) (gaps : List (Nat × String))
    : Array String := Id.run do
  let mut errs : Array String := #[]
  for i in [1:entries.size] do
    let p := entries[i-1]!; let e := entries[i]!
    if !keyLt p.key e.key then
      errs := errs.push s!"DOCS.md:{e.line}: item {e.name} follows item {p.name} (DOCS.md:{p.line}) — entries must strictly ascend by (number, letter)"
    if e.date < p.date then
      errs := errs.push s!"DOCS.md:{e.line}: item {e.name} dated {e.date} follows item {p.name} dated {p.date} (DOCS.md:{p.line}) — dates must not regress"
  let present := entries.map (·.number)
  let lo := entries[0]!.number; let hi := entries[entries.size - 1]!.number
  for n in [lo:hi+1] do
    if present.contains n then continue
    match gaps.lookup n with
    | none =>
      errs := errs.push s!"DOCS.md: item {n} has no closure-log entry and no DECLARED_GAPS row — add the entry, or declare where it is documented"
    | some a =>
      if !anchors.contains a then
        errs := errs.push s!"scripts/check_closure_log.py: DECLARED_GAPS[{n}] points at #{a}, which is not a heading in DOCS.md"
  let sortedGaps := (gaps.map (·.1)).toArray.qsort (· < ·)
  for n in sortedGaps do
    if present.contains n then
      errs := errs.push s!"scripts/check_closure_log.py: DECLARED_GAPS[{n}] excuses an item that now HAS a closure-log entry — drop the row"
    else if !(lo ≤ n && n ≤ hi) then
      errs := errs.push s!"scripts/check_closure_log.py: DECLARED_GAPS[{n}] is outside the log's range {lo}..{hi} — it excuses nothing"
  return errs

/-- The whole gate over the text of `DOCS.md`: `(exit code, lines to print)`. -/
def gate (text : String) (gaps : List (Nat × String) := declaredGaps) : UInt32 × Array String :=
  let lines := (text.splitOn "\n").toArray
  -- Python `splitlines()` drops a final empty line after a trailing newline
  let lines := if lines.size > 0 && lines[lines.size-1]! == "" then lines.pop else lines
  let anchors := anchorsOf lines
  let p := parseLog lines
  if p.entries.isEmpty then
    (2, #["DOCS.md: no `### Item N (DATE)` entries found — the gate is matching nothing, which is a defect in the gate"])
  else
    let errs := p.errors ++ checkEntries p.entries anchors gaps
    let lo := p.entries[0]!.number; let hi := p.entries[p.entries.size-1]!.number
    if errs.isEmpty then
      (0, #[s!"CLOSURE-LOG: {p.entries.size} entries, items {lo}..{hi}, ascending; dates non-decreasing; {gaps.length} gap(s) declared"])
    else
      (1, errs ++ #["", s!"CLOSURE-LOG: {errs.size} error(s) over {p.entries.size} entries (items {lo}..{hi})"])

-- heading shapes
#guard parseHeading "### Item 212 (2026-09-01)" == some (212, "", " (2026-09-01)")
#guard parseHeading "### Item 67a (2026-09-01)" == some (67, "a", " (2026-09-01)")
#guard parseHeading "###  Item   7 — x (2026-09-01)" == some (7, "", " — x (2026-09-01)")
#guard parseHeading "### Item 67ab (2026-09-01)" == none        -- `\b` fails after `a`
#guard parseHeading "#### Item 12 (2026-09-01)" == none
#guard parseHeading "### Items 12 (2026-09-01)" == none
#guard parseHeading "### Item (2026-09-01)" == none
#guard dateOf " — title (2026-09-27)" == some "2026-09-27"
#guard dateOf " — title (2026-09-27)   " == some "2026-09-27"
#guard dateOf " — title 2026-09-27" == none
#guard dateOf " (2026-9-27)" == none
#guard slug " Surrogate hex escapes: decoded to NUL! " == "surrogate-hex-escapes-decoded-to-nul"
#guard slug "Row 12 — β.5 closure log" == "row-12--β5-closure-log"
#guard slug "§3 Build → gates (a_b)" == "3-build--gates-a_b"
#guard keyLt (67, "") (67, "a") && keyLt (67, "a") (68, "") && !keyLt (68, "") (67, "a") && !keyLt (67, "") (67, "")

-- the gate on a tiny log
private def tiny (body : String) : UInt32 × Array String :=
  gate ("# Doc\n## surrogate hex escapes decoded to NUL\n" ++ body) [(18, "surrogate-hex-escapes-decoded-to-nul")]
#guard (tiny "### Item 17 (2026-01-01)\n### Item 19 (2026-01-02)\n").1 == 0
#guard (tiny "### Item 17 (2026-01-01)\n### Item 18 (2026-01-02)\n### Item 19 (2026-01-02)\n") ==
  (1, #["scripts/check_closure_log.py: DECLARED_GAPS[18] excuses an item that now HAS a closure-log entry — drop the row",
        "", "CLOSURE-LOG: 1 error(s) over 3 entries (items 17..19)"])
#guard (tiny "### Item 20 (2026-01-01)\n### Item 19 (2025-12-31)\n").2.size == 5
#guard (tiny "### Item 20 (2026-01-01)\n### Item 22 (2026-01-01)\n").2[0]! ==
  "DOCS.md: item 21 has no closure-log entry and no DECLARED_GAPS row — add the entry, or declare where it is documented"
#guard (tiny "### Item 20 (2026-01-01)\n### Item 21 no date\n### Item 22 (2026-01-01)\n").2[0]! ==
  "DOCS.md:4: item 21 — heading has no trailing (YYYY-MM-DD) date"
#guard (gate "nothing here\n").1 == 2

end Scripts.Docs.ClosureLog
