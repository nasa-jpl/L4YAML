module

/-!
# Scripts.Ledger.Diff — the pure half of `lake run ledger-diff`

The port of `scripts/ledger_diff.py` (Rule 9 phase 2).  A ledger snapshot
(`Blueprint/ledgers/parse_iff_grammar/YYYY-MM-DD.md`) is Markdown whose `## ` sections
hold tables keyed by their first column and one `## Instruments` table of `| key | value |`
rows.  Everything here is a function of the two files' text: the row splitter (a pipe is
escaped by an odd run of backslashes — PRs #125/#126), the section/table reader, the
instrument diff with its numeric Δ, the row diff cell by cell, and the Markdown report
`lake run ledger-diff` prints.  Each reading is pinned by a `#guard` on the Python's own
cases.  The IO (reading the files, `--latest`, `--out`) is `Scripts.Main.LedgerDiff`.

Deltas are exact decimals here; the Python subtracted floats and printed them through
`%g`, which agrees on every value a ledger holds (integers and short decimals).
-/

namespace Scripts.Ledger.Diff

public section

/-- Python's `strip()` on the ASCII whitespace a ledger holds. -/
def strip (s : String) : String := s.trimAscii.toString

/-- `split_row`: the cells of a Markdown table row, split on unescaped pipes.  A pipe is
    escaped when an odd number of backslashes precedes it; `\|` decodes to `|`, any other
    backslash run is kept as written.  A blank tail after the last pipe is not a cell. -/
def splitRow (line : String) : Array String := Id.run do
  let body : List Char := (strip line).toList
  let body : List Char := if body.head? == some '|' then body.drop 1 else body
  let mut cells : Array String := #[]
  let mut cur : List Char := []
  let mut rest := body
  while !rest.isEmpty do
    match rest with
    | '\\' :: _ =>
      let run := rest.takeWhile (· == '\\')
      let after := rest.drop run.length
      if after.head? == some '|' && run.length % 2 == 1 then
        cur := cur ++ List.replicate (run.length - 1) '\\' ++ ['|']
        rest := after.drop 1
      else
        cur := cur ++ run
        rest := after
    | '|' :: t =>
      cells := cells.push (String.ofList cur)
      cur := []
      rest := t
    | c :: t =>
      cur := cur ++ [c]
      rest := t
    | [] => pure ()
  let tail := String.ofList cur
  if strip tail != "" || cells.isEmpty then cells := cells.push tail
  return cells.map strip

#guard splitRow "| a | b | c |" == #["a", "b", "c"]
#guard splitRow "| a | b | c" == #["a", "b", "c"]
#guard splitRow "a | b" == #["a", "b"]
-- #125: `\|` inside a cell is a literal pipe, not a cell boundary.
#guard splitRow "| F1 | `a \\| b` | x |" == #["F1", "`a | b`", "x"]
-- #126: only an odd backslash run escapes; `\\|` is a backslash then a boundary.
#guard splitRow "| a \\\\| b |" == #["a \\\\", "b"]
#guard splitRow "| a \\\\\\| b |" == #["a \\\\| b"]
#guard splitRow "| a \\n b |" == #["a \\n b"]
#guard splitRow "|" == #[""]
#guard splitRow "| a |   " == #["a"]
#guard splitRow "" == #[""]

/-- `esc`: a cell re-encoded for a Markdown table in the report. -/
def esc (cell : String) : String := cell.replace "|" "\\|"

#guard esc "a | b" == "a \\| b"

/-- `:?-{3,}:?` as a full match. -/
def isRuleCell (c : String) : Bool :=
  let cs := c.toList
  let cs := if cs.head? == some ':' then cs.drop 1 else cs
  let cs := if cs.getLast? == some ':' then cs.dropLast else cs
  cs.length ≥ 3 && cs.all (· == '-')

/-- `is_rule`: every non-empty cell is a rule (`---`, `:---:`, …) and one is non-empty. -/
def isRule (cells : Array String) : Bool :=
  (cells.all fun c => c.isEmpty || isRuleCell c) && cells.any (!·.isEmpty)

#guard isRule #["---", ":---:", "---:"]
#guard !isRule #["--:"]
#guard isRule #["---", ""]
#guard !isRule #["--", "---"]
#guard !isRule #["", ""]
#guard !isRule #["F1", "---"]
#guard !isRule #["-:-"]

structure Section where
  header : Option (Array String) := none
  /-- `(key, cells)` in file order; a repeated key keeps every appearance in `order` and the
      last cells in the lookup, as the Python's `rows[key] = cells` / `order.append(key)`. -/
  rows : Array (String × Array String) := #[]
  deriving Repr, Inhabited, BEq

namespace Section

def order (s : Section) : Array String := s.rows.map (·.1)

def get? (s : Section) (k : String) : Option (Array String) :=
  (s.rows.findRev? (·.1 == k)).map (·.2)

end Section

/-- Sections in order of first table row; `(preamble)` is the text before any `## `. -/
abbrev Ledger := Array (String × Section)

def Ledger.get? (l : Ledger) (name : String) : Option Section :=
  (l.find? (·.1 == name)).map (·.2)

def Ledger.names (l : Ledger) : Array String := l.map (·.1)

private def upsert (l : Ledger) (name : String) (f : Section → Section) : Ledger :=
  match l.findIdx? (·.1 == name) with
  | some i => l.modify i fun (n, s) => (n, f s)
  | none => l.push (name, f {})

/-- `splitlines` for the shapes a ledger has: `\r\n`, `\r` and `\n`, no final empty line. -/
def lines (text : String) : Array String :=
  let ls := (((text.replace "\r\n" "\n").replace "\r" "\n").splitOn "\n").toArray
  if ls.size > 0 && ls.back! == "" then ls.pop else ls

#guard lines "a\r\nb\rc\n" == #["a", "b", "c"]
#guard lines "" == #[]

/-- `parse`: the sections and tables of one snapshot, plus the `name:lineno: N cells, header
    has M` warnings the Python printed to stderr.  Fenced code is skipped; a `## ` heading
    or a blank line ends the current table (the next row is a header); a rule row is
    skipped; the first cell keys the row. -/
def parse (name text : String) : Ledger × Array String := Id.run do
  let mut out : Ledger := #[]
  let mut warn : Array String := #[]
  let mut sec := "(preamble)"
  let mut header : Option (Array String) := none
  let mut inCode := false
  let mut lineno := 0
  for raw in lines text do
    lineno := lineno + 1
    if raw.startsWith "```" then inCode := !inCode
    else if inCode then pure ()
    else if raw.startsWith "## " then
      sec := strip (raw.drop 3).toString
      header := none
    else if raw.startsWith "|" then
      let cells := splitRow raw
      if isRule cells then pure ()
      else
        match header with
        | none =>
          header := some cells
          out := upsert out sec fun s => { s with header := some cells }
        | some h =>
          if cells.size != h.size then
            warn := warn.push s!"{name}:{lineno}: {cells.size} cells, header has {h.size}"
          out := upsert out sec fun s => { s with rows := s.rows.push (cells[0]!, cells) }
    else if strip raw == "" then header := none
  return (out, warn)

private def sample : String :=
  "# T\n\n## Instruments\n\n| key | value |\n|---|---|\n| a | 1 |\n| b | `2` |\n\n## Rows\n\n```\n| not | a | table |\n```\n| id | State | Note |\n|:---|---|---:|\n| F1 | x | y |\n| F2 | p \\| q | r | extra |\n"

#guard (parse "s.md" sample).2 == #["s.md:18: 4 cells, header has 3"]
#guard (parse "s.md" sample).1.names == #["Instruments", "Rows"]
#guard ((parse "s.md" sample).1.get? "Instruments").map (·.order) == some #["a", "b"]
#guard ((parse "s.md" sample).1.get? "Rows").bind (·.get? "F2") == some #["F2", "p | q", "r", "extra"]
#guard ((parse "s.md" sample).1.get? "Rows").map (·.header) == some (some #["id", "State", "Note"])
-- A repeated key: both appearances in `order`, the last cells win.
#guard (((parse "d.md" "## S\n| k | v |\n|---|---|\n| a | 1 |\n| a | 2 |\n").1.get? "S").map fun s => (s.order, s.get? "a"))
  == some (#["a", "a"], some #["a", "2"])

/-! ## Numbers: `^-?\d+(\.\d+)?$` after stripping backticks and commas, exact -/

/-- A decimal as `mant / 10^scale`. -/
structure Dec where
  mant : Int
  scale : Nat
  deriving Repr, BEq

def num? (s : String) : Option Dec := do
  let s := strip ((s.replace "`" "").replace "," "")
  let cs := s.toList
  let (neg, cs) := if cs.head? == some '-' then (true, cs.drop 1) else (false, cs)
  let intPart := cs.takeWhile Char.isDigit
  guard !intPart.isEmpty
  let rest := cs.drop intPart.length
  let (frac, rest) ← match rest with
    | [] => pure ([], [])
    | '.' :: t =>
      let f := t.takeWhile Char.isDigit
      if f.isEmpty then none else pure (f, t.drop f.length)
    | _ => none
  guard rest.isEmpty
  let digits := String.ofList (intPart ++ frac)
  let m : Int := digits.toNat!
  pure { mant := if neg then -m else m, scale := frac.length }

#guard num? "42" == some ⟨42, 0⟩
#guard num? "`1,234`" == some ⟨1234, 0⟩
#guard num? "-3.50" == some ⟨-350, 2⟩
#guard num? "1e3" == none
#guard num? "12 (#1)" == none
#guard num? "." == none
#guard num? "—" == none

def Dec.sub (b a : Dec) : Dec :=
  let s := max a.scale b.scale
  { mant := b.mant * 10 ^ (s - b.scale) - a.mant * 10 ^ (s - a.scale), scale := s }

/-- `fmt_num`: an integer as such, otherwise the shortest decimal (`%g` on a ledger value). -/
def Dec.format (d : Dec) : String :=
  let digits := (toString d.mant.natAbs).toList
  let digits := if digits.length ≤ d.scale then List.replicate (d.scale + 1 - digits.length) '0' ++ digits else digits
  let ip := digits.take (digits.length - d.scale)
  let fp := ((digits.drop (digits.length - d.scale)).reverse.dropWhile (· == '0')).reverse
  (if d.mant < 0 then "-" else "") ++ String.ofList ip ++ (if fp.isEmpty then "" else "." ++ String.ofList fp)

/-- The Δ column: `+N` when new − old ≥ 0, else `-N`; empty unless both values are numbers. -/
def delta (ov nv : String) : String :=
  match num? ov, num? nv with
  | some a, some b =>
    let d := b.sub a
    (if d.mant ≥ 0 then "+" else "") ++ d.format
  | _, _ => ""

#guard delta "381" "398" == "+17"
#guard delta "12" "9" == "-3"
#guard delta "5" "`5`" == "+0"
#guard delta "0.1" "0.3" == "+0.2"
#guard delta "1.50" "1" == "-0.5"
#guard delta "2.5" "2.5" == "+0"
#guard delta "—" "266" == ""
#guard delta "26 (#122–#147)" "24" == ""

/-! ## The diff -/

/-- `dict.fromkeys(a + b)`: the union, first appearance first. -/
def dedupKeys (a b : Array String) : Array String :=
  (a ++ b).foldl (fun acc k => if acc.contains k then acc else acc.push k) #[]

#guard dedupKeys #["a", "b", "a"] #["c", "b"] == #["a", "b", "c"]

/-- `diff_instruments`: the `## Instruments` block of the report. -/
def diffInstruments (old new : Ledger) : Array String := Id.run do
  let o := (old.get? "Instruments").getD {}
  let n := (new.get? "Instruments").getD {}
  let mut moved : Array (String × String × String × String) := #[]
  let mut same := 0
  for k in dedupKeys o.order n.order do
    let ov := (o.get? k).map fun c => c[1]?.getD ""
    let nv := (n.get? k).map fun c => c[1]?.getD ""
    if ov == nv then same := same + 1
    else
      let d := match ov, nv with | some a, some b => delta a b | _, _ => ""
      moved := moved.push (k, ov.getD "—", nv.getD "—", d)
  let mut out : Array String := #["## Instruments\n"]
  if moved.isEmpty then return out.push s!"No instrument moved ({same} unchanged).\n"
  out := out.push "| key | old | new | Δ |" |>.push "|---|---|---|---|"
  for (k, ov, nv, d) in moved do
    out := out.push s!"| `{esc k}` | {esc ov} | {esc nv} | {d} |"
  return out.push s!"\n{moved.size} moved, {same} unchanged.\n"

/-- `cell_diff`: the changed cells of one row, by header name (`col i` without one). -/
def cellDiff (oc nc : Array String) (header : Option (Array String)) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [1:max oc.size nc.size] do
    let a := oc[i]?.getD ""
    let b := nc[i]?.getD ""
    if a != b then
      let col := match header with
        | some h => if i < h.size then h[i]! else s!"col {i}"
        | none => s!"col {i}"
      out := out.push s!"  - **{col}**" |>.push s!"    - was: {a}" |>.push s!"    - now: {b}"
  return out

/-- `diff_tables`: one block per section with a difference, then the `**Rows:**` line. -/
def diffTables (old new : Ledger) : Array String := Id.run do
  let sections := (dedupKeys old.names new.names).filter fun s => s != "Instruments" && s != "(preamble)"
  let mut changed := 0; let mut added := 0; let mut removed := 0; let mut unchanged := 0
  let mut out : Array String := #[]
  for s in sections do
    let o := (old.get? s).getD {}
    let n := (new.get? s).getD {}
    let header := match n.header with | some h => if h.isEmpty then o.header else some h | none => o.header
    let mut block : Array String := #[]
    for k in dedupKeys o.order n.order do
      match o.get? k, n.get? k with
      | none, some nrow =>
        added := added + 1
        block := block.push (s!"- **{k}** — ADDED: " ++ " · ".intercalate (nrow.extract 1 nrow.size).toList)
      | some orow, none =>
        removed := removed + 1
        block := block.push (s!"- **{k}** — REMOVED (was: " ++ " · ".intercalate (orow.extract 1 orow.size).toList ++ ")")
      | some orow, some nrow =>
        if orow.extract 1 orow.size != nrow.extract 1 nrow.size then
          changed := changed + 1
          block := block.push s!"- **{k}** — changed" ++ cellDiff orow nrow header
        else unchanged := unchanged + 1
      | none, none => pure ()
    if !block.isEmpty then
      out := out.push s!"## {s}\n" ++ block |>.push ""
  return out.push s!"**Rows:** {changed} changed, {added} added, {removed} removed, {unchanged} unchanged.\n"

/-- The whole report, one entry per output line (joined with `\n`, then a final newline). -/
def report (oldName newName : String) (old new : Ledger) : Array String :=
  #[s!"# Ledger diff: `{oldName}` → `{newName}`\n"] ++ diffInstruments old new ++ diffTables old new

private def oldL : Ledger := (parse "o.md" "## Instruments\n| key | value |\n|---|---|\n| n | 3 |\n| t | a |\n| gone | 1 |\n\n## Rows\n| id | State | Note |\n|---|---|---|\n| F1 | x | y |\n| F3 | q | q |\n| F4 | same | same |\n").1
private def newL : Ledger := (parse "n.md" "## Instruments\n| key | value |\n|---|---|\n| n | 5 |\n| t | a \\| b |\n| new | — |\n\n## Rows\n| id | State | Note |\n|---|---|---|\n| F1 | x | z |\n| F2 | p | r |\n| F4 | same | same |\n").1

#guard report "o.md" "n.md" oldL newL == #[
  "# Ledger diff: `o.md` → `n.md`\n",
  "## Instruments\n",
  "| key | old | new | Δ |", "|---|---|---|---|",
  "| `n` | 3 | 5 | +2 |",
  "| `t` | a | a \\| b |  |",
  "| `gone` | 1 | — |  |",
  "| `new` | — | — |  |",
  "\n4 moved, 0 unchanged.\n",
  "## Rows\n",
  "- **F1** — changed", "  - **Note**", "    - was: y", "    - now: z",
  "- **F3** — REMOVED (was: q · q)",
  "- **F2** — ADDED: p · r",
  "",
  "**Rows:** 1 changed, 1 added, 1 removed, 1 unchanged.\n"]
#guard report "a" "a" oldL oldL == #["# Ledger diff: `a` → `a`\n", "## Instruments\n", "No instrument moved (3 unchanged).\n", "**Rows:** 0 changed, 0 added, 0 removed, 3 unchanged.\n"]

end

end Scripts.Ledger.Diff
