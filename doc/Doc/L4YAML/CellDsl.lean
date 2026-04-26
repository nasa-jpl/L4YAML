/-
  L4YAML Documentation — shared cell-DSL helpers.

  Both `StatsTable.lean` and `ModuleGroups.lean` build Verso `Block.table`
  blocks from data computed at elaboration time. They share a small DSL
  for cell content (text + inline-code runs) and for converting it into
  the syntax that the table block extension expects.
-/
import Lean
import VersoManual

open Lean Elab
open Verso Doc Elab
open Verso.Genre Manual

namespace Doc.L4YAML.CellDsl

/-- A run of inline content in a table cell: plain text or inline code. -/
inductive Run where
  | text (s : String)
  | code (s : String)

abbrev Cell := List Run

/-- Quote a `Run` as the corresponding `Verso.Doc.Inline` term. -/
def Run.toInlineSyntax : Run → DocElabM (TSyntax `term)
  | .text s => `(Verso.Doc.Inline.text $(Lean.quote s))
  | .code s => `(Verso.Doc.Inline.code $(Lean.quote s))

/-- Quote a `Cell` as a `ListItem.mk #[Block.para #[<inlines>]]` term. -/
def Cell.toListItemSyntax (c : Cell) : DocElabM (TSyntax `term) := do
  let inls : Array (TSyntax `term) ← c.toArray.mapM Run.toInlineSyntax
  `(Verso.Doc.ListItem.mk #[Verso.Doc.Block.para #[$inls,*]])

/-- Build a 2/3-column `Block.table` from a flat array of cells. The
    table block extension chunks the cell list back into rows by `columns`,
    so the caller just hands over `[header_cell_0, header_cell_1, …,
    row1_cell_0, row1_cell_1, …]` in row-major order. -/
def buildTableSyntax (columns : Nat) (header : Bool)
    (cells : Array Cell) : DocElabM (TSyntax `term) := do
  let listItems ← cells.mapM Cell.toListItemSyntax
  let tag : Option String := none
  let alignment : Option Verso.Genre.Manual.TableConfig.Alignment := none
  `(Verso.Doc.Block.other
      (Verso.Genre.Manual.Block.table $(Lean.quote columns) $(Lean.quote header)
        $(Lean.quote tag) $(Lean.quote alignment))
      #[Verso.Doc.Block.ul #[$[$listItems],*]])

/-- Parse a string with backtick-delimited inline code into a `Cell`.
    Example: `"foo `bar` baz"` ↦ `[.text "foo ", .code "bar", .text " baz"]`.
    Empty runs are dropped. Unbalanced backticks treat trailing content
    as plain text. -/
def parseProse (s : String) : Cell :=
  let parts := s.splitOn "`"
  let rec go (xs : List String) (isCode : Bool) : List Run :=
    match xs with
    | [] => []
    | p :: rest =>
      let head : List Run :=
        if p.isEmpty then [] else [if isCode then .code p else .text p]
      head ++ go rest !isCode
  go parts false

end Doc.L4YAML.CellDsl
