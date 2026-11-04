module

public import Scripts.Html.Svg
public import Scripts.Html.Merge

/-!
# `scripts-html-pdf` — `lake run svg-objects` / `html-merge` / `html-to-pdf`

The publishing row of Rule 9 (Blueprint 09, Q3 — the CLI route): the HTML rewriting
of `scripts/svg-objects.py` and `scripts/html-to-pdf.py` in Lean, and the one external
program, WeasyPrint, run as its own command-line tool (`$WEASYPRINT`, else `weasyprint`
on PATH — CI and `generate-all.sh` point it at their venv's copy), never through Python
logic of ours.
-/

namespace Scripts.HtmlPdf

open Scripts.Html

def version : String := "scripts-html-pdf 1.0 (Rule 9 phase 4 row 4)"

def usage : String := "usage: scripts-html-pdf [-C ROOT] COMMAND ARGS

  svg-objects DIR               rewrite <img src=\"*.svg\"> as <object> in place under DIR
                                (lake run svg-objects -- DIR; was scripts/svg-objects.py)
  merge HTML_INPUT MERGED_HTML  the single PDF-ready document: first page's head, every
                                page's pruned body, renumbered headings, print stylesheet
                                (lake run html-merge -- IN OUT.html)
  pdf HTML_INPUT OUTPUT_PDF     merge beside the source, render it with the weasyprint CLI
                                ($WEASYPRINT, else weasyprint on PATH), remove the merged file
                                (lake run html-to-pdf -- IN OUT.pdf; was scripts/html-to-pdf.py)

  HTML_INPUT is a self-contained page (rendered as is, in document order) or a site
  directory (its chapter index.html pages, ordered by the numbered table of contents).
  -C, --root ROOT               resolve relative paths against ROOT (default: the cwd)
  -h, --help / -V, --version

exit: svg-objects 2 on a bad argument; merge/pdf 1 on a bad argument, a missing root
index.html, an unavailable weasyprint or a failed render."

def resolveArg (root : Option System.FilePath) (a : String) : System.FilePath :=
  match root with
  | some r => if a.startsWith "/" then a else r / a
  | none => a

def isFile (p : System.FilePath) : IO Bool := do
  try return (← p.metadata).type == IO.FS.FileType.file catch _ => return false

def readPage (p : System.FilePath) : IO ByteArray := do
  let b := universalNewlines (← IO.FS.readBinFile p)
  unless b.validateUTF8 do
    throw (IO.userError s!"{p}: not UTF-8 ('utf-8' codec can't decode)")
  return b

def sortedFiles (dir : System.FilePath) (keep : System.FilePath → Bool) : IO (Array System.FilePath) := do
  let all ← dir.walkDir
  let mut files := #[]
  for p in all do
    if keep p && (← isFile p) then files := files.push p
  return files.qsort fun a b => ltComps a.components b.components

def svgObjects (root : Option System.FilePath) (args : List String) : IO UInt32 := do
  let [dirArg] := args
    | IO.eprintln "usage: lake run svg-objects -- <html-tree>"; return 2
  let shown := pyPath dirArg
  let dir := resolveArg root dirArg
  unless ← dir.isDir do IO.eprintln s!"error: {shown} is not a directory"; return 2
  let mut pages := 0
  let mut files := 0
  for p in ← sortedFiles dir (·.extension == some "html") do
    let (out, n) := Svg.rewriteBytes (← readPage p)
    if n > 0 then
      IO.FS.writeBinFile p out
      pages := pages + 1
      files := files + n
  IO.eprintln s!"svg-objects: rewrote {files} SVG <img> into <object> across {pages} pages under {shown}"
  return 0

/-- Lexical `..`/`.` collapse, as `Path.resolve()` does before touching the filesystem. -/
def normalize (p : System.FilePath) : System.FilePath :=
  let abs := p.toString.startsWith "/"
  let comps := p.components.foldl (init := ([] : List String)) fun acc c =>
    if c.isEmpty || c == "." then acc
    else if c == ".." then (if acc.isEmpty then acc else acc.dropLast) else acc ++ [c]
  let s := "/".intercalate comps
  if abs then "/" ++ s else if s.isEmpty then "." else s

def isPrefixOf (a b : List String) : Bool := a.isPrefixOf b

/-- `_resolve_page`: the nav href, relative to the page it appears on, as an
`index.html` under `rootReal`, or `none`. -/
def resolvePage (idx : System.FilePath) (href : String) (rootReal : System.FilePath) :
    IO (Option System.FilePath) := do
  let target := (((href.splitOn "#").headD "").splitOn "?").headD ""
  if target.isEmpty then return none
  let base ← IO.FS.realPath (idx.parent.getD ".")
  let dest := normalize (if target.startsWith "/" then target else base / target)
  let dest ← if ← dest.pathExists then IO.FS.realPath dest else pure dest
  let dest := if ← dest.isDir then dest / "index.html" else dest
  unless isPrefixOf rootReal.components dest.components do return none
  return if ← isFile dest then some dest else none

/-- `find_all_pages`; `none` after the Python's `Error: … not found` (exit 1). -/
def findAllPages (shownIn : String) (input : System.FilePath) : IO (Option (List System.FilePath)) := do
  if ← isFile input then return some [input]
  let rootIdx := input / "index.html"
  unless ← isFile rootIdx do
    IO.eprintln s!"Error: {pyPath shownIn}/index.html not found"; return none
  let rootReal ← IO.FS.realPath input
  let mut pageOfNum : Array (String × System.FilePath) := #[]
  for idx in ← sortedFiles input (·.fileName == some "index.html") do
    let text := universalNewlines (← IO.FS.readBinFile idx)
    for (num, href) in Merge.navRows text do
      if let some page ← resolvePage idx href rootReal then
        let key := stripDots num
        unless pageOfNum.any (·.1 == key) do pageOfNum := pageOfNum.push (key, page)
  let mut keyed : List (List Nat × System.FilePath) := []
  for (key, page) in pageOfNum do
    match Merge.numKey key with
    | .ok k => keyed := keyed ++ [(k, page)]
    | .error e => throw (IO.userError s!"ValueError: {e}")
  let ordered := keyed.mergeSort fun a b => !Merge.ltKey b.1 a.1
  let mut pages := [rootIdx]
  let mut seen := [← IO.FS.realPath rootIdx]
  for (_, page) in ordered do
    let rp ← IO.FS.realPath page
    unless seen.contains rp do
      seen := seen ++ [rp]
      pages := pages ++ [page]
  if pages.length == 1 then
    IO.eprintln "warning: no numbered table-of-contents found; rendering the root page only"
  return some pages

def mergeDoc (shownIn : String) (input : System.FilePath) : IO (Option String) := do
  let some pages ← findAllPages shownIn input | return none
  let baseShown := if ← isFile input then pyParent shownIn else pyPath shownIn
  IO.println s!"Found {pages.length} HTML page(s); base {baseShown}"
  let mut bytes := #[]
  for p in pages do bytes := bytes.push (← readPage p)
  return some (Merge.mergeBytes bytes)

def merge (root : Option System.FilePath) (args : List String) : IO UInt32 := do
  let [inArg, outArg] := args
    | IO.eprintln "Usage: lake run html-merge -- HTML_INPUT MERGED_HTML"; return 1
  let some merged ← mergeDoc inArg (resolveArg root inArg) | return 1
  let out := resolveArg root outArg
  if let some d := out.parent then IO.FS.createDirAll d
  IO.FS.writeFile out merged
  return 0

/-- `f"{size/1024:.0f}"`: the exact quotient rounded half to even. -/
def kbOf (size : Nat) : Nat :=
  let q := size / 1024
  let r := size % 1024
  if r > 512 || (r == 512 && q % 2 == 1) then q + 1 else q

def weasyprintAvailable (wp : String) : IO Bool := do
  try
    let o ← IO.Process.output { cmd := wp, args := #["--version"] }
    return o.exitCode == 0
  catch _ => return false

def pdf (root : Option System.FilePath) (args : List String) : IO UInt32 := do
  let [inArg, outArg] := args
    | IO.eprintln "Usage: lake run html-to-pdf -- HTML_INPUT OUTPUT_PDF"; return 1
  let wp := (← IO.getEnv "WEASYPRINT").getD "weasyprint"
  unless ← weasyprintAvailable wp do
    IO.eprintln s!"Error: weasyprint not available ({wp} --version failed). Point WEASYPRINT at a venv's weasyprint or put it on PATH."
    return 1
  let input := resolveArg root inArg
  let some merged ← mergeDoc inArg input | return 1
  let baseDir ← if ← isFile input then pure (input.parent.getD ".") else pure input
  let mergedPath := baseDir / "_merged_for_pdf.html"
  IO.FS.writeFile mergedPath merged
  let out := resolveArg root outArg
  IO.println s!"Generating PDF: {pyPath outArg}"
  if let some d := out.parent then IO.FS.createDirAll d
  let code ← try
      let child ← IO.Process.spawn { cmd := wp, args := #[mergedPath.toString, out.toString] }
      child.wait
    catch e =>
      IO.eprintln s!"Error: {wp}: {e}"; pure (1 : UInt32)
  try IO.FS.removeFile mergedPath catch _ => pure ()
  if code != 0 then
    IO.eprintln s!"Error: weasyprint exited {code}"; return 1
  let size := (← out.metadata).byteSize.toNat
  IO.println s!"PDF generated: {pyPath outArg} ({kbOf size} KB)"
  return 0

def cli (args : List String) : IO UInt32 := do
  let mut root : Option System.FilePath := none
  let mut rest : Array String := #[]
  let mut it := args
  while true do
    match it with
    | [] => break
    | "-h" :: _ | "--help" :: _ => IO.println usage; return 0
    | "-V" :: _ | "--version" :: _ => IO.println version; return 0
    | "-C" :: r :: more | "--root" :: r :: more => root := some r; it := more
    | a :: more => rest := rest.push a; it := more
  match rest.toList with
  | "svg-objects" :: as => svgObjects root as
  | "merge" :: as => merge root as
  | "pdf" :: as => pdf root as
  | c :: _ => IO.eprintln s!"scripts-html-pdf: unknown command '{c}'\n{usage}"; return 2
  | [] => IO.eprintln usage; return 2

end Scripts.HtmlPdf

public def main (args : List String) : IO UInt32 := Scripts.HtmlPdf.cli args
