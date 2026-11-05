module

public import Scripts.Spec.Annotations
public import Scripts.Html.Bytes

/-!
# `scripts-verify-spec-annotations` — `lake run verify-spec-annotations [-- --spec-file PATH | --spec-url URL] [--lean-root DIR]`

Rule 9's last row (was `scripts/verify_yaml_spec_annotations.py`): every `@[yaml_spec
"section" NNN "name"]` in the tree against the `:NNN: name` table of yaml/yaml-grammar's
`yaml-spec-1.2.yaml` — name mismatches, unknown rule numbers, coverage.  The grammar file
is not vendored (yaml/yaml-grammar carries no licence): by default it is fetched by `curl`
(an external program, as WeasyPrint is) from the raw URL pinned to the commit that last
changed it, or read from `--spec-file PATH`.  The report is the Python's, line for line.

exit status: 0 consistent; 1 a mismatch or unknown rule was found, the spec could not be
read, or the Lean root does not exist; 2 usage.
-/

namespace Scripts.Spec.Main

open Scripts.Spec
open Scripts.Html (ltComps universalNewlines)

def version : String := "scripts-verify-spec-annotations 1.0 (Rule 9, the last row)"

/-- yaml/yaml-grammar `yaml-spec-1.2.yaml`, pinned to the commit that last changed it
    (2020-10-26; blob 0af81136…, 61 915 bytes). -/
def defaultSpecUrl : String :=
  "https://raw.githubusercontent.com/yaml/yaml-grammar/7bc2eabfc4312c13686d02cca6dd9e56c265c029/yaml-spec-1.2.yaml"

def usage : String := s!"usage: scripts-verify-spec-annotations [-C ROOT] [--spec-file PATH | --spec-url URL] [--lean-root DIR]

  Verify @[yaml_spec] annotations against yaml-spec-1.2.yaml (yaml/yaml-grammar):
    1. NAME MISMATCHES  — rule number exists in spec but annotation has a different name
    2. UNKNOWN RULES    — annotation references a rule number not in the spec (1–211)
    3. COVERAGE         — spec rules not referenced by any annotation

  -f, --spec-file PATH   read the grammar file locally (overrides --spec-url)
  -u, --spec-url URL     fetch it with curl (default: the pinned upstream commit,
                         {defaultSpecUrl})
  -l, --lean-root DIR    the tree to scan for *.lean (default: ROOT)
  -C, --root ROOT        the checkout (default: the cwd)
  -h, --help / -V, --version"

def leanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let all ← root.walkDir
  let mut files := #[]
  for p in all do
    if p.extension == some "lean" then
      if (← p.metadata).type == IO.FS.FileType.file then files := files.push p
  return files.qsort fun a b => ltComps a.components b.components

def relTo (root p : System.FilePath) : String :=
  let r := root.toString
  let s := p.toString
  if s.startsWith (r ++ "/") then (s.drop (r.length + 1)).toString else s

def scan (root : System.FilePath) : IO (List Annotation) := do
  let mut anns := []
  for p in ← leanFiles root do
    let text := String.fromUTF8! (universalNewlines (← IO.FS.readBinFile p))
    let rel := relTo root p
    let mut n := 1
    for line in text.splitOn "\n" do
      anns := anns ++ annotationsOfLine rel n line
      n := n + 1
  return anns

def run (root : System.FilePath) (specFile specUrl leanRoot : Option String) : IO UInt32 := do
  let leanRootPath : System.FilePath := match leanRoot with
    | some d => if d.startsWith "/" then d else root / d
    | none => root
  let shownRoot ← match leanRoot with
    | some d => pure d
    | none => do pure (← IO.FS.realPath root).toString
  unless ← leanRootPath.isDir do
    IO.eprintln s!"Error: Lean root not found: {shownRoot}"; return 1
  let specText ← match specFile with
    | some f =>
      IO.println s!"Reading spec from {f}"
      let p : System.FilePath := if f.startsWith "/" then f else root / f
      try pure (String.fromUTF8! (universalNewlines (← IO.FS.readBinFile p)))
      catch e => IO.eprintln s!"Error: {e}"; return 1
    | none =>
      let url := specUrl.getD defaultSpecUrl
      IO.println s!"Fetching spec from {url}"
      let r ← try IO.Process.output { cmd := "curl", args := #["-sSfL", url] }
        catch e => IO.eprintln s!"Error: curl: {e}"; return 1
      if r.exitCode != 0 then
        IO.eprintln s!"Error: curl exited {r.exitCode} fetching {url}: {Scripts.Restate.rstrip r.stderr}"; return 1
      pure r.stdout
  let spec := parseSpec specText
  IO.println s!"Parsed {spec.size} spec rules (expected 211)"
  if spec.size != 211 then IO.eprintln s!"  WARNING: expected 211 rules, got {spec.size}"
  IO.println s!"Scanning Lean files under {shownRoot}"
  let anns ← scan leanRootPath
  let withRule := anns.filter (·.ruleNum.isSome)
  let unique := (withRule.filterMap (·.ruleNum)).eraseDups
  IO.println s!"Found {anns.length} total annotations ({withRule.length} with rule numbers, {anns.length - withRule.length} section-only)"
  IO.println s!"Covering {unique.length} unique rule numbers"
  IO.println ""
  let rep := verify spec anns
  let mut code : UInt32 := 0
  unless rep.mismatches.isEmpty do
    code := 1
    IO.println s!"=== NAME MISMATCHES ({rep.mismatches.length}) ==="
    IO.println "  Annotation rule name doesn't match spec rule name:"
    for m in rep.mismatches do IO.println m
    IO.println ""
  unless rep.unknown.isEmpty do
    code := 1
    IO.println s!"=== UNKNOWN RULES ({rep.unknown.length}) ==="
    IO.println "  Rule number not found in spec:"
    for u in rep.unknown do IO.println u
    IO.println ""
  IO.println s!"=== COVERAGE ({unique.length}/{spec.size} rules) ==="
  IO.println s!"  {pct1 unique.length spec.size}% of spec rules are annotated"
  if rep.uncovered.isEmpty then IO.println "  All spec rules are covered!"
  else
    IO.println s!"  {rep.uncovered.length} uncovered rules:"
    for u in rep.uncovered do IO.println u
  IO.println ""
  IO.println (if code == 0 then "OK — all annotated rules are consistent with the spec."
    else "FAIL — inconsistencies found (see above).")
  return code

def cli (args : List String) : IO UInt32 := do
  let mut root : System.FilePath := "."
  let mut specFile : Option String := none
  let mut specUrl : Option String := none
  let mut leanRoot : Option String := none
  let mut it := args
  while true do
    match it with
    | [] => break
    | "-h" :: _ | "--help" :: _ => IO.println usage; return 0
    | "-V" :: _ | "--version" :: _ => IO.println version; return 0
    | "-C" :: r :: more | "--root" :: r :: more => root := r; it := more
    | "-f" :: p :: more | "--spec-file" :: p :: more => specFile := some p; it := more
    | "-u" :: u :: more | "--spec-url" :: u :: more => specUrl := some u; it := more
    | "-l" :: d :: more | "--lean-root" :: d :: more => leanRoot := some d; it := more
    | a :: _ => IO.eprintln s!"scripts-verify-spec-annotations: unrecognized argument '{a}'\n{usage}"; return 2
  run root specFile specUrl leanRoot

end Scripts.Spec.Main

public def main (args : List String) : IO UInt32 := Scripts.Spec.Main.cli args
