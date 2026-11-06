module

public import Scripts.Spec.Annotations
public import Scripts.Spec.Env
public import Scripts.Html.Bytes

/-!
# `scripts-verify-spec-annotations` — `lake run verify-spec-annotations [-- --spec-file PATH | --spec-url URL] [--lean-root DIR] [--no-build]`

Rule 9's last row (was `scripts/verify_yaml_spec_annotations.py`): every `@[yaml_spec
"section" NNN "name"]` reference the build registered against the `:NNN: name` table of
yaml/yaml-grammar's `yaml-spec-1.2.yaml` — name mismatches, unknown rule numbers, coverage.

The references are read off the environment, not the text (Rule 9 §2): `lake build` first
(Lake's content hashes decide what is stale; `--no-build` reads the `.olean`s as they are),
then for every `*.lean` under the Lean root that is a module of this workspace (its `.olean`
under `.lake/build/lib/lean`), the `yamlSpecExt` entries of that `.olean` — the declaration
and the reference — placed by `declRangeExt`.  Source files that are not built modules
(`lakefile.lean`, `doc/`, scratch files) hold no entries and are not read; their count goes
to stderr.  A diagnostic points at `file:line decl`.

The grammar file is not vendored (yaml/yaml-grammar carries no licence): by default it is
fetched by `curl` (an external program, as WeasyPrint is) from the raw URL pinned to the
commit that last changed it, or read from `--spec-file PATH`.  Relative paths given on the
command line are the caller's (resolved against the working directory, as the Python did);
`-C ROOT` only names the checkout.  The report is the Python's, line for line.

exit status: 0 consistent; 1 a mismatch or unknown rule was found, the spec could not be
read, the Lean root does not exist or is outside the checkout, or the build failed; 2 usage.
-/

namespace Scripts.Spec.Main

open Scripts.Spec
open Scripts.Html (ltComps universalNewlines)
open Scripts.Lean.DeclRanges (readRanges)

def version : String := "scripts-verify-spec-annotations 1.1 (Rule 9, the last row)"

/-- yaml/yaml-grammar `yaml-spec-1.2.yaml`, pinned to the commit that last changed it
    (2020-10-26; blob 0af81136…, 61 915 bytes). -/
def defaultSpecUrl : String :=
  "https://raw.githubusercontent.com/yaml/yaml-grammar/7bc2eabfc4312c13686d02cca6dd9e56c265c029/yaml-spec-1.2.yaml"

def usage : String := s!"usage: scripts-verify-spec-annotations [-C ROOT] [--spec-file PATH | --spec-url URL] [--lean-root DIR] [--no-build]

  Verify the @[yaml_spec] references the build registered against yaml-spec-1.2.yaml
  (yaml/yaml-grammar), off the .oleans (`lake build` runs first unless --no-build):
    1. NAME MISMATCHES  — rule number exists in spec but annotation has a different name
    2. UNKNOWN RULES    — annotation references a rule number not in the spec (1–211)
    3. COVERAGE         — spec rules not referenced by any annotation

  -f, --spec-file PATH   read the grammar file locally (overrides --spec-url)
  -u, --spec-url URL     fetch it with curl (default: the pinned upstream commit,
                         {defaultSpecUrl})
  -l, --lean-root DIR    the subtree whose modules are read (default: ROOT)
  -n, --no-build         read the .oleans as they are (build first if they must be current)
  -C, --root ROOT        the checkout (default: the cwd)
  -h, --help / -V, --version

  PATH and DIR are resolved against the working directory, not ROOT."

def leanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let all ← root.walkDir fun d => pure (d.fileName != some ".lake" && d.fileName != some ".git")
  let mut files := #[]
  for p in all do
    if p.extension == some "lean" then
      if (← p.metadata).type == IO.FS.FileType.file then files := files.push p
  return files.qsort fun a b => ltComps a.components b.components

/-- `p` relative to `root` (both real paths), when it is below it. -/
def relTo? (root p : System.FilePath) : Option String :=
  let r := root.toString
  let s := p.toString
  if s.startsWith (r ++ "/") then some (s.drop (r.length + 1)).toString else none

/-- The module's `.olean`: `.lake/build/lib/lean/<rel without .lean>.olean`. -/
def oleanOf (root : System.FilePath) (rel : String) : System.FilePath :=
  root / ".lake" / "build" / "lib" / "lean" / (String.ofList (rel.toList.take (rel.length - 5)) ++ ".olean")

/-- Every reference registered by the modules under `leanRoot`, in file order then source
    order; the second component counts the `.lean` files that are not built modules. -/
def readAll (root leanRoot : System.FilePath) : IO (List Annotation × Nat) := do
  let mut anns : Array Annotation := #[]
  let mut skipped := 0
  for p in ← leanFiles leanRoot do
    let some rel := relTo? root p | skipped := skipped + 1; continue
    let olean := oleanOf root rel
    unless ← olean.pathExists do skipped := skipped + 1; continue
    let refs := (← Env.readSpecRefs olean).filter fun (n, _) => Env.isUserDecl n
    if refs.isEmpty then continue
    let ranges ← try readRanges olean catch _ => pure #[]
    for (line, n, r) in Env.ordered refs ranges do
      anns := anns.push { file := rel, decl := Env.userName n, line, section_ := r.specSection,
                          ruleNum := r.rule, ruleName := r.name }
  return (anns.toList, skipped)

def run (root : System.FilePath) (specFile specUrl leanRoot : Option String) (build : Bool) : IO UInt32 := do
  unless ← root.isDir do
    IO.eprintln s!"Error: checkout not found: {root}"; return 1
  let rootReal ← IO.FS.realPath root
  let leanRootGiven : System.FilePath := leanRoot.getD root.toString
  let shownRoot := leanRoot.getD rootReal.toString
  unless ← leanRootGiven.isDir do
    IO.eprintln s!"Error: Lean root not found: {shownRoot}"; return 1
  let leanRootReal ← IO.FS.realPath leanRootGiven
  unless leanRootReal == rootReal || (relTo? rootReal leanRootReal).isSome do
    IO.eprintln s!"Error: Lean root {shownRoot} is not inside the checkout {rootReal}"; return 1
  let specText ← match specFile with
    | some f =>
      IO.println s!"Reading spec from {f}"
      try pure (String.fromUTF8! (universalNewlines (← IO.FS.readBinFile f)))
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
  if build then
    IO.println "Building (lake build; the references are read off the .oleans)"
    let b ← IO.Process.output { cmd := "lake", args := #["build"], cwd := some rootReal }
    if b.exitCode != 0 then
      IO.eprintln b.stdout; IO.eprintln b.stderr
      IO.eprintln "Error: lake build failed; the .oleans are not a reading"; return 1
  IO.println s!"Reading @[yaml_spec] references of the modules under {shownRoot}"
  let (anns, skipped) ← readAll rootReal leanRootReal
  if skipped > 0 then
    IO.eprintln s!"  ({skipped} .lean files under {shownRoot} are not built modules of this workspace and hold no references)"
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
  let mut build := true
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
    | "-n" :: more | "--no-build" :: more => build := false; it := more
    | a :: _ => IO.eprintln s!"scripts-verify-spec-annotations: unrecognized argument '{a}'\n{usage}"; return 2
  run root specFile specUrl leanRoot build

end Scripts.Spec.Main

public def main (args : List String) : IO UInt32 := Scripts.Spec.Main.cli args
