module

public import Lean.Data.Json

/-!
# `scripts-release-asset NAME < release.json` — one field of a GitHub release

Prints the API `url` of the asset called NAME from the release JSON on stdin (what
`curl …/releases/tags/TAG` returns); `ERROR: asset not found` on stderr and exit 1
when no asset has that name, exit 2 when stdin is not a release.  This was the
`python3 -c` lookup in `test-coverage.yml`'s theorem-graph download step.
-/

namespace Scripts.ReleaseAsset

open Lean (Json)

def version : String := "scripts-release-asset 1.0 (Rule 9 phase 4 row 3)"

def usage : String := "usage: scripts-release-asset NAME < release.json

  prints the `url` of the release asset called NAME; exit 1 when there is none, 2 on bad JSON
  -h, --help / -V, --version"

/-- The asset's `url`, or `none`. -/
def assetUrl? (release : Json) (name : String) : Except String (Option String) := do
  let assets ← match release.getObjVal? "assets" with
    | .ok (.arr a) => pure a
    | .ok _ => throw "`assets` is not an array"
    | .error _ => pure #[]
  for a in assets do
    if let .ok n := a.getObjValAs? String "name" then
      if n == name then
        match a.getObjValAs? String "url" with
        | .ok u => return some u
        | .error _ => throw s!"asset {name} has no `url`"
  return none

def cli (args : List String) : IO UInt32 := do
  if args.any (fun a => a == "-h" || a == "--help") then IO.println usage; return 0
  if args.any (fun a => a == "-V" || a == "--version") then IO.println version; return 0
  let args := if args.headD "" == "-C" || args.headD "" == "--root" then args.drop 2 else args
  let [name] := args | IO.eprintln usage; return 2
  let text ← (← IO.getStdin).readToEnd
  match Json.parse text >>= (assetUrl? · name) with
  | .ok (some url) => IO.println url; return 0
  | .ok none => IO.eprintln "ERROR: asset not found"; return 1
  | .error e => IO.eprintln s!"ERROR: release JSON: {e}"; return 2

end Scripts.ReleaseAsset

public def main (args : List String) : IO UInt32 := Scripts.ReleaseAsset.cli args
