module

public import Scripts.Stats.Hygiene

/-!
# `lake run check-hygiene -- [STATS]` — zero sorries, zero custom axioms, kernel-accurate

Reads `collect-stats`'s `stats.json` (default `docs/reports/stats.json`) and prints the
heredoc's line — `env clean: N theorems, 0 sorries, 0 custom axioms` — or
`proof-hygiene gate failed: {…}` on stderr with exit 1.  Exit 2 when the file cannot be
read or has not the shape.
-/

namespace Scripts.CheckHygiene

open Scripts.Stats.Hygiene

def version : String := "scripts-check-hygiene 1.0 (Rule 9 phase 4 row 3)"

def usage : String := "usage: lake run check-hygiene -- [STATS] [-C ROOT]

  STATS            collect-stats' stats.json (default: docs/reports/stats.json under ROOT)
  -C, --root ROOT  repository root (default: the current directory)
  -h, --help / -V, --version

exit 0 clean; 1 a sorry or custom axiom in the compiled environment; 2 the file is unreadable."

def cli (args : List String) : IO UInt32 := do
  if args.any (fun a => a == "-h" || a == "--help") then IO.println usage; return 0
  if args.any (fun a => a == "-V" || a == "--version") then IO.println version; return 0
  let mut root : System.FilePath := "."
  let mut stats : Option String := none
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | ("-C" :: r :: more) | ("--root" :: r :: more) => root := r; rest := more
    | a :: more =>
      if a.startsWith "-" then IO.eprintln s!"{usage}\nerror: unrecognized argument: {a}"; return 2
      if stats.isSome then IO.eprintln s!"{usage}\nerror: one STATS file"; return 2
      stats := some a; rest := more
  let path := match stats with
    | some p => if System.FilePath.isAbsolute p then System.FilePath.mk p else root / p
    | none => root / "docs" / "reports" / "stats.json"
  let text ← try IO.FS.readFile path catch e => do IO.eprintln s!"{path}: {e}"; return 2
  match verdictOf text with
  | .ok line => IO.println line; return 0
  | .error e =>
    if e.startsWith "proof-hygiene gate failed" then IO.eprintln e; return 1
    IO.eprintln s!"{path}: {e}"; return 2

end Scripts.CheckHygiene

public def main (args : List String) : IO UInt32 := Scripts.CheckHygiene.cli args
