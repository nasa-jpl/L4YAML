module

public import L4YAML.Output.Align

@[expose] public section Blanket

/-!
# l4yaml-fmt — column-aligning YAML formatter

Aligns the values of `key: value` entries (and the nodes of
`key: &anchor value` entries) inside each block mapping, changing nothing
but the blanks after `:` and after node properties.  See
`L4YAML.Output.Align` for the policy and the guarantees.

## Usage

```
lake build l4yaml-fmt

# stdin → stdout
./.lake/build/bin/l4yaml-fmt < params.yaml

# rewrite files in place, cells rounded to multiples of 8
./.lake/build/bin/l4yaml-fmt -w -r 8 config/*.yaml

# CI: fail if any file would change
./.lake/build/bin/l4yaml-fmt --check config/*.yaml
```
-/

open L4YAML.Align

namespace L4YamlFmt

def version : String := "0.7.0"

def usage : String :=
s!"l4yaml-fmt {version} — column-align YAML mapping values (L4YAML)

Usage: l4yaml-fmt [options] [--] [file ...]

Without files, reads YAML from stdin and writes the aligned text to stdout.
With files, writes each aligned file to stdout unless -w or --check is given.

Options:
  -w, --write          rewrite each file in place (only files that change)
  -n, --check          exit 1 if any input would change; print its name
  -g, --group KIND     alignment group: 'mapping' (whole block mapping,
                       default) or 'run' (split mappings at blank lines)
  -c, --max-cell N     widest key cell (key start to value start) that is
                       aligned; wider keys keep the minimum gap (default 40)
  -r, --round N        pad cells to a multiple of N columns (default 1)
  -s, --gap N          minimum spaces after ':' and after a property
                       (default 1; must be at least 1)
  -V, --version        print the version and exit
  -h, --help           print this help and exit

Only blanks after ':' and after '&anchor' / '!tag' are changed; comments,
blank lines, block scalars, flow collections and quoting are kept verbatim.
The result is re-scanned and must produce the same tokens and comments,
otherwise the input is left unchanged and an error is reported.  Aliases
must be defined in the same input (the scanner rejects undefined aliases).

Exit status: 0 ok; 1 --check found a file that would change;
             2 usage error; 3 input rejected (does not scan, or refused)."

partial def readAll (h : IO.FS.Stream) (acc : String) : IO String := do
  let l ← h.getLine
  if l.isEmpty then pure acc else readAll h (acc ++ l)

/-- Format one input; `none` after reporting an error (exit status 3). -/
def formatInput (o : Options) (name text : String) : IO (Option String) := do
  match format o.cfg text with
  | .ok out => pure (some out)
  | .error e =>
    IO.eprintln s!"l4yaml-fmt: {name}: {e}"
    pure none


/-- Replace `f` with `out` through a sibling temporary file and a rename, so an
    interrupted or failed write never leaves `f` truncated. -/
def replaceFile (f : String) (out : String) : IO Bool := do
  let tmp := f ++ ".l4yaml-fmt.tmp"
  try
    IO.FS.writeFile tmp out
    IO.FS.rename tmp f
    pure true
  catch e =>
    IO.eprintln s!"l4yaml-fmt: {f}: {e}"
    try IO.FS.removeFile tmp catch _ => pure ()
    pure false

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error msg =>
    IO.eprintln s!"l4yaml-fmt: {msg}"
    return 2
  | .ok o =>
    if o.help then IO.println usage; return 0
    if o.showVersion then IO.println s!"l4yaml-fmt {version}"; return 0
    if o.write && o.check then
      IO.eprintln "l4yaml-fmt: -w/--write and -n/--check are mutually exclusive"; return 2
    let mut status : UInt32 := 0
    if o.files.isEmpty then
      if o.write then
        IO.eprintln "l4yaml-fmt: -w/--write needs file arguments"; return 2
      let text ← readAll (← IO.getStdin) ""
      match ← formatInput o "<stdin>" text with
      | none => return 3
      | some out =>
        if o.check then
          if out != text then IO.println "<stdin>: would be reformatted"; return 1
          return 0
        (← IO.getStdout).putStr out
        return 0
    for f in o.files do
      let read? ← try pure (some (← IO.FS.readFile f)) catch e =>
        IO.eprintln s!"l4yaml-fmt: {f}: {e}"; pure none
      match read? with
      | none => status := max status 3
      | some text =>
      match ← formatInput o f text with
      | none => status := max status 3
      | some out =>
        if o.check then
          if out != text then
            IO.println s!"{f}: would be reformatted"
            status := max status 1
        else if o.write then
          if out != text then
            if ← replaceFile f out then IO.eprintln s!"{f}: reformatted"
            else status := max status 3
        else
          (← IO.getStdout).putStr out
    return status

end L4YamlFmt

def main (args : List String) : IO UInt32 := L4YamlFmt.main args

end Blanket
