module

@[expose] public section Blanket

/-!
# Scripts.Ledger — the Rule 9 ledger and its gate logic

Rule 9 (`Blueprint/06-discipline.md`): every script this repository runs
is a Lean program; no new `scripts/*.py`.  `scripts/scripts-ledger.txt`
is the record of the Python that still exists, one row per script:

```
# open: 85
scripts/flip_census.py | I | todo
scripts/repin.py | I | lean:scripts-repin
inline:.github/workflows/test-coverage.yml:python3 - | G | todo
```

A row key is a `.py` path under `scripts/` or `inline:<file>:<command prefix>` for a
`python3 -c …` / `python3 - <<EOF` site in a shell wrapper or workflow.
Class is the plan's (`Blueprint/09-scripts-in-lean.md` §1): `G` gate,
`I` instrument, `F` flip/price, `R` report.  Status is `todo`,
`lean:<exe>` (ported; the Python is deleted and `<exe>` is a `lean_exe`
in `lakefile.lean`) or `exception:<reason>` (plan §4).

The `# open: N` header pins the number of open rows (`todo` +
`exception`).  The gate requires the count to equal the pin, so the pin
is a reading and not a ceiling: a conversion lowers it in the same PR, a
new Python script cannot land without raising it, and the raise is
visible in the diff — the ledger may only shrink.

This module is the pure half: parsers for the two line shapes (a ledger
row, a shell/YAML line that invokes `python`) and the check over the
inventory an `IO` driver collects (`Scripts/Main/CheckScriptsLedger.lean`).
Every parser has `#guard` rows below taken from the tree.
-/

namespace Scripts.Ledger

/-- The plan's four classes of script (§1). -/
inductive Class where
  | G | I | F | R
  deriving DecidableEq, Repr, Inhabited

def Class.parse? : String → Option Class
  | "G" => some .G
  | "I" => some .I
  | "F" => some .F
  | "R" => some .R
  | _ => none

def Class.render : Class → String
  | .G => "G" | .I => "I" | .F => "F" | .R => "R"

/-- Status of a row: still Python, ported to the named `lean_exe`, or a
listed exception. -/
inductive Status where
  | todo
  | lean (exe : String)
  | exception (reason : String)
  deriving DecidableEq, Repr, Inhabited

/-- `todo` and `exception` rows are the Python that still exists; they
are what the `# open:` pin counts. -/
def Status.isOpen : Status → Bool
  | .todo => true
  | .exception _ => true
  | .lean _ => false

def Status.parse? (s : String) : Option Status :=
  if s == "todo" then some .todo
  else if s.startsWith "lean:" then
    let exe := String.ofList (s.toList.drop 5)
    if exe.isEmpty then none else some (.lean exe)
  else if s.startsWith "exception:" then
    let reason := String.ofList (s.toList.drop 10)
    if reason.isEmpty then none else some (.exception reason)
  else none

def Status.render : Status → String
  | .todo => "todo"
  | .lean exe => s!"lean:{exe}"
  | .exception r => s!"exception:{r}"

#guard Status.parse? "todo" == some .todo
#guard Status.parse? "lean:scripts-repin" == some (.lean "scripts-repin")
#guard Status.parse? "exception:weasyprint" == some (.exception "weasyprint")
#guard Status.parse? "lean:" == none
#guard Status.parse? "done" == none
#guard (Status.lean "scripts-flip").render == "lean:scripts-flip"

/-- One ledger row. -/
structure Row where
  key : String
  cls : Class
  status : Status
  deriving DecidableEq, Repr, Inhabited

/-- Prefix of an inline-Python row key. -/
def inlinePrefix : String := "inline:"

def Row.isInline (r : Row) : Bool := r.key.startsWith inlinePrefix

def Row.render (r : Row) : String :=
  s!"{r.key} | {r.cls.render} | {r.status.render}"

/-- The parsed ledger: the pinned open-row count and the rows in file order. -/
structure Ledger where
  pin : Nat
  rows : Array Row
  deriving DecidableEq, Repr, Inhabited

def trim (s : String) : String := s.trimAscii.toString

/-- A row line: `key | class | status`, blanks around the bars ignored.  The
last two bars separate; an inline key may itself contain `|`. -/
def parseRow (line : String) : Except String Row :=
  match (line.splitOn "|").map trim |>.reverse with
  | st :: c :: keyParts@(_ :: _) =>
    let key := " | ".intercalate keyParts.reverse
    if key.isEmpty then .error s!"empty key in row `{line}`"
    else match Class.parse? c, Status.parse? st with
      | some cls, some status => .ok { key, cls, status }
      | none, _ => .error s!"unknown class `{c}` in row `{line}` (G|I|F|R)"
      | _, none => .error s!"unknown status `{st}` in row `{line}` (todo | lean:<exe> | exception:<reason>)"
  | _ => .error s!"a row has the shape `path | class | status`: `{line}`"

#guard (parseRow "scripts/repin.py | I | todo").toOption == some ⟨"scripts/repin.py", .I, .todo⟩
#guard (parseRow "scripts/repin.py|I|lean:scripts-repin").toOption == some ⟨"scripts/repin.py", .I, .lean "scripts-repin"⟩
#guard (parseRow "inline:.github/workflows/test-coverage.yml:python3 - | G | todo").toOption
  == some ⟨"inline:.github/workflows/test-coverage.yml:python3 -", .G, .todo⟩
#guard (parseRow "inline:scripts/w.sh:python3 -c \"a | b\" | R | todo").toOption
  == some ⟨"inline:scripts/w.sh:python3 -c \"a | b\"", .R, .todo⟩
#guard (parseRow "scripts/a.py | todo").toOption == none
#guard (parseRow "scripts/repin.py | X | todo").toOption == none
#guard (parseRow "scripts/repin.py | I").toOption == none
#guard (parseRow (Row.render ⟨"scripts/a.py", .F, .exception "attic"⟩)).toOption == some ⟨"scripts/a.py", .F, .exception "attic"⟩

/-- The pin header: a comment line `# open: N`. -/
def parsePinLine (line : String) : Option Nat :=
  let body := trim line
  if body.startsWith "#" then
    let rest := trim (String.ofList (body.toList.drop 1))
    if rest.startsWith "open:" then
      (trim (String.ofList (rest.toList.drop 5))).toNat?
    else none
  else none

#guard parsePinLine "# open: 85" == some 85
#guard parsePinLine "#open:0" == some 0
#guard parsePinLine "# open: many" == none
#guard parsePinLine "# a comment" == none
#guard parsePinLine "scripts/a.py | F | todo" == none

/-- Parse the whole file.  Blank lines and `#` comments are skipped; exactly
one `# open: N` header is required. -/
def parseLedger (text : String) : Except String Ledger := do
  let mut pin : Option Nat := none
  let mut rows : Array Row := #[]
  let mut lineNo := 0
  for raw in text.splitOn "\n" do
    lineNo := lineNo + 1
    let line := trim raw
    if line.isEmpty then continue
    if line.startsWith "#" then
      match parsePinLine line with
      | some n =>
        if pin.isSome then throw s!"line {lineNo}: a second `# open:` header"
        pin := some n
      | none => continue
    else
      match parseRow line with
      | .ok r => rows := rows.push r
      | .error e => throw s!"line {lineNo}: {e}"
  match pin with
  | none => throw "no `# open: N` header (the pinned count of todo + exception rows)"
  | some p => return { pin := p, rows }

def Ledger.openCount (l : Ledger) : Nat :=
  (l.rows.filter (·.status.isOpen)).size

#guard (parseLedger "# ledger\n# open: 2\n\nscripts/a.py | F | todo\nscripts/b.py | G | lean:x\nscripts/c.py | R | exception:pdf\n").toOption
  == some { pin := 2, rows := #[⟨"scripts/a.py", .F, .todo⟩, ⟨"scripts/b.py", .G, .lean "x"⟩, ⟨"scripts/c.py", .R, .exception "pdf"⟩] }
#guard ((parseLedger "# open: 2\nscripts/a.py | F | todo\nscripts/b.py | G | lean:x\nscripts/c.py | R | exception:pdf\n").toOption.map Ledger.openCount) == some 2
/-! ## Python invocations in shell and workflow text

The scan is shell-shaped, not line-shaped: `\`-continued physical lines
are one logical command line; a quoted string is one word that carries
its quotes (`"import weasyprint"`), with inner blanks collapsed; a word
beginning inside an open quote is never a command; an interpreter counts
only in *command position* — first word of a simple command, after `|`,
`||`, `&&`, `;`, `(`, `{`, `$(`, `!`, after `if`/`then`/`else`/`elif`/
`do`/`while`/`until`/`exec`/`command`/`time`/`nohup`/`env`, after a
`VAR=val` prefix, or after a YAML key (`run:`) at the head of the line.
A top-level word starting with `#` ends the line (a comment).  The
interpreter is `python`, `python3`, a path ending in one, or `$NAME` /
`"$NAME"` / `${NAME}` for a `NAME=…python3` assignment found anywhere in
the same file. -/

/-- What one interpreter word in command position is followed by.  `cmd`
is the command prefix: the interpreter word and its arguments up to the
first shell operator (`|`, `&&`, `;`, a redirect, a heredoc), blanks
collapsed — the text an inline row is keyed by. -/
inductive PyCall where
  /-- `python3 scripts/x.py …` — the target is a file. -/
  | script (path : String)
  /-- `python3 -c …` or `python3 - …` — inline code; row `inline:<file>:<cmd>`. -/
  | inline (cmd : String)
  /-- `python3 -m <module> …` — a module run; allowed only when §4 covers it. -/
  | moduleRun (cmd : String)
  /-- `python3 --version`, `command -v python3`, … — no code runs. -/
  | none
  deriving DecidableEq, Repr, Inhabited

/-- Split on blanks, dropping empties; quotes and operators stay in the words. -/
def rawWords (line : String) : List String :=
  (line.splitOn " ").flatMap (·.splitOn "\t") |>.filter (!·.isEmpty)

#guard rawWords "  if python3 -c \"import weasyprint\" 2>/dev/null; then" ==
  ["if", "python3", "-c", "\"import", "weasyprint\"", "2>/dev/null;", "then"]

def stripQuotes (w : String) : String :=
  String.ofList (w.toList.filter fun c => c != '"' && c != '\'')

def isBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

/-- A shell word with the physical line it starts on and whether it starts
inside an open quote (then it is the tail of a quoted argument). -/
structure TWord where
  text : String
  line : Nat
  inQuote : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The shell reading of a whole file: a list of logical command lines,
each a list of words.  Quotes bind across physical lines (`"a` ⏎ `b"` is
one word; inner blanks and newlines collapse to one space); `\x` is
literal and `\`⏎ (unquoted or in `"…"`) is a continuation; an unquoted
newline ends the command; `#` at a word start comments out the rest of
the physical line; a heredoc body (`<<EOF` … `EOF`) is skipped.  Each
word carries the physical line it starts on. -/
def tokenizeShell (text : String) : List (List TWord) := Id.run do
  let mut out : Array (List TWord) := #[]
  let mut cur : Array TWord := #[]
  let mut acc : Array Char := #[]
  let mut q : Option Char := none
  let mut ln := 1
  let mut wordLine := 1
  let mut wordInQuote := false
  let mut cs := text.toList
  let mut skipLine := false              -- inside a `#` comment
  let mut heredoc : Option String := none -- terminator of the body being skipped
  let mut lineStart := true
  while !cs.isEmpty do
    match cs with
    | [] => pure ()
    | c :: rest =>
      cs := rest
      -- heredoc body: swallow whole physical lines until the terminator
      if let some term := heredoc then
        if c == '\n' then
          ln := ln + 1; lineStart := true
        else if lineStart then
          let (lineChars, rest') := (c :: rest).span (· != '\n')
          cs := rest'
          lineStart := false
          if (String.ofList lineChars).trimAscii.toString == term then heredoc := none
        continue
      if skipLine then
        if c == '\n' then
          skipLine := false
          cs := c :: rest   -- let the newline end the command below
        continue
      if acc.isEmpty then
        wordLine := ln
        wordInQuote := q.isSome
      match q with
      | none =>
        if c == '\n' then
          if !acc.isEmpty then
            cur := cur.push ⟨String.ofList acc.toList, wordLine, wordInQuote⟩; acc := #[]
          if !cur.isEmpty then
            out := out.push cur.toList
            heredoc := heredocTerminator cur.toList
            cur := #[]
          ln := ln + 1; lineStart := true
        else if isBlank c then
          if !acc.isEmpty then
            cur := cur.push ⟨String.ofList acc.toList, wordLine, wordInQuote⟩; acc := #[]
        else if c == '#' && acc.isEmpty then
          skipLine := true
        else if c == '(' || c == ')' then
          -- unquoted parens are syntax: `$(` opens a substitution, `(`/`)` a subshell
          if c == '(' && acc.back? == some '$' then
            acc := acc.pop
            if !acc.isEmpty then
              cur := cur.push ⟨String.ofList acc.toList, wordLine, wordInQuote⟩; acc := #[]
            cur := cur.push ⟨"$(", ln, false⟩
          else
            if !acc.isEmpty then
              cur := cur.push ⟨String.ofList acc.toList, wordLine, wordInQuote⟩; acc := #[]
            cur := cur.push ⟨String.singleton c, ln, false⟩
        else if c == '"' || c == '\'' then
          acc := acc.push c; q := some c
        else if c == '\\' then
          match rest with
          | '\n' :: rest' => cs := rest'; ln := ln + 1        -- continuation
          | d :: rest' => acc := acc.push c |>.push d; cs := rest'
          | [] => acc := acc.push c
        else acc := acc.push c
      | some qc =>
        if c == qc then
          acc := acc.push c; q := none
        else if c == '\n' then
          ln := ln + 1
          if acc.back? != some ' ' then acc := acc.push ' '
        else if isBlank c then
          if acc.back? != some ' ' then acc := acc.push ' '
        else if c == '\\' && qc == '"' then
          match rest with
          | '\n' :: rest' => cs := rest'; ln := ln + 1
          | d :: rest' => acc := acc.push c |>.push d; cs := rest'
          | [] => acc := acc.push c
        else acc := acc.push c
  if !acc.isEmpty then
    cur := cur.push ⟨(String.ofList acc.toList).trimAsciiEnd.toString, wordLine, wordInQuote⟩
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList
where
  /-- `<<EOF`, `<<'EOF'`, `<<\EOF`, `<<-EOF`, `<< EOF` (not `<<<`) → the body's
  terminator: the delimiter word after shell quote removal (quotes and `\`
  escapes dropped), cut at a trailing control operator (`;`, `|`, `&`, a
  redirect) that the tokenizer left attached to it. -/
  heredocTerminator (ws : List TWord) : Option String :=
    let rec go : List TWord → Option String
      | [] => none
      | w :: rest =>
        if w.text.startsWith "<<" && !w.text.startsWith "<<<" then
          let after := (w.text.toList.drop 2).dropWhile (· == '-')
          let raw := if after.isEmpty then (rest.head?.map (·.text.toList)).getD [] else after
          let t := delimiter raw
          if t.isEmpty then none else some t
        else go rest
    go ws
  /-- Shell quote removal on a delimiter word, stopping at an unquoted control
  operator character. -/
  delimiter (cs : List Char) : String :=
    let rec go : List Char → Option Char → List Char → List Char
      | [], _, acc => acc.reverse
      | c :: rest, some qc, acc => if c == qc then go rest none acc else go rest (some qc) (c :: acc)
      | c :: rest, none, acc =>
        if c == '"' || c == '\'' then go rest (some c) acc
        else if c == '\\' then (match rest with | d :: r => go r none (d :: acc) | [] => acc.reverse)
        else if c == ';' || c == '|' || c == '&' || c == '<' || c == '>' || c == ')' then acc.reverse
        else go rest none (c :: acc)
    String.ofList (go cs none [])

def wordsOfLine (line : String) : List String := ((tokenizeShell line).headD []).map (·.text)

#guard wordsOfLine "  if python3 -c \"import  weasyprint\" 2>/dev/null; then" ==
  ["if", "python3", "-c", "\"import weasyprint\"", "2>/dev/null;", "then"]
#guard wordsOfLine "echo \"python3 scripts/new.py\"" == ["echo", "\"python3 scripts/new.py\""]
#guard wordsOfLine "python3 -c \"print(\\\"a\\\")\"" == ["python3", "-c", "\"print(\\\"a\\\")\""]
#guard wordsOfLine "| python3 -c \"" == ["|", "python3", "-c", "\""]
#guard wordsOfLine "ls scripts  # python3 scripts/x.py runs it" == ["ls", "scripts"]
#guard wordsOfLine "x=$(python3 --version) (cd a)" == ["x=", "$(", "python3", "--version", ")", "(", "cd", "a", ")"]
-- a quote spans physical lines without a continuation; words keep their start line
#guard tokenizeShell "echo 'a\nb' python3 x.py\nls" ==
  [[⟨"echo", 1, false⟩, ⟨"'a b'", 1, false⟩, ⟨"python3", 2, false⟩, ⟨"x.py", 2, false⟩], [⟨"ls", 3, false⟩]]
-- `\`⏎ continues (unquoted and in double quotes); `\\`⏎ is a literal backslash and the line ends
#guard (tokenizeShell "python3 \\\n  -c 'print(1)'").map (·.map (·.text)) == [["python3", "-c", "'print(1)'"]]
#guard (tokenizeShell "echo \\\\\npython3 -c 1").map (·.map (·.text)) == [["echo", "\\\\"], ["python3", "-c", "1"]]
#guard (tokenizeShell "echo \\\\\\\npython3 -c 1").map (·.map (·.text)) == [["echo", "\\\\python3", "-c", "1"]]
#guard (tokenizeShell "echo \"a \\\nb\"").map (·.map (·.text)) == [["echo", "\"a b\""]]
-- an even backslash run inside an open quote: the quote stays open across the newline
#guard tokenizeShell "echo \"hello \\\\\npython3 -c 'print(1)'\n\"\nls" ==
  [[⟨"echo", 1, false⟩, ⟨"\"hello \\\\ python3 -c 'print(1)' \"", 1, false⟩], [⟨"ls", 4, false⟩]]
-- heredoc bodies are skipped; the command line keeps its words; `<<<` is not a heredoc
#guard (tokenizeShell "python3 - <<'EOF'\nimport sys\nprint('python3 scripts/x.py')\nEOF\nls").map (·.map (·.text)) ==
  [["python3", "-", "<<'EOF'"], ["ls"]]
#guard (tokenizeShell "cat <<-EOF | tee x\n\tpython3 scripts/a.py\nEOF\n").map (·.map (·.text)) == [["cat", "<<-EOF", "|", "tee", "x"]]
#guard (tokenizeShell "read -r a <<<\"$x\"\npython3 scripts/a.py").map (·.map (·.text)) == [["read", "-r", "a", "<<<\"$x\""], ["python3", "scripts/a.py"]]
-- delimiter forms (review finding): `<<\EOF`, `<<EOF;`, `<<'EOF' |`, `<< EOF`, `<<"E O F"` all end at their line
#guard (tokenizeShell "cat <<\\EOF\nhello\nEOF\npython3 -c 1").map (·.map (·.text)) == [["cat", "<<\\EOF"], ["python3", "-c", "1"]]
#guard (tokenizeShell "cat <<EOF; echo x\nhello\nEOF\npython3 -c 1").map (·.map (·.text)) == [["cat", "<<EOF;", "echo", "x"], ["python3", "-c", "1"]]
#guard (tokenizeShell "cat <<'EOF' | tee x\nhello\nEOF\npython3 -c 1").map (·.map (·.text)) == [["cat", "<<'EOF'", "|", "tee", "x"], ["python3", "-c", "1"]]
#guard (tokenizeShell "cat << EOF\nhello\nEOF\npython3 -c 1").map (·.map (·.text)) == [["cat", "<<", "EOF"], ["python3", "-c", "1"]]
#guard (tokenizeShell "cat <<EOF>out\nhello\nEOF\npython3 -c 1").map (·.map (·.text)) == [["cat", "<<EOF>out"], ["python3", "-c", "1"]]
#guard (tokenizeShell "cat <<-\"E O F\"\nhello\nE O F\npython3 -c 1").map (·.map (·.text)) == [["cat", "<<-\"E O F\""], ["python3", "-c", "1"]]
-- comments end at the physical line
#guard (tokenizeShell "# python3 scripts/a.py\nls").map (·.map (·.text)) == [["ls"]]

/-- `NAME=value` → `(NAME, value)` for a shell identifier `NAME`. -/
def assignment? (w : String) : Option (String × String) :=
  match w.splitOn "=" with
  | name :: v :: vs =>
    if !name.isEmpty && name.all (fun c => c.isAlphanum || c == '_') && !name.front.isDigit
    then some (name, "=".intercalate (v :: vs)) else none
  | _ => none

#guard assignment? "VPY=\"$RUNNER_TEMP/ci-venv/bin/python3\"" == some ("VPY", "\"$RUNNER_TEMP/ci-venv/bin/python3\"")
#guard assignment? "PYBASE=/usr/bin/python3.12" == some ("PYBASE", "/usr/bin/python3.12")
#guard assignment? "2>/dev/null" == none
#guard assignment? "a=b=c" == some ("a", "b=c")

/-- Is this word a literal interpreter?  `python`, `python3`, or a path
ending in one (`"$VENV/bin/python3"`); never `python3.12`, `python-ffi`. -/
def isPythonLiteral (raw : String) : Bool :=
  let w := stripQuotes raw
  !w.any (· == '=') && !w.any (· == '(') && !w.any (· == ')') &&
    (w == "python" || w == "python3" || w.endsWith "/python" || w.endsWith "/python3")

/-- `$NAME`, `"$NAME"`, `${NAME}` → `NAME`. -/
def varRef? (raw : String) : Option String :=
  let w := stripQuotes raw
  if w.startsWith "$" then
    let n := String.ofList ((w.toList.drop 1).filter fun c => c != '{' && c != '}')
    if !n.isEmpty && n.all (fun c => c.isAlphanum || c == '_') then some n else none
  else none

#guard varRef? "\"$VPY\"" == some "VPY"
#guard varRef? "${VPY}" == some "VPY"
#guard varRef? "$VENV/bin/python3" == none
#guard varRef? "python3" == none

/-- The interpreter test: a literal, or a reference to a variable assigned
an interpreter somewhere in the file (`vars`). -/
def isPythonWord (vars : List String) (raw : String) : Bool :=
  isPythonLiteral raw || (varRef? raw).any vars.contains

#guard isPythonWord [] "python3"
#guard isPythonWord [] "\"$VENV/bin/python3\""
#guard !isPythonWord [] "/usr/bin/python3.12"
#guard !isPythonWord [] "PYBASE=/usr/bin/python3"
#guard !isPythonWord [] "$(python3"
#guard !isPythonWord [] "python-ffi"
#guard isPythonWord ["VPY"] "\"$VPY\""
#guard !isPythonWord [] "\"$VPY\""
#guard !isPythonWord ["VPY"] "\"$VENV\""

/-- Variables assigned an interpreter anywhere in the text
(`VPY="$RUNNER_TEMP/ci-venv/bin/python3"`, `PYBASE=/usr/bin/python3`). -/
def interpreterVars (text : String) : List String :=
  (tokenizeShell text).flatMap fun ws =>
    ws.filterMap fun w =>
      if w.inQuote then none else
      let t := if w.text.endsWith ";" then String.ofList w.text.toList.dropLast else w.text
      match assignment? t with
      | some (n, v) => if isPythonLiteral v then some n else none
      | none => none

#guard interpreterVars "PYBASE=/usr/bin/python3.12\nif [ ! -x \"$PYBASE\" ]; then PYBASE=/usr/bin/python3; fi\nVPY=\"$RUNNER_TEMP/ci-venv/bin/python3\"\nX=1\n"
  == ["PYBASE", "VPY"]

/-- A word that ends the command: pipe, list operator, group, heredoc or redirect. -/
def isOperatorWord (w : String) : Bool :=
  w == "|" || w == "||" || w == "&&" || w == ";" || w == "\\" || w == "&" || w == "!" ||
  w == "{" || w == "}" || w == "(" || w == ")" || w == "$(" || w == "};" || w == ");" ||
  w.startsWith "<" || w.startsWith ">" ||
  (match w.toList with
   | d :: '>' :: _ => d.isDigit
   | _ => false)

#guard isOperatorWord "2>/dev/null;"
#guard isOperatorWord "<<'EOF'"
#guard isOperatorWord "|"
#guard !isOperatorWord "-c"
#guard !isOperatorWord "\"$REPORTS/stats.json\""

/-- After this word, is the next word in command position?  Control
operators and groups, the keywords that take a command, a word ending in
`;`, and a `VAR=val` prefix all put the next word there. -/
def opensCommand (w : String) : Bool :=
  w == "|" || w == "||" || w == "&&" || w == ";" || w == "!" || w == "{" || w == "(" || w == "$(" ||
  w == "}" || w == ")" || w == "};" || w == ");" || w.endsWith ";" ||
  w == "if" || w == "then" || w == "else" || w == "elif" || w == "do" || w == "while" ||
  w == "until" || w == "exec" || w == "command" || w == "time" || w == "nohup" || w == "env" ||
  w == "fi" || w == "done" ||
  (assignment? w).isSome

#guard opensCommand "2>/dev/null;"
#guard opensCommand "exec"
#guard opensCommand "VPY=\"$X/python3\""
#guard !opensCommand "echo"
#guard !opensCommand "2>/dev/null"

/-- The words of the command starting at the interpreter: up to the first
operator word; a trailing `;` on a word ends it too (`then`, `fi`, … never
belong to the command). -/
def commandWords : List String → List String
  | [] => []
  | w :: rest =>
    if isOperatorWord w then []
    else if w.endsWith ";" then [String.ofList (w.toList.dropLast)]
    else w :: commandWords rest

#guard commandWords ["python3", "-c", "\"import weasyprint\"", "2>/dev/null;", "then"]
  == ["python3", "-c", "\"import weasyprint\""]
#guard commandWords ["python3", "-", "\"$REPORTS/stats.json\"", "<<'EOF'", "|", "tee"]
  == ["python3", "-", "\"$REPORTS/stats.json\""]

def stripDotSlash (p : String) : String :=
  if p.startsWith "./" then String.ofList (p.toList.drop 2) else p

/-- Classify the command words (the interpreter first). -/
def classifyCommand (cmd : List String) : PyCall :=
  match cmd with
  | _ :: w :: _ =>
    let text := " ".intercalate cmd
    if w == "-c" || w == "-" then .inline text
    else if w == "-m" then .moduleRun text
    else
      let p := stripDotSlash (String.ofList ((stripQuotes w).toList.reverse.dropWhile (· == ')')).reverse)
      if p.endsWith ".py" then .script p else .none
  | _ => .none

/-- One invocation found in the tree: the file, its 1-based line, the call. -/
structure Site where
  file : String
  line : Nat
  call : PyCall
  deriving DecidableEq, Repr, Inhabited

/-- The invocations of one logical line (words tagged with their physical
lines), with `vars` the file's interpreter variables.  The state is
"next word is in command position"; it starts true, a YAML key
(`run:`) or `-` at the head keeps it true. -/
def callsOfWords (vars : List String) (file : String) (ws : List TWord) : List Site :=
  let rec go (cmdPos : Bool) (first : Bool) : List TWord → List Site
    | [] => []
    | w :: rest =>
      if w.inQuote then go false false rest
      else
        let t := w.text
        if t.startsWith "#" then []
        else if first && (t.endsWith ":" || t == "-") then go true false rest
        else if cmdPos && isPythonWord vars t then
          let c := classifyCommand (commandWords (t :: rest.map (·.text)))
          let here := if c == .none then [] else [⟨file, w.line, c⟩]
          here ++ go false false rest
        else go (opensCommand t) false rest
  go true true ws

/-- Every python invocation in one line (no interpreter variables). -/
def pyCallsOfLine (line : String) : List PyCall :=
  (callsOfWords [] "" ((tokenizeShell line).headD [])).map (·.call)

def pyCallsOfLineWith (vars : List String) (line : String) : List PyCall :=
  (callsOfWords vars "" ((tokenizeShell line).headD [])).map (·.call)

#guard pyCallsOfLine "exec python3 scripts/check_closure_log.py" == [.script "scripts/check_closure_log.py"]
#guard pyCallsOfLine "exec python3 scripts/rename_lemma.py --check --whitelist scripts/capstones.txt L4YAML"
  == [.script "scripts/rename_lemma.py"]
#guard pyCallsOfLine "python3 scripts/check-serialization-axioms.py \"$work/qualification.log\" \"$work/sorry.log\""
  == [.script "scripts/check-serialization-axioms.py"]
#guard pyCallsOfLine "        run: python3 scripts/svg-objects.py doc/_out/html-multi" == [.script "scripts/svg-objects.py"]
#guard pyCallsOfLine "  python3 ./scripts/x.py" == [.script "scripts/x.py"]
#guard pyCallsOfLine "  \"$VENV/bin/python3\" \"scripts/x.py\" out" == [.script "scripts/x.py"]
#guard pyCallsOfLine "if python3 -c \"import weasyprint\" 2>/dev/null; then" == [.inline "python3 -c \"import weasyprint\""]
#guard pyCallsOfLine "     && python3 -c \"import weasyprint\" 2>/dev/null; }; then" == [.inline "python3 -c \"import weasyprint\""]
#guard pyCallsOfLine "             || { python3 -m pip install --quiet weasyprint" == [.moduleRun "python3 -m pip install --quiet weasyprint"]
#guard pyCallsOfLine "          python3 - <<'EOF'" == [.inline "python3 -"]
#guard pyCallsOfLine "  python3 - \"$REPORTS/stats.json\" <<'EOF' | tee -a \"$LOG\"" == [.inline "python3 - \"$REPORTS/stats.json\""]
#guard pyCallsOfLine "            | python3 -c \"" == [.inline "python3 -c \""]
#guard pyCallsOfLine "elif python3 -m pip install --quiet --disable-pip-version-check weasyprint 2>/dev/null"
  == [.moduleRun "python3 -m pip install --quiet --disable-pip-version-check weasyprint"]
#guard pyCallsOfLine "  python3 -m pytest Tests/test_python_ffi.py -v --tb=short" == [.moduleRun "python3 -m pytest Tests/test_python_ffi.py -v --tb=short"]
#guard pyCallsOfLine "x=$(python3 scripts/a.py) && python3 scripts/b.py" == [.script "scripts/a.py", .script "scripts/b.py"]
-- not invocations: probes, comments, assignments, loop lists, text
#guard pyCallsOfLine "echo \"python         $(python3 --version) ($(command -v python3))\"" == []
#guard pyCallsOfLine "          # GITHUB_PATH so every later `python3` — the pytest steps, the" == []
#guard pyCallsOfLine "ls scripts  # python3 scripts/x.py runs it" == []
#guard pyCallsOfLine "          PYBASE=/usr/bin/python3.12" == []
#guard pyCallsOfLine "  'python/l4yaml/__init__.py|__version__ = \"|\"'" == []
#guard pyCallsOfLine "  for rt in static python perl node ruby haskell dotnet lua; do" == []
-- quoted text in another command's argument is not a call (review finding)
#guard pyCallsOfLine "echo \"python3 scripts/new.py\"" == []
#guard pyCallsOfLine "echo 'usage: python3 scripts/new.py -h'" == []
#guard pyCallsOfLine "echo python3 scripts/new.py" == []
-- interpreter variables (review finding)
#guard pyCallsOfLineWith ["VPY"] "\"$VPY\" -c 'print(1)'" == [.inline "\"$VPY\" -c 'print(1)'"]
#guard pyCallsOfLineWith ["VPY"] "\"$VPY\" -m pip install --quiet pytest" == [.moduleRun "\"$VPY\" -m pip install --quiet pytest"]
#guard pyCallsOfLineWith ["VPY"] "\"$VPY\" --version" == []
#guard pyCallsOfLineWith [] "\"$VPY\" -c 'print(1)'" == []
#guard pyCallsOfLineWith ["VPY"] "echo \"$VPY\"" == []

/-- Module runs plan §4 covers without a ledger row: pytest over the shipped
binding's tests (`Tests/test_python_ffi.py`, `python/tests/`) or its
`--version` probe, and the installs that set that run up — `-m venv`,
`pip install` of the Q3 tool (`weasyprint`), of the test runner (`pytest`)
or of `pip` itself.  Anything else is a script. -/
def coveredModuleRun (cmd : String) : Bool :=
  match rawWords cmd with
  | _ :: "-m" :: "pytest" :: args =>
    args.any fun a => a == "Tests/test_python_ffi.py" || a.startsWith "python/tests" || a == "--version"
  | _ :: "-m" :: "pip" :: "install" :: args =>
    args.any fun a => a == "weasyprint" || a == "pytest" || a == "pip"
  | _ :: "-m" :: "venv" :: _ => true
  | _ => false

#guard coveredModuleRun "python3 -m pytest Tests/test_python_ffi.py -v --tb=short"
#guard coveredModuleRun "python3 -m pytest python/tests/ -v"
#guard coveredModuleRun "\"$VPY\" -m pytest --version"
#guard coveredModuleRun "python3 -m pip install --quiet --disable-pip-version-check weasyprint"
#guard coveredModuleRun "\"$VENV/bin/python3\" -m pip install --quiet --disable-pip-version-check --upgrade pip"
#guard coveredModuleRun "\"$VENV/bin/python3\" -m pip install --quiet --disable-pip-version-check pytest"
#guard coveredModuleRun "\"$PYBASE\" -m venv \"$RUNNER_TEMP/ci-venv\""
#guard !coveredModuleRun "python3 -m pytest scripts/"
#guard !coveredModuleRun "python3 -m pip install requests"
#guard !coveredModuleRun "python3 -m json.tool"

/-- The ledger key of an inline site: `inline:<file>:<command prefix>`. -/
def Site.inlineKey? (s : Site) : Option String :=
  match s.call with
  | .inline cmd => some s!"{inlinePrefix}{s.file}:{cmd}"
  | _ => none

#guard (Site.inlineKey? ⟨"scripts/w.sh", 3, .inline "python3 -c \"import weasyprint\""⟩)
  == some "inline:scripts/w.sh:python3 -c \"import weasyprint\""

/-- Scan a whole file's text; `file` is the path recorded on each site.
The text is read as shell (`tokenizeShell`); a site's line is the physical
line of its interpreter word. -/
def sitesOfText (file : String) (text : String) : Array Site :=
  let vars := interpreterVars text
  ((tokenizeShell text).flatMap (callsOfWords vars file)).toArray

#guard sitesOfText "f.sh" "#!/bin/bash\nexec python3 scripts/a.py\n"
  == #[⟨"f.sh", 2, .script "scripts/a.py"⟩]
-- continuation lines (review finding): a continued `-c` and a continued script call
#guard sitesOfText "f.sh" "python3 \\\n  -c 'print(1)'\n" == #[⟨"f.sh", 1, .inline "python3 -c 'print(1)'"⟩]
#guard sitesOfText "f.sh" "exec \\\n  python3 \\\n  scripts/a.py --flag\n" == #[⟨"f.sh", 2, .script "scripts/a.py"⟩]
#guard sitesOfText "f.sh" "python3 -c 'print(1)' \\\n  2>/dev/null\n" == #[⟨"f.sh", 1, .inline "python3 -c 'print(1)'"⟩]
-- two trailing backslashes are literal: the next line is its own command (review finding)
#guard sitesOfText "f.sh" "echo \\\\\npython3 -c 'print(1)'\n" == #[⟨"f.sh", 2, .inline "python3 -c 'print(1)'"⟩]
#guard sitesOfText "f.sh" "echo \\\\\\\npython3 -c 'print(1)'\n" == #[]
-- an open quote spans lines (review finding): quoted text is echo's argument, not a command;
-- a multi-line `python3 -c "…"` program is one word and the whole key
#guard sitesOfText "f.sh" "echo \"hello \\\\\npython3 -c 'print(1)'\n\"\n" == #[]
#guard sitesOfText "w.yml" "  | python3 -c \"\n  import sys\n  print(1)\n  \")\n" == #[⟨"w.yml", 1, .inline "python3 -c \" import sys print(1) \""⟩]
-- heredoc bodies are not commands
#guard sitesOfText "f.sh" "python3 - <<'EOF'\npython3 scripts/zz.py\nEOF\n" == #[⟨"f.sh", 1, .inline "python3 -"⟩]
-- a real command after each heredoc form is a site (review finding)
#guard sitesOfText "f.sh" "cat <<\\EOF\nhello\nEOF\npython3 -c 'print(1)'\n" == #[⟨"f.sh", 4, .inline "python3 -c 'print(1)'"⟩]
#guard sitesOfText "f.sh" "cat <<EOF; echo x\nhello\nEOF\npython3 scripts/a.py\n" == #[⟨"f.sh", 4, .script "scripts/a.py"⟩]
#guard sitesOfText "f.sh" "cat << EOF\npython3 scripts/zz.py\nEOF\npython3 scripts/a.py\n" == #[⟨"f.sh", 4, .script "scripts/a.py"⟩]
-- the workflow's three-line install probe keeps three sites on three lines
#guard sitesOfText "w.yml" "          if python3 -c \"import weasyprint\" 2>/dev/null \\\n             || { python3 -m pip install --quiet --disable-pip-version-check weasyprint \\\n                  && python3 -c \"import weasyprint\" 2>/dev/null; }; then\n"
  == #[⟨"w.yml", 1, .inline "python3 -c \"import weasyprint\""⟩,
       ⟨"w.yml", 2, .moduleRun "python3 -m pip install --quiet --disable-pip-version-check weasyprint"⟩,
       ⟨"w.yml", 3, .inline "python3 -c \"import weasyprint\""⟩]
-- interpreter variable resolved within the file (review finding)
#guard sitesOfText "w.yml" "VPY=\"$T/bin/python3\"\n\"$VPY\" -m pip install pytest\n\"$VPY\" -c 'print(1)'\n"
  == #[⟨"w.yml", 2, .moduleRun "\"$VPY\" -m pip install pytest"⟩, ⟨"w.yml", 3, .inline "\"$VPY\" -c 'print(1)'"⟩]
#guard sitesOfText "w.yml" "\"$VPY\" -c 'print(1)'\n" == #[]

/-! ## `lean_exe` names in `lakefile.lean` -/

/-- `lean_exe name where` / `lean_exe «name» where` → `name`. -/
def leanExeOfLine (line : String) : Option String :=
  match rawWords line with
  | "lean_exe" :: w :: _ =>
    let cs := w.toList.filter fun c => c != '«' && c != '»'
    if cs.isEmpty then none else some (String.ofList cs)
  | _ => none

#guard leanExeOfLine "lean_exe suiterunner where" == some "suiterunner"
#guard leanExeOfLine "lean_exe «l4yaml-fmt» where" == some "l4yaml-fmt"
#guard leanExeOfLine "@[default_target]" == none
#guard leanExeOfLine "lean_lib Scripts where" == none

def leanExesOfText (text : String) : Array String :=
  ((text.splitOn "\n").filterMap leanExeOfLine).toArray

/-! ## The check -/

/-- What the driver collected from the tree. -/
structure Inventory where
  /-- Every `.py` under `scripts/`, recursively, as `scripts/...` paths. -/
  pyFiles : Array String
  /-- Every python invocation in `scripts/*.sh` and `.github/workflows/*.yml`. -/
  sites : Array Site
  /-- Every `lean_exe` name in `lakefile.lean`. -/
  exes : Array String
  deriving Repr, Inhabited

/-- The inline sites with their ledger keys. -/
def Inventory.inlineSites (inv : Inventory) : Array (String × Site) :=
  inv.sites.filterMap fun s => s.inlineKey?.map (·, s)

/-- Current line numbers of the inline sites keyed `key`, for the report. -/
def Inventory.inlineLines (inv : Inventory) (key : String) : Array Nat :=
  (inv.inlineSites.filter (·.1 == key)).map (·.2.line)

structure Counts where
  pyFiles : Nat
  rows : Nat
  todo : Nat
  exception : Nat
  lean : Nat
  pin : Nat
  scriptCalls : Nat
  inlineCalls : Nat
  moduleCalls : Nat
  deriving Repr, DecidableEq, Inhabited

def Counts.render (c : Counts) : String :=
  s!"py={c.pyFiles} rows={c.rows} todo={c.todo} exception={c.exception} lean={c.lean} open={c.todo + c.exception} pin={c.pin} " ++
  s!"python-calls: script={c.scriptCalls} inline={c.inlineCalls} module={c.moduleCalls}"

def counts (l : Ledger) (inv : Inventory) : Counts :=
  { pyFiles := inv.pyFiles.size
    rows := l.rows.size
    todo := (l.rows.filter (·.status == .todo)).size
    exception := (l.rows.filter fun r => match r.status with | .exception _ => true | _ => false).size
    lean := (l.rows.filter fun r => match r.status with | .lean _ => true | _ => false).size
    pin := l.pin
    scriptCalls := (inv.sites.filter fun s => match s.call with | .script _ => true | _ => false).size
    inlineCalls := inv.inlineSites.size
    moduleCalls := (inv.sites.filter fun s => match s.call with | .moduleRun _ => true | _ => false).size }

/-- The gate.  Returns the list of violations; empty means green.

1. No duplicate `.py` row.  Inline rows are keyed by command text, so two
   identical invocations in one file (the two `import weasyprint` probes)
   are two rows with the same key: the rule for them is multiplicity —
   as many rows as sites (3).
2. Every `.py` under `scripts/` has a row (Rule 9: no new Python).
3. Every inline site (`python3 -c`, `python3 -`) has a row
   `inline:<file>:<command prefix>`, one per invocation line.
4. An open row (`todo`/`exception`) names a thing that exists: the file,
   or an inline site with that key.
5. A `lean:<exe>` row names a thing that is gone (the Python was deleted
   with the port) and an `<exe>` that `lakefile.lean` declares.
6. A `python3 scripts/x.py` call targets an open row — never a ported one,
   never an unlisted file.
7. A `python3 -m …` run is one plan §4 covers (`coveredModuleRun`).
8. The open-row count equals the `# open:` pin. -/
def check (l : Ledger) (inv : Inventory) : Array String := Id.run do
  let mut errs : Array String := #[]
  let keys := l.rows.map (·.key)
  -- 1
  let mut seen : Array String := #[]
  for k in keys do
    if !k.startsWith inlinePrefix then
      if seen.contains k then errs := errs.push s!"duplicate ledger row `{k}`"
      seen := seen.push k
  -- 2
  for f in inv.pyFiles do
    if !keys.contains f then
      errs := errs.push s!"`{f}` is not in the ledger (Rule 9: no new scripts/*.py; a .py that must exist gets a row)"
  -- 3 (multiplicity: rows with key k = sites with key k)
  let inlineKeys := inv.inlineSites.foldl (fun (acc : Array String) ks => if acc.contains ks.1 then acc else acc.push ks.1) #[]
  for k in inlineKeys do
    let nSites := (inv.inlineLines k).size
    let nRows := (keys.filter (· == k)).size
    if nRows < nSites then
      let near := (l.rows.filter fun r => r.key.startsWith s!"{inlinePrefix}{(inv.inlineSites.find? (·.1 == k)).map (·.2.file) |>.getD ""}:").map (·.key)
      let hint := if near.isEmpty then "" else s!" (inline rows for that file: {near.toList}; a changed command is a new row)"
      errs := errs.push s!"inline python at line(s) {(inv.inlineLines k).toList} has {nSites} site(s) and {nRows} ledger row(s) `{k}`{hint}"
    else if nRows > nSites then
      errs := errs.push s!"ledger has {nRows} row(s) `{k}` for {nSites} inline site(s) at line(s) {(inv.inlineLines k).toList} — remove the extra row(s) and lower the pin"
  -- 4, 5
  for r in l.rows do
    let exists_ :=
      if r.isInline then inlineKeys.contains r.key
      else inv.pyFiles.contains r.key
    match r.status with
    | .todo | .exception _ =>
      if !exists_ then
        errs := errs.push s!"ledger row `{r.key}` ({r.status.render}) names a file or inline command that does not exist — remove the row and lower the pin"
    | .lean exe =>
      if exists_ then
        errs := errs.push s!"ledger row `{r.key}` is `lean:{exe}` but the Python still exists — delete it with the port"
      if !inv.exes.contains exe then
        errs := errs.push s!"ledger row `{r.key}` names `lean:{exe}` but lakefile.lean declares no `lean_exe {exe}`"
  -- 6, 7
  for s in inv.sites do
    match s.call with
    | .script p =>
      match l.rows.find? (·.key == p) with
      | none => errs := errs.push s!"{s.file}:{s.line} runs `python3 {p}` which has no ledger row"
      | some r =>
        match r.status with
        | .lean exe => errs := errs.push s!"{s.file}:{s.line} still runs `python3 {p}`, ported as `lake exe {exe}`"
        | _ => pure ()
    | .moduleRun cmd =>
      if !coveredModuleRun cmd then
        errs := errs.push s!"{s.file}:{s.line} runs `{cmd}`, a module run plan §4 does not cover (pytest over the binding's tests; pip install of weasyprint, pytest or pip)"
    | _ => pure ()
  -- 8
  let open_ := l.openCount
  if open_ > l.pin then
    errs := errs.push s!"the ledger grew: {open_} open rows (todo + exception) against `# open: {l.pin}` — the ledger may only shrink"
  else if open_ < l.pin then
    errs := errs.push s!"the pin is stale: {open_} open rows against `# open: {l.pin}` — lower the pin to {open_}"
  return errs

section Guards

def probe : String := "python3 -c \"import weasyprint\""

def exampleLedger : Ledger :=
  { pin := 4
    rows := #[⟨"scripts/a.py", .F, .todo⟩,
              ⟨"scripts/b.py", .I, .lean "scripts-b"⟩,
              ⟨s!"inline:scripts/w.sh:{probe}", .R, .exception "probe"⟩,
              ⟨s!"inline:scripts/w.sh:{probe}", .R, .exception "probe"⟩,
              ⟨"inline:scripts/w.sh:python3 -", .G, .todo⟩] }

def exampleInventory : Inventory :=
  { pyFiles := #["scripts/a.py"]
    sites := #[⟨"scripts/w.sh", 2, .script "scripts/a.py"⟩,
               ⟨"scripts/w.sh", 3, .inline probe⟩,
               ⟨"scripts/w.sh", 5, .inline probe⟩,
               ⟨"scripts/w.sh", 9, .inline "python3 -"⟩]
    exes := #["scripts-b"] }

-- green
#guard check exampleLedger exampleInventory == #[]
#guard (counts exampleLedger exampleInventory) ==
  { pyFiles := 1, rows := 5, todo := 2, exception := 2, lean := 1, pin := 4, scriptCalls := 1, inlineCalls := 3, moduleCalls := 0 }
#guard exampleInventory.inlineLines s!"inline:scripts/w.sh:{probe}" == #[3, 5]
-- 1: a duplicate .py row
#guard (check { exampleLedger with pin := 5, rows := exampleLedger.rows.push ⟨"scripts/a.py", .F, .todo⟩ } exampleInventory).size == 1
-- 2: a new .py
#guard (check exampleLedger { exampleInventory with pyFiles := #["scripts/a.py", "scripts/new.py"] }).size == 1
-- 3: an inline site with a new command; a third probe site (2 rows, 3 sites); a moved line is still green
#guard (check exampleLedger { exampleInventory with sites := exampleInventory.sites.push ⟨"scripts/w.sh", 12, .inline "python3 -c \"print(1)\""⟩ }).size == 1
#guard (check exampleLedger { exampleInventory with sites := exampleInventory.sites.push ⟨"scripts/w.sh", 12, .inline probe⟩ }).size == 1
#guard check exampleLedger { exampleInventory with sites := exampleInventory.sites.map fun s => { s with line := s.line + 40 } } == #[]
-- 3/4: a probe site removed but both rows kept (one error: multiplicity; the key still exists)
#guard (check exampleLedger { exampleInventory with sites := exampleInventory.sites.erase ⟨"scripts/w.sh", 5, .inline probe⟩ }).size == 1
-- 4: an open row whose file / inline command is gone
#guard (check exampleLedger { exampleInventory with pyFiles := #[] }).size == 1
#guard (check exampleLedger { exampleInventory with sites := exampleInventory.sites.pop }).size == 1
-- 5: a lean row whose Python still exists / whose exe is not declared
#guard (check exampleLedger { exampleInventory with pyFiles := #["scripts/a.py", "scripts/b.py"] }).size == 1
#guard (check exampleLedger { exampleInventory with exes := #[] }).size == 1
-- 6: a wrapper still calls a ported script / an unlisted one
#guard (check exampleLedger { exampleInventory with sites := exampleInventory.sites.push ⟨"scripts/v.sh", 1, .script "scripts/b.py"⟩ }).size == 1
#guard (check exampleLedger { exampleInventory with sites := exampleInventory.sites.push ⟨"scripts/v.sh", 1, .script "scripts/zz.py"⟩ }).size == 1
-- 7: covered module runs pass, an uncovered one fails
#guard check exampleLedger { exampleInventory with sites := exampleInventory.sites.push ⟨"scripts/v.sh", 1, .moduleRun "python3 -m pytest python/tests/ -v"⟩ } == #[]
#guard (check exampleLedger { exampleInventory with sites := exampleInventory.sites.push ⟨"scripts/v.sh", 1, .moduleRun "python3 -m json.tool"⟩ }).size == 1
-- 8: pin too low (growth) and pin too high (stale)
#guard (check { exampleLedger with pin := 3 } exampleInventory).size == 1
#guard (check { exampleLedger with pin := 5 } exampleInventory).size == 1

end Guards

end Scripts.Ledger
