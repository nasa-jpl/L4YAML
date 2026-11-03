module

public import Lean.Data.Json
public meta import Lean.Data.Json

/-!
# Scripts.Matrix.Score — the readings behind `lake run matrix-score`

The pure half of `scripts/matrix_score.py` (Rule 9 phase 4 row 2): the scorer of
the yaml-test-suite *data* form, exactly as http://matrix.yaml.info scores it.

* an error test (the directory has an `error` file) is correct iff the tester
  rejects it (exit code ≠ 0);
* a valid test on the event axis is correct iff the emitted events equal
  `test.event` after `normEvents` (trailing `\r` and trailing blank lines dropped);
* a valid test on the json axis is correct iff the emitted JSON stream equals
  `in.json` structurally (`pyEq`: `1` = `1.0`, objects compared by key).

The IO — the testers, the docker calls, the pool — is `Scripts.Main.MatrixScore`.
Every reading here is pinned by a `#guard` row.
-/

@[expose] public section

namespace Scripts.Matrix.Score

open Lean (Json JsonNumber)

/-- Python `str.rstrip(chars)`. -/
def rstrip (s : String) (p : Char → Bool) : String :=
  String.ofList (s.toList.reverse.dropWhile p).reverse

#guard rstrip "ab\r\r" (· == '\r') == "ab"
#guard rstrip "" (· == '/') == ""

/-- Python `norm_events`: split on `\n`, strip a trailing `\r` from each line, drop
    trailing empty lines. -/
def normEvents (text : String) : List String :=
  let lines := (text.splitOn "\n").map fun l => rstrip l (· == '\r')
  (lines.reverse.dropWhile (· == "")).reverse

#guard normEvents "+STR\n+DOC\r\n-DOC\n-STR\n\n\n" == ["+STR", "+DOC", "-DOC", "-STR"]
#guard normEvents "" == []
#guard normEvents "\n\na\n" == ["", "", "a"]

/-- Python `parse_json_stream`: a concatenated multi-document stream — values
    separated by JSON whitespace, each read by `Lean.Json.Parser.anyCore`
    (Python's `JSONDecoder.raw_decode`), to the end of the text. -/
def parseJsonStream (s : String) : Except String (List Json) :=
  let one : Std.Internal.Parsec.String.Parser Json := do
    let v ← Lean.Json.Parser.anyCore
    Std.Internal.Parsec.String.ws
    pure v
  let stream : Std.Internal.Parsec.String.Parser (List Json) := do
    Std.Internal.Parsec.String.ws
    let vs ← Std.Internal.Parsec.many one
    Std.Internal.Parsec.eof
    pure vs.toList
  Std.Internal.Parsec.String.Parser.run stream s

#guard (parseJsonStream "").toOption == some []
#guard (parseJsonStream " \n{\"a\": 1}\n[1, 2]\n\"s\"\nnull\n").toOption ==
  some [Json.mkObj [("a", 1)], Json.arr #[1, 2], Json.str "s", Json.null]
#guard (parseJsonStream "{\"a\": 1} }").toOption == none
#guard (parseJsonStream "[1,").toOption == none

/-- `1`, `1.0` and `1.00` are the same number: trailing zeros of the mantissa are
    traded against the exponent (Python compares the parsed floats). -/
def normNum (n : JsonNumber) : JsonNumber :=
  if n.mantissa == 0 then ⟨0, 0⟩ else go n n.exponent
where
  go (n : JsonNumber) : Nat → JsonNumber
    | 0 => n
    | k + 1 =>
      if n.exponent > 0 && n.mantissa % 10 == 0 then go ⟨n.mantissa / 10, n.exponent - 1⟩ k else n

#guard normNum ⟨100, 2⟩ == ⟨1, 0⟩
#guard normNum ⟨150, 2⟩ == ⟨15, 1⟩
#guard normNum ⟨-0, 3⟩ == ⟨0, 0⟩
#guard normNum ⟨100, 0⟩ == ⟨100, 0⟩

/-- Python `==` on two parsed JSON numbers: the previous scorer compared `json.loads`'s
    `float`s, so two decimals that round to the same binary64 are equal
    (`0.1 == 0.10000000000000001`); exact equality is kept beside it so two integers
    beyond 2⁵³ that differ compare unequal as in Python unless they round to the same
    double — the one residue, far outside any oracle's values. -/
def pyNumEq (a b : JsonNumber) : Bool :=
  normNum a == normNum b || a.toFloat == b.toFloat

#guard pyNumEq ⟨1, 1⟩ ⟨10000000000000001, 17⟩          -- 0.1 == 0.10000000000000001
#guard !pyNumEq ⟨1, 1⟩ ⟨11, 2⟩                          -- 0.1 ≠ 0.11
#guard pyNumEq ⟨1, 0⟩ ⟨100, 2⟩                          -- 1 == 1.00
#guard pyNumEq ⟨-15, 1⟩ ⟨-150, 2⟩                       -- -1.5 == -1.50
#guard !pyNumEq ⟨15, 1⟩ ⟨-15, 1⟩

/-- Python `==` on two parsed JSON values: structural, objects by key, numbers by
    `pyNumEq` — and `True == 1`, `False == 0` (`bool` is a subclass of `int`). -/
partial def pyEq : Json → Json → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => pyNumEq a b
  | .bool a, .num b | .num b, .bool a => pyNumEq b ⟨if a then 1 else 0, 0⟩
  | .str a, .str b => a == b
  | .arr a, .arr b => a.size == b.size && (a.zip b).all fun (x, y) => pyEq x y
  | .obj a, .obj b =>
    a.size == b.size && a.all fun k v => match b.get? k with
      | some w => pyEq v w
      | none => false
  | _, _ => false

/-- Python `got == exp` on two streams. -/
def streamsEq (a b : List Json) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => pyEq x y

def streamsEqText (a b : String) : Option Bool := do
  pure (streamsEq (← (parseJsonStream a).toOption) (← (parseJsonStream b).toOption))

#guard streamsEqText "{\"b\": [1.0, 2], \"a\": null}\n1" "1.0\n{\"a\": null, \"b\": [1, 2.00]}" == some false
#guard streamsEqText "{\"b\": [1.0, 2], \"a\": null}\n1" "{\"a\": null, \"b\": [1, 2.00]}\n1.0" == some true
#guard streamsEqText "{\"a\": 1}" "{\"a\": 1, \"b\": 2}" == some false
#guard streamsEqText "{\"a\": 1, \"b\": 2}" "{\"a\": 1}" == some false
#guard streamsEqText "[1, 2]" "[1, 2] 3" == some false
#guard streamsEqText "\"1\"" "1" == some false
#guard streamsEqText "true" "true" == some true
#guard streamsEqText "[0.1, 1e2]" "[0.10000000000000001, 100.0]" == some true
#guard streamsEqText "0.1" "0.2" == some false
#guard streamsEqText "true" "1" == some true
#guard streamsEqText "1.0" "true" == some true
#guard streamsEqText "false" "0.0" == some true
#guard streamsEqText "true" "2" == some false
#guard streamsEqText "false" "null" == some false
#guard streamsEqText "{\"enabled\": true}" "{\"enabled\": 1}" == some true
#guard streamsEqText "[true, 0]" "[1, false]" == some true
#guard streamsEqText "" "" == some true

/-- What the harness got back from a tester: it could not be started at all
    (Python's `rc is None`), the harness killed it (`TIMEOUT_RC`), or it exited. -/
inductive Rc where
  | unstarted
  | timeout
  | code (n : UInt32)
  deriving BEq, Repr

/-- Python `rc_category`: the category the exit code alone decides; `none` when the
    output must be compared.  `unstarted` first so a broken harness never scores
    `err-ok`; `timeout` before `isErr` — a killed tester rejected nothing. -/
def rcCategory (rc : Rc) (isErr : Bool) : Option String :=
  match rc with
  | .unstarted => some "harness-error"
  | .timeout => some "timeout"
  | .code n => if isErr then some (if n != 0 then "err-ok" else "err-miss")
               else if n != 0 then some "reject" else none

#guard rcCategory .unstarted true == some "harness-error"
#guard rcCategory .timeout true == some "timeout"
#guard rcCategory (.code 1) true == some "err-ok"
#guard rcCategory (.code 0) true == some "err-miss"
#guard rcCategory (.code 1) false == some "reject"
#guard rcCategory (.code 0) false == none

/-- Python `test_id`: the directory's last component, or the last two joined by `/`
    when the last is a variant number (`DK95/01`). -/
def testId (d : String) : String :=
  let parts := (System.FilePath.mk (rstrip d fun c => c == '/' || c == '\\')).components
  match parts.reverse with
  | last :: prev :: _ => if !last.isEmpty && last.all Char.isDigit then s!"{prev}/{last}" else last
  | [last] => last
  | [] => ""

#guard testId "data/229Q" == "229Q"
#guard testId "data/DK95/01/" == "DK95/01"
#guard testId "/abs/data/9MQT/01" == "9MQT/01"
#guard testId "229Q" == "229Q"

/-- The verdict once the tester exited 0 on a valid event test. -/
def eventVerdict (got exp : String) : String :=
  if normEvents got == normEvents exp then "pass" else "diff"

/-- The verdict once the tester exited 0 on a valid json test; malformed JSON is `diff`. -/
def jsonVerdict (got : String) (exp : List Json) : String :=
  match parseJsonStream got with
  | .ok g => if streamsEq g exp then "pass" else "diff"
  | .error _ => "diff"

#guard eventVerdict "+STR\n-STR\n" "+STR\r\n-STR\r\n\n" == "pass"
#guard eventVerdict "+STR\n" "+STR\n-STR\n" == "diff"
#guard jsonVerdict "{\"a\": 1.0}" [Json.mkObj [("a", 1)]] == "pass"
#guard jsonVerdict "{\"a\": " [Json.mkObj [("a", 1)]] == "diff"

/-- The categories the Python lists under `fails`. -/
def isFail (c : String) : Bool :=
  c == "diff" || c == "reject" || c == "err-miss" || c == "timeout" || c == "harness-error"

/-- `cats[cat] = cats.get(cat, 0) + 1`, insertion order kept (the JSON keeps it). -/
def bump (cats : List (String × Nat)) (c : String) : List (String × Nat) :=
  if cats.any (·.1 == c) then cats.map fun (k, n) => if k == c then (k, n + 1) else (k, n)
  else cats ++ [(c, 1)]

#guard bump (bump (bump [] "pass") "skip") "pass" == [("pass", 2), ("skip", 1)]

def pad (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)
def rjust (n : Nat) (w : Nat) : String := let s := toString n; "".pushn ' ' (w - s.length) ++ s

/-- Python `str(dict(sorted(cats.items())))`. -/
def pyDictRepr (cats : List (String × Nat)) : String :=
  let sorted := cats.toArray.qsort (fun a b => a.1 < b.1)
  "{" ++ ", ".intercalate (sorted.toList.map fun (k, n) => s!"'{k}': {n}") ++ "}"

#guard pyDictRepr [("pass", 308), ("err-ok", 94)] == "{'err-ok': 94, 'pass': 308}"
#guard pyDictRepr [] == "{}"

/-- The per-processor stderr line:
    `f"{pid:20s} {axis:5s}  correct={correct:3d}/{total:3d}  {dict(sorted(cats.items()))}"`,
    `correct = pass + err-ok`, `total` everything but `skip`. -/
def summaryLine (pid axis : String) (cats : List (String × Nat)) : String :=
  let get (k : String) : Nat := (cats.find? (·.1 == k)).map (·.2) |>.getD 0
  let correct := get "pass" + get "err-ok"
  let total := cats.foldl (fun n (k, c) => if k == "skip" then n else n + c) 0
  s!"{pad pid 20} {pad axis 5}  correct={rjust correct 3}/{rjust total 3}  {pyDictRepr cats}"

#guard summaryLine "L4YAML" "json" [("pass", 279), ("skip", 120), ("err-ok", 3)] ==
  "L4YAML               json   correct=282/282  {'err-ok': 3, 'pass': 279, 'skip': 120}"
#guard summaryLine "c-libfyaml" "event" [("harness-error", 402)] ==
  "c-libfyaml           event  correct=  0/402  {'harness-error': 402}"

/-- Python `json.dumps` of a `str` (`ensure_ascii=True`). -/
def pyJsonStr (s : String) : String :=
  let hex4 (n : Nat) : String :=
    let h := String.ofList (Nat.toDigits 16 n)
    "\\u" ++ "".pushn '0' (4 - h.length) ++ h
  s.foldl (init := "\"") (fun acc c =>
    acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\"
      else if c == '\n' then "\\n" else if c == '\r' then "\\r" else if c == '\t' then "\\t"
      else if c == '\x08' then "\\b" else if c == '\x0c' then "\\f"
      else if c.val < 0x20 || (c.val ≥ 0x7f && c.val < 0x10000) then hex4 c.toNat
      else if c.val ≥ 0x10000 then
        let v := c.toNat - 0x10000
        hex4 (0xD800 + v / 0x400) ++ hex4 (0xDC00 + v % 0x400)
      else c.toString)) ++ "\""

#guard pyJsonStr "a\"b\\c\n" == "\"a\\\"b\\\\c\\n\""
#guard pyJsonStr "é" == "\"\\u00e9\""
#guard pyJsonStr "😀" == "\"\\ud83d\\ude00\""

/-- One processor's axis reading: the categories (insertion order) and the fails. -/
structure AxisResult where
  cats : List (String × Nat)
  fails : List (String × String)
  deriving Repr

/-- `json.dump(results, indent=1)` of `{pid: {axis: {"cats": {...}, "fails": [[cat, id], …]}}}`. -/
def resultsJson (results : List (String × List (String × AxisResult))) : String :=
  let block (open_ close : String) (items : List String) (ind : String) : String :=
    if items.isEmpty then open_ ++ close else
    open_ ++ "\n" ++ ",\n".intercalate (items.map (ind ++ " " ++ ·)) ++ "\n" ++ ind ++ close
  let axisJson (r : AxisResult) (ind : String) : String :=
    block "{" "}"
      [ s!"\"cats\": " ++ block "{" "}" (r.cats.map fun (k, n) => s!"{pyJsonStr k}: {n}") (ind ++ " "),
        s!"\"fails\": " ++ block "[" "]" (r.fails.map fun (c, t) =>
          block "[" "]" [pyJsonStr c, pyJsonStr t] (ind ++ "  ")) (ind ++ " ") ] ind
  block "{" "}" (results.map fun (pid, axes) =>
    s!"{pyJsonStr pid}: " ++ block "{" "}" (axes.map fun (axis, r) =>
      s!"{pyJsonStr axis}: " ++ axisJson r "  ") " ") ""

#guard resultsJson [] == "{}"
#guard resultsJson [("L4YAML", [("event", ⟨[("pass", 308), ("err-ok", 94)], []⟩)])] ==
  "{\n \"L4YAML\": {\n  \"event\": {\n   \"cats\": {\n    \"pass\": 308,\n    \"err-ok\": 94\n   },\n   \"fails\": []\n  }\n }\n}"
#guard resultsJson [("c", [("json", ⟨[("harness-error", 1)], [("harness-error", "229Q")]⟩)]), ("d", [])] ==
  "{\n \"c\": {\n  \"json\": {\n   \"cats\": {\n    \"harness-error\": 1\n   },\n   \"fails\": [\n    [\n     \"harness-error\",\n     \"229Q\"\n    ]\n   ]\n  }\n },\n \"d\": {}\n}"

/-- argparse's `type=float` for `--timeout`, in whole milliseconds (floored): Python's
    float syntax — `5`, `5.0`, `.5`, `+2`, `1e-3`, `2.5E+1` — except `inf`/`nan`,
    negatives and anything beyond 10^12 s, which are no deadline. -/
def parseSeconds (s : String) : Option Nat := do
  let s := if s.startsWith "+" then (s.drop 1).toString else s
  let (num, exp) ← match s.splitOn "e" with
    | [n] => match n.splitOn "E" with
      | [n] => some (n, "0")
      | [n, e] => some (n, e)
      | _ => none
    | [n, e] => some (n, e)
    | _ => none
  let (whole, frac) ← match num.splitOn "." with
    | [w] => some (w, "")
    | [w, f] => some (w, f)
    | _ => none
  guard (!(whole.isEmpty && frac.isEmpty) && whole.all Char.isDigit && frac.all Char.isDigit)
  let digits ← (if whole.isEmpty && frac.isEmpty then none else (whole ++ frac).toNat?)
  let e : Int ← match exp.splitOn "-" with
    | [p] => (if p.startsWith "+" then (p.drop 1).toString else p).toNat?.map Int.ofNat
    | ["", n] => n.toNat?.map fun k => -(Int.ofNat k)
    | _ => none
  -- value·1000 = digits · 10^(e + 3 − |frac|); the power is never built for an exponent
  -- that cannot matter: zero digits or a shift below the digit count floor to 0 ms, and a
  -- deadline beyond 10^15 ms (a thousand millennia) is out of range
  let shift : Int := e + 3 - frac.length
  if digits == 0 then pure 0
  else if shift < -(Int.ofNat (toString digits).length) then pure 0
  else if shift > 15 then none
  else if shift ≥ 0 then pure (digits * 10 ^ shift.toNat) else pure (digits / 10 ^ (-shift).toNat)

#guard parseSeconds "5" == some 5000
#guard parseSeconds "5.0" == some 5000
#guard parseSeconds "0.25" == some 250
#guard parseSeconds ".5" == some 500
#guard parseSeconds "0.0015" == some 1
#guard parseSeconds "1e-3" == some 1
#guard parseSeconds "1e-4" == some 0
#guard parseSeconds "5E2" == some 500000
#guard parseSeconds ".5e1" == some 5000
#guard parseSeconds "2.5E+1" == some 25000
#guard parseSeconds "+2" == some 2000
#guard parseSeconds "abc" == none
#guard parseSeconds "" == none
#guard parseSeconds "." == none
#guard parseSeconds "-1" == none
#guard parseSeconds "1e" == none
#guard parseSeconds "inf" == none
#guard parseSeconds "1e-1000000000" == some 0
#guard parseSeconds "0e1000000000" == some 0
#guard parseSeconds "0.000e-999999999" == some 0
#guard parseSeconds "1e12" == some 1000000000000000
#guard parseSeconds "1e13" == none
#guard parseSeconds "1e1000000000" == none

/-- processor → (event tester, json tester) of the `yamlall` container, the Python's `DOCKER` table. -/
def dockerTesters : List (String × Option String × Option String) :=
  [ ("c-libfyaml",        some "c-libfyaml-event",        some "c-libfyaml-json"),
    ("c-libyaml",         some "c-libyaml-event",         none),
    ("cpp-yamlcpp",       some "cpp-yamlcpp-event",       none),
    ("dotnet-yamldotnet", some "dotnet-yamldotnet-event", some "dotnet-yamldotnet-json"),
    ("hs-hsyaml",         some "hs-hsyaml-event",         some "hs-hsyaml-json"),
    ("java-snakeyaml",    some "java-snakeyaml-event",    some "java-snakeyaml-json"),
    ("js-jsyaml",         none,                           some "js-jsyaml-json"),
    ("js-yaml",           some "js-yaml-event",           some "js-yaml-json"),
    ("lua-lyaml",         none,                           some "lua-lyaml-json"),
    ("nim-nimyaml",       some "nim-nimyaml-event",       none),
    ("perl-pp",           some "perl-pp-event",           some "perl-pp-json"),
    ("perl-pplibyaml",    some "perl-pplibyaml-event",    some "perl-pplibyaml-json"),
    ("perl-refparser",    some "perl-refparser-event",    none),
    ("perl-syck",         none,                           some "perl-syck-json"),
    ("perl-tiny",         none,                           some "perl-tiny-json"),
    ("perl-xs",           none,                           some "perl-xs-json"),
    ("perl-yaml",         none,                           some "perl-yaml-json"),
    ("py-pyyaml",         some "py-pyyaml-event",         some "py-pyyaml-json"),
    ("py-ruamel",         some "py-ruamel-event",         some "py-ruamel-json"),
    ("ruby-psych",        none,                           some "ruby-psych-json"),
    ("raku-yamlish",      none,                           some "raku-yamlish-json") ]

#guard dockerTesters.length == 21

end Scripts.Matrix.Score

end
