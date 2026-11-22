module

@[expose] public section Blanket

/-!
# Scripts.Lean.TheoremKeyword — `theorem` keyword sites in Lean source text

Rule 7 (`Blueprint/06-discipline.md`): the `theorem` keyword is reserved for
the `@[capstone]` declarations listed in `scripts/capstones.txt`; everything
else is `lemma`.  Formerly `scripts/rename_lemma.py`.

The scanner is comment-, string- and char-literal-aware: block comments
(slash-dash … dash-slash) nest, so doc comments are covered; `--` runs to end of line,
`"…"` is escape-aware and may span lines, `'c'` is a char literal only when
the `'` does not follow an identifier character (`foo'` stays an identifier,
`'"'` does not open a string).  A `theorem` token counts only in code, at a
token boundary, not preceded by `.` or `` ` `` (so `Parser.Command.theorem`
name literals and docstring prose are never sites), and only when an
identifier follows.

Whitelist format: one `relative/path.lean:name` per line, `#` comments, a
trailing `*` in the name is a prefix wildcard (`SIndent_*`).
-/

namespace Scripts.Lean.TheoremKeyword

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

def isNameStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == '«'

/-- The (possibly dot-qualified, possibly `«»`-quoted) identifier starting at
the head of `cs`, as the Python's `decl_name_after`. -/
partial def declNameAfter (cs : List Char) (acc : List String := []) : Option String :=
  let (part?, rest) :=
    match cs with
    | '«' :: t =>
      let inner := t.takeWhile (· != '»')
      if inner.length == t.length then (none, []) else (some (String.ofList inner), t.drop (inner.length + 1))
    | _ =>
      let id := cs.takeWhile isIdentChar
      if id.isEmpty then (none, cs) else (some (String.ofList id), cs.drop id.length)
  match part? with
  | none => none
  | some part =>
    let acc := acc ++ [part]
    match rest with
    | '.' :: c :: t => if isNameStart c then declNameAfter (c :: t) acc else some (".".intercalate acc)
    | _ => some (".".intercalate acc)

/-- One `theorem` keyword site in code: the keyword's character offset in the
file, its 1-based line, and the declaration name that follows. -/
structure Site where
  offset : Nat
  line : Nat
  name : String
  deriving Repr, BEq

/-- Every `theorem` keyword site in code, in source order. -/
partial def sites (text : String) : Array Site :=
  let cs := text.toList
  go cs.length cs '\n' 1 0 false false #[]
where
  isKw : List Char → Bool
    | 't' :: 'h' :: 'e' :: 'o' :: 'r' :: 'e' :: 'm' :: _ => true
    | _ => false
  go (total : Nat) (cs : List Char) (prev : Char) (line depth : Nat) (inLine inStr : Bool)
      (acc : Array Site) : Array Site :=
    match cs with
    | [] => acc
    | c :: rest =>
      let line' := if c == '\n' then line + 1 else line
      if inLine then go total rest c line' depth (c != '\n') false acc
      else if depth > 0 then
        match cs with
        | '/' :: '-' :: t => go total t '-' line (depth + 1) false false acc
        | '-' :: '/' :: t => go total t '/' line (depth - 1) false false acc
        | _ => go total rest c line' depth false false acc
      else if inStr then
        match cs with
        | '\\' :: e :: t => go total t e (if e == '\n' then line + 1 else line) 0 false true acc
        | '"' :: t => go total t '"' line 0 false false acc
        | _ => go total rest c line' 0 false true acc
      else
        match cs with
        | '/' :: '-' :: t => go total t '-' line 1 false false acc
        | '-' :: '-' :: t => go total t '-' line 0 true false acc
        | '"' :: t => go total t '"' line 0 false true acc
        | '\'' :: t =>
          if !isIdentChar prev then
            let (body, after) := match t with
              | '\\' :: e :: u => ([ '\\', e ], u)
              | e :: u => ([e], u)
              | [] => ([], [])
            match after with
            | '\'' :: u => go total u '\'' (line + (body.count '\n')) 0 false false acc
            | _ => go total t '\'' line 0 false false acc
          else go total t '\'' line 0 false false acc
        | _ =>
          if isKw cs then
            let after := cs.drop 7
            let nxt := after.headD '\n'
            if !isIdentChar prev && prev != '.' && prev != '`' && (nxt == ' ' || nxt == '\t' || nxt == '\n') then
              let acc := match declNameAfter (after.dropWhile fun c => c == ' ' || c == '\t' || c == '\n') with
                | some name => acc.push { offset := total - cs.length, line, name }
                | none => acc
              go total after 'm' line 0 false false acc
            else go total rest c line' 0 false false acc
          else go total rest c line' 0 false false acc

/-- `(line, name)` of every site — the shape the guards and reports read. -/
def siteLines (text : String) : Array (Nat × String) := (sites text).map fun s => (s.line, s.name)

/-- The text with `lemma` written over the 7-character `theorem` keyword at each
offset (ascending offsets, as `sites` reports them; the Python's `--apply`). -/
def rewriteAt (text : String) (offsets : Array Nat) : String := Id.run do
  let cs := text.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  for off in offsets do
    if off < i || off + 7 > cs.size then continue
    out := out ++ cs.extract i off ++ "lemma".toList.toArray
    i := off + 7
  out := out ++ cs.extract i cs.size
  return String.ofList out.toList

/-- Whitelist rows `(file, name)`; a trailing `*` is a prefix wildcard. -/
def parseWhitelist (text : String) : List (String × String) :=
  (text.splitOn "\n").filterMap fun raw =>
    let l := raw.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then none
    else match l.toList.reverse.dropWhile (· != ':') with
      | [] => none
      | _ :: fileRev =>
        let file := String.ofList fileRev.reverse
        let name := String.ofList (l.toList.reverse.takeWhile (· != ':')).reverse
        some (file, name)

def allowed (wl : List (String × String)) (file name : String) : Bool :=
  wl.any fun (f, w) =>
    f == file && (if w.endsWith "*" then name.startsWith (w.dropEnd 1) else name == w)

#guard siteLines "theorem foo : True := trivial" == #[(1, "foo")]
#guard siteLines "lemma foo : True := trivial" == #[]
#guard siteLines "/-- a theorem about x -/\ntheorem Foo.bar_baz' (n : Nat) : n = n := rfl" == #[(2, "Foo.bar_baz'")]
#guard siteLines "-- theorem commented\n\ntheorem «weird name».x : True := trivial" == #[(3, "weird name.x")]
#guard siteLines "def s := \"theorem in a string\"\ntheorem t : True := trivial" == #[(2, "t")]
#guard siteLines "def c := '\"'\ntheorem t : True := trivial" == #[(2, "t")]
#guard siteLines "def c := 'a'\ntheorem t : True := trivial" == #[(2, "t")]
#guard siteLines "/- outer /- nested theorem -/ still comment -/ theorem u : True := trivial" == #[(1, "u")]
#guard siteLines "Parser.Command.theorem\n`theorem\nmytheorem x\ntheorem_ x" == #[]
#guard siteLines "theorem\n  multi_line : True := trivial" == #[(1, "multi_line")]
#guard siteLines "theorem  (x) : True := trivial" == #[]     -- no identifier follows
#guard siteLines "def s := \"a \\\" theorem \\\" b\"\ntheorem v : True := trivial" == #[(2, "v")]
#guard siteLines "theorem a : True := trivial\ntheorem b.c : True := trivial" == #[(1, "a"), (2, "b.c")]
#guard (sites "/- theorem example -/ theorem actual : True := trivial").map (·.offset) == #[22]
#guard rewriteAt "/- theorem example -/ theorem actual : True := trivial" #[22]
  == "/- theorem example -/ lemma actual : True := trivial"
#guard rewriteAt "theorem a : T := t\ntheorem b : T := t\ntheorem c : T := t" #[0, 38]
  == "lemma a : T := t\ntheorem b : T := t\nlemma c : T := t"
#guard rewriteAt "x" #[0] == "x"
#guard parseWhitelist "# c\nL4YAML/X.lean:foo\n\nL4YAML/Y.lean:SIndent_*\n" == [("L4YAML/X.lean", "foo"), ("L4YAML/Y.lean", "SIndent_*")]
#guard allowed [("a.lean", "SIndent_*")] "a.lean" "SIndent_x" && !allowed [("a.lean", "SIndent_*")] "b.lean" "SIndent_x"
#guard allowed [("a.lean", "foo")] "a.lean" "foo" && !allowed [("a.lean", "foo")] "a.lean" "foo2"

end Scripts.Lean.TheoremKeyword
