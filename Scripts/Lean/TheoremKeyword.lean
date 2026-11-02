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

/-- Every `theorem` keyword site in code: `(1-based line, declaration name)`. -/
partial def sites (text : String) : Array (Nat × String) :=
  go text.toList '\n' 1 0 false false #[]
where
  isKw : List Char → Bool
    | 't' :: 'h' :: 'e' :: 'o' :: 'r' :: 'e' :: 'm' :: _ => true
    | _ => false
  go (cs : List Char) (prev : Char) (line depth : Nat) (inLine inStr : Bool)
      (acc : Array (Nat × String)) : Array (Nat × String) :=
    match cs with
    | [] => acc
    | c :: rest =>
      let line' := if c == '\n' then line + 1 else line
      if inLine then go rest c line' depth (c != '\n') false acc
      else if depth > 0 then
        match cs with
        | '/' :: '-' :: t => go t '-' line (depth + 1) false false acc
        | '-' :: '/' :: t => go t '/' line (depth - 1) false false acc
        | _ => go rest c line' depth false false acc
      else if inStr then
        match cs with
        | '\\' :: e :: t => go t e (if e == '\n' then line + 1 else line) 0 false true acc
        | '"' :: t => go t '"' line 0 false false acc
        | _ => go rest c line' 0 false true acc
      else
        match cs with
        | '/' :: '-' :: t => go t '-' line 1 false false acc
        | '-' :: '-' :: t => go t '-' line 0 true false acc
        | '"' :: t => go t '"' line 0 false true acc
        | '\'' :: t =>
          if !isIdentChar prev then
            let (body, after) := match t with
              | '\\' :: e :: u => ([ '\\', e ], u)
              | e :: u => ([e], u)
              | [] => ([], [])
            match after with
            | '\'' :: u => go u '\'' (line + (body.count '\n')) 0 false false acc
            | _ => go t '\'' line 0 false false acc
          else go t '\'' line 0 false false acc
        | _ =>
          if isKw cs then
            let after := cs.drop 7
            let nxt := after.headD '\n'
            if !isIdentChar prev && prev != '.' && prev != '`' && (nxt == ' ' || nxt == '\t' || nxt == '\n') then
              let acc := match declNameAfter (after.dropWhile fun c => c == ' ' || c == '\t' || c == '\n') with
                | some name => acc.push (line, name)
                | none => acc
              go after 'm' line 0 false false acc
            else go rest c line' 0 false false acc
          else go rest c line' 0 false false acc

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

#guard sites "theorem foo : True := trivial" == #[(1, "foo")]
#guard sites "lemma foo : True := trivial" == #[]
#guard sites "/-- a theorem about x -/\ntheorem Foo.bar_baz' (n : Nat) : n = n := rfl" == #[(2, "Foo.bar_baz'")]
#guard sites "-- theorem commented\n\ntheorem «weird name».x : True := trivial" == #[(3, "weird name.x")]
#guard sites "def s := \"theorem in a string\"\ntheorem t : True := trivial" == #[(2, "t")]
#guard sites "def c := '\"'\ntheorem t : True := trivial" == #[(2, "t")]
#guard sites "def c := 'a'\ntheorem t : True := trivial" == #[(2, "t")]
#guard sites "/- outer /- nested theorem -/ still comment -/ theorem u : True := trivial" == #[(1, "u")]
#guard sites "Parser.Command.theorem\n`theorem\nmytheorem x\ntheorem_ x" == #[]
#guard sites "theorem\n  multi_line : True := trivial" == #[(1, "multi_line")]
#guard sites "theorem  (x) : True := trivial" == #[]     -- no identifier follows
#guard sites "def s := \"a \\\" theorem \\\" b\"\ntheorem v : True := trivial" == #[(2, "v")]
#guard sites "theorem a : True := trivial\ntheorem b.c : True := trivial" == #[(1, "a"), (2, "b.c")]
#guard parseWhitelist "# c\nL4YAML/X.lean:foo\n\nL4YAML/Y.lean:SIndent_*\n" == [("L4YAML/X.lean", "foo"), ("L4YAML/Y.lean", "SIndent_*")]
#guard allowed [("a.lean", "SIndent_*")] "a.lean" "SIndent_x" && !allowed [("a.lean", "SIndent_*")] "b.lean" "SIndent_x"
#guard allowed [("a.lean", "foo")] "a.lean" "foo" && !allowed [("a.lean", "foo")] "a.lean" "foo2"

end Scripts.Lean.TheoremKeyword
