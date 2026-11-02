module

@[expose] public section Blanket

/-!
# Scripts.Lean.Regex — the regex subset `docs-nav grep` accepts

A small backtracking matcher, so `lake run docs-nav -- grep REGEX [-i]` takes
the same patterns `scripts/docs_nav.py grep` did without a regex dependency
(plan §6, Q1).  Supported: literals, `.`, classes `[a-z_]` / `[^…]` with
ranges and the escapes below, `\d \w \s \D \W \S \b \B`, anchors `^ $`,
groups `( )` (non-capturing in effect) and `(?: )`, alternation `|`, and the
quantifiers `* + ? {m} {m,} {m,n}`, each optionally lazy (`*?`).  `-i` folds
ASCII case.  `\A` / `\Z` are the string anchors (same as `^` / `$` here:
no multiline mode).  Literal escapes: `\n \t \r \f \v \a` and any escaped
non-alphanumeric character (`\. \* \- \\`).

**Boundary.**  This is the subset the repository's recorded searches use, not
Python's `re`; what is *not* supported is rejected at compile time (exit 2
with the reason), never reinterpreted: capturing semantics and
back-references (`\1`), `\x41` / `\u` / octal escapes, any other alphanumeric
escape (`\p`, `\h`, …; `\b` inside a class), look-around `(?=` `(?!` `(?<`,
inline flags `(?i)`, named groups, possessive quantifiers, Unicode classes
and case folding beyond ASCII.  A pattern that compiles matches as Python's
`re.search` would on one line.
-/

namespace Scripts.Lean.Regex

inductive Node where
  | chr (c : Char)
  | any
  | cls (neg : Bool) (items : List (Char × Char)) (escapes : List Char)   -- ranges and \d\w\s letters
  | esc (c : Char)                                                        -- \d \w \s \D \W \S
  | bol | eol | wordB | nonWordB
  | group (alts : List (List Node))
  | rep (n : Node) (lo : Nat) (hi : Option Nat) (lazy : Bool)
  deriving Repr, Inhabited

def isWord (c : Char) : Bool := c.isAlphanum || c == '_'
def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == '\x0b'

def escMatches (e : Char) (c : Char) : Bool :=
  match e with
  | 'd' => c.isDigit | 'D' => !c.isDigit
  | 'w' => isWord c | 'W' => !isWord c
  | 's' => isSpace c | 'S' => !isSpace c
  | _ => false

/-- The character an escape stands for; an alphanumeric escape this subset
does not define (`\x41`, `\1`, `\p`, …) is rejected, never read literally. -/
def escChar (e : Char) : Except String Char :=
  match e with
  | 'n' => pure '\n' | 't' => pure '\t' | 'r' => pure '\r' | 'f' => pure '\x0c'
  | 'v' => pure '\x0b' | 'a' => pure '\x07'
  | c => if c.isAlphanum then throw s!"unsupported escape `\\{c}`" else pure c

/-- After `{`: Python's `{m}`, `{m,}`, `{m,n}`, `{,n}`, `{,}` (an empty bound is
0 / unbounded); `{}` or anything else is not a quantifier and the `{` is literal. -/
def braceQuant? (t : List Char) : Option (Nat × Option Nat × List Char) :=
  let lo := t.takeWhile Char.isDigit
  let loN := if lo.isEmpty then 0 else (String.ofList lo).toNat!
  match t.drop lo.length with
  | '}' :: r => if lo.isEmpty then none else some (loN, some loN, r)
  | ',' :: r =>
    let hi := r.takeWhile Char.isDigit
    match r.drop hi.length with
    | '}' :: r' => some (loN, (if hi.isEmpty then none else some (String.ofList hi).toNat!), r')
    | _ => none
  | _ => none

mutual
  /-- Inside `[...]`, after the optional `^`: items until the closing `]`
  (a leading `]` is literal). -/
  partial def classGo (neg : Bool) (cs : List Char) (first : Bool) (items : List (Char × Char))
      (escs : List Char) : Except String (Node × List Char) :=
    match cs with
    | ']' :: t => if first then classGo neg t false (items ++ [(']', ']')]) escs else pure (.cls neg items escs, t)
    | [] => throw "missing ]"
    | '\\' :: e :: t =>
      if "dDwWsS".toList.contains e then classGo neg t false items (escs ++ [e])
      else do classItem neg (← escChar e) t items escs
    | c :: t => classItem neg c t items escs
  partial def classItem (neg : Bool) (c : Char) (t : List Char) (items : List (Char × Char))
      (escs : List Char) : Except String (Node × List Char) :=
    match t with
    | '-' :: d :: u =>
      if d == ']' then classGo neg t false (items ++ [(c, c)]) escs
      else do
        let (d, u) ← match d, u with
          | '\\', e :: u' => (escChar e).map (·, u')
          | _, _ => pure (d, u)
        classGo neg u false (items ++ [(c, d)]) escs
    | _ => classGo neg t false (items ++ [(c, c)]) escs
end

def parseClass (cs : List Char) : Except String (Node × List Char) :=
  match cs with
  | '^' :: t => classGo true t true [] []
  | _ => classGo false cs true [] []

mutual
  /-- alternation: `alts` -/
  partial def parseAlt (cs : List Char) : Except String (List (List Node) × List Char) := do
    let (seq, rest) ← parseSeq cs
    match rest with
    | '|' :: t => let (alts, r) ← parseAlt t; pure (seq :: alts, r)
    | _ => pure ([seq], rest)
  partial def parseSeq (cs : List Char) : Except String (List Node × List Char) := do
    match cs with
    | [] | '|' :: _ | ')' :: _ => pure ([], cs)
    | _ =>
      let (atom, rest) ← parseAtom cs
      let (atom, rest) ← parseQuant atom rest
      let (more, rest) ← parseSeq rest
      pure (atom :: more, rest)
  partial def parseAtom (cs : List Char) : Except String (Node × List Char) := do
    match cs with
    | '(' :: '?' :: ':' :: t | '(' :: t =>
      let (alts, rest) ← parseAlt t
      match rest with
      | ')' :: r => pure (.group alts, r)
      | _ => throw "missing )"
    | '[' :: t => parseClass t
    | '.' :: t => pure (.any, t)
    | '^' :: t => pure (.bol, t)
    | '$' :: t => pure (.eol, t)
    | '\\' :: e :: t =>
      if "dDwWsS".toList.contains e then pure (.esc e, t)
      else if e == 'b' then pure (.wordB, t)
      else if e == 'B' then pure (.nonWordB, t)
      else if e == 'A' then pure (.bol, t)
      else if e == 'Z' then pure (.eol, t)
      else do pure (.chr (← escChar e), t)
    | '\\' :: [] => throw "trailing backslash"
    | c :: t =>
      if c == '*' || c == '+' || c == '?' then throw s!"nothing to repeat before `{c}`"
      else pure (.chr c, t)
    | [] => throw "unexpected end of pattern"
  partial def parseQuant (atom : Node) (cs : List Char) : Except String (Node × List Char) := do
    -- A quantifier on a quantifier (`a?{2}`, `a**`) is Python's "multiple repeat" error.
    let mk (lo : Nat) (hi : Option Nat) (rest : List Char) : Except String (Node × List Char) :=
      let (n, r) := match rest with
        | '?' :: r => (Node.rep atom lo hi true, r)
        | _ => (Node.rep atom lo hi false, rest)
      match r with
      | '*' :: _ | '+' :: _ | '?' :: _ => throw "multiple repeat"
      | '{' :: t => if (braceQuant? t).isSome then throw "multiple repeat" else pure (n, r)
      | _ => pure (n, r)
    match cs with
    | '*' :: t => mk 0 none t
    | '+' :: t => mk 1 none t
    | '?' :: t => mk 0 (some 1) t
    | '{' :: t =>
      match braceQuant? t with
      | some (lo, hi, r) => mk lo hi r
      | none => pure (atom, cs)
    | _ => pure (atom, cs)
end

def compile (pattern : String) : Except String (List (List Node)) := do
  let (alts, rest) ← parseAlt pattern.toList
  if !rest.isEmpty then throw "unbalanced )"
  pure alts

structure Ctx where
  text : Array Char
  icase : Bool

def Ctx.eqc (x : Ctx) (a b : Char) : Bool := if x.icase then a.toLower == b.toLower else a == b

def Ctx.inClass (x : Ctx) (neg : Bool) (items : List (Char × Char)) (escs : List Char) (c : Char) : Bool :=
  let hit := items.any (fun (lo, hi) => (lo ≤ c && c ≤ hi) ||
      (x.icase && ((lo ≤ c.toLower && c.toLower ≤ hi) || (lo ≤ c.toUpper && c.toUpper ≤ hi))))
    || escs.any (escMatches · c)
  if neg then !hit else hit

mutual
  /-- Match `nodes` at `i`, then the continuation `k`; backtracking through `Option`. -/
  partial def matchSeq (x : Ctx) (nodes : List Node) (i : Nat) (k : Nat → Option Nat) : Option Nat :=
    match nodes with
    | [] => k i
    | n :: rest => matchNode x n i fun j => matchSeq x rest j k
  partial def matchNode (x : Ctx) (n : Node) (i : Nat) (k : Nat → Option Nat) : Option Nat :=
    let at_ (p : Char → Bool) : Option Nat :=
      if h : i < x.text.size then if p x.text[i] then k (i + 1) else none else none
    match n with
    | .chr c => at_ (x.eqc c)
    | .any => at_ (· != '\n')
    | .esc e => at_ (escMatches e)
    | .cls neg items escs => at_ (x.inClass neg items escs)
    | .bol => if i == 0 then k i else none
    | .eol => if i == x.text.size then k i else none
    | .wordB | .nonWordB =>
      let before := i > 0 && isWord (x.text[i-1]!)
      let after := i < x.text.size && isWord (x.text[i]!)
      let b := before != after
      if (match n with | .wordB => b | _ => !b) then k i else none
    | .group alts => alts.firstM fun seq => matchSeq x seq i k
    | .rep m lo hi lazy => matchRep x m lo hi lazy i 0 k
  partial def matchRep (x : Ctx) (m : Node) (lo : Nat) (hi : Option Nat) (lazy : Bool) (i count : Nat)
      (k : Nat → Option Nat) : Option Nat :=
    let canStop : Bool := count ≥ lo
    let canMore : Bool := match hi with | some h => count < h | none => true
    -- An empty iteration counts while the repetition is still below `lo` (bounded by
    -- `lo`); once `lo` is reached a further empty iteration adds nothing, so stop there.
    let more := if canMore then matchNode x m i (fun j =>
      if j == i then (if count + 1 < lo then matchRep x m lo hi lazy j (count + 1) k else k i)
      else matchRep x m lo hi lazy j (count + 1) k) else none
    if lazy then (if canStop then k i <|> more else more)
    else (more <|> (if canStop then k i else none))
end

/-- `re.search`: does the pattern match anywhere in `s`? -/
def search (alts : List (List Node)) (s : String) (icase : Bool := false) : Bool :=
  let x : Ctx := { text := s.toList.toArray, icase }
  (List.range (x.text.size + 1)).any fun i =>
    (alts.firstM fun seq => matchSeq x seq i some).isSome

def test (pattern s : String) (icase := false) : Bool :=
  match compile pattern with | .ok a => search a s icase | .error _ => false

#guard test "escape" "the escape's domain" && !test "Escape" "the escape's domain" && test "Escape" "the escape's domain" true
#guard test "dropClose|ride" "a ride" && test "dropClose|ride" "dropClose x" && !test "dropClose|ride" "rid"
#guard test "^\\*\\*NEXT" "**NEXT — x" && !test "^\\*\\*NEXT" " **NEXT"
#guard test "FLIP-211" "the FLIP-211 reading" && test "flip-211" "FLIP-211" true
#guard test "a.c" "abc" && !test "a.c" "a\nc" && test "a\\.c" "a.c" && !test "a\\.c" "abc"
#guard test "[a-c]+x" "zzbbx" && !test "[^a-c]x" "ax" && test "[^a-c]x" "dx" && test "[]a]" "]" && test "[\\d_]{3}" "1_2"
#guard test "\\bride\\b" "a ride here" && !test "\\bride\\b" "override" && test "\\Bride" "override"
#guard test "colou?r" "color" && test "colou?r" "colour" && !test "colou?r" "colr"
#guard test "x{2,3}" "axxb" && !test "x{2,3}" "axb" && test "^x{2}$" "xx" && !test "^x{2}$" "xxx" && test "x{2,}" "xxxx"
#guard test "(ab)+c" "ababc" && !test "(ab)+c" "abac" && test "(?:a|b)c$" "zbc"
#guard test "\\s\\w+\\s" " word " && test "\\d+" "item 419" && !test "\\d+" "item"
#guard test "a*" "" && test "^$" "" && !test "^$" "x" && test "(a|ab)(c|bcd)(d*)" "abcd"
#guard test "a.*?b" "aXXb" && test "<.+?>" "<a><b>"
#guard test "(?:a?){2}b" "b" && test "(?:a?){2}b" "aab" && !test "(?:a?){2}c" "b" && test "(a*)*b" "b" && test "(a*)+b" "aab" && !test "(a*)+b" "c"
#guard test "\\AItem" "Item 1" && !test "\\AItem" " Item" && test "x\\Z" "ax" && !test "x\\Z" "xa"
#guard (compile "\\x41").isOk == false && (compile "[\\x41]").isOk == false && (compile "[a-\\x41]").isOk == false && (compile "\\1").isOk == false && (compile "\\p").isOk == false
#guard test "\\n" "a\nb" && test "\\-" "-" && test "[\\-a]" "-" && test "[\\.]" "." && !test "[\\.]" "x" && test "\\t" "\t"
#guard test "a*{2x}" "aa{2x}" && test "a{}" "a{}" && test "^a{,2}b$" "ab" && !test "^a{,2}b$" "aaab" && test "^a{,}b$" "aaab" && (compile "a*{2}").isOk == false && (compile "a*{,2}").isOk == false
#guard (compile "a?{2}").isOk == false && (compile "a**").isOk == false && (compile "a{2}{3}").isOk == false && (compile "a*?").isOk && test "a*{" "{" && test "a{2}?b" "aab"
#guard (compile "(ab").isOk == false && (compile "ab)").isOk == false && (compile "*a").isOk == false && (compile "[ab").isOk == false

end Scripts.Lean.Regex
