module

/-!
# Scripts.Punt.Price — the pure half of `lake run punt-price`

The port of `scripts/punt_reason_price.py` (Rule 9 phase 3.2b): the price of
`KeyPackPunt`'s reasons in `L4YAML/Proofs/Production/StreamAccum.lean`, read off
`lake env lean`'s own error locations.  Everything here is a function of the file's
lines and of Lean's output: the constructor block, the deletion patch (`price`), the
`∨ True → ∨ False` narrowings (`phantom`, `reaches`), the error-location reader, the
census by enclosing declaration and every line the Python printed.  The IO (the
backup, the `lake env lean` run, the restore) is `Scripts.Main.PuntPrice`.
-/

namespace Scripts.Punt.Price

public section

def target : String := "L4YAML/Proofs/Production/StreamAccum.lean"

/-- Item 297 deleted `dedent`; item 300 added `markerLine`. -/
def reasons : List String := ["tab", "implicitValue", "markerLine", "noKeyContext"]

/-- Printed apart rather than dropped: it re-writes a reason, it does not spend one. -/
def transport : String := "keyPackPunt_transport"

def strip (s : String) : String := s.trimAscii.toString
def lstrip (s : String) : String := s.trimAsciiStart.toString
def rstrip (s : String) : String := s.trimAsciiEnd.toString

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Python's `{s:<w}`. -/
def padRight (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

/-- Python's `{n:3d}`. -/
def padLeft (s : String) (w : Nat) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

#guard padRight "ab" 4 == "ab  "
#guard padLeft "7" 3 == "  7"
#guard padLeft "1234" 3 == "1234"

/-- `s[:n]` by codepoint. -/
def take (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
def drop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- `re.match(r"^lemma NAME\b")`. -/
def isLemmaHead (decl line : String) : Bool :=
  line.startsWith s!"lemma {decl}" &&
    match (drop line (6 + decl.length)).toList.head? with
    | some c => !isWordChar c
    | none => true

#guard isLemmaHead "foo" "lemma foo (x : Nat) :"
#guard !isLemmaHead "foo" "lemma foobar :"
#guard !isLemmaHead "foo" "private lemma foo :"

/-- `(first, last)` line indices of `inductive KeyPackPunt`'s constructors: the line
    after the head, to the first blank line. -/
def inductiveBlock (lines : Array String) : Option (Nat × Nat) := do
  let start ← lines.findIdx? (·.startsWith "inductive KeyPackPunt ")
  let mut e := start + 1
  while e < lines.size && strip lines[e]! != "" do e := e + 1
  return (start + 1, e)

/-- `^  \| \w+` -/
def isCtorHead (line : String) : Bool :=
  line.startsWith "  | " && (match (drop line 4).toList.head? with | some c => isWordChar c | none => false)

/-- `^  \| REASON\b` -/
def isCtorHeadOf (reason line : String) : Bool :=
  line.startsWith s!"  | {reason}" &&
    match (drop line (4 + reason.length)).toList.head? with
    | some c => !isWordChar c
    | none => true

/-- `constructor_span`: the lines one constructor occupies, or the Python's exit message. -/
def constructorSpan (lines : Array String) (reason : String) : Except String (Nat × Nat) := do
  let some (first, last) := inductiveBlock lines | throw "no `inductive KeyPackPunt` in the file"
  let heads := ((List.range (last - first)).map (· + first)).filter fun i => isCtorHead lines[i]!
  if heads.length != reasons.length then
    throw s!"{heads.length} constructors, expected {reasons.length} -- the type moved"
  match heads.zipIdx.find? fun (i, _) => isCtorHeadOf reason lines[i]! with
  | some (i, j) => return (i, heads[j + 1]?.getD last)
  | none => throw s!"no constructor `{reason}` in KeyPackPunt"

/-- `apply_delete`: the constructor commented out line by line (the prefix is the
    Python's; it is written to the scratch copy only), and the 1-based inclusive span. -/
def applyDelete (lines : Array String) (reason : String) : Except String (Array String × Nat × Nat) := do
  let (lo, hi) ← constructorSpan lines reason
  let mut out := lines
  for i in [lo:hi] do
    out := out.set! i ("  -- PUNT REASON DELETED (scripts/punt_reason_price.py): " ++ strip lines[i]!)
  return (out, lo + 1, hi)

private def declHead? (line : String) : Option String :=
  let rest := if line.startsWith "private " then drop line 8 else line
  let kws := ["lemma ", "theorem ", "def ", "abbrev "]
  kws.findSome? fun kw =>
    if rest.startsWith kw then
      let name := String.ofList ((drop rest kw.length).toList.takeWhile isWordChar)
      if name.isEmpty then none else some name
    else none

/-- `enclosing_decl(lines, lineno)`: the last `^(?:private )?(?:lemma|theorem|def|abbrev) (\w+)`
    among `lines[0..lineno-1]` (the Python's `range(min(lineno, len))`), else `<file scope>`. -/
def enclosingDecl (lines : Array String) (lineno : Nat) : String := Id.run do
  let mut decl := "<file scope>"
  for i in [0:min lineno lines.size] do
    if let some n := declHead? lines[i]! then decl := n
  return decl

private def sample : Array String := #[
  "inductive KeyPackPunt (x : Nat) : Prop where",
  "  | tab (h : x = 1)",
  "  | implicitValue",
  "  | markerLine (h : x = 2)",
  "      (h' : True)",
  "  | noKeyContext",
  "",
  "lemma foo : True := by",
  "  exact KeyPackPunt.tab rfl",
  "private def keyPackPunt_transport := 1",
  "theorem bar (h : P ∨ True) : True := trivial"]

#guard inductiveBlock sample == some (1, 6)
#guard (constructorSpan sample "markerLine").toOption == some (3, 5)
#guard (constructorSpan sample "noKeyContext").toOption == some (5, 6)
#guard (match constructorSpan sample "dedent" with | .error e => e == "no constructor `dedent` in KeyPackPunt" | .ok _ => false)
#guard ((applyDelete sample "markerLine").map (fun (o, a, b) => (o[3]!, o[4]!, a, b))).toOption
  == some ("  -- PUNT REASON DELETED (scripts/punt_reason_price.py): | markerLine (h : x = 2)",
          "  -- PUNT REASON DELETED (scripts/punt_reason_price.py): (h' : True)", 4, 5)
#guard enclosingDecl sample 9 == "foo"
#guard enclosingDecl sample 10 == "keyPackPunt_transport"
#guard enclosingDecl sample 7 == "<file scope>"
#guard enclosingDecl sample 8 == "foo"

/-! ## Lean's error locations -/

/-- `^L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): error` → `(line, col)`. -/
def errorLoc? (line : String) : Option (Nat × Nat) := do
  let pre := target ++ ":"
  guard (line.startsWith pre)
  let rest := (drop line pre.length).toList
  let d1 := rest.takeWhile Char.isDigit
  guard !d1.isEmpty
  let rest := rest.drop d1.length
  guard (rest.head? == some ':')
  let d2 := (rest.drop 1).takeWhile Char.isDigit
  guard !d2.isEmpty
  let rest := (rest.drop 1).drop d2.length
  guard ((String.ofList rest).startsWith ": error")
  return ((String.ofList d1).toNat!, (String.ofList d2).toNat!)

#guard errorLoc? "L4YAML/Proofs/Production/StreamAccum.lean:31195:14: error: Type mismatch" == some (31195, 14)
#guard errorLoc? "L4YAML/Proofs/Production/StreamAccum.lean:31195:14: warning: x" == none
#guard errorLoc? "L4YAML/Proofs/Production/Other.lean:3:1: error: x" == none

/-- The sorted set of `(line, col)` error locations in Lean's output. -/
def errorLocs (out : String) : List (Nat × Nat) :=
  let locs := (out.splitOn "\n").filterMap errorLoc?
  let dedup := locs.foldl (fun acc l => if acc.contains l then acc else acc.push l) (#[] : Array (Nat × Nat))
  (dedup.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)).toList

#guard errorLocs "x\nL4YAML/Proofs/Production/StreamAccum.lean:9:2: error: a\nL4YAML/Proofs/Production/StreamAccum.lean:4:7: error: b\nL4YAML/Proofs/Production/StreamAccum.lean:9:2: error: a\n" == [(4, 7), (9, 2)]

/-- An insertion-ordered census `decl ↦ hits`. -/
abbrev Census (α : Type) := Array (String × Array α)

def Census.add {α : Type} (c : Census α) (k : String) (v : α) : Census α :=
  match c.findIdx? (·.1 == k) with
  | some i => c.modify i fun (n, vs) => (n, vs.push v)
  | none => c.push (k, #[v])

/-- `sorted(items, key=(-len, name))`. -/
def Census.sorted {α : Type} (c : Census α) : Census α :=
  c.qsort fun a b => a.2.size > b.2.size || (a.2.size == b.2.size && a.1 < b.1)

/-! ## `price REASON` -/

/-- The census of one deletion: error lines outside the constructor's own span, by the
    declaration enclosing each (1-based line, the Python's `enclosing_decl(lines, h)`). -/
def priceCensus (lines : Array String) (span : Nat × Nat) (out : String) : Census Nat :=
  let hits := ((errorLocs out).map (·.1)).eraseDups
  let hits := hits.filter fun h => !(span.1 ≤ h && h ≤ span.2)
  hits.foldl (fun c h => Census.add c (enclosingDecl lines h) h) (#[] : Census Nat)

def joinL (hs : Array Nat) : String := ", ".intercalate (hs.toList.map fun h => s!"L{h}")

/-- `report`. -/
def priceReport (reason : String) (census : Census Nat) : Array String := Id.run do
  let spend := census.filter (·.1 != transport)
  let total := spend.foldl (· + ·.2.size) 0
  let mut out := #[s!"\n=== {reason}: {total} errors / {spend.size} declarations ==="]
  for (decl, hits) in Census.sorted spend do
    out := out.push s!"  {padLeft (toString hits.size) 3}  {padRight decl 36} {joinL hits}"
  if let some (_, hits) := census.find? (·.1 == transport) then
    out := out.push s!"  [{hits.size}] {padRight transport 34} {joinL hits}   (RE-WRITES a reason, does not spend one)"
  if census.isEmpty then
    out := out.push "  none -- the reason has no producer at all: a PHANTOM by the compiler's own reading"
  return out

#guard priceReport "tab" #[("foo", #[9, 12]), ("keyPackPunt_transport", #[20]), ("bar", #[30, 31])]
  == #["\n=== tab: 4 errors / 2 declarations ===",
       "    2  bar                                  L30, L31",
       "    2  foo                                  L9, L12",
       "  [1] keyPackPunt_transport              L20   (RE-WRITES a reason, does not spend one)"]
#guard priceReport "tab" #[] == #["\n=== tab: 0 errors / 0 declarations ===",
  "  none -- the reason has no producer at all: a PHANTOM by the compiler's own reading"]

/-! ## `phantom`: falsify one optional premise of `flowKeyPack_of_close` -/

/-- `(decl, anchor test, where)`: the anchor is the Python's regex as a line predicate. -/
def phantomSwitches : List (String × String × (String → Bool) × String) :=
  [("stamp", "flowKeyPack_of_close",
    (· == "      (sc.implicitValueLine = some sc.simpleKey.pos.line ∨ True))"), "here"),
   ("keyroute", "flowKeyPack_of_close",
    (·.endsWith "ResumeFrames (ExplValueLine sp_start nv) ks sp_e) ∨ True)) ∨ True)"), "last")]

def phantomNames : List String := phantomSwitches.map (·.1)

/-- Replace the last occurrence of `pat` in `s` by `rep` (`str.rpartition`). -/
def replaceLast (s pat rep : String) : String :=
  let parts := s.splitOn pat
  if parts.length ≤ 1 then s
  else pat.intercalate parts.dropLast ++ rep ++ parts.getLast!

#guard replaceLast "a ∨ True b ∨ True c" "∨ True" "∨ False" == "a ∨ True b ∨ False c"
#guard replaceLast "abc" "x" "y" == "abc"

/-- `apply_narrow`: `(patched lines, decl, 1-based hit line)`. -/
def applyNarrow (lines : Array String) (which : String) : Except String (Array String × String × Nat) := do
  let some (_, decl, anchor, where_) := phantomSwitches.find? (·.1 == which) | throw s!"no switch `{which}`"
  let some start := lines.findIdx? (isLemmaHead decl) | throw s!"no `lemma {decl}` in {target}"
  let some hit := (List.range (lines.size - start)).findSome? (fun k => if anchor lines[start + k]! then some (start + k) else none)
    | throw s!"the `{which}` anchor is not in `{decl}`; the lemma moved and this switch needs re-aiming"
  let l := lines[hit]!
  let parts := l.splitOn "∨ True"
  let firstOnly := if parts.length ≤ 1 then l else parts[0]! ++ "∨ False" ++ "∨ True".intercalate (parts.drop 1)
  let l' := if where_ == "last" then replaceLast l "∨ True" "∨ False" else firstOnly
  return (lines.set! hit l', decl, hit + 1)

#guard ((applyNarrow #["lemma flowKeyPack_of_close (a : Nat)", "    (h : x ∨ True)", "      (sc.implicitValueLine = some sc.simpleKey.pos.line ∨ True))"] "stamp").map (fun (o, d, h) => (o[2]!, d, h))).toOption
  == some ("      (sc.implicitValueLine = some sc.simpleKey.pos.line ∨ False))", "flowKeyPack_of_close", 3)
#guard ((applyNarrow #["lemma flowKeyPack_of_close :", "  (A ∨ True) → (ResumeFrames (ExplValueLine sp_start nv) ks sp_e) ∨ True)) ∨ True)"] "keyroute").map (·.1[1]!)).toOption
  == some "  (A ∨ True) → (ResumeFrames (ExplValueLine sp_start nv) ks sp_e) ∨ True)) ∨ False)"

/-- Whether the error at `(h, col)` sits on a declined context: the text from the column
    starts with `trivial` and the prefix ends with `Or.inr`. -/
def declinedAt (lines : Array String) (h col : Nat) : Bool × String :=
  let line := lines[h - 1]?.getD ""
  let pre := take line col
  let text := strip (drop line col)
  (text.startsWith "trivial" && (rstrip pre).endsWith "Or.inr", text)

#guard declinedAt #["  (Or.inr trivial) h"] 1 9 == (true, "trivial) h")
#guard declinedAt #["  (Or.inr h_keyctx) x"] 1 9 == (false, "h_keyctx) x")

/-- `phantom_census`'s report, given the narrowed lemma, its hit line and Lean's output. -/
def phantomReport (lines : Array String) (which decl : String) (hit : Nat) (out : String) : Array String := Id.run do
  let census : Census (Nat × Nat) := (errorLocs out).foldl (fun c (h, col) => Census.add c (enclosingDecl lines h) (h, col)) (#[] : Census (Nat × Nat))
  let own := ((census.find? (·.1 == decl)).map (·.2)).getD #[]
  let census := census.filter (·.1 != decl)
  let total := census.foldl (· + ·.2.size) 0
  let mut o := #[s!"\n=== narrow {which} ({decl}, L{hit}): {total} caller errors / {census.size} declarations ==="]
  for (d, hs) in Census.sorted census do
    o := o.push s!"  {padLeft (toString hs.size) 3}  {d}"
    for (h, col) in hs do
      let (declined, text) := declinedAt lines h col
      let kind := if declined then "DECLINES" else "pays/relays"
      o := o.push s!"         L{h}:{padRight (toString col) 4} {padRight kind 12} {take text 48}"
  o := o.push (s!"  [{own.size}] {padRight (decl ++ "  (its own body)") 34} " ++ ", ".intercalate (own.toList.map fun (h, _) => s!"L{h}"))
  if census.isEmpty then
    o := o.push "  NO CALLER declines the premise -- the `inr` branch is reachable from no call site in this tree"
  return o

/-! ## `split`: productions vs consumer arms -/

def armVerdicts : List (String × String) :=
  [("DEFERS to the escape at its own arm", "block_dispatch_deferred_inline"),
   ("RIDES the caller's deferral", "exact h_punt"),
   ("WEAKENS the consumer's own premise", "Or.inr trivial")]

def spends : String := "SPENDS it -- a refutation, or the reason as a datum"

def indentOf (s : String) : Nat := s.length - (lstrip s).length

/-- `^(\s*(?:· )?)cases \w+ with\s*$` → the indent (the length of group 1). -/
def casesWith? (line : String) : Option Nat := do
  let ws := String.ofList (line.toList.takeWhile Char.isWhitespace)
  let rest := drop line ws.length
  let (g1, rest) := if rest.startsWith "· " then (ws.length + 2, drop rest 2) else (ws.length, rest)
  guard (rest.startsWith "cases ")
  let after := (drop rest 6).toList
  let name := after.takeWhile isWordChar
  guard !name.isEmpty
  let tail := String.ofList (after.drop name.length)
  guard (tail.startsWith " with" && strip (drop tail 5) == "" )
  return g1

#guard casesWith? "    cases h_punt with" == some 4
#guard casesWith? "  · cases r with  " == some 4
#guard casesWith? "    cases h with x" == none
#guard casesWith? "    rcases h with" == none

/-- `^\s*\| (\w+)` -/
def altName? (line : String) : Option String :=
  let s := lstrip line
  if s.startsWith "| " then
    let n := String.ofList ((drop s 2).toList.takeWhile isWordChar)
    if n.isEmpty then none else some n
  else none

def isComment (line : String) : Bool := (strip line).startsWith "--"

/-- `punt_match_blocks`: `(line index, label)` of every alternative of a `cases … with`
    whose labels (two or more) are all punt reasons, outside the inductive's own block. -/
def puntMatchBlocks (lines : Array String) : List (Nat × String) := Id.run do
  let (lo, hi) := (inductiveBlock lines).getD (0, 0)
  let mut blocks : Array (Nat × String) := #[]
  for i in [0:lines.size] do
    let some ind := casesWith? lines[i]! | continue
    let mut alts : Array (Nat × String) := #[]
    let mut j := i + 1
    let mut go := true
    while go && j < lines.size do
      let s := lines[j]!
      if strip s == "" || isComment s then j := j + 1; continue
      let cur := indentOf s
      if cur < ind then go := false
      else
        match altName? s with
        | some a => if cur == ind then alts := alts.push (j, a)
        | none => if cur == ind then go := false
        j := j + 1
    let names := (alts.map (·.2)).toList.eraseDups
    if names.length ≥ 2 && names.all reasons.contains then
      blocks := blocks ++ alts.filter fun (j, _) => !(lo ≤ j && j ≤ hi)
  return blocks.toList

private def splitSample : Array String := #[
  "inductive KeyPackPunt (x : Nat) : Prop where",
  "  | tab", "  | implicitValue", "  | markerLine", "  | noKeyContext", "",
  "lemma c1 : True := by",
  "  cases h with",
  "  | tab => exact h_punt (fun _ => block_dispatch_deferred_inline x)",
  "  -- a note",
  "  | noKeyContext =>",
  "    exact Or.inr trivial",
  "  | implicitValue => exact absurd h h'",
  "lemma c2 : True := by",
  "  cases h with",
  "  | inl => exact a",
  "  | inr => exact b",
  "lemma p : True := KeyPackPunt.tab h"]

#guard puntMatchBlocks splitSample == [(8, "tab"), (10, "noKeyContext"), (12, "implicitValue")]

/-- `split_census`'s report. -/
def splitReport (lines : Array String) : Array String := Id.run do
  let (lo, hi) := (inductiveBlock lines).getD (0, 0)
  let arms := puntMatchBlocks lines
  let mut out : Array String := #[]
  for reason in reasons do
    let needle := s!"KeyPackPunt.{reason}"
    let prod := (List.range lines.size).filterMap fun i =>
      let line := lines[i]!
      if (line.splitOn needle).length > 1 && !(lo ≤ i && i ≤ hi) && !isComment line
          && !line.contains '`' && enclosingDecl lines i != transport
      then some (i + 1, enclosingDecl lines i) else none
    let mine := arms.filterMap fun (j, n) =>
      if n == reason && enclosingDecl lines j != transport then some (j + 1, enclosingDecl lines j, lines[j]!) else none
    out := out.push s!"\n=== {reason}: {prod.length} productions / {mine.length} consumer arms ==="
    for (ln, decl) in prod do out := out.push s!"  PRODUCTION   L{padRight (toString ln) 6} {decl}"
    for (ln, decl, line) in mine do
      let s := strip line
      let body := match s.splitOn "=>" with
        | _ :: rest => strip ("=>".intercalate rest)
        | [] => ""
      let body := if body.isEmpty then
          ((lines.extract ln lines.size).toList.find? fun t => strip t != "" && !isComment t).map strip |>.getD ""
        else body
      let verdict := (armVerdicts.find? fun (_, pat) => (body.splitOn pat).length > 1).map (·.1) |>.getD spends
      out := out.push s!"  CONSUMER ARM L{padRight (toString ln) 6} {padRight decl 28} {verdict}"
  return out

#guard splitReport splitSample == #[
  "\n=== tab: 1 productions / 1 consumer arms ===",
  "  PRODUCTION   L18     c2",
  "  CONSUMER ARM L9      c1                           DEFERS to the escape at its own arm",
  "\n=== implicitValue: 0 productions / 1 consumer arms ===",
  "  CONSUMER ARM L13     c1                           SPENDS it -- a refutation, or the reason as a datum",
  "\n=== markerLine: 0 productions / 0 consumer arms ===",
  "\n=== noKeyContext: 0 productions / 1 consumer arms ===",
  "  CONSUMER ARM L11     c1                           WEAKENS the consumer's own premise"]

/-! ## `reaches`: the phantom, decided at the production -/

def contexts : List String := ["h_keyctx", "h_suffixctx", "h_nodocctx", "h_markerctx", "h_propsctx"]
def reachDecl : String := "content_dispatch_routed"

/-- `narrow_binder`: falsify the binder's `∨ True` → `(patched, 1-based hit)`. -/
def narrowBinder (lines : Array String) (decl binder : String) : Except String (Array String × Nat) := do
  let some start := lines.findIdx? (isLemmaHead decl) | throw s!"no `lemma {decl}` in {target}"
  let some b := (List.range (lines.size - start)).findSome? (fun k => if lines[start + k]!.startsWith s!"    ({binder} :" then some (start + k) else none)
    | throw s!"no binder `({binder} :` in `{decl}`"
  let some hit := (List.range (lines.size - b)).findSome? (fun k => if (lines[b + k]!.splitOn " ∨ True)").length > 1 then some (b + k) else none)
    | throw s!"no ` ∨ True)` after `{binder}` in `{decl}`"
  let l := lines[hit]!
  let parts := l.splitOn "∨ True"
  let l' := parts[0]! ++ "∨ False" ++ "∨ True".intercalate (parts.drop 1)
  return (lines.set! hit l', hit + 1)

#guard ((narrowBinder #["lemma content_dispatch_routed", "    (h_keyctx :", "      (a ∨ True) → (b ∨ True))"] "content_dispatch_routed" "h_keyctx").map (·.1[2]!)).toOption
  == some "      (a ∨ False) → (b ∨ True))"

/-- `call_sites`: 1-based lines where `decl` is applied (its own head excluded). -/
def callSites (lines : Array String) (decl : String) : List Nat :=
  (List.range lines.size).filterMap fun i =>
    let l := lines[i]!
    if (l.splitOn decl).length > 1 && !isLemmaHead decl l && !isComment l && !l.contains '`' then some (i + 1) else none

/-- `re.search(rf"\b{binder}\b", text)` -/
def hasWord (text word : String) : Bool := Id.run do
  let cs := text.toList
  let w := word.toList
  for i in [0:cs.length + 1] do
    if (cs.drop i).take w.length == w then
      let before := if i == 0 then none else cs[i - 1]?
      let after := cs[i + w.length]?
      if before.all (!isWordChar ·) && after.all (!isWordChar ·) then return true
  return false

#guard hasWord "foo (h_keyctx) bar" "h_keyctx"
#guard !hasWord "foo h_keyctx2 bar" "h_keyctx"
#guard hasWord "h_keyctx" "h_keyctx"

structure ReachRow where
  site : Nat
  h : Nat
  col : Nat
  verdict : String
  text : String

/-- One binder's reading: rows, the sites that declined it, the sites that relay. -/
def reachRows (lines : Array String) (apps : List Nat) (binder : String) (out : String) :
    Array ReachRow × List Nat × List Nat := Id.run do
  let mut rows : Array ReachRow := #[]
  let mut declined : List Nat := []
  let mut relays : List Nat := []
  for (h, col) in errorLocs out do
    if enclosingDecl lines (h - 1) == reachDecl then continue
    let site := (apps.filter (· ≤ h)).foldl max 0
    let (dec, text) := declinedAt lines h col
    if dec then
      declined := declined ++ [site]
      rows := rows.push ⟨site, h, col, "DECLINES", text⟩
    else if hasWord text binder then
      relays := relays ++ [site]
      rows := rows.push ⟨site, h, col, "RELAYS  ", text⟩
    else rows := rows.push ⟨site, h, col, "pays    ", text⟩
  return (rows, declined, relays)

def binderLines (binder : String) (rows : Array ReachRow) : Array String :=
  #[s!"\n  {binder}:"] ++ rows.map fun r =>
    s!"    L{padRight (toString r.site) 6} {r.verdict} at L{r.h}:{padRight (toString r.col) 4} {take r.text 46}"

/-- The closing table: per application, how many contexts it declines. -/
def reachSummary (lines : Array String) (apps : List Nat) (declines : List (Nat × List String)) (relays : List Nat) : Array String := Id.run do
  let mut out : Array String := #[""]
  let n := contexts.length
  let mut reach := 0
  for a in apps do
    let k := ((declines.find? (·.1 == a)).map (·.2.eraseDups.length)).getD 0
    let mark := if relays.contains a then "  <-- RELAYS: the decision is its own caller's"
      else if k == n then "  <-- reaches `noKeyContext`" else ""
    if k == n && !relays.contains a then reach := reach + 1
    out := out.push s!"  L{padRight (toString a) 6} {padRight (enclosingDecl lines (a - 1)) 30} declines {k}/{n}{mark}"
  out := out.push s!"\n  {reach} of {apps.length} applications decline ALL FIVE ({relays.eraseDups.length} relay their caller's)"
  if reach == 0 then
    out := out.push "  -- no application reaches `noKeyContext`: a PHANTOM at this production, on the compiler's own locations"
  return out

#guard reachSummary #["lemma a : T", "  content_dispatch_routed x"] [2] [(2, ["h_keyctx", "h_suffixctx", "h_nodocctx", "h_markerctx", "h_propsctx"])] []
  == #["", "  L2      a                              declines 5/5  <-- reaches `noKeyContext`", "\n  1 of 1 applications decline ALL FIVE (0 relay their caller's)"]

def usageModes : String :=
  "|".intercalate reasons ++ "|all|split|phantom|reaches|" ++ "|".intercalate phantomNames

end

end Scripts.Punt.Price
