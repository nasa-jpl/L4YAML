module

@[expose] public section Blanket

/-!
# Scripts.Docs.ReflectionIndex — the Reflections index's narrative half

`Tests/Reflections.lean` has two independent halves.  Its `import` lines are
load-bearing (they make the demos build; `scripts-check-import-closure` gates
them).  Below them is a *narrative* index: `## theme` / `### sub-theme
(Reflections N, M, …)` headings, each followed by `` * `DemoModule` — Reflection N (…) ``
bullets.  Formerly `scripts/check_reflection_index.py`; five checks, each a
hard failure, messages unchanged:

1. bullet names resolve — every bullet's module is imported by the index
   (not the converse: the bullet list is declared PARTIAL);
2. bullets are claimed — every Reflection number in a bullet's label is in
   the number list of the sub-theme heading it sits under;
3. claims are backed — every number a sub-theme lists has a bullet in that
   block;
4. no number is claimed twice;
5. blocks ascend by each bullet's primary (first) number.

The import list is read off the index's own text (the gate runs before
`Tests.Reflections` is built in CI, and the question is whether the
documentation agrees with the file's own import lines, not with an
environment).
-/

namespace Scripts.Docs.ReflectionIndex

def index : String := "Tests/Reflections.lean"

/-- `(public )?(meta )?import (all )?Tests.Reflections.<rest>` → `<rest>`
(the Python's `IMPORT_RE`). -/
def importOf (line : String) : Option String := do
  let ws := line.splitOn " " |>.filter (· != "")
  let ws := match ws with | "public" :: t => t | t => t
  let ws := match ws with | "meta" :: t => t | t => t
  let ws ← match ws with | "import" :: t => some t | _ => none
  let ws := match ws with | "all" :: t => t | t => t
  let m ← ws.head?
  let p := "Tests.Reflections."
  guard (m.startsWith p)
  guard (line.startsWith "public" || line.startsWith "meta" || line.startsWith "import")
  pure (m.drop p.length).toString

def imports (lines : Array String) : Array String := lines.filterMap importOf

/-- `245–248, 251` → `{245, 246, 247, 248, 251}`; en- and hyphen-dashes both. -/
def expand (inner : String) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for tok in inner.splitOn "," do
    let t := tok.trimAscii.toString
    let range : List String := (t.splitOn "–").flatMap (·.splitOn "-") |>.map (·.trimAscii.toString)
    match range with
    | [a, b] =>
      if !a.isEmpty && !b.isEmpty && a.all Char.isDigit && b.all Char.isDigit then
        for n in [a.toNat!:b.toNat!+1] do out := out.push n
    | [a] => if !a.isEmpty && a.all Char.isDigit then out := out.push a.toNat!
    | _ => pure ()
  return out

/-- `### <name> (Reflections? <list>)` → `(name, list)`. -/
def subtheme (line : String) : Option (String × String) := do
  guard (line.startsWith "### ")
  let body : String := (line.drop 4).trimAscii.toString
  guard (body.endsWith ")")
  let body : String := (body.dropEnd 1).toString
  -- the LAST `(Reflections` opens the list (Python: lazy `(.*?)` then `\(Reflections?`)
  let parts : List String := body.splitOn "(Reflection"
  guard (parts.length ≥ 2)
  let last : String := parts.getLast!
  let inner : String := if last.startsWith "s" then (last.drop 1).toString else last
  guard (inner.startsWith " " || inner.startsWith "\t")
  guard (!inner.any (· == ')'))
  let name := "(Reflection".intercalate (parts.dropLast) |>.trimAscii.toString
  pure (name, inner.trimAscii.toString)

/-- `` * `Module` — rest `` → `(Module, rest)`. -/
def bullet (line : String) : Option (String × String) := do
  guard (line.startsWith "*")
  let t : List Char := (line.drop 1).toString.toList
  guard (t.headD ' ' == ' ' || t.headD ' ' == '\t')
  let t := t.dropWhile (fun c => c == ' ' || c == '\t')
  guard (t.headD ' ' == '`')
  let m := (t.drop 1).takeWhile fun c => c.isAlphanum || c == '_' || c == '.'
  guard (!m.isEmpty)
  let t := (t.drop (1 + m.length))
  guard (t.headD ' ' == '`')
  let t := (t.drop 1).dropWhile (fun c => c == ' ' || c == '\t')
  guard (t.take 1 == ['—'])
  let rest := (t.drop 1).dropWhile (fun c => c == ' ' || c == '\t')
  pure (String.ofList m, String.ofList rest)

/-- Reflection numbers a bullet claims: every 3-digit run (at word boundaries)
before the first `(`. -/
partial def labelNumbers (rest : String) : List Nat :=
  let label := (rest.splitOn "(").headD ""
  go label.toList '\n' []
where
  go : List Char → Char → List Nat → List Nat
    | [], _, acc => acc.reverse
    | c :: t, prev, acc =>
      if c.isDigit && !(prev.isAlphanum || prev == '_') then
        let ds := (c :: t).takeWhile Char.isDigit
        let t' := (c :: t).drop ds.length
        let bounded := t'.head?.all fun c => !(c.isAlphanum || c == '_')
        let acc := if ds.length == 3 && bounded then (String.ofList ds).toNat! :: acc else acc
        go t' (ds.getLastD c) acc
      else go t c acc

structure Bullet where
  line : Nat
  module : String
  nums : List Nat
  deriving Repr, BEq

structure Block where
  line : Nat
  name : String
  claimed : Array Nat
  bullets : Array Bullet := #[]
  deriving Repr

/-- Walk the narrative half, grouping bullets under their sub-theme; a `## `
heading closes the current block. -/
def blocks (lines : Array String) : Array Block := Id.run do
  let mut out : Array Block := #[]
  let mut cur : Option Block := none
  let mut lineno := 0
  for ln in lines do
    lineno := lineno + 1
    if ln.startsWith "## " then
      if let some b := cur then out := out.push b
      cur := none
    else if let some (name, list) := subtheme ln then
      if let some b := cur then out := out.push b
      cur := some { line := lineno, name, claimed := expand list }
    else if let some (m, rest) := bullet ln then
      if let some b := cur then
        cur := some { b with bullets := b.bullets.push { line := lineno, module := m, nums := labelNumbers rest } }
  if let some b := cur then out := out.push b
  return out

/-- `(exit code, lines to print)`; the Python's text and order. -/
def gate (text : String) : UInt32 × Array String := Id.run do
  let lines := (text.splitOn "\n").toArray
  let imported := imports lines
  let bs := blocks lines
  if bs.isEmpty then
    return (1, #[s!"{index}: no `### sub-theme (Reflections ...)` headings found — has the index format changed?"])
  let mut failures : Array String := #[]
  let mut owner : List (Nat × Nat) := []   -- number ↦ bullet line
  for b in bs do
    for bl in b.bullets do
      if !imported.contains bl.module then
        failures := failures.push s!"{index}:{bl.line}: bullet `{bl.module}` is not imported by the index"
      if bl.nums.isEmpty then
        failures := failures.push s!"{index}:{bl.line}: bullet `{bl.module}` names no Reflection number before its '('"
      for n in bl.nums do
        if !b.claimed.contains n then
          failures := failures.push s!"{index}:{bl.line}: Reflection {n} (`{bl.module}`) is not in the list of its sub-theme \"{b.name}\" ({index}:{b.line})"
        match owner.lookup n with
        | some l => failures := failures.push s!"{index}:{bl.line}: Reflection {n} also claimed at {index}:{l}"
        | none => owner := owner ++ [(n, bl.line)]
    let present := b.bullets.toList.flatMap (·.nums)
    let missing := (b.claimed.filter (!present.contains ·)).qsort (· < ·)
    for n in missing do
      let where_ := match owner.lookup n with
        | some l => s!", whose bullet is at {index}:{l}"
        | none => ""
      failures := failures.push s!"{index}:{b.line}: \"{b.name}\" lists Reflection {n} but has no such bullet{where_}"
    let prim := b.bullets.filterMap fun bl => bl.nums.head?.map fun n => (n, bl.line, bl.module)
    for i in [1:prim.size] do
      let (n1, _, m1) := prim[i-1]!; let (n2, l2, m2) := prim[i]!
      if n2 < n1 then
        failures := failures.push s!"{index}:{l2}: `{m2}` (Reflection {n2}) follows `{m1}` (Reflection {n1}) — block \"{b.name}\" is not ascending"
  let demos := (bs.toList.flatMap fun b => b.bullets.toList.map (·.module)).eraseDups.length
  if !failures.isEmpty then
    return (1, #[s!"Reflections index: {failures.size} problem(s)", ""] ++ failures.map (s!"  {·}")
      ++ #["", s!"{bs.size} sub-themes, {demos} bulleted demos, {owner.length} reflections indexed."])
  return (0, #[s!"Reflections index OK: {bs.size} sub-themes, {demos} bulleted demos, {owner.length} reflections indexed, {imported.size} demos imported."])

#guard importOf "public import Tests.Reflections.Foo" == some "Foo"
#guard importOf "import all Tests.Reflections.Foo.Bar" == some "Foo.Bar"
#guard importOf "public meta import Tests.Reflections.X" == some "X"
#guard importOf "import Tests.Other.X" == none
#guard importOf "  import Tests.Reflections.X" == none
#guard expand "245–248, 251" == #[245, 246, 247, 248, 251]
#guard expand "592, 593, 596-597" == #[592, 593, 596, 597]
#guard expand "" == #[]
#guard subtheme "### Tactics & elaboration (Reflections 592, 593)" == some ("Tactics & elaboration", "592, 593")
#guard subtheme "### One (Reflection 352)" == some ("One", "352")
#guard subtheme "### Parens (a) in name (Reflections 1, 2)" == some ("Parens (a) in name", "1, 2")
#guard subtheme "### No list" == none
#guard subtheme "## Theme (Reflections 1)" == none
#guard bullet "* `LoopPushPointwise`   — Reflection 592 (x)" == some ("LoopPushPointwise", "Reflection 592 (x)")
#guard bullet "* `A.B` — Reflections 245, 246 (y)" == some ("A.B", "Reflections 245, 246 (y)")
#guard bullet "- `A` — Reflection 1" == none
#guard labelNumbers "Reflection 592 (cites 611)" == [592]
#guard labelNumbers "Reflections 245, 246 and 1234 (x 300)" == [245, 246]
#guard labelNumbers "no number (300)" == []
#guard labelNumbers "Reflection 123x" == []
#guard labelNumbers "Reflection 123_a, 124" == [124]
#guard (gate "import Tests.Reflections.A\n## T\n### S (Reflections 100, 101)\n* `A` — Reflections 100, 101 (z)\n").1 == 0
#guard (gate "import Tests.Reflections.A\n## T\n### S (Reflections 100)\n* `A` — Reflection 100 (z)\n* `B` — Reflection 101 (z)\n").2 ==
  #["Reflections index: 2 problem(s)", "",
    "  Tests/Reflections.lean:5: bullet `B` is not imported by the index",
    "  Tests/Reflections.lean:5: Reflection 101 (`B`) is not in the list of its sub-theme \"S\" (Tests/Reflections.lean:3)",
    "", "1 sub-themes, 2 bulleted demos, 2 reflections indexed."]
#guard (gate "## T\n### S (Reflections 100, 102)\n* `A` — Reflection 102\n* `A` — Reflection 100\n").2 ==
  #["Reflections index: 3 problem(s)", "",
    "  Tests/Reflections.lean:3: bullet `A` is not imported by the index",
    "  Tests/Reflections.lean:4: bullet `A` is not imported by the index",
    "  Tests/Reflections.lean:4: `A` (Reflection 100) follows `A` (Reflection 102) — block \"S\" is not ascending",
    "", "1 sub-themes, 1 bulleted demos, 2 reflections indexed."]
#guard (gate "nothing\n").1 == 1

end Scripts.Docs.ReflectionIndex
