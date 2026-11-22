module

public import Scripts.Lean.BuildLog
meta import Scripts.Lean.BuildLog

@[expose] public section Blanket

/-!
# Scripts.Pack.Residue — the PACK residue's declines classed by their existential index

The port of `scripts/residue_classes.py` (item 403).  Read-only: joins three pinned/derived
readings and runs nothing:

* `Tests/Guards/Proofs/OrTrueAudit.lean` — `expectedPositions` (which `∨` positions have a
  `PackAlt`/`PackAltG` alternative) and `expectedSupply` (the `DECLINE=n` edges at each);
* `L4YAML/Proofs/Production/StreamAccum.lean` — the binder of each such field, read off the
  text of its carrier structure or the telescope of its lemma / constructor, classed by the
  ghost datum its informative side quantifies: `ks`, `ns`, `pack`, `scalar`, `none`;
* optionally the TSV of `pack-census residue --tsv` — the residue's DECLINE sites split into
  `∨`-position sites and bare `PackAlt` lemma parameters (`h_alt := … trivial`,
  `(fun _ => trivial)`), which the audit does not see.

The plan (Blueprint/09 §3 phase 2 item 2) suggests reading the binders from the environment;
this port keeps the Python's text reading so its classes are reproduced byte for byte — the
environment reading is a later refinement, stated there.
-/

open Scripts.Lean.BuildLog (pyStrip)

namespace Scripts.Pack.Residue

def ns := "L4YAML.Proofs.StreamAccum."

def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || ('₀' ≤ c && c ≤ '₉')

def boundaryAfter (cs : List Char) : Bool := cs.head?.all (fun c => !isWordChar c)

/-- `s[n:]` by code points. -/
def dropS (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- `lean_list`: the string literals of `def NAME : List String :=\s*[ … \n  ]`. -/
def leanList (text name : String) : Option (Array String) := do
  let marker := s!"def {name} : List String :="
  let i ← (text.splitOn marker)[1]?
  let after := i.toList.dropWhile Char.isWhitespace
  let '[' :: body := after | none
  let inner := (String.ofList body).splitOn "\n  ]" |>.head!
  let parts := inner.splitOn "\""
  -- quoted strings are the odd-indexed parts of the split on `"`
  return (parts.toArray.zipIdx.filter (fun (_, k) => k % 2 == 1)).map (·.1)

#guard leanList "x\ndef foo : List String :=\n  [ \"a b\",\n    \"c\"\n  ]\ndef bar : List String := []" "foo" == some #["a b", "c"]
#guard leanList "def foo : List String :=\n  [\n  ]\n" "foo" == some #[]
#guard leanList "nothing" "foo" == none

/-- The `(field : …)` binder of `decl` as the Python's `binder_text` read it: the field line of a
`structure <first component of decl>` block, else the first balanced `(field :` group within
40 000 characters after a `lemma|theorem|def <leaf>` head or a `| <leaf>` constructor head. -/
def binderText (lines : Array String) (decl field : String) : String := Id.run do
  let comps := decl.splitOn "."
  let leaf := comps.getLast!
  let first := comps.head!
  let headOf (l : String) : Option Nat :=
    let l' := if l.startsWith "public " then some (dropS l 7) else if l.startsWith "private " then some (dropS l 8) else some l
    l'.bind fun l' =>
      ["lemma ", "theorem ", "def "].findSome? fun k =>
        if l'.startsWith (k ++ leaf) && boundaryAfter (l'.toList.drop (k.length + leaf.length)) then
          some (l.length - l'.length + k.length + leaf.length)
        else none
  let ctorOf (l : String) : Option Nat :=
    let ws := l.toList.takeWhile Char.isWhitespace
    let r := String.ofList (l.toList.drop ws.length)
    if r.startsWith ("| " ++ leaf) && boundaryAfter (r.toList.drop (2 + leaf.length)) then
      some (ws.length + 2 + leaf.length) else none
  -- structure blocks named `first`
  for i in [0:lines.size] do
    let l := lines[i]!
    if l.startsWith ("structure " ++ first) && boundaryAfter (l.toList.drop (10 + first.length)) then
      let mut j := i + 1
      while j < lines.size && (lines[j]!.toList.head?.all Char.isWhitespace) do j := j + 1
      -- the block is lines i..j-1; the field line is `  field :…`
      for k in [i + 1:j] do
        let fl := lines[k]!
        if fl.startsWith ("  " ++ field ++ " :") then
          let mut acc := dropS fl (4 + field.length)
          let mut q := k + 1
          while q < j do
            let nl := lines[q]!
            let isField := nl.startsWith "  " && (nl.toList.drop 2).head?.any isWordChar &&
              (let w := (nl.toList.drop 2).takeWhile isWordChar
               String.ofList ((nl.toList.drop 2).drop w.length) |>.startsWith " :")
            if isField || nl.toList.head?.all (fun c => !c.isWhitespace) then break
            acc := acc ++ "\n" ++ nl
            q := q + 1
          return "(" ++ field ++ " :" ++ acc ++ ")"
  -- heads: every declaration head first, then every constructor head
  let mut heads : Array (Nat × Nat) := #[]
  for i in [0:lines.size] do
    if let some c := headOf lines[i]! then heads := heads.push (i, c)
  for i in [0:lines.size] do
    if let some c := ctorOf lines[i]! then heads := heads.push (i, c)
  let pat := ("(" ++ field ++ " :").toList.toArray
  for (i, c) in heads do
    -- the 40 000-character window after the head
    let mut window : Array Char := (lines[i]!.toList.drop c).toArray
    let mut q := i + 1
    while window.size < 40000 && q < lines.size do
      window := window.push '\n' ++ lines[q]!.toList.toArray
      q := q + 1
    window := window.extract 0 (min window.size 40000)
    let mut found : Option Nat := none
    let mut p := 0
    while found.isNone && p + pat.size ≤ window.size do
      if (List.range pat.size).all (fun k => window[p + k]! == pat[k]!) then found := some p
      p := p + 1
    if let some s := found then
      let mut depth : Int := 0
      let mut j := s
      let mut done := false
      while j < window.size && !done do
        if window[j]! == '(' then depth := depth + 1
        else if window[j]! == ')' then depth := depth - 1
        if depth == 0 then done := true else j := j + 1
      return String.ofList ((window.extract s (min window.size (j + 1))).toList)
  return ""

def exampleSrc : Array String := #[
  "structure PendingNode where",
  "  h_vpack : ∃ ns : List Nat, P ns",
  "  h_other : Q",
  "",
  "inductive Node where",
  "  | pendingContent (h_kslot : ∃ (ne : Bool) (nv : Nat), R nv)",
  "",
  "lemma accum_block_pending {sc : ScannerState} (h_vslot : ∃ ks : List FrameLevel,",
  "    ∃ w : Nat, S ks w) (h_alt : PackAlt sc) : True := trivial",
  "lemma accum_block_pending' (h_vslot : ∃ ks : List FrameLevel, ∃ ns : List Nat, T) : True := trivial"]

#guard binderText exampleSrc "PendingNode.mk" "h_vpack" == "(h_vpack : ∃ ns : List Nat, P ns)"
#guard binderText exampleSrc "Node.pendingContent" "h_kslot" == "(h_kslot : ∃ (ne : Bool) (nv : Nat), R nv)"
#guard binderText exampleSrc "accum_block_pending" "h_vslot" == "(h_vslot : ∃ ks : List FrameLevel,\n    ∃ w : Nat, S ks w)"
#guard binderText exampleSrc "accum_block_pending'" "h_vslot" == "(h_vslot : ∃ ks : List FrameLevel, ∃ ns : List Nat, T)"
#guard binderText exampleSrc "accum_block_pending" "h_missing" == ""

def contains (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- `∃ \(?(?:ne )?nv\b` — a bare value slot. -/
def hasSlot (s : String) : Bool := Id.run do
  for part in (s.splitOn "∃ ").drop 1 do
    let cs := part.toList
    let cs := if cs.head? == some '(' then cs.drop 1 else cs
    let cs := if (String.ofList cs).startsWith "ne " then cs.drop 3 else cs
    if (String.ofList cs).startsWith "nv" && boundaryAfter (cs.drop 2) then return true
  return false

/-- `classify`: the ghost datum the binder's `∃` quantifies. -/
def classify (binder : String) : String :=
  let hasKs := contains binder "List FrameLevel" || contains binder "List IndentStackCover.FrameLevel"
  let hasChain := contains binder "List Nat"
  if hasKs && hasChain then "pack"
  else if hasKs then "ks"
  else if hasChain || hasSlot binder then "ns"
  else if contains binder "∃" then "scalar"
  else "none"

#guard classify "(h : ∃ ks : List FrameLevel, ∃ ns : List Nat, T)" == "pack"
#guard classify "(h : ∃ ks : List FrameLevel, ∃ w : Nat, S)" == "ks"
#guard classify "(h : ∃ (ne : Bool) (nv : Nat), R nv)" == "scalar"  -- the Python's regex needs `∃ (nv` or `∃ (ne nv`
#guard classify "(h : ∃ (nv : Nat), R nv)" == "ns"
#guard classify "(h : ∃ ne nv, R nv)" == "ns"
#guard classify "(h : ∃ nvx : Nat, R)" == "scalar"
#guard classify "(h : PackAlt sc)" == "none"

/-- `(\S+) (top|nested) ∨ (PackAlt\S*)` at the start of a position row: the key and the alternative. -/
def positionKey? (p : String) : Option (String × String) :=
  match p.splitOn " " with
  | key :: kind :: "∨" :: alt :: _ =>
    if key ≠ "" && (kind == "top" || kind == "nested") && alt.startsWith "PackAlt" then some (key, alt) else none
  | _ => none

#guard positionKey? "L4YAML.Proofs.StreamAccum.X.mk[6].valueF nested ∨ PackAlt sc" == some ("L4YAML.Proofs.StreamAccum.X.mk[6].valueF", "PackAlt")
#guard positionKey? "L4YAML.Proofs.StreamAccum.X.mk[6].valueF nested ∨ True" == none

/-- `(.*?)\[(\d+|ret)\]\.?(\S*)`: the declaration and the field of a supply key. -/
def supplyKey? (k : String) : Option (String × String) := Id.run do
  let cs := k.toList.toArray
  for i in [0:cs.size] do
    if cs[i]! == '[' then
      let rest := (cs.extract (i + 1) cs.size).toList
      let idx := rest.takeWhile Char.isDigit
      let after := if !idx.isEmpty then some (rest.drop idx.length)
        else if (String.ofList rest).startsWith "ret" then some (rest.drop 3) else none
      if let some (']' :: r) := after then
        let r := if r.head? == some '.' then r.drop 1 else r
        return some (String.ofList (cs.extract 0 i).toList, String.ofList (r.takeWhile (fun c => !c.isWhitespace)))
  return none

#guard supplyKey? "PendingNode.pendingContent[9].h_vpack" == some ("PendingNode.pendingContent", "h_vpack")
#guard supplyKey? "flowKeyRoute_of_open[ret]" == some ("flowKeyRoute_of_open", "")
#guard supplyKey? "noindex" == none

/-- `DECLINE=(\d+)` anywhere in the row, else 0. -/
def declineN (s : String) : Nat :=
  match (s.splitOn "DECLINE=")[1]? with
  | some r => (String.ofList (r.toList.takeWhile Char.isDigit)).toNat?.getD 0
  | none => 0

structure Row where
  cls : String
  n : Nat
  key : String
  rest : String
  deriving Repr, Inhabited, DecidableEq

def stripNs (k : String) : String := if k.startsWith ns then dropS k ns.length else k

def padRight (s : String) (w : Nat) : String := s.pushn ' ' (w - min w s.length)
def padLeft (s : String) (w : Nat) : String := "".pushn ' ' (w - min w s.length) ++ s

/-- The report: the per-field rows, the `RESIDUE-CLASSES` line, the unsupplied fields. `tsv` = the
rows of `pack-census residue --tsv`, when given. -/
def report (positions supply : Array String) (src : Array String) (tsv : Option (Array (Array String))) :
    Array String := Id.run do
  let mut packFields : Array (String × String) := #[]
  for p in positions do
    if let some (k, alt) := positionKey? p then
      if !packFields.any (·.1 == k) then packFields := packFields.push (k, alt)
  let mut rows : Array Row := #[]
  for s in supply do
    let key := (s.splitOn " ").head!
    if !packFields.any (·.1 == key) then continue
    let n := declineN s
    match supplyKey? (stripNs key) with
    | none => continue
    | some (decl, field) =>
      let cls := if field == "" then "conclusion"
        else let b := binderText src decl field; if b == "" then "unread" else classify b
      rows := rows.push { cls, n, key := stripNs key, rest := (s.splitOn " ").tail.foldl (fun a x => if a == "" then x else a ++ " " ++ x) "" }
  let sorted := rows.qsort fun a b =>
    a.cls < b.cls || (a.cls == b.cls && (a.n > b.n || (a.n == b.n && a.key < b.key)))
  let mut out : Array String := #[]
  for r in sorted do
    out := out.push s!"  {padRight r.cls 10} {padLeft (toString r.n) 3}  {r.key}  {r.rest}"
  let total (c : String) : Nat := (rows.filter (·.cls == c)).foldl (fun a r => a + r.n) 0
  let unsupplied := (packFields.filter fun (k, _) => !supply.any (·.startsWith (k ++ " "))).map (fun (k, _) => dropS k ns.length)
  let edges := rows.foldl (fun a r => a + r.n) 0
  let mut line := s!"RESIDUE-CLASSES positions={(positions.filter (contains · "∨ PackAlt")).size} " ++
    s!"fields={packFields.size} declineEdges={edges} " ++
    " ".intercalate (["ns", "ks", "pack", "scalar", "none", "unread"].map fun k => s!"{k}={total k}") ++
    s!" unsuppliedFields={unsupplied.size}"
  if let some trows := tsv then
    let sites := trows.filter fun r => r.size ≥ 7 && r[3]! == "DECLINE"
    let bare := (sites.filter fun r => contains r[6]! "h_alt :=" || contains r[6]! "fun _ => trivial").size
    line := line ++ s!" sites={sites.size} orSites={sites.size - bare} bareParamSites={bare}"
  out := out.push line
  out := out.push ("  unsupplied PackAlt fields: " ++ ", ".intercalate unsupplied.toList)
  return out

#guard report
    #[ns ++ "PendingNode.mk[1].h_vpack top ∨ PackAlt sc", ns ++ "accum_block_pending[3].h_vslot nested ∨ PackAlt sc",
       ns ++ "Node.pendingContent[2].h_kslot top ∨ PackAlt sc", ns ++ "other[1].x top ∨ True"]
    #[ns ++ "PendingNode.mk[1].h_vpack relayed [DECLINE=4 SPLIT=1]", ns ++ "accum_block_pending[3].h_vslot relayed [DECLINE=2]"]
    exampleSrc (some #[#["1", "9", "3", "DECLINE", "d", "m", "x (h_alt := trivial)"], #["1", "9", "3", "DECLINE", "d", "m", "Or.inr trivial"], #["1", "9", "3", "RELAY", "d", "m", "y"]])
  == #["  ks           2  accum_block_pending[3].h_vslot  relayed [DECLINE=2]",
       "  ns           4  PendingNode.mk[1].h_vpack  relayed [DECLINE=4 SPLIT=1]",
       "RESIDUE-CLASSES positions=3 fields=3 declineEdges=6 ns=4 ks=2 pack=0 scalar=0 none=0 unread=0 unsuppliedFields=1 sites=2 orSites=1 bareParamSites=1",
       "  unsupplied PackAlt fields: Node.pendingContent[2].h_kslot"]

end Scripts.Pack.Residue
