module

/-!
# Scripts.TraceOf.Gen — the pure half of `lake run gen-traceof`

The port of `scripts/gen_traceof.py` (Rule 9 phase 2).  Given the mutual block of
`L4YAML/Surface/Node.lean` as data — each inductive's name, signature text and
constructors, each constructor's name, binder text, premise texts and conclusion
text — compute the event-annotated twin block `TraceOf/Node.lean` holds: the
event-*bearing* closure (a production is bearing when one of its premises names a
bearing production; the hand-written leaves `SCNsProperties` / `SCNsAliasNode`
seed it), the annotated form of each premise (`T<Name>` with one more `ev` index,
`Lift` for the productions without events, the combinators `GOpt`/`GStar`/…
rewritten to `TOpt`/`TStar`/…), and the constructor's concluding concatenation of
its event lists in text order.  Reading the block off the syntax tree is
`Scripts.Main.GenTraceOf`.

Each reading is pinned by a `#guard` on the Python's own shapes.  Terms are read
with the Python's tokenizer — `⟨…⟩` is one token, parentheses group — so a
rewritten premise prints as the Python printed it.
-/

namespace Scripts.TraceOf.Gen

public section

/-- A term as the Python tokenized it: an atom, or a parenthesised group. -/
inductive Tm where
  | atom (s : String)
  | group (xs : List Tm)
  deriving Repr, BEq, Inhabited

/-- `tokenize`: whitespace separates, `(` `)` are tokens, `⟨…⟩` (nested) is one token,
    anything else runs to the next space, parenthesis or angle bracket. -/
def tokenize (s : String) : List String := Id.run do
  let mut cs := s.toList
  let mut toks : Array String := #[]
  while !cs.isEmpty do
    match cs with
    | c :: t =>
      if c.isWhitespace then cs := t
      else if c == '⟨' then
        let mut depth := 0
        let mut tok : List Char := []
        let mut rest := cs
        let mut go := true
        while go do
          match rest with
          | [] => go := false
          | d :: r =>
            tok := tok ++ [d]; rest := r
            if d == '⟨' then depth := depth + 1
            else if d == '⟩' then
              depth := depth - 1
              if depth == 0 then go := false
        toks := toks.push (String.ofList tok); cs := rest
      else if c == '(' || c == ')' then toks := toks.push c.toString; cs := t
      else
        let run := cs.takeWhile fun d => !d.isWhitespace && d != '(' && d != ')' && d != '⟨' && d != '⟩'
        if run.isEmpty then cs := t   -- a stray `⟩`: the Python never terminated; skip it
        else toks := toks.push (String.ofList run); cs := cs.drop run.length
    | [] => pure ()
  return toks.toList

#guard tokenize "GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂"
  == ["GOpt", "(", "GSeq", "(", "SCNsProperties", "n", "c", ")", "(", "SSeparate", "n", "c", ")", ")", "s₁", "s₂"]
#guard tokenize "SFoo ⟨a, (b ⟨c⟩)⟩ s" == ["SFoo", "⟨a, (b ⟨c⟩)⟩", "s"]
#guard tokenize "  x\n  y " == ["x", "y"]

/-- `parse`: parenthesised groups to nested lists (an unbalanced `)` closes nothing). -/
def parseToks (toks : List String) : List Tm := Id.run do
  let mut stack : Array (Array Tm) := #[#[]]
  for t in toks do
    if t == "(" then stack := stack.push #[]
    else if t == ")" then
      if stack.size > 1 then
        let g := stack.back!
        stack := stack.pop
        stack := stack.modify (stack.size - 1) (·.push (.group g.toList))
    else stack := stack.modify (stack.size - 1) (·.push (.atom t))
  return stack[0]!.toList

def parseTerm (s : String) : List Tm := parseToks (tokenize s)

partial def Tm.show : Tm → String
  | .atom s => s
  | .group xs => "(" ++ " ".intercalate (xs.map Tm.show) ++ ")"

def Tm.head : Tm → String
  | .atom s => s
  | .group (x :: _) => x.head
  | .group [] => ""

def Tm.args : Tm → List Tm
  | .group (_ :: xs) => xs
  | _ => []

#guard parseTerm "GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂"
  == [.atom "GOpt", .group [.atom "GSeq", .group [.atom "SCNsProperties", .atom "n", .atom "c"], .group [.atom "SSeparate", .atom "n", .atom "c"]], .atom "s₁", .atom "s₂"]
#guard (Tm.group (parseTerm "GSeq (A x) (B y)")).show == "(GSeq (A x) (B y))"

/-- The hand-written leaves that seed the bearing closure. -/
def leaves : List String := ["SCNsProperties", "SCNsAliasNode"]

/-- The combinators and how many relation arguments each takes before its positions. -/
def comb : List (String × Nat) :=
  [("GOpt", 1), ("GStar", 1), ("GPlus", 1), ("GSeq", 2), ("GSeq3", 3), ("GAlt", 2)]

def combArity? (h : String) : Option Nat := (comb.find? (·.1 == h)).map (·.2)

/-- `^[SG]\w+$` on an atom (ASCII word characters, as every production name is). -/
def isRelName (s : String) : Bool :=
  match s.toList with
  | c :: rest => (c == 'S' || c == 'G') && !rest.isEmpty && rest.all fun d => d.isAlphanum || d == '_'
  | [] => false

#guard isRelName "SBlockNode" && isRelName "GOpt" && !isRelName "n" && !isRelName "S" && !isRelName "s'"

partial def relNames : Tm → List String
  | .atom s => if isRelName s then [s] else []
  | .group xs => xs.flatMap relNames

structure Ctor where
  name : String
  binders : String
  premises : Array String
  concl : String
  deriving Repr, BEq, Inhabited

structure Ind where
  name : String
  sig : String
  ctors : Array Ctor
  deriving Repr, BEq, Inhabited

/-- `closure`: the least set containing the leaves and every inductive one of whose
    premises names a member. -/
partial def bearing (inds : Array Ind) : List String :=
  let rec go (b : List String) : List String :=
    let b' := inds.foldl (init := b) fun b i =>
      if b.contains i.name then b
      else if i.ctors.any (fun c => c.premises.any fun p =>
          (relNames (.group (parseTerm p))).any b.contains) then b ++ [i.name]
      else b
    if b'.length == b.length then b else go b'
  go leaves

def tname (n : String) : String := "T" ++ String.ofList (n.toList.drop 1)

/-- `rel_bearing`: a bearing head, or a combinator one of whose relation arguments is. -/
partial def relBearing (b : List String) (e : Tm) : Bool :=
  let h := e.head
  if b.contains h then true
  else match combArity? h with
    | some n => (e.args.take n).any (relBearing b)
    | none => false

/-- `trel`: the annotated relation (positions and `ev` left to the caller). -/
partial def trel (b : List String) (e : Tm) : String :=
  let h := e.head
  let args := e.args
  if b.contains h then
    if args.isEmpty then tname h
    else "(" ++ " ".intercalate (tname h :: args.map Tm.show) ++ ")"
  else match combArity? h with
    | some n =>
      let subs := (args.take n).map fun a => if relBearing b a then trel b a else "(Lift " ++ a.show ++ ")"
      "(T" ++ String.ofList (h.toList.drop 1) ++ " " ++ " ".intercalate subs ++ ")"
    | none => "(Lift " ++ e.show ++ ")"

/-- `premise`: one premise rewritten, with the event list it binds (if any). -/
def premise (b : List String) (p : String) (k : Nat) : String × Bool :=
  let e := parseTerm p
  let h := (Tm.group e).head
  if h == "GNot" then (p, false)
  else match combArity? h with
    | some n =>
      let rels := (e.drop 1).take n
      if !rels.any (relBearing b) then (p, false)
      else
        let rel := trel b (.group ([Tm.atom h] ++ rels))
        let pos := (e.drop 1).drop n
        let ev := s!"ev{k + 1}"
        (s!"{rel} {" ".intercalate (pos.map Tm.show)} {ev}", true)
    | none =>
      if b.contains h then
        let ev := s!"ev{k + 1}"
        (s!"{tname h} {" ".intercalate ((e.drop 1).map Tm.show)} {ev}", true)
      else (p, false)

private def b0 : List String := ["SCNsProperties", "SCNsAliasNode", "SBlockSeqEntries", "SFlowNode"]

#guard premise b0 "SSeparate n c s s₁" 0 == ("SSeparate n c s s₁", false)
#guard premise b0 "GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂" 0
  == ("(TOpt (TSeq (TCNsProperties n c) (Lift (SSeparate n c)))) s₁ s₂ ev1", true)
#guard premise b0 "GOpt (GSeq (SSeparate n c) (SCNsProperties n c)) s s₁" 0
  == ("(TOpt (TSeq (Lift (SSeparate n c)) (TCNsProperties n c))) s s₁ ev1", true)
#guard premise b0 "SBlockSeqEntries (seqSpaces n c + m) s₂ s'" 1 == ("TBlockSeqEntries (seqSpaces n c + m) s₂ s' ev2", true)
#guard premise b0 "GNot SNsChar s₂" 0 == ("GNot SNsChar s₂", false)
#guard premise b0 "GStar (SSeparate n c) s s'" 0 == ("GStar (SSeparate n c) s s'", false)
#guard premise b0 "GAlt (SFlowNode n c) SFoo s s'" 2 == ("(TAlt (TFlowNode n c) (Lift SFoo)) s s' ev3", true)
#guard premise b0 "SFlowNode n .flowOut s₁ s₂" 0 == ("TFlowNode n .flowOut s₁ s₂ ev1", true)

/-- `emit`: the twin inductives, one line per entry, a blank line after each. -/
def emit (inds : Array Ind) : Array String := Id.run do
  let b := bearing inds
  let mut out : Array String := #[]
  for i in inds do
    if !b.contains i.name then continue
    let tsig := i.sig.replace "SurfPos → SurfPos → Prop" "SurfPos → SurfPos → List Event → Prop"
    out := out.push s!"  /-- Event-annotated `{i.name}`. -/"
    out := out.push s!"  inductive {tname i.name} : {tsig} where"
    for c in i.ctors do
      let mut evs : Array String := #[]
      let mut tprem : Array String := #[]
      for p in c.premises do
        let (t, bound) := premise b p evs.size
        if bound then evs := evs.push s!"ev{evs.size + 1}"
        tprem := tprem.push t
      let ce := parseTerm c.concl
      let tconcl := " ".intercalate (tname (Tm.group ce).head :: (ce.drop 1).map Tm.show)
      let evexpr := if evs.isEmpty then "[]" else " ++ ".intercalate evs.toList
      let bs := c.binders ++ (if evs.isEmpty then "" else s!" ({" ".intercalate evs.toList} : List Event)")
      out := out.push s!"    | {c.name} {bs} :"
      for tp in tprem do out := out.push s!"        {tp} →"
      out := out.push s!"        {tconcl} ({evexpr})"
    out := out.push ""
  return out

private def sampleInds : Array Ind := #[
  { name := "SBlockNode", sig := "Nat → YamlContext → SurfPos → SurfPos → Prop", ctors := #[
    { name := "blockSeq", binders := "(n : Nat) (c : YamlContext) (m : Nat) (s s₁ s₂ s' : SurfPos)",
      premises := #["GOpt (GSeq (SSeparate n c) (SCNsProperties n c)) s s₁", "SSLComments s₁ s₂", "SBlockSeqEntries (seqSpaces n c + m) s₂ s'"],
      concl := "SBlockNode n c s s'" },
    { name := "emptyNode", binders := "(n : Nat) (c : YamlContext) (s s' : SurfPos)",
      premises := #["SSLComments s s'"], concl := "SBlockNode n c s s'" }] },
  { name := "SBlockSeqEntries", sig := "Nat → SurfPos → SurfPos → Prop", ctors := #[
    { name := "one", binders := "(n : Nat) (s s' : SurfPos)", premises := #["SBlockNode n .blockIn s s'"], concl := "SBlockSeqEntries n s s'" }] },
  { name := "SPlain", sig := "SurfPos → SurfPos → Prop", ctors := #[
    { name := "p", binders := "(s s' : SurfPos)", premises := #["SNsChar s s'"], concl := "SPlain s s'" }] }]

#guard bearing sampleInds == ["SCNsProperties", "SCNsAliasNode", "SBlockNode", "SBlockSeqEntries"]
#guard emit sampleInds == #[
  "  /-- Event-annotated `SBlockNode`. -/",
  "  inductive TBlockNode : Nat → YamlContext → SurfPos → SurfPos → List Event → Prop where",
  "    | blockSeq (n : Nat) (c : YamlContext) (m : Nat) (s s₁ s₂ s' : SurfPos) (ev1 ev2 : List Event) :",
  "        (TOpt (TSeq (Lift (SSeparate n c)) (TCNsProperties n c))) s s₁ ev1 →",
  "        SSLComments s₁ s₂ →",
  "        TBlockSeqEntries (seqSpaces n c + m) s₂ s' ev2 →",
  "        TBlockNode n c s s' (ev1 ++ ev2)",
  "    | emptyNode (n : Nat) (c : YamlContext) (s s' : SurfPos) :",
  "        SSLComments s s' →",
  "        TBlockNode n c s s' ([])",
  "",
  "  /-- Event-annotated `SBlockSeqEntries`. -/",
  "  inductive TBlockSeqEntries : Nat → SurfPos → SurfPos → List Event → Prop where",
  "    | one (n : Nat) (s s' : SurfPos) (ev1 : List Event) :",
  "        TBlockNode n .blockIn s s' ev1 →",
  "        TBlockSeqEntries n s s' (ev1)",
  ""]

/-- The generated module around `emit`'s block; `header` names the generator. -/
def render (inds : Array Ind) : String :=
  let head := "/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- GENERATED by `lake run gen-traceof` from L4YAML/Surface/Node.lean — do not edit.
module

public import L4YAML.Proofs.Serialization.TraceOf.Leaves

namespace L4YAML.Proofs.Serialization.TraceOf

@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed

mutual
"
  head ++ "\n" ++ "\n".intercalate (emit inds).toList ++ "\n" ++ "end\n\nend\n\nend L4YAML.Proofs.Serialization.TraceOf\n"

/-- Python's `repr` of a list of plain names. -/
def pyList (xs : List String) : String := "[" ++ ", ".intercalate (xs.map fun s => "'" ++ s ++ "'") ++ "]"

#guard pyList ["a", "b"] == "['a', 'b']"
#guard pyList [] == "[]"

/-- `--report`. -/
def report (inds : Array Ind) : Array String :=
  let b := bearing inds
  let names := inds.toList.map (·.name)
  let sorted (l : List String) : List String := (l.toArray.qsort (· < ·)).toList
  #[s!"mutual inductives: {pyList names}",
    s!"bearing: {pyList (sorted b)}",
    s!"non-bearing: {pyList (sorted (names.filter (!b.contains ·)))}"]
  ++ inds.map fun i => s!"  {i.name}: {i.ctors.size} ctors"

#guard report sampleInds == #["mutual inductives: ['SBlockNode', 'SBlockSeqEntries', 'SPlain']",
  "bearing: ['SBlockNode', 'SBlockSeqEntries', 'SCNsAliasNode', 'SCNsProperties']",
  "non-bearing: ['SPlain']", "  SBlockNode: 2 ctors", "  SBlockSeqEntries: 1 ctors", "  SPlain: 1 ctors"]

/-- `strip_comments` on a term's source text: `/- … -/` (nested once as the Python's
    non-greedy match read it) and `-- …` to end of line removed. -/
def stripComments (s : String) : String := Id.run do
  let mut cs := s.toList
  let mut out : List Char := []
  while !cs.isEmpty do
    match cs with
    | '/' :: '-' :: t =>
      let mut rest := t
      let mut go := true
      while go do
        match rest with
        | '-' :: '/' :: r => rest := r; go := false
        | _ :: r => rest := r
        | [] => go := false
      cs := rest
    | '-' :: '-' :: t => cs := t.dropWhile (· != '\n')
    | c :: t => out := out ++ [c]; cs := t
    | [] => pure ()
  return String.ofList out

#guard stripComments "SFoo n /- note -/ s s'" == "SFoo n  s s'"
#guard stripComments "SFoo n s s' -- trailing\n" == "SFoo n s s' \n"
#guard stripComments "a -/ b" == "a -/ b"

end

end Scripts.TraceOf.Gen
