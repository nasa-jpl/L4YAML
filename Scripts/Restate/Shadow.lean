module

public import Scripts.Restate.Text
meta import Scripts.Restate.Text

/-!
# `Scripts.Restate.Shadow` — `decline_all_optional.shadow` (items 226/227)

The roster of optional (`_ ∨ True`) binders is read off the ENVIRONMENT by a probe
(`Scripts.Restate.Probes`); this module is the edit it drives: one
`  have <binder> : <type> := <witness>` inserted under each lemma's `:= by`, shadowing
the premise with the canonical inhabitant.  `witness` and `keep` are the seam item 227
narrows through (`Or.inr trivial` over every row is item 226's measurement exactly;
`Or.inl ⟨[], by simp⟩` over the `chain` rows is item 227's).

The geometry is the Python's: the lemma is the first `lemma NAME`/`theorem NAME` line,
the binder the first `(NAME : ` or `{NAME : ` within 400 lines of it (parenthesis depth
closes it, across lines), the proof the first line within 700 lines of the binder whose
comment-stripped text ends in `:= by` (a bare `:=` is a term-mode proof: skipped), the
type text comment-stripped and whitespace-collapsed.  Rows are skipped, and counted by
reason, when the binder belongs to a constructor, when the lemma, binder or proof is not
found, or when `keep` rejects the row.
-/

namespace Scripts.Restate.Shadow

open Scripts.Restate

@[expose] public section

/-- One `ROSTER` line of a probe: `lemma|binder|index|kind[|chain]`. -/
abbrev Row := Array String

def rowsOf (out : String) : Array Row :=
  (out.splitOn "\n").foldl (init := #[]) fun acc l =>
    let l := strip l
    if l.startsWith "ROSTER " then acc.push (((l.drop 7).toString.splitOn "|").toArray) else acc

def bump (m : List (String × Nat)) (k : String) : List (String × Nat) :=
  if m.any (·.1 == k) then m.map (fun kv => if kv.1 == k then (k, kv.2 + 1) else kv) else m ++ [(k, 1)]

/-- `(binder line, column, end line, end column, opener)` of `(NAME : …)` / `{NAME : …}`. -/
def binderSpan (lines : Array (Array Char)) (start : Nat) (bname : String) :
    Option (Nat × Nat × Nat × Nat × Char) :=
  tryOp '(' ')' <|> tryOp '{' '}'
where
  tryOp (op cl : Char) : Option (Nat × Nat × Nat × Nat × Char) :=
    let pat := chars (String.singleton op ++ bname ++ " : ")
    (List.range (min (start + 400) lines.size - start)).findSome? fun k =>
      let i := start + k
      match findSub lines[i]! pat with
      | none => none
      | some c => scan op cl i c i c 0 (lines.size * 2000 + 1)
  scan (op cl : Char) (i c li ci depth : Nat) : Nat → Option (Nat × Nat × Nat × Nat × Char)
    | 0 => none
    | fuel + 1 =>
      if li ≥ lines.size then none else
      let line := lines[li]!
      let ch := if ci < line.size then line[ci]! else '\n'
      let depth' := if ch == op then depth + 1 else depth
      if ch == cl then
        if depth' - 1 == 0 then some (i, c, li, ci, op)
        else step op cl i c li ci (depth' - 1) fuel
      else step op cl i c li ci depth' fuel
  step (op cl : Char) (i c li ci depth fuel : Nat) : Option (Nat × Nat × Nat × Nat × Char) :=
    let ci := ci + 1
    if ci ≥ lines[li]!.size then scan op cl i c (li + 1) 0 depth fuel else scan op cl i c li ci depth fuel

/-- `(line, is `:= by`)` of the first statement end within 700 lines of `start`. -/
def proofStart (lines : Array (Array Char)) (start : Nat) : Option (Nat × Bool) :=
  (List.range (min (start + 700) lines.size - start)).findSome? fun k =>
    let i := start + k
    let s := rstrip (stripComment (ofChars lines[i]!))
    if s.endsWith ":= by" then some (i, true)
    else if s.endsWith ":=" then some (i, false)
    else none

/-- The binder's type text, comment-stripped per line, whitespace-collapsed. -/
def typeText (lines : Array (Array Char)) (bi bc ei ec : Nat) (head : String) : String :=
  let ty :=
    if bi == ei then stripComment (slice lines[bi]! (bc + head.length) ec)
    else
      let parts := [stripComment (slice lines[bi]! (bc + head.length) lines[bi]!.size)]
        ++ (List.range (ei - bi - 1)).map (fun k => stripComment (ofChars lines[bi + 1 + k]!))
        ++ [stripComment (slice lines[ei]! 0 ec)]
      " ".intercalate (parts.map strip)
  collapseWs ty

structure Result where
  lines : Array String
  shadowed : Nat
  skipped : List (String × Nat)
  deriving Repr

/-- `shadow(rows, witness, keep)` on the file's lines. -/
def shadow (src : Array String) (rows : Array Row) (witness : String) (keep : Row → Bool) : Result := Id.run do
  let lines := src.map chars
  let lemmaAt := declLines false src
  let mut inserts : Array (Nat × String) := #[]
  let mut skipped : List (String × Nat) := []
  for row in rows do
    let lem := row[0]!; let bn := row[1]!; let kind := row[3]!
    if !keep row then skipped := bump skipped "not selected"; continue
    if kind == "ctor" then skipped := bump skipped "constructor field"; continue
    let some start := lookup lemmaAt lem | skipped := bump skipped "no lemma"; continue
    let some (bi, bc, ei, ec, op) := binderSpan lines start bn | skipped := bump skipped "no binder"; continue
    let head := String.singleton op ++ bn ++ " : "
    let ty := typeText lines bi bc ei ec head
    let some (pi, isBy) := proofStart lines ei | skipped := bump skipped "no proof"; continue
    if !isBy then skipped := bump skipped "term-mode proof"; continue
    inserts := inserts.push (pi, s!"  have {bn} : {ty} := {witness}")
  -- `sorted(inserts, key=lambda t: -t[0])` is stable: equal lines keep roster order, and each
  -- later one is inserted at the same `pi + 1`, i.e. ABOVE the earlier one.
  let ordered := inserts.toList.mergeSort fun a b => a.1 ≥ b.1
  let mut out := src
  for (pi, txt) in ordered do
    out := out.insertIdx! (pi + 1) txt
  return { lines := out, shadowed := inserts.size, skipped }

def sampleSrc : Array String := #[
  "lemma foo (x : Nat)",
  "    (h_opt : x = 0 ∨ True) -- optional",
  "    {h_two : (x = 1 ∨",
  "      x = 2) ∨ True} :",
  "    x = x := by",
  "  rfl",
  "lemma bar (h_opt : True ∨ True) : True :=",
  "  trivial",
  "lemma baz (h_opt : True ∨ True) : True := by",
  "  trivial"]

#guard rowsOf "info: x\n  ROSTER foo|h_opt|1|lemma\nother\nROSTER bar|h_opt|0|lemma|chain\n"
  == #[#["foo", "h_opt", "1", "lemma"], #["bar", "h_opt", "0", "lemma", "chain"]]
#guard binderSpan (sampleSrc.map chars) 0 "h_two" == some (2, 4, 3, 19, '{')
#guard binderSpan (sampleSrc.map chars) 0 "nope" == none
#guard proofStart (sampleSrc.map chars) 1 == some (4, true)
#guard proofStart (sampleSrc.map chars) 6 == some (6, false)
#guard (shadow sampleSrc #[#["foo", "h_two", "2", "lemma"], #["foo", "h_opt", "1", "lemma"],
    #["bar", "h_opt", "0", "lemma"], #["baz", "h_opt", "0", "lemma"], #["Ctor", "f", "0", "ctor"],
    #["gone", "h", "0", "lemma"], #["foo", "h_none", "3", "lemma"]] "Or.inr trivial" (fun _ => true)).lines
  == #["lemma foo (x : Nat)", "    (h_opt : x = 0 ∨ True) -- optional", "    {h_two : (x = 1 ∨",
       "      x = 2) ∨ True} :", "    x = x := by",
       "  have h_opt : x = 0 ∨ True := Or.inr trivial",
       "  have h_two : (x = 1 ∨ x = 2) ∨ True := Or.inr trivial",
       "  rfl", "lemma bar (h_opt : True ∨ True) : True :=", "  trivial",
       "lemma baz (h_opt : True ∨ True) : True := by", "  have h_opt : True ∨ True := Or.inr trivial", "  trivial"]
#guard (shadow sampleSrc #[#["foo", "h_two", "2", "lemma"], #["bar", "h_opt", "0", "lemma"],
    #["Ctor", "f", "0", "ctor"], #["gone", "h", "0", "lemma"], #["foo", "h_none", "3", "lemma"],
    #["baz", "h_opt", "0", "lemma", "-"]] "Or.inr trivial" (fun r => r.size < 5)).skipped
  == [("term-mode proof", 1), ("constructor field", 1), ("no lemma", 1), ("no binder", 1), ("not selected", 1)]

end

end Scripts.Restate.Shadow
