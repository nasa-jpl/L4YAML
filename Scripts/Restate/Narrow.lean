module

public import Scripts.Restate.Text
meta import Scripts.Restate.Text

/-!
# `Scripts.Restate.Narrow` — `narrow_conclusion.py`'s edits (item 228)

A declaration whose CONCLUSION is `… ∨ True` is narrowed to `… ∨ False`, the tightest
narrowing, and `lake build` prices the obligation.  `narrow` rewrites the last `∨ True`
of each named declaration's statement (the lines from its `lemma` head to the first
comment-stripped line ending in `:=` / `:= by`); `narrowDeep` also rewrites every
`∨ True` in the proof body up to the next declaration, docstring, `end` or `def` — the
motives — and premises are left alone on purpose (narrowing a premise strengthens the
hypothesis).  A name is resolved under whatever suffix its `namespace` leaves written
(`IndentFloor.transport`, not the full name).
-/

namespace Scripts.Restate.Narrow

open Scripts.Restate

@[expose] public section

def orTrue : String := "∨ True"
def orFalse : String := "∨ False"

/-- `(lemma line, statement end line)`. -/
def statementSpan (lines : Array String) (start : Nat) : Option (Nat × Nat) :=
  (List.range (min (start + 700) lines.size - start)).findSome? fun k =>
    let s := rstrip (stripComment lines[start + k]!)
    if s.endsWith ":=" || s.endsWith ":= by" then some (start, start + k) else none

/-- The LAST `∨ True` inside the statement span — the conclusion's. -/
def conclusionSite (lines : Array String) (lo hi : Nat) : Option (Nat × Nat) :=
  (List.range (hi + 1 - lo)).findSome? fun k =>
    let i := hi - k
    (rfindSub (chars (stripComment lines[i]!)) (chars orTrue)).map (i, ·)

/-- The suffix of the dotted name the file declares, if any. -/
def resolve (at_ : List (String × Nat)) (nm : String) : Option String :=
  let parts := nm.splitOn "."
  (List.range parts.length).findSome? fun i =>
    let k := ".".intercalate (parts.drop i)
    if at_.any (·.1 == k) then some k else none

/-- The line before the next declaration, docstring, `end` or `def`. -/
def declEnd (lines : Array String) (start : Nat) : Nat :=
  match (List.range (lines.size - start - 1)).find? (fun k =>
      let l := lines[start + 1 + k]!
      (declHead? true l).isSome || l.startsWith "/-- " || l.startsWith "/-! " || l.startsWith "end " || l.startsWith "def ") with
  | some k => start + k
  | none => lines.size - 1

def replaceAt (line : String) (c : Nat) : String :=
  let a := chars line
  slice a 0 c ++ orFalse ++ slice a (c + orTrue.length) a.size

/-- `narrow(src, names)` → (lines, narrowed names, skipped with reason). -/
def narrow (src : Array String) (names : List String) : Array String × List String × List (String × String) := Id.run do
  let at_ := declLines true src
  let mut lines := src
  let mut done : List String := []
  let mut skipped : List (String × String) := []
  for nm in names do
    let some short := resolve at_ nm | skipped := skipped ++ [(nm, "no declaration (projection or structure field)")]; continue
    let some (lo, hi) := statementSpan lines (lookup at_ short).get! | skipped := skipped ++ [(nm, "no statement end")]; continue
    let some (i, c) := conclusionSite lines lo hi | skipped := skipped ++ [(nm, "no `∨ True` in the statement")]; continue
    lines := lines.set! i (replaceAt lines[i]! c)
    done := done ++ [nm]
  return (lines, done, skipped)

/-- `narrow_deep(src, names)` → (lines, hits per name in order, skipped). -/
def narrowDeep (src : Array String) (names : List String) : Array String × List (String × Nat) × List (String × String) := Id.run do
  let at_ := declLines true src
  let mut lines := src
  let mut hits : List (String × Nat) := []
  let mut skipped : List (String × String) := []
  for nm in names do
    let some short := resolve at_ nm | skipped := skipped ++ [(nm, "no declaration (projection or structure field)")]; continue
    let start := (lookup at_ short).get!
    let some (lo, hi) := statementSpan lines start | skipped := skipped ++ [(nm, "no statement end")]; continue
    let some (i, c) := conclusionSite lines lo hi | skipped := skipped ++ [(nm, "no `∨ True` in the statement")]; continue
    lines := lines.set! i (replaceAt lines[i]! c)
    let mut k := 1
    let stop := declEnd lines start
    for j in [hi + 1 : stop + 1] do
      let body := stripComment lines[j]!
      let n := countSub body orTrue
      if n > 0 then
        k := k + n
        lines := lines.set! j (body.replace orTrue orFalse ++ (lines[j]!.drop body.length).toString)
    hits := hits ++ [(nm, k)]
  return (lines, hits, skipped)

def sample : Array String := #[
  "namespace Foo",
  "/-- doc -/",
  "lemma IndentFloor.transport (h : A ∨ True) :",
  "    B ∨ True := by",
  "  rcases h with h | _  -- ∨ True here is a comment",
  "  · exact Or.inr trivial",
  "  · exact (Or.inr trivial : B ∨ True)",
  "lemma other : C ∨ True ∨ True :=",
  "  Or.inr trivial",
  "end Foo"]

#guard resolve (declLines true sample) "L4YAML.Foo.IndentFloor.transport" == some "IndentFloor.transport"
#guard resolve (declLines true sample) "nothing.here" == none
#guard statementSpan sample 2 == some (2, 3)
#guard conclusionSite sample 2 3 == some (3, 6)
#guard conclusionSite sample 7 7 == some (7, 23)
#guard declEnd sample 2 == 6
#guard (narrow sample ["Foo.IndentFloor.transport", "other", "gone"]).2.1 == ["Foo.IndentFloor.transport", "other"]
#guard (narrow sample ["Foo.IndentFloor.transport", "other", "gone"]).1[3]! == "    B ∨ False := by"
#guard (narrow sample ["other"]).1[7]! == "lemma other : C ∨ True ∨ False :="
#guard (narrow sample ["gone"]).2.2 == [("gone", "no declaration (projection or structure field)")]
#guard (narrowDeep sample ["IndentFloor.transport"]).2.1 == [("IndentFloor.transport", 2)]
#guard (narrowDeep sample ["IndentFloor.transport"]).1[6]! == "  · exact (Or.inr trivial : B ∨ False)"
#guard (narrowDeep sample ["IndentFloor.transport"]).1[4]! == "  rcases h with h | _  -- ∨ True here is a comment"
#guard (narrowDeep sample ["IndentFloor.transport"]).1[2]! == "lemma IndentFloor.transport (h : A ∨ True) :"

end

end Scripts.Restate.Narrow
