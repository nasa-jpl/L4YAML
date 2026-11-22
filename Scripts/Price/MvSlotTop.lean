module

public import Scripts.Price.Attribute
meta import Scripts.Price.Attribute

/-!
# Scripts.Price.MvSlotTop — `mv_slot_top_price.py` (item 209): the SLOT's own stack top

Adds `sc.currentIndent ≤ (n : Int) ∧` to `pendingMapValue.h_vslot`'s left disjunct and
splits the errors into PRODUCERS (anchored on a `PendingNode.pendingMapValue` application
in the same declaration, among the six `*_open_map` lemmas), other applications, and
CONSUMERS (the rest, by declaration); the producers that did not break pay `Or.inr trivial`.
-/

namespace Scripts.Price.MvSlotTop

open Scripts.Price.Attribute

public section

def anchor : String := "      (h_vslot : (sp_scan.col = n + 1 ∧ ∀ sp_v : SurfPos,"
def probeLines : Array String :=
  #["      -- SLOT-TOP PROBE (scripts/mv_slot_top_price.py)",
    "      (h_vslot : (sc.currentIndent ≤ (n : Int) ∧ sp_scan.col = n + 1 ∧ ∀ sp_v : SurfPos,"]
def producers : List String :=
  ["colon_open_map", "question_open_map", "colon_open_map_explicit",
   "compact_open_map", "colon_open_map_implicit", "colon_open_map_props"]
def headline : String := "probe: slot top inside pendingMapValue.h_vslot's left disjunct"

def applyProbe (lines : Array String) : Except String (Array String) := do
  let hits := (Array.range lines.size).filter fun i => rstrip lines[i]! == rstrip anchor
  if hits.size != 1 then throw s!"AssertionError: anchor matched {hits.size} lines"
  return replaceLine lines hits[0]! probeLines

def anchors (patched : Array String) : Array Anchor :=
  (Array.range patched.size).filterMap fun i =>
    let l := patched[i]!
    if (l.splitOn "PendingNode.pendingMapValue").length > 1 && !isComment l then some (i + 1, "") else none

/-- `prior[-1]` counts only when it sits in the error's own declaration. -/
def attributeSameDecl (patched : Array String) (as : Array Anchor) (census : Array Nat) :
    Array (Anchor × Array Nat) × Array Nat := Id.run do
  let mut groups : Array (Anchor × Array Nat) := #[]
  let mut unanchored : Array Nat := #[]
  for raw in census do
    let prior := as.filter (·.1 ≤ raw)
    let decl := enclosingDecl patched raw
    match prior.back? with
    | some a =>
      if enclosingDecl patched a.1 == decl then
        groups := match groups.findIdx? (·.1 == a) with
          | some i => groups.modify i fun (k, hs) => (k, hs.push raw)
          | none => groups.push (a, #[raw])
      else unanchored := unanchored.push raw
    | none => unanchored := unanchored.push raw
  return (groups, unanchored)

def report (patched : Array String) (log : String) : Array String := Id.run do
  let census := sortedNat (errorLines log)
  let (groups, unanchored) := attributeSameDecl patched (anchors patched) census
  let prodHits := groups.filter fun ((a, _), _) => producers.contains (enclosingDecl patched a)
  let otherHits := groups.filter fun g => !prodHits.contains g
  let mut cons : Array (String × Array Nat) := #[]
  for raw in unanchored do cons := addTo cons (enclosingDecl patched raw) raw
  let mut out : Array String := #["", s!"raw error sites: {census.size}",
    s!"PRODUCERS (pay the conjunct):  {prodHits.size}"]
  for ((a, _), h) in stableSort prodHits (fun x y => x.1.1 < y.1.1) do
    out := out.push (s!"    L{a}  {enclosingDecl patched a}" ++ (if h.size > 1 then s!"   [{h.size} raw]" else ""))
  if !otherHits.isEmpty then
    out := out.push s!"other applications:            {otherHits.size}"
    for ((a, _), h) in stableSort otherHits (fun x y => x.1.1 < y.1.1) do
      out := out.push s!"    L{a}  {enclosingDecl patched a}   [{h.size} raw]"
  out := out.push s!"CONSUMERS (read the tuple):    {cons.size} declaration(s), {unanchored.size} raw"
  for (d, hits) in stableSort cons (fun x y => y.2.size < x.2.size) do
    out := out.push s!"    {Scripts.Punt.Price.padLeft (toString hits.size) 3}  {d}"
  let broke := prodHits.map fun ((a, _), _) => enclosingDecl patched a
  let silent := producers.filter fun p => !broke.contains p
  out := out.push "" |>.push s!"producers that did NOT break ({silent.length}) — they pay `Or.inr trivial` and owe nothing:"
  for p in silent do out := out.push s!"    {p}"
  if census.isEmpty then out := out.push "  (none)"
  return out

private def sample : Array String := #[
  "lemma colon_open_map : True := by",
  "  exact PendingNode.pendingMapValue a b",
  "    (by trivial)",
  "lemma reader : True := by",
  "  cases h with | PendingNode.pendingMapValue => ?_",
  "  exact x"]

#guard anchors sample == #[(2, ""), (5, "")]
#guard (applyProbe sample).toOption == none
#guard report sample "L4YAML/Proofs/Production/StreamAccum.lean:3:1: error: a\nL4YAML/Proofs/Production/StreamAccum.lean:2:1: error: b\nL4YAML/Proofs/Production/StreamAccum.lean:6:1: error: c\n" ==
  #["", "raw error sites: 3", "PRODUCERS (pay the conjunct):  1", "    L2  colon_open_map   [2 raw]",
    "other applications:            1", "    L5  reader   [1 raw]",
    "CONSUMERS (read the tuple):    0 declaration(s), 0 raw", "",
    "producers that did NOT break (5) — they pay `Or.inr trivial` and owe nothing:",
    "    question_open_map", "    colon_open_map_explicit", "    compact_open_map",
    "    colon_open_map_implicit", "    colon_open_map_props"]

end

end Scripts.Price.MvSlotTop
