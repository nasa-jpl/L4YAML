module

public import L4YAML.Scanner.Scanner

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Align — a column-aligning YAML formatter

`L4YAML.Align.format` rewrites a YAML text so that, inside each block
mapping, the values of `key: value` entries start in the same column, and so
do the nodes of `key: &anchor value` / `key: !tag value` entries (a second
column for the node after the properties).  It is a *whitespace-only*
transformation:

* The scanner (`scanWithComments`) locates every block-mapping entry whose
  key, `:` indicator and value start lie on one line.
* Only the whitespace run between `:` and what follows it, and the run
  between the last node property and the node, are rewritten.  Comments,
  blank lines, block-scalar bodies, flow collections, quoting and
  continuation lines are copied byte for byte.
* The result is re-scanned and must yield the same tokens and the same
  comments (positions aside); otherwise `format` refuses and returns the
  error instead of a changed text (fail-closed).

Group shape and the "reasonable" cap are configured by `AlignConfig`:

* `grouping := .mapping` aligns a whole block mapping (blank and comment
  lines do not split it); `.run` splits a mapping at blank lines.
* `maxCell` caps the key cell (key start to value start, inclusive of the
  colon and the gap).  A key wider than the cap keeps `minGap` spaces and
  does not drag the rest of its group to the right.
* `round` pads every cell up to a multiple of `round` columns.

What is proved (`L4YAML.Proofs.Output.AlignProofs`): the edit application
preserves every non-blank character in order (hence the line structure),
`format` succeeds only with token- and comment-identical output, and the
cell arithmetic never produces a gap narrower than `minGap`.
-/

namespace L4YAML.Align

open L4YAML.Scanner

/-- How entries are grouped for alignment. -/
inductive Grouping where
  /-- One group per block mapping; blank and comment lines do not split it. -/
  | mapping
  /-- A block mapping is split into runs at blank (whitespace-only) lines. -/
  | run
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Formatter configuration. -/
structure AlignConfig where
  grouping : Grouping := .mapping
  /-- Widest key cell (key start → value start, colon and gap included) that
      still takes part in alignment; wider keys are outliers. -/
  maxCell : Nat := 40
  /-- Cells are padded to a multiple of this many columns (`1` = no rounding). -/
  round : Nat := 1
  /-- Minimum number of spaces after `:` and after a node property. -/
  minGap : Nat := 1
  deriving Repr, BEq, Inhabited

/-! ## Edits over the character list -/

/-- A blank character for alignment purposes (`s-white`, §5.5 [33]). -/
def isWhite (c : Char) : Bool := c == ' ' || c == '\t'

/-- Replace the characters at indices `[start, stop)` by `width` spaces —
    applied only when that region is blank. -/
structure Edit where
  start : Nat
  stop : Nat
  width : Nat
  deriving Repr, BEq, Inhabited

/-- Apply ascending, non-overlapping edits in one left-to-right pass.  `pos`
    is the absolute index of the head of `l`.  An edit that is out of order,
    inverted, or whose region is not blank is skipped. -/
def applyEditsFrom (pos : Nat) : List Edit → List Char → List Char
  | [], l => l
  | e :: es, l =>
    if pos ≤ e.start ∧ e.start ≤ e.stop then
      let pre := l.take (e.start - pos)
      let mid := (l.drop (e.start - pos)).take (e.stop - e.start)
      if mid.all isWhite then
        pre ++ List.replicate e.width ' ' ++ applyEditsFrom e.stop es (l.drop (e.stop - pos))
      else applyEditsFrom pos es l
    else applyEditsFrom pos es l

/-- Apply a list of edits (sorted by `start` first) to a string. -/
def applyEdits (edits : Array Edit) (s : String) : String :=
  let sorted := edits.qsort (fun a b => a.start < b.start)
  String.ofList (applyEditsFrom 0 sorted.toList s.toList)

/-! ## Cell arithmetic -/

/-- Round `x` up to a multiple of `r` (`r ≤ 1`: identity). -/
def roundUp (x r : Nat) : Nat :=
  if r ≤ 1 then x else ((x + r - 1) / r) * r

lemma le_roundUp (x r : Nat) : x ≤ roundUp x r := by
  unfold roundUp
  split
  · exact Nat.le_refl x
  · rename_i h
    have hr : 0 < r := by omega
    have hd := Nat.div_add_mod (x + r - 1) r
    rw [Nat.mul_comm] at hd
    have hm := Nat.mod_lt (x + r - 1) hr
    omega

/-- The common cell width of a group: the largest cell at most `maxCell`,
    rounded.  `none` when no cell fits. -/
def groupTarget (cells : List Nat) (maxCell round : Nat) : Option Nat :=
  match cells.filter (· ≤ maxCell) with
  | [] => none
  | c :: cs => some (roundUp (cs.foldl max c) round)

lemma le_foldl_max (c : Nat) (cs : List Nat) : c ≤ cs.foldl max c := by
  induction cs generalizing c with
  | nil => exact Nat.le_refl c
  | cons d ds ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left c d) (ih (max c d))

lemma mem_le_foldl_max (c : Nat) (cs : List Nat) (x : Nat) (hx : x ∈ cs) :
    x ≤ cs.foldl max c := by
  induction cs generalizing c with
  | nil => cases hx
  | cons d ds ih =>
    simp only [List.foldl_cons]
    cases hx with
    | head => exact Nat.le_trans (Nat.le_max_right c x) (le_foldl_max _ _)
    | tail _ h => exact ih (max c d) h

/-- Every fitting cell is at most the group target. -/
lemma le_groupTarget (cells : List Nat) (maxCell round c t : Nat)
    (hc : c ∈ cells) (hfit : c ≤ maxCell)
    (ht : groupTarget cells maxCell round = some t) : c ≤ t := by
  unfold groupTarget at ht
  have hmem : c ∈ cells.filter (· ≤ maxCell) := by
    rw [List.mem_filter]; exact ⟨hc, by simpa using hfit⟩
  split at ht
  · rename_i h; rw [h] at hmem; cases hmem
  · rename_i d ds h
    cases ht
    rw [h] at hmem
    apply Nat.le_trans _ (le_roundUp _ _)
    cases hmem with
    | head => exact le_foldl_max _ _
    | tail _ hm => exact mem_le_foldl_max _ _ _ hm

/-- The width of the gap after a `:` (or a property) sitting at column
    `cellStart + used` inside a cell of width `cell`, when the cell fits the
    target `t`; outliers get `minGap`. -/
def gapWidth (fits : Bool) (t used minGap : Nat) : Nat :=
  if fits then t - used else minGap

/-- A gap is never narrower than `minGap` when `used + minGap ≤ t`. -/
lemma minGap_le_gapWidth (fits : Bool) (t used minGap : Nat)
    (h : fits = true → used + minGap ≤ t) : minGap ≤ gapWidth fits t used minGap := by
  unfold gapWidth
  cases fits with
  | false => simp
  | true => simp only [ite_true]; have := h rfl; omega

/-! ## Entries -/

/-- One alignable block-mapping entry, in columns (characters) of its line. -/
structure Entry where
  /-- Line of the key, the `:` and the start of the value. -/
  line : Nat
  /-- Column of the first character of the key (a property, if the key has one). -/
  keyCol : Nat
  /-- Column of the `:` indicator. -/
  colonCol : Nat
  /-- Column of the first token after `:` (a node property or the node). -/
  firstCol : Nat
  /-- When the entry has node properties followed by the node on the same
      line: (column just past the last property, column of the node). -/
  propNode : Option (Nat × Nat)
  /-- Identity of the block mapping the entry belongs to. -/
  mapId : Nat
  deriving Repr, BEq, Inhabited

/-- Start of a node that can sit inline after `:` or after a property. -/
def isInlineNodeStart : YamlToken → Bool
  | .scalar .. | .alias .. | .flowSequenceStart | .flowMappingStart => true
  | _ => false

/-- A node property token. -/
def isProperty : YamlToken → Bool
  | .anchor .. | .tag .. => true
  | _ => false

/-- Character index of the start of every line, following the scanner's line
    counting (`\n`, `\r\n` and a lone `\r` each end a line). A leading byte-order
    mark is skipped by the scanner before it starts counting columns, so the
    first line starts after it. -/
def lineStarts (chars : Array Char) : Array Nat := Id.run do
  let bom := if chars.size > 0 && chars[0]! == '\uFEFF' then 1 else 0
  let mut starts : Array Nat := #[bom]
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    if c == '\n' then
      starts := starts.push (i + 1)
    else if c == '\r' then
      if i + 1 < chars.size && chars[i + 1]! == '\n' then
        starts := starts.push (i + 2)
        i := i + 1
      else
        starts := starts.push (i + 1)
    i := i + 1
  return starts

/-- A line consisting of blanks only (or an empty line). -/
def isBlankLine (chars : Array Char) (starts : Array Nat) (line : Nat) : Bool := Id.run do
  let s := starts.getD line chars.size
  let e := starts.getD (line + 1) chars.size
  let mut i := s
  while i < e do
    let c := chars[i]!
    if !(isWhite c || c == '\n' || c == '\r') then return false
    i := i + 1
  return true

/-- Index of the first non-blank character at or before `idx` on its line,
    scanning backwards from `idx` (exclusive) — i.e. the end of the token
    preceding the blank run that ends at `idx`. -/
def blankRunStart (chars : Array Char) (idx : Nat) : Nat := Id.run do
  let mut j := idx
  while j > 0 && isWhite chars[j - 1]! do
    j := j - 1
  return j

/-- A frame of the structural stack while walking the token stream. -/
inductive Frame where
  | blockMap (id : Nat)
  | blockSeq
  | flow
  deriving Repr, BEq, Inhabited

/-- Collect the alignable entries from a scanned token stream. -/
def collectEntries (chars : Array Char) (starts : Array Nat)
    (toks : Array (Positioned YamlToken)) : Array Entry := Id.run do
  let mut entries : Array Entry := #[]
  let mut stack : List Frame := []
  let mut nextId := 0
  let mut lastKey : Option (Nat × Nat) := none   -- (line, keyCol)
  let n := toks.size
  for i in [:n] do
    let t := toks[i]!
    match t.val with
    | .blockMappingStart =>
      stack := .blockMap nextId :: stack
      nextId := nextId + 1
    | .blockSequenceStart => stack := .blockSeq :: stack
    | .flowSequenceStart | .flowMappingStart => stack := .flow :: stack
    | .blockEnd | .flowSequenceEnd | .flowMappingEnd => stack := stack.tail
    | .key =>
      match stack with
      | .blockMap _ :: _ =>
        if i + 1 < n then
          let k := toks[i + 1]!
          lastKey := if k.pos.line == t.pos.line then some (k.pos.line, k.pos.col) else none
        else lastKey := none
      | _ => lastKey := none
    | .value =>
      match stack, lastKey with
      | .blockMap id :: _, some (kline, kcol) =>
        if kline == t.pos.line && i + 1 < n && toks[i + 1]!.pos.line == t.pos.line
            && (isProperty toks[i + 1]!.val || isInlineNodeStart toks[i + 1]!.val) then
          let firstCol := toks[i + 1]!.pos.col
          -- walk the property run
          let mut j := i + 1
          while j < n && toks[j]!.pos.line == t.pos.line && isProperty toks[j]!.val do
            j := j + 1
          let propNode :=
            if j > i + 1 && j < n && toks[j]!.pos.line == t.pos.line
                && isInlineNodeStart toks[j]!.val then
              let nodeCol := toks[j]!.pos.col
              let nodeIdx := starts.getD t.pos.line 0 + nodeCol
              let propEnd := blankRunStart chars nodeIdx - starts.getD t.pos.line 0
              some (propEnd, nodeCol)
            else none
          entries := entries.push
            { line := t.pos.line, keyCol := kcol, colonCol := t.pos.col,
              firstCol := firstCol, propNode := propNode, mapId := id }
        lastKey := none
      | _, _ => lastKey := none
    | _ => pure ()
  return entries

/-- Assign group identities: the mapping id, refined by blank-line runs under
    `Grouping.run`.  Entries arrive in document order. -/
def assignGroups (cfg : AlignConfig) (chars : Array Char) (starts : Array Nat)
    (entries : Array Entry) : Array (Entry × Nat) := Id.run do
  match cfg.grouping with
  | .mapping => return entries.map fun e => (e, e.mapId)
  | .run =>
    -- A run id is allocated per (mapId, segment); segments change at blank lines.
    let mut out : Array (Entry × Nat) := #[]
    let mut lastOfMap : Array (Nat × Nat × Nat) := #[]  -- (mapId, lastLine, runId)
    let mut nextRun := 0
    for e in entries do
      match lastOfMap.findIdx? (fun p => p.1 == e.mapId) with
      | some k =>
        let (_, lastLine, runId) := lastOfMap[k]!
        let mut blank := false
        for l in [lastLine + 1 : e.line] do
          if isBlankLine chars starts l then blank := true
        let runId' := if blank then nextRun else runId
        if blank then nextRun := nextRun + 1
        lastOfMap := lastOfMap.set! k (e.mapId, e.line, runId')
        out := out.push (e, runId')
      | none =>
        lastOfMap := lastOfMap.push (e.mapId, e.line, nextRun)
        out := out.push (e, nextRun)
        nextRun := nextRun + 1
    return out

/-- The key cell an entry needs: key start → value start, with the minimum gap. -/
def keyCell (cfg : AlignConfig) (e : Entry) : Nat :=
  e.colonCol + 1 - e.keyCol + cfg.minGap

/-- Plan the edits of one group. -/
def planGroup (cfg : AlignConfig) (starts : Array Nat) (group : Array Entry) : Array Edit := Id.run do
  let cells := group.toList.map (keyCell cfg)
  let t1 := groupTarget cells cfg.maxCell cfg.round
  let mut edits : Array Edit := #[]
  -- first column: the value (or its first property)
  let mut placed : Array (Entry × Nat × Bool) := #[]   -- entry, new first column, fits
  for e in group do
    let cell := keyCell cfg e
    let fits := cell ≤ cfg.maxCell && t1.isSome
    let w := gapWidth fits (t1.getD 0) (e.colonCol + 1 - e.keyCol) cfg.minGap
    let ls := starts.getD e.line 0
    edits := edits.push { start := ls + e.colonCol + 1, stop := ls + e.firstCol, width := w }
    placed := placed.push (e, e.colonCol + 1 + w, fits)
  -- second column: the node after the properties. An entry takes part only if
  -- it took part in the first column (an outlier key must not drag the node
  -- column either) and its property cell is itself within the cap.
  let withProps := placed.filterMap fun (e, vcol, fits1) =>
    e.propNode.map fun (propEnd, nodeCol) =>
      let pw := propEnd - e.firstCol
      (e, vcol, pw, nodeCol, fits1 && pw + cfg.minGap ≤ cfg.maxCell)
  let cells2 := withProps.toList.map fun (e, vcol, pw, _, _) => vcol + pw + cfg.minGap - e.keyCol
  let fits2 := withProps.toList.filterMap fun (e, vcol, pw, _, ok) =>
    if ok then some (vcol + pw + cfg.minGap - e.keyCol) else none
  let t2 := groupTarget fits2 (cells2.foldl max 0) cfg.round
  for (e, vcol, pw, nodeCol, ok) in withProps do
    let fits := ok && t2.isSome
    let w := gapWidth fits (t2.getD 0) (vcol + pw - e.keyCol) cfg.minGap
    let ls := starts.getD e.line 0
    let propEnd := e.firstCol + pw
    edits := edits.push { start := ls + propEnd, stop := ls + nodeCol, width := w }
  return edits

/-- Plan every edit of a token stream. -/
def planEdits (cfg : AlignConfig) (chars : Array Char) (starts : Array Nat)
    (toks : Array (Positioned YamlToken)) : Array Edit := Id.run do
  let grouped := assignGroups cfg chars starts (collectEntries chars starts toks)
  let ids := (grouped.map (·.2)).toList.eraseDups
  let mut edits : Array Edit := #[]
  for g in ids do
    let group := (grouped.filter (·.2 == g)).map (·.1)
    edits := edits ++ planGroup cfg starts group
  return edits

/-- Align `s` given its scanned tokens (no re-scan check). -/
def alignText (cfg : AlignConfig) (s : String) (toks : Array (Positioned YamlToken)) : String :=
  let chars := s.toList.toArray
  let starts := lineStarts chars
  applyEdits (planEdits cfg chars starts toks) s

/-! ## The fail-closed formatter -/

/-- Why `format` refused. -/
inductive AlignError where
  /-- The input does not scan. -/
  | scanError (e : ScanError)
  /-- The aligned text does not scan (should be unreachable; reported, not hidden). -/
  | rescanError (e : ScanError)
  /-- The aligned text scans to different tokens or comments (should be
      unreachable; reported, not hidden). -/
  | drift
  deriving Repr, Inhabited

instance : ToString AlignError where
  toString
    | .scanError e => s!"input does not scan: {e}"
    | .rescanError e => s!"refused: aligned text does not scan ({e}); input left unchanged"
    | .drift => "refused: aligned text scans differently; input left unchanged"

/-- Token values and comment texts of a scan — what alignment must preserve. -/
def scanShape (s : String) : Option (Array YamlToken × Array String) :=
  match scanWithComments s with
  | .ok (toks, cms) => some (toks.map (·.val), cms.map (·.2))
  | .error _ => none

/-- Align `s`; succeed only when the result has the same `scanShape`. -/
def format (cfg : AlignConfig) (s : String) : Except AlignError String :=
  match scanWithComments s with
  | .error e => .error (.scanError e)
  | .ok (toks, cms) =>
    let out := alignText cfg s toks
    match scanWithComments out with
    | .error e => .error (.rescanError e)
    | .ok (toks', cms') =>
      if toks.map (·.val) = toks'.map (·.val) ∧ cms.map (·.2) = cms'.map (·.2)
      then .ok out else .error .drift

/-! ## Command-line options (shared by `l4yaml-fmt` and `aligntest`) -/

structure Options where
  cfg : AlignConfig := {}
  write : Bool := false
  check : Bool := false
  help : Bool := false
  showVersion : Bool := false
  files : Array String := #[]

def parseNat (flag v : String) : Except String Nat :=
  match v.toNat? with
  | some n => .ok n
  | none => .error s!"{flag}: expected a number, got '{v}'"

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "-h" :: _, o | "--help" :: _, o => .ok { o with help := true }
  | "-V" :: _, o | "--version" :: _, o => .ok { o with showVersion := true }
  | "-w" :: rest, o | "--write" :: rest, o => parseArgs rest { o with write := true }
  | "-n" :: rest, o | "--check" :: rest, o => parseArgs rest { o with check := true }
  | "-g" :: v :: rest, o | "--group" :: v :: rest, o =>
    match v with
    | "mapping" => parseArgs rest { o with cfg := { o.cfg with grouping := .mapping } }
    | "run" => parseArgs rest { o with cfg := { o.cfg with grouping := .run } }
    | _ => .error s!"-g/--group: expected 'mapping' or 'run', got '{v}'"
  | "-c" :: v :: rest, o | "--max-cell" :: v :: rest, o => do
    let n ← parseNat "-c/--max-cell" v
    parseArgs rest { o with cfg := { o.cfg with maxCell := n } }
  | "-r" :: v :: rest, o | "--round" :: v :: rest, o => do
    let n ← parseNat "-r/--round" v
    parseArgs rest { o with cfg := { o.cfg with round := n } }
  | "-s" :: v :: rest, o | "--gap" :: v :: rest, o => do
    let n ← parseNat "-s/--gap" v
    if n == 0 then .error "-s/--gap: must be at least 1 (YAML needs a space after ':')"
    parseArgs rest { o with cfg := { o.cfg with minGap := n } }
  | "--" :: rest, o => .ok { o with files := o.files ++ rest.toArray }
  | a :: rest, o =>
    if a.startsWith "-" && a != "-" then .error s!"unknown option '{a}' (try --help)"
    else parseArgs rest { o with files := o.files.push a }

end L4YAML.Align

end Blanket
