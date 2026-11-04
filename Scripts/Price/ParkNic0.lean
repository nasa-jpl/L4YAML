module

public import Scripts.Price.Attribute
meta import Scripts.Price.Attribute

/-!
# Scripts.Price.ParkNic0 — `park_nic0_price.py` (items 206/207): the ARMED-AT-COLUMN-ZERO carrier

A park's name (default `pendingFlow`) or `all` adds `h_nic0_probe : sp_scan.col = 0 →
sc.needIndentCheck = true` to the constructor and counts its producers; `escape` also adds
the premise to `block_dispatch_deferred`; `sites` threads it through every wrapper; `payers`
splits the PAID ring by the term each site spends (no Lean run).
-/

namespace Scripts.Price.ParkNic0

open Scripts.Price.Attribute

public section

def parks : List String :=
  ["pendingContent", "pendingDocEnd", "pendingDocStart", "pendingFlow", "pendingBlockContent"]
def probeLine : String := "  -- NIC0 PROBE (scripts/park_nic0_price.py)"
def field : String := "      (h_nic0_probe : sp_scan.col = 0 → sc.needIndentCheck = true) :"
def escapeAnchor : String := "    (h_nic0 : sp_scan'.col = 0 → s'.needIndentCheck = true) :"
def escapeProbe : String :=
  "    -- NIC0 PROBE (scripts/park_nic0_price.py)\n    (h_nic0_probe : sp_scan'.col = 0 → s'.needIndentCheck = true)\n"
def wrapAnchor : String := "    (h_nic0 : sp_scan'.col = 0 → s'.needIndentCheck = true)"
def wrapProbe : String := "    (h_nic0_probe : sp_scan'.col = 0 → s'.needIndentCheck = true)"
def parkCall : String := "   PendingNode.pendingFlow sp_start sp_X sp_scan' h_stream h_arm h_nodir h_nic0,"
def escapeCall : String := "  block_dispatch_deferred sp_start sp_X sp_scan' s' h_stream h_arm hcorr h_nodir h_nic0"

def modes : List String := parks ++ ["all", "escape", "sites", "payers"]
def usageModes : String := "|".intercalate modes

/-- `apply_probe(lines, which)`.  The `escape` / `sites` splices keep the Python's shape: a
    single element holding embedded newlines, so later indices (and the anchors read off
    them) are the Python's. -/
def applyProbe (lines : Array String) (which : String) : Except String (Array String × Array String) := do
  let spans := constructorSpans lines
  let targets : List String :=
    if which == "all" then parks else if which == "escape" || which == "sites" then ["pendingFlow"] else [which]
  let mut withSpan : Array (String × Nat) := #[]
  for t in targets do
    match spans.find? (·.1 == t) with
    | some (_, s) => withSpan := withSpan.push (t, s)
    | none => throw s!"KeyError: {t}"
  let mut out := lines
  for (_, concl) in bottomUp withSpan do
    out ← spliceSig out (concl - 1) probeLine field
  if which == "escape" then
    let idx := (Array.range out.size).filter fun i => out[i]! == escapeAnchor
    if idx.size != 1 then throw s!"AssertionError: {idx.toList}"
    out := out.set! idx[0]! (escapeProbe ++ escapeAnchor)
  if which == "sites" then
    let mut nSig := 0; let mut nPark := 0; let mut nCall := 0
    for i in [0:out.size] do
      let l := out[i]!
      if l == wrapAnchor ++ " :" then out := out.set! i (wrapAnchor ++ "\n" ++ wrapProbe ++ " :"); nSig := nSig + 1
      else if l == wrapAnchor then out := out.set! i (wrapAnchor ++ "\n" ++ wrapProbe); nSig := nSig + 1
      else if l == parkCall then out := out.set! i (Scripts.Punt.Price.take parkCall (parkCall.length - 1) ++ " h_nic0_probe,"); nPark := nPark + 1
      else if l == escapeCall then out := out.set! i (escapeCall ++ " h_nic0_probe"); nCall := nCall + 1
    if !(nPark == 1 && nCall ≥ 1 && nSig == nCall + 1) then
      throw s!"AssertionError: splice landed on {nSig} signatures, {nPark} park applications and {nCall} escape calls; expected one signature per wrapper plus the escape's own, one call per wrapper, and one park"
  return (out, sortedStrs targets.toArray)

def headline (which : String) (names : Array String) : String :=
  s!"probe: {which} -> {", ".intercalate names.toList}" ++
    (if which == "escape" then " + block_dispatch_deferred premise"
     else if which == "sites" then " + escape and every wrapper threaded" else "")

/-- `(^|[ (⟨])block_dispatch_deferred\w*\b`. -/
def escapeMention (line : String) : Bool := Id.run do
  let parts := line.splitOn "block_dispatch_deferred"
  let mut pos := 0
  for k in [0:parts.length - 1] do
    pos := pos + parts[k]!.length
    let prev := if pos == 0 then none else line.toList[pos - 1]?
    if pos == 0 || prev == some ' ' || prev == some '(' || prev == some '⟨' then return true
    pos := pos + "block_dispatch_deferred".length
  return false

#guard escapeMention "  (block_dispatch_deferred x)"
#guard escapeMention "block_dispatch_deferred x"
#guard !escapeMention "  h_block_dispatch_deferred x"

def anchors (patched : Array String) (which : String) (names : Array String) : Array Anchor := Id.run do
  let mut out : Array Anchor := #[]
  for i in [0:patched.size] do
    let line := patched[i]!
    if which == "sites" then
      if escapeMention line && !(line.splitOn "`").length > 1 &&
          !(line.startsWith "lemma " || line.startsWith "private lemma ") && !isComment line then
        out := out.push (i + 1, "block_dispatch_deferred")
    else
      for n in names do
        if (line.splitOn s!"PendingNode.{n}").length > 1 then out := out.push (i + 1, s!"PendingNode.{n}")
  return out

def report (patched : Array String) (which : String) (names : Array String) (log : String) : Array String := Id.run do
  let census := errorLines log
  let (groups, unanchored) := anchorErrors (anchors patched which names) (sortedNat census)
  let decls := byDecl patched groups unanchored
  let mut out : Array String := #["", s!"raw error sites: {census.size}",
    s!"applications:    {groups.size + unanchored.size}   <- the producer census",
    s!"declarations:    {decls.size}", ""]
  out := out ++ declLines decls
  let casc := cascades groups
  if !casc.isEmpty then
    out := out.push "" |>.push s!"collapsed cascades ({cascadeCount groups} errors were not producers):"
    for ((aline, n), hits) in casc do
      out := out.push s!"  L{aline}  {n}  <- errors at {joinNats hits}"
  if !unanchored.isEmpty then
    out := out.push "" |>.push s!"UNANCHORED ({unanchored.size}): no constructor literal precedes these, so they are counted one-for-one and the total is a CEILING:"
    for raw in unanchored do out := out.push s!"  L{raw}  in {enclosingDecl patched raw}"
  if census.isEmpty then out := out.push "  (none -- the carrier is already discharged everywhere)"
  return out

def landingDecls : List String :=
  ["accum_block_pending", "accum_block_on_noPending", "accum_block_on_closeThenBlock",
   "accum_block_on_pendingContent", "accum_block_on_pendingBlockContent", "accum_block_on_pendingBlock"]

/-- `\(NAME\b`: `(NAME` followed by a non-word character or the end. -/
def parenWord (line needle : String) : Bool := Id.run do
  let parts := line.splitOn s!"({needle}"
  let mut pos := 0
  for k in [0:parts.length - 1] do
    pos := pos + parts[k]!.length + 1 + needle.length
    match line.toList[pos]? with
    | none => return true
    | some c => if !Scripts.Punt.Price.isWordChar c then return true
  return false

#guard parenWord "  exact (content_park_nic_any h)" "content_park_nic_any"
#guard !parenWord "  exact (content_park_nic_any2 h)" "content_park_nic_any"
#guard parenWord "(nic0_of_col_pos" "nic0_of_col_pos"

def payers : List (String × String) :=
  [("content_park_nic_any", "content_park_nic_any"), ("content_park_nic", "content_park_nic hbs"),
   ("nic0_of_col_pos", "nic0_of_col_pos")]

/-- `payers_census()`: the PAID ring split by the term each site spends (item 207). -/
def payersReport (lines : Array String) : Array String := Id.run do
  let mut census : Array (String × Array (Nat × String)) := payers.toArray.map fun (n, _) => (n, #[])
  for i in [0:lines.size] do
    for (name, needle) in payers do
      if parenWord lines[i]! needle then
        census := census.modify (census.findIdx? (·.1 == name)).get! fun (k, hs) => (k, hs.push (i + 1, enclosingDecl lines (i + 1)))
  let total := census.foldl (· + ·.2.size) 0
  let mut out : Array String := #[s!"paid sites: {total}", ""]
  for (name, hits) in census do
    let mut byDecl : Array (String × Nat) := #[]
    for (_, d) in hits do
      byDecl := match byDecl.findIdx? (·.1 == d) with
        | some k => byDecl.modify k fun (d, n) => (d, n + 1)
        | none => byDecl.push (d, 1)
    out := out.push s!"  {Scripts.Punt.Price.padLeft (toString hits.size) 3}  {name}"
    for (d, n) in stableSort byDecl (fun a b => b.2 < a.2 || (a.2 == b.2 && a.1 < b.1)) do
      out := out.push s!"         {Scripts.Punt.Price.padLeft (toString n) 3}  {d}"
  let landing := census.foldl (fun acc (_, hs) => acc + (hs.filter fun (_, d) => landingDecls.contains d).size) 0
  out := out.push "" |>.push s!"ring 2, the park PRODUCERS (total minus the landing's payments and the escape's own site): {(total : Int) - landing - 1}"
  out := out.push s!"the LANDING's own payments (item 210's ring): {landing}"
  return out

private def sample : Array String := #[
  "inductive PendingNode : Prop where",
  "  | pendingFlow (sp_start sp_X sp_scan : SurfPos)",
  "      (h : True) :",
  "      PendingNode sc []",
  "lemma accum_block_on_noPending : True := by",
  "  exact (content_park_nic_any h)",
  "lemma other : True := by",
  "  exact (nic0_of_col_pos h) (PendingNode.pendingFlow a b c)"]

#guard (applyProbe sample "pendingFlow").toOption.map (·.2) == some #["pendingFlow"]
#guard (applyProbe sample "pendingFlow").toOption.map (fun p => p.1[4]!) == some field
#guard (applyProbe sample "escape").toOption == none
#guard anchors sample "pendingFlow" #["pendingFlow"] == #[(8, "PendingNode.pendingFlow")]
#guard payersReport sample == #["paid sites: 2", "", "    1  content_park_nic_any", "           1  accum_block_on_noPending",
  "    0  content_park_nic", "    1  nic0_of_col_pos", "           1  other", "",
  "ring 2, the park PRODUCERS (total minus the landing's payments and the escape's own site): 0",
  "the LANDING's own payments (item 210's ring): 1"]

end

end Scripts.Price.ParkNic0
