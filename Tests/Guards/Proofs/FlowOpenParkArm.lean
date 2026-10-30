module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flow open's park arm (DOCS item 78)

Item 75 threaded the column of the key a depth-0 `[`/`{` STACKS all the way to
the matching close, and left it optional at both ends: the frame offered `kc = k`
only when the park could say whether preprocessing had re-saved, and the close
spent it against a mask that may have been collapsed.

Items 76 and 77 answered the park's half between them — off a line start the
walk's own break re-arms `simpleKeyAllowed`, at one the park carries the flag —
and this item reads the two as ONE datum on the pending
(`PendingNode.arm_or_col`) and spends it at the open.  So `FlowBaseRoutes.key`
carries the equation itself, and what a close still decides per input is the
MASK's promise alone.

§1–§3 are the compile-time witnesses: the datum is uniform over the nine
`false`-indexed constructors, the two route lemmas deliver an EQUATION rather
than an option, and the close's pack has one funder left.  §4 is the
measurement, which is what says the two funders are exhaustive on real input:
at every depth-0 flow open the saved key is FRESH whenever the park was armed,
and INHERITED from the park otherwise. -/

namespace Tests.Guards.FlowOpenParkArm

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.CouplingBridge

/-! ## §1  The datum is uniform over the pendings

The four content parks got their flag-or-column from item 77 and `noPending`
from item 76; the two indicator parks carried `simpleKeyAllowed` outright since
items 34/58 and the props park its column since item 68.  Nine constructors,
one disjunction — so a consumer that only needs THIS need not case on the
pending at all, which is what lets the flow open take the measurement once,
ahead of its own split. -/

example {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}
    (h_noflow : sc.inFlow = false)
    (h : PendingNode sc false sp_start sp_block sp_scan) :
    sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col :=
  h.arm_or_col h_noflow

/-! ## §2  The route lemmas deliver an equation, not an option

Both arms of each lemma now measure.  The ROOT needs no premise beyond the
datum: its landed arm has the walk's re-arm and its no-break arm IS the park at
column 0, where the datum's other disjunct is refuted by arithmetic. -/

-- Item 311: the flow frame's alternative is the gate's (`PackAltG g`); these probes name an ungated frame.
example {sc s_prep : ScannerState} {c : Char} {sp_start sp_scan sp_prep : SurfPos}
    (h_noflow : s_prep.inFlow = false)
    (h_park : sc.simpleKeyAllowed = true ∨ 0 < sp_scan.col)
    -- Item 157: the close carries the park's own face, and both arms of this
    -- route pay it from the very flag this pin is about.
    (h_close : danglingNodePos? sc = none →
      underIndentedFlowValuePos? sc = none →
      ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid)
    (h_dn : scanNextToken_checkDanglingNode sc s_prep = .ok ())
    -- Item 275: §8.1's check rides beside §9.2's the whole way down.
    (h_fv : scanNextToken_checkFlowValueIndent sc s_prep = .ok ())
    (h_corr : ScannerSurfCorr sc sp_scan)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    -- Item 143: §9.2's landing refusal rides beside the two document faces;
    -- this pin is about the park's flag, so the tail punts here too.
    (h_bare : scanNextToken_checkBareDocument s_prep = .ok ())
    -- Item 146: …and so does the stack's base, which is what lets the refusal
    -- read the dedent exemption off the landing's column.
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) 
    (h_alt : PackAlt sc)
    (h_gate : sc.col ≠ 0 → ¬(Proofs.ScannerCoupling.CommentOk sc ∧ sc.peek? = some '#')) :
    (∃ (k : Nat) (sp_key : SurfPos),
      (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
      (∀ sp_end, SFlowContent 0 .flowOut sp_prep sp_end →
        ImplicitKeyHead sp_key sp_end ∨ True) ∧
      s_prep.simpleKey.pos.col = k ∧
      -- Item 196: the value-line pair is a CHAIN, in step with the pack.
      ((∀ nv ∈ L4YAML.Proofs.RegisterWitness.markedCols s_prep,
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
        ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
        ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) ∨ True) ∧
      ((∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < k) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        ResumeFrames (SLYamlStream sp_start) ks sp_e) ∨ True) ∧
      ((∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width < k) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        KeyFrames (ExplValueLine sp_start nv) ks sp_e) ∨ True)) ∨ True :=
  -- Item 136: the head face rides beside the suffix one; this pin is about the
  -- park's flag, so both punt here — and so do item 176's resume face and item
  -- 201's value-line twin beside it.
  flowKeyRoute_of_root (g := none) (m := 0) (Or.inr trivial) h_noflow h_park h_close h_dn h_fv h_corr
    hcorr_prep h_preprocess (GStar.nil _) (fun _ => h_gate) (Or.inr trivial) (Or.inr trivial) h_bare h_base
    (Or.inr trivial) (Or.inr trivial) (Or.inr h_alt)

/-- The ENTRY's version, whose compact arm crosses no break and so spends the
    park's flag directly.  Its route and the width to measure it against travel
    as one option (item 78), because the arm that has the one has the other. -/
example {n : Nat} {sc s_prep : ScannerState} {c : Char}
    {sp_start sp_scan sp_prep : SurfPos}
    (h_node : ∀ sp, SBlockNode n .blockIn sp_scan sp → SLYamlStream sp_start sp)
    (h_compact : ∀ sp, SBlockIndented n .blockIn sp_scan sp → SLYamlStream sp_start sp)
    (h_col : sp_scan.col = n + 1)
    (h_noflow : s_prep.inFlow = false)
    (h_sk : sc.simpleKeyAllowed = true)
    (h_corr : ScannerSurfCorr sc sp_scan)
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c))) 
    (h_alt : PackAlt sc)
    (h_gate : sc.col ≠ 0 → ¬(Proofs.ScannerCoupling.CommentOk sc ∧ sc.peek? = some '#')) :
    (∃ (k : Nat) (sp_key : SurfPos),
      (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
      (∀ sp_end, SFlowContent 0 .flowOut sp_prep sp_end →
        ImplicitKeyHead sp_key sp_end ∨ True) ∧
      s_prep.simpleKey.pos.col = k ∧
      -- Item 196: the value-line pair is a CHAIN, in step with the pack.
      ((∀ nv ∈ L4YAML.Proofs.RegisterWitness.markedCols s_prep,
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
        ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
        ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) ∨ True) ∧
      ((∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < k) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        ResumeFrames (SLYamlStream sp_start) ks sp_e) ∨ True) ∧
      ((∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width < k) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        KeyFrames (ExplValueLine sp_start nv) ks sp_e) ∨ True)) ∨ True :=
  flowKeyRoute_of_open (g := none) (m := 0) h_node (Or.inl ⟨h_compact, h_col⟩) (Or.inr h_alt) h_noflow
    (Or.inl h_sk) h_corr hcorr_prep h_preprocess h_gate

/-! ## §3  …and the close's pack carries its column

The frame's half is an equation (item 78) and the MASK's is one too (item 79),
so the pack's column conjunct is derived at this producer rather than offered.
What is still optional here is the key ROUTE — a fact about the enclosing
construct, not a measurement — and, since item 103, the open's stamp reading,
which is a fact about the input and is what names the punt where the route is
absent. -/

example {sc : ScannerState} {kc : Nat} {sp_start sp_br sp_tok sp_key : SurfPos}
    (route : ∀ sp_v, SBlockMapEntry kc sp_key sp_v → SLYamlStream sp_start sp_v)
    (head : ∀ sp_end, SFlowContent 0 .flowOut sp_br sp_end →
      ImplicitKeyHead sp_key sp_end ∨ True)
    (h_kc : sc.simpleKey.pos.col = kc)
    (h_park : StalePark sc)
    (h_content : SFlowContent 0 .flowOut sp_br sp_tok) :
    sc.simpleKey.possible = true → sc.simpleKey.pos.line = sc.line →
      ImplicitKeyPack sc sp_start sp_tok ∨ KeyPackPunt sc :=
  flowKeyPack_of_close (g := none) (Or.inl ⟨kc, sp_key, route, head, rfl, Or.inr trivial,
      Or.inr trivial, Or.inr trivial⟩)
    -- Item 300: the base slot's third reading, the marker's line, declined here.
    ⟨h_kc, Or.inr trivial, Or.inr trivial⟩ h_park h_content

/-! ## §4  The two funders, measured at every depth-0 open

`openSaveOk` is the pair the open spends, checked on the scanner itself: an
ARMED park gets a fresh save (the key sits at the cursor preprocessing stopped
on), and every open's key is that fresh one or the park's own.  The predicate
is what would fail if a park reached a bracket carrying neither. -/

private def openStepOk (s sp : ScannerState) (c : Char) : Bool :=
  if (c == '[' || c == '{') && s.flowLevel == 0 then
    -- an armed park FRESHENS the save…
    (!s.simpleKeyAllowed || sp.simpleKey.pos.col == sp.col) &&
    -- …and every open's key is that one or the park's own
    (sp.simpleKey.pos.col == sp.col || sp.simpleKey.pos.col == s.simpleKey.pos.col)
  else true

private def openSaveOkLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => true
    | .ok none => true
    | .ok (some (sp, c)) =>
      openStepOk s sp c &&
        (match scanNextToken s with
         | .error _ => true
         | .ok none => true
         | .ok (some s') => openSaveOkLoop s' fuel')

private def openSaveOk (input : String) : Bool :=
  openSaveOkLoop ((ScannerState.mk' input).emit .streamStart) (input.utf8ByteSize + 1)

/-- …and the same walk reporting whether a depth-0 open was REACHED at all, so
    the check above is not vacuous on the shape it is there to measure. -/
private def openSeenLoop (s : ScannerState) (fuel : Nat) (inherited : Bool) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match scanNextToken_preprocess s with
    | .error _ => false
    | .ok none => false
    | .ok (some (sp, c)) =>
      ((c == '[' || c == '{') && s.flowLevel == 0 &&
        (!inherited || sp.simpleKey.pos.col != sp.col)) ||
        (match scanNextToken s with
         | .error _ => false
         | .ok none => false
         | .ok (some s') => openSeenLoop s' fuel' inherited)

private def openSeen (input : String) : Bool :=
  openSeenLoop ((ScannerState.mk' input).emit .streamStart) (input.utf8ByteSize + 1) false

/-- A depth-0 open whose key is NOT the fresh one — the props park, which leaves
    the flag down and so hands the frame the column the property saved. -/
private def openInherited (input : String) : Bool :=
  openSeenLoop ((ScannerState.mk' input).emit .streamStart) (input.utf8ByteSize + 1) true

-- The five parks that reach a depth-0 open with a key route to offer.
#guard openSaveOk "[1]: b\n" && openSeen "[1]: b\n"
#guard openSaveOk "- [1]: b\n" && openSeen "- [1]: b\n"
#guard openSaveOk "k:\n  [1]: b\n" && openSeen "k:\n  [1]: b\n"
#guard openSaveOk "&a [1]: b\n" && openSeen "&a [1]: b\n"
#guard openSaveOk "? [1]\n: v\n" && openSeen "? [1]\n: v\n"
-- …the landings, where the walk's own break is the funder…
#guard openSaveOk "# c\n[1]: b\n" && openSeen "# c\n[1]: b\n"
#guard openSaveOk "...\n[1]: b\n" && openSeen "...\n[1]: b\n"
#guard openSaveOk "&a\n[1]: b\n" && openSeen "&a\n[1]: b\n"
-- …and the value openings, which offer no key at all.
#guard openSaveOk "[1]\n" && openSaveOk "{a: b}\n"
#guard openSaveOk "- [1]\n" && openSaveOk "k: {a: b}\n"
#guard openSaveOk "&a [1]\n"

-- The INHERIT half is load-bearing: the props park really does reach a bracket
-- with the flag down, and the fresh half really does not cover it.
#guard openInherited "&a [1]: b\n"
#guard openInherited "- &p [1]: b\n"
#guard !openInherited "[1]: b\n"
#guard !openInherited "- [1]: b\n"

/-! ## §5  The readings the open's key route is FOR, held fixed -/

private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

private def refused (input : String) : Bool := bothEvents input == (none, none)

#guard emits "[1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "- [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
#guard emits "k:\n  [1]: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "&a [1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ [] &a", "=VAL :1", "-SEQ", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "- &p [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ [] &p", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "? [1]\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "# c\n[1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- The two shapes whose arms hand `Or.inr trivial` for the SCANNER's reason
-- rather than the pending's: a nested mapping on the line, and content on the
-- document-start line.
#guard refused "k: [1]: b\n"
#guard refused "--- [1]: b\n"

end Tests.Guards.FlowOpenParkArm

end Blanket
