module

public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Leaf evidence at a nonzero reading index (DOCS item 45)

Item 44 gave the flow stack an index; this file pins the LEAF evidence item
45 built for threading it — the landing split at a given `n`
(`gstar_white_take_sIndent` / `preprocess_some_separate_at_anyCol`) and the
three scalar lifts (`SCDoubleQuoted_at` / `SCSingleQuoted_at` /
`SNsPlain_at`).

§1 pins the splitter on CONCRETE runs — two spaces split at 2, under-run at
3, and a tab at column 1 under-runs 2 with the tab as the located witness.
§2 pins the lifts' types from abstract hypotheses and inhabits a nonzero-index
single-line reading concretely (`"a"` at index 2, context `.flowOut` — the
shape `  a: "a"`'s value slot wants).  §3 pins the separator lemma's shape.
-/

namespace L4YAML.Tests.Guards.FlowIndexLeafEvidence

open L4YAML L4YAML.Surface L4YAML.Scanner L4YAML.Proofs.CouplingBridge L4YAML.Proofs.FlowIndexLift L4YAML.Proofs.StreamAccum

/-! ## §1  The landing split, concretely -/

/-- The two-space run `"  x"` as a white run. -/
private theorem run2 : GStar SSWhite ⟨[' ', ' ', 'x'], 0⟩ ⟨['x'], 2⟩ :=
  GStar.cons _ _ _ (SSWhite.space _ 0)
    (GStar.cons _ _ _ (SSWhite.space _ 1) (GStar.nil _))

/-- Two spaces supply `s-indent(2)` with an empty residue. -/
example : ∃ sx, SIndent 2 (⟨[' ', ' ', 'x'], 0⟩ : SurfPos) sx ∧
    GStar SSWhite sx ⟨['x'], 2⟩ :=
  ⟨⟨['x'], 2⟩, SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero _)),
   GStar.nil _⟩

/-- ... and the splitter finds that or an under-run — the application pin. -/
example : (∃ sx, SIndent 2 (⟨[' ', ' ', 'x'], 0⟩ : SurfPos) sx ∧
      GStar SSWhite sx ⟨['x'], 2⟩) ∨
    WhiteRunUnderRun 2 ⟨[' ', ' ', 'x'], 0⟩ ⟨['x'], 2⟩ :=
  gstar_white_take_sIndent 2 run2

/-- Two spaces UNDER-RUN 3: one short, with the run's end as the witness. -/
example : WhiteRunUnderRun 3 (⟨[' ', ' ', 'x'], 0⟩ : SurfPos) ⟨['x'], 2⟩ :=
  ⟨2, ⟨['x'], 2⟩,
   by omega,
   SIndent.succ 1 _ 0 _ (SIndent.succ 0 _ 1 _ (SIndent.zero _)),
   GStar.nil _, Or.inl rfl⟩

/-- A tab at column 1 under-runs 2, and the WITNESS is the tab's own
    position — `[63] s-indent` is spaces only. -/
example : WhiteRunUnderRun 2 (⟨[' ', '\t', 'x'], 0⟩ : SurfPos) ⟨['x'], 2⟩ :=
  ⟨1, ⟨['\t', 'x'], 1⟩,
   by omega,
   SIndent.succ 0 _ 0 _ (SIndent.zero _),
   GStar.cons _ _ _ (SSWhite.tab _ 1) (GStar.nil _),
   Or.inr rfl⟩

/-! ## §2  The scalar lifts -/

/-- The lift's application shape: `.blockIn` evidence at 0 serves a
    `.flowOut` slot at 2, or names the crossing. -/
example {s s' : SurfPos} (h : SCDoubleQuoted 0 .blockIn s s') :
    SCDoubleQuoted 2 .flowOut s s' ∨ DoubleQuotedCrossed s :=
  SCDoubleQuoted_at 2 .flowOut h

example {s s' : SurfPos} (h : SCSingleQuoted 0 .blockIn s s') :
    SCSingleQuoted 2 .flowOut s s' ∨ SingleQuotedCrossed s :=
  SCSingleQuoted_at 2 .flowOut h

/-- The plain lift keeps its context (`[127] ns-plain-safe(c)`). -/
example {s s' : SurfPos} (h : SNsPlain 0 .flowIn s s') :
    SNsPlain 2 .flowIn s s' ∨ PlainCrossed s :=
  SNsPlain_at 2 h

/-- A single-line `"a"` read at index 2, context `.flowOut`, CONCRETELY — the
    reading an entry at index 2 needs from its quoted value, which no
    derivation could state before item 44. -/
example : SCDoubleQuoted 2 .flowOut ⟨['"', 'a', '"'], 4⟩ ⟨[], 7⟩ :=
  SCDoubleQuoted.mk 2 .flowOut _ _ _ _ (GLit.mk _ 4)
    (SNbDoubleMultiLine.single 2 _ _
      (GStar.cons _ _ _
        (SNbDoubleChar.plain 'a' _ 5 (by decide) (by decide) (by decide))
        (GStar.nil _)))
    (GLit.mk _ 6)

/-! ## §3  The separator at a given index -/

/-- The landing read's shape: `s-separate-lines(n)` from preprocessing, or the
    LOCATED under-run on the landing line — which item 66 hands on with §6.1's
    own gate beside it, so the caller can refuse the run's tab half where the
    caller knows a break was crossed. -/
example (n : Nat) (sc : ScannerState) (sp : SurfPos) (s_prep : ScannerState)
    (c : Char) (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_gate : sc.col ≠ 0 → ¬(Proofs.ScannerCoupling.CommentOk sc ∧ sc.peek? = some '#')) :
    ∃ sp_prep, ScannerSurfCorr s_prep sp_prep ∧
      ((SSeparateLines n sp sp_prep ∨ (sp_prep = sp ∧ sp = sp ∧ 0 < sp.col)) ∨
        ∃ sp_mid, SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
          WhiteRunUnderRun n sp_mid sp_prep ∧
          Proofs.LandingTab.LandingTabFacts sc.currentIndent sc.needIndentCheck s_prep.peek? sp sp_mid) :=
  preprocess_some_separate_at_anyCol n sc sp s_prep c hcorr hok (GStar.nil _) (fun _ => h_gate)

end L4YAML.Tests.Guards.FlowIndexLeafEvidence

end Blanket
