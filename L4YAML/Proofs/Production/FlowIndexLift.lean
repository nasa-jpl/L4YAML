/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Surface.Node

@[expose] public section Blanket

/-! # Reading-index lifts for scalar tokens and landing runs (DOCS item 45)

The flow stack carries a reading index `n` (item 44), and the accumulation's
evidence producers all conclude at 0.  This satellite is the leaf evidence
that lets item 46 thread a NONZERO index without reworking the deep scan-loop
inductions:

* **The landing split** (`gstar_white_take_sIndent`): the whites a
  break-crossing lands on either open with `[63] s-indent(n)` — `n` spaces,
  the rest `[66] s-separate-in-line` — or they under-run, and the under-run is
  LOCATED (`WhiteRunUnderRun`): `j < n` spaces followed by the run's end or a
  tab.  This is `gstar_white_sIndent_or_tab`'s question asked at a GIVEN `n`
  instead of an existential one, and it is the whole content of
  `[69] s-flow-line-prefix(n)` on a landing line.

* **The scalar lifts** (`SCDoubleQuoted_at` / `SCSingleQuoted_at` /
  `SNsPlain_at`): a scalar token's reading at 0 is a reading at EVERY `n`
  unless the derivation crossed a line — the single-line constructors bind
  their index without constraining it, so the lift is the same derivation
  re-tagged, and the multi-line case is returned as a located witness
  (`*Crossed`: the first line's own content, then the break) rather than
  generalized.  Lift the derivation, not the induction (Reflection 671): the
  scan-loop `_prod` chains stay at 0 untouched.

  The quoted lifts convert the CONTEXT freely (`[110]`/`[121]` read the same
  body classes in every context, so `.blockIn` evidence serves a `.flowOut`
  slot); the plain lift keeps its context — `[127] ns-plain-safe(c)` makes a
  plain scalar's characters context-sensitive, so only the index moves.

What stays at 0 after this file: multi-line scalar tokens (the `*Crossed`
witnesses) — item 46 collapses those at a nonzero index, and a later item can
narrow further by re-deriving their readings at `n` from the scanner's
per-line checks.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.FlowIndexLift

open L4YAML.Surface

/-! ## §1 The landing split at a given index -/

/-- The located under-run: the run opens with `j < n` spaces and then either
    ends or hits a tab — the two ways a landing line fails to supply
    `[63] s-indent(n)`. -/
def WhiteRunUnderRun (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ j sx, j < n ∧ SIndent j s sx ∧ GStar SSWhite sx s' ∧
    (sx = s' ∨ sx.chars.head? = some '\t')

/-- **The DEDENT, located** (item 64).  The step crossed a break, and the
    landing's `[63] s-indent` run ENDS at a width strictly below the pending's
    index — `j` spaces and then the content, with no tab, because §6.1 refuses
    a tab there (`LandingTab.NoLandingTabAt`).  This is the half of
    `WhiteRunUnderRun` that survives the runtime: the enclosing entry has
    ended and a sibling opens at an outer level, which is a FRAME question and
    not a missing separator — there is no `[70] s-separate-lines(n)` to derive
    here at any price, because the landing never reaches `n`. -/
def DedentLanding (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ sp_mid j, SSLComments s sp_mid ∧ sp_mid.col = 0 ∧ j < n ∧ SIndent j sp_mid s'

/-- Split a white run at a GIVEN `n`: `s-indent(n)` plus residual whites, or
    the located under-run. -/
lemma gstar_white_take_sIndent (n : Nat) {s s' : SurfPos}
    (h : GStar SSWhite s s') :
    (∃ sx, SIndent n s sx ∧ GStar SSWhite sx s') ∨ WhiteRunUnderRun n s s' := by
  induction n generalizing s with
  | zero => exact Or.inl ⟨s, SIndent.zero s, h⟩
  | succ n ih =>
    cases h with
    | nil => exact Or.inr ⟨0, _, by omega, SIndent.zero _, GStar.nil _, Or.inl rfl⟩
    | cons _ s₂ s₃ hw hrest =>
      cases hw with
      | space rest col =>
        rcases ih hrest with ⟨sx, hind, hws⟩ | ⟨j, sx, hj, hind, hws, hend⟩
        · exact Or.inl ⟨sx, SIndent.succ n rest col sx hind, hws⟩
        · exact Or.inr ⟨j + 1, sx, by omega, SIndent.succ j rest col sx hind, hws, hend⟩
      | tab rest col =>
        exact Or.inr ⟨0, ⟨'\t' :: rest, col⟩, by omega, SIndent.zero _,
          GStar.cons _ _ _ (SSWhite.tab rest col) hrest, Or.inr rfl⟩

/-- The clean split, packaged as the line prefix `[69]` wants. -/
lemma gstar_white_flowLinePrefix_or_underRun (n : Nat) {s s' : SurfPos}
    (h : GStar SSWhite s s') :
    SFlowLinePrefix n s s' ∨ WhiteRunUnderRun n s s' := by
  rcases gstar_white_take_sIndent n h with ⟨sx, hind, hws⟩ | hur
  · refine Or.inl (SFlowLinePrefix.mk n s sx s' hind ?_)
    match hws with
    | GStar.nil _ => exact GOpt.none _
    | GStar.cons a b c hfirst hrest =>
      exact GOpt.some a c (SSeparateInLine.whites a c (GPlus.mk a b c hfirst hrest))
  · exact Or.inr hur

/-! ## §2 The scalar lifts -/

/-- A double-quoted body crossed a line: the first line's content, then
    `[113] s-double-break` (flow fold or escaped break). -/
def DoubleQuotedCrossed (s : SurfPos) : Prop :=
  ∃ s₁ sa sb, GLit '"' s s₁ ∧ SNbDoubleOneLine s₁ sa ∧ SSDoubleBreak 0 sa sb

/-- A single-quoted body crossed a line. -/
def SingleQuotedCrossed (s : SurfPos) : Prop :=
  ∃ s₁ sa sb, GLit '\'' s s₁ ∧ SNbSingleOneLine s₁ sa ∧ SBBreak sa sb

/-- A plain scalar crossed a line: its first line, then
    `[134] s-ns-plain-next-line`. -/
def PlainCrossed (s : SurfPos) : Prop :=
  ∃ (c : L4YAML.YamlContext) (sa sb : SurfPos),
    SNsPlainOneLine c s sa ∧ SSNsPlainNextLine 0 c sa sb

/-- One-line double-quoted body text reads at every index and context. -/
private lemma doubleText_of_oneLine (n : Nat) (c : L4YAML.YamlContext)
    {s₁ s₂ : SurfPos} (h : SNbDoubleOneLine s₁ s₂) : SNbDoubleText n c s₁ s₂ := by
  cases c <;> first
    | exact h
    | exact SNbDoubleMultiLine.single n s₁ s₂ h

/-- Read a multi-line double-quoted body back to one line, or the crossing. -/
private lemma doubleMulti_cases {s₁ s₂ : SurfPos}
    (h : SNbDoubleMultiLine 0 s₁ s₂) :
    SNbDoubleOneLine s₁ s₂ ∨
      ∃ sa sb, SNbDoubleOneLine s₁ sa ∧ SSDoubleBreak 0 sa sb := by
  cases h with
  | single _ _ hl => exact Or.inl hl
  | multi _ _ _ _ _ hl hb _ => exact Or.inr ⟨_, _, hl, hb⟩

/-- Read a double-quoted body back to one line, or the crossing. -/
private lemma doubleText_cases {c : L4YAML.YamlContext} {s₁ s₂ : SurfPos}
    (h : SNbDoubleText 0 c s₁ s₂) :
    SNbDoubleOneLine s₁ s₂ ∨
      ∃ sa sb, SNbDoubleOneLine s₁ sa ∧ SSDoubleBreak 0 sa sb := by
  cases c <;> first
    | exact Or.inl h
    | exact doubleMulti_cases h

/-- **The double-quoted lift**: a reading at 0 in any context is a reading at
    every `n` in every context, unless the body crossed a line. -/
lemma SCDoubleQuoted_at (n : Nat) (c' : L4YAML.YamlContext)
    {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SCDoubleQuoted 0 c s s') :
    SCDoubleQuoted n c' s s' ∨ DoubleQuotedCrossed s := by
  cases h with
  | mk _ _ _ hq1 hbody hq2 =>
    rcases doubleText_cases hbody with hone | ⟨sa, sb, hl, hb⟩
    · exact Or.inl (SCDoubleQuoted.mk n c' _ _ _ _ hq1
        (doubleText_of_oneLine n c' hone) hq2)
    · exact Or.inr ⟨_, sa, sb, hq1, hl, hb⟩

/-- One-line single-quoted body text reads at every index and context. -/
private lemma singleText_of_oneLine (n : Nat) (c : L4YAML.YamlContext)
    {s₁ s₂ : SurfPos} (h : SNbSingleOneLine s₁ s₂) : SNbSingleText n c s₁ s₂ := by
  cases c <;> first
    | exact h
    | exact SNbSingleMultiLine.single n s₁ s₂ h

/-- Read a multi-line single-quoted body back to one line, or the crossing. -/
private lemma singleMulti_cases {s₁ s₂ : SurfPos}
    (h : SNbSingleMultiLine 0 s₁ s₂) :
    SNbSingleOneLine s₁ s₂ ∨
      ∃ sa sb, SNbSingleOneLine s₁ sa ∧ SBBreak sa sb := by
  cases h with
  | single _ _ hl => exact Or.inl hl
  | multi _ _ _ _ _ _ hl hb _ _ _ => exact Or.inr ⟨_, _, hl, hb⟩

/-- Read a single-quoted body back to one line, or the crossing. -/
private lemma singleText_cases {c : L4YAML.YamlContext} {s₁ s₂ : SurfPos}
    (h : SNbSingleText 0 c s₁ s₂) :
    SNbSingleOneLine s₁ s₂ ∨
      ∃ sa sb, SNbSingleOneLine s₁ sa ∧ SBBreak sa sb := by
  cases c <;> first
    | exact Or.inl h
    | exact singleMulti_cases h

/-- **The single-quoted lift** (see `SCDoubleQuoted_at`). -/
lemma SCSingleQuoted_at (n : Nat) (c' : L4YAML.YamlContext)
    {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SCSingleQuoted 0 c s s') :
    SCSingleQuoted n c' s s' ∨ SingleQuotedCrossed s := by
  cases h with
  | mk _ _ _ hq1 hbody hq2 =>
    rcases singleText_cases hbody with hone | ⟨sa, sb, hl, hb⟩
    · exact Or.inl (SCSingleQuoted.mk n c' _ _ _ _ hq1
        (singleText_of_oneLine n c' hone) hq2)
    · exact Or.inr ⟨_, sa, sb, hq1, hl, hb⟩

/-- The multi-line half of the plain lift. -/
private lemma plainMulti_at (n : Nat) {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SNsPlainMultiLine 0 c s s') :
    SNsPlainMultiLine n c s s' ∨ PlainCrossed s := by
  cases h with
  | mk _ _ hone hnext =>
    cases hnext with
    | nil => exact Or.inl (SNsPlainMultiLine.mk n _ _ _ _ hone (GStar.nil _))
    | cons _ _ _ hn _ => exact Or.inr ⟨_, _, _, hone, hn⟩

/-- **The plain lift**: same context — `[127] ns-plain-safe(c)` makes the
    characters context-sensitive, so only the index moves. -/
lemma SNsPlain_at (n : Nat) {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SNsPlain 0 c s s') :
    SNsPlain n c s s' ∨ PlainCrossed s := by
  cases c <;> first
    | exact Or.inl h
    | exact plainMulti_at n h

/-! ## §3  Composite lifts -/

/-- `[66] s-separate-in-line` as a white run (the `startOfLine` alternative is
    zero-width). -/
lemma sSeparateInLine_to_gstar {s s' : SurfPos} (h : SSeparateInLine s s') :
    GStar SSWhite s s' :=
  match h with
  | .whites _ _ (.mk _ _ _ h1 h2) => GStar.cons _ _ _ h1 h2
  | .startOfLine _ => GStar.nil _

/-- **The separator lift**: a `[70] s-separate-lines(0)` re-reads at `n`
    unless it took the commented form and its landing under-runs
    `s-indent(n)`. -/
lemma SSeparateLines_at (n : Nat) {s s' : SurfPos} (h : SSeparateLines 0 s s') :
    SSeparateLines n s s' ∨
      ∃ s₁, SSLComments s s₁ ∧ WhiteRunUnderRun n s₁ s' := by
  cases h with
  | inline _ h_il => exact Or.inl (SSeparateLines.inline n _ _ h_il)
  | commented s₁ _ h_ssl h_flp =>
    cases h_flp with
    | mk _ sx h_ind h_opt =>
      cases h_ind
      have h_run : GStar SSWhite s₁ s' := by
        cases h_opt with
        | none => exact GStar.nil _
        | some _ h_il => exact sSeparateInLine_to_gstar h_il
      rcases gstar_white_flowLinePrefix_or_underRun n h_run with h_flp_n | h_ur
      · exact Or.inl (SSeparateLines.commented n _ _ _ h_ssl h_flp_n)
      · exact Or.inr ⟨s₁, h_ssl, h_ur⟩

/-- What a 0-content can leave behind under the lift: a scalar that crossed a
    line, or a nested flow collection (whose reading at `n` is the stack's to
    build stepwise, never a single token's). -/
inductive FlowContent0Residue (s : SurfPos) : Prop where
  | dq (h : DoubleQuotedCrossed s) : FlowContent0Residue s
  | sq (h : SingleQuotedCrossed s) : FlowContent0Residue s
  | plain (h : PlainCrossed s) : FlowContent0Residue s
  | collection : FlowContent0Residue s

/-- **The content lift**: `[158] ns-flow-content` at 0 re-reads at `n` for
    single-line scalar tokens; the residue is located per constructor. -/
lemma SFlowContent_at (n : Nat) {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowContent 0 c s s') :
    SFlowContent n c s s' ∨ FlowContent0Residue s := by
  cases h with
  | plain _ _ _ _ hp =>
    rcases SNsPlain_at n hp with h_n | h_x
    · exact Or.inl (.plain n _ _ _ h_n)
    · exact Or.inr (.plain h_x)
  | flowSeq => exact Or.inr .collection
  | flowMap => exact Or.inr .collection
  | singleQ _ _ _ _ hq =>
    rcases SCSingleQuoted_at n c hq with h_n | h_x
    · exact Or.inl (.singleQ n _ _ _ h_n)
    · exact Or.inr (.sq h_x)
  | doubleQ _ _ _ _ hq =>
    rcases SCDoubleQuoted_at n c hq with h_n | h_x
    · exact Or.inl (.doubleQ n _ _ _ h_n)
    · exact Or.inr (.dq h_x)

/-- The under-run a lifted separator can leave behind, at any position. -/
def SeparatorUnderRun (n : Nat) : Prop :=
  ∃ p q r, SSLComments p q ∧ WhiteRunUnderRun n q r

/-- `[69] s-separate(n,c)` lifted: key contexts mention no index; the other
    four are `SSeparateLines_at`. -/
lemma SSeparate_at (n : Nat) (c : L4YAML.YamlContext) {s s' : SurfPos}
    (h : SSeparate 0 c s s') :
    SSeparate n c s s' ∨ SeparatorUnderRun n := by
  cases c <;>
    first
      | exact Or.inl h
      | (rcases SSeparateLines_at n h with h' | ⟨s₁, hssl, hur⟩
         · exact Or.inl h'
         · exact Or.inr ⟨s, s₁, s', hssl, hur⟩)

/-- `[96] c-ns-properties` lifted: the index occurs only in the optional
    second half's separator. -/
lemma SCNsProperties_at (n : Nat) {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SCNsProperties 0 c s s') :
    SCNsProperties n c s s' ∨ SeparatorUnderRun n := by
  cases h with
  | tagFirst _ _ hT hopt =>
    cases hopt with
    | none => exact Or.inl (.tagFirst _ _ _ _ _ hT (.none _))
    | some _ hseq =>
      cases hseq with
      | mk _ _ hsep hA =>
        rcases SSeparate_at n c hsep with hsep' | hx
        · exact Or.inl (.tagFirst _ _ _ _ _ hT (.some _ _ (.mk _ _ _ hsep' hA)))
        · exact Or.inr hx
  | anchorFirst _ _ hA hopt =>
    cases hopt with
    | none => exact Or.inl (.anchorFirst _ _ _ _ _ hA (.none _))
    | some _ hseq =>
      cases hseq with
      | mk _ _ hsep hT =>
        rcases SSeparate_at n c hsep with hsep' | hx
        · exact Or.inl (.anchorFirst _ _ _ _ _ hA (.some _ _ (.mk _ _ _ hsep' hT)))
        · exact Or.inr hx

/-- What a 0-node can leave behind under the lift; the content residue's
    position is the crossing's own (mid-node for a properties-bearing form). -/
inductive FlowNode0Residue (s : SurfPos) : Prop where
  | content {s₀ : SurfPos} (h : FlowContent0Residue s₀) : FlowNode0Residue s
  | separator (n : Nat) (h : SeparatorUnderRun n) : FlowNode0Residue s

/-- `[161] ns-flow-node` lifted: aliases mention no index; the other three
    constructors lift their pieces. -/
lemma SFlowNode_at (n : Nat) {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowNode 0 c s s') :
    SFlowNode n c s s' ∨ FlowNode0Residue s := by
  cases h
  case alias =>
    rename_i hA
    exact Or.inl (.alias n _ _ _ hA)
  case content =>
    rename_i hc
    rcases SFlowContent_at n hc with h' | hx
    · exact Or.inl (.content n _ _ _ h')
    · exact Or.inr (.content hx)
  case propsContent =>
    rename_i hsep hp hc
    rcases SCNsProperties_at n hp with hp' | hx
    · rcases SSeparate_at n c hsep with hsep' | hx
      · rcases SFlowContent_at n hc with hc' | hx
        · exact Or.inl (.propsContent n _ _ _ _ _ hp' hsep' hc')
        · exact Or.inr (.content hx)
      · exact Or.inr (.separator n hx)
    · exact Or.inr (.separator n hx)
  case propsEmpty =>
    rename_i hp
    rcases SCNsProperties_at n hp with hp' | hx
    · exact Or.inl (.propsEmpty n _ _ _ hp')
    · exact Or.inr (.separator n hx)

end L4YAML.Proofs.FlowIndexLift

end Blanket
