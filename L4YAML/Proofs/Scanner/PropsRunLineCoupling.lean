module

public import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Scanner.ScannerLinePreservation
public import L4YAML.Proofs.Scanner.FlowAdjacency
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The depth-0 props-run ↔ scanner coupling substrate (DOCS item 12)

Item 9t parked a scanned-but-unattached `[96] c-ns-properties` run at depth 0 as
`PendingNode.pendingProps`.  Retiring its content-dispatch escape (`&a b`,
`&a !t [b]`) needs the accumulation to FIRE item 9k's same-line property tests
(`propertyRunHasAnchor` / `propertyRunHasTag` / `lastTokenIsNodeProperty`, block
half) against a run it holds as grammar — the depth-0 twin of the in-flow
coupling `InteriorGap.props` carries.

The in-flow coupling reads `trailingPropertyRun` (values only, any distance).
The block half reads `trailingPropertyRunOnLine` — POSITIONED tokens, filtered
by the current line — so the substrate here is the positioned twin of the
`lastRealTokenVal?` family (§1), the OnLine run's push/read lemmas (§2), line
and flag transparency of the anchor/tag scans (§3), and the preprocessing facts
that carry the coupling from the step that parked the run to the step that
consumes it (§4): a run parked with `needIndentCheck = false` is read one
dispatch later either across a break (the flag or the surface `SSLComments`
says so — the pending CLOSES) or on the run's own line with the token readings
and the line untouched (the coupling FIRES). -/

namespace L4YAML.Proofs.PropsRunLineCoupling

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML
open L4YAML.Scanner
open L4YAML.Proofs.FlowAdjacency
open L4YAML.Proofs.ScannerCorrectness

/-! ## §1  The positioned twin of the `lastRealTokenVal?` family

`trailingPropertyRunOnLine` reads `lastRealToken?` / `penultRealToken?` — item
9k's positioned readers — so the stability lemmas the val-level family provides
(`FlowAdjacency`, `StreamAccum` §0c) are needed once more at the positioned
level.  Same proofs, whole tokens. -/

/-- With a real final slot there is no placeholder-skipping to do. -/
lemma lastRealToken_of_real {tokens : Array (Positioned YamlToken)}
    (h : LastTokenReal tokens) :
    lastRealToken? tokens = some tokens[tokens.size - 1]! := by
  obtain ⟨hsz, hne⟩ := h
  unfold lastRealToken?
  simp only [hsz, ↓reduceIte, beq_eq_false_iff_ne.mpr hne, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

/-- A pushed real token is the last real token, position and all. -/
lemma lastRealToken_push {tokens : Array (Positioned YamlToken)}
    {p : Positioned YamlToken} (h : p.val ≠ .placeholder) :
    lastRealToken? (tokens.push p) = some p := by
  have hp : (tokens.push p)[(tokens.push p).size - 1]! = p := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.size_push, Array.getElem_push]
  rw [lastRealToken_of_real (lastTokenReal_push (tokens := tokens) h), hp]

/-- Two reservation placeholders on a real-ended array leave the positioned
    reading alone (the positioned `lastRealTokenVal_push_two_ph_of_real`). -/
lemma lastRealToken_push_two_ph_of_real
    {tokens : Array (Positioned YamlToken)} {ph1 ph2 : Positioned YamlToken}
    (h1 : ph1.val = .placeholder) (h2 : ph2.val = .placeholder)
    (hr : LastTokenReal tokens) :
    lastRealToken? ((tokens.push ph1).push ph2) = lastRealToken? tokens := by
  obtain ⟨hsz, hne⟩ := hr
  rw [lastRealToken_of_real ⟨hsz, hne⟩]
  unfold lastRealToken?
  dsimp only []
  simp only [Array.size_push]
  simp only [show tokens.size + 1 + 1 > 0 from by omega, ↓reduceIte,
    show tokens.size + 1 + 1 - 1 = tokens.size + 1 from by omega]
  have h_elem1 : ((tokens.push ph1).push ph2)[tokens.size + 1]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.getElem_push, Array.size_push, h2]
  simp only [h_elem1, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
    Bool.true_and, show tokens.size + 1 > 0 from by omega,
    show tokens.size + 1 - 1 = tokens.size from by omega]
  have h_elem2 : ((tokens.push ph1).push ph2)[tokens.size]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega)]
    simp [Array.getElem_push, Array.size_push, h1]
  have h_elem3 : ((tokens.push ph1).push ph2)[tokens.size - 1]! =
      tokens[tokens.size - 1]! := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega),
        getElem!_pos _ _ (by omega)]
    simp only [Array.getElem_push,
      show tokens.size - 1 < (tokens.push ph1).size from by simp [Array.size_push]; omega,
      show tokens.size - 1 < tokens.size from by omega, dite_true]
  simp only [h_elem2, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
    Bool.true_and, show tokens.size + 1 > 1 from by omega,
    show tokens.size + 1 - 2 = tokens.size - 1 from by omega, h_elem3]
  simp

/-- The positioned token before a freshly pushed real one is the previous last
    real token. -/
lemma penultRealToken_push {tokens : Array (Positioned YamlToken)}
    {p : Positioned YamlToken} (h : p.val ≠ .placeholder) :
    penultRealToken? (tokens.push p) = lastRealToken? tokens := by
  have hp : (tokens.push p)[tokens.size]! = p := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.getElem_push]
  have hidx : lastRealTokenIdx? (tokens.push p) = some tokens.size := by
    unfold lastRealTokenIdx?
    simp only [Array.size_push, show tokens.size + 1 > 0 from by omega, ↓reduceIte,
      show tokens.size + 1 - 1 = tokens.size from by omega, hp,
      beq_eq_false_iff_ne.mpr h, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  unfold penultRealToken?
  rw [hidx]
  congr 1
  simp

/-- …and the two reservation placeholders leave the positioned penult reading
    alone as well. -/
lemma penultRealToken_push_two_ph_of_real
    {tokens : Array (Positioned YamlToken)} {ph1 ph2 : Positioned YamlToken}
    (h1 : ph1.val = .placeholder) (h2 : ph2.val = .placeholder)
    (hr : LastTokenReal tokens) :
    penultRealToken? ((tokens.push ph1).push ph2) = penultRealToken? tokens := by
  obtain ⟨hsz, hne⟩ := hr
  have h_elem1 : ((tokens.push ph1).push ph2)[tokens.size + 1]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.getElem_push, Array.size_push, h2]
  have h_elem2 : ((tokens.push ph1).push ph2)[tokens.size]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega)]
    simp [Array.getElem_push, Array.size_push, h1]
  have hidx1 : lastRealTokenIdx? ((tokens.push ph1).push ph2) = some (tokens.size - 1) := by
    unfold lastRealTokenIdx?
    simp only [Array.size_push, show tokens.size + 1 + 1 > 0 from by omega, ↓reduceIte,
      show tokens.size + 1 + 1 - 1 = tokens.size + 1 from by omega]
    simp only [h_elem1, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show tokens.size + 1 > 0 from by omega,
      show tokens.size + 1 - 1 = tokens.size from by omega]
    simp only [h_elem2, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show tokens.size + 1 > 1 from by omega,
      show tokens.size + 1 - 2 = tokens.size - 1 from by omega]
    simp
  have hidx2 : lastRealTokenIdx? tokens = some (tokens.size - 1) := by
    unfold lastRealTokenIdx?
    simp only [hsz, ↓reduceIte, beq_eq_false_iff_ne.mpr hne, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
  unfold penultRealToken?
  rw [hidx1, hidx2]
  show lastRealToken? (((tokens.push ph1).push ph2).extract 0 (tokens.size - 1)) =
    lastRealToken? (tokens.extract 0 (tokens.size - 1))
  congr 1
  apply Array.ext
  · simp; omega
  · intro i h1' h2'
    have hi : i < tokens.size := by
      simp only [Array.size_extract] at h2'; omega
    simp only [Array.getElem_extract, Array.getElem_push, Nat.zero_add,
      show i < (tokens.push ph1).size from by simp; omega, hi, ↓reduceDIte]

/-- `saveSimpleKey` leaves the positioned last-real reading alone when the
    array ends real (the positioned `saveSimpleKey_preserves_lastRealTokenVal`). -/
lemma saveSimpleKey_preserves_lastRealToken (s : ScannerState)
    (hr : LastTokenReal s.tokens) :
    lastRealToken? (saveSimpleKey s).tokens = lastRealToken? s.tokens := by
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
      (saveSimpleKey s).tokens = ((s.tokens.push ⟨s.currentPos, .placeholder, s.currentPos⟩).push
        ⟨s.currentPos, .placeholder, s.currentPos⟩) := by
    unfold saveSimpleKey
    split
    · exact .inl rfl
    · split
      · right; dsimp only []
      · exact .inl rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq]
  · rw [h_eq]; exact lastRealToken_push_two_ph_of_real rfl rfl hr

/-- …and the positioned penult reading. -/
lemma saveSimpleKey_preserves_penultRealToken (s : ScannerState)
    (hr : LastTokenReal s.tokens) :
    penultRealToken? (saveSimpleKey s).tokens = penultRealToken? s.tokens := by
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
      (saveSimpleKey s).tokens = ((s.tokens.push ⟨s.currentPos, .placeholder, s.currentPos⟩).push
        ⟨s.currentPos, .placeholder, s.currentPos⟩) := by
    unfold saveSimpleKey
    split
    · exact .inl rfl
    · split
      · right; dsimp only []
      · exact .inl rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq]
  · rw [h_eq]; exact penultRealToken_push_two_ph_of_real rfl rfl hr

/-! ## §2  Reading and growing the same-line run

The four shapes a coupling consumer needs: congruence under preserved readings,
the pushed property as the run's HEAD, the displaced property as its PENULT, and
the extraction of the head back out of a positive `any`. -/

/-- The OnLine run is a function of the two positioned readings alone. -/
lemma trailingPropertyRunOnLine_congr {a b : Array (Positioned YamlToken)} {l : Nat}
    (h1 : lastRealToken? a = lastRealToken? b)
    (h2 : penultRealToken? a = penultRealToken? b) :
    trailingPropertyRunOnLine a l = trailingPropertyRunOnLine b l := by
  unfold trailingPropertyRunOnLine
  rw [h1, h2]

/-- A pushed real property token on line `l` is the HEAD of the new same-line
    run, so a guard testing for its own half fires. -/
lemma trailingPropertyRunOnLine_push_head {tokens : Array (Positioned YamlToken)}
    {p : Positioned YamlToken} {l : Nat} {f : YamlToken → Bool}
    (h : p.val ≠ .placeholder) (hnp : p.val.isNodeProperty = true)
    (hl : p.pos.line = l) (hf : f p.val = true) :
    (trailingPropertyRunOnLine (tokens.push p) l).any f = true := by
  unfold trailingPropertyRunOnLine
  rw [lastRealToken_push h]
  simp only [hnp, hl, beq_self_eq_true, Bool.true_and, ↓reduceIte]
  cases hpen : penultRealToken? (tokens.push p) with
  | none => simp [hf]
  | some t2 =>
    by_cases hn : t2.val.isNodeProperty && t2.pos.line == l
    · simp only [hn]; simp [hf]
    · simp only [hn]; simp [hf]

/-- …and the real property it displaces stays in the same-line run: this is
    where the two-token lookback is load-bearing at depth 0 (`&a !t &b` on one
    line is refused because the run visible at `&b` still carries `&a`). -/
lemma trailingPropertyRunOnLine_push_penult {tokens : Array (Positioned YamlToken)}
    {p t2 : Positioned YamlToken} {l : Nat} {f : YamlToken → Bool}
    (h : p.val ≠ .placeholder) (hnp : p.val.isNodeProperty = true)
    (hl : p.pos.line = l)
    (h2 : lastRealToken? tokens = some t2) (hnp2 : t2.val.isNodeProperty = true)
    (hl2 : t2.pos.line = l) (hf : f t2.val = true) :
    (trailingPropertyRunOnLine (tokens.push p) l).any f = true := by
  unfold trailingPropertyRunOnLine
  rw [lastRealToken_push h, penultRealToken_push h, h2]
  simp only [hnp, hl, hnp2, hl2, beq_self_eq_true, Bool.true_and, ↓reduceIte]
  simp [hf]

/-- The head of the same-line run without a push: a last real token that is a
    property on line `l` puts its own half in the run's `any`.  This is what
    disambiguates the held token's KIND — if the head were the other half, the
    other guard would have fired. -/
lemma trailingPropertyRunOnLine_head {tokens : Array (Positioned YamlToken)}
    {t : Positioned YamlToken} {l : Nat} {f : YamlToken → Bool}
    (h : lastRealToken? tokens = some t) (hnp : t.val.isNodeProperty = true)
    (hl : t.pos.line = l) (hf : f t.val = true) :
    (trailingPropertyRunOnLine tokens l).any f = true := by
  unfold trailingPropertyRunOnLine
  rw [h]
  simp only [hnp, hl, beq_self_eq_true, Bool.true_and, ↓reduceIte]
  cases hpen : penultRealToken? tokens with
  | none => simp [hf]
  | some t2 =>
    by_cases hn : t2.val.isNodeProperty && t2.pos.line == l
    · simp only [hn]; simp [hf]
    · simp only [hn]; simp [hf]

/-- A positive `any` over the same-line run pins the LAST REAL token: it is a
    node property sitting on line `l`.  (The head might not be the token `f`
    found — the run may satisfy `f` at its penult — but the head is a property
    on the line regardless, which is all the alias refutation reads.) -/
lemma runOnLine_any_last {tokens : Array (Positioned YamlToken)} {l : Nat}
    {f : YamlToken → Bool}
    (h : (trailingPropertyRunOnLine tokens l).any f = true) :
    ∃ t, lastRealToken? tokens = some t ∧ t.val.isNodeProperty = true ∧
      t.pos.line = l := by
  unfold trailingPropertyRunOnLine at h
  cases hlast : lastRealToken? tokens with
  | none => rw [hlast] at h; simp at h
  | some t1 =>
    rw [hlast] at h
    by_cases hc : t1.val.isNodeProperty && t1.pos.line == l
    · obtain ⟨hp, hline⟩ := Bool.and_eq_true_iff.mp hc
      exact ⟨t1, rfl, hp, by simpa using hline⟩
    · simp only [hc] at h; simp at h

/-- The same fact read at the `lastTokenIsNodePropertyOnLine` test (the alias
    guard's block half). -/
lemma lastTokenIsNodePropertyOnLine_of_last {tokens : Array (Positioned YamlToken)}
    {t : Positioned YamlToken} {l : Nat}
    (h : lastRealToken? tokens = some t) (hnp : t.val.isNodeProperty = true)
    (hl : t.pos.line = l) :
    lastTokenIsNodePropertyOnLine tokens l = true := by
  unfold lastTokenIsNodePropertyOnLine
  rw [h]
  simp [hnp, hl]

/-! ## §3  Line and flag transparency of the anchor/tag scans

`scanAnchorOrAlias` and `scanTag` advance only on characters their collect
loops admit, and every admitted class excludes `b-char` — so both scans leave
`line` alone, and neither reaches `consumeNewline`, so `needIndentCheck` is
untouched too.  `emitAt` and the trailing record updates are transparent by
definition. -/

lemma emitAt_line_nic (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).line = s.line ∧
      (s.emitAt pos tok).needIndentCheck = s.needIndentCheck :=
  ⟨rfl, rfl⟩

lemma saveSimpleKey_line (s : ScannerState) :
    (saveSimpleKey s).line = s.line := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl

lemma saveSimpleKey_needIndentCheck (s : ScannerState) :
    (saveSimpleKey s).needIndentCheck = s.needIndentCheck := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl

lemma collectAnchorNameLoop_line_nic (s : ScannerState) (name : String) (fuel : Nat) :
    (collectAnchorNameLoop s name fuel).2.line = s.line ∧
    (collectAnchorNameLoop s name fuel).2.needIndentCheck = s.needIndentCheck := by
  induction fuel generalizing s name with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · rename_i c hp
      split
      · rename_i hcond
        have hb : CharPredicates.isLineBreakBool c = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcond
          exact hcond.1.1.2
        have hn : c ≠ '\n' := by intro h; rw [h] at hb; exact absurd hb (by decide)
        have hr : c ≠ '\r' := by intro h; rw [h] at hb; exact absurd hb (by decide)
        obtain ⟨ihl, ihn⟩ := ih s.advance (name.push c)
        exact ⟨by rw [ihl, advance_preserves_line_of_ne_break s c hp hn hr],
               by rw [ihn, advance_preserves_needIndentCheck s]⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

lemma scanAnchorOrAlias_line_nic {s s' : ScannerState} {isAnchor : Bool} {c : Char}
    (hp : s.peek? = some c) (hn : c ≠ '\n') (hr : c ≠ '\r')
    (h : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.line = s.line ∧ s'.needIndentCheck = s.needIndentCheck := by
  unfold scanAnchorOrAlias at h
  dsimp only [] at h
  split at h
  · exact absurd h (by simp)
  · have heq := Except.ok.inj h
    subst heq
    obtain ⟨hl, hnic⟩ := collectAnchorNameLoop_line_nic s.advance "" (s.inputEnd - s.advance.offset)
    exact ⟨hl.trans (advance_preserves_line_of_ne_break s c hp hn hr),
           hnic.trans (advance_preserves_needIndentCheck s)⟩

lemma collectVerbatimTagLoop_line_nic (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).2.2.line = s.line ∧
    (collectVerbatimTagLoop s uri fuel).2.2.needIndentCheck = s.needIndentCheck := by
  induction fuel generalizing s uri with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · rename_i hp
      exact ⟨advance_preserves_line_of_ne_break s '>' hp (by decide) (by decide),
             advance_preserves_needIndentCheck s⟩
    · rename_i c _ hp
      split
      · rename_i hcond
        have hn : c ≠ '\n' := by intro h; rw [h] at hcond; exact absurd hcond (by decide)
        have hr : c ≠ '\r' := by intro h; rw [h] at hcond; exact absurd hcond (by decide)
        obtain ⟨ihl, ihn⟩ := ih s.advance (uri.push c)
        exact ⟨by rw [ihl, advance_preserves_line_of_ne_break s c hp hn hr],
               by rw [ihn, advance_preserves_needIndentCheck s]⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

lemma collectTagSuffixLoop_line_nic (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).2.line = s.line ∧
    (collectTagSuffixLoop s suffix fuel).2.needIndentCheck = s.needIndentCheck := by
  induction fuel generalizing s suffix with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · rename_i c hp
      split
      · rename_i hcond
        have hn : c ≠ '\n' := by intro h; rw [h] at hcond; exact absurd hcond (by decide)
        have hr : c ≠ '\r' := by intro h; rw [h] at hcond; exact absurd hcond (by decide)
        obtain ⟨ihl, ihn⟩ := ih s.advance (suffix.push c)
        exact ⟨by rw [ihl, advance_preserves_line_of_ne_break s c hp hn hr],
               by rw [ihn, advance_preserves_needIndentCheck s]⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

lemma collectTagHandleLoop_line_nic (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).2.2.line = s.line ∧
    (collectTagHandleLoop s chars fuel).2.2.needIndentCheck = s.needIndentCheck := by
  induction fuel generalizing s chars with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · rename_i hp
      exact ⟨advance_preserves_line_of_ne_break s '!' hp (by decide) (by decide),
             advance_preserves_needIndentCheck s⟩
    · rename_i c _ hp
      split
      · rename_i hcond
        have hn : c ≠ '\n' := by intro h; rw [h] at hcond; exact absurd hcond (by decide)
        have hr : c ≠ '\r' := by intro h; rw [h] at hcond; exact absurd hcond (by decide)
        obtain ⟨ihl, ihn⟩ := ih s.advance (chars.push c)
        exact ⟨by rw [ihl, advance_preserves_line_of_ne_break s c hp hn hr],
               by rw [ihn, advance_preserves_needIndentCheck s]⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

lemma scanVerbatimTag_line_nic {s s' : ScannerState} {startPos : YamlPos}
    (hp : s.peek? = some '<')
    (h : scanVerbatimTag s startPos = .ok s') :
    s'.line = s.line ∧ s'.needIndentCheck = s.needIndentCheck := by
  unfold scanVerbatimTag at h
  dsimp only [] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · have heq := Except.ok.inj h
      subst heq
      obtain ⟨hl, hnic⟩ := collectVerbatimTagLoop_line_nic s.advance ""
        (startPos.offset + s.inputEnd - s.advance.offset)
      exact ⟨hl.trans (advance_preserves_line_of_ne_break s '<' hp (by decide) (by decide)),
             hnic.trans (advance_preserves_needIndentCheck s)⟩

lemma scanSecondaryTag_line_nic (s : ScannerState) (startPos : YamlPos)
    (hp : s.peek? = some '!') :
    (scanSecondaryTag s startPos).line = s.line ∧
    (scanSecondaryTag s startPos).needIndentCheck = s.needIndentCheck := by
  unfold scanSecondaryTag
  obtain ⟨hl, hnic⟩ := collectTagSuffixLoop_line_nic s.advance ""
    (startPos.offset + s.inputEnd - s.advance.offset)
  exact ⟨hl.trans (advance_preserves_line_of_ne_break s '!' hp (by decide) (by decide)),
         hnic.trans (advance_preserves_needIndentCheck s)⟩

lemma scanNamedTag_line_nic (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).line = s.line ∧
    (scanNamedTag s startPos inputEnd).needIndentCheck = s.needIndentCheck := by
  unfold scanNamedTag
  dsimp only []
  obtain ⟨hl1, hn1⟩ := collectTagHandleLoop_line_nic s "" (inputEnd - s.offset)
  split
  · rename_i hfound
    obtain ⟨hl2, hn2⟩ := collectTagSuffixLoop_line_nic
      (collectTagHandleLoop s "" (inputEnd - s.offset)).2.2 ""
      (inputEnd - (collectTagHandleLoop s "" (inputEnd - s.offset)).2.2.offset)
    exact ⟨hl2.trans hl1, hn2.trans hn1⟩
  · obtain ⟨hl2, hn2⟩ := collectTagSuffixLoop_line_nic
      (collectTagHandleLoop s "" (inputEnd - s.offset)).2.2
      ("!", (collectTagHandleLoop s "" (inputEnd - s.offset)).fst).snd
      (inputEnd - (collectTagHandleLoop s "" (inputEnd - s.offset)).2.2.offset)
    exact ⟨hl2.trans hl1, hn2.trans hn1⟩

lemma scanTag_line_nic {s s' : ScannerState}
    (hp : s.peek? = some '!')
    (h : scanTag s = .ok s') :
    s'.line = s.line ∧ s'.needIndentCheck = s.needIndentCheck := by
  unfold scanTag at h
  dsimp only [] at h
  have hadv_l : s.advance.line = s.line :=
    advance_preserves_line_of_ne_break s '!' hp (by decide) (by decide)
  have hadv_n : s.advance.needIndentCheck = s.needIndentCheck :=
    advance_preserves_needIndentCheck s
  split at h
  · -- `!<uri>`
    rename_i hp2
    simp only [bind, Except.bind] at h
    generalize hv : scanVerbatimTag s.advance s.currentPos = vres at h
    cases vres with
    | error => simp at h
    | ok s_verb =>
      change Except.ok _ = Except.ok s' at h
      have heq := Except.ok.inj h; subst heq
      obtain ⟨hl, hnic⟩ := scanVerbatimTag_line_nic hp2 hv
      exact ⟨by show s_verb.line = s.line; rw [hl, hadv_l],
             by show s_verb.needIndentCheck = s.needIndentCheck; rw [hnic, hadv_n]⟩
  · -- `!!suffix`
    rename_i hp2
    have heq := Except.ok.inj h; subst heq
    obtain ⟨hl, hnic⟩ := scanSecondaryTag_line_nic s.advance s.currentPos hp2
    exact ⟨hl.trans hadv_l, hnic.trans hadv_n⟩
  · -- `!handle!suffix` / `!suffix`
    have heq := Except.ok.inj h; subst heq
    obtain ⟨hl, hnic⟩ := scanNamedTag_line_nic s.advance s.currentPos s.inputEnd
    exact ⟨hl.trans hadv_l, hnic.trans hadv_n⟩

/-- The `&` arm of the content dispatch leaves `line` and `needIndentCheck`
    alone — an anchor never crosses a break. -/
lemma dispatchContent_anchor_line_nic {s s' : ScannerState}
    (hp : s.peek? = some '&')
    (hok : scanNextToken_dispatchContent s '&' = .ok s') :
    s'.line = s.line ∧ s'.needIndentCheck = s.needIndentCheck := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · split at hok
    · simp at hok
    generalize h_anch : scanAnchorOrAlias s true = anch_result at hok
    cases anch_result with
    | error => simp at hok
    | ok s_anch =>
      change Except.ok _ = Except.ok s' at hok
      have h := Except.ok.inj hok; subst h
      obtain ⟨hl, hnic⟩ := scanAnchorOrAlias_line_nic hp (by decide) (by decide) h_anch
      exact ⟨hl, hnic⟩
  · rename_i h_neq; exact absurd rfl h_neq

/-- The `*` arm's twin (item 61).  An alias cannot cross a break —
    `[104] c-ns-alias-node` is `'*' ns-anchor-name` and `[102] ns-anchor-char`
    excludes `s-white` and `b-char` — so the step that scanned it stayed on its
    line, and `validateAliasClose` writes nothing.  This is the fact that makes
    the alias's arm in the FOLD branch a phantom: that branch is entered only
    when the token crossed a line. -/
lemma dispatchContent_alias_line_nic {s s' : ScannerState}
    (hp : s.peek? = some '*')
    (hok : scanNextToken_dispatchContent s '*' = .ok s') :
    s'.line = s.line ∧ s'.needIndentCheck = s.needIndentCheck := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq; exact absurd h_eq (by decide)
  · split at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · generalize h_al : scanAnchorOrAlias s false = al_result at hok
          cases al_result with
          | error => simp at hok
          | ok s_al =>
            obtain ⟨hl, hnic⟩ := scanAnchorOrAlias_line_nic hp (by decide) (by decide) h_al
            split at hok
            · exact absurd hok (by simp)
            · rename_i v heq
              have hv : v = s_al := (Except.ok.inj heq).symm
              subst hv
              split at hok
              · exact absurd hok (by simp)
              · simp only [Except.ok.injEq] at hok; subst hok
                exact ⟨hl, hnic⟩
    · rename_i h_neq; exact absurd rfl h_neq

/-- The `!` arm's twin. -/
lemma dispatchContent_tag_line_nic {s s' : ScannerState}
    (hp : s.peek? = some '!')
    (hok : scanNextToken_dispatchContent s '!' = .ok s') :
    s'.line = s.line ∧ s'.needIndentCheck = s.needIndentCheck := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · rename_i h_eq; exact absurd h_eq (by decide)
  · split at hok
    · rename_i h_eq; exact absurd h_eq (by decide)
    · split at hok
      · split at hok
        · simp at hok
        generalize h_tag : scanTag s = tag_result at hok
        cases tag_result with
        | error => simp at hok
        | ok s_tag =>
          simp only [Except.ok.injEq] at hok; subst hok
          exact scanTag_line_nic hp h_tag
      · rename_i h_neq; exact absurd rfl h_neq

/-! ## §4  The flag across a full preprocessing pass

A run parked by an anchor/tag dispatch sits at `needIndentCheck = false` (the
preprocessing that preceded the dispatch cleared or never set it, §3 kept it).
That flag is the no-break witness the coupling's consumption needs: if the NEXT
preprocessing crossed no break, its `skipToContentLoop` exit flag is still
`false`, so the armed unwind branch did not run and both the line and the
positioned token readings survive to the dispatch (`saveSimpleKey` adds only
reservation placeholders). -/

/-- A preprocessing pass that yields a content character lands on
    `needIndentCheck = false` outside a flow: the armed branch clears the flag,
    and the plain branch is only taken when it is already clear. -/
lemma preprocess_some_needIndentCheck_false {sc s_prep : ScannerState} {c : Char}
    (h_inflow : sc.inFlow = false)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.needIndentCheck = false := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    have h_inflow_content : s_content.inFlow = false := by
      unfold ScannerState.inFlow
      rw [skipToContent_preserves_flowLevel _ _ h_skip]
      exact h_inflow
    split at hok
    · simp at hok
    · split at hok
      · -- armed branch: the flag is cleared explicitly.
        split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, _⟩ := Prod.mk.inj h; subst h1
            rw [closeStaleExplicitKey_needIndentCheck, saveSimpleKey_needIndentCheck]
      · -- plain branch: the branch condition says the flag is already clear.
        rename_i h_cond
        have h_flag : s_content.needIndentCheck = false := by
          rw [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h_cond
          by_cases hf : s_content.needIndentCheck = false
          · exact hf
          · exact absurd ⟨h_inflow_content, by revert hf; cases s_content.needIndentCheck <;> simp⟩ h_cond
        split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, _⟩ := Prod.mk.inj h; subst h1
            rw [closeStaleExplicitKey_needIndentCheck, saveSimpleKey_needIndentCheck, h_flag]

end L4YAML.Proofs.PropsRunLineCoupling

end Blanket
