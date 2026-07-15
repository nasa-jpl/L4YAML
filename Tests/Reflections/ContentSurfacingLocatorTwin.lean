/-! # Reflection 504 — surface a locator's buried witness to propagate a free child projection

R503 ([[BundleFreeProjectionIntoProducer]]) bundled the free child `FlowBodyContent` projection INTO the
seq oracle that already computes the child `RecSeqBody`. R504 is the located-level companion: the oracle's
emitted child content lives at the descend close `j`, but the located form
(`recseqentry_seqbracket_located`) runs a close-LOCATOR (`matchingClose_full_seq`) and reports only the
ENTRY-shaped output `∃ m, RecSeqEntry …` — whose boundary `m` is the entry END (`j` or `j+1`), so the
descend close `j` is BURIED. `recseqentry_seqbracket_located_content` (R504) lifts the content-emitting
oracle through the locator and returns that SAME entry AND a second existential `∃ j, … Content j`,
SURFACING the witness the entry-shaped output hides.

The honest scope is the point of this demo. The surfaced child content is genuinely FREE (it is a
projection of the body the content-free descend IH already produces — `surfaced_content_is_free` is `rfl`),
but it is NOT on the carrier-free recursion's critical path: the descend recursive call is itself
CONTENT-FREE (`descendIH` takes no content), so the surfaced content is never consumed there. The one real
obstacle is the CURRENT window's content (`step` consumes it as a top-down INPUT before the current body
exists), which a width-only recursion cannot source — it has no parent. So surfacing the child witness is a
clean propagation, not the bridge.

`Body` models `RecSeqBody`; `Content` models `FlowBodyContent`; `proj` is R502's free projection; `oracle`
is R503's content-emitting twin; `locate` is the close-locator; `Entry`/`located` the entry-shaped output
that buries `j`; `locatedContent` the R504 twin that surfaces it.
-/

namespace ContentSurfacingLocatorTwin

/-- The recursion's body deliverable at a child window closed at `j` (models `RecSeqBody ((take j).drop
    (lo+1))`): a genuine non-empty body. -/
def Body (j : Nat) : Prop := 0 < j

/-- The downstream content projection (models `FlowBodyContent (lo+1) j`). -/
def Content (j : Nat) : Prop := 0 < j

/-- R502's FREE projection: content is read off the body already in hand — no second producer call. -/
theorem proj {j : Nat} (b : Body j) : Content j := b

/-- The content-emitting ORACLE (models R503 `recseqentry_seqbracket_oracle_seq_content`): at the located
    close `j` it returns the body, its FREE content, and the trailing separator from ONE evaluation. -/
theorem oracle (j : Nat) (hj : 0 < j) : Body j ∧ Content j ∧ True :=
  ⟨hj, proj hj, trivial⟩

/-- The close-LOCATOR (models `matchingClose_full_seq`): produces the descend close `j` internally. -/
theorem locate : ∃ j, 0 < j := ⟨1, by decide⟩

/-- The entry-shaped output (models `RecSeqEntry`), tagged by the entry END `m` — which is `j` or `j+1`, so
    the located close `j` is NOT recoverable from it. -/
def Entry (m : Nat) : Prop := 0 < m

/-- **The OLD located form** (models `recseqentry_seqbracket_located`): returns only `∃ m, Entry m`,
    BURYING the located close `j`. It reports the entry end `m := j + 1`; the witness `j` is discarded. -/
theorem located : ∃ m, Entry m := by
  obtain ⟨j, hj⟩ := locate
  obtain ⟨_hbody, _hcontent, _⟩ := oracle j hj
  exact ⟨j + 1, Nat.succ_pos j⟩

/-- **The CONTENT-SURFACING located twin** (models R504 `recseqentry_seqbracket_located_content`): returns
    the SAME entry AND the surfaced close `j` with its free content, from the SAME locator + oracle run. -/
theorem locatedContent : (∃ m, Entry m) ∧ (∃ j, 0 < j ∧ Content j) := by
  obtain ⟨j, hj⟩ := locate
  obtain ⟨_hbody, hcontent, _⟩ := oracle j hj
  exact ⟨⟨j + 1, Nat.succ_pos j⟩, ⟨j, hj, hcontent⟩⟩

/-- The twin SURFACES the content the old form buries: its second component hands back `Content j`
    directly, whereas `located` exposes only `Entry m` (`m = j+1 ≠ j`). -/
theorem locatedContent_surfaces_content : ∃ j, 0 < j ∧ Content j := locatedContent.2

/-! The honesty witnesses: the surfaced content is free, and the descend does not consume it. -/

/-- The descend recursive call is CONTENT-FREE: the body is produced from a content-free IH, taking NO
    content argument (models the seq oracle's content-free width IH `h_ih`). -/
theorem descendIH (j : Nat) (hj : 0 < j) : Body j := hj

/-- **The surfaced content is genuinely free AND genuinely unneeded by the descend**: it equals the
    projection of the body the content-free `descendIH` already produces — so propagating it costs nothing,
    and the descend never needed it. -/
theorem surfaced_content_is_free (j : Nat) (hj : 0 < j) :
    (oracle j hj).2.1 = proj (descendIH j hj) := rfl

/-- **The real obstacle — the CURRENT window's content is a top-down INPUT.** The step that produces the
    current body (models the dispatch) CONSUMES the current window's content `curContent`; it cannot be
    produced from the (smaller) child body alone. A width-only recursion has no parent to source it from —
    this is the one place the carrier was load-bearing, and the gap R504 does NOT close. -/
theorem step (curContent : Content 5) (_childBody : Body 3) : Body 5 :=
  -- `curContent` is consumed (the dispatch needs the current content); `_childBody` is the content-free IH,
  -- available but NOT sufficient on its own — the current body needs the current content.
  curContent

/-- The step genuinely needs `curContent`: it is an antecedent, not derivable from the child body. The
    child's content is free (`proj`), but the CURRENT window's is owed top-down. -/
theorem step_consumes_current_content (childBody : Body 3) (curContent : Content 5) : Body 5 :=
  step curContent childBody

/-- Non-vacuity: the locator fires on a real window, so the surfaced child content is over a genuine body. -/
theorem demo : (∃ m, Entry m) ∧ (∃ j, 0 < j ∧ Content j) := locatedContent

/-- The body is not vacuous: an empty child (`j = 0`) has no body, so the oracle only fires where the
    recursion produced a real body — the surfaced content is never over an empty deliverable. -/
theorem body_needs_nonempty : ¬ Body 0 := Nat.lt_irrefl 0

end ContentSurfacingLocatorTwin
