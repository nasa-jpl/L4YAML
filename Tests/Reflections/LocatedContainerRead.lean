/-! # Reflection 506 — a navigator LOCATES a container that STORES the deliverable; the read is free

R505 ([[ParametricCarrierExtraction]]) reduced the carrier-free `RecSeqBody` recursion to ONE
obligation: a per-window content PROVIDER `∀ lo hi, <guards> → FlowBodyContent tokens lo hi`. The
fixpoint-free way to discharge it is the NAVIGATOR — navigate the root `RecSeqBody` (known off
emission) down to each window and READ its content off the body it already holds, never PRODUCING the
body from content (which would need content for its own dispatch — the same-window self-cycle R505's
`guard_does_not_entail_content` exhibits).

R506 (`flowBodyContent_of_located_seq_entry`) is the navigator's terminal READ, and it pins the
navigator's deliverable. The emission-spine-walk navigator (R350–R359, slice-keyed LEAF/DESCEND/ADVANCE
arms, awaiting only the recursion wrapper) does not PRODUCE a window body — it LOCATES the enclosing seq
ENTRY, which STORES the interior `RecSeqBody` in its `seq.h_rec` field. So the window's content is a
FREE projection off the located entry: `recseqentry_seq_extract` reads the stored body out, a slice
re-base (R353) re-aligns it to the window, and R502 `flowBodyContent_of_recseqbody_seq` projects it to
content — three landed lemmas, NO carrier.

**The transferable rule.** When a bottom-up width recursion cannot thread a top-down fact (R504), do
not PRODUCE the carrier's deliverable bottom-up — NAVIGATE a structure already known top-down to the
container that STORES it, and READ the deliverable (and its downstream projections) out of the located
container as free reads. The navigator's job collapses to LOCATION; everything downstream of the stored
witness is a projection. So "navigator produces window bodies" becomes "navigator locates window
entries + a fixed read."

This demo models the located container (`LocatedEntry`, storing the interior body), the read
(`extract`), the projection to content (`proj`, consuming the body AND the content-free deep guard, as
R502 does), and the carrier-free bridge (`content_of_located`). The CONTRAST `guard_cannot_produce`
shows the same-window cycle: content is NOT producible from a content-free guard alone — only from a
LOCATED body — which is exactly why the provider must NAVIGATE, not produce.
-/

namespace LocatedContainerRead

/-- The depth-`0` separator-successor fact the content-free guard cannot see (models
    `FlowBodyContent.bodySucc` / the `n ≠ 7` of [[ParametricCarrierExtraction]]). -/
def BodySucc (n : Nat) : Prop := n ≠ 7

/-- The content-free deep guard the provider supplies for free (models `FlowBodyContentDeepSeq`):
    opener/separator fields with a descend-stable form, but NOT the `BodySucc` successor fact. -/
def Deep (_n : Nat) : Prop := True

/-- The window body (models `RecSeqBody ((take hi).drop lo)`): it CARRIES the successor fact, so its
    content projects back off it for free. -/
def Body (n : Nat) : Prop := BodySucc n

/-- The per-window content the recursion consumes (models `FlowBodyContent tokens lo hi`). -/
def Content (n : Nat) : Prop := BodySucc n

/-- **A LOCATED seq entry** — the emission-spine-walk navigator's output (models `RecSeqEntry.seq` at
    the enclosing window). The navigator does not PRODUCE a body; it LOCATES this container, which
    STORES the interior body witness in its `stored` field (the `seq.h_rec` of the real entry). -/
structure LocatedEntry (n : Nat) : Prop where
  /-- the stored interior `RecSeqBody` — what `recseqentry_seq_extract` reads off the located entry. -/
  stored : Body n

/-- **extract** (models `recseqentry_seq_extract`): the located entry STORES the body — read it
    straight off, no production. (In the real bridge a slice re-base `nestedSeq_recseqentry_locate_descend`
    re-aligns the stored interior to the window `[lo, hi)`; the abstract model stores it at the window.) -/
theorem extract {n : Nat} (e : LocatedEntry n) : Body n := e.stored

/-- **proj** (models R502 `flowBodyContent_of_recseqbody_seq`): the body PROJECTS to its content, given
    the content-free deep guard — the body carries `BodySucc`, the deep guard carries the rest. -/
theorem proj {n : Nat} (b : Body n) (_d : Deep n) : Content n := b

/-- **The R506 bridge** — located entry ⟹ content, carrier-free: `proj (extract e) d`. The navigator's
    only job was to LOCATE `e`; the body and its content fall out as free reads off the stored witness. -/
theorem content_of_located {n : Nat} (e : LocatedEntry n) (d : Deep n) : Content n :=
  proj (extract e) d

/-! The CONTRAST that makes the navigator necessary — content is NOT producible from a content-free
    guard, only from a LOCATED body (the same-window cycle of R505). -/

/-- The content-free window guard (models `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed`). -/
def Guard (n : Nat) : Prop := 0 < n

/-- The guard does NOT entail the content (R505's `guard_does_not_entail_content`): `Guard 7` holds
    (`0 < 7`) yet `Content 7` fails (`BodySucc 7 = 7 ≠ 7` is `False`). So a PRODUCER keyed on the guard
    alone is stuck — the same-window cycle — and only a LOCATED body, which already carries the
    successor fact, dissolves it. That located body is exactly what the navigator supplies. -/
theorem guard_cannot_produce : Guard 7 ∧ ¬ Content 7 :=
  ⟨by unfold Guard; decide, by unfold Content BodySucc; decide⟩

/-- The deep guard is genuinely free at every window (it never carries `BodySucc`) — so it is NOT what
    is missing; the stored body is. -/
theorem deep_is_free (n : Nat) : Deep n := trivial

/-- Non-vacuity: a located entry never sits at the degenerate point — its stored body forces
    `BodySucc`, so the bad window `n = 7` cannot be located. -/
theorem located_excludes_bad : ¬ LocatedEntry 7 := fun e => e.stored rfl

/-- The demo deliverable: a located entry yields content for FREE (the navigator-read), while the
    guard-only producer is blocked — so the carrier-free provider must NAVIGATE (locate + read), not
    produce. -/
theorem demo : (∀ n, LocatedEntry n → Deep n → Content n) ∧ (Guard 7 ∧ ¬ Content 7) :=
  ⟨fun _ e d => content_of_located e d, guard_cannot_produce⟩

end LocatedContainerRead
