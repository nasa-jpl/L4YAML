/-!
# Reflection 456 — strengthening a predicate whose INTERMEDIATE existential SEVERED a fact set is a
# verbatim MIRROR-TRANSPORT from the sibling arm that did NOT sever: the proof content pre-exists in
# the mirror, so the cost is re-exposing the dropped binders + the same wrap lemmas, not new
# derivation.  The wrapped output fact splits into a BOUNDARY half (free off the deliverable's
# projection, R455) and an INTERIOR half (re-threaded from the scan).

Self-contained (core Lean, no `L4YAML` import) toy of the R456 finding, made executing STEP D step 2a
of the `mapRec` programme: strengthen the KEY predicate `EmitScansInFlowSavedKeyRecEntry` to carry
the body adjacency facts (`OpenerAdj`/`SepAdj`/tail) the assembler needs, having found (R455) that the
interior facts cannot be derived from the deliverable and must stay scan-threaded.

The setup.  One producer (`emit_scans_in_flow_rec_entry_both`) establishes BOTH a value-side predicate
(`EmitScansInFlowRecEntry`, the `.1`) and a saved-key-side predicate (`EmitScansInFlowSavedKeyRecEntry`,
the `.2`) for the SAME `emit v`.  The seq case routes its body through an intermediate existential
(`∃ bodyBlock, … ∧ RecSeqBody-builder ∧ …`).  The VALUE arm's intermediate already threads the five
body facts (`OpenerAdj`/head/tail/`SepAdj`/lns); the SAVED-KEY arm's intermediate had SEVERED them
(dropped the recseqbody `OpenerAdj`∧`SepAdj` into a `_`-binder, omitted head/tail/lns).

The finding R456 proves.  Strengthening the saved-key arm was NOT new proof work:

1.  **Mirror-transport.**  The value arm `.1` is the verbatim template — its intermediate-existential
    shape, its sub-case discharges, and its wrap-lemma calls transport line-for-line to the saved-key
    arm `.2`.  The proof content already EXISTS in the sibling; strengthening the dropper = copy it.
2.  **Re-thread, don't re-derive, the INTERIOR half.**  `OpenerAdj`/`SepAdj` of the body are NOT
    projections of `RecSeqBody` (R455 — the flat-`map` severance makes `WellBracketed ⇏ OpenerAdj`).
    The recseqbody producer ALREADY proves them (it carries them in its output); the saved-key arm had
    merely DROPPED them.  Re-threading = un-drop the binder (`_h_body_oa` → `h_body_oa, h_body_sa`),
    not re-run the scan.
3.  **Derive the BOUNDARY half off the deliverable (R455).**  The head/tail/lns inputs to the wrap
    lemma come FREE from `RecSeqBody.openerAdjHead`/`.lastNonOpener`/`.lastNonSep` — boundary
    projections off the recursive witness the intermediate already carries.

So the wrapped output fact = boundary (deliverable projection) + interior (re-threaded scan fact),
and the whole strengthening is a mechanical mirror of the sibling.

This toy mirrors that exactly:

* `Body`               — the recursive body deliverable (mirror `RecSeqBody`).
* `Body.last_not_op`   — a BOUNDARY projection, derivable OFF the deliverable (mirror
                         `RecSeqBody.lastNonOpener`).
* `Interior`           — the INTERIOR fact NOT derivable from `Body` (mirror `OpenerAdj`); scan-supplied.
* `Wrapped` / `wrapped_of_body` — the wrapped output fact = boundary (off the deliverable) + interior
                         (threaded), the wrap lemma both arms call.
* `ValPred` / `KeyPred` / `KeyPredStrong` — the value arm carries both facts; the saved-key arm DROPS
                         `Interior`; the strengthened saved-key re-threads it.
* `producer_strengthened` — strengthening the dropper is the value arm's term VERBATIM (the same
                         `hi`).

Sharpens `[[ref-recursive-producer-mirrors-flat-over-shared-induction]]` (the mirror is value↔saved-key
here, not flat↔recursive) and composes `[[ref-severed-constructor-boundary-projects-interior-doesnt]]`
(boundary derived off the deliverable, interior re-threaded).

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.StrengthenSeveredPredicateMirrorsSibling

/-- Toy alphabet: `a` content, `op`/`cl` the wrap brackets. -/
inductive Tok where
  | a | op | cl
deriving DecidableEq

/-- The recursive body deliverable (mirror `RecSeqBody`): one or more `a`s. -/
inductive Body : List Tok → Prop where
  | single : Body [Tok.a]
  | cons (rest : List Tok) (h : Body rest) : Body (Tok.a :: rest)

/-- **BOUNDARY projection — derivable OFF the deliverable** (mirror `RecSeqBody.lastNonOpener`).  The
    last token is an `a`, never the opener `op`; read off the recursive structure's tail.  This is the
    half the wrap lemma gets FREE, no threading. -/
theorem Body.last_not_op : {l : List Tok} → Body l → ∃ t, l.getLast? = some t ∧ t ≠ Tok.op
  | _, .single => ⟨Tok.a, rfl, by decide⟩
  | _, .cons rest h => by
      obtain ⟨t, hgl, ht⟩ := h.last_not_op
      have hne : rest ≠ [] := by cases h <;> simp
      refine ⟨t, ?_, ht⟩
      rw [List.getLast?_cons_of_ne_nil hne, hgl]

/-- **INTERIOR fact — NOT a projection of `Body`** (mirror `OpenerAdj`): supplied by the scan, must be
    threaded.  (Trivial here; the point is its PROVENANCE — it cannot come off `Body`, per R455.) -/
def Interior (_ : List Tok) : Prop := True

/-- The WRAPPED output fact, assembled from the body's BOUNDARY (off the deliverable) and INTERIOR
    (threaded) — the wrap lemma BOTH arms call (mirror `OpenerAdj_wrap_seq`, whose tail input is the
    boundary projection and whose `OpenerAdj` input is the threaded interior fact). -/
def Wrapped (l : List Tok) : Prop := (∃ t, l.getLast? = some t ∧ t ≠ Tok.op) ∧ Interior l

/-- The wrap lemma: boundary derived off the deliverable `hb`, interior threaded as `hi`. -/
theorem wrapped_of_body {l : List Tok} (hb : Body l) (hi : Interior l) : Wrapped l :=
  ⟨hb.last_not_op, hi⟩

/-! ### The two paired predicates one producer establishes. -/

/-- Value arm (`.1`) — carries BOTH the deliverable and the threaded interior fact. -/
def ValPred (l : List Tok) : Prop := Body l ∧ Interior l
/-- Saved-key arm (`.2`) ORIGINAL — carries only the deliverable; DROPS `Interior`. -/
def KeyPred (l : List Tok) : Prop := Body l
/-- Saved-key arm STRENGTHENED — re-threads `Interior` (so the assembler can read it). -/
def KeyPredStrong (l : List Tok) : Prop := Body l ∧ Interior l

/-- The producer establishes a body witness carrying BOTH facts.  The value arm threads `Interior`;
    the saved-key arm originally DROPS it (the `_hi` discard is the severance). -/
theorem producer {l : List Tok} (hb : Body l) (hi : Interior l) : ValPred l ∧ KeyPred l :=
  ⟨⟨hb, hi⟩, hb⟩   -- saved-key arm: `hi` dropped

/-! ### The finding — strengthening the dropper is the sibling's term VERBATIM. -/

/-- **Strengthening the saved-key arm is a mirror-transport, not new proof.**  `KeyPredStrong`'s new
    `Interior` field is discharged by the SAME `hi` the value arm's `ValPred` already threads — the
    producer establishes it for both, so re-exposing it costs zero new derivation.  (In the real code:
    re-thread recseqbody's dropped `OpenerAdj`∧`SepAdj`, and pull head/tail/lns off
    `RecSeqBody.openerAdjHead`/`.lastNonOpener`/`.lastNonSep`.) -/
theorem producer_strengthened {l : List Tok} (hb : Body l) (hi : Interior l) :
    ValPred l ∧ KeyPredStrong l :=
  ⟨⟨hb, hi⟩, ⟨hb, hi⟩⟩   -- saved-key arm now MIRRORS the value arm exactly

/-! ### The law, packaged. -/

/-- **The finding in one proposition.**  (i) The wrapped output fact assembles from the deliverable's
    BOUNDARY projection (`Body.last_not_op`, free) plus the threaded INTERIOR fact; and (ii)
    strengthening the saved-key arm to re-thread `Interior` is dischargeable by the SAME witnesses the
    value arm already carries (the sibling is the verbatim template).  Sharpens
    `[[ref-recursive-producer-mirrors-flat-over-shared-induction]]` and composes
    `[[ref-severed-constructor-boundary-projects-interior-doesnt]]`. -/
theorem strengthen_severed_mirrors_sibling :
    (∀ l, Body l → Interior l → Wrapped l)                                   -- boundary + interior
    ∧ (∀ l, Body l → Interior l → ValPred l ∧ KeyPredStrong l) :=            -- strengthening = mirror
  ⟨fun _ hb hi => wrapped_of_body hb hi, fun _ hb hi => producer_strengthened hb hi⟩

end Tests.Reflections.StrengthenSeveredPredicateMirrorsSibling
