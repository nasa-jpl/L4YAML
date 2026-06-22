/-! # Reflection 500 — a *forced second projection* dissolves under a weaker→fuller COERCION

R499 predicted that when a weaker-guard twin's CONSUMER **unifies** a residual the strong consumer
**split**, the producer is FORCED to project its recursive deliverable a SECOND, fuller way. Building the
actual `_seq` descend edge (`flowBodyContent_descend_seq`) REFUTES that for this instance: the unit
projection ALONE serves the unified residual, because the weaker projection (`SafeBodyUnit`) is
**coercible** to the fuller one (`SafeBody`) given a head condition — and that coercion is already wired
into the windowed consumer helper. So the number of *distinct* projections a producer must supply is
reduced by any head/element-conditioned coercion `Weak → Strong` available on the consume side: the
unified residual then routes through `(weak projection) + (coercion)`, not a second projection.

Two conditions make the coercion possible — and they are exactly what R499's minimal-pair demo dropped:

* the WEAK projection must carry the INTERIOR data (not just a boundary). R499's `unitProj := head?`
  carried no interior, so it was genuinely non-coercible — the NON-coercible regime where the forcing
  holds. Here `Weak.tail_true` carries the interior, so the coercion has something to build on;
* a HEAD/element condition (`Weak.head_typed`, modelling `ContentStartTok ≠ .flowEntry`) closes the one
  gap — the head — between Weak and Strong.

Here `Deliv` models `RecSeqBody`; `Weak` models `SafeBodyUnit` (interior + content-typed head); `Strong`
models `SafeBody` (all-true / all-content). `Weak.toStrong` is the `SafeBodyUnit_safeBody` coercion;
`strong_via_coercion` is the dissolution: `Strong` from the WEAK projection, no second projection of `Deliv`.
-/

namespace CoercionDissolvesForcedProjection

/-- The recursive deliverable (models `RecSeqBody`): a nonempty all-`true` list. -/
inductive Deliv : List Bool → Prop
  | single : Deliv [true]
  | cons (rest : List Bool) : Deliv rest → Deliv (true :: rest)

/-- WEAK projection (models `SafeBodyUnit`): the proper TAIL is all-`true` (the INTERIOR data the weak
    form ALREADY carries) and the head is "content-typed" (here: not `false`, the analog of
    `ContentStartTok v → v ≠ .flowEntry`). It states the head more loosely than `Strong` — that one gap
    is what the coercion closes. -/
structure Weak (l : List Bool) : Prop where
  tail_true : ∀ x ∈ l.tail, x = true
  head_typed : ∀ y, l.head? = some y → y ≠ false

/-- FULLER projection (models `SafeBody`): EVERY element is `true`. -/
def Strong (l : List Bool) : Prop := ∀ x ∈ l, x = true

/-- **The COERCION** `Weak → Strong` under the head condition (models `SafeBodyUnit_safeBody` with
    `ContentStartTok_ne_flowEntry`): the tail is all-true by `tail_true`, and the head is true because
    `head_typed` rules out `false`. The interior carried by `Weak` is exactly what lets this go through. -/
theorem Weak.toStrong : {l : List Bool} → Weak l → Strong l
  | [], _ => by intro x hx; simp at hx
  | a :: rest, h => by
      intro x hx
      rcases List.mem_cons.1 hx with heq | htail
      · -- x is the head `a`: `head_typed` gives `a ≠ false`, hence `a = true`.
        have ha : a ≠ false := h.head_typed a rfl
        cases a with
        | false => exact absurd rfl ha
        | true => exact heq
      · -- x is in the tail (`= rest`): `tail_true`, the interior data `Weak` already carries.
        exact h.tail_true x htail

/-- The deliverable projects to the WEAK form (models `RecSeqBody.toSafeBodyUnit`, R494). The tail facts
    come from the IH coerced to `Strong` — faithfully, the weak projection's interior is itself the
    sibling's data, not a fresh `Deliv → Strong`. -/
theorem Deliv.toWeak : {l : List Bool} → Deliv l → Weak l
  | _, .single =>
      ⟨by intro x hx; simp at hx,
       by intro y hy; cases y with | false => simp at hy | true => decide⟩
  | _, .cons rest hrest =>
      ⟨by intro x hx; exact hrest.toWeak.toStrong x hx,
       by intro y hy; cases y with | false => simp at hy | true => decide⟩

/-- **The DISSOLUTION.** The fuller fact R499 thought forced a SECOND projection of `Deliv` is recovered
    from the WEAK projection by the coercion — `Deliv.toWeak` then `Weak.toStrong`, with NO direct
    `Deliv → Strong`. This is `flowBodyContent_descend_seq` (R500): the unit projection (R494) alone serves
    the unified residual; `seqChild_safeBody_seq` (R499) is not on the critical path. -/
theorem strong_via_coercion {l : List Bool} (h : Deliv l) : Strong l :=
  h.toWeak.toStrong

/-- **The head condition is LOAD-BEARING.** Without `head_typed`, the coercion fails: `[false]` has an
    all-`true` (empty) tail — so it satisfies the interior half of `Weak` — yet is NOT `Strong`. So the
    coercion genuinely consumes the head condition; the interior alone does not close the gap. (Contrast
    R499's `unitProj`, which carried NO interior either, modelling the fully non-coercible regime.) -/
theorem head_condition_load_bearing :
    (∀ x ∈ ([false] : List Bool).tail, x = true) ∧ ¬ Strong [false] :=
  ⟨by intro x hx; simp at hx, by intro h; exact absurd (h false (by simp)) (by decide)⟩

end CoercionDissolvesForcedProjection
