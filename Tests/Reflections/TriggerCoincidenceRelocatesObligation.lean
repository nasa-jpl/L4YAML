/-!
# Reflection 421 — trigger-coincidence RELOCATES the obligation (and restricts the tail-bridge domain)

Self-contained (core Lean, no `L4YAML` import) toy model of the `SepAdj` wrap/seam/tail layer (R421),
the token-CONCRETE layer ABOVE the `SepAdj` combinator layer (R420,
`AdjacencyMirrorCornerIsLayerScoped`).

R420 (`ref-adjacency-mirror-corner-is-layer-scoped`) established that when mirroring a gated-adjacency
producer stack to a sibling (trigger, gate), the list-COMBINATOR layer clones VERBATIM (token-opaque)
but the token-CONCRETE wrap/seam/glue layer does NOT.  R420 said WHERE the work is.  THIS reflection is
what the work IS: the single content-start OBLIGATION is CONSERVED but RELOCATES to whichever emitted
structural token coincides with the NEW trigger; the sibling's obligated seat goes VACUOUS.

* `adj` / `adj_singleton` / `adj_cons` / `adj_append`  — the token-opaque combinator layer (R420),
  parametric over `(trig, gate)` (the verbatim-cloning floor below).
* `adj_wrap_headed`                                    — a headed wrap `op :: (body ++ [cl])` whose
                                                          head `op` MAY coincide with the trigger.
* `adj_seam`                                           — a seam glue `a ++ [feTok] ++ rest` whose seam
                                                          `feTok` MAY coincide with the trigger.
* `adjA_wrapHeaded_obligated` / `adjA_seam_vacuous`    — POSITIVE, at trigger = OPENER: the obligation
                                                          sits on the WRAP HEAD; the seam is vacuous.
* `adjB_wrapHeaded_vacuous` / `adjB_seam_obligated`    — POSITIVE, at trigger = SEAM: the obligation
                                                          RELOCATED to the SEAM; the wrap head is
                                                          vacuous.  Same two parametric lemmas, the
                                                          obligation swapped head↔seam.
* `seamTrailing_last_is_trigger` / `_not_ne_trigger`   — NEGATIVE: the 'last ≠ trigger' tail bridge
                                                          over `a ++ [feTok] ++ rest` is UNSOUND at
                                                          `rest = []` when `feTok = trigger` (the last
                                                          token IS the trigger seam).
* `seamNonTrailing_last_ne_trigger`                    — the SOUND form needs `rest ≠ []`: the
                                                          tail bridge's domain excises the
                                                          trigger-coinciding seat.

Refines `AdjacencyMirrorCornerIsLayerScoped` (R420 localises the non-free layer; this gives the SHAPE
of the non-free work — relocate one conserved obligation + restrict the tail bridge, not re-derive
from scratch).
-/

namespace Tests.Reflections.TriggerCoincidenceRelocatesObligation

set_option autoImplicit false

/-- Toy token kinds: seq opener `opn` / closer `cls`, separator `sep`, content scalar `scal`,
    explicit key indicator `key`.  Two adjacency pairs live here: (`opn`, `cls`) — the trigger
    coincides with the block OPENER — and (`sep`, `key`) — the trigger coincides with the SEAM. -/
inductive Tok where
  | opn | cls | sep | scal | key
  deriving DecidableEq, BEq

/-- A content start: a scalar or an opener (toy of `isFlowContentStart`). -/
def isContent : Tok → Bool
  | .scal | .opn => true
  | _ => false

/-! ## The TOKEN-OPAQUE combinator layer (R420) — the verbatim-cloning floor, parametric. -/

/-- A gated adjacency field, PARAMETRIC over the trigger and gate (toy of `OpenerAdj`/`SepAdj`). -/
def adj (trig gate : Tok) (l : List Tok) : Prop :=
  ∀ (k : Nat) (h : k + 1 < l.length),
    (l[k]'(by omega)) = trig →
    (l[k+1]'h) ≠ gate →
    isContent (l[k+1]'h) = true

theorem adj_singleton (trig gate : Tok) (t : Tok) : adj trig gate [t] := by
  intro k h; simp at h

theorem adj_cons (trig gate : Tok) (t : Tok) (rest : List Tok)
    (h_rest : adj trig gate rest)
    (h_head : t = trig →
       ∀ (h0 : 0 < rest.length), (rest[0]'h0) ≠ gate → isContent (rest[0]'h0) = true) :
    adj trig gate (t :: rest) := by
  intro k hk htrig hne
  match k with
  | 0 =>
    have hr0 : 0 < rest.length := by simp [List.length_cons] at hk; omega
    rw [List.getElem_cons_zero] at htrig
    rw [List.getElem_cons_succ] at hne ⊢
    exact h_head htrig hr0 hne
  | k'+1 =>
    have hrk : k' + 1 < rest.length := by simp [List.length_cons] at hk; omega
    rw [List.getElem_cons_succ] at htrig
    rw [List.getElem_cons_succ] at hne ⊢
    exact h_rest k' hrk htrig hne

theorem adj_append (trig gate : Tok) (a b : List Tok)
    (ha : adj trig gate a) (hb : adj trig gate b)
    (h_tail : ∀ (hla : 0 < a.length),
       (a[a.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ trig) :
    adj trig gate (a ++ b) := by
  intro k hk htrig hne
  have hlen : (a ++ b).length = a.length + b.length := by rw [List.length_append]
  rcases Nat.lt_or_ge (k + 1) a.length with hk1 | hge1
  · have e_k : (a ++ b)[k]'(by omega) = a[k]'(by omega) := List.getElem_append_left (by omega)
    have e_k1 : (a ++ b)[k+1]'hk = a[k+1]'hk1 := List.getElem_append_left hk1
    rw [e_k1]; rw [e_k] at htrig; rw [e_k1] at hne
    exact ha k hk1 htrig hne
  · rcases Nat.lt_or_ge k a.length with hka | hkb
    · exfalso
      have hka' : k = a.length - 1 := by omega
      have e_k : (a ++ b)[k]'(by omega) = a[k]'hka := List.getElem_append_left hka
      rw [e_k] at htrig
      simp only [hka'] at htrig
      exact h_tail (by omega) htrig
    · obtain ⟨m, hm⟩ : ∃ m, k = a.length + m := ⟨k - a.length, by omega⟩
      subst hm
      have hmb1 : m + 1 < b.length := by rw [hlen] at hk; omega
      have e_k : (a ++ b)[a.length + m]'(by omega) = b[m]'(by omega) := by
        rw [List.getElem_append_right (by omega)]; congr 1; omega
      have e_k1 : (a ++ b)[a.length + m + 1]'hk = b[m+1]'hmb1 := by
        rw [List.getElem_append_right (by omega)]; congr 1; omega
      rw [e_k1]; rw [e_k] at htrig; rw [e_k1] at hne
      exact hb m hmb1 htrig hne

/-! ## The TOKEN-CONCRETE wrap/seam layer — where the obligation can RELOCATE. -/

/-- A headed wrap `op :: (body ++ [cl])` (toy of `OpenerAdj_wrap_seq`/`SepAdj_wrap_seq`).  The head
    obligation is GATED on `op = trig`: it is load-bearing exactly when the block opener `op`
    coincides with the trigger, vacuous otherwise. -/
theorem adj_wrap_headed (trig gate : Tok) (op cl : Tok) (body : List Tok)
    (h_body : adj trig gate body)
    (h_head : op = trig →
       ∀ (h0 : 0 < (body ++ [cl]).length), ((body ++ [cl])[0]'h0) ≠ gate →
         isContent ((body ++ [cl])[0]'h0) = true)
    (h_tail : ∀ (hla : 0 < body.length),
       (body[body.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ trig) :
    adj trig gate (op :: (body ++ [cl])) :=
  adj_cons trig gate op (body ++ [cl])
    (adj_append trig gate body [cl] h_body (adj_singleton trig gate cl) h_tail)
    h_head

/-- A seam glue `a ++ [feTok] ++ rest` (toy of `OpenerAdj_seam`/`SepAdj_seam`).  The seam obligation
    is GATED on `feTok = trig`: it is load-bearing exactly when the seam token coincides with the
    trigger, vacuous otherwise. -/
theorem adj_seam (trig gate : Tok) (a rest : List Tok) (feTok : Tok)
    (ha : adj trig gate a) (h_rest : adj trig gate rest)
    (h_head_rest : feTok = trig →
       ∀ (h0 : 0 < rest.length), (rest[0]'h0) ≠ gate → isContent (rest[0]'h0) = true)
    (h_tail_a : ∀ (hla : 0 < a.length),
       (a[a.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ trig) :
    adj trig gate (a ++ [feTok] ++ rest) := by
  have h_cons : adj trig gate (feTok :: rest) :=
    adj_cons trig gate feTok rest h_rest h_head_rest
  rw [List.append_assoc]
  exact adj_append trig gate a (feTok :: rest) ha h_cons h_tail_a

/-! ## POSITIVE — the obligation RELOCATES head↔seam as the trigger moves.

Both blocks below have a `.opn`-headed wrap and a `.sep`-seamed glue.  Only WHICH lemma's head
obligation is load-bearing changes — governed by which emitted token coincides with the trigger. -/

/-- `adjA`: trigger `.opn` coincides with the block OPENER. -/
abbrev adjA (l : List Tok) : Prop := adj Tok.opn Tok.cls l
/-- `adjB`: trigger `.sep` coincides with the SEAM. -/
abbrev adjB (l : List Tok) : Prop := adj Tok.sep Tok.key l

/-- At the OPENER trigger: the headed wrap's head obligation is LOAD-BEARING (`op = .opn` IS the
    trigger), so a real `h_head` content-start obligation must be supplied. -/
theorem adjA_wrapHeaded_obligated (cl : Tok) (body : List Tok)
    (h_body : adjA body)
    (h_head : ∀ (h0 : 0 < (body ++ [cl]).length), ((body ++ [cl])[0]'h0) ≠ Tok.cls →
        isContent ((body ++ [cl])[0]'h0) = true)
    (h_tail : ∀ (hla : 0 < body.length),
       (body[body.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ Tok.opn) :
    adjA (Tok.opn :: (body ++ [cl])) :=
  adj_wrap_headed Tok.opn Tok.cls Tok.opn cl body h_body (fun _ => h_head) h_tail

/-- At the OPENER trigger: the SEAM glue's head obligation is VACUOUS (the `.sep` seam ≠ `.opn`
    trigger), so NO content-start obligation is owed there — the seam is inert. -/
theorem adjA_seam_vacuous (a rest : List Tok) (ha : adjA a) (h_rest : adjA rest)
    (h_tail_a : ∀ (hla : 0 < a.length),
       (a[a.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ Tok.opn) :
    adjA (a ++ [Tok.sep] ++ rest) :=
  adj_seam Tok.opn Tok.cls a rest Tok.sep ha h_rest (fun h => absurd h (by decide)) h_tail_a

/-- At the SEAM trigger: the headed wrap's head obligation is VACUOUS (the `.opn` opener ≠ `.sep`
    trigger), so NO content-start obligation is owed there — the obligation SHED from the head. -/
theorem adjB_wrapHeaded_vacuous (cl : Tok) (body : List Tok)
    (h_body : adjB body)
    (h_tail : ∀ (hla : 0 < body.length),
       (body[body.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ Tok.sep) :
    adjB (Tok.opn :: (body ++ [cl])) :=
  adj_wrap_headed Tok.sep Tok.key Tok.opn cl body h_body (fun h => absurd h (by decide)) h_tail

/-- At the SEAM trigger: the SEAM glue's head obligation is LOAD-BEARING (the `.sep` seam IS the
    `.sep` trigger), so the content-start obligation RELOCATED here from the wrap head. -/
theorem adjB_seam_obligated (a rest : List Tok) (ha : adjB a) (h_rest : adjB rest)
    (h_head_rest : ∀ (h0 : 0 < rest.length), (rest[0]'h0) ≠ Tok.key →
        isContent (rest[0]'h0) = true)
    (h_tail_a : ∀ (hla : 0 < a.length),
       (a[a.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ Tok.sep) :
    adjB (a ++ [Tok.sep] ++ rest) :=
  adj_seam Tok.sep Tok.key a rest Tok.sep ha h_rest (fun _ => h_head_rest) h_tail_a

/-! ## NEGATIVE — the 'last ≠ trigger' tail bridge loses its empty-tail case at the trigger seam. -/

/-- A seam shape `a ++ [feTok] ++ rest` with `rest = []` and `feTok = .sep` (the seam trigger):
    `[scal] ++ [sep] ++ [] = [scal, sep]`. -/
def wSeamTrailing : List Tok := [Tok.scal] ++ [Tok.sep] ++ []

/-- With `rest = []`, the last token of this shape IS the `.sep` trigger seam.  For the OPENER
    trigger the analogue covered `rest = []` (the inert `.sep` seam ≠ `.opn`); here it cannot. -/
theorem seamTrailing_last_is_trigger :
    wSeamTrailing[wSeamTrailing.length - 1]'(by decide) = Tok.sep := by decide

/-- So 'last ≠ trigger' is FALSE at `rest = []`: the `OpenerAdj`-style tail bridge has NO sound
    `.sep` analogue at the empty tail — its domain must excise the trigger-coinciding seat. -/
theorem seamTrailing_last_not_ne_trigger :
    ¬ (wSeamTrailing[wSeamTrailing.length - 1]'(by decide) ≠ Tok.sep) := by decide

/-- The SOUND form needs `rest ≠ []`: with a content tail (`rest = [scal]`) the shape
    `[scal] ++ [sep] ++ [scal]` ends in `.scal`, not the `.sep` seam, so 'last ≠ .sep' holds —
    exactly the `rest ≠ []` restriction (`lastNonSep_append_right`). -/
def wSeamNonTrailing : List Tok := [Tok.scal] ++ [Tok.sep] ++ [Tok.scal]

theorem seamNonTrailing_last_ne_trigger :
    wSeamNonTrailing[wSeamNonTrailing.length - 1]'(by decide) ≠ Tok.sep := by decide

#guard isContent Tok.scal == true
#guard isContent Tok.cls == false
#guard wSeamTrailing.length == 2          -- rest = [] ⇒ the seam is the last token
#guard wSeamNonTrailing.length == 3       -- rest ≠ [] ⇒ a content token is last

end Tests.Reflections.TriggerCoincidenceRelocatesObligation
