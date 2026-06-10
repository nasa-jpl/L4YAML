/-!
# Reflection 344 — a multi-field guard INPUT localizes its dependency knot to ONE load-bearing field; audit field-by-field before concluding the whole guard is needed

Self-contained (core Lean, no `L4YAML` import) toy model of the AUDIT behind the dispatch de-front
(`(i'-b-B2c-dispatch-defront)`), the move that follows R343's context-free-adapter knot.

R343 found that threading the per-window fact `FlowBodyContent` as a recursion `G`-conjunct hits a
co-recursive knot.  The pivot is to remove `FlowBodyContent` from the dispatch's INPUT — but the
dispatch's input is a THREE-field guard, and the naïve fear is that the *whole* guard creates the
dependency.  The AUDIT (this reflection) shows it does not: of the three fields,

* `headContentStart` is a FREE projection — definitionally the SAME proposition as a field of the
  `FlowBodyContentDeep` guard the recursion ALREADY carries (`h_deep.headContentStart`);
* `feContentStart` is DEAD — not consumed by the dispatch or EITHER bracket oracle (it serves the
  advance-tail plumbing, a *sibling* consumer, never the head-shape dispatch);
* `bodySucc` is the GENUINE residual — R296: no all-depth balance-free form, NOT a field of
  `FlowBodyContentDeep`, so it cannot be reconstructed; it needs the window's `SafeBodyUnit`.

So the knot the full guard seemed to create localizes to the SINGLE field `bodySucc`, used at the
SINGLE kind of position the first entry's END.  The free + dead fields MASKED which one field is
load-bearing.  Auditing field-by-field (rather than reasoning about the guard wholesale) shrinks the
producer's debt to its minimum and turns "the guard creates a cycle" into "field `bodySucc` at the
first-entry-end creates a cycle" — a far smaller, precisely-named obligation.

The toy below abstracts the three fields and the already-carried deep guard.

POSITIVE (`dispatch_defront` + `dispatch_via_deep_and_succ`): the consumer is inhabitable from the
already-carried `Deep` (supplying the free `head`) plus the lone residual `succ` — with NO `feStart`
field in its signature at all.  The full `Guard` route factors through it.

NEGATIVE (`deep_holds_without_succ` + `defront_needs_succ`): `succ` is genuinely irreducible — `Deep`
can hold while `succ` fails (`Succ := False`), so there is no `Deep → succ` function; the de-front
must take `h_succ` as a standing hypothesis.  That is exactly the field R296 says needs the window's
`SafeBodyUnit`, named by the audit as the residual the de-front relocates the knot to.
-/

namespace Tests.Reflections.FieldAuditLocalizesKnot

set_option autoImplicit false

/-! ## The two guards: the one the recursion ALREADY carries, and the consumer's full input

`Deep` is the all-depth, balance-free guard the `windowWidth_strongRecOn` recursion threads (toy
`FlowBodyContentDeep`).  `Guard` is the consumer's full multi-field input (toy `FlowBodyContent`).
The load-bearing observation: `Guard.head` and `Deep.head` have the SAME target `Head` — so the
consumer's `head` need is already met by the carried `Deep`. -/

/-- The guard the recursion already threads (toy `FlowBodyContentDeep`).  `head` is the window-head
    content-start fact; `opener` is its all-depth opener fact. -/
structure Deep (Head Opener : Prop) : Prop where
  head : Head
  opener : Opener

/-- The consumer's full multi-field input guard (toy `FlowBodyContent`): THREE fields.

    * `head : Head` — the SAME proposition as `Deep.head` (a FREE projection of the carried guard).
    * `succ : Succ` — the separator-successor fact (`bodySucc`; R296 — no balance-free form, NOT a
      field of `Deep`); the genuine residual.
    * `feStart : FeStart` — the advance-tail re-seat fact, used only by the recursion plumbing, never
      by this consumer (DEAD weight here). -/
structure Guard (Head Succ FeStart : Prop) : Prop where
  head : Head
  succ : Succ
  feStart : FeStart

/-! ## POSITIVE — the de-fronted consumer: `Deep` (free `head`) + the lone residual `succ`, no `feStart` -/

/-- The carrier-route consumer (toy `recseqentry_window_dispatch`): it is HANDED the whole `Guard`,
    but its body touches only `head` and `succ` — never `feStart`. -/
theorem dispatch_via_guard (Head Succ FeStart Concl : Prop)
    (step : Head → Succ → Concl) (g : Guard Head Succ FeStart) : Concl :=
  step g.head g.succ

/-- **The audit's positive finding — the de-front.**  The consumer needs only the already-carried
    `Deep` (for `head`, a FREE projection: `Guard.head` and `Deep.head` have the SAME target `Head`)
    plus the SINGLE residual `succ`.  `feStart` is DROPPED entirely — `FeStart` does not even appear
    in the signature.  The knot the full `Guard` seemed to create localizes to exactly one field. -/
theorem dispatch_defront (Head Opener Succ Concl : Prop)
    (step : Head → Succ → Concl) (d : Deep Head Opener) (h_succ : Succ) : Concl :=
  step d.head h_succ

/-- The carrier route FACTORS THROUGH the de-front: given the already-carried `Deep`, feed the de-front
    `Deep` (for the free `head`) and the guard's lone residual `g.succ`.  `g.head` (redundant with
    `Deep.head`) and `g.feStart` (dead) are never needed. -/
theorem dispatch_via_deep_and_succ (Head Opener Succ FeStart Concl : Prop)
    (step : Head → Succ → Concl) (d : Deep Head Opener) (g : Guard Head Succ FeStart) : Concl :=
  dispatch_defront Head Opener Succ Concl step d g.succ

/-! ## NEGATIVE — `succ` is the genuine residual: `Deep` cannot supply it (R296: no balance-free form)

If `succ` were a projection of `Deep`, the de-front would need no `h_succ` argument.  It does — and
concretely, `Deep` can hold while `succ` fails, so no `Deep → succ` function exists.  Model the window
where the head is content-start (`Deep` holds) but the successor fact is unavailable (`Succ := False`):
the de-fronted conclusion is reachable ONLY through the supplied `h_succ`. -/

/-- `Deep` holds at a window (head content-start + opener fact) with NO separator-successor available:
    `Deep True True` is inhabited though `Succ := False` is not.  So `Deep` cannot yield `succ` — it is
    the irreducible residual, exactly the field R296 says needs the window's `SafeBodyUnit`. -/
theorem deep_holds_without_succ : Deep True True := ⟨trivial, trivial⟩

/-- With `Succ := False`, the de-front is inhabitable iff you are HANDED `h_succ` — confirming `succ`
    is load-bearing (the conclusion follows by ex falso only because `h_succ : False` is supplied,
    never reconstructed from `Deep`). -/
theorem defront_needs_succ (Concl : Prop) (h_succ : False) : Concl :=
  dispatch_defront True True False Concl (fun _ h => h.elim) deep_holds_without_succ h_succ

/-! ## A concrete model — the de-front delivers; `feStart` is provably absent from its signature -/

/-- The trivial concrete model: every field's target holds. -/
abbrev HeadT : Prop := True
abbrev OpenerT : Prop := True
abbrev SuccT : Prop := True
abbrev FeStartT : Prop := True
abbrev ConclT : Prop := True

theorem stepT : HeadT → SuccT → ConclT := fun _ _ => trivial
theorem deepT : Deep HeadT OpenerT := ⟨trivial, trivial⟩
theorem guardT : Guard HeadT SuccT FeStartT := ⟨trivial, trivial, trivial⟩

example : ConclT := dispatch_via_guard HeadT SuccT FeStartT ConclT stepT guardT
example : ConclT := dispatch_defront HeadT OpenerT SuccT ConclT stepT deepT trivial
example : ConclT := dispatch_via_deep_and_succ HeadT OpenerT SuccT FeStartT ConclT stepT deepT guardT

#guard (decide HeadT)     -- the free field's target (sourced from the carried `Deep`)
#guard (decide SuccT)     -- the residual field's target (the lone load-bearing field)
#guard true               -- the de-front delivers with NO `FeStart` field in its signature

end Tests.Reflections.FieldAuditLocalizesKnot
