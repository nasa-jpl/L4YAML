/-!
# Parametric assembler extraction — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the **parametric assembler extraction**
principle, documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`, Reflections 226 + 228
(sibling of `ReductionByImport.lean` / `ConvergentReduction.lean`).

**The principle.** When an inline `have P[c]` proves a *fixed instance* (`c` a concrete span / index)
and `P` is the shape you ultimately need *universally*, check whether the proof's dependence on `c`
flows entirely through its **hypotheses**. If so, lift it to a parametric assembler
`assemble : ∀ x, hyps x → P[x]` *now* — it generalizes **for free** (a proof whose only
constant-dependence is in its hypotheses is secretly a schema). This **partitions** the residual into
an *assemble* half (done, parametric, reusable) and a *produce-the-primitives* half (the recursion).
A proof that bakes the constant in *outside* the hypotheses (e.g. `decide` on the concrete value) does
**not** lift — it is stuck at the instance, and the recursion that needs `P` at other indices is blocked.

**Second, symmetric assembler is fresh-but-cheap** (Reflection 228). The map-side `mapBodyProps_assemble`
had no inline `have` to lift, yet was a one-shot increment, because the hard sub-lemmas (the bracket
conjuncts) were built as a *symmetric pair*. A second assembler over a parallel structure is pure
field-shape dispatch, only the helper differs.

The real instance: `seqBodyProps_assemble` / `mapBodyProps_assemble (tokens) (lo hi)`. Each takes the
balanced-subrange facts plus per-subrange primitives and produces the full `SeqBodyProps`/`MapBodyProps
tokens lo hi`; the proof generalized off the fixed span `(2, tokens.size−2)` for free because its only
span-specific inputs were hypotheses and the conjunct helpers were already parametric in `lo hi`.

This toy mirrors that exactly:

* **`SpanProps lo hi`** — a multi-field structural property of a half-open span `[lo, hi)`: two fields are
  *direct primitive projections* (`lo_pos`, `width`), one is *derived by a span-generic helper*
  (`mid_ok`, via `midpoint_in_span`) — the BodyProps shape in miniature.
* **POSITIVE `assemble`** — `∀ lo hi, 0 < lo → hi ≤ lo + 8 → SpanProps lo hi`: constant-free. The fixed
  instance `props_at_3_9` is one call; the SAME lemma serves any span (`props_at_1_5`), so the recursion
  calls one joint per node.
* **NEGATIVE `assembleBad`** — its extra `parity` field is true at `(3,9)` only, dischargeable by `decide`
  *after* substituting the constant, NOT among the primitives. So `assembleBad` carries an `(lo,hi)=(3,9)`
  premise: it yields the instance but no schema. `propsBad_not_at_3_8` witnesses that `SpanPropsBad` is not
  span-generic — the recursion is stuck.

The point is `assemble` (reused at a second span for free) vs `assembleBad` (cannot be reused — indeed
`SpanPropsBad 3 8` is false): deps-in-hypotheses lifts, baked-in-constant does not.

Run it: open in the IDE (the `#eval`s render in the infoview) or
`lake build Tests.ParametricAssemblerExtraction` (the `#guard`s fail the build if any expectation is wrong).
-/

namespace ParametricAssemblerExtraction

/-! ## The structure and its span-generic helper (the "conjunct"). -/

/-- **The span-generic helper** — the parametric "conjunct": for ANY non-empty span the midpoint lies in
    it.  Proven once, for all `(lo, hi)`; the assembler projects the `mid_ok` field through it.  This is
    the part that makes the lifted assembler reusable — it never depends on a concrete span. -/
theorem midpoint_in_span (lo hi : Nat) (h : lo < hi) :
    lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 < hi := by omega

/-- **The structural property** of a half-open span `[lo, hi)`, three fields — a BodyProps in miniature:
    - `lo_pos` / `width`: *direct primitive projections* (the producer must supply these per span);
    - `mid_ok`: *derived by the helper* `midpoint_in_span` (span-generic, no per-span input). -/
structure SpanProps (lo hi : Nat) : Prop where
  lo_pos : 0 < lo
  width  : hi ≤ lo + 8
  mid_ok : lo < hi → lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 < hi

/-! ## POSITIVE: the constant-free assembler lifts for free and serves every span. -/

/-- **POSITIVE assembler.**  Parametric in `(lo, hi)`, constant-free.  Every field is a projection of a
    primitive (`lo_pos` ← `hp`, `width` ← `hw`) or the span-generic helper (`mid_ok` ← `midpoint_in_span`).
    This IS the lifted inline `have SpanProps[c]`: the proof never mentions a concrete span, so abstracting
    the span to a parameter was free. -/
def assemble (lo hi : Nat) (hp : 0 < lo) (hw : hi ≤ lo + 8) : SpanProps lo hi :=
  ⟨hp, hw, fun h => midpoint_in_span lo hi h⟩

/-- The fixed instance — the former inline `have` — is now a one-line call. -/
theorem props_at_3_9 : SpanProps 3 9 := assemble 3 9 (by omega) (by omega)

/-- The SAME parametric lemma discharges a DIFFERENT span for free — this is the partition's payoff: the
    recursion calls one joint per node, never re-deriving the field assembly. -/
theorem props_at_1_5 : SpanProps 1 5 := assemble 1 5 (by omega) (by omega)

/-- *Produce-the-primitives* half, then compose: feed the per-span primitives to the assembler to get the
    property over the whole valid family.  `assemble ∘ produce = universal` — the recursion is exactly this,
    with the primitives derived from the nested structure rather than hypotheses. -/
theorem props_all (lo hi : Nat) (hp : 0 < lo) (hw : hi ≤ lo + 8) : SpanProps lo hi :=
  assemble lo hi hp hw

/-! ## NEGATIVE: a field whose proof bakes in the constant does not lift. -/

/-- **NEGATIVE structure.**  Same two primitives, plus `parity` — true at `(3,9)` (`12 % 2 = 0`) but NOT
    span-generic and NOT among the primitives.  A fixed-span proof could close it with `decide`; there is no
    helper that proves it for all spans (because it is false for some, e.g. `(3,8)`). -/
structure SpanPropsBad (lo hi : Nat) : Prop where
  lo_pos : 0 < lo
  width  : hi ≤ lo + 8
  parity : (lo + hi) % 2 = 0

/-- **NEGATIVE assembler.**  The `parity` field cannot be projected off a primitive or a span-generic
    helper, so the proof must BAKE IN the constant: it requires `(lo, hi) = (3, 9)`, then closes `parity` by
    `decide` after substitution.  The constant-dependence is now in the body, not (only) the hypotheses. -/
def assembleBad (lo hi : Nat) (hc : lo = 3 ∧ hi = 9) (hp : 0 < lo) (hw : hi ≤ lo + 8) :
    SpanPropsBad lo hi :=
  ⟨hp, hw, by obtain ⟨rfl, rfl⟩ := hc; decide⟩

/-- The fixed instance still works — the baked-in constant is available here. -/
theorem propsBad_at_3_9 : SpanPropsBad 3 9 := assembleBad 3 9 ⟨rfl, rfl⟩ (by omega) (by omega)

/-- But there is NO schema to extract: `SpanPropsBad` is genuinely false at `(3, 8)` (`11 % 2 = 1`), so no
    constant-free `∀ lo hi, hyps → SpanPropsBad lo hi` exists, and the recursion that needs the property at
    other spans is stuck.  The baked-in `(lo,hi)=(3,9)` premise cannot feed a varied recursion. -/
theorem propsBad_not_at_3_8 : ¬ SpanPropsBad 3 8 := by
  intro h; have := h.parity; omega

/-- The blockage made explicit: the baked-in constant cannot hold across a recursion over varied spans. -/
theorem no_universal_constant : ¬ ∀ lo hi, lo = 3 ∧ hi = 9 := by
  intro h; obtain ⟨h1, _⟩ := h 0 0; omega

/-! ## Second, symmetric assembler — fresh but cheap (Reflection 228).

A parallel structure `SpanProps2` (the "map side") with one extra field requiring one extra primitive
(mirroring the map body's 8 primitives vs the seq body's 3).  Its assembler is built FRESH — there was no
inline `have` to lift — yet is cheap: identical field-shape dispatch, the two helper-derived fields are the
bare outputs of a SYMMETRIC helper pair (`midpoint_in_span` / `lower_quarter_in_span`), no new mathematics.
(In the real code: M9/M10 `bracket_{seq,map}` are the bare typed-locator outputs, no successor wrapper.) -/

/-- The symmetric partner of `midpoint_in_span` — same proof shape, a different interior point. -/
theorem lower_quarter_in_span (lo hi : Nat) (h : lo < hi) :
    lo ≤ (3 * lo + hi) / 4 ∧ (3 * lo + hi) / 4 < hi := by omega

/-- **Second structure** (the "map side"): one extra primitive `extra` (the asymmetry), and one extra
    helper-derived field `quarter_ok` — the bare symmetric-helper output. -/
structure SpanProps2 (lo hi : Nat) : Prop where
  lo_pos     : 0 < lo
  width      : hi ≤ lo + 8
  extra      : lo ≤ hi
  mid_ok     : lo < hi → lo ≤ (lo + hi) / 2 ∧ (lo + hi) / 2 < hi
  quarter_ok : lo < hi → lo ≤ (3 * lo + hi) / 4 ∧ (3 * lo + hi) / 4 < hi

/-- **Second assembler.**  Built from scratch, but pure dispatch: three direct primitive projections and
    two bare symmetric-helper outputs.  The cost is field-shape matching, not proof. -/
def assemble2 (lo hi : Nat) (hp : 0 < lo) (hw : hi ≤ lo + 8) (he : lo ≤ hi) : SpanProps2 lo hi :=
  ⟨hp, hw, he, fun h => midpoint_in_span lo hi h, fun h => lower_quarter_in_span lo hi h⟩

/-- The second assembler serves the fixed span too — one call, same shape as `assemble`. -/
theorem props2_at_3_9 : SpanProps2 3 9 := assemble2 3 9 (by omega) (by omega) (by omega)

/-! ## `#guard` — the underlying computations: helper-field generalizes, baked-in field does not. -/

-- The span-generic helper at `(3,9)`: midpoint 6 lies in the span.
#guard (3 + 9) / 2 == 6
#guard 3 ≤ (3 + 9) / 2 && (3 + 9) / 2 < 9
-- The baked-in `parity` fact: holds at `(3,9)` …
#guard (3 + 9) % 2 == 0
-- … but FAILS at `(3,8)` — why it is not a span-generic schema.
#guard (3 + 8) % 2 == 1
-- The shared primitive (`width`) at `(3,9)`.
#guard 9 ≤ 3 + 8
-- The symmetric helper's interior point at `(3,9)`: (3*3+9)/4 = 18/4 = 4, in `[3,9)`.
#guard (3 * 3 + 9) / 4 == 4
#guard 3 ≤ (3 * 3 + 9) / 4 && (3 * 3 + 9) / 4 < 9

/-! ## `#eval` — over a family of spans: the helper field is universal, the baked-in field is not. -/

/-- One diagnostic row for span `[lo, hi)`: the helper-derived midpoint (always in-span) and the baked-in
    parity (span-specific). -/
def spanReport (lo hi : Nat) : String :=
  let m := (lo + hi) / 2
  s!"[{lo},{hi})  mid={m}  mid∈span={decide (lo ≤ m ∧ m < hi)}  parity0={decide ((lo + hi) % 2 = 0)}"

-- `mid∈span` is `true` everywhere (the helper generalizes — its assembler lifts); `parity0` varies
-- (the baked-in field is span-specific — its assembler does not lift).
/-- info: ["[3,9)  mid=6  mid∈span=true  parity0=true", "[3,8)  mid=5  mid∈span=true  parity0=false",
 "[1,5)  mid=3  mid∈span=true  parity0=true", "[2,7)  mid=4  mid∈span=true  parity0=false"] -/
#guard_msgs in
#eval [(3, 9), (3, 8), (1, 5), (2, 7)].map (fun p => spanReport p.1 p.2)

end ParametricAssemblerExtraction
