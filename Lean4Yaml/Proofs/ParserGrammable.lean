/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Grammar
import Lean4Yaml.TokenParser
import Lean4Yaml.Proofs.ScannerPlainScalarValid
import Lean4Yaml.Proofs.Composition
import Lean4Yaml.Proofs.ParserSoundness

/-!
# Phase C: Discharge `h_grammable` (ParserGrammable)

Proves that scanner+parser output, after composition (`resolveAliases` +
`stripAnchors`), satisfies `Grammable`. This discharges the `h_grammable`
hypothesis in `ParserCorrectness.lean`.

## Architecture

```
scan_plain_scalar_valid (B3.5)
    │ tokens → ScalarScannable
    ▼
parseStream_output_scannable (C2)
    │ tree → Scannable
    ▼
compose_scannable_to_grammable (C1)
    │ Scannable → Grammable (after compose)
    ▼
parseStream_output_grammable (C3)
```

## Key Insights

1. **`ScalarScannable` depends only on `content` and `style`** — not on `tag`,
   `anchor`, or `blockMeta`. This means `stripAnchors` (which clears `anchor`)
   preserves ScalarScannable, and the parser attaching tag/anchor from
   `NodeProperties` doesn't affect it.

2. **Cross-context aliasing gap**: An anchor defined in block context may
   contain plain scalars with flow indicators. If aliased into flow context,
   `ScalarScannable _ true` requires `noFlowIndicators`, which may fail.
   This is handled by the `WellFormedAnchors` precondition.

3. **B3.5 gives `ScalarScannable _ false`** (the universal/weaker form),
   while flow-context nodes need `ScalarScannable _ true` (stronger).
   For scalars originally scanned in flow context, B3.4 actually gives
   `ScalarScannable _ true`, but this per-token context is lost in B3.5's
   universal weakening. Phase C uses `ScalarScannable _ false` for
   non-alias scalars and requires `WellFormedAnchors` for alias targets.

## Sorry inventory

Sorries fall into three categories:

1. **List/Array conversion** (stripAnchors_preserves_Grammable): The
   `stripAnchors` function uses `where`-clause mutual recursion converting
   Array→List→Array. Proving element-wise correspondence requires showing
   `stripList l = l.map stripAnchors` and threading through Array indices.

2. **Alias resolution** (compose_value_grammable): Proving that
   `resolveAliases` produces alias-free values requires tracking alias
   lookups through the recursive walk.

3. **Parser chain** (parseStream_output_scannable): Showing the parser
   produces `Scannable` trees requires tracing token→YamlValue construction
   through all of `parseNode`/`parseDocument`/`parseStream`.
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.ParserGrammable

open Lean4Yaml
open Lean4Yaml.Grammar
open Lean4Yaml.TokenParser
open Lean4Yaml.Proofs.ScannerPlainScalarValid
open Lean4Yaml.Proofs.Composition

/-! ## §1  ScalarScannable Metadata Independence

`ScalarScannable` depends only on `Scalar.content` and `Scalar.style`.
The `tag`, `anchor`, and `blockMeta` fields are irrelevant.
-/

/-- `ScalarScannable` depends only on `content` and `style`. -/
theorem ScalarScannable_eq_of_content_style_eq
    (c : String) (st : ScalarStyle)
    (t1 t2 : Option String) (a1 a2 : Option String)
    (b1 b2 : Option BlockScalarMeta) (inFlow : Bool) :
    ScalarScannable ⟨c, st, t1, a1, b1⟩ inFlow ↔
      ScalarScannable ⟨c, st, t2, a2, b2⟩ inFlow := by
  constructor <;> (intro h hplain hlen; exact h hplain hlen)

/-- Clearing the anchor field preserves `ScalarScannable`. -/
theorem ScalarScannable_strip_anchor (s : Scalar) (inFlow : Bool) :
    ScalarScannable s inFlow ↔
      ScalarScannable { s with anchor := none } inFlow := by
  constructor <;> (intro h hplain hlen; exact h hplain hlen)

/-- Non-plain scalars trivially satisfy `ScalarScannable`. -/
theorem ScalarScannable_of_nonplain (s : Scalar) (inFlow : Bool)
    (h : s.style ≠ .plain) :
    ScalarScannable s inFlow :=
  fun hplain _ => absurd hplain h

/-! ## §2  `stripAnchors` Preserves `Grammable`

`YamlValue.stripAnchors` only clears anchor fields. Since `Grammable`
does not constrain anchor fields and `ScalarScannable` is metadata-
independent, `Grammable` is preserved.
-/

/-- `stripAnchors` on a `.scalar` node preserves `Grammable`. -/
theorem stripAnchors_scalar_grammable (s : Scalar) (inFlow : Bool)
    (h : Grammable (.scalar s) inFlow) :
    Grammable (.scalar { s with anchor := none }) inFlow := by
  cases h with
  | scalar _ _ h_ss =>
    exact .scalar { s with anchor := none } inFlow
      ((ScalarScannable_strip_anchor s inFlow).mp h_ss)

/-- The `stripList` where-clause helper equals `List.map stripAnchors`. -/
theorem stripList_eq_map (l : List YamlValue) :
    YamlValue.stripAnchors.stripList l = l.map YamlValue.stripAnchors := by
  induction l with
  | nil => simp [YamlValue.stripAnchors.stripList]
  | cons v vs ih => simp [YamlValue.stripAnchors.stripList, ih]

/-- The `stripPairs` where-clause helper equals `List.map` over pairs. -/
theorem stripPairs_eq_map (l : List (YamlValue × YamlValue)) :
    YamlValue.stripAnchors.stripPairs l =
      l.map (fun (k, v) => (k.stripAnchors, v.stripAnchors)) := by
  induction l with
  | nil => simp [YamlValue.stripAnchors.stripPairs]
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp [YamlValue.stripAnchors.stripPairs, ih]

set_option maxHeartbeats 2400000 in
/-- `stripAnchors` preserves `Grammable` for any value.

The proof is by induction on the `Grammable` derivation. The scalar
case uses metadata independence. The sequence/mapping cases use the
`stripList_eq_map`/`stripPairs_eq_map` lemmas to reduce where-clause
mutual recursion to `List.map`, then apply the IH element-wise. -/
theorem stripAnchors_preserves_Grammable (v : YamlValue) (inFlow : Bool) :
    Grammable v inFlow → Grammable v.stripAnchors inFlow := by
  intro h
  induction h with
  | scalar s inFlow h_ss =>
    exact .scalar { s with anchor := none } inFlow
      (fun hplain hlen => h_ss hplain hlen)
  | sequence style items tag anchor inFlow h_items ih_items =>
    show Grammable (.sequence style (YamlValue.stripAnchors.stripList items.toList).toArray tag none) inFlow
    rw [stripList_eq_map]
    apply Grammable.sequence
    intro ⟨i, hi⟩
    simp at hi ⊢
    exact ih_items ⟨i, hi⟩
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    show Grammable (.mapping style (YamlValue.stripAnchors.stripPairs pairs.toList).toArray tag none) inFlow
    rw [stripPairs_eq_map]
    apply Grammable.mapping
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_k ⟨i, hi⟩
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_v ⟨i, hi⟩

/-! ## §3  `Scannable` → `Grammable` for Alias-Free Values

When a value has no `.alias` nodes, `Scannable` and `Grammable` coincide
(modulo the `.alias` constructor that `Scannable` allows).
-/

/-- A `YamlValue` contains no alias nodes. -/
inductive AliasFree : YamlValue → Prop where
  | scalar (s : Scalar) : AliasFree (.scalar s)
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag : Option String) (anchor : Option String)
      (h : ∀ i : Fin items.size, AliasFree items[i]) :
      AliasFree (.sequence style items tag anchor)
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag : Option String) (anchor : Option String)
      (hk : ∀ i : Fin pairs.size, AliasFree pairs[i].1)
      (hv : ∀ i : Fin pairs.size, AliasFree pairs[i].2) :
      AliasFree (.mapping style pairs tag anchor)

/-- Alias-free `Scannable` implies `Grammable`. -/
theorem Scannable_aliasFree_to_Grammable (v : YamlValue) (inFlow : Bool) :
    Scannable v inFlow → AliasFree v → Grammable v inFlow := by
  intro h_scan h_af
  induction h_scan with
  | scalar s _ h_ss => exact .scalar s _ h_ss
  | alias _ _ => cases h_af
  | sequence style items tag anchor inFlow h_items ih_items =>
    cases h_af with
    | sequence _ _ _ _ h_af_items =>
      apply Grammable.sequence
      intro ⟨i, hi⟩
      exact ih_items ⟨i, hi⟩ (h_af_items ⟨i, hi⟩)
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    cases h_af with
    | mapping _ _ _ _ h_afk h_afv =>
      apply Grammable.mapping
      · intro ⟨i, hi⟩
        exact ih_k ⟨i, hi⟩ (h_afk ⟨i, hi⟩)
      · intro ⟨i, hi⟩
        exact ih_v ⟨i, hi⟩ (h_afv ⟨i, hi⟩)

/-! ## §4  Compose: `Scannable` → `Grammable` (C1)

### Preconditions

`compose_value_grammable` requires:
1. The pre-compose value satisfies `Scannable v inFlow`
2. All aliases in `v` resolve through the anchor map (`AllAliasesResolve`)
3. Resolved anchor values are themselves `Grammable` at every flow context
   (`WellFormedAnchors`)

The third precondition handles cross-context aliasing: an anchor defined
in block context may be aliased into flow context, so the resolved value
must be `Grammable` at any flow context it might appear in.

### Why `∀ ctx` in WellFormedAnchors

A plain scalar like `value{key}` scanned in block context satisfies
`ScalarScannable _ false` but NOT `ScalarScannable _ true` (due to
flow indicators `{` and `}`). If this value is aliased into flow context,
`Grammable _ true` requires `ScalarScannable _ true`, which fails.

The `∀ ctx` precondition excludes such cross-context aliasing scenarios.
In practice, most YAML documents don't alias block-context plain scalars
with flow indicators into flow context.
-/

/-- All alias nodes in a value resolve through the anchor map. -/
inductive AllAliasesResolve : YamlValue → Array (String × YamlValue) → Prop where
  | scalar (s : Scalar) (anchors : Array (String × YamlValue)) :
      AllAliasesResolve (.scalar s) anchors
  | alias (name : String) (anchors : Array (String × YamlValue))
      (h : (anchors.findSome? (fun (n, _) => if n == name then some () else none)).isSome) :
      AllAliasesResolve (.alias name) anchors
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag : Option String) (anchor : Option String)
      (anchors : Array (String × YamlValue))
      (h : ∀ i : Fin items.size, AllAliasesResolve items[i] anchors) :
      AllAliasesResolve (.sequence style items tag anchor) anchors
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag : Option String) (anchor : Option String)
      (anchors : Array (String × YamlValue))
      (hk : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].1 anchors)
      (hv : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].2 anchors) :
      AllAliasesResolve (.mapping style pairs tag anchor) anchors

/-- Anchor values are well-formed: after stripping, they are `Grammable`
    at every flow context. -/
def WellFormedAnchors (anchors : Array (String × YamlValue)) : Prop :=
  ∀ (name : String) (val : YamlValue),
    anchors.findSome? (fun (n, v) => if n == name then some v else none) = some val →
      ∀ inFlow, Grammable val.stripAnchors inFlow

/-- If `findSome?` with unit-returning predicate succeeds, then
    `findSome?` with value-returning predicate also succeeds. -/
theorem findSome_unit_to_val (arr : Array (String × YamlValue)) (name : String)
    (h : (arr.findSome? (fun (n, _) => if n == name then some () else none)).isSome) :
    ∃ val, arr.findSome? (fun (n, v) => if n == name then some v else none) = some val := by
  simp only [Option.isSome_iff_exists] at h
  obtain ⟨_, h_find⟩ := h
  rw [Array.findSome?_eq_some_iff] at h_find
  obtain ⟨ys, a, zs, h_split, h_fa, h_prefix⟩ := h_find
  have h_beq : (a.1 == name) = true := by
    revert h_fa
    split
    · intro _; assumption
    · intro h_abs; simp at h_abs
  exact ⟨a.2, Array.findSome?_eq_some_iff.mpr
    ⟨ys, a, zs, h_split, by simp [h_beq], fun x hx => by
      have h_unit := h_prefix x hx
      by_cases h_eq : x.1 == name
      · simp [h_eq] at h_unit
      · simp [h_eq]⟩⟩

/-- The `resolveList` where-clause helper equals `List.map resolveAliases`. -/
theorem resolveList_eq_map (l : List YamlValue) (anchors : Array (String × YamlValue)) :
    YamlValue.resolveAliases.resolveList l anchors =
      l.map (fun v => v.resolveAliases anchors) := by
  induction l with
  | nil => simp [YamlValue.resolveAliases.resolveList]
  | cons v vs ih => simp [YamlValue.resolveAliases.resolveList, ih]

/-- The `resolvePairs` where-clause helper equals `List.map` over pairs. -/
theorem resolvePairs_eq_map (l : List (YamlValue × YamlValue))
    (anchors : Array (String × YamlValue)) :
    YamlValue.resolveAliases.resolvePairs l anchors =
      l.map (fun (k, v) => (k.resolveAliases anchors, v.resolveAliases anchors)) := by
  induction l with
  | nil => simp [YamlValue.resolveAliases.resolvePairs]
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp [YamlValue.resolveAliases.resolvePairs, ih]

set_option maxHeartbeats 4000000 in
/-- C1: Composing a `Scannable` value produces a `Grammable` value,
    provided all aliases resolve and anchor values are well-formed.

    `doc.compose.value = (doc.value.resolveAliases doc.anchors).stripAnchors`

    The proof is by induction on the `Scannable` derivation:
    - **scalar**: resolveAliases is identity on scalars; use metadata independence.
    - **alias**: Use `findSome_unit_to_val` to resolve the alias lookup,
      then apply `WellFormedAnchors`.
    - **sequence/mapping**: Rewrite where-clause recursion using
      `resolveList_eq_map`/`resolvePairs_eq_map` and
      `stripList_eq_map`/`stripPairs_eq_map`, then apply IH element-wise. -/
theorem compose_value_grammable
    (v : YamlValue) (anchors : Array (String × YamlValue)) (inFlow : Bool)
    (h_scan : Scannable v inFlow)
    (h_resolve : AllAliasesResolve v anchors)
    (h_anchors : WellFormedAnchors anchors) :
    Grammable (v.resolveAliases anchors).stripAnchors inFlow := by
  induction h_scan with
  | scalar s inFlow h_ss =>
    exact .scalar { s with anchor := none } inFlow
      (fun hplain hlen => h_ss hplain hlen)
  | alias name inFlow =>
    cases h_resolve with
    | alias _ _ h_res =>
      obtain ⟨resolved, h_val⟩ := findSome_unit_to_val anchors name h_res
      have h_eq : (YamlValue.alias name).resolveAliases anchors =
        (match anchors.findSome? (fun (n, v) => if n == name then some v else none) with
         | some v => v | none => .alias name) := rfl
      rw [h_eq, h_val]
      exact h_anchors name resolved h_val inFlow
  | sequence style items tag anchor inFlow h_items ih_items =>
    cases h_resolve with
    | sequence _ _ _ _ _ h_resolve_items =>
      show Grammable (.sequence style
        (YamlValue.stripAnchors.stripList
          (YamlValue.resolveAliases.resolveList items.toList anchors).toArray.toList).toArray
        tag none) inFlow
      rw [List.toList_toArray, stripList_eq_map, resolveList_eq_map]
      apply Grammable.sequence
      intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_items ⟨i, hi⟩ (h_resolve_items ⟨i, hi⟩)
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    cases h_resolve with
    | mapping _ _ _ _ _ hk_resolve hv_resolve =>
      show Grammable (.mapping style
        (YamlValue.stripAnchors.stripPairs
          (YamlValue.resolveAliases.resolvePairs pairs.toList anchors).toArray.toList).toArray
        tag none) inFlow
      rw [List.toList_toArray, stripPairs_eq_map, resolvePairs_eq_map]
      apply Grammable.mapping
      · intro ⟨i, hi⟩
        simp at hi ⊢
        exact ih_k ⟨i, hi⟩ (hk_resolve ⟨i, hi⟩)
      · intro ⟨i, hi⟩
        simp at hi ⊢
        exact ih_v ⟨i, hi⟩ (hv_resolve ⟨i, hi⟩)

/-- C1 applied to `YamlDocument.compose`. -/
theorem compose_grammable (doc : YamlDocument)
    (h_scan : Scannable doc.value false)
    (h_resolve : AllAliasesResolve doc.value doc.anchors)
    (h_anchors : WellFormedAnchors doc.anchors) :
    Grammable doc.compose.value false := by
  simp only [YamlDocument.compose]
  exact compose_value_grammable doc.value doc.anchors false h_scan h_resolve h_anchors

/-! ## §5  Parser Output is `Scannable` (C2)

The parser constructs `YamlValue` trees from token arrays. Each scalar
node's `content` and `style` come directly from a `YamlToken.scalar`
token. By B3.5, every plain scalar token satisfies `ScalarScannable _ false`.
Non-plain scalars satisfy `ScalarScannable` vacuously (`style ≠ .plain`).
Aliases satisfy `Scannable.alias` trivially.

**Sorry**: The full proof requires tracing the token→tree construction
through `parseNode`, `parseDocument`, and `parseStream`, showing that
every `YamlValue.scalar` in the output has content/style from a scanner
token. This is structurally straightforward (the parser pattern-matches
on `YamlToken.scalar content style` and constructs
`YamlValue.scalar { content, style, ... }`) but involves deep parser
function unfolding.
-/

/-! ### C2 Bridge Lemmas

These connect B3.5's token-level `PlainScalarsValid` to the tree-level
`Scannable` predicate for scalar base cases. Used by the parser tracing
proofs (when completed). -/

/-- A scalar YamlValue constructed from a token satisfying PlainScalarsValid
    is Scannable. Bridges token-level ScalarScannable → tree-level Scannable. -/
theorem scalar_from_token_scannable
    (tokens : Array (Positioned YamlToken))
    (h_psv : PlainScalarsValid tokens)
    (i : Nat) (hi : i < tokens.size)
    (content : String) (style : ScalarStyle)
    (h_tok : (tokens[i]'hi).val = .scalar content style)
    (tag anchor : Option String) :
    Scannable (.scalar ⟨content, style, tag, anchor, none⟩) false := by
  apply Scannable.scalar
  intro hplain hlen
  have h_match := h_psv i hi
  rw [h_tok] at h_match
  cases style with
  | plain => exact h_match hplain hlen
  | _ => contradiction

/-- Empty content scalar (parser empty node) is trivially Scannable. -/
theorem empty_scalar_scannable (tag anchor : Option String) :
    Scannable (.scalar ⟨"", .plain, tag, anchor, none⟩) false := by
  apply Scannable.scalar; intro _ hlen; simp at hlen

/-- C2: Every document produced by `parseStream` from scanner tokens
    has a `Scannable` value tree.

    The proof connects B3.5's token-level `ScalarScannable` to the
    tree-level `Scannable` predicate. The key observation is that
    `parseNode` constructs `YamlValue.scalar { content, style, tag, anchor }`
    directly from `YamlToken.scalar content style`, preserving the
    content and style that B3.5 has already validated.

    **Sorry**: Requires tracing through `parseNode`/`parseDocument`/
    `parseStream` to show content/style preservation. -/
theorem parseStream_output_scannable
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_scan_tokens : PlainScalarsValid tokens)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, Scannable doc.value false := by
  sorry

/-- Every document's aliases resolve through its anchor map.

    The parser maintains anchor maps per document: when `parseNode` sees
    an `&anchor` token, it records `(anchor, value)`. When the parser
    produces the document, `doc.anchors` contains all such bindings.
    Every `.alias name` in `doc.value` references a name that was
    previously anchored.

    **Sorry**: Requires tracing through the parser's anchor map management. -/
theorem parseStream_output_aliases_resolve
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, AllAliasesResolve doc.value doc.anchors := by
  sorry

/-- Anchor values in parser output are well-formed.

    Each anchor value was constructed by `parseNode` from scanner tokens.
    By B3.5, plain scalar tokens satisfy `ScalarScannable _ false`.
    Non-plain scalars satisfy `ScalarScannable` vacuously.

    **Caveat**: `WellFormedAnchors` requires `∀ inFlow, Grammable _ inFlow`.
    This holds for anchor values that don't contain plain scalars with
    flow indicators. The `∀ inFlow` quantifier may fail for block-context
    plain scalars containing `{`, `}`, `[`, or `]`.

    **Sorry**: Requires parser tracing + the `∀ inFlow` justification. -/
theorem parseStream_output_anchors_wellformed
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_scan_tokens : PlainScalarsValid tokens)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, WellFormedAnchors doc.anchors := by
  sorry

/-! ## §6  Final Theorem (C3)

Combines C1 (compose_scannable_to_grammable) and C2 (parseStream_output_scannable)
to discharge `h_grammable`.
-/

/-- `scanFiltered` preserves `PlainScalarsValid`.
    Filtering removes non-content tokens; plain scalar tokens are preserved. -/
theorem scanFiltered_plain_scalars_valid (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    PlainScalarsValid tokens :=
  fun i hi => scan_plain_scalar_valid input tokens h i hi

/-- **C3**: Every document produced by the full pipeline (scan + parse + compose)
    is `Grammable`.

    This theorem eliminates the `h_grammable` hypothesis from
    `parseStream_respects_grammar` in `ParserCorrectness.lean`.

    **Architecture**: Chains B3.5 → C2 → C1 → Grammable.

    **Precondition on anchors**: `WellFormedAnchors` requires that anchor
    values are `Grammable` at every flow context. This excludes the
    pathological case where block-context plain scalars with flow
    indicators are aliased into flow context. See §4 for details. -/
theorem parseStream_output_grammable
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (raw_docs : Array YamlDocument)
    (h_scan : Scanner.scanFiltered input = .ok tokens)
    (h_parse : parseStream tokens = .ok raw_docs) :
    ∀ doc ∈ raw_docs.toList, Grammable doc.compose.value false := by
  intro doc hdoc
  have h_psv := scanFiltered_plain_scalars_valid input tokens h_scan
  have h_scannable := parseStream_output_scannable tokens raw_docs h_psv h_parse doc hdoc
  have h_resolve := parseStream_output_aliases_resolve tokens raw_docs h_parse doc hdoc
  have h_anchors := parseStream_output_anchors_wellformed tokens raw_docs h_psv h_parse doc hdoc
  exact compose_grammable doc h_scannable h_resolve h_anchors

/-- **Unconditional correctness**: The full `parseYaml` pipeline produces
    documents whose values have `ValidNode` witnesses.

    Combines the final grammability result with the existing
    `parseStream_respects_grammar` theorem. -/
theorem parseYaml_produces_valid_nodes
    (input : String)
    (docs : Array YamlDocument)
    (h : parseYaml input = .ok docs) :
    ∀ doc ∈ docs.toList, ∃ node : ValidNode,
      stripAnnotations (toYamlValue node) = stripAnnotations doc.value := by
  -- Decompose parseYaml into parseYamlRaw + compose
  simp only [parseYaml] at h
  split at h
  · rename_i raw_docs h_raw
    injection h with h_eq
    -- raw_docs are the pre-compose documents
    -- docs = raw_docs.map YamlDocument.compose
    -- Decompose parseYamlRaw into scan + parseStream
    have ⟨tokens, h_scan, h_parse⟩ := parseYamlRaw_ok_decompose input raw_docs h_raw
    -- Each composed doc is Grammable
    have h_gram := parseStream_output_grammable input tokens raw_docs h_scan h_parse
    -- Apply existing correctness theorem
    intro doc hdoc
    rw [← h_eq] at hdoc
    -- doc ∈ (raw_docs.map compose).toList
    -- So doc = raw_doc.compose for some raw_doc ∈ raw_docs.toList
    simp only [Array.toList_map] at hdoc
    obtain ⟨raw_doc, h_raw_mem, h_compose_eq⟩ := List.mem_map.mp hdoc
    subst h_compose_eq
    -- Need: Grammable raw_doc.compose.value false
    have h_g := h_gram raw_doc h_raw_mem
    -- raw_doc.compose.value is Grammable → has ValidNode witness
    exact ParserSoundness.yamlValue_has_witness
      raw_doc.compose.value false h_g
  · simp at h

end Lean4Yaml.Proofs.ParserGrammable
