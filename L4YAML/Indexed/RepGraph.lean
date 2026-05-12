/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.Range
import L4YAML.Spec.Types

/-! # `RepGraph input range` — indexed L1 representation graph

The L1 representation graph parameterised by the input string and
the byte range it occupies (D1 from Blueprint 08).

## Indexing discipline

- `input : String` is a type parameter. Two graphs from different
  inputs have different types and cannot be confused.
- `range : Range input` is a type parameter (D1(a)). The graph
  occupies exactly the byte interval `range`.
- Sub-graphs in collections each carry their own range. The
  natural shape is `Σ r : Range input, RepGraph input r`, but Lean's
  nested-inductive elaboration rejects `Sigma` whose second
  component references the inductive being defined.
  D1(b) is realised via a **mutual inductive** with two sibling
  types `RepGraphChild` / `RepGraphPair` that play the role of the
  `Σ`-pairs (one wraps a single sub-graph at an arbitrary range; the
  other wraps a key/value pair at independent ranges).
- `AnchorMap input` is *not* a parameter of `RepGraph` itself — it
  is a side-channel produced/consumed by `compose`/`construct`,
  parameterised by the same `input` (D1(c)). The corresponding
  type lives in `L4YAML/Algebra/AnchorMap.lean` (Phase 2 §6).

## Phase 2 finding (D1(b) refinement)

The original D1(b) wording was “dependent pair
`Σ (r : Range input), RepGraph input r`”. Lean 4's kernel rejects
that as a nested inductive parameter. We realise the same
*type-level* content via a mutual sibling inductive
`RepGraphChild input` whose single constructor packages
`(r : Range input) × RepGraph input r`. The semantics are identical;
the syntactic shape differs. This refinement does not require
re-opening Phase 1 — D1(b) was an implementation guidance, not a
load-bearing API claim. The blueprint reflection in §Phase 2
records the choice.

## Phase 2 scope (this file)

Type signatures only — no construction, no elimination, no
algebra. The `compose : TokenStream input → Option (Σ r, RepGraph input r)`
function and the `construct` function land in Phases 4 and 5.

## Counterpart (legacy)

The legacy `YamlValue` (Spec/Types.lean) is the unindexed precursor.
Phase 4's parser cutover deletes the use of `YamlValue` in the
parser pipeline; `YamlValue` may remain as a thin façade for
application code that does not need source provenance.
-/

namespace L4YAML.Indexed

open L4YAML

mutual

/-- The L1 representation graph, indexed by source string and byte range.

    Each constructor carries its own `range` argument, which is
    required to equal the index `range` (the type system enforces
    this — the redundancy makes pattern matching ergonomic). -/
inductive RepGraph (input : String) : Range input → Type where
  /-- A scalar: source content + style. The `content` may differ
      from the raw bytes at `range` (escapes resolved, line folding
      applied). The original raw bytes are recoverable via `range`. -/
  | scalar
      (range : Range input)
      (content : String)
      (style : ScalarStyle)
      : RepGraph input range
  /-- A sequence (block or flow). Items are sub-graphs each at
      their own range; the outer `range` spans the whole collection
      (from the opening indicator or first item through the closing
      indicator or last item). -/
  | sequence
      (range : Range input)
      (style : CollectionStyle)
      (items : Array (RepGraphChild input))
      : RepGraph input range
  /-- A mapping (block or flow). Pairs are key/value sub-graphs each
      at independent ranges. -/
  | mapping
      (range : Range input)
      (style : CollectionStyle)
      (pairs : Array (RepGraphPair input))
      : RepGraph input range
  /-- An alias `*name`: refers to a previously-defined anchor.
      Resolution is performed by `construct` against an `AnchorMap`. -/
  | alias
      (range : Range input)
      (name : String)
      : RepGraph input range

/-- A single sub-graph at *some* range (the `Σ`-bundle realised as
    a mutual sibling inductive — see file docstring §Phase 2 finding). -/
inductive RepGraphChild (input : String) : Type where
  | mk (range : Range input) (graph : RepGraph input range) : RepGraphChild input

/-- A key/value pair where key and value live at *independent* ranges. -/
inductive RepGraphPair (input : String) : Type where
  | mk
      (keyRange : Range input)   (key   : RepGraph input keyRange)
      (valRange : Range input)   (value : RepGraph input valRange)
      : RepGraphPair input

end

namespace RepGraph

/-- The range an `RepGraph` occupies (mirrors the index parameter). -/
@[inline] def range {input : String} {r : Range input}
    (_ : RepGraph input r) : Range input := r

end RepGraph

end L4YAML.Indexed
