/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `LoadConfig` — bundled load-time configuration

Initiative 4 settled choice (Blueprint 08 §LoadConfig): bundle
`EqMode` + `DuplicateKeyPolicy` into a single `LoadConfig` structure
threaded through `parse`, `compose`, and `construct`.

The default value (`{}`) gives spec-strict behaviour:
  - `eqMode := .strict`              (error on cycle)
  - `duplicateKeyPolicy := .error`   (libyaml default)

This file holds **types only**; the `parse`/`compose`/`construct`
threading lands in Phases 3–5 along with the indexed-type pipeline.

## Open subtype: `EqMode.bisim` witness

D3 settled `Bisimulation` typeclass as the witness shape; the
typeclass itself lands in `L4YAML/Algebra/Equivalence.lean` (Phase 2
§3). Until then, `EqMode.bisim` carries no payload at the type
level, and the parser refuses `bisim` mode if the typeclass is not
in scope at the call site.
-/

namespace L4YAML.Config

/-- Cycle-equality discipline for the `≈` relation on `RepGraph`
    (Algebra Item 3). Threaded through `compose` and `construct`. -/
inductive EqMode where
  /-- Default: error on cycle. -/
  | strict
  /-- Cycles compare by anchor name. -/
  | identity
  /-- Terminate equality testing at depth `n`. -/
  | depthBounded (n : Nat)
  /-- Requires a client-supplied `Bisimulation` witness (D3). -/
  | bisim
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Policy for duplicate keys encountered during composition.
    Threaded through `compose`. -/
inductive DuplicateKeyPolicy where
  /-- Default: parse error on duplicate (libyaml semantics). -/
  | error
  /-- Keep the first occurrence; silently drop later ones. -/
  | first
  /-- Keep the last occurrence (Python `yaml` default). -/
  | last
  /-- Merge values via the supplied combinator.
      The argument is left abstract (`α → α → α`) at this layer; the
      concrete instantiation `YamlValue → YamlValue → YamlValue`
      lands when the indexed `RepGraph` API is wired up in Phase 4. -/
  | merge
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Bundled load-time configuration. The default value gives
    spec-strict behaviour (error on cycle, error on duplicate key).

    Initiative 4 design note: this is the `LoadConfig` referenced
    throughout Blueprint 08. It is intentionally minimal at this
    phase — fields are added only when a downstream stage needs them
    (Guardrail 2: do not strengthen ahead of consumers). -/
structure LoadConfig where
  eqMode             : EqMode             := .strict
  duplicateKeyPolicy : DuplicateKeyPolicy := .error
  deriving Inhabited

end L4YAML.Config
