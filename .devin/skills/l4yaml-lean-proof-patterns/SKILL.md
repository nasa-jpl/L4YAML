---
name: l4yaml-lean-proof-patterns
description: Lean 4.35 + module-system mechanics that have repeatedly cost time in L4YAML proofs — String.Slice returns, BEq on derived enums, rfl vs native_decide pins, meta/public imports, guarded recursion, census-breaking module additions. Use when a proof or test file fails to elaborate for a reason that smells like tooling rather than mathematics.
---

# Lean proof patterns for this repo

Project-specific lessons; the general digest of closed proof episodes is
`Blueprint/08-init4.md` (from `Tests/Reflections/*`).

## Strings

- `String.drop/take/trimAscii` return `String.Slice` in this toolchain; add
  `.toString` or state the lemma over `List Char` and prove the `String`
  wrapper by `simp [String.toList]`-style transport.  Prefer `List Char` for
  anything inductive.
- `rfl` will not unfold `normalizeTag`/`String.startsWith`; pin with
  `native_decide` on the concrete instance, then `rw`.

## Decidable pins and `BEq`

- Derived `BEq` on an enum: `simp` may not reduce `a == b`; add an explicit
  `(by rfl : (A.x == A.y) = false)` pin before simplifying.
- `#guard` for small decidable checks, `native_decide` for big ones; every
  `native_decide` adds `Lean.ofReduceBool` to the axiom profile at that site
  — acceptable, but list it in the census.
- A pin on a `Prop` disjunction is vacuous (proof irrelevance); pin the
  constructed witness or a `Bool` projection of it (§7).

## Case splits and dispatchers

- Dispatcher proofs are arm-by-arm: `match h : dispatch … with` and keep the
  equation `h`; an arm with no live input is a deletion candidate, not a
  `sorry`.
- When a destructuring fails, every construction behind it is unreported —
  fix the destructuring, rebuild, then read the real count.
- Optional conjuncts (`Or.inr`-declinable premises) are how carriers are
  added without breaking the other applications: add the premise as
  `h : P ∨ True`-shaped optional, let the seven other sites decline it, pay
  it at the one site that needs it.

## Module system

- `module` header on every library file; `public import` only what the
  downstream statement mentions; `@[expose] public section` for defs proofs
  unfold across modules.
- Deriving instances via metaprograms: generate syntax/quotations, not
  reparsed strings — private-mangled names break reparsing.
- `meta initialize` + `meta def` for handlers that importers must run;
  tests that `#eval` reflected data need `meta import` alongside `import`.
- Adding a library module moves `FreeSurfaceCensus`/`DropDependents`/
  `ParkBill` closure pins (full build only).

## Schema / serialization (when touching `L4YAML/Schema`)

- Handwritten `FromYaml`/`ToYaml` must list every field; `HashMap` keys built
  by hand go through `ToYaml String`.
- Errors: `.unknownVariant` for a bad scalar value, `.notASequence` /
  `.notAMapping` only for shape mismatch.  Raw `YamlValue` fields need a
  local identity instance.
- `lake run check-serialization-proofs` gates this layer; run it before the
  full build.
