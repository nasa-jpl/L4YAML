/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Token.Token

/-!
# Parser Fuel

Initial fuel computation for the recursive-descent parser.

Split from `Parser/TokenParser.lean` during Blueprint Initiative 1
Phase 3.  See `Blueprint/03-code-organization.md`.

## Fuel-based termination (P10.8a–b)

All 14 functions in the mutual block in `TokenParser.lean` take a
`fuel : Nat` parameter that decreases by 1 at each function entry
(via `match fuel with | fuel + 1 => ...`).  Lean 4 infers termination
automatically from the structural decrease on `fuel`, so no explicit
`termination_by` annotations are needed.

`initialFuel` sets the bound passed to `parseNode` from `parseDocument`.
The formula `4 * tokens.size + 4` reflects the worst-case observation
that each token generates at most ~4 mutual-function entries (dispatch
+ collection + loop + sub-node).  The constant `+ 4` covers the
dispatch wrapper for the very first token (tag/anchor/scalar dispatch
chain).

This file holds only the fuel calculation; the formula appears once in
production code (in `parseDocument`) and once in proofs (capstone fuel
budget reasoning), so factoring it out keeps both call sites in sync.
-/

namespace L4YAML.TokenParser

open L4YAML

/-- Initial fuel for `parseNode` invoked by `parseDocument`.

    Value: `4 * tokens.size + 4`.

    **Why `4 * N + 4`**: each token may trigger at most one collection
    open (`parseBlockSequence`, …), one collection-loop entry
    (`parseBlockSequenceLoop`, …), one node dispatch (`parseNode`),
    and one content dispatch (`parseNodeContent`).  The trailing `+ 4`
    absorbs the leading dispatch chain before the first token is
    consumed.

    Note: `parseDocument` currently inlines the formula
    `4 * ps.tokens.size + 4` rather than calling this helper, so that
    existing proofs in `EmitterScannability` which match on the literal
    can continue to unify without `simp [initialFuel]`.  This def
    therefore exists as the *named* fuel reference for new tooling
    (proofs, audits) that wants to talk about the formula by name. -/
def initialFuel (tokens : Array (Positioned YamlToken)) : Nat :=
  4 * tokens.size + 4

end L4YAML.TokenParser
