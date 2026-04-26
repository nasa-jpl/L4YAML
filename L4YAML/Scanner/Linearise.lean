/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State

/-!
# Linearisation: append-only `(tokens, pendingKeys)` → flat token stream

Defines the one-shot pass invoked by `scanFiltered` (Initiative 3 /
Path C) that splices resolved `pendingKeys` entries into the linear
token stream at their `insertBeforeIdx` positions.  Replaces the
legacy in-place `Array.setIfInBounds` placeholder rewrites.

Introduced in **Phase J.1**: types, function body, and property
*statements* land here; the proofs are sorry'd until **Phase J.3**.

See `Blueprint/07-initiative-3-append-only.md` for the algorithm
design and the `{a: [1, 2], b: c}` worked example.
-/

namespace L4YAML.Scanner

open L4YAML

/-! ## Linearisation algorithm -/

/-- Expand a `PendingKeyEntry` into the token sequence linearisation
    should splice.  Unresolved entries vanish; resolved entries either
    contribute a single `.key` token (`keyOnly`) or the two-token
    sequence `[.blockMappingStart, .key]` (`blockMappingStartAndKey`). -/
def expandKind (e : PendingKeyEntry) : Array (Positioned YamlToken) :=
  match e.kind with
  | .unresolved => #[]
  | .keyOnly => #[⟨e.pos, .key, e.pos⟩]
  | .blockMappingStartAndKey =>
      #[⟨e.pos, .blockMappingStart, e.pos⟩, ⟨e.pos, .key, e.pos⟩]

/-- Tail-recursive worker for `linearise`.

    Walks `tokens[k..]` and `pendingKeys[p..]` simultaneously,
    appending each splice/copy to `acc`.

    Loop invariant (informal): when `go k p acc` is called, `acc` is
    the linearised prefix corresponding to `tokens[0..k]` interleaved
    with `expandKind pendingKeys[j]` for every `j < p`.

    Termination: the lex-pair `(tokens.size - k, pendingKeys.size - p)`
    decreases at every recursive call (sum decreases by 1). -/
def linearise.go
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry)
    (k p : Nat)
    (acc : Array (Positioned YamlToken))
    : Array (Positioned YamlToken) :=
  if hp : p < pendingKeys.size then
    let e := pendingKeys[p]
    if e.insertBeforeIdx ≤ k then
      linearise.go tokens pendingKeys k (p + 1) (acc ++ expandKind e)
    else if hk : k < tokens.size then
      linearise.go tokens pendingKeys (k + 1) p (acc.push tokens[k])
    else
      -- All real tokens emitted but a pending entry wants to splice
      -- after the end; flush it at the tail.
      linearise.go tokens pendingKeys k (p + 1) (acc ++ expandKind e)
  else if hk : k < tokens.size then
    linearise.go tokens pendingKeys (k + 1) p (acc.push tokens[k])
  else
    acc
termination_by (tokens.size - k) + (pendingKeys.size - p)

/-- One-shot linearisation pass over a `(tokens, pendingKeys)` pair.

    Walks `tokens` from index 0; before emitting `tokens[k]`, splices
    every `pendingKeys[p]` with `insertBeforeIdx ≤ k`.  Save-time
    monotonicity (each `saveSimpleKey` runs after at least one new
    token is appended) makes the splice index sequence strictly
    increasing, so the splices fire in order without scanning ahead.

    Resolution kinds drive the per-entry splice:
    * `.unresolved` → vanishes (placeholder dropped at filter time)
    * `.keyOnly` → splices `[.key]`
    * `.blockMappingStartAndKey` → splices `[.blockMappingStart, .key]`

    Replaces the legacy `tokens.filter (· != .placeholder)` step in
    `scanFiltered`. -/
def linearise (tokens : Array (Positioned YamlToken))
              (pendingKeys : Array PendingKeyEntry)
              : Array (Positioned YamlToken) :=
  linearise.go tokens pendingKeys 0 0 #[]

/-! ## Basic properties (J.1 statements; J.3 proofs)

These three theorems pin down the *shape* of `linearise` for downstream
use; their proofs are deferred to J.3 alongside the rest of the
scanner-proof corpus migration.  Each statement is independently
useful in scanner reasoning even before its proof is discharged: the
J.2 migration plugs `linearise` into `scanFiltered`'s seam and treats
these as black-box lemmas.
-/

/-- **Append-monotonicity** (the headline property of Path C).

    Pushing a new token to `tokens` extends `linearise`'s output
    rightward — the existing prefix is preserved, only a tail is
    appended.  This is the "filter monotonicity" property the legacy
    `setIfInBounds` model could not deliver: under the legacy scheme
    the same token push could trigger a placeholder rewrite that
    *changed* an earlier output position.

    The hypothesis `h` says every pending entry's `insertBeforeIdx` is
    at most `tokens.size` — i.e. all current pendings target a slot
    inside (or at the tail of) the existing token array.  Save-time
    monotonicity guarantees this throughout scanning. -/
theorem linearise_append_token
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry)
    (t : Positioned YamlToken)
    (h : ∀ e ∈ pendingKeys, e.insertBeforeIdx ≤ tokens.size) :
    ∃ tail, linearise (tokens.push t) pendingKeys
              = linearise tokens pendingKeys ++ tail := by
  sorry

/-- **Unresolved-key invariance**: pushing an unresolved pending key is
    a no-op for the linearised output.  Equivalent to "placeholders
    don't appear in the user-facing token stream" in the legacy model,
    but established constructively here (no filter pass needed). -/
theorem linearise_append_unresolved
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry)
    (e : PendingKeyEntry) (he : e.kind = .unresolved) :
    linearise tokens (pendingKeys.push e) = linearise tokens pendingKeys := by
  sorry

/-- **Output-size accounting**: linearise's output is exactly the
    original tokens plus the total expansion of all pending entries.
    Unresolved entries contribute zero, `keyOnly` contributes one,
    `blockMappingStartAndKey` contributes two — matching the legacy
    `placeholder` slot-reservation count. -/
theorem linearise_resolved
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry) :
    (linearise tokens pendingKeys).size
      = tokens.size + pendingKeys.foldl (fun n e => n + (expandKind e).size) 0 := by
  sorry

end L4YAML.Scanner
