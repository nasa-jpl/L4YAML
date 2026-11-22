module

public import L4YAML.Scanner.Scanner

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # §7.1 [104]: an alias node ends its node (item 9h) — the peel

`scanNextToken_dispatchContent`'s `*` arm now runs `validateAliasClose` on the
state the alias scan produced (see `L4YAML/Scanner/Scanner.lean`, the §7.1 [104]
section).  `validateAliasClose` is a pure *check*: it returns `Unit`, so the arm
still yields exactly the state `scanAnchorOrAlias` produced.

Every dispatcher-level lemma that walks the `*` arm — offset monotonicity,
token growth, prefix/flow-level/simple-key preservation, `ScanInv` — is stated
about `scanAnchorOrAlias s false = .ok s'` and is unaffected by the check.  This
file supplies the one step that gets them back there, so each of those proofs
peels the new validation in a single application instead of re-deriving it.

**Why the check is a bind and not a third disjunct of the arm's existing `if`.**
It could have been the latter: `anchorNameEnd s` already gives the post-name
state, so the whole test is a function of `s` alone, and folding it into the
guard the way item 9g folded its test into the `?` arm's condition would have
cost *zero* proof sites.  What that buys, though, is the guard's error —
`invalidNodeProperties` at the `*` — for an input whose properties are perfectly
well formed.  The faithful error is `trailingContent` at the offending
character, which is what the quoted-scalar sibling reports for `k: "v" [b]`, and
what the indexed twin reports.  So the cost here is not the test; it is the
diagnostic (cf. Reflection 617: a guard's price is its discharge, and the
discharge you owe depends on the shape you ship, not on what you test).
-/

namespace L4YAML.Scanner

/-- **Item 9h peel.**  If the `*` arm succeeded, so did the alias scan itself,
    with the same resulting state: `validateAliasClose` cannot change it. -/
lemma aliasArm_scan_ok {s s' : ScannerState}
    (h : (do let v ← scanAnchorOrAlias s false; validateAliasClose v; pure v) = .ok s') :
    scanAnchorOrAlias s false = .ok s' := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · rename_i v hv
    split at h
    · exact absurd h (by simp)
    · rw [hv, Except.ok.inj h]

end L4YAML.Scanner

end Blanket
