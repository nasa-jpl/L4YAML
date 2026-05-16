/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.IndexedDispatch
import L4YAML.Scanner.IndexedPresenter

/-! # `IndexedRoundtrip` — Phase 3 Step 5c corpus roundtrip theorem (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6).

## Statement

For each `input` in the fixed corpus, scanning the input succeeds
and re-presenting the resulting token stream recovers the original
source:

```
scanIx input = .ok ts ∧ present ts = input
```

The two conjuncts together imply the roundtrip
`scanIx (present ts) = .ok ts` (since `present ts = input`).

## Corpus design

The corpus is restricted to inputs whose token streams cover every
byte of `input` with no inter-token whitespace gaps — `present`'s
hybrid render (see `L4YAML/Scanner/IndexedPresenter.lean`)
reconstructs `input` exactly only when (i) every indicator token
sits at the position of its literal character, with no surrounding
spaces, and (ii) every implicit `key` / `value` token is purely
virtual (no explicit `?`/`:` in source). The current corpus is:

- `""` — empty stream (only the virtual `streamStart` / `streamEnd`)
- `"x"` — single plain scalar at root
- `"abc"` — multi-character plain scalar at root
- `"hello"` — five-character plain scalar at root
- `"[]"` — empty flow sequence
- `"{}"` — empty flow mapping
- `"[x]"` — flow sequence with a single plain entry
- `"[x,y]"` — flow sequence with two plain entries
- `"[a,b,c]"` — flow sequence with three plain entries
- `"[a,b,c,d]"` — flow sequence with four plain entries
- `"[[]]"` — nested empty flow sequence
- `"[{}]"` — flow sequence containing an empty flow mapping
- `"{a}"` — single-key flow mapping (implicit key, no value)
- `"{a,b}"` — two-key flow mapping
- `"[a,[b,c]]"` — flow sequence with a nested flow sequence
- `"[{a},b]"` — flow sequence with a nested flow mapping
- `"{a,{b}}"` — nested flow mappings
- `"[[],[]]"` — flow sequence of empty flow sequences
- `"{[]}"` — flow mapping containing an empty flow sequence

Inputs that include inter-token whitespace (`"x: y"`, `"{a: 1}"`,
multi-line documents, comments, explicit `?`/`:` keys, anchors,
tags, quoted scalars, block scalars, etc.) do *not* roundtrip
with the current presenter design; extending the corpus to cover
them requires a richer presenter that interpolates gaps from the
input type-parameter and recovers explicit-vs-implicit key/value
distinctions, deferred to a follow-up step (the full
bidirectional `compose ∘ parse ∘ present ∘ serialize` roundtrip
is Phase 4+).

## Proof discipline

Each roundtrip theorem closes by `native_decide`: both `scanIx
input` (a fully computable function with fuel) and `present ts` (a
fold) reduce on a fixed `String` corpus entry, so the goal
`match scanIx input with | .ok ts => present ts = input | .error _ => False`
is a `Decidable` proposition that `native_decide` evaluates by
compiling to native code. No symbolic reasoning is required — the
roundtrip is *exhibited*, not derived, which is exactly the role of
a staging corpus theorem (Step 5c precedes the bidirectional
correctness obligations of Phase 4).
-/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.Indexed L4YAML.Scanner.Indexed.ScannerStateIx

/-- A single roundtrip test: scanning succeeds and re-presenting
    the resulting stream recovers the input. Bundling both
    conjuncts into a `Bool`-valued check makes the corpus suite
    uniform — each entry is one `native_decide` on a `= true`
    equation, which sidesteps the dependent-`Prop` instance plumbing
    that a `match`-shaped predicate would need. -/
def roundtripOk (input : String) : Bool :=
  match scanIx input with
  | .ok ts => present ts == input
  | .error _ => false

/-! ## Corpus

Each entry below exhibits the roundtrip for one fixed input by
`native_decide` — both `scanIx input` and `present ts` are
fully computable functions, so the goal reduces to a concrete
`Bool` equation that the kernel compiles and evaluates. -/

theorem roundtrip_empty : roundtripOk "" = true := by native_decide

theorem roundtrip_plain_x : roundtripOk "x" = true := by native_decide

theorem roundtrip_plain_abc : roundtripOk "abc" = true := by native_decide

theorem roundtrip_plain_hello : roundtripOk "hello" = true := by native_decide

theorem roundtrip_flow_seq_empty : roundtripOk "[]" = true := by native_decide

theorem roundtrip_flow_map_empty : roundtripOk "{}" = true := by native_decide

theorem roundtrip_flow_seq_one : roundtripOk "[x]" = true := by native_decide

theorem roundtrip_flow_seq_two : roundtripOk "[x,y]" = true := by native_decide

theorem roundtrip_flow_seq_three : roundtripOk "[a,b,c]" = true := by native_decide

theorem roundtrip_flow_seq_four : roundtripOk "[a,b,c,d]" = true := by native_decide

theorem roundtrip_flow_seq_nested_empty : roundtripOk "[[]]" = true := by native_decide

theorem roundtrip_flow_seq_of_map : roundtripOk "[{}]" = true := by native_decide

theorem roundtrip_flow_map_one : roundtripOk "{a}" = true := by native_decide

theorem roundtrip_flow_map_two : roundtripOk "{a,b}" = true := by native_decide

theorem roundtrip_flow_seq_mixed_a : roundtripOk "[a,[b,c]]" = true := by native_decide

theorem roundtrip_flow_seq_mixed_b : roundtripOk "[{a},b]" = true := by native_decide

theorem roundtrip_flow_map_mixed : roundtripOk "{a,{b}}" = true := by native_decide

theorem roundtrip_flow_seq_of_seq : roundtripOk "[[],[]]" = true := by native_decide

theorem roundtrip_flow_map_of_seq : roundtripOk "{[]}" = true := by native_decide

/-! ## Closed-form consequence

From `roundtripOk input = true`, the `scanIx (present ts) = .ok ts`
formulation in the Blueprint follows directly: `present ts = input`
makes `scanIx (present ts)` reduce to `scanIx input`, which is
already known to equal `.ok ts` by the `match`. -/

theorem scanIx_present_of_roundtripOk (input : String)
    (h : roundtripOk input = true) :
    ∃ ts : Indexed.TokenStream input,
      scanIx input = .ok ts ∧ present ts = input := by
  unfold roundtripOk at h
  cases hSc : scanIx input with
  | error e => rw [hSc] at h; cases h
  | ok ts =>
    rw [hSc] at h
    refine ⟨ts, rfl, ?_⟩
    exact (beq_iff_eq).1 h

end L4YAML.Scanner.Indexed
