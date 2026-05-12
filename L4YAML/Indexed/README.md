# `L4YAML.Indexed` — Indexed type substrate (Initiative 4, Phase 2)

Indexed types parameterised by the source string `input`. The substrate
that Phase 3+ build on:

| File | Type | Indexed by |
|---|---|---|
| `Range.lean` | `Range input` | `input : String` |
| `RepGraph.lean` | `RepGraph input range` | `input : String`, `range : Range input` |
| `TokenStream.lean` | `TokenStream input` | `input : String` |

D1 settled (Blueprint 08):
- (a) `range` is a separate parameter of `RepGraph` (not a field).
- (b) Nested ranges encoded via dependent pair `Σ (r : Range input), RepGraph input r`.
- (c) `AnchorMap input` as separate parameter.

## Phase 2 scope (this directory)

Definitions only — no scanning/parsing semantics, no theorems.
The construction/elimination machinery lands in Phase 3+.
