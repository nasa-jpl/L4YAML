# BRIDGING.md — Grammar Specification Gap Analysis

## Problem Statement

`Grammar.lean` defines a formal YAML 1.2.2 specification with 19 definitions.
The doc-verification-bridge analysis found **0 theorems** about 13 of them.
The existing proof suite (33 files under `Lean4Yaml/Proofs/`) proves properties
about `NodeToValue`, `toYamlValue`, `stripAnnotations`, and `Grammable`, but
leaves the character-level predicates, indentation, token stream, and top-level
structures entirely unconnected to the parser implementation.

This document catalogs each gap and proposes the theorems needed to bridge
the Grammar specification to the implementation.

---

## Architecture Overview

The intended proof architecture is:

```
String ──[scan]──▸ ValidTokenStream ──[parseStream]──▸ ∃ ValidNode ──[NodeToValue]──▸ YamlValue
                                                            │
                                                   Grammar.ValidYaml
```

What actually exists:

```
String ──[scan]──▸ tokens ──[parseStream]──▸ docs ──[compose]──▸ final docs
                     │                         │
               (no contract)           (Grammable ASSUMED)
                                               │
                                    EndToEndCorrectness.ValidYaml
                                    (pipeline existence only —
                                     no Grammar.ValidYaml connection)
```

### Two `ValidYaml` Definitions (THE CENTRAL PROBLEM)

| Definition | Location | Type | Status |
|---|---|---|---|
| `Grammar.ValidYaml` | Grammar.lean:541–548 | `structure` with `input`, `value`, `grammar : ValidNode`, `corresponds : NodeToValue grammar value` | **Dead** — no theorem constructs or consumes it from parser output |
| `EndToEndCorrectness.ValidYaml` | EndToEndCorrectness.lean:93 | `def ... : Prop` — `∃ filtered_tokens raw_docs, scanFiltered = ok ∧ parseStream = ok ∧ docs = raw_docs.map compose` | **Tautological** — `parse_sound`/`parse_complete` just decompose/recompose the pipeline |

**No theorem connects these two definitions.** The Grammar-level `ValidYaml` bundles
a `ValidNode` witness and `NodeToValue` correspondence, while the E2E `ValidYaml` only
asserts pipeline success. The entire Grammar specification is therefore disconnected
from verified properties.

---

## Gap Inventory

### Gap 0: The `h_grammable` Hypothesis (BLOCKING)

**Severity: CRITICAL — blocks all downstream Grammar connections**

`ParserCorrectness.lean` has two theorems:

```lean
theorem parseStream_values_have_witnesses
    (h_grammable : ∀ doc ∈ docs.toList, Grammable (doc.compose.value))
    ...

theorem parseStream_respects_grammar
    (h_grammable : ∀ doc ∈ docs.toList, Grammable (doc.compose.value))
    ...
```

Both **assume** `h_grammable` — that parser output is `Grammable` — but this is
never proven. `Grammable v` requires:
- No `alias` nodes (after composition — likely holds)
- Every plain scalar satisfies `validPlainFirst`, `noColonSpace`, `noSpaceHash`

This is ultimately a **scanner obligation**: the scanner must emit tokens whose
content satisfies these character predicates. Until this is proven, the Grammable
assumption is an axiom-in-disguise.

**Required theorems:**

```lean
-- Scanner-level: tokens satisfy character constraints
theorem scan_plain_scalar_valid (input : String) (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens)
    (i : Fin tokens.size) (s : Scalar)
    (hs : tokens[i].val = .scalar s) (hplain : s.style = .plain)
    (hne : s.content.length > 0) :
    validPlainFirst s.content ∧ noColonSpace s.content ∧ noSpaceHash s.content

-- Parser-level: composed output is Grammable
theorem parseStream_output_grammable (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h : TokenParser.parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, Grammable (doc.compose.value)
```

**Proof strategy:** The scanner already enforces these constraints operationally
(it reads characters matching `ns-plain-first` and `ns-plain-char`). The proof
must show the scanner's character-matching logic implies the formal predicates.
This likely requires a scanner invariant that tracks character constraints through
the scanning state machine.

---

### Gap 1: `validPlainFirst`

**Severity: CRITICAL**

**Definition** (Grammar.lean:296–300):
```lean
def validPlainFirst (content : String) : Prop :=
  match content.toList with
  | c :: _ => canStartPlainScalar c
  | [] => True
```

**Current state:** Used as a proof obligation in `ValidNode.plainScalarBlock` and
`ValidNode.plainScalarFlow`. The `Grammable` predicate requires it for plain scalars.
`scalar_has_witness` in `ParserSoundness.lean` takes it as a hypothesis. No theorem
proves the scanner produces tokens satisfying it.

**Has `Decidable` instance:** Yes.

**Required theorems:**

```lean
-- Scanner enforces validPlainFirst on emitted plain scalar tokens
theorem scan_enforces_validPlainFirst (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    ∀ i (hi : i < tokens.size),
      ∀ s : Scalar, tokens[i].val = .scalar s →
        s.style = .plain → s.content.length > 0 →
        validPlainFirst s.content

-- Characterization: validPlainFirst ↔ canStartPlainScalar on first char
theorem validPlainFirst_iff (content : String) (hne : content.length > 0) :
    validPlainFirst content ↔ canStartPlainScalar (content.toList.head (by ...))
```

---

### Gap 2: `noColonSpace`

**Severity: CRITICAL**

**Definition** (Grammar.lean:313–314):
```lean
def noColonSpace (content : String) : Prop :=
  ¬ ∃ i, content.toList[i]? = some ':' ∧ content.toList[i + 1]? = some ' '
```

**Current state:** Used in `ValidNode.plainScalarBlock/Flow` and `Grammable`.
No theorem proves the scanner enforces it. ✅ `Decidable` instance added (Phase A)
via `hasAdjacentChars` helper.

**Required theorems:**

```lean
-- Scanner enforcement (subsumed by Gap 0's scan_plain_scalar_valid)
```

---

### Gap 3: `noSpaceHash`

**Severity: CRITICAL**

**Definition** (Grammar.lean:322–323):
```lean
def noSpaceHash (content : String) : Prop :=
  ¬ ∃ i, content.toList[i]? = some ' ' ∧ content.toList[i + 1]? = some '#'
```

**Current state:** Same as `noColonSpace` — used in `ValidNode` and `Grammable`,
never proven enforced. ✅ `Decidable` instance added (Phase A) via `hasAdjacentChars`.

**Required theorems:**

```lean
-- Scanner enforcement (subsumed by Gap 0's scan_plain_scalar_valid)
```

---

### Gap 4: `noFlowIndicators`

**Severity: CRITICAL**

**Definition** (Grammar.lean:331–332):
```lean
def noFlowIndicators (content : String) : Prop :=
  ∀ c ∈ content.toList, ¬isFlowIndicator c
```

**Current state:** Used only in `ValidNode.plainScalarFlow`. Not included in
`Grammable` (which does not distinguish block/flow context). No theorem proves
the scanner enforces it in flow context.

✅ `Decidable` instance added (Phase A) via `List.decidableBAll`.

**Required theorems:**

```lean
-- Scanner enforcement in flow context
theorem scan_flow_plain_no_indicators (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens)
    (i : Fin tokens.size) (s : Scalar)
    (hs : tokens[i].val = .scalar s)
    (hplain : s.style = .plain)
    (hflow : -- token is in flow context --) :
    noFlowIndicators s.content
```

**Note:** The `Grammable` predicate currently does not track flow context.
Either `Grammable` needs a flow-context variant, or `noFlowIndicators` must be
proven separately when constructing `ValidNode.plainScalarFlow` from parser output.

---

### Gap 5: `canStartPlainScalar`

**Severity: HIGH** (used transitively via `validPlainFirst`)

**Definition** (Grammar.lean:115–123):
```lean
def canStartPlainScalar (c : Char) : Prop :=
  isPrintable c ∧ ¬ isWhiteSpace c ∧ ¬ isLineBreak c
  ∧ c ∉ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
         '\'', '"', '%', '@', '`']
```

**Current state:** Has a `Decidable` instance (Grammar.lean:124). Referenced
indirectly through `validPlainFirst`. No direct theorems characterize it.

**Required theorems:**

```lean
-- Relationship to YAML spec character classes
theorem canStartPlainScalar_iff (c : Char) :
    canStartPlainScalar c ↔
    isPrintable c ∧ ¬isWhiteSpace c ∧ ¬isLineBreak c ∧ ¬isIndicator c

-- Scanner uses this predicate at plain-scalar entry points
theorem scan_plain_entry_char (c : Char)
    (h : -- scanner enters plain scalar state at char c --) :
    canStartPlainScalar c
```

---

### Gap 6: `IndentedAtLeast` / `Indented` / `decideIndented`

**Severity: HIGH** (block structure correctness depends on indentation)

**Definitions** (Grammar.lean:150–195):
```lean
inductive Indented : Nat → List Char → Prop where
  | zero (cs : List Char) : Indented 0 cs
  | space (n : Nat) (cs : List Char) : Indented n cs → Indented (n + 1) (' ' :: cs)

def IndentedAtLeast (n : Nat) (cs : List Char) : Prop :=
  ∃ m, m ≥ n ∧ Indented m cs
```

**Current state:** Both have `Decidable` instances. `indented_weaken` is proven.
These definitions are used in the `ValidNode` block constructors' intended semantics
(block-seq/block-map carry an `indent` field) but are never referenced in `NodeToValue`
or any proof file.

**Required theorems:**

```lean
-- Scanner emits correct indentation levels
theorem scan_block_indent_correct (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    -- For each blockSeq/blockMap token, the indent field matches
    -- the actual leading spaces in the source line
    sorry

-- Indentation monotonicity for nested blocks
theorem indented_nested {n m : Nat} {cs : List Char}
    (h : Indented m cs) (hlt : n < m) :
    ∃ rest, Indented n rest

-- IndentedAtLeast transitivity
theorem indentedAtLeast_trans {n m : Nat} {cs : List Char}
    (h : IndentedAtLeast m cs) (hle : n ≤ m) :
    IndentedAtLeast n cs
```

---

### Gap 7: `ValidTokenStream`

**Severity: HIGH** (scanner/parser bridge contract)

**Definition** (Grammar.lean:436–451):
```lean
structure ValidTokenStream where
  input : String
  tokens : Array (Positioned YamlToken)
  sizeGe2 : tokens.size ≥ 2
  firstIsStreamStart : (tokens[0]'...).val = .streamStart
  lastIsStreamEnd : (tokens[tokens.size - 1]'...).val = .streamEnd
  positionsOrdered : ∀ (i j : Fin tokens.size), i.val < j.val →
    (tokens[i]).pos.offset ≤ (tokens[j]).pos.offset
```

**Current state:** Defined but never used in any theorem. The scanner does
not produce a `ValidTokenStream` — neither `Scanner.scan` nor
`Scanner.scanFiltered` return this type. The comment in Grammar.lean
explicitly says:

> The scanner's correctness theorem (future work) will state:
> `theorem scan_valid (input : String) ... : ValidTokenStream input tokens`

**Required theorems:**

```lean
-- THE scanner correctness theorem
theorem scan_produces_valid_token_stream (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    ValidTokenStream.mk input tokens
      (by sorry) -- sizeGe2
      (by sorry) -- firstIsStreamStart
      (by sorry) -- lastIsStreamEnd
      (by sorry) -- positionsOrdered

-- Parser consumes ValidTokenStream correctly
theorem parseStream_consumes_valid_tokens
    (vts : ValidTokenStream)
    (h : TokenParser.parseStream vts.tokens = .ok docs) :
    -- parseStream succeeds on any ValidTokenStream
    True  -- exact obligation TBD
```

---

### Gap 8: `ValidYaml` (Grammar-level)

**Severity: CRITICAL** (the entire specification target)

**Definition** (Grammar.lean:541–548):
```lean
structure ValidYaml where
  input : String
  value : YamlValue
  grammar : ValidNode
  corresponds : NodeToValue grammar value
```

**Current state:** `Soundness.lean` has `validYaml_construct` and
`validYaml_value_eq_toYamlValue` for construction/decomposition, but
these are about the structure itself — not about connecting parser output
to it. No theorem states:

```
parse input = .ok docs → Grammar.ValidYaml input docs[i].value
```

**Required theorem (the main soundness goal):**

```lean
theorem parse_produces_valid_yaml (input : String)
    (docs : Array YamlDocument)
    (h : TokenParser.parseYaml input = .ok docs) :
    ∀ i : Fin docs.size,
      ∃ vy : Grammar.ValidYaml,
        vy.input = input ∧
        stripAnnotations vy.value = stripAnnotations docs[i].compose.value
```

**Dependencies:** This requires Gap 0 (`h_grammable` discharge) which requires
Gaps 1–4 (character predicates). It is the capstone theorem.

---

### Gap 9: `ValidStream`

**Severity: LOW (dead code)**

**Definition** (Grammar.lean:409–413):
```lean
structure ValidStream where
  documents : List ValidDocument
  nonempty : documents.length > 0
```

**Current state:** Never referenced outside Grammar.lean. `ValidDocument` is
also unreferenced.

**Recommendation:** Either:
1. Remove as dead code, or
2. Connect to `parseStream` output by proving multi-document stream validity

If kept, the required theorem would be:

```lean
theorem parseStream_produces_valid_stream
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h : TokenParser.parseStream tokens = .ok docs)
    (hne : docs.size > 0) :
    ∃ vs : ValidStream, vs.documents.length = docs.size
```

---

### Gap 10: `isContentChar`

**Severity: LOW** (block scalar header parsing)

**Definition** (Grammar.lean:758–759):
```lean
def isContentChar (c : Char) : Prop :=
  isBlockScalarHeaderChar c = false
```

**Current state:** Has `Decidable` instance. Used to classify characters during
block scalar header parsing. The block scalar header proofs
(`BlockScalarHeader.lean`, `BlockScalarHeaderSpec.lean`) likely use this — needs
verification.

**Required theorems:**

```lean
-- isContentChar is the complement of isBlockScalarHeaderChar
theorem isContentChar_iff_not_header (c : Char) :
    isContentChar c ↔ ¬(isBlockScalarHeaderChar c = true)

-- Block scalar header parser stops at content chars
theorem blockScalarHeader_stops_at_content (cs : List Char)
    (c : Char) (rest : List Char)
    (h : isContentChar c) :
    -- header parser does not consume c
    sorry
```

---

### Gap 11: `isNamedEscapeChar`

**Severity: LOW** (double-quoted scalar parsing)

**Definition** (Grammar.lean:278–279):
```lean
def isNamedEscapeChar (c : Char) : Prop :=
  resolveNamedEscape c ≠ none
```

**Current state:** Has `Decidable` instance. Used to validate escape sequences
in double-quoted scalars. No theorems characterize the escape resolution.

**Required theorems:**

```lean
-- Named escape chars resolve to exactly one output char
theorem isNamedEscapeChar_resolves (c : Char) (h : isNamedEscapeChar c) :
    ∃ out : Char, resolveNamedEscape c = some out

-- Exhaustive characterization
theorem isNamedEscapeChar_chars :
    isNamedEscapeChar c ↔ c ∈ ['0', 'a', 'b', 't', '\t', 'n', 'v', 'f',
                                'r', 'e', ' ', '"', '/', '\\', 'N', '_']
```

---

### Gap 12: `validHeaderLength`

**Severity: LOW** (block scalar header constraint)

**Definition** (Grammar.lean:747–748):
```lean
def validHeaderLength (cs : List Char) : Prop :=
  (extractHeaderChars cs).1.length ≤ 2
```

**Current state:** Has `Decidable` instance. Used to bound the header indicator
count. Likely referenced in block scalar header proofs.

**Required theorems:**

```lean
-- At most one chomp + one indent indicator
theorem validHeaderLength_spec (cs : List Char) :
    validHeaderLength cs ↔ (extractHeaderChars cs).1.length ≤ 2

-- extractHeaderChars terminates within 2 chars for valid input
theorem extractHeaderChars_bounded (cs : List Char)
    (h : validHeaderLength cs) :
    ∀ c ∈ (extractHeaderChars cs).1, isBlockScalarHeaderChar c = true
```

---

## Priority Plan

### Phase A: Decidable Instances ✅ COMPLETE

Added missing `Decidable` instances for:
1. ✅ `noColonSpace` — via `hasAdjacentChars ':' ' '` boolean helper + iff proof
2. ✅ `noSpaceHash` — via `hasAdjacentChars ' ' '#'` boolean helper + iff proof
3. ✅ `noFlowIndicators` — via `List.decidableBAll`

All added to `Grammar.lean`. Build: 211/211, tests: 869/869, 0 sorry, 0 axioms.

#### Phase A Reflections

**Approach chosen:** Instead of trying to get `Decidable` for the negated
existential `¬ ∃ i, ...` directly, we introduced a boolean scanning function
`hasAdjacentChars` and proved the bidirectional `hasAdjacentChars_iff` theorem
that connects it to the `∃ i, cs[i]? = ...` proposition. The `Decidable`
instance then pattern-matches on the boolean result.

**Unexpected challenges:**
- `beq_iff_eq.mp`/`.mpr` produces `(c == a) = true` not `c = a`. Using `subst`
  after `simp` destructures the BEq hypothesis cleanly. First attempt failed
  because `simp [beq_iff_eq.mp h]` doesn't substitute into the goal — `subst`
  is required.
- `push_neg` is Mathlib-only. The `isFalse` branch uses
  `absurd ((iff).mp h) hn` instead.
- `List.getElem?` is not a valid identifier in Lean 4.28 (it's notation, not
  a def). Simplification lemmas `List.getElem?_cons_zero` and
  `List.getElem?_cons_succ` work with bare `simp`.

**Simplifications:**
- `noFlowIndicators` was trivial: `List.decidableBAll` from core Lean handles
  `∀ c ∈ list, ¬P c` directly, given `Decidable (isFlowIndicator c)` which
  already existed.
- The `hasAdjacentChars` helper is reusable — it works for any two-character
  adjacency pattern, making `noColonSpace` and `noSpaceHash` share the same
  proof infrastructure.

**Idiom:** For `¬ ∃ i, P i` decidability without Mathlib, the pattern is:
```lean
match h : booleanCheck args with
| false => .isTrue (fun hex => absurd (iff.mpr hex) (by simp [h]))
| true  => .isFalse (fun hn => absurd (iff.mp h) hn)
```

### Phase B: Scanner Character Predicate Enforcement (CRITICAL PATH)

Prove that the scanner produces tokens satisfying `validPlainFirst`,
`noColonSpace`, `noSpaceHash`, and (in flow context) `noFlowIndicators`.

This requires:
1. Identifying the scanner functions that emit plain scalar tokens
2. Tracing character consumption through the scanner state machine
3. Showing the consumed characters satisfy the Grammar predicates

**Theorem:** `scan_plain_scalar_valid` (Gap 0)

**Estimated difficulty:** High. The scanner is a complex state machine.
May require introducing a scanner invariant (analogous to `ScanInv`).

### Phase C: Discharge `h_grammable` (CRITICAL PATH)

With Phase B's scanner theorem, prove:

```lean
theorem parseStream_output_grammable : ...
    ∀ doc ∈ docs.toList, Grammable (doc.compose.value)
```

This also requires showing that `compose` (alias resolution) preserves
`Grammable` — specifically that resolved aliases are still alias-free
and plain scalar constraints are preserved.

**Estimated difficulty:** Medium. Requires showing `compose` preserves
`Grammable` and that `parseStream` propagates scanner token properties.

### Phase D: Bridge `Grammar.ValidYaml` to Parser Output (CAPSTONE)

With `h_grammable` discharged, the existing `parseStream_respects_grammar`
gives `∃ ValidNode` witnesses. Combine with `NodeToValue` (already proven
via `Soundness.lean`) to construct `Grammar.ValidYaml`:

```lean
theorem parse_produces_valid_yaml : ...
    ∀ i : Fin docs.size, ∃ vy : Grammar.ValidYaml, ...
```

**Estimated difficulty:** Medium. The machinery exists; this is composition.

### Phase E: ValidTokenStream Contract (SUPPORTING)

Prove `scan_produces_valid_token_stream` so the scanner/parser boundary
has a typed contract. This is architecturally important but not blocking
the critical path (the existing proofs bypass `ValidTokenStream`).

**Estimated difficulty:** Medium. Requires scanner internals analysis.

### Phase F: Dead Code & Low-Priority Gaps

1. **ValidStream / ValidDocument** — decide keep-or-remove
2. **isContentChar** — verify block scalar header proofs reference it
3. **isNamedEscapeChar** — characterization theorems
4. **validHeaderLength** — bounded extraction theorems
5. **IndentedAtLeast** — scanner indent correctness

---

## Dependency Graph

```
Phase A (Decidable instances)
    │
    ▼
Phase B (Scanner character predicates)  ──▸  Phase E (ValidTokenStream)
    │
    ▼
Phase C (Discharge h_grammable)
    │
    ▼
Phase D (Grammar.ValidYaml bridge)  ◀── capstone
    │
    ▼
Phase F (cleanup & low-priority)
```

## Summary Table

| Definition | YAML Spec | Severity | Has Decidable | Has Theorems | Blocking |
|---|---|---|---|---|---|
| `validPlainFirst` | §7.3.3 [123] | CRITICAL | ✅ | ❌ | Phase B |
| `noColonSpace` | §7.3.3 [127] | CRITICAL | ✅ (Phase A) | ❌ | Phase B |
| `noSpaceHash` | §7.3.3 [127] | CRITICAL | ✅ (Phase A) | ❌ | Phase B |
| `noFlowIndicators` | §7.3.3 [126] | CRITICAL | ✅ (Phase A) | ❌ | Phase B |
| `canStartPlainScalar` | §7.3.3 [123] | HIGH | ✅ | ❌ | Phase B |
| `IndentedAtLeast` | §6.1 [65] | HIGH | ✅ | `indented_weaken` only | Phase F |
| `Indented` / `decideIndented` | §6.1 [63] | HIGH | ✅ | `indented_weaken` only | Phase F |
| `ValidTokenStream` | §3.1 | HIGH | n/a | ❌ | Phase E |
| `ValidYaml` (Grammar) | §9 / top | CRITICAL | n/a | construction only | Phase D |
| `ValidStream` | §9 [205] | LOW | n/a | ❌ dead code | Phase F |
| `isContentChar` | §8.1.1 [158] | LOW | ✅ | ❌ | Phase F |
| `isNamedEscapeChar` | §5.7 | LOW | ✅ | ❌ | Phase F |
| `validHeaderLength` | §8.1.1 [158] | LOW | ✅ | ❌ | Phase F |
