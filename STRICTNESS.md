# Plan: STRICTNESS.md — Formalizing YAML 1.2.2 Surface Syntax

## TL;DR

This document that analyzes the gap between Grammar.lean's output-structure formalization and the input-level surface syntax defined by the 205 YAML 1.2.2 productions. The document explains what's missing, proposes a formalization approach using parameterized inductive predicates over positioned character streams, and shows how this enables proving the acceptance strictness property (`parseYaml s = .ok docs → InYamlLanguage s`).

## Steps

### Phase 1: Document structure and gap analysis

1. **Section 1 — The Verification Asymmetry**: Explain the current soundness-only verification. Grammar.lean captures output structure (ValidNode, ValidTokenStream) but not input acceptance criteria. Reference the README's existing discussion.

2. **Section 2 — What's Already Formalized**: Inventory the ~17 `@[yaml_spec]`-tagged definitions covering productions [1], [22], [23], [26], [31], [33], [61], [63], [65], [123], [126], [158], [200], [204], [205]. CharPredicates.lean covers [1]-[33] character classes. Grammar.lean covers [63], [65] (indentation), [200] (c-forbidden), [61] (escapes), [158] (block scalar headers), [196]/[157] (ValidNode), [204]/[205] (documents/streams). Note that these are all *output-structure* or *character-class* predicates, not *input-language* predicates.

3. **Section 3 — What's Missing**: The 205 productions grouped into 5 layers, with analysis of each layer's formalization status:
   - **Layer 1: Character classes [1]-[40]** — ~90% formalized in CharPredicates.lean
   - **Layer 2: Basic structures [41]-[93]** — Escape sequences ([61] done), comments ([74]-[79] not formalized as input predicates), indentation ([63],[65] done as output predicates), separation ([66]-[70] not formalized), directives ([82]-[93] not formalized)
   - **Layer 3: Flow styles [94]-[157]** — Tag properties ([96]-[100] not formalized), anchor/alias ([101]-[104] not formalized), flow sequences ([134]-[136] not formalized), flow mappings ([137]-[157] not formalized), plain scalars ([123]-[133] partially via CharPredicates)
   - **Layer 4: Block styles [158]-[199]** — Block scalars ([158]-[179] partially via header predicates), block sequences ([180]-[183] not formalized as input predicates), block mappings ([184]-[199] not formalized)
   - **Layer 5: Document/stream [200]-[211]** — c-forbidden ([200] done), document markers ([201]-[205] partially), stream rules ([206]-[211] not formalized)

4. **Section 4 — Why Output Predicates ≠ Input Predicates**: Concrete examples showing the gap:
   - `ValidNode.blockSeq 2 items` says "block sequence at indent 2" but NOT "input has `-` at column 3 followed by content at column ≥ 4"
   - `ValidNode.plainScalarBlock content ...` carries character constraints but NOT "content appeared at position (line, col) with indentation n in block context c"
   - `ValidTokenStream` says tokens are ordered and stream-bounded but NOT "the input characters between token positions are exactly the whitespace/comments that the grammar allows"

### Phase 2: Formalization approach

5. **Section 5 — Positioned Character Streams**: Define the formalization target — predicates over `(String × Nat)` (input string + position offset), not just `List Char`. The YAML grammar is inherently position-sensitive (line, column tracking) so the formalization must carry position.

6. **Section 6 — Parameterized Inductive Predicates**: Propose encoding each YAML production as a Lean inductive `Prop` parameterized by `(n : Nat)` (indent) and `(c : Context)` (block-out/block-in/flow-out/flow-in/block-key/flow-key). Example encodings for representative productions from each layer:
   - [63] `s-indent(n)` → `SIndent n input pos` (already close to `Indented`)  
   - [66] `s-separate-in-line` → `SSeparateInLine input pos pos'`
   - [134] `c-flow-sequence(n,c)` → `CFlowSequence n c input pos pos'`
   - [180] `l+block-sequence(n)` → `LBlockSequence n input pos pos'`
   - [205] `l-yaml-stream` → `LYamlStream input`

7. **Section 7 — Context-Sensitivity**: Explain why YAML is context-sensitive (not CFG) and how the parameterized predicates handle this. The indent parameter `n` threads through the grammar creating indentation-sensitivity. The context parameter `c` determines which characters are legal in plain scalars and whether flow indicators have structural meaning.

8. **Section 8 — The Strictness Theorem**: State the target theorem and show how the formalization enables it:
   ```
   theorem parse_strict : parseYaml s = .ok docs → LYamlStream s
   ```
   Proof strategy: show that each scanner/parser function, when it succeeds, produces output that corresponds to the grammar production it implements. Chain these correspondences through the pipeline.

### Phase 3: Practical considerations

9. **Section 9 — Incremental Strategy**: Propose a bottom-up formalization order:
   - Phase A: Complete Layer 1 (character classes) — mostly done
   - Phase B: Layer 2 (separation, comments, directives) 
   - Phase C: Layer 4 (block structures) — highest strictness-bug density
   - Phase D: Layer 3 (flow structures)
   - Phase E: Layer 5 (document/stream composition)
   Each phase independently useful: even partial formalization catches strictness bugs in the covered subset.

10. **Section 10 — Estimated Scale**: Rough sizing of the formalization effort. ~165 new inductive definitions, ~200 coupling theorems (implementation ↔ spec), ~100 composition lemmas. Compare to existing Grammar.lean (~1000 lines) and CharPredicates.lean (~700 lines).

11. **Section 11 — Alternatives Considered**: Why other approaches are insufficient:
    - Empirical testing only (current v0.2.11 approach): catches bugs but doesn't prove absence
    - Formalizing the scanner state machine directly: ties proofs to implementation, not spec
    - CFG approximation: YAML is context-sensitive, CFG loses indentation constraints

## Relevant files

- [Lean4Yaml/Grammar.lean](lean/lean4-yaml-verified.iterators/Lean4Yaml/Grammar.lean) — Current output-structure formalization (ValidNode, ValidTokenStream, etc.)
- [Lean4Yaml/CharPredicates.lean](lean/lean4-yaml-verified.iterators/Lean4Yaml/CharPredicates.lean) — Bool/Prop character class predicates with coupling theorems
- [Lean4Yaml/YamlSpec.lean](lean/lean4-yaml-verified.iterators/Lean4Yaml/YamlSpec.lean) — `@[yaml_spec]` attribute system for spec traceability
- [Lean4Yaml/Token.lean](lean/lean4-yaml-verified.iterators/Lean4Yaml/Token.lean) — YamlToken (23 constructors), ScanError (34 constructors), TokenStream
- [Lean4Yaml/Scanner.lean](lean/lean4-yaml-verified.iterators/Lean4Yaml/Scanner.lean) — Scanner implementation with 50+ spec production references in comments
- [Lean4Yaml/TokenParser.lean](lean/lean4-yaml-verified.iterators/Lean4Yaml/TokenParser.lean) — Token-to-AST parser
- [Lean4Yaml/Proofs/](lean/lean4-yaml-verified.iterators/Lean4Yaml/Proofs/) — 1,769 theorems (soundness direction only)

## Verification

1. The document should be reviewed for accuracy against the YAML 1.2.2 spec production numbering
2. Example production encodings should be checked for faithfulness to the spec
3. The gap analysis should be cross-checked against `#yaml_spec_coverage` output to ensure no tagged definitions are missed

## Decisions

- The document is analysis/planning, not implementation — no Lean code changes
- Focus on explaining the *conceptual gap* clearly enough that a reader unfamiliar with the codebase understands why 1,769 theorems don't give strictness
- Include concrete examples showing how a leniency bug (e.g., `? : b` acceptance) is invisible to the current formalization
- Reference the v0.2.11 leniency audit as motivation

## Further Considerations

1. **Mutual recursion depth**: Productions [180]-[199] and [134]-[157] are mutually recursive through [196] `s-l+block-node`. Lean 4's `mutual inductive` may need careful structuring to handle ~165 mutually recursive definitions. **Recommendation**: Group into ~10 mutual blocks by layer, with explicit interfaces between layers.

2. **Auto-detection productions**: Some productions like block scalar indentation ([183] `s-b-comment`) involve auto-detection that depends on runtime state. These may need to be formalized as existential quantification (`∃ m, indent = m ∧ ...`) rather than as parametric predicates. **Recommendation**: Document these special cases explicitly.

