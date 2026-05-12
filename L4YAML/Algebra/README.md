# `L4YAML.Algebra` — Frozen algebra library (Initiative 4, Phase 2)

This directory hosts the 23 algebraic items inventoried in
`Blueprint/08-initiative-4-intrinsic-foundations.md` §Algebra library.

The inventory is **closed**: every algebraic statement used in
Phase 3+ must decompose into one of Items 0–23. Adding a 24th item
triggers a re-opening of Phase 1 (Guardrail 2).

## Layout (one file per item-cluster, per D4)

| File | Items | Status |
|---|---|---|
| `Position.lean` | 7, 13 | Landed (Phase 2 §1) |
| `Indent.lean` | 8 | Landed |
| `StringList.lean` | 9, 22 | Landed (Item 22 migrated; Item 9 added) |
| `TokenStream.lean` | 10 | TODO |
| `Fuel.lean` | 11 | TODO |
| `AnchorMap.lean` | 12 | Migrated from `Spec/Types.lean` |
| `Combinators.lean` | 14 | TODO |
| `Schema.lean` | 15, 16 | TODO |
| `Token.lean` | 17 | TODO |
| `Value.lean` | 18–21 | Migrated |
| `LawfulBEq.lean` | 23 | Migrated |
| `Equivalence.lean` | 1, 2, 3, 5, 6 | TODO (depends on AnchorMap) |
| `Idempotence.lean` | 4 | TODO (capstone of Phase 2) |

Items 0 (immutable data) and the indexed-type substrate live
under `L4YAML/Indexed/` rather than here.

## Sorry budget: 0 at phase boundary.
