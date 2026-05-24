/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.EmitScans

/-! # `IndexedEmitterScannability.ParseStream` — Phase 3 Step 6f.3b3 staging

**Status**: staging file (skeleton). Populated incrementally as the
emit-parse interaction proofs are ported to the indexed substrate.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **§4 Full Pipeline: Emit → Scan → Parse** (legacy lines
    8400–8489, ~90 LOC). `scanFiltered_exists_of_isOk`,
    `parseStreamLoop_single_doc`, `emit_parsed_grammable` (top-
    level composition: `emit v` parsed back via `parseYamlRaw` gives
    a `Grammable` value).

  - **§5.2 Scanner content preservation** (legacy lines 8531–8874,
    ~344 LOC). `scanFiltered_emitScalar_content` /
    `scanFiltered_emitScalar_vals` (the scanner preserves emitted
    scalar content exactly), `parseDirectives_skip`,
    `parseStream_three_tokens_scalar`,
    `parseYamlRaw_emitScalar_value`.

These proofs bridge the scanner-acceptance result
(`emit_produces_valid_yaml` from `EmitScans.lean`) to the parser
output, showing that the recovered AST matches the original value
via the `compose` content-fidelity layer.

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

namespace L4YAML.Proofs.Indexed.EmitterScannability.ParseStream

-- (content to be added incrementally in 6f.3b3.parsestream sub-step)

end L4YAML.Proofs.Indexed.EmitterScannability.ParseStream
