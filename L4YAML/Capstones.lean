/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Composition
import L4YAML.Proofs.Scanner.ScanStrictCoupling
import L4YAML.Proofs.EndToEndCorrectness
import L4YAML.Proofs.Soundness
import L4YAML.Proofs.Output.EmitterScannability
import L4YAML.Proofs.Output.ScannerEmitBridge
import L4YAML.Proofs.Production.DocumentProduction
import L4YAML.Proofs.Parser.ParserCompleteness
import L4YAML.Proofs.Parser.IndexedCompleteness
import L4YAML.Proofs.Coupling.SurfaceCoupling
import L4YAML.Proofs.RoundTrip.RoundTrip

/-!
# Capstones — the library's trust kernel, machine-pinned

The `@[capstone]`-tagged headline theorems of `Blueprint/04-capstones.md`
(the prose primary, per `Blueprint/06-discipline.md` Rule 4), pinned here
so that any drift **fails the build**:

- the `#capstones` pin freezes the tagged **set** — adding, removing, or
  renaming a capstone must update this file (and `scripts/capstones.txt`,
  which drives `scripts/check-theorem-keyword.sh`: these are the only
  declarations allowed to use the `theorem` keyword);
- the `#assert_capstone_axioms` pin freezes each capstone's **axiom
  profile** — `pure` = `propext`/`Classical.choice`/`Quot.sound` only,
  `native` = additionally `Lean.ofReduceBool`-backed `native_decide`
  reflected-decide leaves. Any `sorryAx` or project-declared axiom is a
  hard error, and a capstone silently acquiring a `native_decide`
  dependency flips its line and fails the pin;
- the `#guard` sentinels are compile-time non-vacuity witnesses: the
  hypotheses of the parse capstones are inhabited on real inputs (the
  deep coverage lives in `Tests/AdversarialInstantiation.lean`).

| Group | Capstones (short names) |
|-------|-------------------------|
| 1 pipeline | `parseYaml_pipeline` |
| 2 scanner | `scan_full_consumption` |
| 3 parser | `parseStream_respects_grammar_unconditional`, `soundness_completeness_compose` ×2, `grammar_value_roundtrip` ×2 (indexed twins) |
| 4 end-to-end | `parse_sound_shallow`, `parse_sound_deep`, `parse_complete`, `parse_deterministic` |
| 5 values | `validYaml_construct`, `toYamlValue_correct` |
| 6 round-trip | `universal_roundtrip`, `emit_roundtrip_content_eq`, `canonical_roundtrip_conditional`, `escapeTag_roundtrip` |
| 7 strictness | `parse_strict_proof`, `scan_strict_proof` |
| 8 coupling | `SIndent_zero/succ/col/chars/all_spaces`, `GChar_col` |
-/

/--
info: L4YAML.Proofs.SurfaceCoupling.SIndent_zero
L4YAML.Proofs.EndToEndCorrectness.parse_sound_deep
L4YAML.Proofs.ParserCompleteness.grammar_value_roundtrip
L4YAML.Proofs.ScanStrictCoupling.scan_full_consumption
L4YAML.Proofs.DocumentProduction.parse_strict_proof
L4YAML.Proofs.EndToEndCorrectness.parse_complete
L4YAML.Proofs.Soundness.toYamlValue_correct
L4YAML.Proofs.SurfaceCoupling.SIndent_col
L4YAML.Proofs.DocumentProduction.scan_strict_proof
L4YAML.Proofs.SurfaceCoupling.GChar_col
L4YAML.Proofs.SurfaceCoupling.SIndent_all_spaces
L4YAML.Proofs.EndToEndCorrectness.parse_sound_shallow
L4YAML.Proofs.Composition.parseYaml_pipeline
L4YAML.Proofs.SurfaceCoupling.SIndent_chars
L4YAML.Proofs.RoundTrip.escapeTag_roundtrip
L4YAML.Proofs.SurfaceCoupling.SIndent_succ
L4YAML.Proofs.EndToEndCorrectness.parse_deterministic
L4YAML.Proofs.Indexed.Completeness.grammar_value_roundtrip
L4YAML.Proofs.EndToEndCorrectness.parseStream_respects_grammar_unconditional
L4YAML.Proofs.Indexed.Completeness.soundness_completeness_compose
L4YAML.Proofs.ParserCompleteness.soundness_completeness_compose
L4YAML.Proofs.EmitterScannability.universal_roundtrip
L4YAML.Proofs.EmitterScannability.emit_roundtrip_content_eq
L4YAML.Proofs.ScannerEmitBridge.canonical_roundtrip_conditional
L4YAML.Proofs.Soundness.validYaml_construct
-/
#guard_msgs in
#capstones

/--
info: L4YAML.Proofs.SurfaceCoupling.SIndent_zero: pure
L4YAML.Proofs.EndToEndCorrectness.parse_sound_deep: native
L4YAML.Proofs.ParserCompleteness.grammar_value_roundtrip: pure
L4YAML.Proofs.ScanStrictCoupling.scan_full_consumption: pure
L4YAML.Proofs.DocumentProduction.parse_strict_proof: native
L4YAML.Proofs.EndToEndCorrectness.parse_complete: pure
L4YAML.Proofs.Soundness.toYamlValue_correct: pure
L4YAML.Proofs.SurfaceCoupling.SIndent_col: pure
L4YAML.Proofs.DocumentProduction.scan_strict_proof: native
L4YAML.Proofs.SurfaceCoupling.GChar_col: pure
L4YAML.Proofs.SurfaceCoupling.SIndent_all_spaces: pure
L4YAML.Proofs.EndToEndCorrectness.parse_sound_shallow: pure
L4YAML.Proofs.Composition.parseYaml_pipeline: pure
L4YAML.Proofs.SurfaceCoupling.SIndent_chars: pure
L4YAML.Proofs.RoundTrip.escapeTag_roundtrip: native
L4YAML.Proofs.SurfaceCoupling.SIndent_succ: pure
L4YAML.Proofs.EndToEndCorrectness.parse_deterministic: pure
L4YAML.Proofs.Indexed.Completeness.grammar_value_roundtrip: pure
L4YAML.Proofs.EndToEndCorrectness.parseStream_respects_grammar_unconditional: native
L4YAML.Proofs.Indexed.Completeness.soundness_completeness_compose: pure
L4YAML.Proofs.ParserCompleteness.soundness_completeness_compose: pure
L4YAML.Proofs.EmitterScannability.universal_roundtrip: native
L4YAML.Proofs.EmitterScannability.emit_roundtrip_content_eq: native
L4YAML.Proofs.ScannerEmitBridge.canonical_roundtrip_conditional: pure
L4YAML.Proofs.Soundness.validYaml_construct: pure
-/
#guard_msgs in
#assert_capstone_axioms

-- Non-vacuity sentinels: the parse capstones' hypotheses are inhabited
-- on real inputs (block mapping, block sequence, nested flow).
#guard (L4YAML.TokenParser.parseYaml "a: 1").isOk
#guard (L4YAML.TokenParser.parseYaml "- x\n- y").isOk
#guard (L4YAML.TokenParser.parseYaml "[1, 2, {k: v}]").isOk
