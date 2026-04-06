import Lean4Yaml.TokenParser
import Lean4Yaml.Scanner
import Lean4Yaml.Grammar

/-!
# Composition Theorems

This module provides composition theorems for the tokenized YAML pipeline:

```
  String ──Scanner.scan──→ Array (Positioned YamlToken) ──parseStream──→ Array YamlDocument
         └── parseYamlRaw ──────────────────────────────────────────────┘
         └── parseYaml ────────("compose" aliases)────────────────────────→ Array YamlDocument
```

## Architecture

**P10.5 rewrite**: The previous version composed old char-level parser specs
(position algebra, fuel wrappers, lean4-parser combinator extensions) for the
pre-P10 `yamlStream` parser.  Now that the public API delegates to
`TokenParser.parseYamlRaw` / `TokenParser.parseYaml`, the relevant composition
is about the **Scanner → TokenParser** pipeline.

### Sections

1. **Scanner–TokenParser Pipeline** (§1): `parseYamlRaw` decomposes into
   `Scanner.scan` followed by `parseStream`.  Error propagation flows
   naturally from `do`-notation.

2. **Compose Layer** (§2): `parseYaml` applies `YamlDocument.compose`
   to each document from `parseYamlRaw`, resolving aliases and stripping
   anchors.  The key theorem `parseYaml_ok_iff` (in `Completeness.lean`)
   is re-exported here for convenience.
-/

namespace Lean4Yaml.Proofs.Composition

open Lean4Yaml
open Lean4Yaml.Grammar
open Lean4Yaml.TokenParser

/-! ## §1  Scanner–TokenParser Pipeline

`parseYamlRaw` is `do let tokens ← Scanner.scanFiltered input; parseStream tokens`.
The following theorems decompose this pipeline.
-/

/--
`parseYamlRaw` decomposes into scanning then parsing: if both stages
succeed, the result is the `parseStream` output on the scanned tokens.
-/
theorem parseYamlRaw_pipeline (input : String)
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_scan : Scanner.scanFiltered input = .ok tokens)
    (h_parse : parseStream tokens = .ok docs) :
    parseYamlRaw input = .ok docs := by
  simp only [parseYamlRaw, h_scan, h_parse]

/--
If `parseYamlRaw` succeeds, then both `Scanner.scan` and `parseStream`
must have succeeded.
-/
theorem parseYamlRaw_ok_decompose (input : String) (docs : Array YamlDocument)
    (h : parseYamlRaw input = .ok docs) :
    ∃ tokens : Array (Positioned YamlToken),
      Scanner.scanFiltered input = .ok tokens ∧ parseStream tokens = .ok docs := by
  simp only [parseYamlRaw] at h
  match h_scan : Scanner.scanFiltered input with
  | .ok tokens =>
    simp only [h_scan] at h
    match h_parse : parseStream tokens with
    | .ok docs' =>
      simp only [h_parse, Except.ok.injEq] at h
      subst h; exact ⟨tokens, rfl, h_parse⟩
    | .error e =>
      simp only [h_parse] at h; contradiction
  | .error e =>
    simp only [h_scan] at h; contradiction

/--
If `Scanner.scan` fails, `parseYamlRaw` fails with the same error.
-/
theorem parseYamlRaw_scan_error (input : String) (e : ScanError)
    (h : Scanner.scanFiltered input = .error e) :
    parseYamlRaw input = .error e := by
  simp only [parseYamlRaw, h]

/--
If `Scanner.scan` succeeds but `parseStream` fails, `parseYamlRaw` fails
with the same parse error.
-/
theorem parseYamlRaw_parse_error (input : String) (e : ScanError)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered input = .ok tokens)
    (h_parse : parseStream tokens = .error e) :
    parseYamlRaw input = .error e := by
  simp only [parseYamlRaw, h_scan, h_parse]

/-! ## §2  Compose Layer

`parseYaml` extends `parseYamlRaw` by applying `YamlDocument.compose`
to each raw document, resolving aliases and stripping anchor annotations.
The primary decomposition theorem `parseYaml_ok_iff` is in `Completeness.lean`;
here we provide additional convenience forms.
-/

/--
If `parseYamlRaw` succeeds, `parseYaml` succeeds with composed documents.
-/
theorem parseYaml_of_parseYamlRaw_ok (input : String) (docs : Array YamlDocument)
    (h : parseYamlRaw input = .ok docs) :
    parseYaml input = .ok (docs.map YamlDocument.compose) := by
  simp only [parseYaml, h]

/--
If `parseYamlRaw` fails, `parseYaml` fails with the same error.
-/
theorem parseYaml_of_parseYamlRaw_error (input : String) (e : ScanError)
    (h : parseYamlRaw input = .error e) :
    parseYaml input = .error e := by
  simp only [parseYaml, h]

/--
Full pipeline composition: Scanner.scan → parseStream → compose.
If scanning and parsing both succeed, `parseYaml` returns composed documents.
-/
theorem parseYaml_pipeline (input : String)
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_scan : Scanner.scanFiltered input = .ok tokens)
    (h_parse : parseStream tokens = .ok docs) :
    parseYaml input = .ok (docs.map YamlDocument.compose) :=
  parseYaml_of_parseYamlRaw_ok input docs (parseYamlRaw_pipeline input tokens docs h_scan h_parse)

end Lean4Yaml.Proofs.Composition
