import Lean4Yaml

/-!
# TryRoundTrip — YAML parse → emit → re-parse round-trip test

Reads a YAML file from `inputPath`, parses it, emits canonical YAML
via `Emit.emit`, writes the result to `outputPath`, then re-parses
the canonical output and checks structural equivalence with `contentEq`.

## Exit codes

| Code | Meaning                                      |
|------|----------------------------------------------|
| 0    | Round-trip succeeded, values content-equal    |
| 1    | Initial parse failed                         |
| 2    | Re-parse of canonical output failed          |
| 3    | Content equivalence check failed             |
| 4    | Usage error                                  |
-/

open Lean4Yaml

/--
Emit an array of YAML documents as a multi-document canonical string.

Each document is wrapped in `---` / `...` markers and emitted in
canonical flow form.  Single-document streams omit the markers for
cleanliness.
-/
private def emitDocuments (docs : Array YamlDocument) : String :=
  if docs.size == 1 then
    Emit.emit docs[0]!.value ++ "\n"
  else
    let parts := docs.map fun doc =>
      "---\n" ++ Emit.emit doc.value ++ "\n...\n"
    String.join parts.toList

/--
Check content equivalence of two document arrays.

Compares document-by-document using `Emit.contentEq`.
Returns `true` iff both arrays have the same length and every
pair of corresponding document values is content-equivalent.
-/
private def documentsContentEq
    (ds₁ ds₂ : Array YamlDocument) : Bool :=
  ds₁.size == ds₂.size &&
    (List.zip ds₁.toList ds₂.toList).all fun (d₁, d₂) =>
      Emit.contentEq d₁.value d₂.value

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputPath, outputPath] =>
    -- Step 1: Read and parse original YAML
    let content ← IO.FS.readFile inputPath
    let docs ← match Parse.parseYaml content with
      | .ok docs => pure docs
      | .error e =>
        IO.eprintln s!"parse error (input): {e}"
        return 1

    -- Step 2: Emit canonical form and write to output
    let canonical := emitDocuments docs
    IO.FS.writeFile outputPath canonical

    -- Step 3: Re-parse canonical output
    let docs' ← match Parse.parseYaml canonical with
      | .ok docs' => pure docs'
      | .error e =>
        IO.eprintln s!"parse error (canonical output): {e}"
        return 2

    -- Step 4: Check content equivalence
    if documentsContentEq docs docs' then
      return 0
    else
      IO.eprintln s!"content equivalence check failed"
      IO.eprintln s!"  original documents: {docs.size}"
      IO.eprintln s!"  canonical documents: {docs'.size}"
      return 3

  | _ =>
    IO.eprintln "Usage: tryroundtrip <input.yaml> <output.yaml>"
    return 4
