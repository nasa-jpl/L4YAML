/-
  Config Deserialization — FromYaml/ToYaml instances for ParserLimits and DumpConfig

  Self-hosted configuration: the verified parser reads its own limit and
  dump configuration from YAML using the Schema FromYaml/ToYaml machinery,
  bootstrapped with hardcoded strict limits (no circular dependency —
  the config parser uses `parseYamlSingleSafe` with built-in limits).

  ## YAML Representation

  All struct fields are optional; omitted fields use the struct default.
  This mirrors the `FromJson` pattern in Dump.lean.

  ```yaml
  # ParserLimits (partial — omitted fields use defaults)
  alias:
    maxAliasDepth: 20
    maxAliasExpansions: 1000
  structural:
    maxDepth: 50
  tag:
    policy: coreSchemaOnly
  enabled: true

  # DumpConfig (partial)
  indent: 4
  defaultStyle: block
  ```

  ### TagPolicy YAML encoding

  0-ary variants as plain scalars, parametric variants as single-key mappings:
  - `allowAll`, `rejectAll`, `coreSchemaOnly` → plain scalar
  - `{whitelist: ["tag:yaml.org,2002:str", ...]}` → `.whitelist`
  - `{blacklist: ["!!python/"]}` → `.blacklist`
-/
import L4YAML.Config.Limits
import L4YAML.Output.Dump
import L4YAML.Schema.FromToYaml
import L4YAML.Schema.Struct

set_option autoImplicit false

namespace L4YAML.Config

open L4YAML
open L4YAML.Schema
open L4YAML.Dump (DefaultStyle ScalarPref DumpConfig)

/-! ## Dump Configuration Types -/

instance : FromYaml DefaultStyle where
  fromYaml? v := do
    let str ← getString v
    match str with
    | "block" => .ok .block
    | "flow"  => .ok .flow
    | "auto"  => .ok .auto
    | other   => .error (.unknownVariant other "DefaultStyle")

instance : ToYaml DefaultStyle where
  toYaml
    | .block => YamlValue.scalar { content := "block", style := .plain }
    | .flow  => YamlValue.scalar { content := "flow", style := .plain }
    | .auto  => YamlValue.scalar { content := "auto", style := .plain }

instance : FromYaml ScalarPref where
  fromYaml? v := do
    let str ← getString v
    match str with
    | "plain"        => .ok .plain
    | "doubleQuoted" => .ok .doubleQuoted
    | "singleQuoted" => .ok .singleQuoted
    | "auto"         => .ok .auto
    | other          => .error (.unknownVariant other "ScalarPref")

instance : ToYaml ScalarPref where
  toYaml
    | .plain        => YamlValue.scalar { content := "plain", style := .plain }
    | .doubleQuoted => YamlValue.scalar { content := "doubleQuoted", style := .plain }
    | .singleQuoted => YamlValue.scalar { content := "singleQuoted", style := .plain }
    | .auto         => YamlValue.scalar { content := "auto", style := .plain }

instance : FromYaml DumpConfig where
  fromYaml? v := do
    let pairs ← getMapping v
    let dflt : DumpConfig := {}
    return {
      indent := (← getFieldOpt pairs "indent").getD dflt.indent
      defaultStyle := (← getFieldOpt pairs "defaultStyle").getD dflt.defaultStyle
      scalarStyle := (← getFieldOpt pairs "scalarStyle").getD dflt.scalarStyle
      lineWidth := (← getFieldOpt pairs "lineWidth").getD dflt.lineWidth
      sortKeys := (← getFieldOpt pairs "sortKeys").getD dflt.sortKeys
      allowReservedPlain := (← getFieldOpt pairs "allowReservedPlain").getD dflt.allowReservedPlain
      omitEmpty := (← getFieldOpt pairs "omitEmpty").getD dflt.omitEmpty
      compactSequenceMap := (← getFieldOpt pairs "compactSequenceMap").getD dflt.compactSequenceMap
    }

instance : ToYaml DumpConfig where
  toYaml cfg := mkMapping [
    ("indent", toYaml cfg.indent),
    ("defaultStyle", toYaml cfg.defaultStyle),
    ("scalarStyle", toYaml cfg.scalarStyle),
    ("lineWidth", toYaml cfg.lineWidth),
    ("sortKeys", toYaml cfg.sortKeys),
    ("allowReservedPlain", toYaml cfg.allowReservedPlain),
    ("omitEmpty", toYaml cfg.omitEmpty),
    ("compactSequenceMap", toYaml cfg.compactSequenceMap)
  ]

/-! ## Parser Limits Types -/

instance : FromYaml AliasLimits where
  fromYaml? v := do
    let pairs ← getMapping v
    let dflt : AliasLimits := {}
    return {
      maxAliasDepth := (← getFieldOpt pairs "maxAliasDepth").getD dflt.maxAliasDepth
      maxAliasExpansions := (← getFieldOpt pairs "maxAliasExpansions").getD dflt.maxAliasExpansions
      maxResolvedNodes := (← getFieldOpt pairs "maxResolvedNodes").getD dflt.maxResolvedNodes
      rejectCycles := (← getFieldOpt pairs "rejectCycles").getD dflt.rejectCycles
    }

instance : ToYaml AliasLimits where
  toYaml cfg := mkMapping [
    ("maxAliasDepth", toYaml cfg.maxAliasDepth),
    ("maxAliasExpansions", toYaml cfg.maxAliasExpansions),
    ("maxResolvedNodes", toYaml cfg.maxResolvedNodes),
    ("rejectCycles", toYaml cfg.rejectCycles)
  ]

instance : FromYaml StructuralLimits where
  fromYaml? v := do
    let pairs ← getMapping v
    let dflt : StructuralLimits := {}
    return {
      maxDepth := (← getFieldOpt pairs "maxDepth").getD dflt.maxDepth
      maxSequenceLength := (← getFieldOpt pairs "maxSequenceLength").getD dflt.maxSequenceLength
      maxMappingSize := (← getFieldOpt pairs "maxMappingSize").getD dflt.maxMappingSize
      maxScalarBytes := (← getFieldOpt pairs "maxScalarBytes").getD dflt.maxScalarBytes
      maxTotalNodes := (← getFieldOpt pairs "maxTotalNodes").getD dflt.maxTotalNodes
    }

instance : ToYaml StructuralLimits where
  toYaml cfg := mkMapping [
    ("maxDepth", toYaml cfg.maxDepth),
    ("maxSequenceLength", toYaml cfg.maxSequenceLength),
    ("maxMappingSize", toYaml cfg.maxMappingSize),
    ("maxScalarBytes", toYaml cfg.maxScalarBytes),
    ("maxTotalNodes", toYaml cfg.maxTotalNodes)
  ]

instance : FromYaml DocumentLimits where
  fromYaml? v := do
    let pairs ← getMapping v
    let dflt : DocumentLimits := {}
    return {
      maxDocuments := (← getFieldOpt pairs "maxDocuments").getD dflt.maxDocuments
      maxAnchors := (← getFieldOpt pairs "maxAnchors").getD dflt.maxAnchors
      maxInputBytes := (← getFieldOpt pairs "maxInputBytes").getD dflt.maxInputBytes
    }

instance : ToYaml DocumentLimits where
  toYaml cfg := mkMapping [
    ("maxDocuments", toYaml cfg.maxDocuments),
    ("maxAnchors", toYaml cfg.maxAnchors),
    ("maxInputBytes", toYaml cfg.maxInputBytes)
  ]

/-! ## TagPolicy — manual instances (parametric constructors) -/

instance : FromYaml TagPolicy where
  fromYaml? v :=
    -- Try scalar first (0-ary variants)
    match v with
    | .scalar s =>
      match s.content with
      | "allowAll"       => .ok .allowAll
      | "rejectAll"      => .ok .rejectAll
      | "coreSchemaOnly" => .ok .coreSchemaOnly
      | other            => .error (.unknownVariant other "TagPolicy")
    | .mapping _ pairs _ _ =>
      -- Single-key mapping for parametric variants
      if pairs.size != 1 then
        .error (.unknownVariant s!"mapping with {pairs.size} keys" "TagPolicy")
      else
        let (key, val) := pairs[0]!
        match getScalarContent key with
        | some "whitelist" => do
            let allowed ← fromYaml? val
            .ok (.whitelist allowed)
        | some "blacklist" => do
            let forbidden ← fromYaml? val
            .ok (.blacklist forbidden)
        | some other => .error (.unknownVariant other "TagPolicy")
        | none => .error (.unknownVariant "non-scalar key" "TagPolicy")
    | _ => .error (.unknownVariant "non-scalar/mapping" "TagPolicy")

instance : ToYaml TagPolicy where
  toYaml
    | .allowAll       => YamlValue.scalar { content := "allowAll", style := .plain }
    | .rejectAll      => YamlValue.scalar { content := "rejectAll", style := .plain }
    | .coreSchemaOnly => YamlValue.scalar { content := "coreSchemaOnly", style := .plain }
    | .whitelist allowed =>
      mkMapping [("whitelist", toYaml allowed)]
    | .blacklist forbidden =>
      mkMapping [("blacklist", toYaml forbidden)]

instance : FromYaml TagLimits where
  fromYaml? v := do
    let pairs ← getMapping v
    let dflt : TagLimits := {}
    return {
      policy := (← getFieldOpt pairs "policy").getD dflt.policy
      rejectLanguageTags := (← getFieldOpt pairs "rejectLanguageTags").getD dflt.rejectLanguageTags
      maxTagLength := (← getFieldOpt pairs "maxTagLength").getD dflt.maxTagLength
      maxUniqueTags := (← getFieldOpt pairs "maxUniqueTags").getD dflt.maxUniqueTags
      rejectCustomHandles := (← getFieldOpt pairs "rejectCustomHandles").getD dflt.rejectCustomHandles
      maxHandlePrefixLength := (← getFieldOpt pairs "maxHandlePrefixLength").getD dflt.maxHandlePrefixLength
    }

instance : ToYaml TagLimits where
  toYaml cfg := mkMapping [
    ("policy", toYaml cfg.policy),
    ("rejectLanguageTags", toYaml cfg.rejectLanguageTags),
    ("maxTagLength", toYaml cfg.maxTagLength),
    ("maxUniqueTags", toYaml cfg.maxUniqueTags),
    ("rejectCustomHandles", toYaml cfg.rejectCustomHandles),
    ("maxHandlePrefixLength", toYaml cfg.maxHandlePrefixLength)
  ]

instance : FromYaml ParserLimits where
  fromYaml? v := do
    let pairs ← getMapping v
    let dflt : ParserLimits := {}
    return {
      alias := (← getFieldOpt pairs "alias").getD dflt.alias
      structural := (← getFieldOpt pairs "structural").getD dflt.structural
      document := (← getFieldOpt pairs "document").getD dflt.document
      tag := (← getFieldOpt pairs "tag").getD dflt.tag
      enabled := (← getFieldOpt pairs "enabled").getD dflt.enabled
    }

instance : ToYaml ParserLimits where
  toYaml cfg := mkMapping [
    ("alias", toYaml cfg.alias),
    ("structural", toYaml cfg.structural),
    ("document", toYaml cfg.document),
    ("tag", toYaml cfg.tag),
    ("enabled", toYaml cfg.enabled)
  ]

/-! ## Safe Config Parsing (bootstrapping) -/

/-- Hardcoded limits for config parsing — config YAML is small and trusted
    but we still enforce basic safety.  These are tighter than `.strict`
    since config documents should never be large or complex. -/
def configParserLimits : ParserLimits := {
  alias := { maxAliasDepth := 5, maxAliasExpansions := 10,
             maxResolvedNodes := 500 }
  structural := { maxDepth := 10, maxSequenceLength := 100,
                  maxMappingSize := 50, maxScalarBytes := 4096,
                  maxTotalNodes := 1000 }
  document := { maxDocuments := 1, maxAnchors := 10,
                maxInputBytes := 65536 }
  tag := { policy := .rejectAll }
}

/-- Parse a YAML string into a typed value using safe parsing with
    tight config-specific limits.  This is the bootstrapping entry point:
    the parser parses its own configuration.

    Combines `parseYamlSingleSafe` (with `configParserLimits`) and
    `Schema.fromYaml?` into a single safe pipeline. -/
def parseConfigYaml (α : Type) [FromYaml α] (input : String) : Except String α := do
  let yaml ← (parseYamlSingleSafe input configParserLimits).mapError toString
  (fromYaml? yaml).mapError toString

end L4YAML.Config
