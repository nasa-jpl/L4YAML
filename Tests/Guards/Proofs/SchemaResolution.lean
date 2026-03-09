import Lean4Yaml.Proofs.SchemaResolution

namespace Lean4Yaml.Schema.Proofs

open Lean4Yaml.Schema
open Lean4Yaml

-- Null resolution
#guard resolveImplicit "" == .null
#guard resolveImplicit "null" == .null
#guard resolveImplicit "~" == .null
#guard resolveImplicit "Null" == .null
#guard resolveImplicit "NULL" == .null

-- Boolean resolution
#guard resolveImplicit "true" == .bool true
#guard resolveImplicit "false" == .bool false
#guard resolveImplicit "True" == .bool true
#guard resolveImplicit "False" == .bool false
#guard resolveImplicit "TRUE" == .bool true
#guard resolveImplicit "FALSE" == .bool false

-- Integer resolution
#guard resolveImplicit "0" == .int 0
#guard resolveImplicit "42" == .int 42
#guard resolveImplicit "-17" == .int (-17)
#guard resolveImplicit "+3" == .int 3
#guard resolveImplicit "0xFF" == .int 255
#guard resolveImplicit "0o17" == .int 15

-- String fallback
#guard resolveImplicit "hello" == .str "hello"
#guard resolveImplicit "Hello World" == .str "Hello World"
#guard resolveImplicit "yes" == .str "yes"   -- NOT bool in YAML 1.2.2

-- Explicit tag override
#guard resolveScalar "42" (some "tag:yaml.org,2002:str") == .str "42"
#guard resolveScalar "true" (some "tag:yaml.org,2002:str") == .str "true"
#guard resolveScalar "" (some "tag:yaml.org,2002:str") == .str ""
#guard resolveScalar "42" (some "tag:yaml.org,2002:int") == .int 42
#guard resolveScalar "hello" (some "tag:yaml.org,2002:null") == .null

-- Resolve on YamlValue (isXxx Boolean checks)
#guard (resolve (.scalar { content := "hello", style := .plain })).isStr
#guard (resolve (.scalar { content := "42", style := .plain })).isInt
#guard (resolve (.scalar { content := "true", style := .plain })).isBool
#guard (resolve (.scalar { content := "null", style := .plain })).isNull
#guard (resolve (.sequence .block #[] none none)).isSeq
#guard (resolve (.mapping .block #[] none none)).isMap

end Lean4Yaml.Schema.Proofs
