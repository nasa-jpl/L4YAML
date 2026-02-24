import LeanYaml
import Std.Data.HashMap

/-!
# Serialization Example

Demonstrates round-trip serialization: Lean → YAML → Lean

Shows how to use the emitter with typed values.
-/

open LeanYaml
open LeanYaml.Schema

/-! ## Example 1: Simple Struct Serialization -/

structure ServerConfig where
  host : String
  port : Nat
  enabled : Bool
  deriving LeanYaml.Schema.FromYaml, LeanYaml.Schema.ToYaml, Repr

def example1 : IO Unit := do
  IO.println "=== Example 1: Struct Serialization ==="

  -- Create a Lean value
  let config : ServerConfig := {
    host := "localhost"
    port := 8080
    enabled := true
  }

  -- Convert to YAML
  let yaml := emit (Schema.toYaml config)
  IO.println "Serialized YAML:"
  IO.println yaml
  IO.println ""

  -- Parse it back
  match parseAs ServerConfig yaml with
  | .ok parsed =>
      IO.println s!"Parsed back: {repr parsed}"
      if parsed.host == config.host && parsed.port == config.port && parsed.enabled == config.enabled then
        IO.println "✓ Round-trip successful!"
      else
        IO.println "✗ Round-trip failed"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
  IO.println ""

/-! ## Example 2: Enum Serialization -/

inductive LogLevel where
  | debug | info | warning | error
  deriving LeanYaml.Schema.FromYaml, LeanYaml.Schema.ToYaml, Repr, BEq

def example2 : IO Unit := do
  IO.println "=== Example 2: Enum Serialization ==="

  let level := LogLevel.warning
  let yaml := emit (Schema.toYaml level)
  IO.println s!"Log level: {repr level}"
  IO.println s!"Serialized: {yaml}"

  match parseAs LogLevel yaml with
  | .ok parsed =>
      if parsed == level then
        IO.println "✓ Round-trip successful!"
      else
        IO.println "✗ Round-trip failed"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
  IO.println ""

/-! ## Example 3: HashMap Serialization -/

def example3 : IO Unit := do
  IO.println "=== Example 3: HashMap Serialization ==="

  let config := Std.HashMap.ofList [
    ("database", "postgres"),
    ("cache", "redis"),
    ("queue", "rabbitmq")
  ]

  let yaml := emit (Schema.toYaml config)
  IO.println "Services map:"
  IO.println yaml
  IO.println ""

  match parseAs (Std.HashMap String String) yaml with
  | .ok parsed =>
      IO.println s!"Parsed {parsed.size} entries"
      for (k, v) in parsed.toList do
        IO.println s!"  {k}: {v}"
      IO.println "✓ Round-trip successful!"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
  IO.println ""

/-! ## Example 4: Nested Structure Serialization -/

structure DatabaseConfig where
  host : String
  port : Nat
  deriving LeanYaml.Schema.FromYaml, LeanYaml.Schema.ToYaml, Repr

structure AppConfig where
  appName : String
  database : DatabaseConfig
  logLevel : LogLevel
  deriving LeanYaml.Schema.FromYaml, LeanYaml.Schema.ToYaml, Repr

def example4 : IO Unit := do
  IO.println "=== Example 4: Nested Structure Serialization ==="

  let config : AppConfig := {
    appName := "MyApp"
    database := {
      host := "db.example.com"
      port := 5432
    }
    logLevel := LogLevel.info
  }

  let yaml := emit (Schema.toYaml config)
  IO.println "Application config:"
  IO.println yaml
  IO.println ""

  match parseAs AppConfig yaml with
  | .ok parsed =>
      IO.println s!"Parsed: {repr parsed}"
      IO.println "✓ Round-trip successful!"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
  IO.println ""

/-! ## Example 5: Array Serialization -/

def example5 : IO Unit := do
  IO.println "=== Example 5: Array Serialization ==="

  let servers := #["web1.example.com", "web2.example.com", "web3.example.com"]
  let yaml := emit (Schema.toYaml servers)
  IO.println "Server list:"
  IO.println yaml
  IO.println ""

  match parseAs (Array String) yaml with
  | .ok parsed =>
      IO.println s!"Parsed {parsed.size} servers:"
      for server in parsed do
        IO.println s!"  - {server}"
      IO.println "✓ Round-trip successful!"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
  IO.println ""

/-! ## Example 6: Optional Fields -/

structure UserProfile where
  username : String
  email : String
  age : Option Nat := none
  bio : Option String := none
  deriving LeanYaml.Schema.FromYaml, LeanYaml.Schema.ToYaml, Repr

def example6 : IO Unit := do
  IO.println "=== Example 6: Optional Fields Serialization ==="

  let user : UserProfile := {
    username := "alice"
    email := "alice@example.com"
    age := some 30
    bio := none
  }

  let yaml := emit (Schema.toYaml user)
  IO.println "User profile:"
  IO.println yaml
  IO.println ""

  match parseAs UserProfile yaml with
  | .ok parsed =>
      IO.println s!"Parsed: {repr parsed}"
      IO.println "✓ Round-trip successful!"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
  IO.println ""

def main : IO Unit := do
  example1
  example2
  example3
  example4
  example5
  example6
  IO.println "✅ All serialization examples complete!"
