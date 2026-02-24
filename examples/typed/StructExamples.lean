import LeanYaml

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Struct Support Examples

Demonstrates how to add `FromYaml` and `ToYaml` instances for custom structs.

## Pattern

1. Define your struct
2. Implement `FromYaml` using helper functions
3. Implement `ToYaml` using helper functions
4. Use with `parseAs` and `toYaml`
-/

namespace StructExamples

open LeanYaml
open LeanYaml.Schema (FromYaml ToYaml getMapping getField getFieldOpt mkMapping addField addFieldOpt)

/-! ## Example 1: Simple Configuration -/

structure ServerConfig where
  host : String
  port : Nat
  enabled : Bool

instance : FromYaml ServerConfig where
  fromYaml? v := do
    let pairs ← getMapping v
    return {
      host := ← getField pairs "host"
      port := ← getField pairs "port"
      enabled := ← getField pairs "enabled"
    }

instance : ToYaml ServerConfig where
  toYaml cfg :=
    mkMapping [
      ("host", toYaml cfg.host),
      ("port", toYaml cfg.port),
      ("enabled", toYaml cfg.enabled)
    ]

def testServerConfig : IO Unit := do
  let yaml := "
host: localhost
port: 8080
enabled: true
"
  match parseAs ServerConfig yaml with
  | .ok config =>
      IO.println s!"✓ Parsed config:"
      IO.println s!"  Host: {config.host}"
      IO.println s!"  Port: {config.port}"
      IO.println s!"  Enabled: {config.enabled}"

      -- Round-trip: convert back to YAML
      let yamlValue := toYaml config
      IO.println s!"✓ Round-trip YAML: {repr yamlValue}"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
      IO.Process.exit 1

/-! ## Example 2: Nested Structures -/

structure DatabaseConfig where
  host : String
  port : Nat
  username : String
  password : String

structure AppConfig where
  appName : String
  debug : Bool
  database : DatabaseConfig

instance : FromYaml DatabaseConfig where
  fromYaml? v := do
    let pairs ← getMapping v
    return {
      host := ← getField pairs "host"
      port := ← getField pairs "port"
      username := ← getField pairs "username"
      password := ← getField pairs "password"
    }

instance : ToYaml DatabaseConfig where
  toYaml cfg :=
    mkMapping [
      ("host", toYaml cfg.host),
      ("port", toYaml cfg.port),
      ("username", toYaml cfg.username),
      ("password", toYaml cfg.password)
    ]

instance : FromYaml AppConfig where
  fromYaml? v := do
    let pairs ← getMapping v
    return {
      appName := ← getField pairs "appName"
      debug := ← getField pairs "debug"
      database := ← getField pairs "database"
    }

instance : ToYaml AppConfig where
  toYaml cfg :=
    mkMapping [
      ("appName", toYaml cfg.appName),
      ("debug", toYaml cfg.debug),
      ("database", toYaml cfg.database)
    ]

def testNestedConfig : IO Unit := do
  let yaml := "
appName: MyApp
debug: false
database:
  host: db.example.com
  port: 5432
  username: admin
  password: secret
"
  match parseAs AppConfig yaml with
  | .ok config =>
      IO.println s!"✓ Parsed app config:"
      IO.println s!"  App: {config.appName}"
      IO.println s!"  Debug: {config.debug}"
      IO.println s!"  DB Host: {config.database.host}"
      IO.println s!"  DB Port: {config.database.port}"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
      IO.Process.exit 1

/-! ## Example 3: Optional Fields -/

structure UserProfile where
  username : String
  email : String
  age : Option Nat        -- Optional field
  bio : Option String     -- Optional field

instance : FromYaml UserProfile where
  fromYaml? v := do
    let pairs ← getMapping v
    return {
      username := ← getField pairs "username"
      email := ← getField pairs "email"
      age := ← getFieldOpt pairs "age"
      bio := ← getFieldOpt pairs "bio"
    }

instance : ToYaml UserProfile where
  toYaml profile :=
    let pairs := #[]
    let pairs := addField pairs "username" profile.username
    let pairs := addField pairs "email" profile.email
    let pairs := addFieldOpt pairs "age" profile.age
    let pairs := addFieldOpt pairs "bio" profile.bio
    YamlValue.mapping CollectionStyle.block pairs none

def testOptionalFields : IO Unit := do
  let yaml1 := "
username: alice
email: alice@example.com
age: 30
bio: Software engineer
"
  let yaml2 := "
username: bob
email: bob@example.com
"
  -- Test with all fields
  match parseAs UserProfile yaml1 with
  | .ok profile =>
      IO.println s!"✓ Parsed profile (all fields):"
      IO.println s!"  Username: {profile.username}"
      IO.println s!"  Age: {profile.age}"
      IO.println s!"  Bio: {profile.bio}"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
      IO.Process.exit 1

  -- Test with only required fields
  match parseAs UserProfile yaml2 with
  | .ok profile =>
      IO.println s!"✓ Parsed profile (minimal):"
      IO.println s!"  Username: {profile.username}"
      IO.println s!"  Age: {profile.age}"  -- Should be none
      IO.println s!"  Bio: {profile.bio}"  -- Should be none
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
      IO.Process.exit 1

/-! ## Example 4: Arrays and Collections -/

structure Team where
  name : String
  members : Array String
  active : Bool

instance : FromYaml Team where
  fromYaml? v := do
    let pairs ← getMapping v
    return {
      name := ← getField pairs "name"
      members := ← getField pairs "members"
      active := ← getField pairs "active"
    }

instance : ToYaml Team where
  toYaml team :=
    mkMapping [
      ("name", toYaml team.name),
      ("members", toYaml team.members),
      ("active", toYaml team.active)
    ]

def testArrayFields : IO Unit := do
  let yaml := "name: Engineering\nmembers: [Alice, Bob, Charlie]\nactive: true"
  match parseAs Team yaml with
  | .ok team =>
      IO.println s!"✓ Parsed team:"
      IO.println s!"  Name: {team.name}"
      IO.println s!"  Members: {team.members}"
      IO.println s!"  Active: {team.active}"
  | .error msg =>
      IO.println s!"✗ Error: {msg}"
      IO.Process.exit 1

/-! ## Main Runner -/

def main : IO Unit := do
  IO.println "=== Simple Configuration ==="
  testServerConfig

  IO.println "\n=== Nested Structures ==="
  testNestedConfig

  IO.println "\n=== Optional Fields ==="
  testOptionalFields

  IO.println "\n=== Array Fields ==="
  testArrayFields

  IO.println "\n✅ All struct examples completed!"

end StructExamples

-- Top-level main function for the executable
def main : IO Unit := StructExamples.main
