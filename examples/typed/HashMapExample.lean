import LeanYaml
import Std.Data.HashMap

/-!
# HashMap Example

Demonstrates using Std.HashMap with the lean4-yaml library.

HashMap support enables parsing dynamic key-value configurations where
keys aren't known at compile time.
-/

open LeanYaml
open LeanYaml.Schema

/-! ## Example 1: Simple Configuration Dictionary -/

def yamlConfig : String := "
host: localhost
port: '8080'
timeout: '30'
debug: 'true'
"

def example1 : IO Unit := do
  IO.println "=== Example 1: Simple Configuration Dictionary ==="
  match parseAs (Std.HashMap String String) yamlConfig with
  | Except.ok (config : Std.HashMap String String) =>
      IO.println "Configuration loaded:"
      for (key, value) in config.toList do
        IO.println s!"  {key}: {value}"
  | .error msg =>
      IO.println s!"Error: {msg}"
  IO.println ""

/-! ## Example 2: Nested HashMap with Arrays -/

-- HashMap where values are arrays
def yamlUsers : String := "
admin: [alice, bob]
users: [charlie, dave, eve]
guests: [frank]
"

def example2 : IO Unit := do
  IO.println "=== Example 2: HashMap with Array Values ==="
  match parseAs (Std.HashMap String (Array String)) yamlUsers with
  | Except.ok (groups : Std.HashMap String (Array String)) =>
      IO.println "User groups:"
      for (group, members) in groups.toList do
        IO.println s!"  {group}: {members.toList}"
  | .error msg =>
      IO.println s!"Error: {msg}"
  IO.println ""

/-! ## Example 3: Nested HashMap (HashMap of HashMap) -/

def yamlNested : String := "
config:
  host: localhost
  port: '8080'
database:
  host: db.example.com
  port: '5432'
  user: admin
"

def example3 : IO Unit := do
  IO.println "=== Example 3: Nested HashMap (HashMap of HashMap) ==="
  match parseAs (Std.HashMap String (Std.HashMap String String)) yamlNested with
  | Except.ok (nested : Std.HashMap String (Std.HashMap String String)) =>
      IO.println "Nested configuration:"
      for (sec, values) in nested.toList do
        IO.println s!"  {sec}:"
        for (key, value) in values.toList do
          IO.println s!"    {key}: {value}"
  | .error msg =>
      IO.println s!"Error: {msg}"
  IO.println ""

/-! ## Example 4: Integer Keys (converted from strings) -/

def yamlScores : String := "{'100': Alice, '95': Bob, '87': Charlie, '92': Dave}"

def example4 : IO Unit := do
  IO.println "=== Example 4: String Keys (that look like numbers) ==="
  match parseAs (Std.HashMap String String) yamlScores with
  | Except.ok (scores : Std.HashMap String String) =>
      IO.println "Scores:"
      for (score, name) in scores.toList do
        IO.println s!"  {score}: {name}"
  | .error msg =>
      IO.println s!"Error: {msg}"
  IO.println ""

/-! ## Example 5: Dynamic Plugin Configuration -/

-- Real-world use case: plugin system with dynamic configs
def yamlPlugins : String := "
logger:
  enabled: 'true'
  level: debug
cache:
  enabled: 'true'
  ttl: '3600'
auth:
  enabled: 'false'
  provider: oauth
"

-- Since plugin configs are heterogeneous, use HashMap String String
-- Each plugin can parse its own config later
def example5 : IO Unit := do
  IO.println "=== Example 5: Dynamic Plugin Configuration ==="
  match parseAs (Std.HashMap String (Std.HashMap String String)) yamlPlugins with
  | Except.ok (plugins : Std.HashMap String (Std.HashMap String String)) =>
      IO.println "Plugins:"
      for (plugin, config) in plugins.toList do
        IO.println s!"  {plugin}:"
        for (key, value) in config.toList do
          IO.println s!"    {key}: {value}"
  | .error msg =>
      IO.println s!"Error: {msg}"
  IO.println ""

def main : IO Unit := do
  example1
  example2
  example3
  example4
  example5
  IO.println "✅ All HashMap examples complete!"
