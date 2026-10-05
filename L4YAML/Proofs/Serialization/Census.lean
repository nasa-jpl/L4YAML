/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.Composition
import L4YAML.Scanner.Scanner

/-!
# SerializationWellFormed runtime census

Fixed-input measurement only.  This file intentionally uses execution to map
the scope boundaries of the two stateful error families. The guards below
fail the build if the selected runtime behavior changes. No generalized
theorem depends on these measurements.
-/

namespace L4YAML.Proofs.Serialization.Census

open L4YAML

def classifyScan (input : String) : String :=
  match Scanner.scanFiltered input with
  | .ok _ => "scan:ok"
  | .error (.undefinedAlias name line col) =>
      s!"scan:undefinedAlias({name})@{line}:{col}"
  | .error e => s!"scan:other:{repr e}"

def classifyLoad (input : String) : String :=
  match TokenParser.parseYaml input with
  | .ok _ => "load:ok"
  | .error (.undefinedAlias name line col) =>
      s!"load:undefinedAlias({name})@{line}:{col}"
  | .error (.undeclaredTagHandle handle line col) =>
      s!"load:undeclaredTagHandle({handle})@{line}:{col}"
  | .error e => s!"load:other:{repr e}"

def rejectsUndefinedAlias (input : String) : Bool :=
  match TokenParser.parseYaml input with
  | .error (.undefinedAlias ..) => true
  | _ => false

def rejectsUndeclaredTagHandle (input : String) : Bool :=
  match TokenParser.parseYaml input with
  | .error (.undeclaredTagHandle ..) => true
  | _ => false

def aliasCases : List (String × String) := [
  ("unbound", "*x"),
  ("same-doc forward", "a: &x 1\nb: *x\n"),
  ("use-before-definition", "a: *x\nb: &x 1\n"),
  ("explicit same-doc", "---\na: &x 1\nb: *x\n"),
  ("cross-doc reset", "---\na: &x 1\n...\n---\nb: *x\n"),
  ("redefine next-doc", "---\na: &x 1\n...\n---\nb: &x 2\nc: *x\n"),
  ("self-reference seq", "&x [*x]\n"),
  ("self-reference map", "&x {a: *x}\n"),
  ("nested define then use", "a: [&x 1, *x]\n"),
  ("redefine same doc", "a: &x 1\nb: &x 2\nc: *x\n")
]

def tagCases : List (String × String) := [
  ("undeclared named", "!h!x value\n"),
  ("declared named", "%TAG !h! tag:example.com,2026:\n---\n!h!x value\n"),
  ("cross-doc reset", "%TAG !h! tag:example.com,2026:\n---\n!h!x a\n...\n---\n!h!x b\n"),
  ("builtin secondary", "!!str value\n"),
  ("builtin primary", "!local value\n"),
  ("verbatim", "!<tag:example.com,2026:x> value\n")
]


#guard rejectsUndefinedAlias "&x [*x]\n"
#guard rejectsUndefinedAlias "&x {a: *x}\n"
#guard rejectsUndefinedAlias "&x\n- *x\n"
#guard (TokenParser.parseYaml "[&x 1, *x]\n").isOk
#guard rejectsUndefinedAlias "*x"
#guard rejectsUndeclaredTagHandle "!h!x value\n"
#guard (TokenParser.parseYaml "%TAG !h! tag:example.com,2026:\n---\n!h!x value\n").isOk

end L4YAML.Proofs.Serialization.Census
