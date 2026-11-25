/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Parser.Composition

public meta import L4YAML.Parser.Composition
public import L4YAML.Scanner.Scanner

@[expose] public section Blanket

/-!
# SerializationWellFormed runtime census

Fixed-input measurement only.  This file intentionally uses execution to map
the scope boundaries of the two stateful error families. The guards below
fail the build if the selected runtime behavior changes. No generalized
theorem depends on these measurements.
-/

namespace L4YAML.Proofs.Serialization.Census

open L4YAML

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


-- §3.2.2.2 binds an alias to the most recent EVENT carrying the anchor, and for
-- a collection that is its START, so a node may name the anchor of the
-- collection it sits inside.  §7.1's only error is an anchor that does not
-- previously OCCUR, and these three occur.  `YamlValue` expresses sharing by
-- substitution alone, so the load preserves the `.alias` instead of unrolling
-- it; `Tests/Guards/Proofs/AliasNodeRoute.lean` carries that shape to the
-- capstone's own conclusion.
#guard classifyLoad "&x [*x]\n" == "load:ok"
#guard classifyLoad "&x {a: *x}\n" == "load:ok"
#guard classifyLoad "&x\n- *x\n" == "load:ok"
#guard (TokenParser.parseYaml "[&x 1, *x]\n").isOk
-- an anchor that has NOT occurred is still refused, which is the whole of §7.1
#guard rejectsUndefinedAlias "*x"
#guard rejectsUndefinedAlias "[*x]"
#guard rejectsUndefinedAlias "[*x, &x a]"
#guard rejectsUndefinedAlias "&x a\n---\n*x\n"
#guard rejectsUndeclaredTagHandle "!h!x value\n"
#guard (TokenParser.parseYaml "%TAG !h! tag:example.com,2026:\n---\n!h!x value\n").isOk

end L4YAML.Proofs.Serialization.Census

end Blanket
