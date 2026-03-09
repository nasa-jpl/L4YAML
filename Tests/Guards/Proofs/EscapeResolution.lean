import Lean4Yaml.Proofs.EscapeResolution

namespace Lean4Yaml.Proofs.EscapeResolution

open Lean4Yaml.Grammar
open Lean4Yaml.TokenParser

private def parseScalar (s : String) : Option String :=
  match parseYamlSingle s with
  | .ok (.scalar node) => some node.content
  | _ => none

-- Named escape round-trips through the parser
#guard parseScalar "\"\\0\"" == some "\x00"      -- \0 → null
#guard parseScalar "\"\\a\"" == some "\x07"      -- \a → bell
#guard parseScalar "\"\\b\"" == some "\x08"      -- \b → backspace
#guard parseScalar "\"\\t\"" == some "\t"        -- \t → tab
#guard parseScalar "\"\\n\"" == some "\n"        -- \n → line feed
#guard parseScalar "\"\\v\"" == some "\x0b"      -- \v → vertical tab
#guard parseScalar "\"\\f\"" == some "\x0c"      -- \f → form feed
#guard parseScalar "\"\\r\"" == some "\r"        -- \r → carriage return
#guard parseScalar "\"\\e\"" == some "\x1b"      -- \e → escape
#guard parseScalar "\"\\ \"" == some " "         -- \<space> → space
#guard parseScalar "\"\\\"\"" == some "\""       -- \" → double quote
#guard parseScalar "\"\\/\"" == some "/"         -- \/ → slash
#guard parseScalar "\"\\\\\"" == some "\\"       -- \\ → backslash
#guard parseScalar "\"\\N\"" == some "\x85"      -- \N → NEL
#guard parseScalar "\"\\_\"" == some "\xa0"      -- \_ → NBSP

-- Hex unicode escapes
#guard parseScalar "\"\\x41\"" == some "A"       -- \x41 → 'A'
#guard parseScalar "\"\\u0041\"" == some "A"     -- \u0041 → 'A'
#guard parseScalar "\"\\U00000041\"" == some "A" -- \U00000041 → 'A'
#guard parseScalar "\"\\u03B1\"" == some "α"     -- \u03B1 → 'α' (Greek alpha)
#guard parseScalar "\"\\uFFFD\"" == some "\uFFFD" -- \uFFFD → replacement char

end Lean4Yaml.Proofs.EscapeResolution
