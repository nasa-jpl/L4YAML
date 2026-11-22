module

public import L4YAML.Proofs.Errors.EscapeResolution


public meta import L4YAML.Parser.Composition
@[expose] public section Blanket

namespace L4YAML.Proofs.EscapeResolution

open L4YAML.Grammar
open L4YAML.TokenParser

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

-- Surrogate escapes are rejected (§4 of the module docstring).  A lone surrogate is not a
-- Unicode scalar value, so it cannot be a character of any scalar; `parseHexEscape` guards on
-- `Nat.isValidChar`, which is `Char.ofNat`'s own precondition.  Before 2026-08-11 the guard was
-- the weaker `< 0x110000`, so each of these was *accepted* and decoded to U+0000 via
-- `Char.ofNat`'s substituting else-branch — silent corruption, not an error.
#guard parseScalar "\"\\ud800\"" == none        -- first surrogate
#guard parseScalar "\"\\udfff\"" == none        -- last surrogate
#guard parseScalar "\"\\udbff\"" == none        -- mid-block high surrogate
#guard parseScalar "\"\\U0000d800\"" == none    -- same code point, 8-digit form
#guard parseScalar "\"\\uD83D\\uDE00\"" == none -- a UTF-16 pair is still two lone surrogates

-- …and the block is a hole, not a ceiling: both neighbours and the top of the range decode.
#guard parseScalar "\"\\ud7ff\"" == some "\ud7ff"           -- one below the block
#guard parseScalar "\"\\ue000\"" == some "\ue000"           -- one above the block
#guard parseScalar "\"\\U0010FFFF\"" == some (String.singleton (Char.ofNat 0x10FFFF))
#guard parseScalar "\"\\U00110000\"" == none                -- past the end (unchanged)

end L4YAML.Proofs.EscapeResolution

end Blanket
