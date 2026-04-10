import L4YAML.Proofs.FoldNewlines

namespace L4YAML.Proofs.FoldNewlines

open L4YAML.Grammar
open L4YAML.TokenParser

private def parseScalar (s : String) : Option String :=
  match parseYamlSingle s with
  | .ok (.scalar node) => some node.content
  | _ => none

-- Single line break in double-quoted scalar folds to space
#guard parseScalar "\"hello\nworld\"" == some "hello world"

-- Single line break in single-quoted scalar folds to space
#guard parseScalar "'hello\nworld'" == some "hello world"

-- Blank line in double-quoted scalar preserves newline
#guard parseScalar "\"hello\n\nworld\"" == some "hello\nworld"

-- Multiple blank lines preserve multiple newlines
#guard parseScalar "\"hello\n\n\nworld\"" == some "hello\n\nworld"

-- Trailing whitespace is trimmed before folding
#guard parseScalar "\"hello   \nworld\"" == some "hello world"

-- Leading whitespace on continuation line is consumed
#guard parseScalar "\"hello\n  world\"" == some "hello world"

-- Escaped newline (backslash continuation) — no space inserted
#guard parseScalar "\"hello\\\nworld\"" == some "helloworld"

-- Tab in content is preserved
#guard parseScalar "\"hello\tworld\"" == some "hello\tworld"

-- c-forbidden: `---` on continuation line in double-quoted
-- (Parser detects as validation error, falls back)
#guard parseScalar "\"hello\n---\nworld\"" != some "hello world"

-- c-forbidden: `...` on continuation line in double-quoted
#guard parseScalar "\"hello\n...\nworld\"" != some "hello world"

-- Normal fold with document markers NOT at column 0 (inside indented content)
#guard parseScalar "\"hello\n  ---world\"" == some "hello ---world"

-- Empty double-quoted scalar
#guard parseScalar "\"\"" == some ""

-- Single character double-quoted
#guard parseScalar "\"a\"" == some "a"

-- Single-quoted with escaped quote
#guard parseScalar "'it''s'" == some "it's"

-- Fold in single-quoted scalar with blank lines
#guard parseScalar "'hello\n\nworld'" == some "hello\nworld"

end L4YAML.Proofs.FoldNewlines
