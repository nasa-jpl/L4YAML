/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.Composition

/-!
# yaml-test-suite Compile-Time Guards — Document Stage

Auto-generated from yaml-test-suite test files by `gen-suite-guards.py`.
Each `#guard` is evaluated by Lean's kernel during `lake build`.

**15 guards** covering all passing document tests.

These are Phase 4 of the verification plan: yaml-test-suite as compile-time proofs.
-/

namespace L4YAML.Proofs.SuiteGuards.Document

open L4YAML.TokenParser

-- 6XDY:0 Two document start markers
#guard match parseYaml "---\n---\n" with
  | .ok _ => true
  | .error _ => false

-- 7Z25:0 Bare document after document end marker
#guard match parseYaml "---\nscalar1\n...\nkey: value\n" with
  | .ok _ => true
  | .error _ => false

-- BEC7:0 Spec Example 6.14. “YAML” directive
#guard match parseYaml "%YAML 1.3 # Attempt parsing\n          # with a warning\n---\n\"foo\"\n" with
  | .ok _ => true
  | .error _ => false

-- HWV9:0 Document-end marker
#guard match parseYaml "...\n" with
  | .ok _ => true
  | .error _ => false

-- JHB9:0 Spec Example 2.7. Two Documents in a Stream
#guard match parseYaml "# Ranking of 1998 home runs\n---\n- Mark McGwire\n- Sammy Sosa\n- Ken Griffey\n\n# Team ranking\n---\n- Chicago Cubs\n- St Louis Cardinals\n" with
  | .ok _ => true
  | .error _ => false

-- K54U:0 Tab after document header
#guard match parseYaml "---\tscalar\n" with
  | .ok _ => true
  | .error _ => false

-- PUW8:0 Document start on last line
#guard match parseYaml "---\na: b\n---\n" with
  | .ok _ => true
  | .error _ => false

-- QT73:0 Comment and document-end marker
#guard match parseYaml "# comment\n...\n" with
  | .ok _ => true
  | .error _ => false

-- RTP8:0 Spec Example 9.2. Document Markers
#guard match parseYaml "%YAML 1.2\n---\nDocument\n... # Suffix\n" with
  | .ok _ => true
  | .error _ => false

-- RZT7:0 Spec Example 2.28. Log File
#guard match parseYaml "---\nTime: 2001-11-23 15:01:42 -5\nUser: ed\nWarning:\n  This is an error message\n  for the log file\n---\nTime: 2001-11-23 15:02:31 -5\nUser: ed\nWarning:\n  A slightly different error\n  message.\n---\nDate: 2001-11-23 15:03:17 -5\nUser: ed\nFatal:\n  Unknown variable \"bar\"\nStack:\n  - file: TopClass.py\n    line: 23\n    code: |\n      x = MoreObject(\"345\\n\")\n  - file: MoreClass.py\n    line: 58\n    code: |-\n      foo = bar\n" with
  | .ok _ => true
  | .error _ => false

-- S4T7:0 Document with footer
#guard match parseYaml "aaa: bbb\n...\n" with
  | .ok _ => true
  | .error _ => false

-- U9NS:0 Spec Example 2.8. Play by Play Feed from a Game
#guard match parseYaml "---\ntime: 20:03:20\nplayer: Sammy Sosa\naction: strike (miss)\n...\n---\ntime: 20:03:47\nplayer: Sammy Sosa\naction: grand slam\n...\n" with
  | .ok _ => true
  | .error _ => false

-- UT92:0 Spec Example 9.4. Explicit Documents
#guard match parseYaml "---\n{ matches\n% : 20 }\n...\n---\n# Empty\n...\n" with
  | .ok _ => true
  | .error _ => false

-- XLQ9:0 Multiline scalar that looks like a YAML directive
#guard match parseYaml "---\nscalar\n%YAML 1.2\n" with
  | .ok _ => true
  | .error _ => false

-- ZYU8:0 Directive variants
#guard match parseYaml "%YAML1.1\n---\n" with
  | .ok _ => true
  | .error _ => false

end L4YAML.Proofs.SuiteGuards.Document
