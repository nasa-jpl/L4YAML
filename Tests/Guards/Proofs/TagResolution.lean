import L4YAML.TokenParser

/-!
# %TAG Directive Resolution Guards (§6.8.2)

Compile-time guards verifying that `%TAG` handle declarations
are correctly wired to tag expansion during parsing.

## Organization

- §1: `resolveTag` unit tests
- §2: Spec example 6.16 — named handle `!yaml!`
- §3: Spec example 6.18 — primary handle override `%TAG ! ...`
- §4: Spec example 6.19 — secondary handle override `%TAG !! ...`
- §5: Spec example 6.20 — named handle `!e!`
- §6: Spec example 6.21 — multi-document `!m!`
- §7: Spec example 2.24 — global tags `%TAG ! tag:clarkevans.com,2002:`
- §8: Spec example 6.26 — mixed tag shorthands
- §9: Default handles (no %TAG): `!!str`, `!local`
-/

open L4YAML.TokenParser

namespace Tests.Guards.Proofs.TagResolution

/-! ## §1: resolveTag unit tests -/

-- Verbatim tag: pass through suffix unchanged
#guard resolveTag #[] "" "tag:yaml.org,2002:str" == "tag:yaml.org,2002:str"

-- Secondary handle without %TAG override: keep shorthand
#guard resolveTag #[] "!!" "str" == "!!str"
#guard resolveTag #[] "!!" "int" == "!!int"

-- Primary handle without %TAG override: keep shorthand
#guard resolveTag #[] "!" "foo" == "!foo"

-- Named handle with declared mapping
#guard resolveTag #[("!e!", "tag:example.com,2000:app/")] "!e!" "foo" ==
  "tag:example.com,2000:app/foo"

-- Secondary handle with explicit override
#guard resolveTag #[("!!", "tag:example.com,2000:app/")] "!!" "int" ==
  "tag:example.com,2000:app/int"

-- Primary handle with explicit override
#guard resolveTag #[("!", "!foo")] "!" "bar" == "!foobar"

-- Named handle `!yaml!`
#guard resolveTag #[("!yaml!", "tag:yaml.org,2002:")] "!yaml!" "str" ==
  "tag:yaml.org,2002:str"

-- Named handle `!m!`
#guard resolveTag #[("!m!", "!my-")] "!m!" "light" == "!my-light"

-- Empty suffix with secondary handle
#guard resolveTag #[] "!!" "" == "!!"

-- Empty suffix with named handle
#guard resolveTag #[("!e!", "tag:example.com,2000:app/")] "!e!" "" ==
  "tag:example.com,2000:app/"

/-! ## §2: Spec Example 6.16 — "TAG" directive with `!yaml!` -/

-- %TAG !yaml! tag:yaml.org,2002:  →  !yaml!str resolves to tag:yaml.org,2002:str
#guard match parseYamlSingle "%TAG !yaml! tag:yaml.org,2002:\n---\n!yaml!str \"foo\"\n" with
  | .ok (.scalar s) => s.tag == some "tag:yaml.org,2002:str" && s.content == "foo"
  | _ => false

/-! ## §3: Spec Example 6.18 — primary handle override -/

-- Without %TAG: !foo stays as !foo (local tag)
#guard match parseYamlSingle "!foo \"bar\"\n" with
  | .ok (.scalar s) => s.tag == some "!foo"
  | _ => false

-- With %TAG ! tag:example.com,2000:app/: !foo resolves to tag:example.com,2000:app/foo
#guard match parseYamlSingle "%TAG ! tag:example.com,2000:app/\n---\n!foo \"bar\"\n" with
  | .ok (.scalar s) => s.tag == some "tag:example.com,2000:app/foo" && s.content == "bar"
  | _ => false

/-! ## §4: Spec Example 6.19 — secondary handle override -/

-- %TAG !! tag:example.com,2000:app/  →  !!int resolves to tag:example.com,2000:app/int
#guard match parseYamlSingle "%TAG !! tag:example.com,2000:app/\n---\n!!int 1 - 3\n" with
  | .ok (.scalar s) => s.tag == some "tag:example.com,2000:app/int"
  | _ => false

/-! ## §5: Spec Example 6.20 — named handle `!e!` -/

-- %TAG !e! tag:example.com,2000:app/  →  !e!foo resolves to tag:example.com,2000:app/foo
#guard match parseYamlSingle "%TAG !e! tag:example.com,2000:app/\n---\n!e!foo \"bar\"\n" with
  | .ok (.scalar s) => s.tag == some "tag:example.com,2000:app/foo" && s.content == "bar"
  | _ => false

/-! ## §6: Spec Example 6.21 — multi-document `!m!` -/

-- %TAG !m! !my-  →  !m!light resolves to !my-light (both documents)
#guard match parseYaml "%TAG !m! !my-\n--- # Bulb here\n!m!light fluorescent\n...\n%TAG !m! !my-\n--- # Color here\n!m!light green\n" with
  | .ok docs =>
    docs.size == 2 &&
    match docs[0]!.value with
    | .scalar s => s.tag == some "!my-light" && s.content == "fluorescent"
    | _ => false
    &&
    match docs[1]!.value with
    | .scalar s => s.tag == some "!my-light" && s.content == "green"
    | _ => false
  | .error _ => false

/-! ## §7: Spec Example 2.24 — global tags -/

-- %TAG ! tag:clarkevans.com,2002:  →  !shape resolves to tag:clarkevans.com,2002:shape
#guard match parseYaml "%TAG ! tag:clarkevans.com,2002:\n--- !shape\n- !circle\n  center: &ORIGIN {x: 73, y: 129}\n  radius: 7\n- !line\n  start: *ORIGIN\n  finish: { x: 89, y: 102 }\n- !label\n  start: *ORIGIN\n  color: 0xFFEEBB\n  text: Pretty vector drawing.\n" with
  | .ok docs =>
    docs.size == 1 &&
    match docs[0]!.value with
    | .sequence _ items tag _ =>
      tag == some "tag:clarkevans.com,2002:shape" &&
      items.size == 3 &&
      match items[0]! with
      | .mapping _ _ tag _ => tag == some "tag:clarkevans.com,2002:circle"
      | _ => false
    | _ => false
  | .error _ => false

/-! ## §8: Spec Example 6.26 — mixed tag shorthands -/

-- %TAG !e! tag:example.com,2000:app/
-- - !local foo          → tag = "!local"
-- - !!str bar           → tag = "!!str" (no %TAG !! override)
-- - !e!tag%21 baz       → tag = "tag:example.com,2000:app/tag%21"
#guard match parseYaml "%TAG !e! tag:example.com,2000:app/\n---\n- !local foo\n- !!str bar\n- !e!tag%21 baz\n" with
  | .ok docs =>
    docs.size == 1 &&
    match docs[0]!.value with
    | .sequence _ items _ _ =>
      items.size == 3 &&
      match items[0]!, items[1]!, items[2]! with
      | .scalar s0, .scalar s1, .scalar s2 =>
        s0.tag == some "!local" && s0.content == "foo" &&
        s1.tag == some "!!str" && s1.content == "bar" &&
        s2.tag == some "tag:example.com,2000:app/tag%21" && s2.content == "baz"
      | _, _, _ => false
    | _ => false
  | .error _ => false

/-! ## §9: Default handles (no %TAG): shorthand form preserved -/

-- !!str without %TAG → stays !!str
#guard match parseYamlSingle "!!str foo\n" with
  | .ok (.scalar s) => s.tag == some "!!str"
  | _ => false

-- !local without %TAG → stays !local
#guard match parseYamlSingle "!local foo\n" with
  | .ok (.scalar s) => s.tag == some "!local"
  | _ => false

-- !!int without %TAG → stays !!int
#guard match parseYamlSingle "!!int 42\n" with
  | .ok (.scalar s) => s.tag == some "!!int"
  | _ => false

-- Verbatim tag → always passes through as-is
#guard match parseYamlSingle "!<tag:yaml.org,2002:str> foo\n" with
  | .ok (.scalar s) => s.tag == some "tag:yaml.org,2002:str"
  | _ => false

end Tests.Guards.Proofs.TagResolution
