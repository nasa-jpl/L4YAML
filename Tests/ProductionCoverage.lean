import L4YAML.TokenParser
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Automated Production Coverage Analysis

Compile-time automated analysis of YAML 1.2.2 production rule coverage.
Programmatically queries the `@[yaml_spec]` environment extension to build
a real coverage matrix, and generates an HTML report linking each YAML 1.2.2
production to its corresponding Lean source code.

## How it works

1. All 205 YAML 1.2.2 productions are cataloged (static — defines the spec)
2. At **elaboration time**, `@[yaml_spec]` annotations are queried from the
   Lean environment via `getAllYamlSpecDecls`
3. Module names are resolved via `env.getModuleIdxFor?` for source links
4. The coverage matrix is cross-referenced automatically
5. An HTML report can be generated linking productions → spec URLs → source code
-/

namespace Tests.ProdCoverage

open Lean L4YAML
open Tests

/-! ## YAML 1.2.2 Production Catalog

The complete list of YAML 1.2.2 productions. This is static data from
the specification — it doesn't change. -/

/-- A YAML 1.2.2 production from the specification. -/
structure YamlProduction where
  number : Nat
  name : String
  chapter : String       -- e.g., "5", "6", "7", "8", "9"
  specSec : String       -- e.g., "5.1", "6.1", "7.3.1"
  status : String        -- "GP" | "P" | "G" | "OOS" (out of scope)
  deriving Repr, Inhabited

/-- All 211 YAML 1.2.2 productions (numbers 1–211). -/
def yamlProductions : Array YamlProduction := #[
  -- Chapter 5: Character Productions (5.1–5.7)
  { number := 1,   name := "c-printable",                       chapter := "5", specSec := "5.1",   status := "G" },
  { number := 2,   name := "nb-json",                           chapter := "5", specSec := "5.1",   status := "G" },
  { number := 3,   name := "c-byte-order-mark",                 chapter := "5", specSec := "5.2",   status := "P" },
  { number := 4,   name := "c-sequence-entry",                  chapter := "5", specSec := "5.3",   status := "P" },
  { number := 5,   name := "c-mapping-key",                     chapter := "5", specSec := "5.3",   status := "P" },
  { number := 6,   name := "c-mapping-value",                   chapter := "5", specSec := "5.3",   status := "P" },
  { number := 7,   name := "c-collect-entry",                   chapter := "5", specSec := "5.3",   status := "P" },
  { number := 8,   name := "c-sequence-start",                  chapter := "5", specSec := "5.3",   status := "P" },
  { number := 9,   name := "c-sequence-end",                    chapter := "5", specSec := "5.3",   status := "P" },
  { number := 10,  name := "c-mapping-start",                   chapter := "5", specSec := "5.3",   status := "P" },
  { number := 11,  name := "c-mapping-end",                     chapter := "5", specSec := "5.3",   status := "P" },
  { number := 12,  name := "c-comment",                         chapter := "5", specSec := "5.3",   status := "P" },
  { number := 13,  name := "c-anchor",                          chapter := "5", specSec := "5.3",   status := "P" },
  { number := 14,  name := "c-alias",                           chapter := "5", specSec := "5.3",   status := "P" },
  { number := 15,  name := "c-tag",                             chapter := "5", specSec := "5.3",   status := "P" },
  { number := 16,  name := "c-literal",                         chapter := "5", specSec := "5.3",   status := "P" },
  { number := 17,  name := "c-folded",                          chapter := "5", specSec := "5.3",   status := "P" },
  { number := 18,  name := "c-single-quote",                    chapter := "5", specSec := "5.3",   status := "P" },
  { number := 19,  name := "c-double-quote",                    chapter := "5", specSec := "5.3",   status := "P" },
  { number := 20,  name := "c-directive",                       chapter := "5", specSec := "5.3",   status := "P" },
  { number := 21,  name := "c-reserved",                        chapter := "5", specSec := "5.3",   status := "P" },
  { number := 22,  name := "c-indicator",                       chapter := "5", specSec := "5.3",   status := "P" },
  { number := 23,  name := "c-flow-indicator",                  chapter := "5", specSec := "5.3",   status := "GP" },
  { number := 24,  name := "b-line-feed",                       chapter := "5", specSec := "5.4",   status := "GP" },
  { number := 25,  name := "b-carriage-return",                 chapter := "5", specSec := "5.4",   status := "GP" },
  { number := 26,  name := "b-char",                            chapter := "5", specSec := "5.4",   status := "GP" },
  { number := 27,  name := "nb-char",                           chapter := "5", specSec := "5.4",   status := "GP" },
  { number := 28,  name := "b-break",                           chapter := "5", specSec := "5.4",   status := "P" },
  { number := 29,  name := "b-as-line-feed",                    chapter := "5", specSec := "5.4",   status := "P" },
  { number := 30,  name := "b-non-content",                     chapter := "5", specSec := "5.4",   status := "P" },
  { number := 31,  name := "s-space",                           chapter := "5", specSec := "5.5",   status := "GP" },
  { number := 32,  name := "s-tab",                             chapter := "5", specSec := "5.5",   status := "GP" },
  { number := 33,  name := "s-white",                           chapter := "5", specSec := "5.5",   status := "GP" },
  { number := 34,  name := "ns-char",                           chapter := "5", specSec := "5.5",   status := "GP" },
  { number := 35,  name := "ns-dec-digit",                      chapter := "5", specSec := "5.6",   status := "P" },
  { number := 36,  name := "ns-hex-digit",                      chapter := "5", specSec := "5.6",   status := "P" },
  { number := 37,  name := "ns-ascii-letter",                   chapter := "5", specSec := "5.6",   status := "GP" },
  { number := 38,  name := "ns-word-char",                      chapter := "5", specSec := "5.6",   status := "P" },
  { number := 39,  name := "ns-uri-char",                       chapter := "5", specSec := "5.6",   status := "P" },
  { number := 40,  name := "ns-tag-char",                       chapter := "5", specSec := "5.6",   status := "P" },
  { number := 41,  name := "c-escape",                          chapter := "5", specSec := "5.7",   status := "P" },
  { number := 42,  name := "ns-esc-null",                       chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 43,  name := "ns-esc-bell",                       chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 44,  name := "ns-esc-backspace",                  chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 45,  name := "ns-esc-horizontal-tab",             chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 46,  name := "ns-esc-line-feed",                  chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 47,  name := "ns-esc-vertical-tab",               chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 48,  name := "ns-esc-form-feed",                  chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 49,  name := "ns-esc-carriage-return",            chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 50,  name := "ns-esc-escape",                     chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 51,  name := "ns-esc-space",                      chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 52,  name := "ns-esc-double-quote",               chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 53,  name := "ns-esc-slash",                      chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 54,  name := "ns-esc-backslash",                  chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 55,  name := "ns-esc-next-line",                  chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 56,  name := "ns-esc-non-breaking-space",         chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 57,  name := "ns-esc-line-separator",             chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 58,  name := "ns-esc-paragraph-separator",        chapter := "5", specSec := "5.7",   status := "GP" },
  { number := 59,  name := "ns-esc-8-bit",                      chapter := "5", specSec := "5.7",   status := "P" },
  { number := 60,  name := "ns-esc-16-bit",                     chapter := "5", specSec := "5.7",   status := "P" },
  { number := 61,  name := "ns-esc-32-bit",                     chapter := "5", specSec := "5.7",   status := "P" },
  { number := 62,  name := "c-ns-esc-char",                     chapter := "5", specSec := "5.7",   status := "P" },
  -- Chapter 6: Structural Productions (6.1–6.9)
  { number := 63,  name := "s-indent(n)",                       chapter := "6", specSec := "6.1",   status := "GP" },
  { number := 64,  name := "s-indent(<n)",                      chapter := "6", specSec := "6.1",   status := "G" },
  { number := 65,  name := "s-indent(≤n)",                      chapter := "6", specSec := "6.1",   status := "G" },
  { number := 66,  name := "s-separate-in-line",                chapter := "6", specSec := "6.2",   status := "P" },
  { number := 67,  name := "s-line-prefix(n,c)",                chapter := "6", specSec := "6.3",   status := "P" },
  { number := 68,  name := "s-block-line-prefix(n)",            chapter := "6", specSec := "6.3",   status := "P" },
  { number := 69,  name := "s-flow-line-prefix(n)",             chapter := "6", specSec := "6.3",   status := "P" },
  { number := 70,  name := "l-empty(n,c)",                      chapter := "6", specSec := "6.4",   status := "P" },
  { number := 71,  name := "b-l-trimmed(n,c)",                  chapter := "6", specSec := "6.5",   status := "P" },
  { number := 72,  name := "b-as-space",                        chapter := "6", specSec := "6.5",   status := "P" },
  { number := 73,  name := "b-l-folded(n,c)",                   chapter := "6", specSec := "6.5",   status := "P" },
  { number := 74,  name := "s-flow-folded(n)",                  chapter := "6", specSec := "6.5",   status := "P" },
  { number := 75,  name := "c-nb-comment-text",                 chapter := "6", specSec := "6.6",   status := "P" },
  { number := 76,  name := "b-comment",                         chapter := "6", specSec := "6.6",   status := "P" },
  { number := 77,  name := "s-b-comment",                       chapter := "6", specSec := "6.6",   status := "P" },
  { number := 78,  name := "l-comment",                         chapter := "6", specSec := "6.7",   status := "P" },
  { number := 79,  name := "s-l-comments",                      chapter := "6", specSec := "6.7",   status := "P" },
  { number := 80,  name := "s-separate(n,c)",                   chapter := "6", specSec := "6.7",   status := "P" },
  { number := 81,  name := "s-separate-lines(n)",               chapter := "6", specSec := "6.7",   status := "P" },
  { number := 82,  name := "l-directive",                       chapter := "6", specSec := "6.8",   status := "P" },
  { number := 83,  name := "ns-reserved-directive",             chapter := "6", specSec := "6.8",   status := "P" },
  { number := 84,  name := "ns-directive-name",                 chapter := "6", specSec := "6.8",   status := "P" },
  { number := 85,  name := "ns-directive-parameter",            chapter := "6", specSec := "6.8",   status := "P" },
  { number := 86,  name := "ns-yaml-directive",                 chapter := "6", specSec := "6.8.1", status := "P" },
  { number := 87,  name := "ns-yaml-version",                   chapter := "6", specSec := "6.8.1", status := "P" },
  { number := 88,  name := "ns-tag-directive",                  chapter := "6", specSec := "6.8.2", status := "P" },
  { number := 89,  name := "c-tag-handle",                      chapter := "6", specSec := "6.8.2", status := "P" },
  { number := 90,  name := "c-primary-tag-handle",              chapter := "6", specSec := "6.8.2", status := "P" },
  { number := 91,  name := "c-secondary-tag-handle",            chapter := "6", specSec := "6.8.2", status := "P" },
  { number := 92,  name := "c-named-tag-handle",                chapter := "6", specSec := "6.8.2", status := "P" },
  { number := 93,  name := "ns-tag-prefix",                     chapter := "6", specSec := "6.8.2", status := "P" },
  { number := 94,  name := "c-ns-local-tag-prefix",             chapter := "6", specSec := "6.8.2", status := "P" },
  { number := 95,  name := "ns-global-tag-prefix",              chapter := "6", specSec := "6.8.2", status := "P" },
  { number := 96,  name := "c-ns-properties(n,c)",              chapter := "6", specSec := "6.9",   status := "P" },
  { number := 97,  name := "c-ns-tag-property",                 chapter := "6", specSec := "6.9",   status := "P" },
  { number := 98,  name := "c-verbatim-tag",                    chapter := "6", specSec := "6.9",   status := "P" },
  { number := 99,  name := "c-ns-shorthand-tag",                chapter := "6", specSec := "6.9",   status := "P" },
  { number := 100, name := "c-non-specific-tag",                chapter := "6", specSec := "6.9",   status := "P" },
  { number := 101, name := "c-ns-anchor-property",              chapter := "6", specSec := "6.9",   status := "P" },
  { number := 102, name := "ns-anchor-char",                    chapter := "6", specSec := "6.9",   status := "P" },
  { number := 103, name := "ns-anchor-name",                    chapter := "6", specSec := "6.9",   status := "P" },
  -- Chapter 7: Flow Style Productions (7.1–7.5)
  { number := 104, name := "c-ns-alias-node",                   chapter := "7", specSec := "7.1",   status := "P" },
  { number := 105, name := "e-scalar",                          chapter := "7", specSec := "7.2",   status := "P" },
  { number := 106, name := "e-node",                            chapter := "7", specSec := "7.2",   status := "P" },
  { number := 107, name := "nb-double-char",                    chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 108, name := "ns-double-char",                    chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 109, name := "c-double-quoted(n,c)",              chapter := "7", specSec := "7.3.1", status := "GP" },
  { number := 110, name := "nb-double-text(n,c)",               chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 111, name := "nb-double-one-line",                chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 112, name := "s-double-escaped(n)",               chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 113, name := "s-double-break(n)",                 chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 114, name := "nb-ns-double-in-line",              chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 115, name := "s-double-next-line(n)",             chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 116, name := "nb-double-multi-line(n)",           chapter := "7", specSec := "7.3.1", status := "P" },
  { number := 117, name := "c-quoted-quote",                    chapter := "7", specSec := "7.3.2", status := "P" },
  { number := 118, name := "nb-single-char",                    chapter := "7", specSec := "7.3.2", status := "P" },
  { number := 119, name := "ns-single-char",                    chapter := "7", specSec := "7.3.2", status := "P" },
  { number := 120, name := "c-single-quoted(n,c)",              chapter := "7", specSec := "7.3.2", status := "GP" },
  { number := 121, name := "nb-single-text(n,c)",               chapter := "7", specSec := "7.3.2", status := "P" },
  { number := 122, name := "nb-single-one-line",                chapter := "7", specSec := "7.3.2", status := "P" },
  { number := 123, name := "nb-ns-single-in-line",              chapter := "7", specSec := "7.3.2", status := "P" },
  { number := 124, name := "s-single-next-line(n)",             chapter := "7", specSec := "7.3.2", status := "P" },
  { number := 125, name := "nb-single-multi-line(n)",           chapter := "7", specSec := "7.3.2", status := "P" },
  { number := 126, name := "ns-plain-first(c)",                 chapter := "7", specSec := "7.3.3", status := "GP" },
  { number := 127, name := "ns-plain-safe(c)",                  chapter := "7", specSec := "7.3.3", status := "P" },
  { number := 128, name := "ns-plain-safe-out",                 chapter := "7", specSec := "7.3.3", status := "P" },
  { number := 129, name := "ns-plain-safe-in",                  chapter := "7", specSec := "7.3.3", status := "P" },
  { number := 130, name := "ns-plain-char(c)",                  chapter := "7", specSec := "7.3.3", status := "P" },
  { number := 131, name := "ns-plain(n,c)",                     chapter := "7", specSec := "7.3.3", status := "GP" },
  { number := 132, name := "nb-ns-plain-in-line(c)",            chapter := "7", specSec := "7.3.3", status := "P" },
  { number := 133, name := "ns-plain-one-line(c)",              chapter := "7", specSec := "7.3.3", status := "P" },
  { number := 134, name := "s-ns-plain-next-line(n,c)",         chapter := "7", specSec := "7.3.3", status := "P" },
  { number := 135, name := "ns-plain-multi-line(n,c)",          chapter := "7", specSec := "7.3.3", status := "P" },
  { number := 136, name := "in-flow(c)",                        chapter := "7", specSec := "7.4",   status := "P" },
  { number := 137, name := "c-flow-sequence(n,c)",              chapter := "7", specSec := "7.4.1", status := "GP" },
  { number := 138, name := "ns-s-flow-seq-entries(n,c)",        chapter := "7", specSec := "7.4.1", status := "P" },
  { number := 139, name := "ns-flow-seq-entry(n,c)",            chapter := "7", specSec := "7.4.1", status := "P" },
  { number := 140, name := "c-flow-mapping(n,c)",               chapter := "7", specSec := "7.4.2", status := "GP" },
  { number := 141, name := "ns-s-flow-map-entries(n,c)",        chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 142, name := "ns-flow-map-entry(n,c)",            chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 143, name := "ns-flow-map-explicit-entry(n,c)",   chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 144, name := "ns-flow-map-implicit-entry(n,c)",   chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 145, name := "ns-flow-map-yaml-key-entry(n,c)",   chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 146, name := "c-ns-flow-map-empty-key-entry(n,c)", chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 147, name := "c-ns-flow-map-separate-value(n,c)", chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 148, name := "c-ns-flow-map-json-key-entry(n,c)", chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 149, name := "c-ns-flow-map-adjacent-value(n,c)", chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 150, name := "ns-flow-pair(n,c)",                 chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 151, name := "ns-flow-pair-entry(n,c)",           chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 152, name := "ns-flow-pair-yaml-key-entry(n,c)",  chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 153, name := "c-ns-flow-pair-json-key-entry(n,c)", chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 154, name := "ns-s-implicit-yaml-key(c)",         chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 155, name := "c-s-implicit-json-key(c)",          chapter := "7", specSec := "7.4.2", status := "P" },
  { number := 156, name := "ns-flow-yaml-content(n,c)",         chapter := "7", specSec := "7.5",   status := "P" },
  { number := 157, name := "c-flow-json-content(n,c)",          chapter := "7", specSec := "7.5",   status := "P" },
  { number := 158, name := "ns-flow-content(n,c)",              chapter := "7", specSec := "7.5",   status := "P" },
  { number := 159, name := "ns-flow-yaml-node(n,c)",            chapter := "7", specSec := "7.5",   status := "P" },
  { number := 160, name := "c-flow-json-node(n,c)",             chapter := "7", specSec := "7.5",   status := "P" },
  { number := 161, name := "ns-flow-node(n,c)",                 chapter := "7", specSec := "7.5",   status := "P" },
  -- Chapter 8: Block Style Productions (8.1–8.2)
  { number := 162, name := "c-b-block-header(t)",               chapter := "8", specSec := "8.1.1", status := "GP" },
  { number := 163, name := "c-indentation-indicator",           chapter := "8", specSec := "8.1.1", status := "GP" },
  { number := 164, name := "c-chomping-indicator(t)",           chapter := "8", specSec := "8.1.1", status := "GP" },
  { number := 165, name := "b-chomped-last(t)",                 chapter := "8", specSec := "8.1.1", status := "P" },
  { number := 166, name := "l-chomped-empty(n,t)",              chapter := "8", specSec := "8.1.1", status := "P" },
  { number := 167, name := "l-strip-empty(n)",                  chapter := "8", specSec := "8.1.1", status := "P" },
  { number := 168, name := "l-keep-empty(n)",                   chapter := "8", specSec := "8.1.1", status := "P" },
  { number := 169, name := "l-trail-comments(n)",               chapter := "8", specSec := "8.1.1", status := "P" },
  { number := 170, name := "c-l+literal(n)",                    chapter := "8", specSec := "8.1.2", status := "GP" },
  { number := 171, name := "l-nb-literal-text(n)",              chapter := "8", specSec := "8.1.2", status := "P" },
  { number := 172, name := "b-nb-literal-next(n)",              chapter := "8", specSec := "8.1.2", status := "P" },
  { number := 173, name := "l-literal-content(n,t)",            chapter := "8", specSec := "8.1.2", status := "P" },
  { number := 174, name := "c-l+folded(n)",                     chapter := "8", specSec := "8.1.3", status := "GP" },
  { number := 175, name := "s-nb-folded-text(n)",               chapter := "8", specSec := "8.1.3", status := "P" },
  { number := 176, name := "l-nb-folded-lines(n)",              chapter := "8", specSec := "8.1.3", status := "P" },
  { number := 177, name := "s-nb-spaced-text(n)",               chapter := "8", specSec := "8.1.3", status := "P" },
  { number := 178, name := "b-l-spaced(n)",                     chapter := "8", specSec := "8.1.3", status := "P" },
  { number := 179, name := "l-nb-spaced-lines(n)",              chapter := "8", specSec := "8.1.3", status := "P" },
  { number := 180, name := "l-nb-same-lines(n)",                chapter := "8", specSec := "8.1.3", status := "P" },
  { number := 181, name := "l-nb-diff-lines(n)",                chapter := "8", specSec := "8.1.3", status := "P" },
  { number := 182, name := "l-folded-content(n,t)",             chapter := "8", specSec := "8.1.3", status := "P" },
  { number := 183, name := "l+block-sequence(n)",               chapter := "8", specSec := "8.2.1", status := "GP" },
  { number := 184, name := "c-l-block-seq-entry(n)",            chapter := "8", specSec := "8.2.1", status := "P" },
  { number := 185, name := "s-l+block-indented(n,c)",           chapter := "8", specSec := "8.2.1", status := "P" },
  { number := 186, name := "ns-l-compact-sequence(n)",          chapter := "8", specSec := "8.2.1", status := "P" },
  { number := 187, name := "l+block-mapping(n)",                chapter := "8", specSec := "8.2.2", status := "GP" },
  { number := 188, name := "ns-l-block-map-entry(n)",           chapter := "8", specSec := "8.2.2", status := "P" },
  { number := 189, name := "c-l-block-map-explicit-entry(n)",   chapter := "8", specSec := "8.2.2", status := "P" },
  { number := 190, name := "c-l-block-map-explicit-key(n)",     chapter := "8", specSec := "8.2.2", status := "P" },
  { number := 191, name := "l-block-map-explicit-value(n)",     chapter := "8", specSec := "8.2.2", status := "P" },
  { number := 192, name := "ns-l-block-map-implicit-entry(n)",  chapter := "8", specSec := "8.2.2", status := "P" },
  { number := 193, name := "ns-s-block-map-implicit-key",       chapter := "8", specSec := "8.2.2", status := "P" },
  { number := 194, name := "c-l-block-map-implicit-value(n)",   chapter := "8", specSec := "8.2.2", status := "P" },
  { number := 195, name := "ns-l-compact-mapping(n)",           chapter := "8", specSec := "8.2.2", status := "P" },
  { number := 196, name := "s-l+block-node(n,c)",               chapter := "8", specSec := "8.2.3", status := "P" },
  { number := 197, name := "s-l+flow-in-block(n)",              chapter := "8", specSec := "8.2.3", status := "P" },
  { number := 198, name := "s-l+block-in-block(n,c)",           chapter := "8", specSec := "8.2.3", status := "P" },
  { number := 199, name := "s-l+block-scalar(n,c)",             chapter := "8", specSec := "8.2.3", status := "P" },
  { number := 200, name := "s-l+block-collection(n,c)",         chapter := "8", specSec := "8.2.3", status := "P" },
  { number := 201, name := "seq-space(n,c)",                    chapter := "8", specSec := "8.2.1", status := "P" },
  -- Chapter 9: Document Stream Productions (9.1–9.2)
  { number := 202, name := "l-document-prefix",                 chapter := "9", specSec := "9.1.1", status := "P" },
  { number := 203, name := "c-directives-end",                  chapter := "9", specSec := "9.1.2", status := "P" },
  { number := 204, name := "c-document-end",                    chapter := "9", specSec := "9.1.2", status := "P" },
  { number := 205, name := "l-document-suffix",                 chapter := "9", specSec := "9.1.2", status := "P" },
  { number := 206, name := "c-forbidden",                       chapter := "9", specSec := "9.1.2", status := "GP" },
  { number := 207, name := "l-bare-document",                   chapter := "9", specSec := "9.1.3", status := "P" },
  { number := 208, name := "l-explicit-document",               chapter := "9", specSec := "9.1.4", status := "P" },
  { number := 209, name := "l-directive-document",              chapter := "9", specSec := "9.1.5", status := "P" },
  { number := 210, name := "l-any-document",                    chapter := "9", specSec := "9.2",   status := "P" },
  { number := 211, name := "l-yaml-stream",                     chapter := "9", specSec := "9.2",   status := "GP" }
]

/-! ## Automated `@[yaml_spec]` Coverage Query

At elaboration time, we query the Lean environment to discover which
productions have `@[yaml_spec]`-tagged implementations. -/

/-- An implementation mapping discovered from the environment. -/
structure SpecImplEntry where
  declName : String
  moduleName : String
  ruleNum : Option Nat
  ruleName : Option String
  specSection : String
  deriving Repr, Inhabited

/-- Resolve a module name to a file path (L4YAML.Scanner → L4YAML/Scanner.lean). -/
def moduleToPath (modName : String) : String :=
  modName.replace "." "/" ++ ".lean"

/-- Query all `@[yaml_spec]` entries from the environment at elaboration time
    and store them as a definition. -/
elab "#build_spec_coverage" : command => do
  let env ← getEnv
  let entries := getAllYamlSpecDecls env
  let mut result : Array SpecImplEntry := #[]
  for (name, refs) in entries do
    let modName := match env.getModuleIdxFor? name with
      | some idx => s!"{env.header.moduleNames[idx.toNat]!}"
      | none => "(current)"
    for ref in refs do
      result := result.push {
        declName := toString name,
        moduleName := modName,
        ruleNum := ref.rule,
        ruleName := ref.name,
        specSection := ref.specSection
      }
  -- Build the array literal via parsing a source string
  let mut src := "def discoveredSpecEntries : Array SpecImplEntry := #[\n"
  let mut idx := 0
  for e in result do
    let ruleStr := match e.ruleNum with
      | some n => s!"some {n}"
      | none => "none"
    let nameStr := match e.ruleName with
      | some s => s!"some \"{s}\""
      | none => "none"
    let comma := if idx + 1 < result.size then "," else ""
    src := src ++ s!"  ⟨\"{e.declName}\", \"{e.moduleName}\", {ruleStr}, {nameStr}, \"{e.specSection}\"⟩{comma}\n"
    idx := idx + 1
  src := src ++ "]\n"
  match Lean.Parser.runParserCategory (← getEnv) `command src with
  | .error msg => throwError s!"Failed to parse generated definition: {msg}"
  | .ok stx => Elab.Command.elabCommand stx

-- Execute the elaboration command to populate discoveredSpecEntries
#build_spec_coverage

/-! ## Coverage Cross-Reference -/

/-- Check if a production number has at least one `@[yaml_spec]` implementation. -/
def hasImplementation (prodNum : Nat) : Bool :=
  discoveredSpecEntries.any fun e => e.ruleNum == some prodNum

/-- Get all implementation entries for a given production number. -/
def getImplementations (prodNum : Nat) : Array SpecImplEntry :=
  discoveredSpecEntries.filter fun e => e.ruleNum == some prodNum

/-- Unique production numbers covered by `@[yaml_spec]` annotations. -/
def coveredProductionNums : Array Nat :=
  let nums := discoveredSpecEntries.filterMap fun e => e.ruleNum
  nums.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]

/-- Unique module names appearing in `@[yaml_spec]` entries. -/
def coveredModules : Array String :=
  discoveredSpecEntries.foldl (fun acc e =>
    if acc.contains e.moduleName then acc else acc.push e.moduleName) #[]

/-- In-scope productions (excluding out-of-scope). -/
def inScopeProductions : Array YamlProduction :=
  yamlProductions.filter fun p => p.status != "OOS"

/-- Productions with no `@[yaml_spec]` annotation on any rule number. -/
def uncoveredProductions : Array YamlProduction :=
  inScopeProductions.filter fun p => !hasImplementation p.number

/-- Productions with `@[yaml_spec]` annotation. -/
def coveredProductions : Array YamlProduction :=
  inScopeProductions.filter fun p => hasImplementation p.number

/-! ## Indentation-Dependent Production Analysis -/

/-- All indent-dependent production numbers from YAML 1.2.2. -/
def indentProductionNums : Array Nat := #[
  63, 64, 65, 67, 68, 69, 70, 71, 73, 74, 80, 81,
  162, 163, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
  179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194,
  195, 196, 197, 198, 199, 200, 201
]

/-- Indent-dependent productions that have `@[yaml_spec]` coverage. -/
def coveredIndentProductions : Array Nat :=
  indentProductionNums.filter hasImplementation

/-! ## Compile-Time Assertions -/

-- Catalog completeness
#guard yamlProductions.size == 211
#guard inScopeProductions.size == 211  -- all 211 in scope

-- Dynamic coverage discovery (these will be verified at build time)
#guard discoveredSpecEntries.size > 0
#guard coveredProductionNums.size > 0
#guard coveredModules.size > 0

/-! ## HTML Report Generation -/

private def escapeHtml (s : String) : String :=
  s.replace "&" "&amp;"
   |>.replace "<" "&lt;"
   |>.replace ">" "&gt;"
   |>.replace "\"" "&quot;"
   |>.replace "'" "&#39;"

def repoSourceUrl : String :=
  "https://github.jpl.nasa.gov/pass/lean4-yaml-verified/blob/main/"

private def reportCss : String :=
  "    :root {
      --color-covered: #4CAF50;
      --color-uncovered: #ff9800;
      --color-grammar: #2196F3;
      --color-oos: #9e9e9e;
    }
    * { box-sizing: border-box; }
    body {
      font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
      margin: 0; padding: 20px; background: #f5f5f5;
    }
    .container {
      max-width: 1400px; margin: 0 auto; background: white;
      padding: 30px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); border-radius: 8px;
    }
    h1 { color: #333; border-bottom: 3px solid var(--color-covered); padding-bottom: 10px; margin-top: 0; }
    h2 { color: #4CAF50; margin-top: 30px; }
    h3 { color: #555; }
    .subtitle { color: #666; font-size: 16px; margin-bottom: 30px; }

    .stats {
      display: grid; grid-template-columns: repeat(auto-fit, minmax(160px, 1fr));
      gap: 15px; margin: 25px 0;
    }
    .stat-box {
      color: white; padding: 20px; border-radius: 8px; text-align: center;
      box-shadow: 0 4px 6px rgba(0,0,0,0.1);
    }
    .stat-box h3 { margin: 0 0 8px 0; font-size: 13px; opacity: 0.9; color: white; }
    .stat-box .number { font-size: 32px; font-weight: bold; }
    .stat-box .pct { font-size: 14px; margin-top: 4px; opacity: 0.9; }
    .stat-total { background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); }
    .stat-covered { background: linear-gradient(135deg, #4CAF50 0%, #45a049 100%); }
    .stat-grammar { background: linear-gradient(135deg, #2196F3 0%, #1976D2 100%); }
    .stat-uncovered { background: linear-gradient(135deg, #ff9800 0%, #f57c00 100%); }
    .stat-oos { background: linear-gradient(135deg, #9e9e9e 0%, #757575 100%); }
    .stat-annotation { background: linear-gradient(135deg, #00bcd4 0%, #0097a7 100%); }

    .chapter-cards {
      display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr));
      gap: 15px; margin: 20px 0;
    }
    .chapter-card {
      background: #f8f9fa; padding: 18px; border-radius: 6px;
      border-left: 4px solid var(--color-covered);
    }
    .chapter-card-name { font-weight: 600; font-size: 16px; color: #333; margin-bottom: 8px; }
    .chapter-card-stats { color: #666; font-size: 14px; }
    .chapter-bar {
      height: 8px; background: #e0e0e0; border-radius: 4px; margin-top: 10px; overflow: hidden;
    }
    .chapter-bar-fill {
      height: 100%; background: var(--color-covered); border-radius: 4px;
      transition: width 0.3s ease;
    }

    .filters {
      background: #f8f9fa; padding: 15px; border-radius: 6px;
      margin: 20px 0; display: flex; gap: 20px; flex-wrap: wrap; align-items: center;
    }
    .filter-group { display: flex; align-items: center; gap: 8px; }
    .filter-group label { font-weight: 600; color: #555; font-size: 14px; }
    .filter-btn {
      padding: 6px 14px; border: 2px solid #ddd; background: white;
      border-radius: 4px; cursor: pointer; transition: all 0.2s; font-size: 13px;
    }
    .filter-btn:hover { border-color: #4CAF50; }
    .filter-btn.active { background: #4CAF50; color: white; border-color: #4CAF50; }
    select {
      padding: 6px 12px; border: 2px solid #ddd; border-radius: 4px; font-size: 13px;
    }
    .search-input {
      padding: 6px 12px; border: 2px solid #ddd; border-radius: 4px;
      font-size: 13px; width: 200px;
    }
    .search-input:focus { border-color: #4CAF50; outline: none; }

    table {
      width: 100%; border-collapse: collapse; margin: 20px 0;
      box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }
    th {
      background: #4CAF50; color: white; padding: 10px 12px; text-align: left;
      font-weight: 600; position: sticky; top: 0; cursor: pointer;
      user-select: none; font-size: 13px;
    }
    th:hover { background: #45a049; }
    th .sort-arrow { margin-left: 4px; opacity: 0.5; }
    th.sorted .sort-arrow { opacity: 1; }
    td { padding: 8px 12px; border-bottom: 1px solid #e0e0e0; font-size: 13px; }
    tr:hover { background: #f5f5f5; }
    tr.hidden { display: none; }

    .badge {
      display: inline-block; padding: 3px 10px; border-radius: 12px;
      font-size: 11px; font-weight: 600; color: white;
    }
    .badge-covered { background: var(--color-covered); }
    .badge-grammar { background: var(--color-grammar); }
    .badge-uncovered { background: var(--color-uncovered); }
    .badge-oos { background: var(--color-oos); }

    .impl-link {
      color: #1565C0; text-decoration: none; font-family: 'Courier New', monospace;
      font-size: 12px;
    }
    .impl-link:hover { text-decoration: underline; }

    .spec-link {
      color: #1565C0; text-decoration: none; font-weight: 600;
    }
    .spec-link:hover { text-decoration: underline; }

    .nav-link {
      display: inline-block; margin-bottom: 20px; color: #2196F3;
      text-decoration: none; font-size: 14px;
    }
    .nav-link:hover { text-decoration: underline; }

    footer {
      margin-top: 40px; text-align: center; color: #999; font-size: 13px;
      border-top: 1px solid #e0e0e0; padding-top: 20px;
    }
    footer a { color: #2196F3; text-decoration: none; }
    footer a:hover { text-decoration: underline; }

    @media (max-width: 768px) {
      body { padding: 10px; }
      .container { padding: 15px; }
      .filters { flex-direction: column; gap: 10px; }
      .stats { grid-template-columns: repeat(2, 1fr); }
    }
"

private def reportJs : String :=
  "
    let currentStatusFilter = 'all';
    let currentChapterFilter = 'all';
    let currentSearchText = '';
    let sortColumn = 0;
    let sortAscending = true;

    function filterByStatus(status) {
      currentStatusFilter = status;
      document.querySelectorAll('.filter-status .filter-btn').forEach(btn => btn.classList.remove('active'));
      event.target.classList.add('active');
      applyFilters();
    }

    function filterByChapter(chapter) {
      currentChapterFilter = chapter;
      applyFilters();
    }

    function searchProductions(text) {
      currentSearchText = text.toLowerCase();
      applyFilters();
    }

    function applyFilters() {
      const rows = document.querySelectorAll('.prod-row');
      let visible = 0;
      rows.forEach(row => {
        const status = row.dataset.status;
        const chapter = row.dataset.chapter;
        const search = row.dataset.search;
        const statusMatch = currentStatusFilter === 'all' || status === currentStatusFilter;
        const chapterMatch = currentChapterFilter === 'all' || chapter === currentChapterFilter;
        const searchMatch = currentSearchText === '' || search.includes(currentSearchText);
        if (statusMatch && chapterMatch && searchMatch) {
          row.classList.remove('hidden');
          visible++;
        } else {
          row.classList.add('hidden');
        }
      });
      document.getElementById('visibleCount').textContent = visible;
    }

    function sortTable(colIdx) {
      const table = document.getElementById('prodTable');
      const tbody = table.querySelector('tbody');
      const rows = Array.from(tbody.querySelectorAll('.prod-row'));
      if (sortColumn === colIdx) { sortAscending = !sortAscending; }
      else { sortColumn = colIdx; sortAscending = true; }
      table.querySelectorAll('th').forEach((th, i) => {
        th.classList.remove('sorted');
        const arrow = th.querySelector('.sort-arrow');
        if (arrow) arrow.textContent = '↕';
      });
      const th = table.querySelectorAll('th')[colIdx];
      th.classList.add('sorted');
      const arrow = th.querySelector('.sort-arrow');
      if (arrow) arrow.textContent = sortAscending ? '↑' : '↓';
      rows.sort((a, b) => {
        let aVal = a.children[colIdx]?.textContent.trim() || '';
        let bVal = b.children[colIdx]?.textContent.trim() || '';
        const aNum = parseFloat(aVal);
        const bNum = parseFloat(bVal);
        if (!isNaN(aNum) && !isNaN(bNum)) {
          return sortAscending ? aNum - bNum : bNum - aNum;
        }
        return sortAscending ? aVal.localeCompare(bVal) : bVal.localeCompare(aVal);
      });
      rows.forEach(row => tbody.appendChild(row));
    }
  "

/-- Determine the display status for a production. -/
private def productionStatus (p : YamlProduction) : String :=
  if p.status == "OOS" then "oos"
  else if p.status == "G" then "grammar"
  else if hasImplementation p.number then "covered"
  else "uncovered"

/-- Badge HTML for a production status. -/
private def statusBadge (status : String) : String :=
  match status with
  | "covered"   => "<span class=\"badge badge-covered\">Covered</span>"
  | "grammar"   => "<span class=\"badge badge-grammar\">Grammar Only</span>"
  | "uncovered" => "<span class=\"badge badge-uncovered\">No Annotation</span>"
  | "oos"       => "<span class=\"badge badge-oos\">Out of Scope</span>"
  | _           => ""

/-- Format percentage to 1 decimal. -/
private def formatPct (pct : Float) : String :=
  let scaled := (pct * 10.0 + 0.5).floor.toUInt64.toNat
  let whole := scaled / 10
  let frac  := scaled % 10
  s!"{whole}.{frac}"

/-- Generate the production coverage HTML report. -/
def generateProductionCoverageHtml : String :=
  let totalProds := yamlProductions.size
  let oosCount := yamlProductions.filter (fun p => p.status == "OOS") |>.size
  let grammarOnly := yamlProductions.filter (fun p => p.status == "G") |>.size
  let inScope := inScopeProductions.size
  let annotatedCount := coveredProductionNums.size
  let totalAnnotations := discoveredSpecEntries.size
  let moduleCount := coveredModules.size

  -- Stats boxes
  let statsHtml := String.join [
    "  <div class=\"stats\">\n",
    s!"    <div class=\"stat-box stat-total\"><h3>Total Productions</h3><div class=\"number\">{totalProds}</div></div>\n",
    s!"    <div class=\"stat-box stat-covered\"><h3>Annotated Rules</h3><div class=\"number\">{annotatedCount}</div><div class=\"pct\">of {inScope} in-scope</div></div>\n",
    s!"    <div class=\"stat-box stat-annotation\"><h3>@[yaml_spec] Entries</h3><div class=\"number\">{totalAnnotations}</div><div class=\"pct\">across {moduleCount} modules</div></div>\n",
    s!"    <div class=\"stat-box stat-grammar\"><h3>Grammar Only</h3><div class=\"number\">{grammarOnly}</div></div>\n",
    s!"    <div class=\"stat-box stat-oos\"><h3>Out of Scope</h3><div class=\"number\">{oosCount}</div></div>\n",
    "  </div>\n"
  ]

  -- Per-chapter breakdown
  let chapters := #[("5", "Ch 5: Characters"), ("6", "Ch 6: Basic Structures"),
                     ("7", "Ch 7: Flow Styles"), ("8", "Ch 8: Block Styles"),
                     ("9", "Ch 9: Documents")]
  let chapterCards := String.join (chapters.toList.map fun (ch, label) =>
    let chProds := inScopeProductions.filter (fun p => p.chapter == ch)
    let chCovered := chProds.filter (fun p => hasImplementation p.number) |>.size
    let chTotal := chProds.size
    let pct := if chTotal == 0 then 0.0
               else chCovered.toFloat / chTotal.toFloat * 100.0
    let pctStr := formatPct pct
    s!"    <div class=\"chapter-card\">\n" ++
    s!"      <div class=\"chapter-card-name\">{label}</div>\n" ++
    s!"      <div class=\"chapter-card-stats\">{chCovered}/{chTotal} annotated ({pctStr}%)</div>\n" ++
    s!"      <div class=\"chapter-bar\"><div class=\"chapter-bar-fill\" style=\"width: {pctStr}%\"></div></div>\n" ++
    s!"    </div>\n")

  -- Filter bar
  let filtersHtml := String.join [
    "  <div class=\"filters\">\n",
    "    <div class=\"filter-group filter-status\">\n",
    "      <label>Status:</label>\n",
    "      <button class=\"filter-btn active\" onclick=\"filterByStatus('all')\">All</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByStatus('covered')\">Covered</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByStatus('uncovered')\">No Annotation</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByStatus('grammar')\">Grammar Only</button>\n",
    "      <button class=\"filter-btn\" onclick=\"filterByStatus('oos')\">Out of Scope</button>\n",
    "    </div>\n",
    "    <div class=\"filter-group\">\n",
    "      <label>Chapter:</label>\n",
    "      <select onchange=\"filterByChapter(this.value)\">\n",
    "        <option value=\"all\">All Chapters</option>\n",
    "        <option value=\"5\">Ch 5: Characters</option>\n",
    "        <option value=\"6\">Ch 6: Basic Structures</option>\n",
    "        <option value=\"7\">Ch 7: Flow Styles</option>\n",
    "        <option value=\"8\">Ch 8: Block Styles</option>\n",
    "        <option value=\"9\">Ch 9: Documents</option>\n",
    "      </select>\n",
    "    </div>\n",
    "    <div class=\"filter-group\">\n",
    "      <label>Search:</label>\n",
    "      <input type=\"text\" class=\"search-input\" placeholder=\"Name, rule number...\" oninput=\"searchProductions(this.value)\">\n",
    "    </div>\n",
    s!"    <div class=\"filter-group\"><span>Showing <strong id=\"visibleCount\">{totalProds}</strong> of {totalProds}</span></div>\n",
    "  </div>\n"
  ]

  -- Table rows
  let tableRows := String.join (yamlProductions.toList.map fun p =>
    let status := productionStatus p
    let badge := statusBadge status
    let specUrl := s!"https://yaml.org/spec/1.2.2/#rule-{(p.name.takeWhile (· ≠ '('))}"
    let nameLink := s!"<a href=\"{specUrl}\" target=\"_blank\" class=\"spec-link\">{escapeHtml p.name}</a>"
    -- Implementation links
    let impls := getImplementations p.number
    let implLinks := if impls.isEmpty then
        if p.status == "OOS" then "—"
        else if p.status == "G" then "<em>Grammar spec only</em>"
        else "<em>No @[yaml_spec] annotation</em>"
      else
        String.intercalate "<br>" (impls.toList.map fun e =>
          let path := moduleToPath e.moduleName
          s!"<a href=\"{repoSourceUrl}{path}\" target=\"_blank\" class=\"impl-link\">{escapeHtml e.declName}</a>")
    let searchText := s!"{p.number} {p.name} {p.specSec} {status}".toLower
    s!"      <tr class=\"prod-row\" data-status=\"{status}\" data-chapter=\"{p.chapter}\" data-search=\"{escapeHtml searchText}\">\n" ++
    s!"        <td>{p.number}</td>\n" ++
    s!"        <td>{nameLink}</td>\n" ++
    s!"        <td>§{p.specSec}</td>\n" ++
    s!"        <td>{badge}</td>\n" ++
    s!"        <td>{implLinks}</td>\n" ++
    s!"      </tr>\n")

  -- Assemble
  String.join [
    "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n",
    "  <meta charset=\"UTF-8\">\n",
    "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n",
    "  <title>YAML 1.2.2 Production Coverage — lean4-yaml-verified</title>\n",
    "  <style>\n", reportCss, "  </style>\n",
    "</head>\n<body>\n",
    "<div class=\"container\">\n",
    "  <a href=\"index.html\" class=\"nav-link\">← Back to Coverage Index</a>\n",
    "  <h1>YAML 1.2.2 Production Coverage</h1>\n",
    "  <p class=\"subtitle\">Automated cross-reference of YAML 1.2.2 productions with <code>@[yaml_spec]</code> annotations in lean4-yaml-verified</p>\n\n",
    statsHtml,
    "  <h3>Coverage by Chapter</h3>\n",
    "  <div class=\"chapter-cards\">\n",
    chapterCards,
    "  </div>\n\n",
    filtersHtml,
    "  <table id=\"prodTable\">\n",
    "    <thead>\n",
    "      <tr>\n",
    "        <th onclick=\"sortTable(0)\"># <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(1)\">Production <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(2)\">Section <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(3)\">Status <span class=\"sort-arrow\">↕</span></th>\n",
    "        <th onclick=\"sortTable(4)\">Lean Implementation <span class=\"sort-arrow\">↕</span></th>\n",
    "      </tr>\n",
    "    </thead>\n",
    "    <tbody>\n",
    tableRows,
    "    </tbody>\n",
    "  </table>\n\n",
    "  <footer>\n",
    "    Auto-generated by <code>@[yaml_spec]</code> environment query · lean4-yaml-verified · Lean 4\n",
    "  </footer>\n",
    "</div>\n\n",
    "<script>\n", reportJs, "</script>\n",
    "</body>\n</html>\n"
  ]

/-- Write the production coverage HTML report to a file. -/
def writeProductionCoverageHtml (outDir : String) : IO Unit := do
  let dir := if outDir.endsWith "/" then (outDir.toRawSubstring.dropRight 1).toString else outDir
  IO.FS.createDirAll dir
  let html := generateProductionCoverageHtml
  IO.FS.writeFile s!"{dir}/production-coverage.html" html
  IO.println s!"  wrote {dir}/production-coverage.html"

/-! ## Collector for SuiteRunner integration -/

/-- Collect all production coverage analysis results. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)

  setCategory state "Catalog completeness"
  check state s!"YAML 1.2.2 productions cataloged: {yamlProductions.size}"
    (yamlProductions.size == 211)
  check state s!"in-scope productions: {inScopeProductions.size}"
    (inScopeProductions.size == 211)
  check state s!"indent-dependent productions: {indentProductionNums.size}"
    (indentProductionNums.size == 49)

  setCategory state "Automated @[yaml_spec] discovery"
  check state s!"@[yaml_spec] entries discovered: {discoveredSpecEntries.size}"
    (discoveredSpecEntries.size > 0)
  check state s!"unique production rules annotated: {coveredProductionNums.size}"
    (coveredProductionNums.size > 0)
  check state s!"source modules with annotations: {coveredModules.size}"
    (coveredModules.size > 0)

  setCategory state "Coverage analysis"
  check state s!"annotated productions: {coveredProductions.size}/{inScopeProductions.size}"
    (coveredProductions.size > 0)
  check state s!"unannotated in-scope productions: {uncoveredProductions.size}"
    true
  check state s!"indent-dependent with annotations: {coveredIndentProductions.size}/{indentProductionNums.size}"
    (coveredIndentProductions.size > 0)

  setCategory state "Per-module annotation counts"
  for modName in coveredModules do
    let count := discoveredSpecEntries.filter (fun e => e.moduleName == modName) |>.size
    check state s!"{modName}: {count} annotations" (count > 0)

  setCategory state "Per-chapter coverage"
  let chapters := #[("5", "Characters"), ("6", "Basic Structures"),
                     ("7", "Flow Styles"), ("8", "Block Styles"),
                     ("9", "Documents")]
  for (ch, label) in chapters do
    let chProds := inScopeProductions.filter (fun p => p.chapter == ch)
    let chCov := chProds.filter (fun p => hasImplementation p.number) |>.size
    check state s!"Ch {ch} ({label}): {chCov}/{chProds.size}" true

  setCategory state "Unannotated productions (gaps)"
  for p in uncoveredProductions do
    check state s!"[{p.number}] {p.name} (§{p.specSec}) — no @[yaml_spec]" true

  let results ← finish state
  return { name := "productioncoverage",
           label := "Production Coverage Analysis",
           sourceFile := "Tests/ProductionCoverage.lean",
           tests := results }

end Tests.ProdCoverage
