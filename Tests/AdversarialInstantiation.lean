import L4YAML.Scanner
import L4YAML.Emitter
import L4YAML.TokenParser
import L4YAML.Proofs.ParserGrammableBase
import Tests.VerifiedResult

/-!
# Adversarial Instantiation Tests

Computational verification of sorry'd theorem statements by systematically
instantiating them on adversarial inputs. Detects false claims before
investing proof effort.

See `ADVERSARIAL_INSTANTIATION.md` for methodology and triage.

## Priority 1 — Theorems 9g, 9h (emitList / emitPairList characterization)

These theorems claim properties about the filtered token sequence produced by
scanning emitter output. A bug was previously caught here where inner-level
`flowEntry` tokens (inside nested brackets) were incorrectly required to
satisfy the outer-level characterization.

After the `flowBracketBalance` fix, we re-verify with deeply nested,
mixed-nesting, and previously-failing inputs.
-/

open L4YAML L4YAML.Scanner L4YAML.Emit L4YAML.TokenParser L4YAML.Proofs.ParserGrammable
open Tests

namespace Tests.AdversarialInstantiation

/-! ## Infrastructure -/

/-- Compute flowBracketDelta for a token value. -/
private def fbd (t : YamlToken) : Int :=
  match t with
  | .flowSequenceStart | .flowMappingStart => 1
  | .flowSequenceEnd | .flowMappingEnd => -1
  | _ => 0

/-- Compute bracket balance over a token array slice [lo, hi). -/
private def bracketBal (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Int :=
  let slice := tokens.toList.drop lo |>.take (hi - lo)
  slice.foldl (fun acc t => acc + fbd t.val) 0

/-- Check if a token value is a "content start" (scalar, flowSeqStart, or flowMapStart). -/
private def isContentStart (t : YamlToken) : Bool :=
  match t with
  | .scalar _ _ => true
  | .flowSequenceStart => true
  | .flowMappingStart => true
  | _ => false

/-- Pretty-print a token for debugging. -/
private def tokStr (t : YamlToken) : String :=
  match t with
  | .streamStart => "streamStart"
  | .streamEnd => "streamEnd"
  | .placeholder => "placeholder"
  | .flowSequenceStart => "["
  | .flowSequenceEnd => "]"
  | .flowMappingStart => "{"
  | .flowMappingEnd => "}"
  | .flowEntry => ","
  | .key => "key"
  | .value => ":"
  | .scalar c _ => s!"scalar({c})"
  | .blockSequenceStart => "blockSeqStart"
  | .blockMappingStart => "blockMapStart"
  | .blockEnd => "blockEnd"
  | .blockEntry => "blockEntry"
  | .documentStart => "docStart"
  | .documentEnd => "docEnd"
  | .versionDirective m n => s!"%YAML {m}.{n}"
  | .tagDirective h p => s!"%TAG {h} {p}"
  | .anchor n => s!"&{n}"
  | .alias n => s!"*{n}"
  | .tag h s => s!"tag({h},{s})"
  | .comment t => s!"#{t}"

/-- Scan a string and return filtered tokens. -/
private def scanEmitted (input : String) : IO (Array (Positioned YamlToken)) := do
  match scanFiltered input with
  | .ok tokens => return tokens
  | .error e => throw (IO.Error.userError s!"scan failed: {repr e}")

/-! ## Value constructors -/

/-- Scalar value. -/
private def sv (content : String) : YamlValue :=
  .scalar { content, style := .plain }

/-- Flow sequence value. -/
private def seqv (items : List YamlValue) : YamlValue :=
  .sequence .flow items.toArray

/-- Flow mapping value. -/
private def mapv (pairs : List (YamlValue × YamlValue)) : YamlValue :=
  .mapping .flow pairs.toArray

/-! ## 9g: emitList body characterization

  For sequence emission: `"[" ++ emitList items ++ "]"`
  Filtered tokens: streamStart, `[`, <body>, `]`, streamEnd
  Body = first token is content-start;
         every outer-level `,` is followed by content-start
-/

/-- Check 9g characterization for a given list of items. -/
private def check9g (state : IO.Ref TestCollector)
    (label : String) (items : List YamlValue) : IO Unit := do
  let emitted := "[" ++ emit.emitList items ++ "]"
  let tokens ← scanEmitted emitted

  if tokens.size < 5 then
    checkM state s!"{label}: size≥5" false s!"size={tokens.size}"
    return

  check state s!"{label}: streamStart" (tokens[0]!.val == .streamStart)
  check state s!"{label}: flowSeqStart" (tokens[1]!.val == .flowSequenceStart)
  check state s!"{label}: flowSeqEnd" (tokens[tokens.size - 2]!.val == .flowSequenceEnd)
  check state s!"{label}: streamEnd" (tokens[tokens.size - 1]!.val == .streamEnd)

  let bodyStart : Nat := 2
  let bodyEnd : Nat := tokens.size - 2

  if items.isEmpty then return

  -- (1) First body token is content-start
  let firstTok := tokens[bodyStart]!.val
  checkM state s!"{label}: first body is content-start"
    (isContentStart firstTok) s!"got {tokStr firstTok}"

  -- (2) Every outer-level flowEntry is followed by content-start
  for _h : i in [bodyStart:bodyEnd] do
    let tok := tokens[i]!.val
    if tok == .flowEntry then
      let bal := bracketBal tokens bodyStart i
      if bal == 0 then
        if i + 1 < bodyEnd then
          let nextTok := tokens[i + 1]!.val
          checkM state s!"{label}: outer flowEntry@{i} → content-start"
            (isContentStart nextTok) s!"bal=0, next={tokStr nextTok}"
        else
          checkM state s!"{label}: outer flowEntry@{i} → has next"
            false "no token after flowEntry"

/-! ## 9h: emitPairList body characterization

  For mapping emission: `"{" ++ emitPairList pairs ++ "}"`
  Filtered tokens: streamStart, `{`, <body>, `}`, streamEnd
  Body = first token is `.key`;
         every outer-level `,` is followed by `.key`
-/

/-- Check 9h characterization for a given list of pairs. -/
private def check9h (state : IO.Ref TestCollector)
    (label : String) (pairs : List (YamlValue × YamlValue)) : IO Unit := do
  let emitted := "{" ++ emit.emitPairList pairs ++ "}"
  let tokens ← scanEmitted emitted

  if tokens.size < 5 then
    checkM state s!"{label}: size≥5" false s!"size={tokens.size}"
    return

  check state s!"{label}: streamStart" (tokens[0]!.val == .streamStart)
  check state s!"{label}: flowMapStart" (tokens[1]!.val == .flowMappingStart)
  check state s!"{label}: flowMapEnd" (tokens[tokens.size - 2]!.val == .flowMappingEnd)
  check state s!"{label}: streamEnd" (tokens[tokens.size - 1]!.val == .streamEnd)

  let bodyStart : Nat := 2
  let bodyEnd : Nat := tokens.size - 2

  if pairs.isEmpty then return

  -- (1) First body token is .key
  let firstTok := tokens[bodyStart]!.val
  checkM state s!"{label}: first body is .key"
    (firstTok == .key) s!"got {tokStr firstTok}"

  -- (2) Every outer-level flowEntry is followed by .key
  for _h : i in [bodyStart:bodyEnd] do
    let tok := tokens[i]!.val
    if tok == .flowEntry then
      let bal := bracketBal tokens bodyStart i
      if bal == 0 then
        if i + 1 < bodyEnd then
          let nextTok := tokens[i + 1]!.val
          checkM state s!"{label}: outer flowEntry@{i} → .key"
            (nextTok == .key) s!"bal=0, next={tokStr nextTok}"
        else
          checkM state s!"{label}: outer flowEntry@{i} → has next"
            false "no token after flowEntry"

/-! ## Test Suites -/

private def test9g (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9g: emitList_body_filtered_characterization"

  -- Flat sequences
  check9g state "flat-1" [sv "a"]
  check9g state "flat-2" [sv "a", sv "b"]
  check9g state "flat-3" [sv "a", sv "b", sv "c"]

  -- 1-level nesting
  check9g state "nest1-seq" [seqv [sv "a", sv "b"], sv "c"]
  check9g state "nest1-map" [mapv [(sv "k", sv "v")], sv "c"]

  -- 2-level nesting
  check9g state "nest2" [seqv [seqv [sv "a"]]]
  check9g state "nest2-multi" [seqv [seqv [sv "a"]], sv "b"]

  -- Mixed sequences/mappings
  check9g state "mixed-1" [mapv [(sv "k", sv "v")], seqv [sv "a"]]
  check9g state "mixed-2" [sv "plain", seqv [sv "a", sv "b"], mapv [(sv "x", sv "y")]]

  -- Previously-failing case (nested mappings inside sequences)
  check9g state "prev-fail-1" [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")]]
  check9g state "prev-fail-2"
    [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")], sv "after"]

  -- Deep nesting
  check9g state "deep-3" [seqv [seqv [seqv [sv "deep"]]]]
  check9g state "deep-mixed"
    [mapv [(sv "a", seqv [mapv [(sv "b", sv "c")]])]]

  -- Edge cases
  check9g state "empty-scalar" [sv ""]
  check9g state "special-chars" [sv "hello \"world\"", sv "line1\nline2"]
  check9g state "many-items" [sv "a", sv "b", sv "c", sv "d", sv "e", sv "f"]

private def test9h (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9h: emitPairList_body_filtered_characterization"

  -- Single pair
  check9h state "pair-1" [(sv "k", sv "v")]

  -- Multiple pairs
  check9h state "pairs-2" [(sv "k1", sv "v1"), (sv "k2", sv "v2")]
  check9h state "pairs-3" [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3")]

  -- Previously-failing analogue
  check9h state "prev-fail-map" [(sv "k1", sv "v1"), (sv "k2", sv "v2")]

  -- Nested values in mappings
  check9h state "nested-seq-val" [(sv "k", seqv [sv "a", sv "b"])]
  check9h state "nested-map-val" [(sv "k", mapv [(sv "inner_k", sv "inner_v")])]
  check9h state "nested-seq-key" [(seqv [sv "a"], sv "v")]

  -- Mixed nested structures
  check9h state "map-in-map" [(sv "a", mapv [(sv "b", sv "c")])]
  check9h state "seq-in-map"
    [(sv "items", seqv [sv "x", sv "y"]), (sv "count", sv "2")]
  check9h state "complex"
    [(sv "data", seqv [mapv [(sv "id", sv "1")], mapv [(sv "id", sv "2")]]),
     (sv "meta", mapv [(sv "ver", sv "1.0")])]

  -- Deep nesting in mapping values
  check9h state "deep-val" [(sv "k", seqv [seqv [seqv [sv "deep"]]])]
  check9h state "multi-deep"
    [(sv "a", seqv [seqv [sv "1"]]),
     (sv "b", mapv [(sv "c", mapv [(sv "d", sv "e")])])]

  -- Edge cases
  check9h state "empty-key" [(sv "", sv "v")]
  check9h state "empty-val" [(sv "k", sv "")]
  check9h state "special-chars-kv" [(sv "hello \"world\"", sv "line1\nline2")]
  check9h state "many-pairs"
    [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3"),
     (sv "d", sv "4"), (sv "e", sv "5"), (sv "f", sv "6")]

/-! ## Collection entry point -/

/-! ### Priority 2 — Theorems 9c, 9d (emit round-trip content equivalence)

These theorems claim that for any `YamlValue v`:
- 9c (sequences): `parseYamlRaw (emit (.sequence style items ..)) = .ok raw_docs` with
  `raw_docs.size = 1` implies `contentEq (.sequence ..) (composed[0]!.value) = true`
- 9d (mappings): Same for `.mapping`

We test the full pipeline: `emit v → parseYaml → compose → contentEq v result`.
This covers both the sequence and mapping cases, plus scalars as base cases.
-/

/-- Check that `emit v` round-trips through the parser with content preserved.
    Tests: (1) parsing succeeds, (2) exactly 1 document, (3) contentEq holds. -/
private def checkRoundTrip (state : IO.Ref TestCollector)
    (label : String) (v : YamlValue) : IO Unit := do
  let emitted := emit v
  match parseYamlRaw emitted with
  | .error e =>
    checkM state s!"{label}: parse succeeds" false s!"parse error: {repr e}"
  | .ok raw_docs =>
    check state s!"{label}: parse succeeds" true
    checkM state s!"{label}: exactly 1 doc" (raw_docs.size == 1)
      s!"got {raw_docs.size} docs"
    if raw_docs.size == 1 then
      let composed := raw_docs.map YamlDocument.compose
      let result := composed[0]!.value
      let eq := contentEq v result
      if !eq then
        -- Show what we got for debugging
        let emittedResult := emit result
        checkM state s!"{label}: contentEq" false
          s!"emitted='{emitted}' parsed_back='{emittedResult}'"
      else
        check state s!"{label}: contentEq" true

/-! ## Priority 2 Test Suites -/

private def test9cd (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9c/9d: emit round-trip content equivalence"

  -- Scalars (base case for both 9c and 9d)
  checkRoundTrip state "scalar-plain" (sv "hello")
  checkRoundTrip state "scalar-empty" (sv "")
  checkRoundTrip state "scalar-escape" (sv "with \"escape\"")
  checkRoundTrip state "scalar-newline" (sv "line1\nline2")
  checkRoundTrip state "scalar-tab" (sv "col1\tcol2")
  checkRoundTrip state "scalar-backslash" (sv "path\\to\\file")
  checkRoundTrip state "scalar-unicode" (sv "hello \u0000world")
  checkRoundTrip state "scalar-colon-space" (sv "key: value")
  checkRoundTrip state "scalar-hash" (sv "not # a comment")
  checkRoundTrip state "scalar-brackets" (sv "[not, a, sequence]")
  checkRoundTrip state "scalar-braces" (sv "{not: a, mapping: true}")

  -- 9c: Sequences
  setCategory state "9c: emit_roundtrip_sequence_content_eq"

  -- Empty
  checkRoundTrip state "seq-empty" (seqv [])

  -- Flat
  checkRoundTrip state "seq-1" (seqv [sv "a"])
  checkRoundTrip state "seq-2" (seqv [sv "a", sv "b"])
  checkRoundTrip state "seq-3" (seqv [sv "a", sv "b", sv "c"])

  -- Nested sequences
  checkRoundTrip state "seq-nested-1" (seqv [seqv [sv "a", sv "b"], sv "c"])
  checkRoundTrip state "seq-nested-2" (seqv [seqv [seqv [sv "deep"]]])
  checkRoundTrip state "seq-nested-3" (seqv [seqv [seqv [seqv [sv "deeper"]]]])

  -- Sequences with mappings
  checkRoundTrip state "seq-with-map" (seqv [mapv [(sv "k", sv "v")], sv "c"])
  checkRoundTrip state "seq-with-multi-map"
    (seqv [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")]])

  -- Mixed nesting
  checkRoundTrip state "seq-mixed"
    (seqv [sv "plain", seqv [sv "a", sv "b"], mapv [(sv "x", sv "y")]])
  checkRoundTrip state "seq-deep-mixed"
    (seqv [mapv [(sv "a", seqv [mapv [(sv "b", sv "c")]])]])

  -- Edge cases
  checkRoundTrip state "seq-empty-scalars" (seqv [sv "", sv "", sv ""])
  checkRoundTrip state "seq-special-chars"
    (seqv [sv "hello \"world\"", sv "line1\nline2", sv "tab\there"])
  checkRoundTrip state "seq-many"
    (seqv [sv "a", sv "b", sv "c", sv "d", sv "e", sv "f", sv "g", sv "h"])

  -- Previously-failing patterns (from Priority 1: inner commas)
  checkRoundTrip state "seq-prev-fail"
    (seqv [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")], sv "after"])

  -- 9d: Mappings
  setCategory state "9d: emit_roundtrip_mapping_content_eq"

  -- Empty
  checkRoundTrip state "map-empty" (mapv [])

  -- Flat
  checkRoundTrip state "map-1" (mapv [(sv "k", sv "v")])
  checkRoundTrip state "map-2" (mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")])
  checkRoundTrip state "map-3"
    (mapv [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3")])

  -- Nested mappings
  checkRoundTrip state "map-nested-1" (mapv [(sv "outer", mapv [(sv "inner", sv "val")])])
  checkRoundTrip state "map-nested-2"
    (mapv [(sv "a", mapv [(sv "b", mapv [(sv "c", sv "deep")])])])

  -- Mappings with sequences
  checkRoundTrip state "map-with-seq" (mapv [(sv "items", seqv [sv "x", sv "y"])])
  checkRoundTrip state "map-with-nested-seq"
    (mapv [(sv "data", seqv [seqv [sv "a", sv "b"], seqv [sv "c"]])])

  -- Mixed nesting
  checkRoundTrip state "map-mixed"
    (mapv [(sv "items", seqv [sv "x", sv "y"]), (sv "count", sv "2")])
  checkRoundTrip state "map-complex"
    (mapv [(sv "data", seqv [mapv [(sv "id", sv "1")], mapv [(sv "id", sv "2")]]),
           (sv "meta", mapv [(sv "ver", sv "1.0")])])

  -- Deep nesting
  checkRoundTrip state "map-deep-val"
    (mapv [(sv "k", seqv [seqv [seqv [sv "deep"]]])])
  checkRoundTrip state "map-multi-deep"
    (mapv [(sv "a", seqv [seqv [sv "1"]]),
           (sv "b", mapv [(sv "c", mapv [(sv "d", sv "e")])])])

  -- Edge cases
  checkRoundTrip state "map-empty-key" (mapv [(sv "", sv "v")])
  checkRoundTrip state "map-empty-val" (mapv [(sv "k", sv "")])
  checkRoundTrip state "map-special-chars"
    (mapv [(sv "hello \"world\"", sv "line1\nline2")])
  checkRoundTrip state "map-many"
    (mapv [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3"),
           (sv "d", sv "4"), (sv "e", sv "5"), (sv "f", sv "6")])

  -- Sequence keys in mappings (stress test for key complexity)
  checkRoundTrip state "map-seq-key" (mapv [(seqv [sv "a", sv "b"], sv "v")])
  checkRoundTrip state "map-map-key"
    (mapv [(mapv [(sv "inner", sv "key")], sv "v")])

  -- 5-level deep nesting
  checkRoundTrip state "deep-5"
    (seqv [seqv [seqv [seqv [seqv [sv "bottom"]]]]])
  checkRoundTrip state "map-deep-5"
    (mapv [(sv "1", mapv [(sv "2", mapv [(sv "3",
      mapv [(sv "4", mapv [(sv "5", sv "bottom")])])])])])

  -- Cross: deeply nested mixed structures
  checkRoundTrip state "cross-nested"
    (seqv [mapv [(sv "key", seqv [mapv [(sv "inner", seqv [sv "a", sv "b"])]])]])


/-! ## Priority 3 — Theorems 9a, 9b (parser fuel sufficiency)

These theorems claim that `parseStream` succeeds on emitter output. The key sorry is
in `scanFiltered_emitSeq_nonempty_structure` / `scanFiltered_emitMap_nonempty_structure`:
the fuel bound `4 * tokens.size + 4` suffices for `parseNode` / `parseFlowSequence` /
`parseFlowMapping` to succeed on the token stream produced by the emitter.

We test:
1. **Correctness:** `parseStream (scanFiltered (emit v))` returns `.ok docs` with `docs.size = 1`
2. **Tightness:** `parseNode` at pos=1 with fuel `4*N+3` (one less than `parseDocument` uses) —
   does it still work or is the bound exactly tight?
3. **Scaling:** Report token counts to verify fuel scales with input complexity
-/

/-- Check parser fuel sufficiency for an emitted value.
    Returns `(tokensSize, fuelUsed, tightFuelWorks)`. -/
private def checkFuelSufficiency (state : IO.Ref TestCollector)
    (label : String) (v : YamlValue) : IO Unit := do
  let emitted := emit v
  -- Step 1: Scan to get tokens
  match scanFiltered emitted with
  | .error e =>
    checkM state s!"{label}: scan succeeds" false s!"scan error: {repr e}"
  | .ok tokens =>
    check state s!"{label}: scan succeeds" true
    let n := tokens.size
    let fuel := 4 * n + 4

    -- Step 2: parseStream with standard fuel (4*N+4 inside parseDocument)
    match parseStream tokens with
    | .error e =>
      checkM state s!"{label}: parseStream ok (fuel={fuel}, N={n})" false
        s!"parse error: {repr e}"
    | .ok docs =>
      check state s!"{label}: parseStream ok (fuel={fuel}, N={n})" true
      checkM state s!"{label}: exactly 1 doc" (docs.size == 1)
        s!"got {docs.size} docs"

    -- Step 3: Tightness — call parseNode directly at pos=1 with fuel-1
    if n ≥ 2 then
      let ps1 : ParseState := { tokens := tokens, pos := 1 }
      let tightFuel := 4 * n + 3  -- one less than parseDocument uses
      match parseNode ps1 tightFuel with
      | .ok _ =>
        check state s!"{label}: tight fuel {tightFuel} also works" true
      | .error _ =>
        -- This is informational — if this fails, 4*N+4 is exactly tight
        check state s!"{label}: tight fuel {tightFuel} fails (bound is tight!)" true

/-! ## Priority 3 Test Suites -/

private def test9ab (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9a: parseStream_emitSequence fuel sufficiency"

  -- Empty sequence (base case — already proven, sanity check)
  checkFuelSufficiency state "seq-empty" (seqv [])

  -- Single element
  checkFuelSufficiency state "seq-1" (seqv [sv "a"])

  -- Two elements (minimal non-trivial)
  checkFuelSufficiency state "seq-2" (seqv [sv "a", sv "b"])

  -- Many elements (wide: stress the loop fuel)
  checkFuelSufficiency state "seq-8"
    (seqv [sv "a", sv "b", sv "c", sv "d", sv "e", sv "f", sv "g", sv "h"])
  checkFuelSufficiency state "seq-12"
    (seqv [sv "a", sv "b", sv "c", sv "d", sv "e", sv "f",
           sv "g", sv "h", sv "i", sv "j", sv "k", sv "l"])

  -- Nested sequences (depth: stress recursive parseNode calls)
  checkFuelSufficiency state "seq-depth-2" (seqv [seqv [sv "a", sv "b"]])
  checkFuelSufficiency state "seq-depth-3" (seqv [seqv [seqv [sv "a"]]])
  checkFuelSufficiency state "seq-depth-4" (seqv [seqv [seqv [seqv [sv "a"]]]])
  checkFuelSufficiency state "seq-depth-5"
    (seqv [seqv [seqv [seqv [seqv [sv "a"]]]]])
  checkFuelSufficiency state "seq-depth-6"
    (seqv [seqv [seqv [seqv [seqv [seqv [sv "a"]]]]]])

  -- Wide + deep (both dimensions at once)
  checkFuelSufficiency state "seq-wide-deep"
    (seqv [seqv [sv "a", sv "b", sv "c"],
           seqv [sv "d", sv "e"],
           seqv [sv "f"]])
  checkFuelSufficiency state "seq-deep-wide"
    (seqv [seqv [seqv [sv "a", sv "b"]],
           seqv [seqv [sv "c", sv "d"]]])

  -- Sequences containing mappings (mixed nesting)
  checkFuelSufficiency state "seq-with-map"
    (seqv [mapv [(sv "k", sv "v")]])
  checkFuelSufficiency state "seq-with-multi-map"
    (seqv [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")]])
  checkFuelSufficiency state "seq-with-nested-map"
    (seqv [mapv [(sv "outer", mapv [(sv "inner", sv "val")])]])
  checkFuelSufficiency state "seq-map-seq"
    (seqv [mapv [(sv "items", seqv [sv "x", sv "y"])]])

  -- Previously-failing patterns from P1 (inner commas at depth > 0)
  checkFuelSufficiency state "seq-prev-fail-1"
    (seqv [mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")], sv "after"])
  checkFuelSufficiency state "seq-prev-fail-2"
    (seqv [seqv [sv "a", sv "b"], mapv [(sv "c", sv "d"), (sv "e", sv "f")]])

  -- Deep mixed nesting (worst case for fuel)
  checkFuelSufficiency state "seq-deep-mixed-1"
    (seqv [mapv [(sv "a", seqv [mapv [(sv "b", seqv [sv "c"])]])]])
  checkFuelSufficiency state "seq-deep-mixed-2"
    (seqv [seqv [mapv [(sv "k", seqv [sv "v1", sv "v2"])],
                 mapv [(sv "j", mapv [(sv "m", sv "n")])]]])

  -- Extreme depth: 7 levels
  checkFuelSufficiency state "seq-depth-7"
    (seqv [seqv [seqv [seqv [seqv [seqv [seqv [sv "bottom"]]]]]]])

  -- Extreme width: 16 elements
  checkFuelSufficiency state "seq-width-16"
    (seqv (List.range 16 |>.map (fun i => sv s!"item{i}")))

  setCategory state "9b: parseStream_emitMapping fuel sufficiency"

  -- Empty mapping (base case)
  checkFuelSufficiency state "map-empty" (mapv [])

  -- Single entry
  checkFuelSufficiency state "map-1" (mapv [(sv "k", sv "v")])

  -- Two entries
  checkFuelSufficiency state "map-2" (mapv [(sv "k1", sv "v1"), (sv "k2", sv "v2")])

  -- Many entries (wide)
  checkFuelSufficiency state "map-6"
    (mapv [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3"),
           (sv "d", sv "4"), (sv "e", sv "5"), (sv "f", sv "6")])
  checkFuelSufficiency state "map-10"
    (mapv (List.range 10 |>.map (fun i => (sv s!"k{i}", sv s!"v{i}"))))

  -- Nested mappings (depth)
  checkFuelSufficiency state "map-depth-2"
    (mapv [(sv "outer", mapv [(sv "inner", sv "val")])])
  checkFuelSufficiency state "map-depth-3"
    (mapv [(sv "a", mapv [(sv "b", mapv [(sv "c", sv "val")])])])
  checkFuelSufficiency state "map-depth-4"
    (mapv [(sv "a", mapv [(sv "b", mapv [(sv "c", mapv [(sv "d", sv "val")])])])])
  checkFuelSufficiency state "map-depth-5"
    (mapv [(sv "1", mapv [(sv "2", mapv [(sv "3",
      mapv [(sv "4", mapv [(sv "5", sv "val")])])])])])

  -- Mappings with sequence values
  checkFuelSufficiency state "map-with-seq"
    (mapv [(sv "items", seqv [sv "x", sv "y"])])
  checkFuelSufficiency state "map-with-nested-seq"
    (mapv [(sv "data", seqv [seqv [sv "a", sv "b"], seqv [sv "c"]])])

  -- Mappings with complex keys
  checkFuelSufficiency state "map-seq-key"
    (mapv [(seqv [sv "a", sv "b"], sv "v")])
  checkFuelSufficiency state "map-map-key"
    (mapv [(mapv [(sv "inner", sv "key")], sv "v")])

  -- Many entries with complex values
  checkFuelSufficiency state "map-multi-complex"
    (mapv [(sv "items", seqv [sv "a", sv "b", sv "c"]),
           (sv "config", mapv [(sv "debug", sv "true"), (sv "level", sv "3")]),
           (sv "name", sv "test")])

  -- Deep mixed nesting
  checkFuelSufficiency state "map-deep-mixed-1"
    (mapv [(sv "a", seqv [mapv [(sv "b", seqv [sv "c", sv "d"])]])])
  checkFuelSufficiency state "map-deep-mixed-2"
    (mapv [(sv "x", mapv [(sv "y", seqv [mapv [(sv "z", sv "w")]])])])

  -- Wide + deep
  checkFuelSufficiency state "map-wide-deep"
    (mapv [(sv "a", seqv [sv "1", sv "2"]),
           (sv "b", mapv [(sv "c", sv "3")]),
           (sv "d", seqv [mapv [(sv "e", sv "4")]])])

  -- Extreme depth: 6 levels
  checkFuelSufficiency state "map-depth-6"
    (mapv [(sv "1", mapv [(sv "2", mapv [(sv "3",
      mapv [(sv "4", mapv [(sv "5", mapv [(sv "6", sv "val")])])])])])])

  -- Extreme width: 16 entries
  checkFuelSufficiency state "map-width-16"
    (mapv (List.range 16 |>.map (fun i => (sv s!"k{i}", sv s!"v{i}"))))

  -- Cross-type stress tests
  setCategory state "9a/9b: cross-type fuel stress"

  -- Alternating seq/map nesting
  checkFuelSufficiency state "cross-alt-1"
    (seqv [mapv [(sv "k", seqv [mapv [(sv "j", sv "v")]])]])
  checkFuelSufficiency state "cross-alt-2"
    (mapv [(sv "k", seqv [mapv [(sv "j", seqv [sv "a", sv "b"])]])])

  -- Wide at multiple levels
  checkFuelSufficiency state "cross-wide-multi"
    (seqv [mapv [(sv "a", sv "1"), (sv "b", sv "2")],
           mapv [(sv "c", sv "3"), (sv "d", sv "4")],
           seqv [sv "e", sv "f", sv "g"]])

  -- Complex realistic structure
  checkFuelSufficiency state "cross-realistic"
    (mapv [(sv "users",
            seqv [mapv [(sv "name", sv "alice"),
                        (sv "roles", seqv [sv "admin", sv "user"])],
                  mapv [(sv "name", sv "bob"),
                        (sv "roles", seqv [sv "user"])]]),
           (sv "version", sv "2.0")])

def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  test9g state
  test9h state
  test9cd state
  test9ab state
  let results ← finish state
  return { name := "adversarialinstantiation",
           label := "Adversarial Instantiation Tests (sorry audit)",
           sourceFile := "Tests/AdversarialInstantiation.lean",
           tests := results }

end Tests.AdversarialInstantiation
