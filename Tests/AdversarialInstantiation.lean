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

/-! ## Priority 4 — Theorem 9e (scanner prefix invariant)

Theorem `scanNextToken_prefix_and_sk_inv` claims that for each `scanNextToken` step
from `s` to `s'`, given any prefix index `n ≤ s.tokens.size`:

1. **Prefix preservation:** `∀ i < n, s'.tokens[i] = s.tokens[i]`
2. **Disjunctive SK/EK output invariant:** Either `s'.simpleKey.possible → s'.simpleKey.tokenIndex ≥ n`,
   or `s'.explicitKeyLine = none`.

**Corrected precondition**: The precondition uses `s.simpleKey.possible → tokenIndex ≥ n`
(NO disjunction). The original theorem had `∨ s.explicitKeyLine = none` in the precondition,
which was FALSE: adversarial testing found that when `ek = none` but `sk.possible = true`
and `sk.tokenIndex < n`, the scanner overwrites `tokens[sk.tokenIndex]` (placeholder → key),
violating prefix preservation. Counterexample: `"a: b"` at step 1.

The disjunction is correct in the OUTPUT (conclusion) because flow close operations restore
simpleKeys from the stack with tokenIndex potentially < n, but in those cases ek is none.

**Chain-level tests** verify that with `n₀` fixed at the initial state, both prefix
preservation and the strong SK invariant hold across the full scanning chain.
-/

/-- Check the prefix-and-sk invariant for one scanNextToken step.
    Uses the maximum valid n for which the precondition
    `sk.possible → sk.tokenIndex ≥ n` holds (the CORRECTED precondition
    after removing the false `∨ ek = none` disjunction).
    Returns `(n, prefixOk, skInvOk, origPrecondFails)`.
    `skInvOk` checks the disjunctive OUTPUT: `(sk'.possible → tokenIndex ≥ n) ∨ ek'=none`.
    `origPrecondFails` = true when the original (broken) theorem's disjunction
    would give a larger n that causes prefix violation. -/
private def checkPrefixSkStep (s s' : ScannerState) :
    Nat × Bool × Bool × Bool :=
  -- Max n where precondition (sk.possible → sk.tokenIndex ≥ n) holds:
  let n :=
    if s.simpleKey.possible then
      min s.simpleKey.tokenIndex s.tokens.size
    else
      s.tokens.size

  -- The n the original (broken) theorem would use (including second disjunct):
  let nOrig :=
    if s.explicitKeyLine.isNone then
      s.tokens.size  -- second disjunct allows max n
    else
      n  -- same as corrected

  -- 1. Prefix preservation for corrected n
  let prefixOk := (List.range n).all fun i =>
    if h : i < s.tokens.size then
      if h' : i < s'.tokens.size then
        s'.tokens[i] == s.tokens[i]
      else false
    else true

  -- 2. Disjunctive output invariant: (sk'.possible → tokenIndex ≥ n) ∨ ek'=none
  let skInvOk :=
    (if s'.simpleKey.possible then s'.simpleKey.tokenIndex ≥ n else true) ||
    s'.explicitKeyLine.isNone

  -- 3. Does the original (broken) precondition give a DIFFERENT (larger) n?
  let origPrecondFails := nOrig > n

  (n, prefixOk, skInvOk, origPrecondFails)

/-- Drive scanning step-by-step through an input string, checking the invariant at each step.
    Returns the number of steps taken and whether any check failed. -/
private def checkScanInvariant (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  let s0 := ScannerState.mk' input
  let s0 := s0.emit .streamStart
  -- Handle BOM
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.advance
    | _ => s0
  let fuel := (input.utf8ByteSize + 1) * 4
  let mut s := s0
  let mut step := 0
  let mut allPrefixOk := true
  let mut allSkInvOk := true
  let mut lastFailInfo := ""
  let mut minN := 999999  -- track minimum n across steps (diagnostic)
  let mut maxN := 0       -- track maximum n across steps (diagnostic)
  let mut origDisjunctIssues := 0  -- count steps where ∨ek=none gives bad n
  for _ in [:fuel] do
    match scanNextToken s with
    | .error e =>
      checkM state s!"{label}: no scan error" false s!"step {step}: {repr e}"
      return
    | .ok none =>
      -- End of input
      break
    | .ok (some s') =>
      let (n, prefixOk, skInvOk, origPrecondFails) := checkPrefixSkStep s s'
      if n < minN then minN := n
      if n > maxN then maxN := n
      if !prefixOk then
        allPrefixOk := false
        lastFailInfo := s!"prefix fail at step {step}, n={n}, s.tokens={s.tokens.size}→s'.tokens={s'.tokens.size}, sk.possible={s.simpleKey.possible}, sk.tokenIndex={s.simpleKey.tokenIndex}, ek={repr s.explicitKeyLine}"
      if !skInvOk then
        allSkInvOk := false
        lastFailInfo := s!"sk_inv fail at step {step}: sk.possible={s'.simpleKey.possible}, sk.tokenIndex={s'.simpleKey.tokenIndex}, n={n}, explicitKeyLine={repr s'.explicitKeyLine}"
      if origPrecondFails then
        origDisjunctIssues := origDisjunctIssues + 1
      s := s'
      step := step + 1
  checkM state s!"{label}: prefix preserved ({step} steps, n∈[{minN},{maxN}])" allPrefixOk lastFailInfo
  checkM state s!"{label}: sk/ek output invariant ({step} steps)" allSkInvOk lastFailInfo
  -- Report steps where the original theorem's ∨ek=none disjunct would allow
  -- a larger n that causes prefix violation (counterexample to original statement)
  if origDisjunctIssues > 0 then
    check state s!"{label}: original h_cond disjunct issues ({origDisjunctIssues} steps)" true

/-- Check the chain-level invariant: fix `n₀` at the initial state and verify that
    1. prefix preservation (`∀ i < n₀, s_k.tokens[i] = s₀.tokens[i]`) holds at EVERY step
    2. strong SK invariant (`sk_k.possible → tokenIndex_k ≥ n₀`) holds at EVERY step
    This tests whether `ScanChain_preserves_raw_prefix` can work without the
    `∨ explicitKeyLine = none` disjunction. -/
private def checkChainInvariant (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  let s0 := ScannerState.mk' input
  let s0 := s0.emit .streamStart
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.advance
    | _ => s0
  -- Fix n₀ at start: max n where sk.possible → tokenIndex ≥ n₀
  let n₀ :=
    if s0.simpleKey.possible then
      min s0.simpleKey.tokenIndex s0.tokens.size
    else
      s0.tokens.size
  let fuel := (input.utf8ByteSize + 1) * 4
  let mut s := s0
  let mut step := 0
  let mut allPrefixOk := true
  let mut allStrongSkOk := true
  let mut lastFailInfo := ""
  for _ in [:fuel] do
    match scanNextToken s with
    | .error e =>
      checkM state s!"{label} chain: no scan error" false s!"step {step}: {repr e}"
      return
    | .ok none => break
    | .ok (some s') =>
      -- Chain prefix: s'.tokens[i] = s₀.tokens[i] for i < n₀
      let chainPrefixOk := (List.range n₀).all fun i =>
        if h : i < s0.tokens.size then
          if h' : i < s'.tokens.size then
            s'.tokens[i] == s0.tokens[i]
          else false
        else true
      -- Strong SK at every intermediate state
      let strongSkOk :=
        if s'.simpleKey.possible then s'.simpleKey.tokenIndex ≥ n₀ else true
      if !chainPrefixOk then
        allPrefixOk := false
        lastFailInfo := s!"chain prefix fail at step {step}, n₀={n₀}, s'.tokens.size={s'.tokens.size}"
      if !strongSkOk then
        allStrongSkOk := false
        lastFailInfo := s!"chain sk fail at step {step}: sk'.possible={s'.simpleKey.possible}, sk'.tokenIndex={s'.simpleKey.tokenIndex}, n₀={n₀}"
      s := s'
      step := step + 1
  checkM state s!"{label} chain: prefix preserved (n₀={n₀}, {step} steps)" allPrefixOk lastFailInfo
  checkM state s!"{label} chain: strong sk invariant (n₀={n₀}, {step} steps)" allStrongSkOk lastFailInfo

/-! ## Priority 4 Test Suites -/

private def test9e (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "9e: scanNextToken_prefix_and_sk_inv"

  -- Flow indicators (exercises dispatchFlowIndicators)
  checkScanInvariant state "flow-seq-empty" "[]"
  checkScanInvariant state "flow-seq-1" "[a]"
  checkScanInvariant state "flow-seq-2" "[a, b]"
  checkScanInvariant state "flow-seq-3" "[a, b, c]"
  checkScanInvariant state "flow-map-empty" "{}"
  checkScanInvariant state "flow-map-1" "{a: b}"
  checkScanInvariant state "flow-map-2" "{a: b, c: d}"

  -- Nested flow (exercises simpleKeyStack save/restore)
  checkScanInvariant state "flow-nested-1" "[[a, b], c]"
  checkScanInvariant state "flow-nested-2" "[{a: b}, c]"
  checkScanInvariant state "flow-nested-3" "{a: [b, c]}"
  checkScanInvariant state "flow-nested-deep" "[[[a]]]"
  checkScanInvariant state "flow-nested-mixed" "[{a: [b, {c: d}]}, e]"

  -- Quoted scalars (exercises scanFlowScalar / scanDoubleQuotedScalar)
  checkScanInvariant state "dquoted" "\"hello world\""
  checkScanInvariant state "squoted" "'hello world'"
  checkScanInvariant state "dquoted-escape" "\"line1\\nline2\""
  checkScanInvariant state "dquoted-unicode" "\"\\u0041\""
  checkScanInvariant state "flow-dquoted" "[\"a\", \"b\"]"
  checkScanInvariant state "flow-squoted" "['a', 'b']"

  -- Block scalars (exercises scanBlockScalar)
  checkScanInvariant state "block-literal" "|\n  line1\n  line2"
  checkScanInvariant state "block-folded" ">\n  line1\n  line2"

  -- Block sequences (exercises scanBlockEntry)
  checkScanInvariant state "block-seq-1" "- a"
  checkScanInvariant state "block-seq-2" "- a\n- b"
  checkScanInvariant state "block-seq-3" "- a\n- b\n- c"
  checkScanInvariant state "block-seq-nested" "- - a\n  - b"

  -- Block mappings (exercises scanKey / scanValue)
  checkScanInvariant state "block-map-1" "a: b"
  checkScanInvariant state "block-map-2" "a: b\nc: d"
  checkScanInvariant state "block-map-nested" "a:\n  b: c"
  checkScanInvariant state "block-map-deep" "a:\n  b:\n    c: d"

  -- Explicit keys (exercises explicit key path — sets explicitKeyLine)
  checkScanInvariant state "explicit-key" "? a\n: b"
  checkScanInvariant state "explicit-key-flow" "{? a: b}"

  -- Document markers (exercises scanDocumentStart / scanDocumentEnd)
  checkScanInvariant state "doc-start" "---\na: b"
  checkScanInvariant state "doc-end" "a: b\n..."
  checkScanInvariant state "multi-doc" "---\na: b\n...\n---\nc: d"

  -- Directives (exercises scanDirective)
  checkScanInvariant state "yaml-directive" "%YAML 1.2\n---\na: b"
  checkScanInvariant state "tag-directive" "%TAG !t! tag:example.com,2000:\n---\na: b"

  -- Mixed flow/block
  checkScanInvariant state "block-with-flow-val" "items: [a, b, c]"
  checkScanInvariant state "block-with-flow-map" "config: {debug: true}"
  checkScanInvariant state "block-seq-flow-vals" "- [a, b]\n- {c: d}"

  -- Comments (exercises comment scanning)
  checkScanInvariant state "comment-line" "# comment\na: b"
  checkScanInvariant state "comment-inline" "a: b # comment"
  checkScanInvariant state "comment-only" "# just a comment"

  -- Anchors and aliases (exercises anchor/alias scanning)
  checkScanInvariant state "anchor" "&anc a"
  checkScanInvariant state "anchor-alias" "&anc a\n*anc"
  checkScanInvariant state "anchor-flow" "[&anc a, *anc]"

  -- Tags (exercises tag scanning)
  checkScanInvariant state "tag-named" "!!str hello"
  checkScanInvariant state "tag-verbatim" "!<tag:yaml.org,2002:str> hello"

  -- Empty/minimal inputs
  checkScanInvariant state "empty" ""
  checkScanInvariant state "whitespace-only" "   "
  checkScanInvariant state "newline-only" "\n"
  checkScanInvariant state "just-scalar" "hello"

  -- Plain scalars with tricky chars
  checkScanInvariant state "plain-colon-space" "a : b"
  checkScanInvariant state "plain-multiword" "hello world"

  -- Emitter output (exercises exact token patterns from theorems 9a/9b)
  checkScanInvariant state "emit-seq" (emit (seqv [sv "a", sv "b"]))
  checkScanInvariant state "emit-map" (emit (mapv [(sv "k", sv "v")]))
  checkScanInvariant state "emit-nested"
    (emit (seqv [mapv [(sv "k", seqv [sv "a", sv "b"])]]))
  checkScanInvariant state "emit-deep"
    (emit (seqv [seqv [seqv [seqv [sv "a"]]]]))
  checkScanInvariant state "emit-wide"
    (emit (mapv [(sv "a", sv "1"), (sv "b", sv "2"), (sv "c", sv "3"),
                 (sv "d", sv "4"), (sv "e", sv "5"), (sv "f", sv "6")]))
  checkScanInvariant state "emit-complex"
    (emit (mapv [(sv "users",
                  seqv [mapv [(sv "name", sv "alice"),
                              (sv "roles", seqv [sv "admin", sv "user"])],
                        mapv [(sv "name", sv "bob"),
                              (sv "roles", seqv [sv "user"])]]),
                 (sv "version", sv "2.0")]))

  -- Stress: many steps (deep block nesting)
  checkScanInvariant state "deep-block"
    "a:\n  b:\n    c:\n      d:\n        e:\n          f: val"

  -- Stress: wide block sequence
  checkScanInvariant state "wide-block-seq"
    "- a\n- b\n- c\n- d\n- e\n- f\n- g\n- h\n- i\n- j"

  -- Stress: mixed everything
  checkScanInvariant state "kitchen-sink"
    "%YAML 1.2\n---\nitems:\n  - name: \"alice\"\n    roles: [admin, user]\n  - name: 'bob'\n    tags:\n      ? key1\n      : val1\n...\n---\nsecond: doc"

  -- Chain-level invariant tests (fixed n₀ across all steps)
  checkChainInvariant state "flow-seq-2" "[a, b]"
  checkChainInvariant state "flow-map-1" "{a: b}"
  checkChainInvariant state "flow-nested-mixed" "[{a: [b, {c: d}]}, e]"
  checkChainInvariant state "block-map-1" "a: b"
  checkChainInvariant state "block-map-2" "a: b\nc: d"
  checkChainInvariant state "block-seq-2" "- a\n- b"
  checkChainInvariant state "explicit-key" "? a\n: b"
  checkChainInvariant state "multi-doc" "---\na: b\n...\n---\nc: d"
  checkChainInvariant state "emit-nested"
    (emit (seqv [mapv [(sv "k", seqv [sv "a", sv "b"])]]))
  checkChainInvariant state "kitchen-sink"
    "%YAML 1.2\n---\nitems:\n  - name: \"alice\"\n    roles: [admin, user]\n  - name: 'bob'\n    tags:\n      ? key1\n      : val1\n...\n---\nsecond: doc"

/-! ## Priority 5 — ScannerBound theorems (BoundInv preservation)

Three sorry'd theorems in `ScannerBound.lean` claim that `BoundInv` is preserved
through scanner dispatch phases:

- `preprocess_preserves_bound`: `scanNextToken_preprocess` preserves BoundInv
  (involves `skipToContent` loop, `unwindIndents` loop, `saveSimpleKey`)
- `dispatchStructural_preserves_bound`: `scanNextToken_dispatchStructural` preserves BoundInv
  (involves `scanDocumentStart`/`scanDocumentEnd` with `advanceN 3`, `scanDirective` with loops)
- `dispatchContent_preserves_bound`: `scanNextToken_dispatchContent` preserves BoundInv
  (involves ALL scalar scanners, anchor/alias/tag scanners — all loop-based)

`BoundInv s₀ s` bundles four properties:
1. `s.offset ≤ s.inputEnd` (offset in bounds)
2. `s.inputEnd = s₀.inputEnd` (input end preserved)
3. `s.input = s₀.input` (input string preserved)
4. `String.Pos.Raw.IsValid s.input ⟨s.offset⟩` (offset at valid UTF-8 boundary)

We test by stepping through `scanNextToken` on diverse inputs, checking all four
properties at every step. Special emphasis on:
- Deep indent stacks (stresses `unwindIndents` loop)
- Multi-line scalars (stresses scalar scanner loops)
- UTF-8 multi-byte characters (stresses byte offset arithmetic)
-/

/-- Check whether a byte offset is at a valid UTF-8 character boundary in a string.
    Iterates through valid positions from the start. -/
private def isAtCharBoundary (s : String) (offset : Nat) : Bool :=
  if offset == s.utf8ByteSize then true  -- one-past-end is valid
  else
    let rec go (byteIdx : Nat) (fuel : Nat) : Bool :=
      if fuel = 0 then false
      else if byteIdx == offset then true
      else if byteIdx ≥ s.utf8ByteSize then false
      else go (String.Pos.Raw.next s ⟨byteIdx⟩).byteIdx (fuel - 1)
    go 0 (s.utf8ByteSize + 1)

/-- Check BoundInv properties for one scanNextToken step.
    Returns `(offsetOk, inputEndOk, inputOk, isValidOk)`. -/
private def checkBoundInv (s₀ s' : ScannerState) :
    Bool × Bool × Bool × Bool :=
  let offsetOk := s'.offset ≤ s'.inputEnd
  let inputEndOk := s'.inputEnd == s₀.inputEnd
  let inputOk := s'.input == s₀.input
  let isValidOk := isAtCharBoundary s'.input s'.offset
  (offsetOk, inputEndOk, inputOk, isValidOk)

/-- Drive scanning step-by-step, checking BoundInv at every step. -/
private def checkBoundInvariant (state : IO.Ref TestCollector)
    (label : String) (input : String) : IO Unit := do
  let s0 := ScannerState.mk' input
  let s0 := s0.emit .streamStart
  let s0 := match s0.peek? with
    | some '\uFEFF' => s0.advance
    | _ => s0
  let fuel := (input.utf8ByteSize + 1) * 4
  let mut s := s0
  let mut step := 0
  let mut allOffsetOk := true
  let mut allInputEndOk := true
  let mut allInputOk := true
  let mut allIsValidOk := true
  let mut lastFailInfo := ""
  for _ in [:fuel] do
    match scanNextToken s with
    | .error _e =>
      -- Scan errors are fine for malformed inputs; just stop
      break
    | .ok none => break
    | .ok (some s') =>
      let (offsetOk, inputEndOk, inputOk, isValidOk) := checkBoundInv s0 s'
      if !offsetOk then
        allOffsetOk := false
        lastFailInfo := s!"offset fail at step {step}: offset={s'.offset}, inputEnd={s'.inputEnd}"
      if !inputEndOk then
        allInputEndOk := false
        lastFailInfo := s!"inputEnd fail at step {step}: s'.inputEnd={s'.inputEnd}, s₀.inputEnd={s0.inputEnd}"
      if !inputOk then
        allInputOk := false
        lastFailInfo := s!"input fail at step {step}: s'.input ≠ s₀.input"
      if !isValidOk then
        allIsValidOk := false
        lastFailInfo := s!"isValid fail at step {step}: offset={s'.offset} not at char boundary"
      s := s'
      step := step + 1
  checkM state s!"{label}: offset ≤ inputEnd ({step} steps)" allOffsetOk lastFailInfo
  checkM state s!"{label}: inputEnd preserved ({step} steps)" allInputEndOk lastFailInfo
  checkM state s!"{label}: input preserved ({step} steps)" allInputOk lastFailInfo
  checkM state s!"{label}: offset at char boundary ({step} steps)" allIsValidOk lastFailInfo

/-! ## Priority 5 Test Suites -/

private def test5_bound (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "5: BoundInv preservation (preprocess/structural/content)"

  -- === preprocess_preserves_bound: skipToContent + unwindIndents ===

  -- Deep indent stacks (stress unwindIndents loop)
  checkBoundInvariant state "indent-2"
    "a:\n  b: c"
  checkBoundInvariant state "indent-3"
    "a:\n  b:\n    c: d"
  checkBoundInvariant state "indent-4"
    "a:\n  b:\n    c:\n      d: e"
  checkBoundInvariant state "indent-6"
    "a:\n  b:\n    c:\n      d:\n        e:\n          f: g"
  checkBoundInvariant state "indent-8"
    "a:\n  b:\n    c:\n      d:\n        e:\n          f:\n            g:\n              h: i"
  -- Deep then unwind (deep nesting followed by deindent triggers unwindIndents)
  checkBoundInvariant state "indent-unwind"
    "a:\n  b:\n    c: d\ne: f"
  checkBoundInvariant state "indent-unwind-deep"
    "a:\n  b:\n    c:\n      d: e\n  f: g\nh: i"
  -- Multiple sequence entries (repeated indent/unwind cycles)
  checkBoundInvariant state "seq-indent-cycle"
    "items:\n  - a\n  - b\n  - c\nother: x"

  -- Whitespace/comment skipping (skipToContent loop)
  checkBoundInvariant state "skip-spaces"
    "   a: b"
  checkBoundInvariant state "skip-tabs"
    "\t\ta: b"
  checkBoundInvariant state "skip-comment"
    "# comment\na: b"
  checkBoundInvariant state "skip-multi-comment"
    "# line1\n# line2\n# line3\na: b"
  checkBoundInvariant state "skip-blank-lines"
    "\n\n\na: b"
  checkBoundInvariant state "skip-mixed"
    "  # comment\n\n  # another\na: b"

  -- === dispatchStructural_preserves_bound: doc markers + directives ===

  -- Document start (advanceN 3)
  checkBoundInvariant state "doc-start"
    "---\na: b"
  -- Document end (advanceN 3)
  checkBoundInvariant state "doc-end"
    "a: b\n..."
  -- Multi-document (repeated doc start/end)
  checkBoundInvariant state "multi-doc"
    "---\na: b\n...\n---\nc: d\n..."
  -- YAML directive (loop-based)
  checkBoundInvariant state "yaml-directive"
    "%YAML 1.2\n---\na: b"
  -- TAG directive (loop-based)
  checkBoundInvariant state "tag-directive"
    "%TAG !t! tag:example.com,2000:\n---\na: b"
  -- Multiple directives
  checkBoundInvariant state "multi-directive"
    "%YAML 1.2\n%TAG !t! tag:example.com,2000:\n%TAG !u! tag:example.org,2026:\n---\na: b"

  -- === dispatchContent_preserves_bound: scalar/anchor/tag scanners ===

  -- Double-quoted scalars (loop-based)
  checkBoundInvariant state "dquoted-simple"
    "\"hello\""
  checkBoundInvariant state "dquoted-escape"
    "\"line1\\nline2\\ttab\""
  checkBoundInvariant state "dquoted-unicode-escape"
    "\"\\u0041\\u00E9\\U0001F600\""
  checkBoundInvariant state "dquoted-long"
    "\"abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ\""
  checkBoundInvariant state "dquoted-multiline"
    "\"line1\n  line2\n  line3\""
  checkBoundInvariant state "dquoted-empty"
    "\"\""

  -- Single-quoted scalars (loop-based)
  checkBoundInvariant state "squoted-simple"
    "'hello'"
  checkBoundInvariant state "squoted-escape"
    "'it''s escaped'"
  checkBoundInvariant state "squoted-long"
    "'abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'"
  checkBoundInvariant state "squoted-multiline"
    "'line1\n  line2\n  line3'"

  -- Block scalars (loop-based)
  checkBoundInvariant state "block-literal"
    "|\n  line1\n  line2\n  line3"
  checkBoundInvariant state "block-folded"
    ">\n  line1\n  line2\n  line3"
  checkBoundInvariant state "block-literal-long"
    "|\n  abcdefghijklmnopqrstuvwxyz\n  0123456789ABCDEF\n  final"
  checkBoundInvariant state "block-keep"
    "|+\n  line1\n  line2\n"
  checkBoundInvariant state "block-strip"
    "|-\n  line1\n  line2"
  checkBoundInvariant state "block-indent"
    "|2\n  line1\n  line2"

  -- Plain scalars (loop-based, implicit)
  checkBoundInvariant state "plain-simple"
    "hello"
  checkBoundInvariant state "plain-multiword"
    "hello world"
  checkBoundInvariant state "plain-long"
    "abcdefghijklmnopqrstuvwxyz0123456789"
  checkBoundInvariant state "plain-multiline"
    "line1\n  line2\n  line3"

  -- Anchor scanner (loop-based)
  checkBoundInvariant state "anchor-short"
    "&a value"
  checkBoundInvariant state "anchor-long"
    "&longanchorname value"
  checkBoundInvariant state "alias-short"
    "&a value\n*a"
  checkBoundInvariant state "alias-long"
    "&longanchorname value\n*longanchorname"

  -- Tag scanner (loop-based)
  checkBoundInvariant state "tag-named"
    "!!str hello"
  checkBoundInvariant state "tag-verbatim"
    "!<tag:yaml.org,2002:str> hello"
  checkBoundInvariant state "tag-custom"
    "!custom hello"

  -- === UTF-8 multi-byte characters (byte offset arithmetic) ===

  checkBoundInvariant state "utf8-2byte"
    "key: résumé"
  checkBoundInvariant state "utf8-3byte"
    "key: 日本語"
  checkBoundInvariant state "utf8-4byte"
    "key: 𝕊𝕖𝕥"
  checkBoundInvariant state "utf8-mixed"
    "名前: résumé\n値: 𝕊𝕖𝕥"
  checkBoundInvariant state "utf8-dquoted"
    "\"résumé café naïve\""
  checkBoundInvariant state "utf8-squoted"
    "'日本語テスト'"
  checkBoundInvariant state "utf8-plain"
    "日本語テスト"
  checkBoundInvariant state "utf8-anchor"
    "&名前 日本語"
  checkBoundInvariant state "utf8-tag"
    "!!str 日本語"
  checkBoundInvariant state "utf8-block-literal"
    "|\n  日本語\n  中文\n  한국어"
  checkBoundInvariant state "utf8-deep"
    "名前:\n  性: 田中\n  名:\n    漢字: 太郎\n    読み: たろう"
  -- Emoji (4-byte UTF-8)
  checkBoundInvariant state "utf8-emoji"
    "mood: \"😀😎🎉\""
  -- Mixed ASCII and multi-byte in flow
  checkBoundInvariant state "utf8-flow"
    "[résumé, 日本語, 𝕊𝕖𝕥]"
  checkBoundInvariant state "utf8-flow-map"
    "{名前: 太郎, 年齢: \"25\"}"

  -- === Combined / stress tests ===

  -- All dispatch phases in one input
  checkBoundInvariant state "all-phases"
    "%YAML 1.2\n---\nitems:\n  - \"quoted\"\n  - 'single'\n  - &anc plain\n  - *anc\n  - !!str tagged\n  - |\n    block\n...\n---\nsecond: doc"

  -- Deep nesting with flow (unwind + flow dispatch)
  checkBoundInvariant state "deep-flow-nested"
    "a:\n  b:\n    c: [{d: [e, f]}, {g: [h]}]"

  -- Wide block sequence with mixed content
  checkBoundInvariant state "wide-mixed-content"
    "- \"q1\"\n- 'q2'\n- plain\n- &a val\n- *a\n- !!int 42\n- |\n  block\n- >\n  folded"

  -- Emitter output (exercises the exact patterns theorems care about)
  checkBoundInvariant state "emit-seq"
    (emit (seqv [sv "a", sv "b", sv "c"]))
  checkBoundInvariant state "emit-map"
    (emit (mapv [(sv "k", sv "v"), (sv "k2", sv "v2")]))
  checkBoundInvariant state "emit-nested"
    (emit (seqv [mapv [(sv "k", seqv [sv "a", sv "b"])]]))
  checkBoundInvariant state "emit-deep"
    (emit (seqv [seqv [seqv [seqv [sv "a"]]]]))
  checkBoundInvariant state "emit-complex"
    (emit (mapv [(sv "users",
                  seqv [mapv [(sv "name", sv "alice"),
                              (sv "roles", seqv [sv "admin", sv "user"])],
                        mapv [(sv "name", sv "bob"),
                              (sv "roles", seqv [sv "user"])]]),
                 (sv "version", sv "2.0")]))

  -- UTF-8 emitter output
  checkBoundInvariant state "emit-utf8"
    (emit (mapv [(sv "名前", sv "太郎"), (sv "値", sv "résumé")]))

  -- Edge cases
  checkBoundInvariant state "empty"
    ""
  checkBoundInvariant state "whitespace-only"
    "   "
  checkBoundInvariant state "newlines-only"
    "\n\n\n"
  checkBoundInvariant state "bom"
    "\uFEFF---\na: b"

def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  test9g state
  test9h state
  test9cd state
  test9ab state
  test9e state
  test5_bound state
  let results ← finish state
  return { name := "adversarialinstantiation",
           label := "Adversarial Instantiation Tests (sorry audit)",
           sourceFile := "Tests/AdversarialInstantiation.lean",
           tests := results }

end Tests.AdversarialInstantiation
