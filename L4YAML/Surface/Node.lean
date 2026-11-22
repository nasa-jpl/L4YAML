/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Surface.Scalars


public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-!
# Node & Collection Surface Syntax — Chapters 7.4 & 8.2

Mutually recursive surface syntax predicates for YAML flow collections,
block collections, and the node dispatchers that tie them together.

This module contains the core mutual recursion of the YAML grammar:
- Block nodes contain block sequences/mappings which contain block nodes
- Block nodes can also be flow nodes, which contain flow sequences/mappings
- Flow collections contain flow nodes which can be scalars or nested collections

## Mutual Recursion Structure

```
SBlockNode ─→ SBlockSeqEntries ─→ SBlockIndented ─→ SBlockNode
           ─→ SBlockMapEntries ─→ SBlockNode
           ─→ SFlowNode ─→ SFlowSeqEntries ─→ SFlowNode
                         ─→ SFlowMapEntries ─→ SFlowNode
           ─→ SCompactSeq ─→ SBlockIndented
           ─→ SCompactMap ─→ SBlockNode
```

## Productions Covered

- **Flow collections**: [134]-[146] c-flow-sequence, ns-s-flow-seq-entries,
  ns-flow-seq-entry, c-flow-mapping, ns-s-flow-map-entries, ns-flow-map-entry
- **Flow node**: [154]-[161] c-flow-json-content, ns-flow-yaml-content,
  ns-flow-content, ns-flow-node, c-s-implicit-json-key, ns-s-implicit-yaml-key
- **Block sequences**: [180]-[183] l+block-sequence, c-l-block-seq-entry,
  s-l+block-indented, ns-l-compact-sequence
- **Block mappings**: [184]-[199] l+block-mapping, ns-l-block-map-entry,
  c-l-block-map-explicit-entry/key/value, ns-l-block-map-implicit-entry,
  ns-s-block-map-implicit-key, c-l-block-map-implicit-value,
  ns-l-compact-mapping
- **Block node**: [195]-[199] s-l+flow-in-block, s-l+block-in-block,
  s-l+block-scalar, s-l+block-collection, s-l+block-node
-/

set_option autoImplicit false

namespace L4YAML.Surface

open L4YAML (YamlContext)

/-! ## Mutual Block: Nodes + Collections

All 11 mutually recursive types defined together.
The types reference scalar productions (from Surface.Scalars) and basic
productions (from Surface.Basic) which are defined non-recursively. -/

mutual

  /-- [196] s-l+block-node(n,c): block-context YAML node.
      Can be a block scalar, block collection, flow node, or empty node. -/
  @[yaml_spec "8.2.3" 196 "s-l+block-node(n,c)"]
  inductive SBlockNode : Nat → YamlContext → SurfPos → SurfPos → Prop where
    /-- [198] Block scalar: separator + optional properties + literal or folded.
        Note: n is the content indent level (= spec's n+1, since we use
        n_lean = n_spec + 1 to avoid Int). -/
    | blockLiteral (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SSeparate n c s s₁ →
        GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂ →
        SCLLiteral n s₂ s' →
        SBlockNode n c s s'
    | blockFolded (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SSeparate n c s s₁ →
        GOpt (GSeq (SCNsProperties n c) (SSeparate n c)) s₁ s₂ →
        SCLFolded n s₂ s' →
        SBlockNode n c s s'
    /-- [199] Block sequence: optional properties + comments + sequence.

        `m` is `[183] l+block-sequence(n)`'s **auto-detected extra indentation**
        — the production is `( s-indent(n+m) c-l-block-seq-entry(n+m) )+` for
        some `m > 0` fixed once for the whole collection, so it is bound HERE,
        on the constructor that opens the collection, and threaded into the
        entries' shared index.  (Item 22.  Inlining it at its smallest legal
        value, as this constructor did through item 21, makes every indented
        block sequence — `  - a`, `a:⏎  - x` — underivable; binding it inside
        `SBlockSeqEntries` instead would admit ragged indentation.  Reflection
        647.) -/
    | blockSeq (n : Nat) (c : YamlContext) (m : Nat) (s s₁ s₂ s' : SurfPos) :
        GOpt (GSeq (SSeparate n c) (SCNsProperties n c)) s s₁ →
        SSLComments s₁ s₂ →
        SBlockSeqEntries (seqSpaces n c + m) s₂ s' →
        SBlockNode n c s s'
    /-- [199] Block mapping: optional properties + comments + mapping.

        `m` is `[187] l+block-mapping(n)`'s auto-detected extra indentation,
        bound exactly as `blockSeq`'s above. -/
    | blockMap (n : Nat) (c : YamlContext) (m : Nat) (s s₁ s₂ s' : SurfPos) :
        GOpt (GSeq (SSeparate n c) (SCNsProperties n c)) s s₁ →
        SSLComments s₁ s₂ →
        SBlockMapEntries (n + m) s₂ s' →
        SBlockNode n c s s'
    /-- [195] Flow-in-block: separator + flow node + comments. -/
    | flowInBlock (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SSeparate n .flowOut s s₁ →
        SFlowNode n .flowOut s₁ s₂ →
        SSLComments s₂ s' →
        SBlockNode n c s s'
    /-- [72] Empty node + trailing comments. -/
    | emptyNode (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SSLComments s s' →
        SBlockNode n c s s'

  /-- [185] s-l+block-indented(n,c): content inside a block entry.
      Can be compact notation, a regular block node, or empty.

      **The compact index is `n+1+m`, not `n+m`** (item 33).  The production
      is reached from `[184] c-l-block-seq-entry(n)` — `'-' s-l+block-indented`
      — at the position immediately AFTER the indicator, so the entry's own
      `s-indent(n)` has already been spent and the `-` occupies one more
      column; `s-indent(m)` then walks `m` further.  A compact entry therefore
      sits at column `n+1+m`, which is the width `[186] ns-l-compact-sequence`
      and `[195] ns-l-compact-mapping` require of their SIBLINGS: in `- - a`
      the inner `-` is at column 2 = 0+1+1, and `- - a⏎  - b`'s second entry
      is indented to that same column.  Written `n+m` these two constructors
      named a collection one column to the left of the one the input has.

      Both survived unnoticed because they are the only alternatives of `[185]`
      with NO producer and NO consumer anywhere in the tree — nothing ever
      instantiated the index, so nothing could disagree with it.  Building
      their first consumer is what evaluated them. -/
  @[yaml_spec "8.2.1" 185 "s-l+block-indented(n,c)"]
  inductive SBlockIndented : Nat → YamlContext → SurfPos → SurfPos → Prop where
    /-- Compact sequence: indent(m) + compact-sequence(n+1+m). -/
    | compactSeq (n : Nat) (c : YamlContext) (m : Nat) (s s₁ s' : SurfPos) :
        SIndent m s s₁ →
        SCompactSeq (n + 1 + m) s₁ s' →
        SBlockIndented n c s s'
    /-- Compact mapping: indent(m) + compact-mapping(n+1+m). -/
    | compactMap (n : Nat) (c : YamlContext) (m : Nat) (s s₁ s' : SurfPos) :
        SIndent m s s₁ →
        SCompactMap (n + 1 + m) s₁ s' →
        SBlockIndented n c s s'
    /-- Regular block node.

        **The node index is `n + 1`, not `n`** (item 179).  `[185]`'s
        alternative is `s-l+block-node(n,c)` at the SPEC's parameter, and
        `SBlockNode` is the one type in this tree indexed `n_lean = n_spec + 1`
        (`SLBareDocument`'s convention, stated on `[198]`'s docstring above) —
        `SBlockIndented`'s own `n` is the raw entry column, so the crossing
        adds the one.  Written `n` this arm fed the node's separators and
        collections an index one too small, which is what admitted the
        at-column value readings (`k:⏎a`, the equal-width nested map) the
        runtime refuses — item 107's `m = 0` families, Finding A's encoding
        half. -/
    | node (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SBlockNode (n + 1) c s s' →
        SBlockIndented n c s s'
    /-- Empty node + comments. -/
    | empty (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SSLComments s s' →
        SBlockIndented n c s s'

  /-- [183] l+block-sequence(n): one or more block sequence entries.
      Each entry = s-indent(N) + '-' + s-l+block-indented(N,BLOCK-IN), where
      the index `N` is the production's ALREADY-DETECTED `n+m` — the whole
      collection shares it, and `SBlockNode.blockSeq` is where `m` is chosen
      (item 22).  The '-' indicator must NOT be followed by ns-char
      (distinguishes block entry from plain scalar starting with '-'). -/
  @[yaml_spec "8.2.1" 183 "l+block-sequence(n)"]
  inductive SBlockSeqEntries : Nat → SurfPos → SurfPos → Prop where
    | single (n : Nat) (s s₁ s₂ s₃ s' : SurfPos) :
        SIndent n s s₁ →
        GLit '-' s₁ s₂ →
        GNot SNsChar s₂ →
        SBlockIndented n .blockIn s₂ s' →
        SBlockSeqEntries n s s'
    | cons (n : Nat) (s s₁ s₂ s₃ s' : SurfPos) :
        SIndent n s s₁ →
        GLit '-' s₁ s₂ →
        GNot SNsChar s₂ →
        SBlockIndented n .blockIn s₂ s₃ →
        SBlockSeqEntries n s₃ s' →
        SBlockSeqEntries n s s'

  /-- [188] ns-l-block-map-entry(n): explicit or implicit mapping entry. -/
  @[yaml_spec "8.2.2" 188 "ns-l-block-map-entry(n)"]
  inductive SBlockMapEntry : Nat → SurfPos → SurfPos → Prop where
    /-- [186] Explicit entry: '?' key + ':' value. -/
    | explicit (n : Nat) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        GLit '?' s s₁ →
        SBlockIndented n .blockOut s₁ s₂ →
        SIndent n s₂ s₃ →
        GLit ':' s₃ s₄ →
        SBlockIndented n .blockOut s₄ s' →
        SBlockMapEntry n s s'
    /-- [186] Explicit entry whose VALUE is empty — `? a` with no `:` line at
        all.  The production's tail is `( l-block-map-explicit-value(n) |
        e-node )`, so the value is optional and its `e-node` alternative is
        zero-width: the entry ends exactly where its key does.  (Item 20; the
        `explicit` arm above is the other alternative, and without this one
        `? a`, `?`, `? [1]` and every key-only entry parsed correctly with no
        derivation.) -/
    | explicitEmpty (n : Nat) (s s₁ s' : SurfPos) :
        GLit '?' s s₁ →
        SBlockIndented n .blockOut s₁ s' →
        SBlockMapEntry n s s'
    /-- [189] Implicit key + ':' + block node.

        The value's node index is `n + 1` for the same reason as
        `SBlockIndented.node`'s (item 179): the implicit value production
        spends `s-l+block-node(n, block-out)` at the spec's parameter, and
        `n_lean = n_spec + 1` on `SBlockNode` alone. -/
    | implicitKeyNode (n : Nat) (s s₁ s₂ s' : SurfPos) :
        SImplicitKey s s₁ →
        GLit ':' s₁ s₂ →
        SBlockNode (n + 1) .blockOut s₂ s' →
        SBlockMapEntry n s s'
    /-- [189] Implicit key + ':' + empty value (comments). -/
    | implicitKeyEmpty (n : Nat) (s s₁ s₂ s' : SurfPos) :
        SImplicitKey s s₁ →
        GLit ':' s₁ s₂ →
        SSLComments s₂ s' →
        SBlockMapEntry n s s'
    /-- [189] Empty key + ':' + block node.  The value's node index is `n + 1`,
        as on `implicitKeyNode` (item 179). -/
    | emptyKeyNode (n : Nat) (s s₁ s' : SurfPos) :
        GLit ':' s s₁ →
        SBlockNode (n + 1) .blockOut s₁ s' →
        SBlockMapEntry n s s'
    /-- [189] Empty key + ':' + comments. -/
    | emptyKeyEmpty (n : Nat) (s s₁ s' : SurfPos) :
        GLit ':' s s₁ →
        SSLComments s₁ s' →
        SBlockMapEntry n s s'

  /-- [187] l+block-mapping(n): one or more block mapping entries.  As with
      `SBlockSeqEntries`, the index is the production's already-detected
      `n+m`; `SBlockNode.blockMap` chooses `m` (item 22). -/
  @[yaml_spec "8.2.2" 187 "l+block-mapping(n)"]
  inductive SBlockMapEntries : Nat → SurfPos → SurfPos → Prop where
    | single (n : Nat) (s s₁ s' : SurfPos) :
        SIndent n s s₁ →
        SBlockMapEntry n s₁ s' →
        SBlockMapEntries n s s'
    | cons (n : Nat) (s s₁ s₂ s' : SurfPos) :
        SIndent n s s₁ →
        SBlockMapEntry n s₁ s₂ →
        SBlockMapEntries n s₂ s' →
        SBlockMapEntries n s s'

  /-- [186] ns-l-compact-sequence(n): compact block sequence (no leading indent). -/
  @[yaml_spec "8.2.2" 186 "ns-l-compact-sequence(n)"]
  inductive SCompactSeq : Nat → SurfPos → SurfPos → Prop where
    | mk (n : Nat) (s s₁ s₂ s' : SurfPos) :
        GLit '-' s s₁ →
        GNot SNsChar s₁ →
        SBlockIndented n .blockIn s₁ s₂ →
        SCompactSeqTail n s₂ s' →
        SCompactSeq n s s'

  /-- Tail repetition for compact sequence (inlined GStar). -/
  inductive SCompactSeqTail : Nat → SurfPos → SurfPos → Prop where
    | nil (n : Nat) (s : SurfPos) : SCompactSeqTail n s s
    | cons (n : Nat) (s s₁ s₂ s₃ s' : SurfPos) :
        SIndent n s s₁ →
        GLit '-' s₁ s₂ →
        GNot SNsChar s₂ →
        SBlockIndented n .blockIn s₂ s₃ →
        SCompactSeqTail n s₃ s' →
        SCompactSeqTail n s s'

  /-- [195] ns-l-compact-mapping(n): compact block mapping. -/
  @[yaml_spec "8.2.2" 195 "ns-l-compact-mapping(n)"]
  inductive SCompactMap : Nat → SurfPos → SurfPos → Prop where
    | mk (n : Nat) (s s₁ s' : SurfPos) :
        SBlockMapEntry n s s₁ →
        SCompactMapTail n s₁ s' →
        SCompactMap n s s'

  /-- Tail repetition for compact mapping (inlined GStar). -/
  inductive SCompactMapTail : Nat → SurfPos → SurfPos → Prop where
    | nil (n : Nat) (s : SurfPos) : SCompactMapTail n s s
    | cons (n : Nat) (s s₁ s₂ s' : SurfPos) :
        SIndent n s s₁ →
        SBlockMapEntry n s₁ s₂ →
        SCompactMapTail n s₂ s' →
        SCompactMapTail n s s'

  /-- [193] ns-s-block-map-implicit-key: implicit key on a mapping line.
      Either a JSON-style implicit key or a YAML-style implicit key. -/
  @[yaml_spec "8.2.2" 193 "ns-s-block-map-implicit-key"]
  inductive SImplicitKey : SurfPos → SurfPos → Prop where
    /-- JSON-style implicit key: flow node in BLOCK-KEY context. -/
    | jsonKey (s s₁ s' : SurfPos) :
        SFlowNode 0 .blockKey s s₁ →
        GOpt SSeparateInLine s₁ s' →
        SImplicitKey s s'
    /-- YAML-style implicit key: plain scalar in BLOCK-KEY context. -/
    | yamlKey (s s₁ s' : SurfPos) :
        SNsPlain 0 .blockKey s s₁ →
        GOpt SSeparateInLine s₁ s' →
        SImplicitKey s s'

  /-- [161] ns-flow-node(n,c): flow-context YAML node.
      Alias, direct content, or properties + optional content. -/
  @[yaml_spec "7.5" 161 "ns-flow-node(n,c)"]
  inductive SFlowNode : Nat → YamlContext → SurfPos → SurfPos → Prop where
    /-- [104] Alias node: '*name'. -/
    | alias (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SCNsAliasNode s s' →
        SFlowNode n c s s'
    /-- Direct content (no properties). -/
    | content (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SFlowContent n c s s' →
        SFlowNode n c s s'
    /-- Properties + separator + content. -/
    | propsContent (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SCNsProperties n c s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowContent n c s₂ s' →
        SFlowNode n c s s'
    /-- Properties only (empty content). -/
    | propsEmpty (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SCNsProperties n c s s' →
        SFlowNode n c s s'

  /-- [158] ns-flow-content(n,c): flow YAML or JSON content. -/
  @[yaml_spec "7.5" 158 "ns-flow-content(n,c)"]
  inductive SFlowContent : Nat → YamlContext → SurfPos → SurfPos → Prop where
    /-- [159] Flow YAML: plain scalar. -/
    | plain (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SNsPlain n c s s' →
        SFlowContent n c s s'
    /-- [154] Flow JSON: flow sequence. -/
    | flowSeq (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SFlowSequence n c s s' →
        SFlowContent n c s s'
    /-- [154] Flow JSON: flow mapping. -/
    | flowMap (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SFlowMapping n c s s' →
        SFlowContent n c s s'
    /-- [154] Flow JSON: single-quoted scalar. -/
    | singleQ (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SCSingleQuoted n c s s' →
        SFlowContent n c s s'
    /-- [154] Flow JSON: double-quoted scalar. -/
    | doubleQ (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SCDoubleQuoted n c s s' →
        SFlowContent n c s s'

  /-- [157] c-flow-json-content(n,c): the JSON-like arms of `SFlowContent` (no plain scalar). -/
  @[yaml_spec "7.5" 157 "c-flow-json-content(n,c)"]
  inductive SCFlowJsonContent : Nat → YamlContext → SurfPos → SurfPos → Prop where
    | flowSeq (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SFlowSequence n c s s' →
        SCFlowJsonContent n c s s'
    | flowMap (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SFlowMapping n c s s' →
        SCFlowJsonContent n c s s'
    | singleQ (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SCSingleQuoted n c s s' →
        SCFlowJsonContent n c s s'
    | doubleQ (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SCDoubleQuoted n c s s' →
        SCFlowJsonContent n c s s'

  /-- [160] c-flow-json-node(n,c): `(c-ns-properties s-separate)? c-flow-json-content`. -/
  @[yaml_spec "7.5" 160 "c-flow-json-node(n,c)"]
  inductive SCFlowJsonNode : Nat → YamlContext → SurfPos → SurfPos → Prop where
    | content (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SCFlowJsonContent n c s s' →
        SCFlowJsonNode n c s s'
    | propsContent (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SCNsProperties n c s s₁ →
        SSeparate n c s₁ s₂ →
        SCFlowJsonContent n c s₂ s' →
        SCFlowJsonNode n c s s'

  /-- [137] c-flow-sequence(n,c): '[' + entries + ']'. -/
  @[yaml_spec "7.4.1" 137 "c-flow-sequence(n,c)"]
  inductive SFlowSequence : Nat → YamlContext → SurfPos → SurfPos → Prop where
    | empty (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GLit '[' s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ']' s₂ s' →
        SFlowSequence n c s s'
    | nonempty (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s' : SurfPos) :
        GLit '[' s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        SFlowSeqEntries n (inFlowCtx c) s₂ s₃ →
        GLit ']' s₃ s' →
        SFlowSequence n c s s'

  /-- [138] ns-s-flow-seq-entries(n,c): comma-separated flow sequence entries. -/
  @[yaml_spec "7.4.1" 138 "ns-s-flow-seq-entries(n,c)"]
  inductive SFlowSeqEntries : Nat → YamlContext → SurfPos → SurfPos → Prop where
    | single (n : Nat) (c : YamlContext) (s s₁ s' : SurfPos) :
        SFlowSeqEntry n c s s₁ →
        GOpt (SSeparate n c) s₁ s' →
        SFlowSeqEntries n c s s'
    | consMore (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        SFlowSeqEntry n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ',' s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        SFlowSeqEntries n c s₄ s' →
        SFlowSeqEntries n c s s'
    | consEnd (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s' : SurfPos) :
        SFlowSeqEntry n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ',' s₂ s₃ →
        GOpt (SSeparate n c) s₃ s' →
        SFlowSeqEntries n c s s'

  /-- [139] ns-flow-seq-entry(n,c): flow sequence entry (flow node or pair).

      The `?`-headed and `:`-headed constructors inline `[150] ns-flow-pair`'s
      two alternatives; the last three inline the two arms that only item 9l
      supplied — `[143]`'s `( e-node e-node )` and `[146]`'s empty key. -/
  @[yaml_spec "7.4.1" 139 "ns-flow-seq-entry(n,c)",
    yaml_spec "7.4.2" 143 "ns-flow-map-explicit-entry(n,c)",
    yaml_spec "7.4.2" 146 "c-ns-flow-map-empty-key-entry(n,c)"]
  inductive SFlowSeqEntry : Nat → YamlContext → SurfPos → SurfPos → Prop where
    /-- Regular flow node. -/
    | node (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SFlowNode n c s s' →
        SFlowSeqEntry n c s s'
    /-- Flow pair: key + ':' + separator + value. -/
    | pairValue (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        SFlowNode n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ':' s₂ s₃ →
        SSeparate n c s₃ s₄ →
        SFlowNode n c s₄ s' →
        SFlowSeqEntry n c s s'
    /-- Flow pair: key + ':' + empty value. -/
    | pairEmpty (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SFlowNode n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ':' s₂ s' →
        SFlowSeqEntry n c s s'
    /-- [153] c-ns-flow-pair-json-key-entry then `[149]` (`["a":[1]]`). The key slot reads
        `c-flow-json-node(n,c)` + `s-separate?`, as lenient as `pairValue`'s yaml key; the
        strict `[155] c-s-implicit-json-key(flow-key)` (n = 0, one line) is a follow-up. -/
    | pairJsonAdjacentValue (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        SCFlowJsonNode n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ':' s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        SFlowNode n c s₄ s' →
        SFlowSeqEntry n c s s'
    /-- [150] ns-flow-pair, explicit case, around the JSON-key pair: `[? "a":b]` — the
        explicit key is JSON-like, so `[149]` lets the value be glued to the `':'`. -/
    | explicitPairJsonAdjacentValue (n : Nat) (c : YamlContext)
        (s s₁ s₂ s₃ s₄ s₅ s₆ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        SCFlowJsonNode n c s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        GLit ':' s₄ s₅ →
        GOpt (SSeparate n c) s₅ s₆ →
        SFlowNode n c s₆ s' →
        SFlowSeqEntry n c s s'
    /-- Explicit '?' flow pair with value: `? key : value`. Covers `[? a : b]`
        (ns-flow-pair explicit case [149], reusing `'?' s-separate` + key/value). -/
    | explicitPairValue (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s₅ s₆ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowNode n c s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        GLit ':' s₄ s₅ →
        SSeparate n c s₅ s₆ →
        SFlowNode n c s₆ s' →
        SFlowSeqEntry n c s s'
    /-- Explicit '?' flow pair, empty value: `? key :`. Covers `[? a :]`. -/
    | explicitPairEmpty (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowNode n c s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        GLit ':' s₄ s' →
        SFlowSeqEntry n c s s'
    /-- Explicit '?' key, no value indicator: `? key`. Covers `[? a]`. -/
    | explicitPairKeyOnly (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowNode n c s₂ s' →
        SFlowSeqEntry n c s s'
    /-- Explicit '?' with BOTH nodes empty: `[? ]`, `[? , a]` — `[143]
        ns-flow-map-explicit-entry`'s `( e-node e-node )` alternative, reached
        through `[150] ns-flow-pair`'s explicit arm.  The `s-separate` after the
        `?` is mandatory (item 9j) and both `e-node`s are zero-width, so the
        entry is exactly `'?' s-separate` — the ONE `?` shape whose key is not an
        `ns-flow-node`, which is why the four constructors above cannot spell it.

        Added by item 9l: the shipped pipeline accepts `[? ]` and emits the
        null/null pair, and until now the grammar had no derivation for it. -/
    | explicitPairEmptyNodes (n : Nat) (c : YamlContext) (s s₁ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s' →
        SFlowSeqEntry n c s s'
    /-- Empty key + ':' + separator + value: `[: a]` — `[151]
        ns-flow-pair-entry`'s `c-ns-flow-map-empty-key-entry` alternative
        [146], the sequence twin of `SFlowMapEntry.emptyKeyValue`.

        Added by item 9l.  `SFlowMapEntry` has carried the empty-key pair since
        the start; the sequence side, where it is just as legal, did not. -/
    | emptyKeyValue (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GLit ':' s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowNode n c s₂ s' →
        SFlowSeqEntry n c s s'
    /-- Empty key + ':' + empty value: `[:]` — `[146]` with an `e-node` value
        (item 9l; the sequence twin of `SFlowMapEntry.emptyKeyEmpty`). -/
    | emptyKeyEmpty (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        GLit ':' s s' →
        SFlowSeqEntry n c s s'
    /-- Explicit `?`, EMPTY key, value: `[? : a]` — `[150] ns-flow-pair`'s
        explicit arm reaching `[143]`'s implicit alternative at `[146]
        c-ns-flow-map-empty-key-entry`.

        Item 9l added the two halves separately — `[146]` on its own
        (`emptyKeyValue`, `[: a]`) and `[143]`'s `( e-node e-node )`
        (`explicitPairEmptyNodes`, `[? ]`) — and deliberately left the
        COMPOSITION out, because its only producer is the `:` dispatch and an
        unproducible constructor is inhabitation debt.  Item 9n supplies the
        producer (`SeqFrame.receiveColonQuestion`), so it lands here now. -/
    | explicitEmptyKeyValue (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        GLit ':' s₂ s₃ →
        SSeparate n c s₃ s₄ →
        SFlowNode n c s₄ s' →
        SFlowSeqEntry n c s s'
    /-- Explicit `?`, empty key, empty value: `[? :]` — `[146]` with an `e-node`
        value, under `[150]`'s explicit arm (item 9n). -/
    | explicitEmptyKeyEmpty (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        GLit ':' s₂ s' →
        SFlowSeqEntry n c s s'

  /-- [140] c-flow-mapping(n,c): '{' + entries + '}'. -/
  @[yaml_spec "7.4.2" 140 "c-flow-mapping(n,c)"]
  inductive SFlowMapping : Nat → YamlContext → SurfPos → SurfPos → Prop where
    | empty (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GLit '{' s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit '}' s₂ s' →
        SFlowMapping n c s s'
    | nonempty (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s' : SurfPos) :
        GLit '{' s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        SFlowMapEntries n (inFlowCtx c) s₂ s₃ →
        GLit '}' s₃ s' →
        SFlowMapping n c s s'

  /-- [141] ns-s-flow-map-entries(n,c): comma-separated flow mapping entries. -/
  @[yaml_spec "7.4.2" 141 "ns-s-flow-map-entries(n,c)"]
  inductive SFlowMapEntries : Nat → YamlContext → SurfPos → SurfPos → Prop where
    | single (n : Nat) (c : YamlContext) (s s₁ s' : SurfPos) :
        SFlowMapEntry n c s s₁ →
        GOpt (SSeparate n c) s₁ s' →
        SFlowMapEntries n c s s'
    | consMore (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        SFlowMapEntry n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ',' s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        SFlowMapEntries n c s₄ s' →
        SFlowMapEntries n c s s'
    | consEnd (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s' : SurfPos) :
        SFlowMapEntry n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ',' s₂ s₃ →
        GOpt (SSeparate n c) s₃ s' →
        SFlowMapEntries n c s s'

  /-- [142] ns-flow-map-entry(n,c): explicit '?' entry or implicit entry.

      The explicit constructors inline `[143] ns-flow-map-explicit-entry`,
      whose `( e-node e-node )` alternative arrived with item 9l. -/
  @[yaml_spec "7.4.2" 142 "ns-flow-map-entry(n,c)",
    yaml_spec "7.4.2" 143 "ns-flow-map-explicit-entry(n,c)"]
  inductive SFlowMapEntry : Nat → YamlContext → SurfPos → SurfPos → Prop where
    /-- Explicit '?' + key + ':' + separator + value. -/
    | explicitValue (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s₅ s₆ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowNode n c s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        GLit ':' s₄ s₅ →
        SSeparate n c s₅ s₆ →
        SFlowNode n c s₆ s' →
        SFlowMapEntry n c s s'
    /-- Explicit '?' + key + ':' + empty value. -/
    | explicitEmpty (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowNode n c s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        GLit ':' s₄ s' →
        SFlowMapEntry n c s s'
    /-- Explicit '?' + key with no value indicator: `{? a}` — the `e-node` (empty
        value, no `':'`) branch after `'?' s-separate ns-flow-yaml-node`. -/
    | explicitKeyOnly (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowNode n c s₂ s' →
        SFlowMapEntry n c s s'
    /-- Implicit key + ':' + separator + value. -/
    | implicitValue (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        SFlowNode n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ':' s₂ s₃ →
        SSeparate n c s₃ s₄ →
        SFlowNode n c s₄ s' →
        SFlowMapEntry n c s s'
    /-- Implicit key + ':' + empty value. -/
    | implicitEmpty (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SFlowNode n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ':' s₂ s' →
        SFlowMapEntry n c s s'
    /-- [148] c-ns-flow-map-json-key-entry + [149] c-ns-flow-map-adjacent-value: a JSON-like
        key may be followed by `':'` and the value with NO separation (`{"a":b}`, `{"a":[1]}`).
        The `e-node` value is `implicitEmpty`; the plain-key shape `{a:[1]}` has no arm. -/
    | jsonKeyAdjacentValue (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        SCFlowJsonNode n c s s₁ →
        GOpt (SSeparate n c) s₁ s₂ →
        GLit ':' s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        SFlowNode n c s₄ s' →
        SFlowMapEntry n c s s'
    /-- [142] c-ns-flow-map-explicit-entry around [148]/[149]: `{? "a":b}` — the explicit
        key is a JSON-like node, so the value may be glued to the `':'`. -/
    | explicitJsonKeyAdjacentValue (n : Nat) (c : YamlContext)
        (s s₁ s₂ s₃ s₄ s₅ s₆ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        SCFlowJsonNode n c s₂ s₃ →
        GOpt (SSeparate n c) s₃ s₄ →
        GLit ':' s₄ s₅ →
        GOpt (SSeparate n c) s₅ s₆ →
        SFlowNode n c s₆ s' →
        SFlowMapEntry n c s s'
    /-- Bare YAML key with no value indicator: `{a}` — the `e-node` (empty value,
        no `':'`) branch of `ns-flow-map-yaml-key-entry(n,c)` [145]. Trailing
        separation is absorbed by the enclosing `SFlowMapEntries` GOpt. -/
    | bareKey (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SFlowNode n c s s' →
        SFlowMapEntry n c s s'
    /-- Empty key + ':' + separator + value. -/
    | emptyKeyValue (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GLit ':' s s₁ →
        SSeparate n c s₁ s₂ →
        SFlowNode n c s₂ s' →
        SFlowMapEntry n c s s'
    /-- Empty key + ':' + empty value. -/
    | emptyKeyEmpty (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        GLit ':' s s' →
        SFlowMapEntry n c s s'
    /-- Explicit '?' with BOTH nodes empty: `{? }`, `{? , a}` — `[143]
        ns-flow-map-explicit-entry`'s `( e-node e-node )` alternative (item 9l;
        see `SFlowSeqEntry.explicitPairEmptyNodes`). -/
    | explicitEmptyNodes (n : Nat) (c : YamlContext) (s s₁ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s' →
        SFlowMapEntry n c s s'
    /-- Explicit `?`, EMPTY key, value: `{? : a}` — see
        `SFlowSeqEntry.explicitEmptyKeyValue` (item 9n). -/
    | explicitEmptyKeyValue (n : Nat) (c : YamlContext) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        GLit ':' s₂ s₃ →
        SSeparate n c s₃ s₄ →
        SFlowNode n c s₄ s' →
        SFlowMapEntry n c s s'
    /-- Explicit `?`, empty key, empty value: `{? :}` (item 9n). -/
    | explicitEmptyKeyEmpty (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GLit '?' s s₁ →
        SSeparate n c s₁ s₂ →
        GLit ':' s₂ s' →
        SFlowMapEntry n c s s'

end -- mutual

end L4YAML.Surface

end Blanket
