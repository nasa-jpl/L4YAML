/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Surface.Scalars

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

namespace Lean4Yaml.Surface

open Lean4Yaml (YamlContext)

/-! ## Mutual Block: Nodes + Collections

All 11 mutually recursive types defined together.
The types reference scalar productions (from Surface.Scalars) and basic
productions (from Surface.Basic) which are defined non-recursively. -/

mutual

  /-- [196] s-l+block-node(n,c): block-context YAML node.
      Can be a block scalar, block collection, flow node, or empty node. -/
  inductive SBlockNode : Nat → YamlContext → SurfPos → SurfPos → Prop where
    /-- [198] Block scalar: separator + optional properties + literal or folded. -/
    | blockLiteral (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SSeparate (n + 1) c s s₁ →
        GOpt (GSeq (SCNsProperties (n + 1) c) (SSeparate (n + 1) c)) s₁ s₂ →
        SCLLiteral n s₂ s' →
        SBlockNode n c s s'
    | blockFolded (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SSeparate (n + 1) c s s₁ →
        GOpt (GSeq (SCNsProperties (n + 1) c) (SSeparate (n + 1) c)) s₁ s₂ →
        SCLFolded n s₂ s' →
        SBlockNode n c s s'
    /-- [199] Block sequence: optional properties + comments + sequence. -/
    | blockSeq (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GOpt (GSeq (SSeparate (n + 1) c) (SCNsProperties (n + 1) c)) s s₁ →
        SSLComments s₁ s₂ →
        SBlockSeqEntries (seqSpaces n c) s₂ s' →
        SBlockNode n c s s'
    /-- [199] Block mapping: optional properties + comments + mapping. -/
    | blockMap (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        GOpt (GSeq (SSeparate (n + 1) c) (SCNsProperties (n + 1) c)) s s₁ →
        SSLComments s₁ s₂ →
        SBlockMapEntries n s₂ s' →
        SBlockNode n c s s'
    /-- [195] Flow-in-block: separator + flow node + comments. -/
    | flowInBlock (n : Nat) (c : YamlContext) (s s₁ s₂ s' : SurfPos) :
        SSeparate (n + 1) .flowOut s s₁ →
        SFlowNode (n + 1) .flowOut s₁ s₂ →
        SSLComments s₂ s' →
        SBlockNode n c s s'
    /-- [72] Empty node + trailing comments. -/
    | emptyNode (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SSLComments s s' →
        SBlockNode n c s s'

  /-- [182] s-l+block-indented(n,c): content inside a block entry.
      Can be compact notation, a regular block node, or empty. -/
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
    /-- Regular block node. -/
    | node (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SBlockNode n c s s' →
        SBlockIndented n c s s'
    /-- Empty node + comments. -/
    | empty (n : Nat) (c : YamlContext) (s s' : SurfPos) :
        SSLComments s s' →
        SBlockIndented n c s s'

  /-- [180] l+block-sequence(n): one or more block sequence entries.
      Each entry = s-indent(n+1) + '-' + s-l+block-indented(n+1,BLOCK-IN).
      The '-' indicator must NOT be followed by ns-char (distinguishes
      block entry from plain scalar starting with '-'). -/
  inductive SBlockSeqEntries : Nat → SurfPos → SurfPos → Prop where
    | single (n : Nat) (s s₁ s₂ s₃ s' : SurfPos) :
        SIndent (n + 1) s s₁ →
        GLit '-' s₁ s₂ →
        GNot SNsChar s₂ →
        SBlockIndented (n + 1) .blockIn s₂ s' →
        SBlockSeqEntries n s s'
    | cons (n : Nat) (s s₁ s₂ s₃ s' : SurfPos) :
        SIndent (n + 1) s s₁ →
        GLit '-' s₁ s₂ →
        GNot SNsChar s₂ →
        SBlockIndented (n + 1) .blockIn s₂ s₃ →
        SBlockSeqEntries n s₃ s' →
        SBlockSeqEntries n s s'

  /-- [185] ns-l-block-map-entry(n): explicit or implicit mapping entry. -/
  inductive SBlockMapEntry : Nat → SurfPos → SurfPos → Prop where
    /-- [186] Explicit entry: '?' key + ':' value. -/
    | explicit (n : Nat) (s s₁ s₂ s₃ s₄ s' : SurfPos) :
        GLit '?' s s₁ →
        SBlockIndented n .blockOut s₁ s₂ →
        SIndent n s₂ s₃ →
        GLit ':' s₃ s₄ →
        SBlockIndented n .blockOut s₄ s' →
        SBlockMapEntry n s s'
    /-- [189] Implicit key + ':' + block node. -/
    | implicitKeyNode (n : Nat) (s s₁ s₂ s' : SurfPos) :
        SImplicitKey s s₁ →
        GLit ':' s₁ s₂ →
        SBlockNode n .blockOut s₂ s' →
        SBlockMapEntry n s s'
    /-- [189] Implicit key + ':' + empty value (comments). -/
    | implicitKeyEmpty (n : Nat) (s s₁ s₂ s' : SurfPos) :
        SImplicitKey s s₁ →
        GLit ':' s₁ s₂ →
        SSLComments s₂ s' →
        SBlockMapEntry n s s'
    /-- [189] Empty key + ':' + block node. -/
    | emptyKeyNode (n : Nat) (s s₁ s' : SurfPos) :
        GLit ':' s s₁ →
        SBlockNode n .blockOut s₁ s' →
        SBlockMapEntry n s s'
    /-- [189] Empty key + ':' + comments. -/
    | emptyKeyEmpty (n : Nat) (s s₁ s' : SurfPos) :
        GLit ':' s s₁ →
        SSLComments s₁ s' →
        SBlockMapEntry n s s'

  /-- [184] l+block-mapping(n): one or more block mapping entries. -/
  inductive SBlockMapEntries : Nat → SurfPos → SurfPos → Prop where
    | single (n : Nat) (s s₁ s' : SurfPos) :
        SIndent (n + 1) s s₁ →
        SBlockMapEntry (n + 1) s₁ s' →
        SBlockMapEntries n s s'
    | cons (n : Nat) (s s₁ s₂ s' : SurfPos) :
        SIndent (n + 1) s s₁ →
        SBlockMapEntry (n + 1) s₁ s₂ →
        SBlockMapEntries n s₂ s' →
        SBlockMapEntries n s s'

  /-- [183] ns-l-compact-sequence(n): compact block sequence (no leading indent). -/
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

  /-- [193] ns-l-compact-mapping(n): compact block mapping. -/
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

  /-- [190] ns-s-block-map-implicit-key: implicit key on a mapping line.
      Either a JSON-style implicit key or a YAML-style implicit key. -/
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

  /-- [160] ns-flow-content(n,c): flow YAML or JSON content. -/
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

  /-- [134] c-flow-sequence(n,c): '[' + entries + ']'. -/
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

  /-- [135] ns-s-flow-seq-entries(n,c): comma-separated flow sequence entries. -/
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

  /-- [136] ns-flow-seq-entry(n,c): flow sequence entry (flow node or pair). -/
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

  /-- [137] c-flow-mapping(n,c): '{' + entries + '}'. -/
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

  /-- [138] ns-s-flow-map-entries(n,c): comma-separated flow mapping entries. -/
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

  /-- [139] ns-flow-map-entry(n,c): explicit '?' entry or implicit entry. -/
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

end -- mutual

end Lean4Yaml.Surface
