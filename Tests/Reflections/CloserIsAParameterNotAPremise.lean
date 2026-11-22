/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 669 — the closer is a parameter, not a premise

**The rule.**  A lemma that demands "the pending is CLOSED here" as a premise,
when what its body spends is only "a finished construct re-enters the stream
somehow", has baked one caller's closer into its statement.  Restate the
premise as the CONTINUATION the body actually applies and the lemma serves
the caller that cannot close — at the cost of one `fun` at every caller that
can.  This is item 33's "prefer continuation over accumulator" (Reflection
659's file) applied one level up: not to a grammar closure's interface but to
a whole dispatch lemma's, where the accumulated thing was a closed stream and
the continuation is a route.

**How the instance hid the parameter.**  `content_dispatch_after_close` took
`SLYamlStream sp_start sp_mid` — the stream CLOSED at the landing — and spent
it exactly once per branch, wrapping the finished node as a fresh bare
document (`implicitContinue ∘ SLAnyDocument.bare ∘ SLBareDocument.mk`).  Each
spend is one application of `fun sp_m h_bn => …`, a function OF the closed
stream — so the lemma was the bare-document INSTANCE of a routed general form,
and the generalization deletes nothing and moves nothing: it extracts the one
lambda, `content_dispatch_after_close = content_dispatch_routed` at
`sp_anchor = sp_res` with that lambda passed in (item 39's aphorism again:
writing the special case is writing the general one with the parameter thrown
away).  The caller it admits is the mid-line park, where no `s-l-comments`
can exist and "close first" is not expensive but IMPOSSIBLE.

**The tell, greppable.**  The pending that could not close first had carried
its own closer since the day it was written: `pendingDocStart.h_doc_builder`
takes `GAlt SLBareDocument (GSeq SENode SSLComments)`, and every consumer in
the library applied `GAlt.right` (the empty-node close) — the `SLBareDocument`
branch had ZERO consumers.  A two-branch field one of whose branches is never
applied is a route someone priced and never wired; finding it is a grep, not
a proof.  ([[UnusedAlternativeIsUnchecked]] is the same tell on a grammar
alternative — there the unconsumed thing had never been CHECKED; here it had
been checked and never SPENT.)

§1 the toy: a dispatch over a park, stated close-first.  §2 the general form,
and the instance recovered by passing the lambda.  §3 the caller the premise
excluded: a park where closing is impossible, served by the route it carried
all along.
-/

namespace L4YAML.Tests.Reflections.CloserIsAParameterNotAPremise

/-! ## §1  The toy

A stream is a list of closed documents; a park holds a half-read node.  The
close-first dispatch demands the stream already extended to the landing. -/

/-- A finished node (toy). -/
inductive Node where
  | scalar (s : String)
deriving DecidableEq, Repr

/-- A closed document: bare, or explicit with a `---` marker (toy `[208]`). -/
inductive Doc where
  | bare (n : Node)
  | explicit (n : Node)
deriving DecidableEq, Repr

/-- The stream: closed documents, in order. -/
abbrev Stream := List Doc

/-- What the dispatch produces from a park: the node it finished reading. -/
structure Dispatched where
  node : Node
deriving Repr

/-- **Close-first** (the old statement): the caller must supply the stream
    CLOSED at the landing; the body wraps the node as a fresh bare document.
    The `.bare` wrap is the baked-in closer. -/
def dispatchAfterClose (closed : Stream) (d : Dispatched) : Stream :=
  closed ++ [Doc.bare d.node]

/-! ## §2  The general form: the closer is a parameter -/

/-- **Routed**: the caller says how a finished node re-enters the stream. -/
def dispatchRouted (route : Node → Stream) (d : Dispatched) : Stream :=
  route d.node

/-- The old lemma is the new one at the bare route — the parameter was thrown
    away, not absent.  Definitional, which is the measure of "the
    generalization moves nothing". -/
theorem afterClose_is_routed_at_bare (closed : Stream) (d : Dispatched) :
    dispatchAfterClose closed d =
    dispatchRouted (fun n => closed ++ [Doc.bare n]) d := rfl

/-! ## §3  The caller the premise excluded

A `---` park is MID-LINE: there is no landing to close at, so no `closed`
argument exists for `dispatchAfterClose` — but the pending has carried its
own closer since it was written: build the EXPLICIT document.  The routed
form serves it with the field it already had. -/

/-- The doc-start pending's own closer (toy `h_doc_builder`): the stream
    before the `---`, waiting for the document's body. -/
def docStartCloser (before : Stream) : Node → Stream :=
  fun n => before ++ [Doc.explicit n]

/-- `--- a` composes: the routed dispatch spends the pending's closer, and
    the node lands INSIDE the explicit document — not beside it as a second,
    phantom bare one. -/
example :
    dispatchRouted (docStartCloser [Doc.bare (.scalar "prev")])
      ⟨.scalar "a"⟩ =
    [Doc.bare (.scalar "prev"), Doc.explicit (.scalar "a")] := rfl

/-- The close-first form CANNOT express that: whatever `closed` is handed to
    it, the document the dispatched node lands in comes out `.bare` — the
    baked-in closer is a STATEMENT about the result, and for the explicit
    document it is the wrong one. -/
theorem afterClose_ends_bare (closed : Stream) (d : Dispatched) :
    (dispatchAfterClose closed d).getLast? = some (Doc.bare d.node) := by
  simp [dispatchAfterClose]

theorem afterClose_never_ends_explicit (closed : Stream) (d : Dispatched)
    (n : Node) :
    (dispatchAfterClose closed d).getLast? ≠ some (Doc.explicit n) := by
  simp [dispatchAfterClose]

end L4YAML.Tests.Reflections.CloserIsAParameterNotAPremise

end Blanket
