import Parser

/-! Complete proof strategy test for all combinator specs.
    Key insights:
    1. `match` in definitions vs specs produce different auxiliary functions → rfl fails
    2. `dsimp only [...]` unfolds definitions (equation lemmas) without over-unfolding
    3. `cases <discriminant> <;> rfl` eliminates the match and closes each branch -/

open Parser

-- ═══════════════════════════════════════════════════════════════════
-- §1 Monad Primitives
-- ═══════════════════════════════════════════════════════════════════

-- pure: rfl
example {ε σ : Type} {τ : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (x : α) (s : σ) :
    (pure x : Parser ε σ τ α) s = .ok s x := rfl

-- bind: simp only + cases
example {ε σ : Type} {τ : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (p : Parser ε σ τ α) (f : α → Parser ε σ τ β) (s : σ) :
    (p >>= f) s =
      match p s with
      | .ok s' a => f a s'
      | .error s' e => .error s' e := by
  simp only [bind, Bind.bind, pure, Pure.pure]; cases p s <;> rfl

-- map: simp only + cases
example {ε σ : Type} {τ : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (f : α → β) (p : Parser ε σ τ α) (s : σ) :
    (f <$> p) s =
      match p s with
      | .ok s' a => .ok s' (f a)
      | .error s' e => .error s' e := by
  simp only [Functor.map, bind, Bind.bind, pure, Pure.pure]; cases p s <;> rfl

-- ═══════════════════════════════════════════════════════════════════
-- §2 Stream / Position
-- ═══════════════════════════════════════════════════════════════════

example {ε σ : Type} {τ : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (s : σ) :
    (getStream : Parser ε σ τ σ) s = .ok s s := rfl

example {ε σ : Type} {τ : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (s s' : σ) :
    (setStream s' : Parser ε σ τ PUnit) s = .ok s' .unit := rfl

example {ε σ : Type} {τ : Type}
    [inst : Parser.Stream σ τ] [Parser.Error ε σ τ]
    (s : σ) :
    (Parser.getPosition : Parser ε σ τ inst.Position) s =
      .ok s (inst.getPosition s) := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §3 Error
-- ═══════════════════════════════════════════════════════════════════

example {ε σ : Type} {τ : Type}
    [Parser.Stream σ τ] [inst : Parser.Error ε σ τ]
    (s : σ) :
    (throwUnexpected (α := α) : Parser ε σ τ α) s =
      .error s (inst.unexpected (Parser.Stream.getPosition s) none) := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §4 Backtracking / Control Flow
-- ═══════════════════════════════════════════════════════════════════

-- tryCatch: dsimp only unfolds the MonadExcept chain
example {ε σ : Type} {τ : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (p : Parser ε σ τ α) (handler : ε → Parser ε σ τ α) (s : σ) :
    (tryCatch p handler) s =
      match p s with
      | .ok s' a => .ok s' a
      | .error s' e => handler e s' := by
  dsimp only [tryCatch, tryCatchThe, MonadExcept.tryCatch, MonadExceptOf.tryCatch,
              bind, Bind.bind, pure, Pure.pure, ParserT.run]
  cases p s <;> rfl

-- withBacktracking
example {ε σ : Type} {τ : Type}
    [inst : Parser.Stream σ τ] [Parser.Error ε σ τ]
    (p : Parser ε σ τ α) (s : σ) :
    (withBacktracking p) s =
      match p s with
      | .ok s' a => .ok s' a
      | .error s' e => .error (inst.setPosition s' (inst.getPosition s)) e := by
  dsimp only [withBacktracking, tryCatch, tryCatchThe, MonadExcept.tryCatch,
              MonadExceptOf.tryCatch, MonadExcept.throw,
              bind, Bind.bind, pure, Pure.pure, getPosition, setPosition,
              throw, MonadExceptOf.throw, throwThe, ParserT.run,
              getStream, setStream, Functor.map]
  cases p s <;> rfl

-- orElse: simp unfolds to the direct OrElse instance
-- Note: setPosition uses the error stream s', not the original s
example {ε σ : Type} {τ : Type}
    [inst : Parser.Stream σ τ] [Parser.Error ε σ τ]
    (p q : Parser ε σ τ α) (s : σ) :
    (p <|> q) s =
      match p s with
      | .ok s' a => .ok s' a
      | .error s' _ => q (inst.setPosition s' (inst.getPosition s)) := by
  simp only [HOrElse.hOrElse, OrElse.orElse,
             bind, Bind.bind, pure, Pure.pure]
  cases p s <;> rfl

-- ═══════════════════════════════════════════════════════════════════
-- §5 Option
-- ═══════════════════════════════════════════════════════════════════

-- option? (through the eoption → optionM → optionD → option! → option? chain)
-- Note: p receives s directly; on error, setPosition uses the error stream s'
example {ε σ : Type} {τ : Type}
    [inst : Parser.Stream σ τ] [Parser.Error ε σ τ]
    (p : Parser ε σ τ α) (s : σ) :
    (option? p) s =
      match p s with
      | .ok s' a => .ok s' (some a)
      | .error s' _ => .ok (inst.setPosition s' (inst.getPosition s)) none := by
  simp only [option?, option!, optionD, optionM, eoption, Functor.map,
             bind, Bind.bind, pure, Pure.pure,
             liftM, monadLift, MonadLift.monadLift]
  cases p s <;> rfl

-- ═══════════════════════════════════════════════════════════════════
-- §6 Tokens
-- ═══════════════════════════════════════════════════════════════════

-- lookAhead: restores position in BOTH success and error
-- setPosition uses the post-p stream s'
example {ε σ : Type} {τ : Type}
    [inst : Parser.Stream σ τ] [Parser.Error ε σ τ]
    (p : Parser ε σ τ α) (s : σ) :
    (lookAhead p) s =
      match p s with
      | .ok s' a => .ok (inst.setPosition s' (inst.getPosition s)) a
      | .error s' e => .error (inst.setPosition s' (inst.getPosition s)) e := by
  dsimp only [lookAhead, tryCatch, tryCatchThe, MonadExcept.tryCatch,
              MonadExceptOf.tryCatch, MonadExcept.throw,
              bind, Bind.bind, pure, Pure.pure, getPosition, setPosition,
              throw, MonadExceptOf.throw, throwThe, ParserT.run,
              getStream, setStream, Functor.map]
  cases p s <;> rfl

-- notFollowedBy: succeeds when p fails, fails when p succeeds
-- both branches use the restored-position stream
example {ε σ : Type} {τ : Type}
    [inst : Parser.Stream σ τ] [eInst : Parser.Error ε σ τ]
    (p : Parser ε σ τ α) (s : σ) :
    (notFollowedBy p) s =
      match p s with
      | .ok s' _ =>
          let restored := inst.setPosition s' (inst.getPosition s)
          .error restored (eInst.unexpected (inst.getPosition restored) none)
      | .error s' _ => .ok (inst.setPosition s' (inst.getPosition s)) .unit := by
  simp only [notFollowedBy, lookAhead, tryCatch, tryCatchThe, MonadExcept.tryCatch,
             MonadExceptOf.tryCatch, MonadExcept.throw,
             bind, Bind.bind, pure, Pure.pure, getPosition, setPosition,
             throw, MonadExceptOf.throw, throwThe, throwUnexpected, ParserT.run,
             getStream, setStream, Functor.map]
  cases p s <;> rfl
