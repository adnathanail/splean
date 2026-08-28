import SpLean.Algebraic.AlgPhase

namespace SpLean.Algebraic

/-- Which of the two spider families a node belongs to.

    Deliberately *not* the `SpiderColor` in `SpLean/Axiomatic/Data.lean`, even
    though the two are the same two constructors. Sharing it was the last
    thread tying this module to the graph-style representation, and it bought
    nothing: the rewrite rules pattern-match theirs, this one only ever
    becomes a `"Z"`/`"X"` on the way to the widget. Two three-line types are
    cheaper than a dependency between the halves of the project. -/
inductive SpiderColor where
  | Z  -- green
  | X  -- red
  deriving Repr, BEq, DecidableEq

/-- A free-algebra ZX term, indexed by its arity (`n` inputs, `m` outputs). -/
inductive ZX : Nat → Nat → Type
  | empty    : ZX 0 0
  | wire     : ZX 1 1
  | hadamard : ZX 1 1
  | spider   (c : SpiderColor) (n m : Nat) (φ : AlgPhase := 0) : ZX n m
  | stack    {n m p q : Nat} : ZX n m → ZX p q → ZX (n + p) (m + q)
  | compose  {n m k : Nat} : ZX n m → ZX m k → ZX n k

/-- Sequential composition: `a ≫ b` feeds the outputs of `a` into the inputs of `b`. -/
scoped infixl:55 " ≫ " => ZX.compose -- type as \gg

/-- Parallel composition (stacking): `a ⊗ b` puts `a` and `b` side by side. -/
scoped infixl:60 " ⊗ " => ZX.stack

end SpLean.Algebraic
