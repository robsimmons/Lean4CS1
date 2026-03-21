import VersoManual

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
namespace Week13

#doc (Manual) "Week 13: Streams and Lazy Types" =>

# Infinite data and lazy evaluation
%%%
number := false
%%%

Every data type we have defined so far is _finite_: you can always
reach a leaf.  But some computations naturally produce infinite
sequences: the natural numbers, the Fibonacci sequence, an infinite
stream of sensor readings.

Lean's reduction strategy is _strict_ (call-by-value): arguments are
evaluated before being passed.  To build infinite structures, we must
_delay_ evaluation explicitly using `Thunk`.

A `Thunk α` is a suspended computation of type `α`.  It is not
evaluated until forced.  By building infinite structures out of
`Thunk`s, we can represent them finitely in memory and compute as many
elements as needed.

# Thunk: explicit laziness

```lean
-- Thunk is defined in Lean's core library:
-- structure Thunk (α : Type u) where mk ::
--   fn : Unit → α
-- A Thunk wraps a function from Unit → α.
-- Calling .get on a Thunk forces evaluation.

#check @Thunk      -- Type u → Type u
#check @Thunk.get  -- Thunk α → α
#check @Thunk.mk   -- (Unit → α) → Thunk α

-- Creating and forcing a Thunk:
def lazyFive : Thunk Nat := Thunk.mk (fun _ => 2 + 3)
#eval lazyFive.get   -- 5  (computed only when forced)
```

# Lazy lists (streams)

A lazy list is either empty or a head value paired with a _thunked_
tail.  The tail is not computed until needed.

```lean
inductive LList (α : Type) where
  | nil  : LList α
  | cons : α → Thunk (LList α) → LList α

-- Take the first n elements as a strict list:
def LList.take : Nat → LList α → List α
  | 0,     _            => []
  | _,     .nil         => []
  | n + 1, .cons h t    => h :: LList.take n t.get

-- Drop the first n elements:
def LList.drop : Nat → LList α → LList α
  | 0,     s            => s
  | _,     .nil         => .nil
  | n + 1, .cons _ t    => LList.drop n t.get
```

# Canonical infinite streams

```lean
-- LList is always nonempty (it has a constructor)
instance : Nonempty (LList α) := ⟨.nil⟩

-- The infinite stream of a constant value:
partial def LList.repeat (x : α) : LList α :=
  .cons x (Thunk.mk (fun _ => LList.repeat x))

-- The natural numbers: 0, 1, 2, 3, ...
private partial def natsFrom (n : Nat) : LList Nat :=
  .cons n (Thunk.mk (fun _ => natsFrom (n + 1)))

def nats : LList Nat := natsFrom 0

-- Fibonacci numbers: 1, 1, 2, 3, 5, 8, ...
private partial def fibsFrom (a b : Nat) : LList Nat :=
  .cons a (Thunk.mk (fun _ => fibsFrom b (a + b)))

def fibs : LList Nat := fibsFrom 0 1

-- Test:
#eval LList.take 10 nats    -- [0,1,2,3,4,5,6,7,8,9]
#eval LList.take 10 fibs    -- [0,1,1,2,3,5,8,13,21,34]
```

# Map on streams

```lean
def LList.map (f : α → β) : LList α → LList β
  | .nil       => .nil
  | .cons h t  => .cons (f h) (Thunk.mk (fun _ => LList.map f t.get))

-- Specification: map f on the first n elements equals
-- mapping f on the taken list.
-- This is a provided term-mode proof.
theorem map_take (f : α → β) (n : Nat) :
    ∀ xs : LList α, (xs.map f).take n = (xs.take n).map f := by
  induction n with
  | zero => intro xs; rfl
  | succ n ih =>
    intro xs
    cases xs with
    | nil  => simp [LList.take, LList.map]
    | cons h t =>
        simp only [LList.map, LList.take]
        exact congrArg (f h :: ·) (ih t.get)
```

# Filter on streams

Filter on an infinite stream is partial: if the predicate is always
false, filter never terminates.  We cannot define a total filter on
streams in Lean without restricting the predicate or using `partial`.

This is a fundamental difference from lists.  On a finite list,
filter always terminates.  On an infinite stream, it may not.

This connects back to Week 3: Lean's type system only accepts total
functions.  A stream filter would require `partial`, losing the
ability to prove properties about it.

We CAN define filter on a `take`n prefix:

```lean
def LList.takeWhile (p : α → Bool) : LList α → List α
  | .nil       => []
  | .cons h t  => if p h then h :: LList.takeWhile p t.get else []

#eval LList.takeWhile (· < 5) nats    -- [0,1,2,3,4]
```

# Coinduction: specifications about infinite streams

For finite data, we use induction to prove properties: "for all finite
inputs, the property holds."

For infinite data (streams), we use _coinduction_: "the property holds
at every finite prefix."

The specification of `nats` is a good example:

```lean
-- Specification: the nth element of nats is n.
-- Note: with partial definitions, we state the property but defer the proof.
theorem nats_take_eq : ∀ n : Nat, LList.take n nats = List.range n := by
  intro n
  induction n with
  | zero => rfl
  | succ n _ =>
    simp only [LList.take, nats, natsFrom, List.range_succ]
    sorry
```

# Non-termination and the Thunk boundary

The `Thunk` type makes explicit what is delayed.  Every time you see
`Thunk α` in a type, you know: "this computation has not run yet."

The boundary between finite and infinite structures is the boundary
between:
- Lean's total function world (Week 3: structural recursion, well-founded recursion)
- The `partial` world (where termination is not guaranteed)

Thunks do not cross this boundary.  A `Thunk` value IS a term — it is
just a function waiting to be called.  The infinite structure exists
as a _description_ of how to produce any finite prefix; it does not
actually exist as an infinite object in memory.

This is computationally honest: real programs do not hold infinite
structures; they hold descriptions and lazily demand pieces.

# Exercises
%%%
number := false
%%%

1. Define `LList.zip : LList α → LList β → LList (α × β)` that pairs
   corresponding elements.  State its specification:
   `(zip xs ys).take n = (xs.take n).zip (ys.take n)`.

2. Define `LList.interleave : LList α → LList α → LList α` that
   alternates between two streams.  State its specification.

3. Define the stream of squares: 0, 1, 4, 9, 16, ...  using `LList.map`
   on `nats`.  Check with `#eval` that the first 10 elements are correct.

4. Explain why we cannot define:
   ```lean -keep
   def LList.filter (p : α → Bool) : LList α → LList α := sorry
   ```
   as a total function in Lean.  What would happen to the termination
   checker?

5. State the specification for `LList.map` in terms of take:
   "`map f xs` is the stream where the nth element is `f` applied to
   the nth element of `xs`."  This is exactly `map_take`; read it and
   explain each part.
