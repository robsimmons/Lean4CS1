import VersoManual
import Batteries.Logic

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
namespace Week12

#doc (Manual) "Week 12: Type Classes and the Decidable Type" =>

# What a type class really is
%%%
number := false
%%%

A type class is an interface with implementations provided by instances.
We have seen type classes as abstract types (Week 11).  This week we
examine type classes as _algebraic structures_ — sets with operations
satisfying laws.

More importantly, we examine `Decidable` itself as an inductive type.
Understanding `Decidable` as a data type — not magic — completes the
picture of how `decide` works as a term-mode proof producer.

# Decidable: an inductive type carrying proofs

`Decidable` is defined in Lean's core library as:

```lean -keep
inductive Decidable (p : Prop) where
  | isFalse : ¬p → Decidable p
  | isTrue  :  p → Decidable p
```

This is an ordinary inductive type.  A value of type `Decidable p` is
either:
- `isFalse h` where `h : ¬p` — a proof that p is false, OR
- `isTrue h`  where `h : p`  — a proof that p is true.

`Decidable p` does not just say "p is true or false" — it _provides_
the proof of whichever is the case.

*Evaluation.*  `decide` is not magic — it evaluates.  When you write
`by decide` to prove `p`, Lean:
1. Looks up the `Decidable p` instance (a value of type `Decidable p`).
2. _Evaluates_ that instance to its normal form.
3. If the normal form is `isTrue h`, the proof `h : p` is extracted and
   used.  The goal is closed.
4. If the normal form is `isFalse h`, elaboration fails — the goal is
   `p` but only a refutation exists.

The whole operation is reduction: evaluate the `Decidable` term, inspect
the constructor, extract the payload.  Every `by decide` in this course
is exactly these four steps.

`decide` used as a proof term extracts the `isTrue h` component and
returns `h : p`.  If the instance is `isFalse _`, the file fails to
compile.

```lean
-- We can inspect Decidable values directly:
#check @Decidable.isTrue   -- ∀ {p : Prop}, p → Decidable p
#check @Decidable.isFalse  -- ∀ {p : Prop}, ¬p → Decidable p

-- A Decidable value IS the proof:
example : Decidable (1 < 2) := Decidable.isTrue (by decide)
example : Decidable (2 < 1) := Decidable.isFalse (by decide)

-- The decEq function for Nat:
#check @Nat.decEq   -- (a b : Nat) → Decidable (a = b)

-- For any decidable proposition, we can extract the proof or refutation:
def toProofOrRefutation (p : Prop) [d : Decidable p] : p ∨ ¬p :=
  match d with
  | Decidable.isTrue h  => Or.inl h
  | Decidable.isFalse h => Or.inr h
```

# DecidableEq as a type class instance

`DecidableEq α` is a type class (an alias for `(a b : α) → Decidable (a = b)`).
An instance provides, for every pair of elements, a decision procedure.

```lean
-- Inspecting a DecidableEq instance:
#check (@Nat.decEq : DecidableEq Nat)

-- Using a DecidableEq instance explicitly:
def eqTest [DecidableEq α] (a b : α) : String :=
  match decEq a b with
  | Decidable.isTrue _  => "equal"
  | Decidable.isFalse _ => "not equal"

#eval eqTest (3 : Nat) 3    -- "equal"
#eval eqTest (3 : Nat) 4    -- "not equal"
```

# Functor as a type class

A `Functor` is a type constructor `F : Type → Type` equipped with a
`map` operation satisfying the two functor laws.

```lean
-- Our own Functor class with laws:
class MyFunctor (F : Type → Type) where
  fmap : (α → β) → F α → F β
  map_id  : ∀ (x : F α), fmap id x = x
  map_comp : ∀ (f : β → γ) (g : α → β) (x : F α),
      fmap (f ∘ g) x = fmap f (fmap g x)

-- List instance: the laws are theorems we proved in Week 8.
instance : MyFunctor List where
  fmap     := List.map
  map_id   := List.map_id
  map_comp := fun f g xs => by simp [← List.map_map]

-- Option instance:
instance : MyFunctor Option where
  fmap     := Option.map
  map_id   := fun o => congr_fun Option.map_id o
  map_comp := fun f g o => (Option.map_map f g o).symm
```

# Foldable as a type class

```lean
class MyFoldable (F : Type → Type) where
  fold : (α → β → β) → β → F α → β

instance : MyFoldable List where
  fold := List.foldr

instance : MyFoldable Option where
  fold := fun f z o => o.elim z (fun x => f x z)

-- Specification: fold on List with cons/nil reconstructs the list
theorem list_fold_spec (xs : List α) :
    MyFoldable.fold (· :: ·) [] xs = xs :=
  List.foldr_cons_nil

-- Specification: fold on Option
theorem option_fold_none (f : α → β → β) (z : β) :
    MyFoldable.fold f z (none : Option α) = z :=
  rfl

theorem option_fold_some (f : α → β → β) (z : β) (x : α) :
    MyFoldable.fold f z (some x) = f x z :=
  rfl
```

# Monoid: an algebraic structure with laws

```lean
class MyMonoid (α : Type) where
  one  : α
  mul  : α → α → α
  mul_one   : ∀ a : α, mul a one = a
  one_mul   : ∀ a : α, mul one a = a
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)

-- Nat under addition:
instance : MyMonoid Nat where
  one       := 0
  mul       := (· + ·)
  mul_one   := Nat.add_zero
  one_mul   := Nat.zero_add
  mul_assoc := Nat.add_assoc

-- List under append:
instance : MyMonoid (List α) where
  one       := []
  mul       := (· ++ ·)
  mul_one   := List.append_nil
  one_mul   := List.nil_append
  mul_assoc := List.append_assoc
```


# The boundary, revisited

After twelve weeks, we can state the decidability boundary precisely.

`Decidable p` holds (has an instance) when there is a terminating
algorithm that produces either `isTrue h : p` or `isFalse h : ¬p`.

The boundary is not arbitrary:
- *Nat equality*: decidable. Algorithm: compare digit by digit.
- *List equality* (when element equality is decidable): decidable.
  Algorithm: compare element by element.
- *Float equality*: NOT decidable soundly, because NaN ≠ NaN would
  require an algorithm that produces `isFalse h : ¬(NaN = NaN)`, but
  `rfl : NaN = NaN` would refute it.  The instance cannot exist.
- *Function equality*: NOT decidable in general.  To check `f = g`
  you would need to check all inputs — infinitely many.
- *∀ n : Nat, P n*: NOT decidable in general.  There is no algorithm
  that terminates and checks all natural numbers.
  (This is related to the halting problem.)

Understanding what is and is not decidable — and WHY — is one of the
foundational concepts of computer science.

# Exercises
%%%
number := false
%%%

1. Implement `MyFunctor` for the binary tree type from Week 6.
   State and prove the two functor laws for your implementation.

2. Show that `Bool` forms a `MyMonoid` under `&&` with identity `true`.
   State and prove all three laws.

3. Write a function
   ```lean -keep
   def mapDecide [DecidableEq α] (xs ys : List α) :
       List (α ⊕ α) := sorry
   ```
   that pairs each element of `xs` with itself if it appears in `ys`
   (`Sum.inl`) and marks it missing otherwise (`Sum.inr`).

4. State the specification for `MyFoldable.fold` on lists: it must
   satisfy a "homomorphism" property with respect to append.
   Write this as a ∀ proposition.

5. Explain why `Decidable (∀ n : Nat, n + 0 = n)` nonetheless has an
   instance (`inferInstance` works).  What is different about this `∀`
   compared to an arbitrary `∀ n : Nat, P n`?
