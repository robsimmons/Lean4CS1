```lean
-- FPCourse/Unit3/Week08_HigherOrderFunctions.lean
import Mathlib.Data.List.Basic
```

# Week 8: Higher-Order Functions

## Functions as values

A *higher-order function* takes other functions as arguments or returns
functions as results.  In a typed functional language, this is not a
special case — functions are values like any other, and `→` is a type
constructor like `×` or `List`.

Higher-order functions enable *abstraction over computation patterns*.
Rather than writing separate functions for "sum all elements" and
"product all elements," we write one function `fold` parameterized by
the combining operation.

Every abstraction in this course corresponds to a *specification
pattern*: a family of propositions that all instances must satisfy.
```lean
namespace Week08
```

## 8.1  map, filter, fold: the canonical trio

These three functions together cover an enormous range of list
computations.
```lean
-- map: transform every element
#check @List.map      -- (α → β) → List α → List β

-- filter: keep elements satisfying a predicate
#check @List.filter   -- (α → Bool) → List α → List α

-- foldl: accumulate from the left
#check @List.foldl    -- (β → α → β) → β → List α → β

-- foldr: accumulate from the right
#check @List.foldr    -- (α → β → β) → β → List α → β

-- Evaluation traces for the three canonical operations:
-- map (·*2) [1,2,3]  ↝  [1*2, 2*2, 3*2]  ↝  [2, 4, 6]   (β-reduce per element)
-- filter even [1,2,3,4] ↝ keep 2, keep 4 ↝ [2, 4]        (evaluate predicate per element)
-- foldl (+) 0 [1,2,3]  ↝  foldl (+) 1 [2,3]              (0+1=1)
--                       ↝  foldl (+) 3 [3]                (1+2=3)
--                       ↝  foldl (+) 6 []                 (3+3=6)
--                       ↝  6                               (base case)
#eval [1,2,3,4,5].map (· * 2)              -- [2,4,6,8,10]
#eval [1,2,3,4,5].filter (· % 2 == 0)      -- [2,4]
#eval [1,2,3,4,5].foldl (· + ·) 0          -- 15
#eval [1,2,3,4,5].foldr (· :: ·) []        -- [1,2,3,4,5]
```

## 8.2  Deriving map from fold

`map` can be expressed as a `foldr`:
```lean
def mapViaFoldr (f : α → β) (xs : List α) : List β :=
  xs.foldr (fun x acc => f x :: acc) []

-- Specification: mapViaFoldr agrees with List.map
theorem mapViaFoldr_eq_map (f : α → β) (xs : List α) :
    mapViaFoldr f xs = xs.map f :=
  List.recOn xs
    rfl
    (fun h t ih => congrArg (f h :: ·) ih)

-- Similarly, filter can be expressed as foldr:
def filterViaFoldr (p : α → Bool) (xs : List α) : List α :=
  xs.foldr (fun x acc => if p x then x :: acc else acc) []
```

## 8.3  The functor laws

`List.map` satisfies two *functor laws*.  These are propositions —
logical types — that any correct implementation of `map` must inhabit.

**Law 1 (Identity)**: mapping the identity function does nothing.
**Law 2 (Composition)**: mapping a composition equals composing two maps.

These laws are not just bureaucratic requirements.  They are the
algebraic content of what it means to "transform elements without
changing structure."
```lean
-- Functor Law 1: map id = id
-- Read: "for all lists, mapping the identity is the identity"
theorem map_id_law : ∀ xs : List α, xs.map id = xs :=
  List.map_id

-- Functor Law 2: map (f ∘ g) = map f ∘ map g
-- Read: "for all f, g, lists: mapping their composition equals
--        mapping g then mapping f"
theorem map_comp_law : ∀ (f : β → γ) (g : α → β) (xs : List α),
    xs.map (f ∘ g) = (xs.map g).map f :=
  fun f g xs => by simp [← List.map_map]
```

## 8.4  Writing law statements for other types

A key skill: given a new type with a map-like operation, state the
functor laws for it.  The laws have the same FORM regardless of the type.

Here are the laws for `Option.map`:
```lean
-- You should read these and understand their form.
-- Then practice writing them for new types (see exercises).

theorem option_map_id : ∀ o : Option α, o.map id = o :=
  fun o => congr_fun Option.map_id o

theorem option_map_comp : ∀ (f : β → γ) (g : α → β) (o : Option α),
    o.map (f ∘ g) = (o.map g).map f :=
  fun f g o => (Option.map_map f g o).symm
```

## 8.5  fold and its specification pattern

`foldr f z` replaces each `::` constructor with `f` and the terminal
`[]` with `z`.

The key specification insight: many list properties are theorems about
`foldr`.  Length, sum, map, filter, append — all can be stated as `foldr`
computations.  The specification of `foldr` itself is therefore the
specification of a whole family of operations.
```lean
-- foldr specification: reconstructing the list
theorem foldr_cons_nil (xs : List α) :
    xs.foldr (· :: ·) [] = xs :=
  List.foldr_cons_nil

-- foldr and append:
theorem foldr_append (f : α → β → β) (z : β) (xs ys : List α) :
    (xs ++ ys).foldr f z = xs.foldr f (ys.foldr f z) :=
  List.foldr_append
```

## 8.6  The fusion law

When a `map` is followed immediately by a `fold`, they can be fused into
a single `fold`.  This is a *semantic optimization*: the two-pass
computation is equal to the single-pass computation.

Fusion laws are propositions.  Compilers use them as rewrite rules.
We state them here as types; applying them requires knowing they hold.
```lean
-- map-foldr fusion:
-- foldr f z (map g xs) = foldr (f ∘ g) z xs
theorem map_foldr_fusion (f : β → γ → γ) (z : γ) (g : α → β) (xs : List α) :
    (xs.map g).foldr f z = xs.foldr (f ∘ g) z :=
  List.recOn xs
    rfl
    (fun h t ih => congrArg (f (g h) ·) ih)
```

## Exercises

1. State the functor laws for a type you define:
   ```lean
   inductive MyPair (α : Type) where
     | mk : α → α → MyPair α
   def MyPair.map (f : α → β) : MyPair α → MyPair β
     | .mk a b => .mk (f a) (f b)
   ```
   Write the identity and composition laws as Prop terms.
   Use `decide` on concrete instances to check them.

2. Define `sumList : List Nat → Nat` using `foldl`.
   State the specification: `sumList xs = xs.foldl (· + ·) 0`.

3. State (as a Prop) the specification that `filter p` and `filter q`
   commute: `filter p (filter q xs) = filter q (filter p xs)`.
   Is this always true?  If not, give a counterexample.

4. Write `flatMap (f : α → List β) : List α → List β` using `foldr`.
   State its specification in terms of `List.bind`.

5. Write `flatten : List (List α) → List α` using `foldr` that
   concatenates a list of lists.  Test it:
   ```
   #eval flatten [[1, 2], [3], [4, 5, 6]]   -- [1, 2, 3, 4, 5, 6]
   #eval flatten ([] : List (List Nat))      -- []
   ```
   State its specification: `∀ xss, flatten xss = List.join xss`.
   Then write `countWhere : (α → Bool) → List α → Nat` using `foldr`
   that counts elements satisfying a predicate.  Test:
   ```
   #eval countWhere Nat.even [1, 2, 3, 4, 5]   -- 2
   ```
```lean
end Week08
```

