```lean
-- Distillate/Unit2/Week06_HigherOrderFunctions.lean
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic
```

# Week 6: Higher-Order Functions

## Functions as values

In Lean, functions are values.  You can pass a function as an argument
to another function, return a function from a function, and store a
function in a data structure.

A *higher-order function* takes a function as an argument.  The three
canonical examples — `map`, `filter`, and `fold` — capture the three
most common patterns of computation over lists.  Once you can use these
three fluently, you can express a remarkable range of programs without
writing explicit recursion.

From the specification perspective, higher-order functions are
especially important: the function argument is part of the specification.
`map f` transforms every element using `f`; the specification of `map`
refers to `f` as a parameter.  This is *parametric specification*:
propositions that say something about the behavior of a function in
terms of the functions passed to it.

**The dual reading.**  A higher-order function on data transforms values
using a function argument.  A higher-order function on propositions
transforms proofs using an implication argument.  `map f` applies `f` to
every element; logically, if you have a proof of `P x` for every `x` in
a list, and a proof that `P x → Q x`, then you get a proof of `Q x` for
every `x`.  The function argument is an implication; `map` applies it
uniformly.

You do not need to construct such proofs.  But the pattern is the same
one you saw in Weeks 1–4: the arrow `→` is both computation and
implication.  Higher-order functions correspond to proofs of propositions
that take and return proofs of implications as arguments.

```lean
namespace Week06
```

## 6.1  Map: transforming every element

`map f xs` applies `f` to every element of `xs` and collects the results.
The structure of the list is preserved; only the elements change.

```lean
-- map: apply f to every element
def myMap (f : Nat → Nat) : List Nat → List Nat
  | []     => []
  | h :: t => f h :: myMap f t

#eval myMap (fun n => n * 2) [1, 2, 3, 4]     -- [2, 4, 6, 8]
#eval myMap (fun n => n + 10) [1, 2, 3]        -- [11, 12, 13]
#eval myMap (fun n => n * n) [1, 2, 3, 4, 5]   -- [1, 4, 9, 16, 25]

-- The Lean standard library provides List.map for any element type
#eval List.map (· * 2) [1, 2, 3, 4]            -- [2, 4, 6, 8]
#eval List.map toString [1, 2, 3]               -- ["1", "2", "3"]
```

**Specification of map: the Functor laws.**

A correct `map` satisfies two laws:
1. **Identity**: `map id xs = xs`   (mapping the identity does nothing)
2. **Composition**: `map (f ∘ g) xs = map f (map g xs)`
   (mapping a composition is the same as two passes)

These are not optional; they define what it means to be a correct `map`.

**The dual reading of the Functor laws.**

| Computational law | Logical reading |
|-------------------|-----------------|
| `map id xs = xs` | Applying a trivial implication (P → P) changes nothing |
| `map (f ∘ g) = map f ∘ map g` | Chaining two implications is the same as applying their composition |

These laws hold for the same reason in both readings: the structure
of `map` does not inspect the elements, only passes them through the
function argument.  This is parametricity — the deep reason that
computation and logic stay in sync.

```lean
-- Functor identity law: verified by decide for a concrete list
#check (by decide : myMap id [1, 2, 3] = [1, 2, 3])

-- General proof (id applied elementwise does nothing)
theorem myMap_id (xs : List Nat) : myMap id xs = xs := by
  induction xs with
  | nil       => rfl
  | cons h t ih => simp [myMap, ih]

-- Functor composition law: map (f ∘ g) = map f ∘ map g
theorem myMap_comp (f g : Nat → Nat) (xs : List Nat) :
    myMap (f ∘ g) xs = myMap f (myMap g xs) := by
  induction xs with
  | nil       => rfl
  | cons h t ih => simp [myMap, Function.comp, ih]
```

## 6.2  Filter: keeping elements that satisfy a predicate

`filter p xs` returns the sublist of `xs` containing only the elements
for which the predicate `p` returns `true`.

```lean
def myFilter (p : Nat → Bool) : List Nat → List Nat
  | []     => []
  | h :: t => if p h then h :: myFilter p t else myFilter p t

#eval myFilter (fun n => n % 2 == 0) [1, 2, 3, 4, 5, 6]   -- [2, 4, 6]
#eval myFilter (fun n => n > 3) [1, 2, 3, 4, 5]            -- [4, 5]
#eval myFilter (fun n => n == 0) [1, 2, 3]                  -- []

-- Standard library version
#eval List.filter (· % 2 == 0) [1, 2, 3, 4, 5, 6]   -- [2, 4, 6]
```

**Specification of filter.**

A correct `filter p` satisfies:
- Every element `x` in the output satisfies `p x = true`.
- Every element `x` that satisfies `p x = true` appears in the output
  (if it was in the input).

```lean
-- Concrete specification: filter only keeps even numbers
#check (by decide :
  myFilter (fun n => n % 2 == 0) [1, 2, 3, 4, 5, 6] = [2, 4, 6])

-- General specification: all elements of the result satisfy the predicate
theorem myFilter_subset (p : Nat → Bool) (xs : List Nat) :
    ∀ x, x ∈ myFilter p xs → p x = true := by
  induction xs with
  | nil       => simp [myFilter]
  | cons h t ih =>
    intro x hx
    simp only [myFilter] at hx
    split at hx
    · simp only [List.mem_cons] at hx
      cases hx with
      | inl heq => rw [heq]; assumption
      | inr hmem => exact ih x hmem
    · exact ih x hx
```

## 6.3  Fold: collapsing a list to a single value

`fold` (also called `reduce`) combines all elements of a list into a
single result using a combining function and an initial value.

There are two variants:
- **`foldl`** (left fold): combines from left to right.
- **`foldr`** (right fold): combines from right to left.

For associative operations the result is the same; for non-associative
ones it differs.

```lean
-- foldr: right fold
def myFoldr (f : Nat → Nat → Nat) (init : Nat) : List Nat → Nat
  | []     => init
  | h :: t => f h (myFoldr f init t)

-- foldl: left fold (tail-recursive; accumulator)
def myFoldl (f : Nat → Nat → Nat) (acc : Nat) : List Nat → Nat
  | []     => acc
  | h :: t => myFoldl f (f acc h) t

-- Sum via fold
#eval myFoldr (· + ·) 0 [1, 2, 3, 4]   -- 10
#eval myFoldl (· + ·) 0 [1, 2, 3, 4]   -- 10

-- Product via fold
#eval myFoldr (· * ·) 1 [1, 2, 3, 4]   -- 24
#eval myFoldl (· * ·) 1 [1, 2, 3, 4]   -- 24

-- Maximum (requires a non-empty list or a sensible default)
#eval myFoldr Nat.max 0 [3, 1, 4, 1, 5, 9, 2]   -- 9

-- Map derived from foldr: map is a special fold
def mapViaFoldr (f : Nat → Nat) (xs : List Nat) : List Nat :=
  List.foldr (fun h acc => f h :: acc) [] xs

#eval mapViaFoldr (· * 2) [1, 2, 3]   -- [2, 4, 6]
```

**`fold` unifies `map` and `filter`.**  Both can be expressed as
special cases of `foldr`.  This means `fold` is the most fundamental
of the three: `map` and `filter` are abbreviations.

In practice, use `map` when you are transforming elements, `filter`
when you are selecting elements, and `fold` when you are accumulating.

**The dual reading of fold.**

`foldr f init xs` starts from `init` and applies `f` repeatedly.
Logically, this is iterated modus ponens: if you have a base proposition
and a rule that derives the next proposition from the current one,
`fold` chains the derivations across the entire list.

| `foldr` computation | Logical reading |
|---------------------|-----------------|
| `init : β` (starting value) | Base proposition (starting fact) |
| `f : α → β → β` (combining step) | Inference rule: from an element and a fact, derive a new fact |
| `foldr f init [x₁, x₂, x₃]` | Chain: apply the rule three times from the base |

This is why `fold` is the most powerful of the three: it captures the
general pattern of building an answer (or a proof) one step at a time.

## 6.4  Function composition and anonymous functions

Anonymous functions (`fun x => ...`) and function composition (`∘`)
let you build complex transformations inline, without naming every
intermediate step.

```lean
-- Composition: (f ∘ g) x = f (g x)
def doubleAndSquare : Nat → Nat := (fun n => n * n) ∘ (fun n => n * 2)
#eval doubleAndSquare 3   -- (3 * 2)² = 36

-- Point-free style: chain operations without naming the argument
def processNats : List Nat → List Nat :=
  List.map (· * 2) ∘ List.filter (· % 2 == 0)

#eval processNats [1, 2, 3, 4, 5, 6]   -- [4, 8, 12]   (keep evens, then double)

-- The same pipeline written with the pipe operator
#eval [1, 2, 3, 4, 5, 6]
  |> List.filter (· % 2 == 0)
  |> List.map (· * 2)               -- [4, 8, 12]
```

## 6.5  Polymorphic higher-order functions

The versions of `map`, `filter`, and `fold` above work only on
`List Nat`.  The standard library versions are *polymorphic*:
they work on lists of any type.

The key ingredients:
- A *type parameter* `α` stands for any type.
- The function argument `f : α → β` transforms elements of type `α`
  into elements of type `β`.
- The predicate `p : α → Bool` tests elements of any type `α`.

```lean
-- Polymorphic map: List α → List β
-- (using the standard library version)
#eval List.map (fun s => s.length) ["hello", "world", "!"]   -- [5, 5, 1]
#eval List.map (· + 1) [1, 2, 3]                              -- [2, 3, 4]
#eval List.map (fun b => !b) [true, false, true]              -- [false, true, false]

-- Polymorphic filter
#eval List.filter (fun s => s.length > 3) ["hi", "hello", "bye", "world"]
-- ["hello", "world"]

-- Polymorphic fold
#eval List.foldl (fun acc s => acc ++ s ++ " ") "" ["hello", "world", "!"]
-- "hello world ! "
```

**Specification of polymorphic map.**

For polymorphic `map`, the Functor laws hold at every type:
- `List.map id xs = xs`  for any `xs : List α`
- `List.map (f ∘ g) xs = List.map f (List.map g xs)`

`decide` cannot directly check universal polymorphic statements, but
concrete instances for any specific type can be verified.

```lean
#check (by decide : List.map id [1, 2, 3] = [1, 2, 3])
#check (by decide : List.map ((· * 2) ∘ (· + 1)) [1, 2, 3] =
                    List.map (· * 2) (List.map (· + 1) [1, 2, 3]))
```

## Summary

- **Higher-order functions** take functions as arguments, enabling
  abstraction over computation patterns.
- **`map f xs`**: apply `f` to every element; result is same length.
  Functor laws: identity and composition.
- **`filter p xs`**: keep only elements where `p` returns `true`.
- **`foldr f init xs`** / **`foldl f acc xs`**: collapse a list into
  one value using combining function `f`.
  Both `map` and `filter` can be expressed as `foldr`.
- **Anonymous functions** (`fun x => ...`) and **composition** (`∘`)
  build complex transformations inline.
- **Polymorphic** versions (`List.map`, `List.filter`, `List.foldl`)
  work on lists of any element type.
- Specifications of higher-order functions are *parametric*:
  they describe behavior in terms of the function argument.
- **The dual reading**: higher-order functions on data are higher-order
  functions on propositions.  `map` applies an implication uniformly;
  `fold` chains inference steps.  The Functor laws hold in both readings.

```lean
end Week06
```
