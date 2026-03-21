import VersoManual

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
namespace Week05

#doc (Manual) "Week 5: Lists" =>

# Lists as the canonical inductive type
%%%
number := false
%%%

`List α` is defined inductively:
- `[]` (nil) — the empty list
- `h :: t` (cons) — a head element `h : α` followed by a tail `t : List α`

Every function on lists follows this structure: one clause for `[]`, one
clause for `h :: t` (which may recurse on `t`).

The specifications for list functions are propositions that quantify over
all lists.  Some of these propositions are decidable — when the element
type has `DecidableEq` and the list is finite, we can check them with
`decide`.

# Standard list functions and their specifications

The specifications below are ALL provided as term-mode proofs.
Read them; understand the proposition being stated; observe how the
proof term mirrors the function definition.

```lean
-- Length
theorem length_nil : ([] : List α).length = 0 := rfl
theorem length_cons (h : α) (t : List α) :
    (h :: t).length = t.length + 1 := rfl

-- Append
theorem append_nil (xs : List α) : xs ++ [] = xs :=
  List.append_nil xs

theorem nil_append (xs : List α) : [] ++ xs = xs :=
  List.nil_append xs

theorem append_assoc (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  List.append_assoc xs ys zs

-- Length distributes over append
theorem length_append (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length :=
  List.length_append

-- Membership and append: ∈ distributes over ++
theorem mem_append_iff (a : α) (xs ys : List α) :
    a ∈ xs ++ ys ↔ a ∈ xs ∨ a ∈ ys :=
  List.mem_append
```

# Decide on finite lists

When the element type has `DecidableEq`, propositions of the form
`∀ x ∈ xs, P x` are decidable for finite `xs` (when `P` is decidable).
This means `decide` can verify them automatically.

```lean
-- Evaluation: `decide` checks finite-list claims by evaluating the predicate
-- on each element in turn.  ∀ x ∈ [2,4,6,8], x%2=0 becomes:
--   2%2=0 ↝ true,  4%2=0 ↝ true,  6%2=0 ↝ true,  8%2=0 ↝ true  ✓
example : ∀ x ∈ ([2, 4, 6, 8] : List Nat), x % 2 = 0 := by decide
example : ∀ x ∈ ([1, 3, 5, 7] : List Nat), x % 2 = 1 := by decide
example : ∃ x ∈ ([10, 20, 30] : List Nat), x > 15    := by decide

-- Membership in a concrete list:
example : 3 ∈ ([1, 2, 3, 4] : List Nat) := by decide
example : ¬ (5 ∈ ([1, 2, 3, 4] : List Nat)) := by decide

-- Equality of concrete lists:
example : ([1, 2] ++ [3, 4] : List Nat) = [1, 2, 3, 4] := by decide
```

# Reverse and the auxiliary lemma pattern

`reverse` is defined recursively.  Its specification — that reversing
twice returns the original list — requires a helper lemma about how
`reverse` interacts with `++`.

This illustrates a general pattern: when a direct proof gets stuck,
look at what the inductive step requires and name it as a separate lemma.
The provided proofs below demonstrate this pattern explicitly.

```lean
theorem reverse_append (xs ys : List α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse :=
  List.reverse_append

theorem reverse_reverse (xs : List α) : xs.reverse.reverse = xs :=
  List.reverse_reverse xs

-- The proof of reverse_reverse in Mathlib uses reverse_append.
-- The dependency is: reverse_reverse requires reverse_append,
-- which in turn requires nil_append and append_assoc.
-- Each lemma is proved by structural recursion on the first list.
```

# Map and its specification

`List.map f` applies `f` to every element.  Its specification:
1. Map preserves length.
2. Map distributes over append.
3. Mapping the identity function is the identity on lists.
4. Mapping a composition equals composing two maps.

```lean
theorem map_length (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length :=
  List.length_map f

theorem map_append (f : α → β) (xs ys : List α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f :=
  List.map_append

theorem map_id_eq (xs : List α) : xs.map id = xs :=
  List.map_id xs

theorem map_comp (f : β → γ) (g : α → β) (xs : List α) :
    xs.map (f ∘ g) = (xs.map g).map f := by
  simp [← List.map_map]
```

# Specifications students should practice writing

Reading a specification is easier than writing one.  The following are
propositions about list functions.  Practice writing them yourself,
then check against these.

"filter keeps exactly the elements satisfying the predicate":

```lean
-- ∀ x, x ∈ filter p xs ↔ x ∈ xs ∧ p x = true
theorem mem_filter_iff (p : α → Bool) (xs : List α) (x : α) :
    x ∈ xs.filter p ↔ x ∈ xs ∧ p x = true :=
  List.mem_filter

-- "length of filter is at most length of input"
theorem filter_length_le (p : α → Bool) (xs : List α) :
    (xs.filter p).length ≤ xs.length :=
  List.length_filter_le p xs
```

# Exercises
%%%
number := false
%%%

1. State (as a Prop) the specification: "if n ∈ xs, then n ∈ xs ++ ys."
   Prove it using `List.mem_append`.

2. Use `decide` to verify: every element of `[2, 4, 6, 8, 10]` is even.

3. Use `decide` to verify: there exists an element in `[3, 7, 12, 5]`
   that is greater than 10.

4. State the specification: "map f (reverse xs) = reverse (map f xs)."
   This is `List.map_reverse`.  Look it up and read the type.

5. Write a function `myZip : List α → List β → List (α × β)` that
   pairs corresponding elements.  State its length specification:
   `(myZip xs ys).length = min xs.length ys.length`.
