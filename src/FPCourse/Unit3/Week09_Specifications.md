```lean
-- FPCourse/Unit3/Week09_Specifications.lean
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise

open scoped List
```

# Week 9: Specifications in Practice

## What is a correct sort?

Sorting is one of the most studied problems in computer science, yet
most textbooks define correctness informally.  We will define it
precisely as a type.

A correct sorting function must satisfy two independent conditions:
1. **Sorted output**: the result list is in non-decreasing order.
2. **Permutation**: the result contains exactly the same elements as
   the input, in the same multiplicity.

Both conditions are needed.  Without "sorted": returning the empty list
or a constant list would satisfy "permutation" alone.  Without "permutation":
returning `[]` would satisfy "sorted" alone.

Together, they express exactly what we mean by "correctly sorts."
```lean
namespace Week09

-- List.Sorted is now List.Pairwise in Lean 4.28 / Mathlib
abbrev List.Sorted (r : α → α → Prop) (xs : List α) : Prop := List.Pairwise r xs
```

## 9.1  The Sorted predicate

`List.Sorted r xs` holds iff every adjacent pair in `xs` satisfies `r`.
We use `(· ≤ ·)` for ascending order.
```lean
-- Sorted is now an alias for List.Pairwise:
#check @List.Pairwise   -- (r : α → α → Prop) → List α → Prop

-- Examples — use decide on concrete lists:
example : List.Sorted (· ≤ ·) ([1, 2, 3, 4] : List Nat) := by decide
example : ¬ List.Sorted (· ≤ ·) ([1, 3, 2] : List Nat) := by decide
example : List.Sorted (· ≤ ·) ([] : List Nat) := by decide   -- vacuously
```

## 9.2  The Perm predicate

`List.Perm xs ys` (written `xs ~ ys`) holds iff `xs` is a permutation
of `ys`.  Equivalently: both lists contain the same elements with the
same multiplicities.
```lean
#check @List.Perm   -- List α → List α → Prop

-- Examples:
example : ([1, 2, 3] : List Nat) ~ [3, 1, 2] := by decide
example : ([1, 2, 3] : List Nat) ~ [1, 2, 3] := List.Perm.refl _
example : ¬ ([1, 2] : List Nat) ~ [1, 2, 3] := by decide

-- Perm is symmetric, transitive, and congruent with respect to cons.
theorem perm_symm (xs ys : List α) : xs ~ ys → ys ~ xs :=
  List.Perm.symm
```

## 9.3  The CorrectSort specification

This is the heart of the week: a single type that captures what it means
for a function to be a correct sorting function.
```lean
def CorrectSort (sort : List Nat → List Nat) : Prop :=
  ∀ xs : List Nat,
    List.Sorted (· ≤ ·) (sort xs) ∧   -- output is sorted
    sort xs ~ xs                        -- output is a permutation of input
```

## 9.4  Insertion sort: implementation

Insertion sort inserts each element of the input into the correct
position in an already-sorted list.
```lean
def insert' (x : Nat) : List Nat → List Nat
  | []      => [x]
  | h :: t  => if x ≤ h then x :: h :: t else h :: insert' x t

def insertionSort : List Nat → List Nat
  | []      => []
  | h :: t  => insert' h (insertionSort t)

#eval insertionSort [5, 3, 1, 4, 2]    -- [1, 2, 3, 4, 5]
#eval insertionSort []                  -- []
```

## 9.5  Proving CorrectSort — provided term-mode proofs

Proving `CorrectSort insertionSort` requires two sub-proofs.  Both
are provided here as term-mode proofs for you to read.

**Helper 1**: inserting into a sorted list produces a sorted list.
```lean
-- Local helper for insert_sorted
private theorem insert_perm' (x : Nat) :
    ∀ xs : List Nat, insert' x xs ~ x :: xs
  | []      => List.Perm.refl _
  | h :: t  => by
    simp only [insert']
    split_ifs with hle
    · exact List.Perm.refl _
    · exact List.Perm.trans
        (List.Perm.cons h (insert_perm' x t))
        (List.Perm.swap x h t)

theorem insert_sorted (x : Nat) :
    ∀ xs : List Nat, List.Sorted (· ≤ ·) xs →
      List.Sorted (· ≤ ·) (insert' x xs)
  | [], _ => List.pairwise_singleton (· ≤ ·) x
  | h :: t, hst => by
    simp only [insert']
    split_ifs with hle
    · -- x ≤ h: insert x at front
      apply List.Pairwise.cons
      · intro y hy
        simp only [List.mem_cons] at hy
        cases hy with
        | inl heq =>
          exact heq ▸ hle
        | inr hmem =>
          exact Nat.le_trans hle ((List.pairwise_cons.mp hst).1 y hmem)
      · exact hst
    · -- x > h: insert into tail
      have hxh : h ≤ x := Nat.le_of_not_le hle
      apply List.Pairwise.cons
      · intro y hy
        have : y ∈ x :: t := (insert_perm' x t).subset hy
        simp only [List.mem_cons] at this
        cases this with
        | inl heq => exact heq ▸ hxh
        | inr hmem => exact (List.pairwise_cons.mp hst).1 y hmem
      · exact insert_sorted x t (List.pairwise_cons.mp hst).2
```

**Helper 2**: inserting preserves the permutation relation.
```lean
theorem insert_perm (x : Nat) :
    ∀ xs : List Nat, insert' x xs ~ x :: xs
  | []      => List.Perm.refl _
  | h :: t  => by
    simp only [insert']
    split_ifs with hle
    · exact List.Perm.refl _
    · exact List.Perm.trans
        (List.Perm.cons h (insert_perm x t))
        (List.Perm.swap x h t)
```

**Helper 3**: insertion sort produces a sorted list.
```lean
theorem insertionSort_sorted :
    ∀ xs : List Nat, List.Sorted (· ≤ ·) (insertionSort xs)
  | []      => List.Pairwise.nil
  | h :: t  => insert_sorted h (insertionSort t) (insertionSort_sorted t)
```

**Helper 4**: insertion sort is a permutation.
```lean
theorem insertionSort_perm :
    ∀ xs : List Nat, insertionSort xs ~ xs
  | []      => List.Perm.refl _
  | h :: t  =>
    List.Perm.trans
      (insert_perm h (insertionSort t))
      (List.Perm.cons h (insertionSort_perm t))
```

**Main theorem**: insertion sort is correct.
```lean
theorem insertionSort_correct : CorrectSort insertionSort :=
  fun xs => ⟨insertionSort_sorted xs, insertionSort_perm xs⟩
```

## 9.6  Verifying on concrete instances

Because `Sorted` and `Perm` are decidable on `List Nat`, we can check
correctness on concrete examples with `decide`.
```lean
example : List.Sorted (· ≤ ·) (insertionSort [3, 1, 4, 1, 5, 9]) := by decide
example : insertionSort [3, 1, 4, 1, 5] ~ [3, 1, 4, 1, 5] := by decide
```

## 9.7  Specifications with pre- and postconditions

A more general specification pattern uses explicit pre- and postconditions
attached to function types.  This is the proof-carrying type pattern
generalized.
```lean
-- A function with a precondition in its type:
def sortedMerge
    (xs ys : List Nat)
    (hxs : List.Sorted (· ≤ ·) xs)
    (hys : List.Sorted (· ≤ ·) ys) :
    { zs : List Nat // List.Sorted (· ≤ ·) zs ∧ zs ~ xs ++ ys } :=
  -- Implementation omitted; the TYPE is the specification.
  -- Any implementation must produce a Σ-type (subtype) carrying the proof.
  ⟨(xs ++ ys).mergeSort (· ≤ ·),
   ⟨List.pairwise_mergeSort' (· ≤ ·) (xs ++ ys),
    List.mergeSort_perm (xs ++ ys) (· ≤ ·)⟩⟩
```

## Exercises

1. Use `decide` to check that `insertionSort [9, 1, 3, 7, 2, 6]` produces
   a sorted list.

2. State the specification for a `dedup : List Nat → List Nat` function
   that removes duplicate elements.  What two properties must it satisfy?

3. Define `CorrectSort'` for descending order and show `insertionSort`
   does NOT satisfy it by giving a counterexample with `decide`.

4. State (as a Prop) the specification: "if xs is already sorted,
   then insertionSort xs = xs."  (You need not prove it.)

5. Write the type of a hypothetical `mergeSort : List Nat → List Nat`
   such that its type INCLUDES the proof that it satisfies `CorrectSort`.
   Use a subtype `{ f : List Nat → List Nat // CorrectSort f }`.
```lean
end Week09
```

