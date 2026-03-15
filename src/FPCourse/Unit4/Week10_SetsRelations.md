```lean
-- FPCourse/Unit4/Week10_SetsRelations.lean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Relation
```

# Week 10: Sets and Relations

## Sets as predicates

In Lean (and in Mathlib), a *set* over type `α` is simply a predicate:

```lean
def Set (α : Type u) : Type u := α → Prop
```

A set `s : Set α` is a function that takes an element `x : α` and
returns a proposition `s x : Prop` — the claim that `x` belongs to `s`.

This definition is mathematically natural and computationally illuminating:
membership is a proposition, and propositions are types.  A proof that
`x ∈ s` is a term of type `s x`.

The connection to the course themes: sets are logical types indexed by
their elements.  Every operation on sets is an operation on propositions.
```lean
namespace Week10
```

## 10.1  Set membership and basic notation
```lean
-- Set α is defined in Mathlib as α → Prop
#check @Set        -- (α : Type u) → Type u
#print Set         -- def Set (α : Type u) := α → Prop

-- Membership: x ∈ s is notation for s x
example : (3 : Nat) ∈ ({1, 2, 3} : Set Nat) := by decide
example : (5 : Nat) ∉ ({1, 2, 3} : Set Nat) := by decide

-- The universal set (all elements)
#check @Set.univ   -- Set α  (= fun _ => True)

-- The empty set
#check (∅ : Set _)  -- Set α  (= fun _ => False)

-- Membership in univ and empty:
theorem mem_univ (x : α) : x ∈ (Set.univ : Set α) :=
  trivial

theorem not_mem_empty (x : α) : x ∉ (∅ : Set α) :=
  False.elim
```

## 10.2  Set operations as proposition operations

Because sets are predicates, every set operation corresponds to a
propositional connective.

| Set operation | Logical meaning | Notation |
|--------------|----------------|---------|
| `s ∩ t` (intersection) | `s x ∧ t x` | `∩` |
| `s ∪ t` (union) | `s x ∨ t x` | `∪` |
| `sᶜ` (complement) | `¬ s x` | `·ᶜ` |
| `s \ t` (difference) | `s x ∧ ¬ t x` | `\` |
| `s ⊆ t` (subset) | `∀ x, s x → t x` | `⊆` |

```lean
-- Intersection is ∧:
theorem mem_inter_iff (x : α) (s t : Set α) :
    x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t :=
  Set.mem_inter_iff x s t

-- Union is ∨:
theorem mem_union_iff (x : α) (s t : Set α) :
    x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t :=
  Set.mem_union x s t

-- Subset is ∀/→:
theorem subset_def (s t : Set α) :
    s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t :=
  Iff.intro (fun h x hx => h hx) (fun h x hx => h x hx)
```

## 10.3  Set algebraic laws as propositions

These laws are propositions that hold for all sets.  The proofs are
provided as term-mode proofs.
```lean
-- Commutativity:
theorem inter_comm (s t : Set α) : s ∩ t = t ∩ s :=
  Set.inter_comm s t

theorem union_comm (s t : Set α) : s ∪ t = t ∪ s :=
  Set.union_comm s t

-- Distributivity:
theorem inter_union_distrib (r s t : Set α) :
    r ∩ (s ∪ t) = (r ∩ s) ∪ (r ∩ t) :=
  Set.inter_union_distrib_left r s t

-- De Morgan:
theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  Set.compl_union s t

-- Subset is transitive:
theorem subset_trans {s t u : Set α} (h1 : s ⊆ t) (h2 : t ⊆ u) : s ⊆ u :=
  Set.Subset.trans h1 h2
```

## 10.4  Relations

A *relation* between types `α` and `β` is a predicate on pairs:

```lean
def Rel (α β : Type u) : Type u := α → β → Prop
```

A term `r : Rel α β` applied to `a : α` and `b : β` gives a proposition
`r a b`: the claim that `a` and `b` are related.

Sets are the special case `Rel α α` (homogeneous relations), or `Rel α Prop`
(which is just `Set α`).
```lean
-- Rel is a binary predicate (defined locally for compatibility)
abbrev Rel (α β : Type*) := α → β → Prop

-- Example relations:
def divides : Rel Nat Nat := fun m n => ∃ k, n = m * k
def sameLength : Rel (List α) (List β) := fun xs ys => xs.length = ys.length
def lePair : Rel Nat Nat := (· ≤ ·)

-- Membership in a relation:
example : divides 3 12 := ⟨4, rfl⟩
example : divides 1 n := ⟨n, (Nat.one_mul n).symm⟩   -- for any n
```

## 10.5  Properties of relations

Key relational properties are propositions.  We state each as a type
so that checking a relation has the property means inhabiting the type.
```lean
-- Reflexive: every element is related to itself
def RelReflexive (r : Rel α α) : Prop := ∀ a, r a a

-- Symmetric: if a is related to b then b is related to a
def RelSymmetric (r : Rel α α) : Prop := ∀ a b, r a b → r b a

-- Transitive: r a b and r b c implies r a c
def RelTransitive (r : Rel α α) : Prop := ∀ a b c, r a b → r b c → r a c

-- An equivalence relation satisfies all three:
def Equivalence' (r : Rel α α) : Prop :=
  RelReflexive r ∧ RelSymmetric r ∧ RelTransitive r

-- ≤ on Nat is reflexive and transitive but not symmetric:
example : RelReflexive (· ≤ · : Rel Nat Nat) :=
  fun a => Nat.le_refl a

example : RelTransitive (· ≤ · : Rel Nat Nat) :=
  fun _ _ _ => Nat.le_trans

example : ¬ RelSymmetric (· ≤ · : Rel Nat Nat) :=
  fun h => absurd (h 0 1 (Nat.zero_le 1)) (by decide)

-- = on Nat is an equivalence relation:
example : Equivalence' (· = · : Rel Nat Nat) :=
  ⟨fun _ => rfl,
   fun _ _ h => h.symm,
   fun _ _ _ h1 h2 => h1.trans h2⟩
```

## 10.6  Relational composition and image

*Composition* of relations: `r` composed with `s` relates `a` to `c`
if there exists a `b` such that `r a b` and `s b c`.

*Image* of a set under a relation: the set of all elements reachable
from `s` by following `r`.
```lean
-- Relational composition:
def relComp (r : Rel α β) (s : Rel β γ) : Rel α γ :=
  fun a c => ∃ b, r a b ∧ s b c

-- Image of a set under a function (as a relation):
#check @Set.image
-- Set.image : (α → β) → Set α → Set β
-- (Set.image f s) b ↔ ∃ a ∈ s, f a = b

-- Preimage:
#check @Set.preimage
-- Set.preimage : (α → β) → Set β → Set α
-- (Set.preimage f t) a ↔ f a ∈ t

-- Image of the universal set is the range:
theorem image_univ (f : α → β) :
    Set.image f Set.univ = Set.range f :=
  Set.image_univ
```

## 10.7  Functions as total relations

A function `f : α → β` determines a *functional relation*: the set of
pairs `{(a, f a) | a : α}`.  A relation is *functional* if every element
of the domain is related to exactly one element of the codomain.

Sets and relations are the language in which we write specifications for
programs dealing with collections of data.  The Dict type class (Week 11)
is a partial function — a relation where each key relates to at most one
value.  Sorting is about relations between the input and output lists.

## Exercises

1. Let `s = {n : Nat | n % 2 = 0}` and `t = {n : Nat | n < 10}`.
   State and check with `decide` that `s ∩ t = {0, 2, 4, 6, 8}`.
   (You will need to work with `Finset` for decidable checking;
   or just state the subset direction and check small cases.)

2. Define the relation `adjacentList : Rel (List Nat) (List Nat)` where
   `xs` and `ys` are adjacent if they differ by one insertion or deletion.
   State (as a Prop) that this relation is symmetric.

3. Show that `divides` is reflexive and transitive.  Is it symmetric?

4. State what it means for a relation `r : Rel α α` to be an *order*
   (reflexive, transitive, and antisymmetric: `r a b → r b a → a = b`).
   Show that `(· ≤ ·)` on `Nat` satisfies this.

5. State the specification: "the image of `s ∩ t` under `f` is a subset
   of `(Set.image f s) ∩ (Set.image f t)`."  This is `Set.image_inter_subset`.
   Look it up in Mathlib and read the type.
```lean
end Week10
```

