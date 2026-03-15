```lean
-- FPCourse/Unit2/Week06_Trees.lean
import Mathlib.Data.List.Sort
import Mathlib.Order.Basic
```

# Week 6: Trees and BST Invariants

## Binary trees

A binary tree over type `α` is either a leaf or a node carrying a value
and two subtrees.  Like lists, trees are defined inductively, and
functions on them are defined by structural recursion.

The key new idea this week: *invariants*.  A BST (binary search tree)
is not just any tree — it is a tree satisfying a *predicate* that
constrains the relationship between each node's value and the values in
its subtrees.  That predicate is a proposition, and preserving it is
a specification.
```lean
namespace Week06
```

## 6.1  The BTree type
```lean
inductive BTree (α : Type) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α
deriving Repr
```

## 6.2  Basic tree functions
```lean
def BTree.size : BTree α → Nat
  | .leaf         => 0
  | .node l _ r   => l.size + 1 + r.size

def BTree.height : BTree α → Nat
  | .leaf         => 0
  | .node l _ r   => max l.height r.height + 1

def BTree.member [DecidableEq α] (x : α) : BTree α → Bool
  | .leaf         => false
  | .node l v r   => x == v || l.member x || r.member x

-- In-order traversal produces a list
def BTree.toList : BTree α → List α
  | .leaf         => []
  | .node l v r   => l.toList ++ [v] ++ r.toList

-- Specification of toList and size:
theorem toList_length_eq_size (t : BTree α) :
    t.toList.length = t.size := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
    simp only [BTree.toList, BTree.size, List.length_append, List.length_cons,
               List.length_nil]
    omega
```

## 6.3  The BST predicate

A BST (for `BTree Nat`) is a tree where:
- Every value in the left subtree is strictly less than the root value.
- Every value in the right subtree is strictly greater than the root value.
- Both subtrees are themselves BSTs.

We express "every value in the subtree satisfies P" using an auxiliary
predicate `BTree.ForAll`.
```lean
-- ForAll: every element of a tree satisfies a predicate
def BTree.ForAll (p : α → Prop) : BTree α → Prop
  | .leaf         => True
  | .node l v r   => p v ∧ l.ForAll p ∧ r.ForAll p

-- IsBST: the binary search tree invariant for Nat
inductive IsBST : BTree Nat → Prop where
  | leaf : IsBST .leaf
  | node : IsBST l → IsBST r
         → l.ForAll (· < v)
         → r.ForAll (v < ·)
         → IsBST (.node l v r)

-- We can check IsBST on concrete trees using decide,
-- once we make BTree.ForAll decidable:
instance decForAll (p : Nat → Prop) [DecidablePred p] :
    DecidablePred (BTree.ForAll p)
  | .leaf       => Decidable.isTrue trivial
  | .node l v r =>
    match decForAll p l, decForAll p r, inferInstanceAs (Decidable (p v)) with
    | Decidable.isTrue hl, Decidable.isTrue hr, Decidable.isTrue hv =>
      Decidable.isTrue ⟨hv, hl, hr⟩
    | Decidable.isFalse hl, _, _ =>
      Decidable.isFalse (fun ⟨_, h, _⟩ => hl h)
    | _, Decidable.isFalse hr, _ =>
      Decidable.isFalse (fun ⟨_, _, h⟩ => hr h)
    | _, _, Decidable.isFalse hv =>
      Decidable.isFalse (fun ⟨h, _, _⟩ => hv h)
```

## 6.4  BST insertion

Insert `x` into a BST, maintaining the invariant:
- If `x < v`, insert into the left subtree.
- If `v < x`, insert into the right subtree.
- If `x = v`, the element is already present.
```lean
def bstInsert (x : Nat) : BTree Nat → BTree Nat
  | .leaf         => .node .leaf x .leaf
  | .node l v r   =>
    if x < v then .node (bstInsert x l) v r
    else if v < x then .node l v (bstInsert x r)
    else .node l v r   -- x = v: already present
```

## 6.5  Preservation of ForAll

A key lemma: if all elements of `t` satisfy `p`, and `p x` holds, then all
elements of `bstInsert x t` also satisfy `p`.

The provided proof is by structural recursion on `t`, mirroring the
structure of `bstInsert`.
```lean
-- Provided term-mode proof of ForAll preservation.
theorem forAll_bstInsert (p : Nat → Prop) (x : Nat) (hx : p x) :
    ∀ t : BTree Nat, t.ForAll p → (bstInsert x t).ForAll p
  | .leaf,         _              => by simp [bstInsert, BTree.ForAll]; exact hx
  | .node l v r,  ⟨hv, hfl, hfr⟩ => by
    simp only [bstInsert]
    split_ifs with hlt hgt
    · exact ⟨hv, forAll_bstInsert p x hx l hfl, hfr⟩
    · exact ⟨hv, hfl, forAll_bstInsert p x hx r hfr⟩
    · exact ⟨hv, hfl, hfr⟩
```

## 6.6  Preservation of IsBST

If `t` is a BST and `x : Nat`, then `bstInsert x t` is also a BST.

The proof uses `forAll_bstInsert` twice per recursive case — once for the
left bound and once for the right — along with the structurally recursive
IsBST assumption.

**This proof is complete: no `sorry`, no `by`.**
```lean
theorem bstInsert_isBST (x : Nat) :
    ∀ t : BTree Nat, IsBST t → IsBST (bstInsert x t)
  | .leaf,        _ => by
    simp [bstInsert]
    exact IsBST.node IsBST.leaf IsBST.leaf trivial trivial
  | .node l v r,  IsBST.node hl hr hfl hfr => by
    simp only [bstInsert]
    split_ifs with hlt hgt
    · exact IsBST.node (bstInsert_isBST x l hl) hr
        (forAll_bstInsert (· < v) x hlt l hfl) hfr
    · exact IsBST.node hl (bstInsert_isBST x r hr)
        hfl (forAll_bstInsert (v < ·) x hgt r hfr)
    · exact IsBST.node hl hr hfl hfr
```

## 6.7  Mutual recursion: Rose trees

A *rose tree* has nodes with arbitrarily many children (stored as a list).
Defining rose trees requires mutual recursion between the tree type and
the forest (list of trees) type.
```lean
mutual
  inductive RoseTree (α : Type) where
    | node : α → Forest α → RoseTree α

  inductive Forest (α : Type) where
    | nil  : Forest α
    | cons : RoseTree α → Forest α → Forest α
end

mutual
  def roseSize : RoseTree α → Nat
    | .node _ f => forestSize f + 1

  def forestSize : Forest α → Nat
    | .nil      => 0
    | .cons t f => roseSize t + forestSize f
end
```

## Exercises

1. Define `BTree.map (f : α → β) : BTree α → BTree β` and state its
   specification: "map f preserves size."

2. Define a `BTree.search (x : Nat) (t : BTree Nat) (h : IsBST t) : Bool`
   that searches efficiently (O(log n) on balanced trees, O(n) worst case)
   by exploiting the BST invariant.

3. State (as a Prop) the correctness specification for `bstInsert x t`:
   "x is a member of bstInsert x t."  You may use `BTree.member`.

4. Use `decide` to verify that the following tree IS a BST:
   ```
       5
      / \
     3   7
   ```
   Construct it as a `BTree Nat` value, then apply `IsBST` and check
   with `decide`.

5. State the specification for `roseSize` analogous to
   `toList_length_eq_size`.
```lean
end Week06
```

