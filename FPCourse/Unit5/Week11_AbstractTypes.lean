import VersoManual

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
namespace Week11

#doc (Manual) "Week 11: Abstract Types" =>

# Abstraction via type classes
%%%
number := false
%%%

An _abstract type_ presents an interface — a collection of operations
with specified types — while hiding the implementation.  Callers program
against the interface; the implementation can change without affecting
callers.

In Lean, type classes express abstract types.  A class declaration is an
interface.  An instance declaration is an implementation.  Laws stated in
the class are the _specification_: propositions that every implementation
must satisfy.

The connection to Week 10: the specification for `Dict` is relational.
A dictionary is a partial function — a relation where each key maps to
at most one value.  The laws of `Dict` are laws of partial functions.

# The Dict interface

A dictionary maps keys to values.  Operations: empty dict, insert,
lookup, and delete.

```lean
class Dict (d : Type → Type → Type) where
  empty  : d k v
  insert : k → v → d k v → d k v
  lookup : [DecidableEq k] → k → d k v → Option v
  delete : [DecidableEq k] → k → d k v → d k v
```

# Laws: the specification for Dict

The laws below are propositions that every `Dict` implementation must
satisfy.  They define what it MEANS to be a dictionary.

These are relational specifications in the sense of Week 10: they
describe how the abstract state (a partial function from keys to values)
changes under each operation.

```lean
class LawfulDict (d : Type → Type → Type) [DecidableEq k] extends Dict d where
  lookup_empty  : ∀ (key : k), lookup key (empty : d k v) = none
  lookup_insert_same : ∀ (key : k) (val : v) (m : d k v),
      lookup key (insert key val m) = some val
  lookup_insert_diff : ∀ (k1 k2 : k) (val : v) (m : d k v),
      k1 ≠ k2 → lookup k1 (insert k2 val m) = lookup k1 m
  lookup_delete_same : ∀ (key : k) (m : d k v),
      lookup key (delete key m) = none
  lookup_delete_diff : ∀ (k1 k2 : k) (m : d k v),
      k1 ≠ k2 → lookup k1 (delete k2 m) = lookup k1 m
```

# Association list implementation

An association list stores key-value pairs in a list.

```lean
def AList (k v : Type) := List (k × v)

def AList.empty : AList k v := []

def AList.insert (key : k) (val : v) (m : AList k v) : AList k v :=
  (key, val) :: m

def AList.lookup [DecidableEq k] (key : k) : AList k v → Option v
  | []            => none
  | (k, v) :: t  => if key == k then some v else AList.lookup key t

def AList.delete [DecidableEq k] (key : k) : AList k v → AList k v
  | []            => []
  | (k, v) :: t  => if key == k then AList.delete key t
                    else (k, v) :: AList.delete key t

instance : Dict AList where
  empty  := AList.empty
  insert := AList.insert
  lookup := AList.lookup
  delete := AList.delete

-- Verify the laws hold.  Provided as term-mode proofs:
theorem alist_lookup_empty [DecidableEq k] (key : k) :
    AList.lookup key (AList.empty : AList k v) = none :=
  rfl

theorem alist_lookup_insert_same [DecidableEq k] (key : k) (val : v) (m : AList k v) :
    AList.lookup key (AList.insert key val m) = some val := by
  simp [AList.lookup, AList.insert]

theorem alist_lookup_insert_diff [DecidableEq k] {k1 k2 : k} (val : v)
    (m : AList k v) (hne : k1 ≠ k2) :
    AList.lookup k1 (AList.insert k2 val m) = AList.lookup k1 m := by
  simp [AList.lookup, AList.insert, hne]
```


# Opaque types: hiding implementation details

The `opaque` keyword makes an identifier's definition irreducible to
the elaborator.  Proofs about an `opaque` value must work through the
interface, not by unfolding the definition.

This is abstraction enforced by the type system: callers cannot depend
on the implementation details even if they tried.

```lean
-- A counter type with an opaque implementation
opaque Counter : Type := Nat

@[instance] axiom Counter.instNonempty : Nonempty Counter

noncomputable opaque Counter.zero  : Counter
noncomputable opaque Counter.incr  : Counter → Counter
noncomputable opaque Counter.value : Counter → Nat

-- The specification is stated separately as axioms about the interface:
axiom Counter.value_zero : Counter.value Counter.zero = 0
axiom Counter.value_incr : ∀ c, Counter.value (Counter.incr c) =
                                Counter.value c + 1

-- Note: in a production library, these axioms would be proved as theorems
-- using the concrete implementation.  The opaque/axiom pattern separates
-- the interface (what callers see) from the implementation.
```

# Stack: another abstract type

A stack supports push, pop, and peek, with a size operation.
The specification: push then pop returns the original element and stack.

```lean
class Stack (s : Type → Type) where
  empty : s α
  push  : α → s α → s α
  pop   : s α → Option (α × s α)
  size  : s α → Nat

class LawfulStack (s : Type → Type) extends Stack s where
  pop_empty  : pop (empty : s α) = none
  pop_push   : ∀ (x : α) (st : s α),
      pop (push x st) = some (x, st)
  size_empty : size (empty : s α) = 0
  size_push  : ∀ (x : α) (st : s α),
      size (push x st) = size st + 1

-- List implementation of Stack:
instance : Stack List where
  empty := []
  push  := List.cons
  pop   := fun
    | []      => none
    | h :: t  => some (h, t)
  size  := List.length

instance : LawfulStack List where
  pop_empty  := rfl
  pop_push   := fun _ _ => rfl
  size_empty := rfl
  size_push  := fun _ _ => rfl
```

# Representation independence

The key property of abstract types: any two implementations satisfying
the laws are _observationally equivalent_ from the caller's perspective.

This is not just informal.  Given two `LawfulDict` instances `D1` and `D2`,
any sequence of `empty`, `insert`, `lookup`, `delete` operations produces
the same `lookup` results in both.

This can be stated as a theorem schema — for each sequence of operations,
the `lookup` results agree.  We will not prove this in full generality;
stating it precisely is the skill being practiced.

# Exercises
%%%
number := false
%%%

1. Add a `size : d k v → Nat` operation to `Dict` and extend `LawfulDict`
   with laws relating `size` to `insert` and `delete`.

2. Implement `Dict` using a sorted association list.  The `lookup`
   function can binary search (well, linear search in the sorted order).
   Verify the first two laws.

3. Write the `LawfulStack` instance for a new implementation:
   ```lean -keep
   structure TwoListStack (α : Type) where
     front : List α
     back  : List α
   ```
   where `push` appends to `back` and `pop` takes from `front` (rebalancing
   by reversing `back` when `front` is empty).

4. State the _representation independence_ theorem for `Stack`:
   "for any two `LawfulStack` instances `S1` and `S2`, any program that
   only uses `push`, `pop`, `size`, and `empty` produces the same
   observable results in both."  Write this as precisely as you can in Lean.

5. Define a `Queue` type class with enqueue/dequeue operations and
   state its laws.
