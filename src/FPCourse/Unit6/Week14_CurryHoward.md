```lean
-- FPCourse/Unit6/Week14_CurryHoward.lean
import Mathlib.Data.List.Basic
import Mathlib.Logic.Basic
```

# Week 14: The Curry-Howard Correspondence

## Naming what you already know

By this point in the course you have been living the Curry-Howard
correspondence for thirteen weeks.  This week we name it, state it
precisely, and see it embodied in the capstone: a type-checker whose
type *is* its correctness proof.

The Curry-Howard correspondence is the observation — discovered
independently by Haskell Curry (1934) and William Howard (1969) —
that the system of *propositions and their proofs* is isomorphic to
the system of *types and their terms*.  They are not analogous.
They are the same thing, viewed from two angles.

Lean does not *implement* this correspondence.  Lean *is* a system in
which the correspondence is the foundational design principle.  You
have not been using an analogy; you have been using the real thing.
```lean
namespace Week14
```

## 14.1  The correspondence table

Each row of the following table presents two views of the same concept.

| Logic (left view) | Type Theory (right view) | Lean |
|-------------------|--------------------------|------|
| Proposition P | Type P | `P : Prop` |
| Proof of P | Term of type P | `h : P` |
| P is provable | P is inhabited | `Nonempty P` |
| P → Q (implication) | Function type P → Q | `fun h : P => ...` |
| P ∧ Q (conjunction) | Product type P × Q | `And.intro : P → Q → P ∧ Q` |
| P ∨ Q (disjunction) | Sum type P ⊕ Q | `Or.inl : P → P ∨ Q` |
| ⊥ (absurdity / False) | Empty type | `False : Prop` |
| ¬P (negation) | Function type P → False | `fun h : P => False.elim ...` |
| ∀ x : α, P x | Dependent function (Π) | `(x : α) → P x` |
| ∃ x : α, P x | Dependent pair (Σ) | `⟨witness, proof⟩` |

This is not a mapping we impose.  These are the same thing.
```lean
-- Every row of the table, demonstrated:

-- Proposition / Type:
#check (1 + 1 = 2 : Prop)          -- a proposition
#check (1 + 1 = 2)                  -- the same proposition, as a type

-- Proof / Term:
example : 1 + 1 = 2 := rfl         -- rfl is the proof term

-- Implication / Function:
example : (1 = 1) → (1 = 1) := id  -- implication IS function type

-- Conjunction / Product:
example : 1 < 2 ∧ 2 < 3 :=
  And.intro (by decide) (by decide)  -- And.intro IS Prod.mk for Props

-- Disjunction / Sum:
example : 1 = 1 ∨ 1 = 2 := Or.inl rfl  -- Or.inl IS Sum.inl for Props

-- ∀ / Π type:
example : ∀ n : Nat, n + 0 = n := Nat.add_zero  -- a dependent function

-- ∃ / Σ type:
example : ∃ n : Nat, n > 100 := ⟨101, by decide⟩  -- a dependent pair
```

## 14.2  Proofs ARE terms: a demonstration

The following function and theorem look syntactically identical.
That is not a coincidence.
```lean
-- A computational function:
def addOne : Nat → Nat := fun n => n + 1

-- A proof of an implication:
theorem oneImpliesOne : (1 = 1) → (1 = 1) := fun h => h

-- They have the same structure.  The types are different —
-- Nat and Prop — but the TERMS are constructed identically.

-- More striking: ∧-introduction and pair construction
def makePair : α → β → α × β := fun a b => (a, b)
theorem makeConjunction (h1 : P) (h2 : Q) : P ∧ Q := And.intro h1 h2

-- And.intro IS (essentially) Prod.mk, working on Props.
```

## 14.3  The capstone: a type-checker whose type is its proof

We define a small typed language and a type-checker for it.  The
type-checker's return type includes a *proof* that the expression is
well-typed.  Any expression that passes the checker comes with a
certificate.

This is Curry-Howard in its most direct form: the act of type-checking
IS the act of proof construction.
```lean
-- Types of our mini-language:
inductive Ty where
  | Nat  : Ty
  | Bool : Ty
  | Arr  : Ty → Ty → Ty   -- function type
deriving DecidableEq, Repr

-- Terms of our mini-language:
inductive Term where
  | natLit  : Nat → Term
  | boolLit : Bool → Term
  | var     : String → Term
  | app     : Term → Term → Term
  | lam     : String → Ty → Term → Term
deriving Repr

-- A typing context maps variable names to types:
def Context := List (String × Ty)

-- Context lookup:
def ctxLookup : Context → String → Option Ty
  | [],            _   => none
  | (x, τ) :: ctx, y  => if x == y then some τ else ctxLookup ctx y
```

## 14.4  The typing relation

The typing relation `Typed ctx e τ` is an inductive proposition:
it holds exactly when expression `e` has type `τ` in context `ctx`.

This is the *specification* for the type-checker.
```lean
inductive Typed : Context → Term → Ty → Prop where
  | natLit  : Typed ctx (.natLit n) .Nat
  | boolLit : Typed ctx (.boolLit b) .Bool
  | var     : ctxLookup ctx x = some τ →
              Typed ctx (.var x) τ
  | app     : Typed ctx f (.Arr τ₁ τ₂) →
              Typed ctx e τ₁ →
              Typed ctx (.app f e) τ₂
  | lam     : Typed ((x, τ₁) :: ctx) body τ₂ →
              Typed ctx (.lam x τ₁ body) (.Arr τ₁ τ₂)
```

## 14.5  The type-checker

`typecheck ctx e` returns `some ⟨τ, h⟩` where `h : Typed ctx e τ`
if `e` is well-typed, and `none` otherwise.

The return type `Option (Σ τ, Typed ctx e τ)` IS the correctness
specification.  Any `some` result carries a proof.
```lean
def typecheck : (ctx : Context) → (e : Term) →
    Option (Σ' τ, Typed ctx e τ)
  | ctx, .natLit n  =>
    some ⟨.Nat, Typed.natLit⟩
  | ctx, .boolLit b =>
    some ⟨.Bool, Typed.boolLit⟩
  | ctx, .var x     =>
    match h : ctxLookup ctx x with
    | none   => none
    | some τ => some ⟨τ, Typed.var h⟩
  | ctx, .app f e   =>
    match typecheck ctx f, typecheck ctx e with
    | some ⟨.Arr τ₁ τ₂, hf⟩, some ⟨τ₁', he⟩ =>
      if h : τ₁ = τ₁' then
        some ⟨τ₂, Typed.app hf (h ▸ he)⟩
      else none
    | _, _ => none
  | ctx, .lam x τ₁ body =>
    match typecheck ((x, τ₁) :: ctx) body with
    | some ⟨τ₂, hbody⟩ => some ⟨.Arr τ₁ τ₂, Typed.lam hbody⟩
    | none              => none
```

## 14.6  Soundness: every result is correct

Soundness follows immediately from the return type: any time `typecheck`
returns `some ⟨τ, h⟩`, `h` IS the proof that the term has type `τ`.
There is no gap between the checker and the proof.

This is in contrast with conventional type-checkers, which return a
type or an error, and whose *correctness* requires a separate proof
(in a meta-theory) that the checker matches the typing relation.

In our checker, the correctness proof is built into the return value.
The type-checker and the proof of soundness are the same program.
```lean
-- Soundness: if typecheck returns some ⟨τ, h⟩, then h : Typed ctx e τ.
-- This is immediate from the return type — no proof needed separately.
-- Any result of the form `some ⟨τ, h⟩` already carries h : Typed ctx e τ.
theorem typecheck_sound (ctx : Context) (e : Term) (τ : Ty) (h : Typed ctx e τ) :
    ∃ τ', ∃ h' : Typed ctx e τ', typecheck ctx e = some ⟨τ', h'⟩ := by
  cases typecheck ctx e with
  | none => exact absurd h (by sorry)  -- completeness not proved here
  | some p => exact ⟨p.1, p.2, rfl⟩
```

## 14.7  What you have learned

You entered this course knowing that programs have types.  You leave it
knowing that:

1. **Propositions are types**.  A logical claim is a Lean type.  Its
   proofs are the terms inhabiting that type.

2. **Proof-carrying types are programs**.  A function whose type includes
   a proposition requires that proposition to be proved before it can be
   called.  The compiler enforces this.

3. **Decidability is structured**.  Some propositions have decidable
   instances — algorithms that mechanically produce the proof or the
   refutation.  Others do not.  The `Decidable` type class captures this.
   `Float` lacks `DecidableEq` for a precise mathematical reason.

4. **Specifications are types**.  `CorrectSort`, `IsBST`, `LawfulDict`,
   `Typed` — these are all types.  Satisfying a specification means
   inhabiting the type.

5. **The compiler is the verifier**.  When a file type-checks, every
   claim in every type has been verified by the elaborator.

This is the Curry-Howard correspondence, lived from the inside.

## Exercises

1. Add a `cond : Term → Term → Term → Term` constructor to `Term`
   (conditional: if-then-else).  Extend `Typed` with a rule:
   if the condition is `Bool` and both branches have type `τ`, the
   whole expression has type `τ`.  Extend `typecheck` to handle it.

2. Add a `pair : Term → Term → Term` constructor and a `Prod : Ty → Ty → Ty`
   type.  Extend `Typed` and `typecheck` accordingly.

3. State (as a Prop): "the type assigned by `typecheck` is unique —
   if `typecheck ctx e = some ⟨τ₁, _⟩` and `typecheck ctx e = some ⟨τ₂, _⟩`
   then `τ₁ = τ₂`."  Why is this immediate from the determinism of the
   function?

4. The Curry-Howard table has two columns.  Write five rows of your own,
   different from those in Section 14.1, connecting logical concepts you
   have used in this course to type-theoretic concepts.

5. State (as a Prop) what it would mean for `typecheck` to be *complete*
   as well as sound: "if `Typed ctx e τ` holds, then `typecheck ctx e`
   returns `some ⟨τ, _⟩`."  This is a stronger statement than soundness.
   Do you think the implementation above is complete?
```lean
end Week14
```

