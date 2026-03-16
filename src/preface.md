# Preface

## Why This Book

The cost of constructing formal proofs is dropping rapidly, driven by advances
in proof automation and AI-assisted verification.  As that cost approaches zero,
the barrier that has historically confined certified software to specialized
research settings disappears.  The consequence is predictable: demand for
software that carries a machine-checked correctness proof — certified software —
will explode.

The technology that makes this possible is the constructive logic proof assistant.
The leading system today is **Lean 4**.  To obtain the benefits of certified
software, one must work in the language of such a system.  That language demands
fluency in four things: data types, data values, propositions, and proofs.
This is not an exotic requirement.  It is simply the language of mathematics
made executable.

The secret path to certified software is squarely through the
**Curry-Howard correspondence**: the deep theorem that computation and proof
are the same thing viewed from two angles.  A program and its correctness proof
are not separate artifacts.  They are one.  A type-correct program in Lean 4
*is* a proof of its specification.

## What This Book Is

This draft provides a conceptual skeleton for a first undergraduate course
in computer science built on this foundation.  The course is a programming
course — but not just any programming: *certified* programming.  Specification
is integral from the outset.  Every function is accompanied by a proposition
stating what it must do, and the type checker verifies that the implementation
satisfies that proposition.  A correct program, in this setting, is by
definition a proof-carrying program.

The course is not, however, a course in proof construction.  That is the
subject of the sequel.  Here, proof construction is strategically suppressed.
Where proofs are required, they are supplied — but in all but selected cases,
proof construction is **fully automated**.  The mechanism is decidability: for
propositions in sufficiently constrained formal languages (propositional logic,
bounded arithmetic, finite equality), a decision procedure exists that either
produces a proof or reports that none can be found.  Lean 4's `decide` tactic
is that procedure.  Students learn to recognize which propositions fall within
the decidable fragment and to invoke automation confidently for those that do.

This design has a direct consequence for what students can achieve.  Anyone
versed in programming and specification in generalized predicate logic —
without expending undue cognitive effort on proof construction for most
required proofs — can write certified software.  That is the central claim of
this course, and of this book.

## What Standard Curricula Are Missing

Standard undergraduate CS curricula are unprepared for this change.  A
conventional CS1 course teaches programming in a dynamically or weakly typed
language, with correctness validated by test cases.  Test cases cover finitely
many inputs; a specification covers all of them.  The gap between the two is
exactly the gap between untested and certified.

This course closes that gap from the first week.  Types are propositions.
Programs are proofs.  The compiler is the verifier.  Students who complete
this course are not merely programmers who have learned a new language; they
are programmers who understand, at a foundational level, what it means for
software to be correct.

## The Sequel

This course provides the complete computational foundation.  Its direct sequel,
**CS2: Certified Proofs**, flips the orientation: from `Type` to `Prop`, from
computing a value to proving a proposition.  Every concept introduced here —
algebraic data types, recursion, higher-order functions, specifications,
sets, relations, type classes — ports intact to that setting.  CS2 is not a
new subject.  It is this subject, reread from the logical side of the
Curry-Howard correspondence.
