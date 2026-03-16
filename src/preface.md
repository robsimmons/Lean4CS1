# Preface

## Why This Book

The cost of constructing formal proofs is dropping rapidly, driven by advances
in proof automation and AI-assisted verification.  As that cost approaches zero,
the barrier that has historically confined certified software to research and
high-criticality settings diminishes; and as costs drop precipitously, demand
will increase rapidly.  Software that carries a machine-checked correctness
proof — certified software — is on the verge of becoming a mainstream
engineering expectation.

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

Today, however, CS undergraduate curricula are arguably not ready for this
change.  This document is a proposed conceptual skeleton for a
*specification- and programming-focused, but not proof-construction-focused*
first course for potential or actual CS majors.

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
produces a proof or reports that none can be found.  Lean 4's `decide` term
is that procedure.  Students learn to recognize which propositions fall within
the decidable fragment and to invoke automation confidently for those that do.

## Intellectual Foundations

This curriculum stands on the shoulders of two landmark works in programming
education.

The primary pedagogical influence is **How to Design Programs (HtDP)** by
Matthias Felleisen, Robert Bruce Findler, Matthew Flatt, and Shriram
Krishnamurthi (MIT Press, 2nd ed., 2018; freely available at
[htdp.org](https://htdp.org)).[^htdp]  HtDP introduced the *design recipe*:
a systematic, step-by-step methodology in which data definitions drive
function structure, signatures and purpose statements precede code, and
examples serve simultaneously as specification and automated tests.  This
course adopts that discipline directly — description, signature, specification,
examples, implementation, verification — but replaces HtDP's informal
type-comment signatures and dynamic `check-expect` tests with machine-checked
types and `theorem` statements verified by the Lean kernel.  Where HtDP's
specifications are comments, this course's specifications are proofs.

A more distant influence is **Structure and Interpretation of Computer
Programs (SICP)** by Harold Abelson, Gerald Jay Sussman, and Julie Sussman
(MIT Press, 2nd ed., 1996; freely available via MIT OpenCourseWare).[^sicp]
SICP's ambition — to reveal computation and language as a single unified
subject, culminating in the metacircular evaluator — resonates here.
Week 14's treatment of the Curry-Howard correspondence plays the same role:
not a capstone curiosity, but the revelation that the entire course was
*already* doing logic.  SICP's influence on the sequencing of abstraction
(higher-order functions introduced to eliminate duplication, not as a
language feature) is also present, though this course follows HtDP's
more graduated approach.

[^htdp]: Felleisen, M., Findler, R. B., Flatt, M., & Krishnamurthi, S.
*How to Design Programs: An Introduction to Programming and Computing*,
2nd ed. MIT Press, 2018. [htdp.org](https://htdp.org)

[^sicp]: Abelson, H., Sussman, G. J., & Sussman, J.
*Structure and Interpretation of Computer Programs*, 2nd ed.
MIT Press, 1996. [mitpress.mit.edu](https://mitpress.mit.edu/9780262510875/)

## What Is Novel

Several features of this curriculum have, to our knowledge, no direct precedent
in existing CS1 courses:

1. **Machine-checked specifications at CS1 level.**  Courses in formal
   verification (Software Foundations, PLFA) achieve machine-checked
   correctness, but at graduate level and with proof construction as the
   central skill.  This course achieves the same correctness guarantee at
   CS1 level by automating proof construction wherever possible.

2. **Decidability as explicit curriculum content.**  The question of *when*
   automation works — and why it provably cannot work for certain propositions
   (unbounded quantification, floating-point equality) — is named, taught,
   and assessed.  Students graduate with a principled understanding of the
   automation boundary, not merely a collection of tactics.

3. **The data type suite as a covert Curry-Howard curriculum.**  The core
   types — `→`, `×`, `⊕`, `Unit`, `Empty`, `∀`, `∃` — were chosen precisely
   because they are both deeply fundamental programming types *and*, from
   another perspective, precisely the logical connectives of the generalized
   predicate logic of Lean.  Week 14 names what students have been doing all
   along.  The revelation is structural, not incidental.

4. **The `#eval` → `rfl` → `decide` → `theorem` verification ladder.**
   Students experience concretely what it means for verification strength
   to increase, from dynamic spot-checking to universally-quantified,
   kernel-verified proofs.

5. **An explicit two-course arc.**  The course is designed as the
   computational half of a pair.  CS2: Certified Proofs flips the
   orientation from `Type` to `Prop`; every concept ports exactly.
   The architecture of the sequel is visible in the structure of this course.

## Foundation for What Comes Next

This course is designed to establish a *complete* foundation in the
computational and programming realm for all of the intuitions needed to
rapidly grasp what comes in the logical realm.  Every inference rule in
predicate logic has a computational counterpart already encountered here:
implication introduction is function abstraction; conjunction introduction
is pair construction; disjunction introduction is sum injection; universal
generalization is polymorphic function abstraction; existential introduction
is dependent pair construction.  When a student in CS2 sees the inference
rule for `∧`-introduction, they have already written `And.intro` dozens of
times — they called it building a product type.  The move from CS1 to CS2
is not a change of subject.  It is a change of vocabulary for the same
underlying structure.

## The Sequel

This course provides the complete computational foundation.  Its direct sequel,
**CS2: Certified Proofs**, flips the orientation: from `Type` to `Prop`, from
computing a value to proving a proposition.  Every concept introduced here —
algebraic data types, recursion, higher-order functions, specifications,
sets, relations, type classes — ports intact to that setting.  CS2 is not a
new subject.  It is this subject, reread from the logical side of the
Curry-Howard correspondence.
