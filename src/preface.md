# Preface

## To Contact the Author

Email Kevin Sullivan at [sullivan.kevinj at gmail.com](mailto:sullivan.kevinj@gmail.com).

## Why This Book

The cost of constructing formal proofs even in specialized and deeply
mathematical and sofware domains is collapsing, driven by advances in
proof automation and AI-assisted verification.  As these costs drop, the
impracticality barrier that has historically confined certified software
to research and high-criticality settings crumbles.

As costs drop, demand soars.  Software that carries a machine-checked
correctness proof — certified software — is on the verge of becoming a
mainstream engineering expectation. Attention can finally shift to where
it's needed: **understanding** what to specify and how to specify it in the
first place.

The technology that makes this possible is the constructive logic proof
assistant. The leading system today is **Lean 4**.  To obtain the benefits
of certified software, one must however work in the programming language
of such a system. That in turn demands fluency in data/functions types and
values, and in logical/mathematical propositions and their proofs values.
The reward for gaining fluency in predicate logic and mathematics far more
broadly, is that it is now made executable.

A thesis underlying the structuring of this course skeleton, hardly new,
is learning to program with those types on the computational side of the
Curry Howard correspondence will deeply prepare students to transition to
the second (forthcoming) course skeleton: Computation and proof are the
same thing viewed from two angles.  A program and its correctness proof
are not separate artifacts.  They are one.  A type-correct program in Lean
4 *is* a proof of its specification.

CS undergraduate curricula today are generally far from ready for the
coming (I expect) surge in demand for certified software engineering to
include certified programming.

This document is a hypothesized conceptual skeleton for a course where
specification and programming are one from day one; proof-construction
is not taught or expected of students; but where automated construction
of proofs of decidable propositions (itself a topic) is systematic and routine, allowing
students to focus attention on the *language* of specification not
on explicit proofs.

## What This Book Is

The course is squarely intended and formulated as a *programming* course:
not just any programming but a course in *certified* programming. In this
course, specification and the routine treatment of proofs as data, are
integral from the outset.  Every function is accompanied by a proposition
stating what it must do. The type checker verifies that the implementation
provided by the student satisfies that proposition.  A correct program, in
this setting, is by definition a proof-carrying program.

We further emphasize that the course is unique in surfacing specification
while submersing proof construction, not by omitting it, but by leveraging
automated proof construction in Lean to relieve students of having to prove
anything themselves.

The mechanism is decidability: for propositions in sufficiently constrained
formal languages (propositional logic, bounded arithmetic, finite equality),
a decision procedure exists that either produces a proof or reports that none
can be found.  Lean 4's `decide` term is that procedure.  Students learn to
recognize which propositions fall within the decidable fragment and to invoke
automation confidently for those that do.

## Intellectual Foundations

This curriculum stands on the shoulders of two landmark works in programming
education, and is informed by a third from the proof-assistant tradition.

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
not a capstone curiosity, but an explanation that the whole course was
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

Another more distant reference point — noted here to clarify what this course is *not* — is
**Software Foundations** by Benjamin C. Pierce et al.[^sf]  Software Foundations is
the landmark text for machine-checked reasoning in a proof assistant (Coq).  It is not, however, an introductory programming
course: it is pitched at the graduate level, it presupposes substantial fluency in the very
functional-programming concepts this course teaches, and proof construction is its
central activity.  This course can be understood as the missing prerequisite — the CS1 that prepares students to engage with Software Foundations (or its Lean equivalents) in a subsequent course.

[^sf]: Pierce, B. C., et al.
*Software Foundations*, vol. 1: Logical Foundations.
Electronic textbook, 2024. [softwarefoundations.cis.upenn.edu](https://softwarefoundations.cis.upenn.edu)

## What's Novel

Novel features of this curriculum, no direct precedent in existing CS1
course proposal, to our knowledge, include the following:

1. **Machine-checked specifications at CS1 level.**  Existing courses that
   achieve machine-checked correctness — **Software Foundations** (Pierce et al.)
   and **Programming Language Foundations in Agda** (PLFA) — do so at the
   graduate level.  This course achieves the same immediate correctness
   guarantee at CS1 level by automating proof construction wherever possible,
   so that *specification — not proof — is the primary logical focus*.

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
   The architecture of the sequel, indeed of natural deducation proof,
   is the laid down for students by the overall structure of this course.

## The Sequel

The sequel,**CS2: Certified Proofs**, flips the orientation: from `Type`
to `Prop`, from computing a value to proving a proposition.  Each concept
introduced here in the realm of *programming* — algebraic data types,
recursion, higher-order functions, specifications, sets, relations, type
classes — ports intact to that setting.  CS2 is thus not a new subject but
the same, reread from the logical side of the Curry-Howard correspondence.

## What's Missing Here

In its current form this book is fairly bare bones, not particularly warm
and fuzzy. It's lacking in examples of applications that are fun, linked to
real work domains, graphical or interactive, etc. Further skinning of this
kind would be helpful. For now its bare bones character makes discussing the
core content easier, perhaps.

Realistically, the amount of material covered is likely too much except for
strong students. Subsetting would be needed. Numerous topics could be elided
or shortened considerably. How to distill this integral course into one that
has the same effect but really fits comfortably into a single semester is a
good question to address.

## Contact

If you're interested in discussing these materials or CS1 2030 more generally,
feel free to drop a line. My personal email is [sullivan.kevinj at gmail.com](mailto:sullivan.kevinj@gmail.com).
