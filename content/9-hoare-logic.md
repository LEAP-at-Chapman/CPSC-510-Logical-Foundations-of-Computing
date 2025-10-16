# Hoare Logic with Dafny

*Author: Alex*

## Idea

### Idea

Hoare Logic is a formal system for proving program correctness using logical assertions. It represents programs as Hoare triples:

{P} C {Q}

where (P) is the precondition, (C) the command, and (Q) the postcondition. For example:

{x = 2}\ x := x + 3\ {x = 5}

means that if (x = 2) before execution, then (x = 5) afterward.

Hoare logic forms the basis of modern verification tools like Dafny, which extend it with loop invariants, assertions, and automated theorem proving. Unlike testing, which checks correctness for specific cases, Hoare logic proves correctness for all possible executions.


## Topics

- Hoare logic foundations
- Dafny installation and setup
- Specification languages
- Program verification techniques
- Industrial applications

## Resources

- [Dafny](https://github.com/dafny-lang/dafny)
- [Dafny Tutorial](https://dafny.org/dafny/OnlineTutorial/guide)
- [Dafny Video Tutorial](https://www.youtube.com/watch?v=oLS_y842fMc)

## Exercises

*To be added*


## References

- [Northeastern University – CS2800: Logic and Computation (Spring 2023) Lecture 32: Hoare Logic](https://course.ccs.neu.edu/cs2800sp23/l32.html)

- [University of Rochester – CSC 255/455: Programming Languages (Spring 2024) Lecture 25: Introduction to Hoare Logic](https://www.cs.rochester.edu/~spai4/courses/csc-255-455/spring-2024/static/25-intro-hoare-logic.pdf)

- [University of Pennsylvania – Software Foundations, Volume 2: Programming Language Foundations Chapter: Hoare Logic](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)

- [Carnegie Mellon University – 15-654 Software Engineering (Spring 2006) Lecture Notes: Hoare Logic by Jonathan Aldrich](https://www.cs.cmu.edu/~aldrich/courses/654-sp06/notes/3-hoare-notes.pdf)

- [Alexander Kurz – Hoare Logic Example (HackMD) Worked example: Loop invariants and correctness proofs](https://hackmd.io/@alexhkurz/Hy135C2tH)

- [University of Cambridge – M.J.C. Gordon: Hoare Logic Lecture Notes All Lectures (Formal Semantics, wlp, VCG, and Separation Logic)](https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/AllLectures.pdf)
