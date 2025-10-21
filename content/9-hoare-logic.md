# Hoare Logic with Dafny

*Author: Alex*

## Idea

Hoare Logic introduced the idea that we can reason about programs the same way we reason about mathematical proofs by introducing program verification. Instead of observing program behavior through test cases, we showcase what a program should do in logical form, and then prove that it does so. At its core lies the Hoare triple:

[{P}; C; {Q}]

This notation captures the relationship between a precondition (P), a command (C), and a postcondition (Q). This notation reads as:

<p align="center"> If the execution of program P begins in a state where the precondition C holds, then upon termination, the postcondition Q will hold. </p>

Each component plays a specific role:
- **P** (Precondition) - describes the assumptions or required state before execution.
- **C** (Command) - represents a piece of the program
- **Q** (Postcondition)



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

- [Intro. to the Hoare Triple (Discrete Math Tutorial) - Validity, Calculating Precondition, Explained.](https://www.youtube.com/watch?v=-Bs2Uy3zGsw)
