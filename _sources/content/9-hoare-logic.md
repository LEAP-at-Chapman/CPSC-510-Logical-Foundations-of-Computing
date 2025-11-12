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
- **Q** (Postcondition) - expresses what is guaranteed to be true after execution if the program halts.

This logic provides partial correctness, meaning the result will be correct if the program terminates. To achieve​​ total correctness, we must demonstrate that the program terminates. 

## Basic Theory

*To be added*

## Dafny Installation and Setup

*To be added*

## Program Verification Techniques

*To be added*

## Exercises

*To be added*

## The Landscape of Tools

*To be added*

## Benchmark and Competitions

*To be added*

## Applications in Industry

*To be added*

## Case Studies

*To be added*

## History

In 1949, Alan Turing presented his paper, “Checking a Large Routine”, which was one of the first attempts to describe how programmers could verify the correctness of their code. Throughout his paper, Turing proposed the idea of using assertion statements to explain what should be true at specific points in the program, thereby verifying its correctness. Additionally, Turing introduced the concept of a termination function as a method to ensure that the presented program eventually halts. Using a factorial program, Turing showed that logical reasoning could be applied to computer programs.

Throughout the 1960s, Robert Floyd built on Turing’s ideas by introducing the inductive assertion method, a systematic approach to proving the correctness of flowchart-based programs. Floyd proposed identifying key points in a program with logical statements called invariants, similar to the idea of assertion statements, which are both meant to show specific points during the program that must remain true throughout execution. Although the idea continued to build on Turing’s progress, this was limited to flowcharts rather than structured programming languages.

In the year 1969, C.A.R. Hoare continued to build on these ideas by introducing the Hoare triple: {P} S {Q}. This notation states that if the execution of program P begins in a state where the precondition C holds, then upon termination, the postcondition Q will hold. Although this development seemed simple, it proved to be powerful, as it created rules for statements, loops, and sequences. This notation enabled program proofs to be both structured and easier to understand due to their improved readability. The Hoare triple enabled program verification for all types of code, not just flowcharts, transforming program reasoning into a formal, language-based discipline. 

By the early 1970s, Hoare had expanded his logic to handle recursive procedures and local variables, which enabled reasoning about more complex programs. Working alongside Joseph Foley, he applied these ideas to verify the Quicksort algorithm, which was one of the first detailed proofs of correctness for a real-world program. Around the same time, Hoare began promoting the idea of programming and proving should be done simultaneously. This growing philosophy later influenced Edsger Dijkstra’s work on structured programming and program derivation, transforming Hoare Logic into a guide for creating verified software instead of verifying it after the fact.

The development of Hoare Logic established a foundation in computer science by shifting the perspective from viewing programs as sequences of commands to viewing them as logical systems that can be mathematically analyzed. Building upon Turing’s conceptual groundwork, refining Floyd’s formalization, and realizing Hoare’s framework, this lineage transformed programming into a science of correctness. To this day, Hoare Logic remains a foundational method of verification, and it also serves as a symbol of the connection between logic, mathematics, and computation.


## Current Development, Research Challenges, Conferences and Workshops

*To be added*

## Suggestions for future work on the book

*To be added*

## Industrial Applications

Using preconditions, postconditions, and invariants, as Hoare Logic showcases, this reasoning is now embedded in modern tools and workflows. These principles have now influenced every layer of software reliability. Here are a few examples of how Hoare Logic has been implemented in industry:

- **Safety-Critical Systems:**
Hoare Logic enables formal verification of systems where failure is unacceptable, such as in the aerospace and medical fields. Engineers ensure that autopilot control, satellite guidance, and pacemaker timing behave safely under all possible conditions by proving correctness through preconditions, postconditions, and invariants.


- **Security and Cryptography:**
Used to prove that confidential data cannot leak and that cryptographic algorithms behave exactly as specified. Using Hoare Logic, reasoning supports formal proofs of non-interference, access control, and side-channel resistance in encryption and authentication systems.


- **Static Analysis and Software Quality:**
Modern tools such as Facebook Infer and Microsoft Code Contracts apply Hoare Logic-based reasoning to automatically detect bugs, memory leaks, and logic errors before runtime.


- **Industrial Verification Pipelines:**
Frameworks like Dafny, Frama-C, SPARK Ada, and Coq use Hoare Logic within large organizations such as Microsoft, Airbus, and AWS. They verify encryption libraries, avionics software, and distributed systems, combining enhanced security with practical reliability.

## Resources

- [Dafny](https://github.com/dafny-lang/dafny)
- [Dafny Tutorial](https://dafny.org/dafny/OnlineTutorial/guide)
- [Dafny Video Tutorial](https://www.youtube.com/watch?v=oLS_y842fMc)

## References

- [Northeastern University – CS2800: Logic and Computation (Spring 2023) Lecture 32: Hoare Logic](https://course.ccs.neu.edu/cs2800sp23/l32.html)

- [University of Rochester – CSC 255/455: Programming Languages (Spring 2024) Lecture 25: Introduction to Hoare Logic](https://www.cs.rochester.edu/~spai4/courses/csc-255-455/spring-2024/static/25-intro-hoare-logic.pdf)

- [University of Pennsylvania – Software Foundations, Volume 2: Programming Language Foundations Chapter: Hoare Logic](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)

- [Carnegie Mellon University – 15-654 Software Engineering (Spring 2006) Lecture Notes: Hoare Logic by Jonathan Aldrich](https://www.cs.cmu.edu/~aldrich/courses/654-sp06/notes/3-hoare-notes.pdf)

- [Alexander Kurz – Hoare Logic Example (HackMD) Worked example: Loop invariants and correctness proofs](https://hackmd.io/@alexhkurz/Hy135C2tH)

- [University of Cambridge – M.J.C. Gordon: Hoare Logic Lecture Notes All Lectures (Formal Semantics, wlp, VCG, and Separation Logic)](https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/AllLectures.pdf)

- [Intro. to the Hoare Triple (Discrete Math Tutorial) - Validity, Calculating Precondition, Explained.](https://www.youtube.com/watch?v=-Bs2Uy3zGsw)

- [Fifty years of Hoare’s logic](https://ir.cwi.nl/pub/29146/29146.pdf)
