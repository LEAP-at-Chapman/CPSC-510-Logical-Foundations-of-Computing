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

## Dafny Installation and Setup

*To be added*

## Program Verification Techniques

*To be added*

## Exercises

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
Frameworks like Dafny, Frama-C, SPARK Ada, and Coq operationalize Hoare Logic within large organizations such as Microsoft, Airbus, and AWS. They verify encryption libraries, avionics software, and distributed systems, combining enhanced security with practical reliability.
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
