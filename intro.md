# Introduction

This book project is being developed by the class CPSC 510 Logical Foundations of Computing taught in Fall 2025 at Chapman University. 

Our approach tries to give equal weight to mathematics and to software engineering. On the one hand, we present the mathematical theory of various logics (propositional logic, predicate logic, modal logic, higher order logic, etc), on the other hand, we learn to use various software tools (MiniSat, Prolog, MiniZinc, Z3, Spin, Lean, etc). While the classes emphasize more of the theory, this book puts the tools center stage.

For an outline of the topics see [the overview](overview.md).

Each chapter should by default be devided into the following sections (subject to discussion and revision):
- Idea
- Basic Theory
- Tool (Installation, First Example, First Exercise)
- Introductory Examples
- The Landscape of Tools
- Algorithms
- Benchmark and Competitions
- Applications in Industry
- Case Studies
- History
- Current Development, Research Challenges, Conferences and Workshops
- References

[Chapter 1](content/1-propositional-logic.md) introduces propositional logic with an emphasis on mathematical concepts that are central to understanding applications of logic in computer science: formal language, parsing, syntax, semantics, satisfiability, proof system, soundness, completeness, decidability.

[Chapter 2](content/2-satsolving.md) explores SAT solving using MiniSat, focusing on semantic tableaux algorithms and their applications to satisfiability and validity checking.

[Chapter 3](content/3-logic-programming.md) introduces logic programming with SWI-Prolog, covering unification, resolution, and applications in search with backtracking and database querying.

[Chapter 4](content/4-constraint-solving.md) presents constraint solving using MiniZinc, demonstrating how constraint satisfaction problems can be solved and applied to program synthesis and automated bug fixing.

[Chapter 5](content/5-smt-solving.md) covers SMT (Satisfiability Modulo Theories) solving with Z3, extending beyond propositional logic to handle theories like arithmetic, arrays, and bit-vectors for program verification and model checking.

[Chapter 6](content/6-modal-logic.md) introduces modal logic and the SCAN algorithm for computing first-order correspondents, exploring the mathematical foundations of modalities.

[Chapter 7](content/7-temporal-logic.md) examines temporal logic using the Spin model checker, focusing on LTL (Linear Temporal Logic) model checking and its applications in distributed systems and protocol verification, including the famous Needham-Schroeder Key Exchange protocol.

[Chapter 8](content/8-epistemic-logic.md) explores epistemic logic with SMCDEL, investigating how knowledge and belief can be formally modeled and applied to social network analysis.

[Chapter 9](content/9-hoare-logic.md) presents Hoare logic using Dafny, demonstrating how to formally specify and verify program correctness with preconditions, postconditions, and invariants.

[Chapter 10](content/10-higher-order-logic.md) extends to higher-order logic in Isabelle/HOL, showing how to reason about functions as first-class objects and exploring the foundations of modern theorem proving.

[Chapter 11](content/11-dependent-types.md) presents dependent type theory with Lean, demonstrating how types can depend on values and enabling "proofs as programs" through the Curry-Howard correspondence.

The current suggested outline for each chapter is (see [satsolving.md](content/2-satsolving.md2-) for an example):

- Idea: What you want to tell somebody who doesnt know anything
- Basic Theory: Recap of the basic theory
- Tool: The particular tool we will discuss. How to install it. How to run a basic toy example.
- Introductory Examples
- Tools: The landscape of tools in this area
- The Algorithm: Some basic algorithms on which the tools are based
- Applications in Industry
- Case Studies



