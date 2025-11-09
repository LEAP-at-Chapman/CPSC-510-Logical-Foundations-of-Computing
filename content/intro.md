<div style="text-align: center; margin-top: 10em; margin-bottom: 10em;">

# Logical Foundations of AI

<div style="margin-top: 3em; margin-bottom: 3em; font-size: 1.2em; color: #666;">
A Textbook on Logics and Their Software Tools
</div>

<div style="margin-top: 5em; font-size: 1.1em;">
<strong>CPSC 510</strong><br>
<em>Logical Foundations of Computing</em>
</div>

<div style="margin-top: 2em; font-size: 1em; color: #666;">
Chapman University  
Fall 2025
</div>

<div style="margin-top: 4em; font-size: 0.9em; color: #888; font-style: italic;">
<em>Developed by the students and instructor of CPSC 510</em>
</div>

</div>

---

## Introduction

This book project is being developed by the class CPSC 510 Logical Foundations of Computing taught in Fall 2025 at Chapman University. 

Our approach tries to give equal weight to mathematics and to software engineering. On the one hand, we present the mathematical theory of various logics (propositional logic, predicate logic, modal logic, higher order logic, etc), on the other hand, we learn to use various software tools (MiniSat, Prolog, MiniZinc, Z3, Spin, Lean, etc). While the classes emphasize more of the theory, this book puts the tools center stage.

Each chapter should by default be devided into the following sections (subject to discussion and revision):
- Idea
- Basic Theory
- Tool (Installation, First Example, First Exercise)
- Introductory Examples
- The Landscape of Tools
- Algorithms
- Benchmark and Competitions
- **Applications in Industry**. The applications in industry section should contain clickable references to websites and research articles (as can be found on google scholar). The references should also appear in the references section of each chapter. Look for applications that have been influential and changed the direction of the field. Also look for more recent applications that point to interesting directions. In particular, find out how generative AI is changing research in formal methods. Everybody is now very much interested in how to combine (connectionist, neural network based, generative) AI with (symbolic, logic-based) AI (aka formal methods). 
- **Case Study**. The case study should be code you develop that showcases an exemplary use of the tool. The ideal case study strikes a meaningful balance between being educational/explanatory but also interesting in its own right. Ideally, a reader would look at the case study and exclaim sth like: "Oh, Nice" or "That is interesting" or "Now I understand what I can do with the tool" or "great, maybe I could do sth similar for this other use case of mine".
- **History**. Describe the main stepping stones in the evolution of ideas. See this section on [Early Work](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/2-satsolving.html#early-work) for a partial example.
- Current Development, Research Challenges, Conferences and Workshops
- References
- Suggestions for future work on the book

[Chapter 0](0-logic.md) introduces the fundamental concepts of logic that form the foundation for all subsequent chapters: validity, formal languages, decidability, satisfiability, and the duality between syntax and semantics.

[Chapter 1](1-propositional-logic.md) introduces propositional logic with an emphasis on mathematical concepts that are central to understanding applications of logic in computer science: formal language, parsing, syntax, semantics, satisfiability, proof system, soundness, completeness, decidability.

[Chapter 2](2-satsolving.md) explores SAT solving using MiniSat, focusing on semantic tableaux algorithms and their applications to satisfiability and validity checking.

[Chapter 3](3-logic-programming.md) introduces logic programming with SWI-Prolog, covering unification, resolution, and applications in search with backtracking and database querying.

[Chapter 4](4-constraint-solving.md) presents constraint solving using MiniZinc, demonstrating how constraint satisfaction problems can be solved and applied to program synthesis and automated bug fixing.

[Chapter 5](5-smt-solving.md) covers SMT (Satisfiability Modulo Theories) solving with Z3, extending beyond propositional logic to handle theories like arithmetic, arrays, and bit-vectors for program verification and model checking.

[Chapter 6](6-modal-logic.md) introduces modal logic and the SCAN algorithm for computing first-order correspondents, exploring the mathematical foundations of modalities.

[Chapter 7](7-temporal-logic.md) examines temporal logic using the Spin model checker, focusing on LTL (Linear Temporal Logic) model checking and its applications in distributed systems and protocol verification, including the famous Needham-Schroeder Key Exchange protocol.

[Chapter 8](8-epistemic-logic.md) explores epistemic logic with SMCDEL, investigating how knowledge and belief can be formally modeled and applied to social network analysis.

[Chapter 9](9-hoare-logic.md) presents Hoare logic using Dafny, demonstrating how to formally specify and verify program correctness with preconditions, postconditions, and invariants.

[Chapter 10](10-higher-order-logic.md) extends to higher-order logic in Isabelle/HOL, showing how to reason about functions as first-class objects and exploring the foundations of modern theorem proving.

[Chapter 11](11-dependent-types.md) presents dependent type theory with Lean, demonstrating how types can depend on values and enabling "proofs as programs" through the Curry-Howard correspondence.

The current suggested outline for each chapter is (see [Chapter 2](2-satsolving.md) for an example):

- Idea: What you want to tell somebody who doesnt know anything
- Basic Theory: Recap of the basic theory
- Tool: The particular tool we will discuss. How to install it. How to run a basic toy example.
- Introductory Examples
- Tools: The landscape of tools in this area
- The Algorithm: Some basic algorithms on which the tools are based
- Applications in Industry
- Case Studies



