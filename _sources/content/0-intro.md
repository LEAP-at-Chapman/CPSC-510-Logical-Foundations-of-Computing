# The Book

The first draft of this book project is being developed by the class CPSC 510 Logical Foundations of Computing taught in Fall 2025 at Chapman University. 

Our approach tries to give equal weight to mathematics and to software engineering. On the one hand, we present the mathematical theory of various logics (propositional logic, predicate logic, modal logic, higher order logic, etc), on the other hand, we learn to use various software tools (MiniSat, Prolog, MiniZinc, Z3, Spin, Lean, etc). While the lectures emphasize more of the theory, this book puts the tools center stage.

## Suggested Table of Contents for a Typical Chapter

Each chapter should by default be devided into the following sections (subject to discussion and revision):
- **Idea**: Each tool is based on a logic. Typically there is only a small number of big ideas at the origin of each tool.
- **Basic Theory**: Just enough theory to understand better how each logic provides the technology used to implement the big idea at the origin of the software tool.
- **Tool**: One advantage of learning logic via tools is that one can get hands-on eperience before even digging into the mathematics. This section will be a guide to first steps with the tool (Installation, First Example, First Exercise)
- **Introductory Examples**: The purpose of this section is to illustrate the big idea as well as the basic theory. Given this constraint, the examples should be as easy as possible.
- **The Landscape of Tools**: A big idea together with the basic theory typically gives rise to a range of tools (such as satsolvers, model checkers, interactive theorem provers, etc). While each chapter will emphasize just one of these tools, here is the space to lay out the landscape of tools.
- **Algorithms**: The basic theory needs to be implemented efficiently. This section concentrates on the algorithms that run the tool. 
- **Typical Use Cases**: Each software tool has its own use cases. This section describes typical use cases, including algorithms that can be implemented more efficiently or more easily with the support of the tool in question. 
- **Benchmarks and Competitions**: Not in all but in many cases, progress in formal methods is driven by benchmarks and competitions. Find out more what is happening on this side.
- **Applications in Industry**. The applications in industry section should contain clickable references to websites and research articles (as can be found on google scholar). The references should also appear in the references section of each chapter. Look for applications that have been influential and changed the direction of the field. Also look for more recent applications that point to interesting directions. In particular, find out how generative AI is changing research in formal methods. Everybody is now very much interested in how to combine (connectionist, neural network based, generative) AI with (symbolic, logic-based) AI (aka formal methods). 
- **Case Study**. The case study should be code you develop that showcases an exemplary use of the tool. The ideal case study strikes a meaningful balance between being educational/explanatory but also interesting in its own right. Ideally, a reader would look at the case study and exclaim sth like: "Oh, Nice" or "That is interesting" or "Now I understand what I can do with the tool" or "great, maybe I could do sth similar for this other use case of mine".
- **History**. Describe the main stepping stones in the evolution of ideas, algorithms and industrial application. See this section on [Early Work](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/2-satsolving.html#early-work) for a partial example on the development of the early work on SAT-solvers.
- **Formal Methods and AI**: Under various labels such as neurosymbolic computing, all areas of formal methods are now integrating the recent advances in generative AI into their tools. Moreover, completely new tools are being built. One idea that is finding its way into many tools is to build tools based on guess (gen AI) and verify (symbolic AI).
- **Current Developments**: From your point of view and your literature review of the area, what do  you think are the current research challenges and at which conferences, workshops, venues should one look to stay on top of the most recent developments?
- **References**: We agreed on the format described in [how to cite](how-to-cite.md).
- **Future Work**: I have some general ideas below in the section "Project Ideas for 2026". More specifically, from your own point of view, what work would you like to see from somebody who would want to extend your chapter in the future?
- **Contributors**: Initial author (the student responsible for the chapter), peer reviewers, and other contributors with their contributions.

## Preliminary Table of Contents of the Book

**Introductions**:

- [A Short Intro to Logic](0-logic.md) introduces the fundamental concepts of logic that form the foundation for all subsequent chapters: validity, formal languages, decidability, satisfiability, and the duality between syntax and semantics.
- [Propositional Logic](1-propositional-logic.md) introduces propositional logic with an emphasis on mathematical concepts that are central to understanding applications of logic in computer science: formal language, parsing, syntax, semantics, satisfiability, proof system, soundness, completeness, decidability.
- [Modal Logic](6-modal-logic.md) introduces modal logic and the SCAN algorithm for computing first-order correspondents, exploring the mathematical foundations of modalities.

**Logics and Tools**:

- [SAT solving with MiniSat](2-satsolving.md) explores SAT solving using MiniSat, focusing on semantic tableaux algorithms and their applications to satisfiability and validity checking.
- [Logic Programming with Prolog](3-logic-programming.md) introduces logic programming with SWI-Prolog, covering unification, resolution, and applications in search with backtracking and database querying.
- [Constraints with MiniZinc](4-constraint-solving.md) presents constraint solving using MiniZinc, demonstrating how constraint satisfaction problems can be solved and applied to program synthesis and automated bug fixing.
- [SMT Solving and Z3](5-smt-solving.md) covers SMT (Satisfiability Modulo Theories) solving with Z3, extending beyond propositional logic to handle theories like arithmetic, arrays, and bit-vectors for program verification and model checking.
- [Temporal Logic with Spin](7-temporal-logic.md) examines temporal logic using the Spin model checker, focusing on LTL (Linear Temporal Logic) model checking and its applications in distributed systems and protocol verification, including the famous Needham-Schroeder Key Exchange protocol.
- [Epistemic Logic with SMCDEL](8-epistemic-logic.md) explores epistemic logic with SMCDEL, investigating how knowledge and belief can be formally modeled and applied to social network analysis.
- [Hoare Logic with Dafny](9-hoare-logic.md) presents Hoare logic using Dafny, demonstrating how to formally specify and verify program correctness with preconditions, postconditions, and invariants.
- [Higher-Order Logic with Isabelle](10-higher-order-logic.md) extends to higher-order logic in Isabelle/HOL, showing how to reason about functions as first-class objects and exploring the foundations of modern theorem proving.
- [Type Theory with Lean](11-dependent-types.md) presents dependent type theory with Lean, demonstrating how types can depend on values and enabling "proofs as programs" through the Curry-Howard correspondence.

## Ideas for 2026

- Turn this book from one one "Logical Foundations of Software Engineering" into a book on "Formal Methods and AI"
- Give students a choice between adding a new chapter or doing a project. 
  - Projects would apply a logic-based formal method to some engineering problem. 
  - I would be particularly interested in projects that combine formal methods which generative AI.
  - A great way to learn is to implement a classic algorithm from scratch. A project in this vein could be a simple from-scratch prototype implementation of a tool (eg a Prolog interpreter). The focus would be on simplicity and the educational value.
  - A new chapter would present a logic, a formal method, a software tool. For example:
    - First-order theorem proving: (Vampire, Prover9, ...)
    - Knwoledge Representation, Semantic Web, Ontologies, Description Logics, ... [OntoUML](https://ontouml.org/) ... 
- ... tbc ...


