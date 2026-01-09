

# The Book

The first draft of this book project is being developed by the class CPSC 510 Logical Foundations of Computing taught in Fall 2025 at Chapman University. 

Our approach tries to give equal weight to mathematics and to software engineering. On the one hand, we present the mathematical theory of various logics (propositional logic, predicate logic, modal logic, higher order logic, etc), on the other hand, we learn to use various software tools (MiniSat, Prolog, MiniZinc, Z3, Spin, Lean, etc). While the lectures emphasize more of the theory, this book puts the tools center stage.

(suggested-table-of-contents-for-a-typical-chapter)=
## Suggested Table of Contents for a Typical Chapter

Each chapter should by default be divided into the following sections (subject to discussion and revision):
- **Idea**: Each tool is based on a logic. Typically there is only a small number of big ideas at the origin of each tool.
- **Basic Theory**: Just enough theory to understand better how each logic provides the technology used to implement the big idea at the origin of the software tool.
- **Tool**: One advantage of learning logic via tools is that one can get hands-on experience before even digging into the mathematics. This section will be a guide to first steps with the tool (Installation, First Example, First Exercise)
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

- [A Short Intro to Logic](0-2-intro-logic.md) introduces the fundamental concepts of logic that form the foundation for all subsequent chapters: validity, formal languages, decidability, satisfiability, and the duality between syntax and semantics.
- [Propositional Logic](0-3-intro-propositional-logic.md) introduces propositional logic with an emphasis on mathematical concepts that are central to understanding applications of logic in computer science: formal language, parsing, syntax, semantics, satisfiability, proof system, soundness, completeness, decidability.
- [Modal Logic](0-4-intro-modal-logic.md) introduces modal logic and the SCAN algorithm for computing first-order correspondents, exploring the mathematical foundations of modalities.

**Logics and Tools**:

- [SAT solving with MiniSat](01-sat-solving-minisat.md) explores SAT solving using MiniSat, focusing on semantic tableaux algorithms and their applications to satisfiability and validity checking.
- [Logic Programming with Prolog](02-logic-programming-prolog.md) introduces logic programming with SWI-Prolog, covering unification, resolution, and applications in search with backtracking and database querying.
- [Constraints with MiniZinc](03-constraints-minizinc.md) presents constraint solving using MiniZinc, demonstrating how constraint satisfaction problems can be solved and applied to program synthesis and automated bug fixing.
- [SMT Solving and Z3](04-smt-solving-z3.md) covers SMT (Satisfiability Modulo Theories) solving with Z3, extending beyond propositional logic to handle theories like arithmetic, arrays, and bit-vectors for program verification and model checking.
- [Temporal Logic with Spin](05-temporal-logic-spin.md) examines temporal logic using the Spin model checker, focusing on LTL (Linear Temporal Logic) model checking and its applications in distributed systems and protocol verification, including the famous Needham-Schroeder Key Exchange protocol.
- [Epistemic Logic with SMCDEL](06-epistemic-logic-smcdel.md) explores epistemic logic with SMCDEL, investigating how knowledge and belief can be formally modeled and applied to social network analysis.
- [Hoare Logic with Dafny](07-hoare-logic-dafny.md) presents Hoare logic using Dafny, demonstrating how to formally specify and verify program correctness with preconditions, postconditions, and invariants.
- [Higher-Order Logic with Isabelle](08-higher-order-logic-isabelle.md) extends to higher-order logic in Isabelle/HOL, showing how to reason about functions as first-class objects and exploring the foundations of modern theorem proving.
- [Type Theory with Lean](09-type-theory-lean.md) presents dependent type theory with Lean, demonstrating how types can depend on values and enabling "proofs as programs" through the Curry-Howard correspondence.

## Planning for Fall 2026

### General Ideas

- Develop this book from one on "Logical Foundations of Software Engineering" to one on **"Formal Methods and AI"**, emphasizing the integration of symbolic and neural approaches.
- **Jupyter book version 2**: Upgrade from Jupyter book version 1 to . 
- **Bibtex**: Organize the references of each chapter using bibtex.
- **AI Assistance for Editing**: The folder [Cursor Rules](../.cursor-rules) contains natural language instructions for an AI agent to help with review and editing. They proved to particularly useful for finding typos in text and formulas, for correcting grammar and for maintaining consistent references, labelling, citations. Next time we run the course, it would be interesting to develop and use AI agents from the beginning.

### Outline of Schedule

#### Part 1: Review and Refinement (Weeks 1-6)
**Goal**: Engage new students with existing material while collaboratively improving it.

- **Weeks 1-5: Chapter Review Cycle**
  - Each lecture (2 lectures per week) focuses on one existing chapter
  - **Lecture**: Review the chapter's content, tools, and theory
  - **Homework**: Students make improvement proposals
    - One Discord channel per chapter for discussion
    - Each student must make **one pull request per week** containing an improvement proposal
    - Proposals can include: fixing typos/errors, adding examples, improving explanations, updating references, adding missing sections, enhancing software engineering perspective.
    - I am particularly interested in interactive features that encourage the reader to actively play with the concepts. In some cases, such as [SMCDEL](https://w4eg.de/malvin/illc/smcdelweb) or [Lean](https://adam.math.hhu.de/#/g/leanprover-community/), interactive playgrounds are already available online. For Z3 and MiniZinc one can work with Python notebooks. For Prolog, one can use [SWISH](https://swish.swi-prolog.org/). Dafny? Isabelle?. See also Wikipedia's [Comparison of online source code playgrounds](https://en.wikipedia.org/wiki/Comparison_of_online_source_code_playgrounds).
    - Contribute to the [Appendix on Puzzles](./appendix-puzzles.md).
  
- **Week 6: Synthesis and Prioritization**
  - Rank chapters by quality/completeness
  - Identify highest-impact improvements
  - Allocate time for implementing top improvements
  - Students vote on which chapters need the most work

#### Part 2: Extension and Innovation (Weeks 7-13)

Each student chooses one of two tracks:

##### Track A: New Chapter Development
Create a new chapter following the {ref}`suggested table of contents <suggested-table-of-contents-for-a-typical-chapter>`, presenting:
- A logic, formal method, and software tool
- Integration with AI/formal methods theme where possible

**Potential Topics:**
- **First-order theorem proving**: Vampire, Prover9, E, or other automated first-order provers
- **Knowledge Representation and Description Logics**: Semantic Web, OWL, Description Logic reasoners, [OntoUML](https://ontouml.org/)
- **Separation Logic**: For reasoning about heap-manipulating programs (e.g., with VeriFast, Infer)
- **Alloy**: Model finding and lightweight formal methods
- **TLA+**: Temporal Logic of Actions for system specification
- **ACL2**: Automated theorem proving for hardware/software verification
- **Why3**: Platform for deductive program verification
- **CBMC**: Bounded model checking for C/C++
- **Formal Methods in AI Safety**: Verification of neural networks, adversarial robustness
- **Probabilistic Programming**: Logic-based probabilistic reasoning (e.g., ProbLog, Church)

##### Track B: Project-Based Learning
Apply formal methods to a concrete engineering problem or build educational tools.

**Project Categories:**

1. **Application Projects**
   - Apply a logic-based formal method to a real engineering problem
   - Examples: verify a protocol, model-check a distributed system, solve a scheduling problem, verify a security property
   - Deliverable: Working code + documentation explaining the formal method used

2. **AI + Formal Methods Integration**
   - Combine generative AI with symbolic/formal methods
   - Examples: AI-assisted specification generation, LLM-powered proof tactics, neural-guided model checking, autoformalization tools
   - Deliverable: Working prototype + analysis of AI/formal methods integration

3. **Educational Tool Implementation**
   - Build a simple, educational implementation of a classic algorithm or tool
   - Focus: Simplicity and educational value over performance
   - Examples: 
     - Simple Prolog interpreter (unification, resolution, backtracking)
     - Basic SAT solver (DPLL algorithm)
     - Mini model checker for propositional temporal logic
     - Simple type checker for a small language
   - Deliverable: Working code + tutorial explaining how it works

4. **Chapter Enhancement Projects**
   - Substantial improvements to an existing chapter
   - Examples:
     - Add a comprehensive case study
     - Implement all examples from a chapter as runnable code
     - Create interactive visualizations or demos
     - Expand "Applications in Industry" with detailed analysis
     - Add missing sections (Algorithms, Typical Use Cases, etc.)
   - Deliverable: Enhanced chapter content + supporting materials

#### Part 3: Integration and Publication (Week 14-15)
- Final review of all contributions
- Integration of new chapters into book structure
- Quality assurance pass
- Publication preparation
- Reflection on collaborative process
