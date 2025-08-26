# CPSC 510 - Logical Foundations of Computing (preliminary)

First sketch of content and deliverables, details will change.

We start with an overview of the course in the first week. Setting the scene. 

Then we have 11 weeks of teaching (gaps to be filled, resources to be added, etc):

| Week | Logic | Application (Tool) | Algorithm | Application^2 | Comments 
|:---:|:---:|:---:|:---:|:---:|:---:|
|2| propositional logic | SAT solver [(Z3)](https://github.com/Z3Prover/z3) | semantic tableaux | satisfiability, validity |
|3 | predicate logic 1 | Logic Programming [(SWI-Prolog)](https://www.swi-prolog.org/) | unification, resolution | search with backtracking, data base querying | [[1]](https://book.simply-logical.space/src/simply-logical.html), [[2]](https://swish.swi-prolog.org/)
|4| predicate logic 2 | Constraint Solving [(MiniZinc)](https://www.minizinc.org/) | constraint solving | program synthesis, automated bug fixing |
|5| modal logic | [^ml] | SCAN | computing first-order correspondents | [[1]](https://rkirsling.github.io/modallogic/)
|6| temporal logic | [Spin](https://spinroot.com/spin/whatispin.html) | LTL model checking | distributed systems, Needham-Schroeder Key Exchange |
|7| epistemic logic | [SMCDEL](https://w4eg.de/malvin/illc/smcdelweb/index.html) | | social networks | [[1]](https://vezwork.github.io/modallogic/?model=;AS?formula=_)
|8| Hoare logic | [Dafny](https://github.com/dafny-lang/dafny?tab=readme-ov-file#try-dafny) | | program verification | [[1]](https://dafny.org/dafny/OnlineTutorial/guide), [[2]](https://www.youtube.com/watch?v=oLS_y842fMc),
|9| simply typed lambda calculus | Isabelle/HOL |
|10| higher order logic | Isabelle/HOL |
|11| dependent type theory | [Lean](https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic) | type inference | proofs as programs |
|12| dependent type theory | Lean | type inference | program verification |

[^ml]: Modal logic has too many applications to pick just one but see temporal logic and epistemic logic below for two examples. There are algorithms to compute corespondents. For example, SCAN has implementations that are publicly available [here](https://resources.mpi-inf.mpg.de/departments/rg1/software/scan/basic_form.html) and [here](https://resources.mpi-inf.mpg.de/departments/rg1/software/scan/corr_form.html) but they were not developed into advanced software tools. So this item will be the only one that is not primarily software tool based. I include it because of the central importance of modal logic in the landscape of computational logics.

We finish with two weeks of taking stock. Tying things together. Each student writes a research proposal on a topic related to logic. This will be part of the final report.

Methodology:
- (Deliverable, tool instalation): Before the first class of each week, the tool of the week needs to be installed. Students write a how-to file with installation instructions and a short account of a small but paradigmatic case study performed with the tool.
- (In class): The first class of the week, on a Thursday, we work together through some example tools uses and present the background theory. 
- (Deliverable, weekly homework): ...
- (In class): The second class of the week, on a Tuesday, we deepen what we discuss the homework and deepen our understanding.
- (Final report ... to be revised ...): 5 page essay on one selected topic (literature review, history, state of the art, ongoing research, relation to other fields, applications to industry, success stories). Or a 3 page research proposal. Or ... 

## Some Resources

So far no effort has been made to create a systematic list. Thanks to Malvin Gattinger, Haitian Wang for references.

[Renate Schmidt's list](https://www.cs.man.ac.uk/~schmidt/tools/), [@Scholar: DEMO (Dynamic Epistemic MOdeling)](https://scholar.google.nl/scholar?q=DEMO+(Dynamic+Epistemic+MOdeling)&hl=en&as_sdt=0&as_vis=1&oi=scholart), [SMCDEL](https://github.com/jrclogic/SMCDEL), [MCMAS model checker](https://sail.doc.ic.ac.uk/software/mcmas/), ...

... tbc ...

## Additional Topics

Criteria for the choice of topics were the following.

- Are there mature software tools with a large ecosystem and significant industrial applications available?
- How well does a selected tool illustrates an important logic that has been widely influential in computer science and beyond?

Beyond that more practical constraints such as the knowledge and taste of the lecturer of course also played a role.

Important logics that have not been introduced (tbc):

- Linear Logic
- Quantum Logic
- Dynamic Logic
- Description Logics
- Probabilistic Logics
- HDC/VSA
- ...
