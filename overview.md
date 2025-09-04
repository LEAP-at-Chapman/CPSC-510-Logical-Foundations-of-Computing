# CPSC 510 - Logical Foundations of Computing (preliminary)

First sketch of content and deliverables, details will change.

We start with an overview of the course in the first week. Setting the scene. 

Important: 
- Use LLMs for research, but not for writing. 
- Do not copy LLM-output into a text intended to be read by humans. 
- When you use LLMs to generate code, make sure that you understand the code.
- In summary: Use LLMs for learning. Write to show what you learnt.

Then we have 11 weeks of teaching (gaps to be filled, resources to be added, etc):

| Week | Logic | Application (Tool) | Algorithm | Application^2 | Comments | Author |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|2| propositional logic | SAT solver [(minisat)](https://github.com/niklasso/minisat) | semantic tableaux | satisfiability, validity | | Jake |
|3 | predicate logic 1 | Logic Programming [(SWI-Prolog)](https://www.swi-prolog.org/) | unification, resolution | search with backtracking, data base querying | [[1]](https://book.simply-logical.space/src/simply-logical.html), [[2]](https://swish.swi-prolog.org/) | Brandon |
|4| predicate logic 2 | Constraint Solving [(MiniZinc)](https://www.minizinc.org/) | constraint solving | program synthesis, automated bug fixing | | Matthew |
|5| predicate logic 3 | SMT solving [(Z3)](https://github.com/Z3Prover/z3) | SMT solving | program verification, model checking | | Wayne |
|6| modal logic | [^ml] | SCAN | computing first-order correspondents | [[1]](https://rkirsling.github.io/modallogic/), [[2]](https://www.irit.fr/Lotrec/) | |
|7| temporal logic | [Spin](https://spinroot.com/spin/whatispin.html) | LTL model checking | distributed systems, Needham-Schroeder Key Exchange | | Jack |
|8| epistemic logic | [SMCDEL](https://w4eg.de/malvin/illc/smcdelweb/index.html) | | social networks | [[1]](https://vezwork.github.io/modallogic/?model=;AS?formula=_) | John |
|9| Hoare logic | [Dafny](https://github.com/dafny-lang/dafny?tab=readme-ov-file#try-dafny) | | program verification | [[1]](https://dafny.org/dafny/OnlineTutorial/guide), [[2]](https://www.youtube.com/watch?v=oLS_y842fMc), | Alex |
|10| simply typed lambda calculus | Isabelle/HOL | | | | |
|11| higher order logic | Isabelle/HOL | | | | |
|12| dependent type theory | [Lean](https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic) | type inference | proofs as programs | | |
|13| dependent type theory | Lean | type inference | program verification | | |

[^ml]: Modal logic has too many applications to pick just one but see temporal logic and epistemic logic below for two examples. There are algorithms to compute corespondents. For example, SCAN has implementations that are publicly available [here](https://resources.mpi-inf.mpg.de/departments/rg1/software/scan/basic_form.html) and [here](https://resources.mpi-inf.mpg.de/departments/rg1/software/scan/corr_form.html) but they were not developed into advanced software tools. So this item will be the only one that is not primarily software tool based. I include it because of the central importance of modal logic in the landscape of computational logics.

If we do not change the schedule, we finish with two weeks of taking stock. Tying things together. Each student writes a research proposal on a topic related to logic. 

Methodology:
- The book:
  - The intention is that every row in the table corresponds to a chapter in the book we are going to write. Every student will be responsible for one chapter. (It may be possible to divide one larger chapter among two students.) 
  - In the first week, we will devide up the topics. For their topic, each student starts by downloading their tool and following an available tutorial. Students write a how-to file with installation instructions and a short account of a small but paradigmatic case study performed with the tool.
- Week by week. It may be a good idea to start each logical week on a Thursday:
  - The first class of the week (Thursday), I will present the background theory. 
  - As a homework, students install the tool until Tuesday and work through a small example.
  - The second class of the week (Tuesday), we discuss the homework and deepen our understanding.

## Some Resources

So far no effort has been made to create a systematic list. Thanks to Andrea De Domenico, Malvin Gattinger, Haitian Wang for references.

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
