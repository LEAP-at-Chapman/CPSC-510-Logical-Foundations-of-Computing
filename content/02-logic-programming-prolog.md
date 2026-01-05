
# Logic Programming with Prolog

*Author: Brandon Foley*

## Idea
Logic programming is one of the three core paradigms of programming, alongside imperative and functional approaches. While imperative programming is centered on assignments and state changes, and functional programming emphasizes the application of functions without mutable state, logic programming takes a different perspective. At its core, a logic program consists of a collection of rules and facts, and computation is driven by the process of applying these rules to arrive at conclusions. Rather than specifying how to solve a problem step by step, logic programming focuses on what relationships hold true, allowing the system to infer solutions through logical reasoning.


## Basic Theory

At the center of logic programming there is this idea that computation can be viewed as a process of logical inference. Instead of describing a sequence of operations, as in imperative programming, or composing functions, as in functional programming, a logic program is built from facts and rules that describe relationships. A fact is a basic statement that is always considered true, while a rule expresses a conditional relationship: if certain facts hold, then another fact can be inferred. When you combine these ideas, facts and rules form a knowledge base similar to a database, and running a program means asking questions (or queries) about this knowledge.

The main computational step in logic programming is unification, the process of matching a query with the facts and rules in the program. When a query is issued, the system attempts to unify it with existing facts or the heads of rules. If a match is found, the body of the rule is pursued as a new subproblem. In this way, logical inference proceeds step by step, gradually building towards an answer. Here we can start to introduce an example in database querying. If you had for example a family tree and are searching for the child of a certain parent, it will start at that parent and check each child to see which one is the one that was queried.

One of the most powerful aspects of this logic is its built-in support for backtracking. Since there may be many possible ways to satisfy a query, the system must explore different paths. If one path fails—meaning the inference cannot be completed—the system automatically backtracks to the most recent decision point and tries an alternative. This process continues until either a valid solution is found or all possibilities have been exhausted. Backtracking makes logic programming extremely effective for solving problems that naturally involve search and constraint satisfaction, such as puzzles, planning, or reasoning over complex data. If we go back to our family tree example, say we had a family tree that looks like this:

### Mini Family Tree

```text
graph TD
    P[Parent]
    C1[Child 1]
    C2[Child 2]

    P --> C1
    P --> C2

```

Say from parent we wanted to find child 2, in logic programming, it would first look at child 1 and when it checks if that is child 2 and realizes it isn't, it will then go back to parent and try the other option which is correct. In contrast to imperative programming, which requires precise instructions for every step, logic programming is declarative: the programmer specifies what is true, and the system determines how to find the solution.

## The Tool
The tool that I will mainly be focusing on is Prolog, a unique coding language designed for logic programming. Prolog was first created in France in 1972 by Alain Colmerauer and Philippe Roussel, with its name derived from programmation en logique ("programming in logic"). The earliest version was an interpreter built in Fortran by Gerard Battani and Henri Meloni where later, David H. D. Warren brought this work to Edinburgh, where he then developed a new front-end that established the Edinburgh Prolog syntax which is now used for most modern implementations.

### Installing The Tool
[download and install](https://www.swi-prolog.org/download/stable) Prolog. On MacOS, after moving SWI-Prolog to the Applications folder, you may have to run `echo 'export PATH="/Applications/SWI-Prolog.app/Contents/MacOS:$PATH"' >> ~/.zshrc` to add `swipl` to your path. Then, running `swipl` in your terminal should start the Prolog interpreter.

There is also a web version available at [tio](https://tio.run/##KyjKz8lP1y0uz/wPBMX5OaUlmfl5GhGaegA) that is a great alternative if you do not want to download the tool!

## First Example
The eight queens problem is a logic problem in where a user attempts to place all 8 queens on a chess board such that none threaten another.

**What this shows:**
- How Prolog automatically finds solutions through backtracking
- How constraints work together to eliminate impossible choices
- How recursion naturally models complex problems
- The difference between procedural and declarative programming

Create a file named ```eightqueens.pl``` and add the following code:

```prolog
solution(Queens) :- 
    length(Queens, 8),
    queens(Queens).

queens([]).
queens([queen(Row, Col) | Others]) :- 
    queens(Others),
    length(Others, OthersLength),
    Row is OthersLength + 1,
    member(Col, [1,2,3,4,5,6,7,8]),
    noattack(queen(Row, Col), Others).

noattack(_, []).
noattack(queen(Row, Col), [queen(Row1, Col1) | Others]) :-
    Col =\= Col1,                    
    Col1-Col =\= Row1-Row,           
    Col1-Col =\= Row-Row1,
    noattack(queen(Row, Col), Others).
```

Run the program as follows.
```bash
swipl -f eight-queens.pl
```
Then in the Prolog prompt:
```prolog
?- solution(S).
```

Here there are two options either enter `.` to end the program or `;` to see further possible outputs.

Use Ctrl-d to exit Prolog.

If we enter `trace.` and enter `solution(S).` again. Use the `return` key to look into the execution of a predicate and use `s` to skip directly to the end of the execution of a predicate. Enter `a` to abort the execution. That is useful when you got lost in the execution and want to start over again.

Here is a link to the code to test on the free swi-prolog server: [eight-queens](https://tio.run/##jVJLS8QwEL73V8wxwaSQmwg9eV0q7mlhLUuUsA2miTYpBfG/r9M86u6iaC7NfI/5ZmjeRmfckftZn07emSloZ8njpJT1FO44VICnbW5ZvBhlj6HPPIOWJvg91gVuaV1VGdp37IBlqeKXbN3M4N4ZCp/wEHo1@g5Na1oWJ4aVjByd0ezbRDArsC1of8HADYhE2mkw2gcicGoGG7xm16CGZzUSHOcCtk6GIF9eydXIJXnZcdUcGOw7RH43fW8uIiTOdl82j5mIQ/PURJ7BD6eoBC/SpSGPOX@oeIz@92qD1LaMdf0sUpd51EGtEFiT4F6agH78l9rqoKXRHzKal460PntkO1p/AQ)

## Intro Examples

In logic programming, a Prolog database is composed of facts and rules that describe relationships between entities in a declarative way. Rather than specifying how to compute something, the programmer defines what is true about the problem domain. This allows Prolog to act as a powerful tool for database querying, where relationships can be inferred rather than explicitly stored. Queries are made by posing logical questions to the database then uses backtracking to search through known facts and rules to find all possible solutions to the query.

In a simple family database, the database models a small family tree using facts such as `parent(arthur, george)` and `parent(george, amelia)`, which record direct parent-child relationships. Rules like `grandparent/2`, `sibling/2`, and `ancestor/2` define how more complex family relationships can be logically derived. For instance, `grandparent(X, Z) :- parent(X, Y)`, `parent(Y, Z)` states that X is a grandparent of Z if X is a parent of Y and Y is a parent of Z. The sibling rule ensures that two people are considered siblings if they share a parent but are not the same person. The gender facts, combined with the `father/2` and `mother/2` rules, extends the database by categorizing parents according to gender, allowing for more natural queries like `father(X, Y)` or `mother(X, Y)`.

When a query such as

`?- grandparent(X, richard).`

is executed, Prolog searches through the database to find all individuals X who satisfy the condition of being a grandparent of richard. The trace output reveals Prolog’s reasoning process step by step:

``` prolog
   Call: (12) grandparent(_32210, richard) ? creep
   Call: (13) parent(_32210, _33508) ? creep
   Exit: (13) parent(arthur, george) ? creep
   Call: (13) parent(george, richard) ? creep
   Exit: (13) parent(george, richard) ? creep
   Exit: (12) grandparent(arthur, richard) ? creep
X = arthur ;
   Redo: (13) parent(george, richard) ? creep
   Fail: (13) parent(george, richard) ? creep
   Redo: (13) parent(_32210, _33508) ? creep
   Exit: (13) parent(harriet, george) ? creep
   Call: (13) parent(george, richard) ? creep
   Exit: (13) parent(george, richard) ? creep
   Exit: (12) grandparent(harriet, richard) ? creep
X = harriet ;
```

Here, Prolog begins by attempting to satisfy the rule for `grandparent/2`. It first matches `parent(_32210, _33508)` and discovers that arthur is a parent of george. Then it checks whether george is a parent of richard, which succeeds. As a result, Prolog concludes that arthur is indeed a grandparent of richard. It then continues to find the other grandparent to see if they are present which is found to be harriet. The [trace] output exposes the resolution process, where Prolog recursively attempts and verifies subgoals until a consistent solution is found. If we were to continue with this trace it would search the rest of the database to see if any other combinations would lead to the `grandparent/2` fact being true and when it fails it will just have the two grandparents that are present, arthur and harriet.

### Basic Arithmetic

While Prolog is primarily a symbolic reasoning language, it also supports arithmetic operations and numerical comparisons. Unlike traditional imperative languages where expressions are directly evaluated, Prolog treats arithmetic as part of its logical inference system. Computation occurs through the evaluation operator `is`, which forces the right-hand expression to be evaluated numerically before comparison or assignment.

For example here are some simple relationships between numbers:

```prolog
% ---------- Arithmetic Facts and Rules ----------

% The square of a number
square(X, Y) :- Y is X * X.

% The sum of two numbers
sum(A, B, Result) :- Result is A + B.

% The average of two numbers
average(A, B, Avg) :- Avg is (A + B) / 2.

% Check if one number is greater than another
greater_than(A, B) :- A > B.

```

In this example, Prolog uses the `is` operator to evaluate arithmetic expressions. The left-hand side (like `Y or Result`) becomes bound to the numeric result of the right-hand expression. Arithmetic comparisons such as `>, <, >=, and =<` can then be used within rules to reason about numerical relationships.

You can also do this directly within the terminal of swi-prolog. for example:

```prolog
?- Y is 3 +5.
Y = 8.

?- Y is 5*8.
Y = 40.

?- Y is 10/2.
Y = 5.
```

You could also, using our example from above, run queries like these:

```prolog
?- square(4, Y).
Y = 16.

?- sum(5, 7, R).
R = 12.

?- average(10, 20, A).
A = 15.0.

?- greater_than(8, 5).
true.
```

What's interesting is that prolog doesn’t "calculate" in the way procedural languages do, it evaluates logical truths involving numeric expressions. When you ask ?- square(4, Y)., Prolog checks if there exists a value of Y such that Y is 4 * 4 can be satisfied. Once the arithmetic succeeds, it binds Y to the result 16.

tio run: [code](https://tio.run/##XY/BisIwFEX3/Yq7EVp9dlQUBxdC6x8MLupKojzbMtpokurn1ySNgq5yueQc3r0qeZblWD/qrhtgWzH0rRWKIU8QaNrLgVXUV3FB2CVYjbFDrVFgiCKNokC1F4eYhwyQjmwVZ4Sc8Me6PRuP9tHxGUbI37y4sxIlfztCHTzZvfQS@zpD7BUJfjDznk3Fx3/UJ8iGg8F9KxULY6OpRAPRSFPZSaHcu9LbezHW9qauC4PnlCWp37GgJeU2v@6ZTmg2oY1tPkS/tEjSJw)

## The Landscape Of Tools

Prolog has been implemented in many different environments since its introduction in the 1970s, each designed with particular goals such as speed, interoperability, constraint solving, or educational use. Although the examples throughout this book are written using SWI-Prolog, one of the most popular and accessible implementations, it is worth going through and understanding the broader ecosystem of tools that have shaped the Prolog landscape.

**SWI-Prolog** stands as one of the most widely-used and versatile open-source implementations. Its primary strengths lie in its extensive library support, robust development tools, and strong focus on interoperability and web technologies. SWI-Prolog features a rich ecosystem that includes built-in support for HTTP servers, JSON, RDF data management, and seamless interfaces to languages like C, C++, Java, and Python. This, combined with a powerful development environment and a proactive user community, makes it an excellent choice for a wide range of applications, from academic research and rapid prototyping to complex knowledge-intensive systems and semantic web applications.

**SICStus Prolog** is a commercial-grade Prolog system developed at the Swedish Institute of Computer Science. Known for its robustness and performance, SICStus has been widely adopted in industrial and research environments where reliability is essential. It supports advanced features such as constraint logic programming (CLP), efficient memory management, and an extensive set of libraries for interfacing with external systems. Its stability and compliance with ISO Prolog standards make it a favorite for large-scale applications in AI, natural language processing, and expert systems.

**GNU Prolog** takes a different approach, functioning as a native-code compiler rather than an interpreter. It compiles Prolog code directly into machine code via an intermediate C representation. This results in highly efficient executables compared to SICStus. GNU Prolog also includes a finite domain constraint solver and provides a C interface, allowing integration with low-level systems programming. Its minimalist design and speed make it ideal for embedding Prolog logic in performance-sensitive applications.

**ECLiPSe (ECRC Logic Programming System)** extends traditional Prolog into the field of constraint logic programming (CLP). It supports solving complex combinatorial problems by allowing constraints over integers, reals, sets, and other structures to be expressed directly in logic. ECLiPSe is  strongest in operations research, scheduling, and optimization problems, offering a flexible environment for hybrid programming that blends declarative and procedural paradigms.

Across these systems, the one unifying theme is Prolog’s declarative nature. Each tool preserves the language’s logical foundation while extending it for different domains and computational models. Whether one prioritizes performance, integration, or constraint solving, there exists a Prolog implementation suited to the task.

I want to put an emphasis on **Datalog**, while derived from Prolog, represents a specialized subset of logic programming optimized for database querying and deductive reasoning. Unlike Prolog, Datalog omits complex features such as function symbols and unrestricted recursion, making it declarative, decidable, and well-suited for large-scale data processing.

Modern Datalog systems, such as **Soufflé** and **LogicBlox**, compile logical rules into efficient relational operations, bridging the gap between logic programming and database optimization. Soufflé, for example, is widely used in static program analysis, translating high-level Datalog specifications into optimized C++ code. Similarly, LogicBlox extends Datalog with constraints and aggregates, powering enterprise analytics and reasoning over massive datasets.

In essence, Datalog emphasizes the data-centric dimension of logic programming. While traditional Prolog excels in symbolic AI and dynamic reasoning, Datalog’s strength lies in query optimization, parallel execution, and scalability, making it a core technology in both academic research and industrial data systems.

## Algorithms

In a logic-programming environment like SWI-Prolog, "algorithms" refer to the fundamental computational mechanisms that transform logical declarations into executable programs. Unlike imperative languages where algorithms are primarily written by the programmer, Prolog's core algorithms are built into the language itself and automatically handle the execution of logical predicates.

### Algorithms: Core Computational Mechanisms

The following are the fundamental algorithms that power Prolog's execution model, enabling logical inference and problem-solving.

*   **Unification**
    - Unification is the pattern-matching algorithm at the heart of Prolog. It determines whether two terms can be made identical by substituting variables with appropriate values. This algorithm is used for parameter passing, fact matching, and rule application. Unification enables Prolog to match query terms with database facts and heads of rules without explicit assignment operations.

*   **Resolution and Backtracking**
    - Resolution is the inference algorithm that combines unification with logical deduction. When Prolog attempts to satisfy a goal, it searches for a matching clause in the database. If the clause is a rule, resolution recursively attempts to satisfy the subgoals in its body. Backtracking is the systematic search algorithm that explores alternative execution paths when unification fails or when multiple solutions are requested. It automatically unwinds variable bindings and tries the next possible match.

*   **Depth-First Search with Chronological Backtracking**
    - Prolog implements a specific search strategy for exploring the solution space: depth-first search with chronological backtracking. The algorithm always explores the most recent choice point first, diving deep into one branch of the possibility tree before systematically backtracking to explore alternatives. This provides the predictable left-to-right, depth-first execution order that characterizes Prolog programs.

*   **Constraint Solving Algorithms**
    - When using libraries like CLP(FD), specialized constraint solving algorithms operate alongside unification. These include domain consistency algorithms (like arc consistency), propagation techniques, and intelligent labeling strategies that work together to efficiently prune impossible values from variable domains before and during search.

*   **Term Manipulation and Structure Sharing**
    - Prolog implementations use sophisticated algorithms for term representation and manipulation, often employing structure sharing to efficiently handle variable binding environments during backtracking. These algorithms manage the creation, copying, and destruction of logical terms while maintaining execution efficiency.

### Typical Use Cases

Each software tool has its own use cases. This section describes typical use cases, including algorithms that can be implemented more efficiently or more easily with the support of the tool in question.

*   **Rule-Based Systems and Expert Systems**
    - *Use Case:* Building diagnostic tools, configuration systems, or intelligent assistants that reason through complex rule sets.
    - *Tool Support:* Prolog's built-in resolution algorithm automatically handles the forward or backward chaining through rules. The programmer declares the knowledge as facts and rules, and Prolog's inference engine automatically applies unification and backtracking to find conclusions.

*   **Natural Language Processing**
    - *Use Case:* Implementing parsers, grammar checkers, or semantic analysis tools.
    - *Tool Support:* Definite Clause Grammars (DCGs) leverage Prolog's unification algorithm to match syntactic structures, while backtracking automatically handles ambiguous parses by exploring alternative grammatical interpretations.

*   **Combinatorial Problem Solving**
    - *Use Case:* Solving scheduling problems, puzzle solving (N-Queens, Sudoku), or resource allocation.
    - *Tool Support:* The combination of Prolog's depth-first search with constraint solving algorithms (via CLP libraries) provides a complete solution framework. Programmers declare variables, domains, and constraints, while the system's algorithms handle the complex search and propagation.

*   **Protocol Analysis and Formal Verification**
    - *Use Case:* Analyzing communication protocols, model checking, or verifying system properties.
    - *Tool Support:* Prolog's unification algorithm can match protocol state patterns, while backtracking systematically explores all possible execution paths or state sequences to identify violations of desired properties.

*   **Database Query Optimization and Deductive Databases**
    - *Use Case:* Implementing intelligent query systems that combine database facts with logical rules for deductive reasoning.
    - *Tool Support:* The resolution algorithm processes recursive queries and logical inferences that would require complex joins and recursive SQL in traditional databases. Systems like Datalog optimize this further by applying database-style query optimization to logical resolution.

### Competitions & Broader Formal Methods Benchmarking

While not always Prolog-specific, these competitions shape the formal methods / logic-based reasoning tools' landscape. They offer model languages, standardized input formats, benchmark suites, and evaluation metrics. They may present opportunities for Prolog-based tools (e.g. CLP, logic-programming-as-backend) to compete or be compared.

| Competition / Benchmark | Summary & Relevance |
|------------------------|---------------------|
| **SV-COMP** (Software Verification Competition) | A major international competition for software verification tools. It provides a large benchmark repository, standardized formats, and yearly contest editions. Though not Prolog per se, aspects such as verifying safety / correctness properties might be implemented using logic-based reasoning or Prolog-driven model checkers. [SV-COMP](https://sv-comp.sosy-lab.org/) |
| **CADE ATP / CASC** (Automated Theorem Proving Competition) | Annual competition for first-order logic theorem provers. Prolog may play a role in the proof engine / back-end for logic-based provers. [Wikipedia](https://en.wikipedia.org/wiki/CADE_ATP_System_Competition) |
| **Answer Set Programming (ASP) Competition** | ASP is closely related to logic programming; its competitions compare ASP solvers using benchmark suites. [arXiv](https://arxiv.org/) |
| **RuleML Symposium — International Rule Challenge** | RuleML organizes an "International Rule Challenge" associated with rule-based systems & reasoning engines. [Wikipedia](https://en.wikipedia.org/wiki/RuleML) |
| **POPLmark challenge** | More on the mechanized metatheory side (proofs about programming language semantics), but significant as an example of benchmarking / standardizing challenges in formal methods. [Wikipedia](https://en.wikipedia.org/wiki/POPLmark) |
| **Various verification / model checking competitions** | There are many others in the formal methods / model checking space (e.g. reactive synthesis competitions, termination / SMT-Solver benchmarks).

These competitions often expect tools to support specific input / output formats, provide standard measures (time, memory, correctness), and sometimes require strict conformance or reproducibility.

## Industrial Applications of Logic Programming

Logic programming and its Datalog relatives have had concrete, high-impact uses in industry — from static program analysis to enterprise decision systems — and they are now interacting with generative (neural) methods in ways that are reshaping research and tooling.

---

### Key Industrial Applications

| Area | Why it Mattered | Representative Tools / Projects |
|------|-----------------|--------------------------------|
| **Static Program Analysis & Security** | Datalog enabled concise, portable specifications of whole-program analyses; compiled Datalog engines scale analyses to very large codebases. | Soufflé, DOOP <br> [Soufflé](https://souffle-lang.github.io/) |
| **Declarative Enterprise Analytics** | Logic/Datalog variants provided a unified, declarative backend for analytics + transactional logic, changing how complex business rules are expressed and maintained. | LogicBlox / LogiQL <br> [Department of Computer Science](https://www.cs.cmu.edu/) |
| **Immutable Fact Stores & Auditability** | Datom-style immutable facts let systems expose verifiable histories and temporal queries, useful in finance and audit-focused systems. | Datomic <br> [Datomic](https://www.datomic.com/) |
| **Program-analysis Portability & Reproducibility** | Datalog specifications made analyses portable between engines, improving reproducibility and enabling rapid experiment/production cycles. | DOOP → Soufflé porting studies <br> [PLDI 2017](https://pldi17.sigplan.org/) |

---

### How Generative AI is Changing Formal Methods

Recent years have seen rapid integration of neural/generative methods with formal, symbolic tools:

- **Large language models and neural theorem provers** are being used to propose proof steps, rank candidate proof actions, and generate tactics that formal provers can check
- **Reduced manual effort** and exploration of new hybrid workflows
- **Surveys and recent systems** report improved automation and higher proof rates when neural guidance is combined with traditional provers
- **Neural→symbolic loop** is a major current research direction

**Key Resources:**
- [SciSpace Survey](https://typeset.io) on deep learning for theorem proving

---

### Why These Applications Influenced the Field

Scalability + Abstraction
Datalog's declarative nature made it easier to express large analyses; high-quality engines (Soufflé, LogicBlox) made those analyses fast and deployable, changing where and how researchers built static analyzers.

[Soufflé Project](https://souffle-lang.github.io/)

Reproducibility & Portability
Porting DOOP to Soufflé demonstrated that large, real-world analyses can be expressed in compact rule sets and moved between engines — a pragmatic win for reproducible research.

[PLDI 2017 - Porting Doop to Soufflé](https://pldi17.sigplan.org/)

Neural+Symbolic Synergy
Generative models lower the barrier to producing candidate proofs or tactics; symbolic provers provide rigorous checking. Together they increase automation while maintaining correctness guarantees — a potent combination for verification and formalization workflows.

[SciSpace Research](https://typeset.io)

---

## Case Study
### The Water Jug Problem

The Water Jug Problem is a classic puzzle that  demonstrates Prolog's strengths in state-space search and constraint satisfaction. The scenario of this problem is as follows:

You have two jugs:

- Jug A: Capacity of 4 liters

- Jug B: Capacity of 3 liters

You need to measure exactly 2 liters of water. You can:

- Fill a jug completely

- Empty a jug completely

- Pour water from one jug to another until either the source is empty or the destination is full

This seems simple, but the sequence of operations isn't immediately obvious. With Prolog we can systematically explore all possibilities to find the solution.

These six moves defined below are the core to our solution and define all the legal moves that are available:

``` prolog
% 1. Fill Jug A completely
move(state(_, B), state(4, B)) :- 
    format('Fill Jug A~n').

% 2. Fill Jug B completely  
move(state(A, _), state(A, 3)) :-
    format('Fill Jug B~n').

% 3. Empty Jug A
move(state(_, B), state(0, B)) :-
    format('Empty Jug A~n').

% 4. Empty Jug B
move(state(A, _), state(A, 0)) :-
    format('Empty Jug B~n').

% 5. Pour from A to B until B is full or A is empty
move(state(A, B), state(NewA, NewB)) :-
    A > 0, B < 3,
    PourAmount is min(A, 3 - B),
    NewA is A - PourAmount,
    NewB is B + PourAmount,
    format('Pour ~w liters from Jug A to Jug B~n', [PourAmount]).

% 6. Pour from B to A until A is full or B is empty
move(state(A, B), state(NewA, NewB)) :-
    B > 0, A < 4,
    PourAmount is min(B, 4 - A),
    NewA is A + PourAmount,
    NewB is B - PourAmount,
    format('Pour ~w liters from Jug B to Jug A~n', [PourAmount]).
```

Each rule defines a valid transition from one state to another. The format move(CurrentState, NextState) means "from CurrentState you can move to NextState by performing this action":

Filling Rules (1 & 2): These simply reset a jug to its maximum capacity while leaving the other jug unchanged. The underscore _ acts as an anonymous variable, meaning "I don't care what value was here before."

Emptying Rules (3 & 4): These set a jug to 0 liters while preserving the other jug's contents.

Pouring Rules (5 & 6): These are the most interesting. Rule 5 says: "You can pour from A to B if A has water (A > 0) and B has space (B < 3). The amount poured is the minimum between what A has and what B can accept (min(A, 3 - B))." Rule 6 is the symmetric case for pouring from B to A.

While the move rules define the problem space, we need additional code to search through this space systematically. This "boilerplate" is interesting because it shows how Prolog can implement different search strategies with minimal changes:

```prolog
% Breadth-first search implementation
solve_bfs([state(A, B)|_], Visited, [state(A, B)|Visited]) :-
    (A =:= 2; B =:= 2),  % Goal condition: 2 liters in either jug
    !.

solve_bfs([CurrentState|RestQueue], Visited, Solution) :-
    findall(NextState, 
            (move(CurrentState, NextState), 
             \+ member(NextState, Visited)),
    NewStates),
    append(RestQueue, NewStates, NewQueue),
    solve_bfs(NewQueue, [CurrentState|Visited], Solution).

% Depth-first search alternative
solve_dfs_path(state(A, B), Path, Path) :-
    (A =:= 2; B =:= 2), !.  % Goal reached

solve_dfs_path(CurrentState, Path, Solution) :-
    move(CurrentState, NextState),
    \+ member(NextState, Path),
    solve_dfs_path(NextState, [NextState|Path], Solution).
```

Here the move rules remain unchanged regardless of whether we use BFS, DFS, or any other search strategy. The search algorithms simply navigate the graph defined by those moves.

Tio code is available to run here: [code](https://tio.run/##nVZtb9owEP7Or7h@qAhqQC2wfWDrpGQdkyZ16lqp@8AQSokpnpwX2ckoUtW/zs4vcUwCSFskaOw7P3fP47ujOc9Y9twXG7rbncPPqCAcvpXPcMezJ0YSeMjYH8I752ozmMAYGEUfAcsoj5a02PrKEk5g1LTgoa9ZxCZwSyJRcgLkJVoWbAtD49lBj7594KHA6HBPck4ESXFBs9Sxo7OQHh7GCxafS87RSUUPq1WvgfgYMRrDbfaHCBcIna4GMKWMaVawzJKckYKwbSdBZ0/HWfgQ9nwTdCwXPZj0oQP4rDKeRIXXrUHe0m5vIKGHDnToQAO44IEPCwuOi5ECP4wdWuzRAL4kebHVIY8me1klu4fnnLSAYxcwPJXg5SnAOsN3A7jLSg4rniWobJGhBmVaUIZ/qYBViZwyjhZcEHm@EbMm8Z1scI3fDpUAPoEkBx9h5KsdGSxIMgwhEROaKjGhL4GUg4SRpgD3amdrU1mFcNGyVSQVm7dNVdyKl64a5FZx92FWn59rJd67SoTSOzBKBK4S4f8pEWolAlRifEyJ0Md27UPQUuLihBL9f1YirJQIjijh9jiJ@HINAXvOOC3WSaMt1bSBYk1goybRb0TN9STqCGUz9NVi8bQS3qwq@cveHIPjB0FKOTsMbU5wgAniVds@jhi1EzccU@bDBrMiXreywBRpxGddvAppxY/yzDlNi4UwTl4LT7EOOYniYt1fUS4KEJo4ldMgqaZbp0VD3fvrAlk8UoGpxEjJtZjdua0DL4DryTUMP@A1qBdMFfTgxdmTxlTGmdiRCzQFgsJrbRXCGWbr5GFGqRrGr/dEFD9KUhI3IUvTzgOaxhFjWKcv@pyvh2T1eKqwXWBZzca313CGXxeQkOSJcBfPBO/VpawMwqyjPCdp7Nl0/dpDvapN41tzrQyo8R7rSmSHaquOqwK5oSJn0dat40Z1zGQXNPdUoHljoi70TVeynB05duXrn8qhup5TIFe9g/U62zuO1PZOOuXWmvjmnwA7BOyPv93RI0Cebjd/wNAjxcrHPr4hOfbGVPWGGQqOhPqO4pXY73fcWORRsfbqnrf9YQbA8Z6@mT5Y68R09CF13Ds/GNbM5jvc0d8nm/FsYPsRB8JyTeIW7H5naNxWk53uoc7RzlEJ@odEdJxm9v1V@u9V/m6nzg3@Ag)


### Declarative State Transitions

The most interesting aspect of the Prolog solution is how we describe the *nature* of valid moves rather than prescribing a specific sequence of operations. Instead of writing step-by-step instructions like "first fill jug A, then pour to jug B, then..." we simply define what constitutes a legal transition between states.

Each move rule reads like a natural language description of the physical constraints. The pouring rule essentially says: "If jug B has water and jug A has space, you can transfer the smaller amount between what B contains and what A can accept." This shows how we'd explain the rules to another person, yet it's executable code.

This declarative approach means we're encoding the *physics* of the problem rather than a solution strategy. Prolog then uses these fundamental rules to explore possibilities, much like how a person would mentally simulate different sequences while ensuring they never violate the physical constraints.

### Multiple Search Strategies

Our solution demonstrates how easily Prolog can switch between different problem-solving strategies. We implemented both breadth-first search (BFS) and depth-first search (DFS) approaches, each with distinct characteristics:

- **Breadth-first search** systematically explores all possible moves level by level, guaranteeing it will find the shortest solution sequence. It's methodical and complete but requires more memory to track all possibilities.

- **Depth-first search** follows each path as far as it can go before backtracking. It's more memory-efficient but might stumble upon longer solutions before finding shorter ones.

We're not rewriting the problem rules for each approach, we simply change how we navigate the possibility space. This separation of "what moves are possible" from "how we explore those moves" is a powerful demonstration of logic programming's flexibility.

### Automatic Backtracking

One of Prolog's best features that we've touched on a bit already is its built-in backtracking mechanism. When the system follows a sequence of moves that leads to a dead end, like repeatedly filling and emptying the same jug without progress, it automatically backtracks and tries alternative paths.

This eliminates the need for complex error recovery code or manual stack management that would be required in imperative languages. The programmer never writes "if this doesn't work, go back and try something else", Prolog handles that automatically as part of its fundamental execution model.

This built-in exploration makes Prolog exceptionally well-suited for problems where the solution isn't obvious but the rules are clear. It continually works through combinations that a human might overlook due to frustration or cognitive bias.

### Visual Solution Tracing

The step-by-step output reveals Prolog's reasoning process in action, transforming an abstract computational process into an understandable narrative:

```
Fill Jug A
Jug A: 4 liters, Jug B: 0 liters
Pour 3 liters from Jug A to Jug B
Jug A: 1 liters, Jug B: 3 liters
Empty Jug B
Jug A: 1 liters, Jug B: 0 liters
Pour 1 liters from Jug A to Jug B
Jug A: 0 liters, Jug B: 1 liters
Fill Jug A
Jug A: 4 liters, Jug B: 1 liters
Pour 2 liters from Jug A to Jug B
Jug A: 2 liters, Jug B: 3 liters
```

Each step follows logically from the previous state, and the sequence reveals non-obvious insights—like the need to create intermediate measurements (the 1-liter state) to achieve the final goal.

### The Big Picture

What makes this case study interesting is how it showcases Prolog's ability to bridge human reasoning and computational execution. We describe the problem in terms that make sense to us. Prolog handles the tedious work of exploring all the different combinations.

This approach scales remarkably well to more complex problems. The same pattern of defining state transitions and letting Prolog search for sequences applies to scheduling problems, route planning, configuration tasks, and many other domains where the solution isn't a simple formula but comes from following rules systematically.

## History

Logic programming, with Prolog as its flagship language, experienced a surge of use in the 1970s–80s as part of the broader AI wave. Its declarative nature—specifying *what* rather than *how*, was on course to revolutionize software development, particularly for knowledge-intensive applications like expert systems, natural language processing, and symbolic AI. During this period, Prolog was seen as a direct embodiment of the “fifth-generation computer” vision, where logic would serve as the universal foundation for advanced computing systems.

### The Golden Age (1970s–1980s)

- **Foundations**: Prolog emerged from automated theorem proving and resolution-based inference. Its core execution model—unification, depth-first search with backtracking, and Horn clause resolution—was both elegant and powerful for symbolic reasoning.
- **Rise of Expert Systems**: Tools like IBM’s Watson predecessors, XCON (for configuring DEC computers), and medical diagnostic systems often used Prolog or similar rule-based engines. Logic programming’s strength in encoding domain knowledge made it a natural fit.
- **Academic Dominance**: In Europe and Japan, logic programming was central to AI research. The Japanese Fifth Generation Computer Project (1982–1992) aimed to build massively parallel logic machines, further propelling Prolog into the spotlight.

### The Decline and Niche Survival (1990s–2000s)

- **Performance Concerns**: Prolog’s interpretive execution and unbounded search struggled with the scale and efficiency demands of growing software systems. Imperative and object-oriented languages (C++, Java) dominated industry.
- **Shift in AI**: The “AI winter” and the rise of statistical machine learning moved focus away from symbolic approaches. Prolog remained strong in specific niches: computational linguistics, formal verification, and combinatorial search problems.
- **Tool Specialization**: While general-purpose Prolog use declined, specialized logic-based tools still used prolog:
  - **Datalog** emerged as a tractable subset for database querying and program analysis.
  - **Answer Set Programming (ASP)** gained traction for declarative problem solving.
  - **Constraint Logic Programming (CLP)** integrated finite-domain solvers for scheduling and optimization.

### The Modern Renaissance: Ideas Diffused and Recombined

The core ideas of logic programming didn’t fully disappear rather they diffused into new contexts and hybrid systems:

1. **Deductive Databases and Big Data**
   - Datalog engines like **Soufflé** and **LogicBlox** scaled logic programming to billions of facts, enabling industrial-scale program analysis, security auditing, and enterprise rule systems.
   - **Datomic** brought immutable fact databases with temporal queries to modern web applications.

2. **Formal Methods and Verification**
   - Prolog’s unification and backtracking are embedded in many model checkers, theorem provers (e.g., Coq’s Ltac, Isabelle’s simplifier), and SAT/SMT solvers.
   - Logic programming’s declarative style lives on in specification languages like Alloy and TLA⁺.

3. **Domain-Specific Languages (DSLs)**
   - Many configuration languages, packet-filtering rules (e.g., iptables), and business-rule engines are essentially restricted logic languages.
   - Prolog’s grammar-definition facilities (DCGs) inspired parser generators and data-validation frameworks.

4. **Knowledge Graphs and Semantic Web**
   - RDF and OWL are fundamentally logic-based reasoning engines like SWI-Prolog’s **semweb** library apply Prolog inference to linked data.
   - Graph query languages (Cypher, Gremlin) incorporate pattern-matching ideas from logic programming.

## Formal Methods and AI

Recent advances in generative AI have sparked a renewed synergy between neural and symbolic methods, often called *neurosymbolic AI*. The dominant pattern is **guess (neural) and verify (symbolic)**:

- **Neural Guidance for Symbolic Reasoning**: Large language models (LLMs) propose candidate proofs, lemmas, or tactic sequences that traditional provers (like Vampire, E, or Lean) then verify. Systems like **GPT-f** (for Metamath) and **Thor** show that neural models can dramatically reduce search branching in theorem proving.
- **Symbolic Backends for Neural Outputs**: When LLMs generate code or logical statements, symbolic tools (type checkers, static analyzers, SMT solvers) validate correctness, providing a safety net for generative systems.
- **Hybrid Toolchains**: New pipelines combine:
  1. LLMs for informal-to-formal translation (natural language to specification),
  2. Logic engines for constraint solving and verification,
  3. Gradient-based methods for tuning heuristics or learning search policies.

This hybrid approach leverages the creativity and pattern recognition of neural networks while retaining the rigor and guarantees of symbolic reasoning—making formal methods more accessible and scalable.

## Current Developments

1. **Scalable Neuro-Symbolic Integration**
   - How to jointly train neural and symbolic components end-to-end?
   - How to represent symbolic structures (logic terms, proofs, constraints) in vector spaces effectively?

2. **Explainable and Verifiable AI**
   - Using logic programming to extract interpretable rules from neural models.
   - Building *verification-aware* training where models satisfy formal constraints.

3. **Efficient Inference at Scale**
   - Parallelizing Prolog/Datalog evaluation on modern hardware (GPUs, distributed clusters).
   - Incremental reasoning for streaming data and dynamic knowledge bases.

4. **Usability and Tooling**
   - Better IDEs, debuggers, and profiling tools for logic programs.
   - Seamless interoperability with Python, Rust, and other mainstream ecosystems.

5. **Broadening Application Domains**
   - Applying logic programming to new areas: reinforcement learning (symbolic reward shaping), cybersecurity (attack-tree analysis), and scientific discovery (hypothesis generation from data).

---

## How it's being used today

### Conferences & Workshops

- **ICLP (International Conference on Logic Programming)** – The flagship conference for traditional logic programming.
- **PPDP (Principles and Practice of Declarative Programming)** – Covers logic, functional, and constraint programming.
- **LPAR (Logic for Programming, Artificial Intelligence and Reasoning)** – Focus on logic in AI and verification.
- **CAV (Computer-Aided Verification)** and **FM (Formal Methods)** – For formal methods integrations.
- **NeurIPS / ICML workshops** on Neurosymbolic AI, Knowledge Representation, and Reasoning.
- **PADL (Practical Aspects of Declarative Languages)** – Emphasis on practical implementations and tools.

### Journals

- *Theory and Practice of Logic Programming*
- *Journal of Automated Reasoning*
- *Artificial Intelligence*
- *ACM Transactions on Computational Logic*

### Online Resources & Communities

- **SWI-Prolog Discourse** and **Stack Overflow** (Prolog tag) – Active user communities.
- **arXiv** sections: cs.AI, cs.LO, cs.PL, cs.SE.
- **GitHub** organizations: SWI-Prolog, Soufflé-lang, Datalog-educators.

## References

- Alberi (2021). [An Introduction to Datalog](https://blogit.michelin.io/an-introduction-to-datalog/), Michelin.io Blog
- Carlsson and Mildner (2012). [SICStus Prolog—The first 25 Years](https://scholar.google.com/scholar?q=SICStus+Prolog+the+first+25+Years+Carlsson), ResearchGate
- Diaz et al. [GNU Prolog](http://www.gprolog.org/), GNU Prolog
- Eclipse Foundation. [ECLiPSe Constraint Programming System](https://eclipseclp.org/), Eclipse Foundation
- GeeksforGeeks. [8 Queen Problem](https://www.geeksforgeeks.org/dsa/8-queen-problem/), GeeksforGeeks
- LeetCode. [Water and Jug Problem](https://leetcode.com/problems/water-and-jug-problem/description/), LeetCode
- Metalevel. [Sorting](https://www.metalevel.at/prolog/sorting), The Power of Prolog
- SWI-Prolog. [Logic Programming Introduction](https://swish.swi-prolog.org/p/dselman.swinb), SWISH (SWI-Prolog for Sharing)
- SWI-Prolog. [format/2](https://www.swi-prolog.org/pldoc/man?predicate=format/2), SWI-Prolog Documentation
- Swedish Institute of Computer Science. [SICStus Prolog](https://sicstus.sics.se/), SICStus
- University of Washington (2012). [Prolog Basics](https://courses.cs.washington.edu/courses/cse341/12au/prolog/basics.html), University of Washington