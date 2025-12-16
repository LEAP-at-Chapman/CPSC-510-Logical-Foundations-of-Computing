# SAT solving with MiniSat
Author: Jake Triester

## Idea

A theory in propositional logic can be seen as a set of equations in variables that range over truth values $\{0,1\}$. A SAT-solver is a software tool that solves such equations. Even though SAT is NP-complete, modern SAT-solvers can solve propositional theories with millions of variables and tens of millions of clauses (Heule et al., 2015). And, as we know from the [Cook-Levin theorem](https://en.wikipedia.org/wiki/Cook%E2%80%93Levin_theorem) every NP-problem can be encoded in SAT.

## Basic Theory: SAT

Informal Definition of satisfiability: 
SAT takes a formula and finds a satifying valuation (model).

Formal definition of satisfiability:
Given a boolean formula in propositional logic, does there exist an assignment of truth values to its variables that make this formula true. If so, we say this formula is *satisfiable*. Otherwise, we say this formula is *unsatifiable*.

A SAT specification is written in conjunctive normal form. 

**Theorem**: Every formula in propositional logic has a conjunctive normal form.

*Proof*: (Sketch) The conjunctive normal form can be computed by the following rewrite rules: 

\begin{align*}
a\to b &= \neg a\vee b & \text{eliminate } \to\\
\neg(a\wedge b) &= \neg a \vee \neg b & \text{move } \neg \text{ inside} \\
\neg(a\vee b) &= \neg a\wedge \neg b& \text{move } \neg \text{ inside}\\
\neg\neg a &= a & \text{eliminate } \neg\neg\\
a\vee(b\wedge c) &= (a\vee b)\wedge (a\vee c) & \text{move } \wedge \text{ outside} \\
(b\wedge c)\vee a &= (b\vee a)\wedge (c\vee a) & \text{move } \wedge \text{ outside} \\
\end{align*}

If no rule can be applied anymore, then the formula is in a conjunction $(a_{11}\vee\ldots\vee a_{1n_1})\wedge \ldots \wedge (a_{k1}\vee \ldots \vee a_{kn_k})$ of so-called clauses where each $a_{ij}$ is either a propositional variable or the negation of a propositional variable.

## Tool: MiniSat

Use `brew install minisat` to install on MacOS:

Use `sudo apt install minisat` to install on Linux.

### DIMACS CNF format
A normal DIMACS CNF file looks like this:
```
p cnf <num_variables> <num_clauses>
<literal_1> <literal_2> ... <literal_n> 0
...
c This is a comment line
```
You start the file with `p cnf n m` where n is the number of variables and m is the number of clauses. Each literal is an integer; if it is positive it means it is true, if it is negative it means it is false. Each clause is a list of literals separated by spaces and ending with a `0`. A line can be commented out of the file by starting the line with a `c`.

## Introductory Examples

Let's look at a basic example of a propositional logic formula to emphasize the importance of SAT solvers:

$$(p\vee q)\wedge(\neg p\vee q)$$

Creating the truth table for this, we get:
| p | q | (p ∨ q) ∧ (¬p ∨ q) |
|---|---|--------------------|
| 0 | 0 | 0 |
| 0 | 1 | 1 |
| 1 | 0 | 0 |
| 1 | 1 | 1 |

Since there is at least one assignment of truth values that makes the equation true, this equation is *satisfiable*.

As we can see in this example, finding the truth table to determine if an equation is satisfiable is not incredibly difficult. However, the need for SAT solvers arises when the number of variables increases. In our example, we only had 2 variables, and therefore 4 rows in our truth table. However, there is an exponential increase in size of the truth table as we increase variables because for an equation with *n* variables, the number of rows in our truth table is $2^n$.

**Exercise:** Encode the following 2x2 Sudoku in conjunctive normal form.
```
[1][?]
[?][?]
```

**Exercise:** Estimate the number of variables and clauses you need to encode a 9x9 Sudoku.

**Exercise:**

```
echo "p cnf 2 2
1 2 0
-1 -2 0" | minisat
```

Explain the output, as far as you can.

**Activity:** Save the file
```
p cnf 8 16
c Each cell has exactly one value
1 2 0
-1 -2 0
3 4 0
-3 -4 0
5 6 0
-5 -6 0
7 8 0
-7 -8 0
c Each row contains both values
1 3 0
2 4 0
5 7 0
6 8 0
c Each column contains both values
1 5 0
2 6 0
3 7 0
4 8 0
```
as `sudoku_2x2.cnf`. Call
```
minisat sudoku2x2.cnf solution.txt
```

**Exercise:** Either reconstruct the encoding in `sudoku_2x2.cnf` and explain the solution. Or create your own encoding of `sudoku_2x2.cnf`, run it, and interpret the solution. 

**Exercise:** Consider a Boolean circuit: (A ∧ B) ∨ (C ∧ ¬D) = True with the additional constraint that exactly 2 of {A,B,C,D} are True. Write this as a `cnf` specification and solve it with MiniSat. Explain your encoding and the solution in detail.

## The Landscape of Tools

Many companies such as Intel have their own SAT solvers, but the cutting edge of SAT-solvers are widely considered to the open source solvers such as:

- [MiniSat](http://minisat.se/) - [@Github](https://github.com/niklasso/minisat) The reference implementation
- [Glucose](https://www.labri.fr/perso/lsimon/glucose/), [@GitHub](https://github.com/audemard/glucose) ... [CaDiCaL](http://fmv.jku.at/cadical/), [@GitHub](https://github.com/arminbiere/cadical), [Lingeling](http://fmv.jku.at/lingeling/), [@GitHub](https://github.com/arminbiere/lingeling) ... [CryptoMiniSat](https://www.msoos.org/cryptominisat5/), [@GitHub](https://github.com/msoos/cryptominisat) are some award winning SAT solvers. 
- Intel SAT Solver, [@Github](https://github.com/alexander-nadel/intel_sat_solver), [pdf](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2022.8)
- [Z3](https://microsoft.github.io/z3guide/), [@GitHub](https://github.com/Z3Prover/z3) is Microsoft's SMT solver with powerful SAT core, [Tutorial](https://theory.stanford.edu/~nikolaj/programmingz3.html)
- [Clasp](https://potassco.org/clasp/), [@GitHub](https://github.com/potassco/clasp), Answer Set Programming solver

## The Algorithm

### Resolution

[Resolution](https://en.wikipedia.org/wiki/Resolution_(logic)) has only one inference rule:

$$
\frac{p_1\vee\ldots\vee p_m\vee a\quad\quad\quad\quad q_1\vee\ldots\vee q_n\vee \neg a }{p_1\vee\ldots\vee p_m\vee q_1\vee\ldots\vee q_n}
$$

### Unit Propagation
[Unit Propagation](https://en.wikipedia.org/wiki/Unit_propagation) is a fairly simply concept. All that it says is that if we have a clause where all but one of its literals is evaluated as False, then the last literal must be True in order for the clause to be True. For example, given the following clause:

$$(A\vee B\vee C)$$

If we have $A =$ False and $B =$ False, then $C$ must be True in order for our clause to be True.

Unit propagation can also be used in the case of a clause having only one variable, because if there is only one variable then it has to be true. For example, given the following clause:

$$(\neg A)$$

We know the clause has to be true, so we apply unit propagation, meaning we set $A =$ False.

### Pure Literal Elimination

If a variable appears throughout the entire formula as only positive or only negative, you can set it to satisfy every clause that contains it. This means that if a variable appears only positively, you can replace it by True and remove the clause. Also, if a variable appears only negatively, you can replace it by False and remove the clause. For example, given the following formula:

$$(\neg A \vee B) \wedge (\neg A \vee C)$$

We see that A appears only negatively. Thus we replace A with False and our new formula becomes:

$$(\neg False \vee B) \wedge (\neg False \vee C)$$

Since the opposite of False is True, we are able to remove both of the clauses from our formula.


### Davis–Putnam algorithm

The [Davis–Putnam algorithm](https://en.wikipedia.org/wiki/Davis%E2%80%93Putnam_algorithm) uses resolution but has some additional rules to guarantee termination. 

1. Select a variable
2. Apply Pure Literal Elimination to the variable
3. If a variable appears positively and negatively, use resolution to eliminate all occurrences. 
4. Repeat until all variables are eliminated.
5. If the empty clause is derived, then UNSATISFIABLE, else SATISFIABLE.

#### Davis-Putnam Algorithm example

Given the following formula, we will use the Davis-Putnam algorithm to solve it:

$$(A \vee B) \wedge (\neg A \vee C) \wedge (\neg B \vee \neg C)$$

Step 1 of the algorithm is to select a variable, we will start with A. We see that in clause 1, A appears positively and in clause 2, A appears negatively, meaning we must use resolution. To do that, we take both clauses 1 and 2, remove each instance of A, combine the clauses, and then add it to our formula. So, our new formula is:

$$(B \vee C) \wedge (\neg B \vee \neg C)$$

Now, we repeat our steps with a new variable, we will pick B. Since B appears both positively and negatively, we will use resolution again. After resolution, we are left with the formula:

$$(C \vee \neg C)$$

As we know, this is always true, so we can remove it from our formula. Thus, no clauses are remaining, meaning the formula is satisfiable. 

This may be a little confusing because the 5th step of the algorithm says that if the empty clause is derived, then the formula is unsatisfiable. However, we did not derive the empty clause, and I will give a demonstration of how the empty clause is derived to clear up any confusion. Imagine this is our formula:

$$(A) \wedge (\neg A)$$

Using the algorithm, A appears both positively and negatively, meaning that we have to use resolution again. However, after using resolution, we are left with the empty clause (denoted as $\square$). Thus our formula is unsatisfiable. 

### Davis–Putnam–Logemann–Loveland (DPLL) algorithm

[Davis–Putnam–Logemann–Loveland (DPLL) algorithm](https://en.wikipedia.org/wiki/DPLL_algorithm) 

DP can generate many new clauses. For example in
```
(a ∨ x₁) ∧ (a ∨ x₂) ∧ (a ∨ x₃) ∧ (a ∨ x₄) ∧
(¬a ∨ y₁) ∧ (¬a ∨ y₂) ∧ (¬a ∨ y₃) ∧ (¬a ∨ y₄)
```
DP resolves every clause with `a` against every clause with `¬a`
```
(a ∨ x₁) + (¬a ∨ y₁) → (x₁ ∨ y₁)
(a ∨ x₁) + (¬a ∨ y₂) → (x₁ ∨ y₂)  
(a ∨ x₁) + (¬a ∨ y₃) → (x₁ ∨ y₃)
(a ∨ x₁) + (¬a ∨ y₄) → (x₁ ∨ y₄)

(a ∨ x₂) + (¬a ∨ y₁) → (x₂ ∨ y₁)
(a ∨ x₂) + (¬a ∨ y₂) → (x₂ ∨ y₂)
...
(a ∨ x₄) + (¬a ∨ y₄) → (x₄ ∨ y₄)
```
resulting in 4x4=16 clauses.

DPLL instead intantiates variables and uses backtracking:
```
Try a = True:
- All (a ∨ xᵢ) become satisfied (removed)
- All (¬a ∨ yᵢ) become (yᵢ)
```

Both DP and DPLL have exponential time complexity in the worst case. But in practice DPLL is much better. One difference is that due to backtracking DPLL is linear in memory. 

The algorithm for DPLL follows these steps:
1. Apply Unit Propagation
2. Apply Pure Literal Elimination
3. If the empty clause appears, return UNSAT
4. If no clauses are left, return SAT
5. Choose a variable
6. Recursively try both assignments on that variable

    a. Assign that variable to True

    b. If that fails, assign it to False

    c. If either step a or b succeeds, return SAT, otherwise, return UNSAT

**Example Formula:** `(a ∨ b ∨ c) ∧ (¬a ∨ d) ∧ (¬b ∨ d) ∧ (¬c ∨ d) ∧ (¬d)`

First we apply unit propagation. Since the last clause has only one variable, we know that `d` = False. Then, we simplify so that our new formula is:

`(a ∨ b ∨ c) ∧ (¬a) ∧ (¬b) ∧ (¬c)`

Now, we apply unit propagation again, this time setting `a` equal to False. Our new formula is:

`(b ∨ c) ∧ (¬b) ∧ (¬c)`

One more time, we apply unit propagation, setting `b` equal to False. Our new formula is:

`(c) ∧ (¬c)`

This leads to a contradiction, because `c` cannot be both True and False. Thus, our formula is `UNSAT`

### Conflict-driven Clause Learning (CDCL) algorithm

[Conflict-driven Clause Learning](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning)
(CDCL) is another algorithm for solving SAT problems that is similar to DPLL but the main difference is that CDCL does not back-jump chronologically. CDCL was proposed by Marques-Silva and Karem A. Sakallah (1996, 1999) and Bayardo and Schrag (1997). The algorithm is as follows:

1. Choose a variable and assign it with either True or False (called the decision state).
2. Apply Unit Propagation.
3. Construct the Implication Graph (this will be explained below).
4. If there is any conflict in the graph, do the following:

    a. Determine where in the graph the break that caused the conflict is.

    b. Make a new clause that is the negation of the assignments that caused the conflict.

    c. Backtrack non-chronologically (backjump) to the decision level where the first assigned variable in the conflict was assigned.

5. If there was no conflict, start from step 1 on a new variable until every variable has been assigned.

#### Implication Graphs

An implication graph is something that is drawn in step 3 of the CDCL algorithm, and it involves using your arbitrary choices, unit propagation, and implications to determine a satisfiable answer to an algorithm. To show how implication graphs work (and how the entire algorithm works), we will use this example formula:

$$(\neg A\vee B) \wedge (\neg B\vee C) \wedge (\neg C \vee A) \wedge (\neg A\vee \neg B)$$

Step 1 of the algorithm says to choose a variable and assign it either True or False. For this example, we will start by assigning $A =$ True.
```
(A = 1)
```

Now we move on to step 2 of the algorithm, using unit propagation to assign other variables. In the first clause, since we have $A =$ True, we must have $B =$ True. 
```
(A = 1) -> (B = 1)
```

In the fourth clause, since $A =$ True, $B$ must be False. 
```
(A = 1) -> (B = 1) 
        -> (B = 0)
```

Now we have a conflict, since $B$ cannot be both True and False. According to the algorithm, once we have a conflict we must first determine in the graph the break that caused the conflict. In our graph, it is simple to see that the conflict is solely caused by $A =$ True. Thus, according to the algorithm, we must add a new clause that is the negation of the conflict. So, our new formula is:

$$(\neg A\vee B) \wedge (\neg B\vee C) \wedge (\neg C \vee A) \wedge (\neg A\vee \neg B) \wedge (\neg A)$$

Now we backjump back to where our problem was (in this case, the beginning of the graph) and start again. This time, we will assign $A =$ False. 
```
(A = 0)
```

Using unit propagation, since $A =$ False, C must be False according to clause 3. 
```
(A = 0) -> (C = 0)
```

Since $C =$ False, $B =$ False according to clause 2. 
```
(A = 0) -> (C = 0) -> (B = 0)
```

Now we have hit step 5 of the algorithm, there are no conflicts and every variable has been assigned. Thus, our formula is satisfiable.

### DPLL vs CDCL example

Here, we will solve an example formula using both DPLL and CDCL, and determine which algorithm is better (more efficient) and why. We will start with this formula:

$$(A \vee B) \wedge (\neg A \vee C) \wedge (\neg B \vee C) \wedge (\neg C \vee D) \wedge (\neg C \vee E) \wedge (\neg C \vee F) \wedge (\neg C \vee G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

Since there is no way to apply unit propagation or pure literal elimination, we start by choosing a variable `A` and recursively trying both assignments. First we will assign `A` the value of True. That makes our equation:

$$(C) \wedge (\neg B \vee C) \wedge (\neg C \vee D) \wedge (\neg C \vee E) \wedge (\neg C \vee F) \wedge (\neg C \vee G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

From here we can apply unit propagation to `C`, since we know from the first clause that `C` must be True, leaving us with:

$$(D) \wedge (E) \wedge (F) \wedge (G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

From here we would apply unit propagation on `D`, `E`, `F`, and `G`, setting them all equal to True. This leads us to a contradiction since the final clause will be False. From here, we have to backtrack to our assigned variable, meaning we set `A` to False in our original equation. That makes our formula the following:

$$(B) \wedge (\neg B \vee C) \wedge (\neg C \vee D) \wedge (\neg C \vee E) \wedge (\neg C \vee F) \wedge (\neg C \vee G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

From here, we can apply unit propagation, setting `B` equal to True. This makes our equation:

$$(C) \wedge (\neg C \vee D) \wedge (\neg C \vee E) \wedge (\neg C \vee F) \wedge (\neg C \vee G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

Now we can apply unit propagation one more time, setting `C` equal to True, which brings us back to this formula:

$$(D) \wedge (E) \wedge (F) \wedge (G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

Again, we would apply unit propagation to `D`, `E`, `F`, and `G`, which we know will not be satisfiable from earlier. This means we have recursively tried both assignments on the variable `A`, and they both failed, making this equation `UNSAT`.

As we can see, the DPLL algorithm took a long time and energy because it had to go through every possible branch to confirm that the formula was `UNSAT`. We even combined a few branches (`D`, `E`, `F`, and `G`) and it still took awhile. In comparison, we will now solve this equation with CDCL. As a reminder, here is our original formula:

$$(A \vee B) \wedge (\neg A \vee C) \wedge (\neg B \vee C) \wedge (\neg C \vee D) \wedge (\neg C \vee E) \wedge (\neg C \vee F) \wedge (\neg C \vee G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

The first step of CDCL is to choose a variable and assign it a value. To mirror our DPLL implementation, we will also assign `A` the value of True. As a reminder, we also will be constructing an implication graph.
```
(A = 1)
```
Our new equation becomes:

$$(C) \wedge (\neg B \vee C) \wedge (\neg C \vee D) \wedge (\neg C \vee E) \wedge (\neg C \vee F) \wedge (\neg C \vee G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

We apply unit propagation setting `C` equal to True, making our implication graph:
```
(A = 1) -> (C = 1)
```
And our new formula:

$$(D) \wedge (E) \wedge (F) \wedge (G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G)$$

By applying unit propagation to `D`, `E`, `F`, and `G`, we cause a conflict, and our implication graph looks like this:
```
(A = 1) -> (C = 1) -> (D = 1) -|
                   -> (E = 1) -| -> (¬D1 ∨ ¬D2 ∨ ¬D3 ∨ ¬D4)
                   -> (F = 1) -|
                   -> (G = 1) -|
```

From our implication graph, we can determine the break that caused the conflict is at `(C = 1)`, so we can backjump to the beginning and add a new learned clause of $(\neg C)$, making our formula:

$$(A \vee B) \wedge (\neg A \vee C) \wedge (\neg B \vee C) \wedge (\neg C \vee D) \wedge (\neg C \vee E) \wedge (\neg C \vee F) \wedge (\neg C \vee G) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G) \wedge (\neg C)$$

Now we can apply unit propagation to our learned clause and set `C` equal to False.
```
(C = 0)
```

This makes our new equation:

$$(A \vee B) \wedge (\neg A) \wedge (\neg B) \wedge (\neg D \vee \neg E \vee \neg F \vee \neg G) \wedge (\neg C)$$

From here, we can unit propagate `A` and `B` and set them each equal to False. This will lead to a conflict in clause 1, and our impliation graph looks like this:
```
(C = 0) -> (A = 0) -| -> (A ∨ B)
        -> (B = 0) -|
```

The break that caused the conflict is at `(C = 0)`. Since that is the beginning of our implication graph, we can't backjump anymore. Therefore, the formula is `UNSAT`.

From this example, we can see how much quicker CDCL is than DPLL, and how that speed will only exponentially increase with a greater number of variables and clauses. DPLL had to go through every possible branch, while CDCL learns from each branch that it goes through so it doesn't end up searching through something that it already searched through, making it much more optimal.

## Typical Use Cases

### Parallel Approaches

Some SAT solvers use multiple processors at the same time to speed up problem solving. There are 2 different types of strategies tha modern parallel SAT solvers rely on.

#### Portfolio

The portfolio parallel approach involves running many solvers in parallel on the same problem (Aigner et al., 2013). Once one of the solvers finds a solution, they all can stop. This reduces the time needed to solve because it is trying multiple at once. Many portfolio approaches implement random seeds to decrease the amount of duplicate work that the solvers are doing. Depending on the underlying algorithm behind the SAT solvers, it is possible that the different portfolios could share learned clauses amongst each other, which will decrease time taken to solve even more. A few examples of portfolio parallel SAT solvers are PPfolio and HordeSat.

#### Divide-and-conquer

A different parallel approach involves spitting the problem into smaller sub-problems, and then running each of those on a different processor (Nair et al., 2022). This can cause some processors to finish their problems much earlier than others because different sub-problems can vary in difficulty, which is suboptimal. One very benefical advance is the Cube-and-Conquer approach, which uses two phases. The first phase is the cube part where a solver "looks ahead" and breaks the problem into smaller "cubes." Phase 2 is the conquer f=part where each cube is solved using CDCL. Because of the way the cubes are calculated, if one cube is satisfiable, then the whole problem is satisfiable. One example divide-and-conquer that uses the cube-and-conquer approach is Treengeling.

## Benchmarks and Competitions

The annual [SAT Competition](http://www.satcompetition.org/) tracks the current best performers.

The purpose of this competition is to promote new SAT solvers and compare them to current state-of-the-art ones, as well as identify new benchmarks.

## Applications in Industry

SAT-solvers are used as components in SMT-solvers, CSP-solvers, model checkers and model finders. In all these applications, the implementation mainly consists of translating a problem from the input domain to the language of a SAT-solver, then finding a solution for the given problem and translating this solution back to the original domain language. These applications are central to many industrial workflows. Historically, they have moved the field from theoretical curiosity (like NP-completeness) to large-scale problem solving. Today, solvers can easily handle problems with millions of variables and tens of millions of clauses.

One main area where SAT technology is heavily used is hardware verification (Gupta, Ganai, and Wang, 2006). It is used to verify the pipelines of GPUs and CPUs through property checking. SMT solvers (a descendant of SAT) are especially used in hardware verification because they are able to combine the core principles of SAT with theory solvers for arithmetic and arrays.

Similarly, SAT solvers are also used for software verification and program analysis (Ivančić et al., 2008). They can either provide counterexamples when a property fails or proofs for satisfiability, which is especially helpful when debugging.

SAT solvers are also used for package and dependency solving and optimization. By translating domain constraints into CNF, the solvers can be used for dependency resolution (package managers), combinatorial optimization (scheduling), or other large combinatorial tasks.

While not necessarily an application of use in industry, there is an annual [SAT competition](#benchmarks-and-competitions) that is used to track the state of the art and can help lead to adoption in industry. This competition is beneficial because it leads people to find new algorithms and heuristics than can be used to improve the state of the art.

## Case Studies

At the beginning of this chapter, we looked at an example of a 2x2 sudoku and how to solve it using SAT. Now, we will look at a normal 9x9 sudoku and see how to solve that using SAT. Unlike our 2x2 sudoku which had a very small number of variables and clauses, 9x9 sudoku needs 729 variables and about 12000 clauses. Because of this, we cannot simply write the DIMACS CNF file on our own, we need to create a script that will create the file for us. Similarly to the 2x2 example, we need to create a cnf file that has the following constraints:

1. Each entry has at least one value
2. Each entry has at most one value
3. Each row contains all numbers (1-9)
4. Each column contains all numbers (1-9)
5. Each block contains all numbers (1-9)
6. The solution respects the given clues

In order to create the necessary cnf file, we will use the script taken from this [website](https://users.aalto.fi/~tjunttil/2020-DP-AUT/notes-sat/solving.html#solving-problems-with-cnf-sat-solvers-the-sudoku-example) named `sudoku-encode.py`:


This script will create a cnf representation given an example sudoku board. I created this file named `puzzle.txt` and used it as my input:
```
53..7....
6..195...
.98....6.
8...6...3
4..8.3..1
7...2...6
.6....28.
...419..5
....8..79
```

In order to run these files on Linux (Ubuntu) I did this:

`python3 sudoku-encode.py puzzle.txt`

This will print out the example cnf, but if you want to put it into a file you can run:

`python3 sudoku.py puzzle.txt > puzzle.cnf`

From there, we can use minisat to see if the puzzle is satisfiable and we can output the solution into a `.txt` file by running:

`minisat puzzle.cnf output.txt`

In the terminal, it will tell you whether or not the puzzle was satisfiable, and in the `output.txt` file, it will tell you the assignment values of each of the 729 variables, but it will not show the actual solution to the sudoku puzzle. In order to do that we must use a decoder script such as this one:
```
#!/usr/bin/python3
import sys

D = 3
N = D*D  # 9

def inv_var(x):
    x -= 1
    r = x // (N*N) + 1
    x %= (N*N)
    c = x // N + 1
    v = x % N + 1
    return r, c, v

# read SAT solver output file
model = []
with open(sys.argv[1], "r") as f:
    for line in f:
        if line.startswith("SAT") or line.startswith("UNSAT"):
            continue
        model.extend(map(int, line.split()))

# grid to fill
grid = [[0]*N for _ in range(N)]

# use only positive literals
for literal in model:
    if literal > 0:
        r, c, v = inv_var(literal)
        grid[r-1][c-1] = v

# print sudoku
for row in grid:
    print(" ".join(str(x) for x in row))
```

With this script, we can run:

`python3 decoder.py output.txt`

This will show us the final solution of our sudoku puzzle with our given constraints. Now, we can edit our `puzzle.txt` to be able to determine if any 9x9 sudoku with any given values is satisfiable, and then use `decoder.py` to output the solution of that puzzle. Also, given the way we created our `sudoku-encode.py` and `decoder.py` files, we can try this with any size sudoku by simply changing a few numbers.

## History

In the 1990s, there were two different types of SAT solvers that were used - complete and incomplete solvers (Biere, Heule, Van Maaren, and Walsh, 2021). An incomplete solver is one that searches for a satisfying assignment, but cannot prove that something is unsatisfiable. A complete solver is more similar to the ones seen today, that either finds a satisfying assignment or proves that none exist. Around this time, the complete solvers were using the [DPLL](#davisputnamlogemannloveland-dpll-algorithm) algorithm.

In 1993, a SAT competition was held, named the DIMACS implementation challenge (Fichte, Le Berre, Hecher, and Szeider, 2023). This competition standardized the [DIMACS CNF](#dimacs-cnf-format) format that modern SAT solvers still use as their inputs.

In 1996, the solver GRASP was created (Marques-Silva, J. P., & Sakallah, K. A., 1999). This solver proposed a new architecture that combined the backtracking of the DPLL algorithm with learning, which is now known as the [CDCL](#conflict-driven-clause-learning-cdcl-algorithm) algorithm. After that, the solver Chaff was created (Moskewicz, M. W., Madigan, C. F., Zhao, Y., Zhang, L., & Malik, S., 2001, June). This solver was specifically designed to solve large benchmarks, and do so quickly.

## Formal Methods and AI

### Use of Generative AI

As the use of generative AI becomes more and more integrated into every industry, SAT solvers are no exception. Generative AI (LLMs) are increasingly being used to augment SAT solvers rather than replace them completely. There are a couple of different examples that show this.

First, generative AI models are being used for instance generation. This is beneficial because it is used to generate SAT instaances that mimic real-world problems, which can help to study the behavior of the solvers and see how they can be improved. One example of this is G2SAT, which makes CNF formulas into bipartite graphs and learns to generate realistic SAT instances.

Another example is using solvers to check proofs that are created by LLMs. For example, an LLM will propose a proof, and the solvers will check, reject, or give feedback on these proposed proofs. This is more with SMT solvers than SAT due to their proof checking abilities, but as SMT is a descendant of SAT, it has been included in the section.

Solvers are also being used to reduce hallucinations and increase reliability in certain AI models. Some models, including ones from Amazon have integrated "automated reasoning checks" to constrain generative models (argument checking, verification checks on outputs of the model, rule enforcement) to improve trustworthiness.

More applications of AI use in SAT solvers is seen in the current developments section [below](#current-developments-with-ai)

### How this affects SAT in industry

Hybrid workflows are becoming much more common in industry. This means that generative AI models are proposing something, and SAT solvers are used to provide guarantees of truthfulness or unsatisfiability. This is beneficial because it is utilizing the creativity of generative AI, while confirming correctness through the rigidity of SAT solvers.

## Current Developments

After the developments of CDCL algorithms were added into SAT solvers, there are still a few current developments that have increased the capabilities of SAT solvers a little more.

For one, people have started to create much more efficient SAT encodings by going against what intuition says. Instinctively, people think that a small formula and fewer variables in better, however that is not always true. Sometimes it is more benefical to add some auxillary variables and increase the size of the formula. While adding these variables increases the theoretical search space, the practical search may become easier. This is because SAT solvers do not search everything, and adding some extra variables will allow the solvers to significantly reduce the size of the practical search space by using CDCL.

Another more current development is the use of [parallel solving](#parallel-approaches), which was mentioned more in depth above.

### Current Developments with AI
As can be seen in almost every industry, AI, specifically large language models (LLMs), are being used to try to improve the state of the art. One example in terms of SAT solvers is AutoModSAT (Sun et al., 2025). Using an LLM in a SAT solver can allow the solver to automatically generate new heuristic code so the the solver can work better given specific data. Basically, this means that the LLM is finding better strategies for solving SAT problems, and is able to determine what to use on a specific dataset.

## References

- Aigner et al. (2013). [Analysis of Portfolio-Style Parallel SAT Solving
on Current Multi-Core Architectures∗](https://ckirsch.github.io/publications/conferences/PoS13-AnalysisPortfolioSAT.pdf), University of Salzburg
-  Fichte, Le Berre, Hecher, and Szeider (2023) [The Silent (R)evolution of SAT](https://cacm.acm.org/research/the-silent-revolution-of-sat/#R4), Communications of the ACM
- Gupta, Ganai, and Wang (2006). [SAT-Based Verification Methods and Applications in Hardware Verification](https://link.springer.com/chapter/10.1007/11757283_5#citeas), Formal Methods for Hardware Verification
- Heule et al. (2015). [Clause Elimination for SAT and QSAT](https://jair.org/index.php/jair/article/view/10942), Journal of Artificial Intelligence Research
- Ivančić et al. (2008). [Efficient SAT-based bounded model checking for software verification](https://www.sciencedirect.com/science/article/pii/S0304397508002223), International Symposium on Leveraging Applications of Formal Methods
- Nair et al. (2022). [Proof-Stitch: Proof Combination for
Divide-and-Conquer SAT Solvers](https://theory.stanford.edu/~barrett/pubs/NCW+22.pdf), Formal Methods in Computer-Aided Design

### Early Work

- Biere, Heule, Van Maaren, and Walsh (2021). [Handbook of Satisfiability](https://www.iospress.com/catalog/books/handbook-of-satisfiability-2), Frontiers in Artificial Intelligence and Applications
- Davis, Martin; Putnam, Hilary (1960). [A Computing Procedure for Quantification Theory](https://scholar.google.com/scholar?q=A+Computing+Procedure+for+Quantification+Theory). Journal of the ACM. 7 (3): 201–215. 
    - The original resolution based algorithm that also gave rise to Prolog later, via (Robinson 1965).
- Davis, Martin; Logemann, George; Loveland, Donald (1962). [A Machine Program for Theorem Proving](https://scholar.google.com/scholar?q=A+Machine+Program+for+Theorem+Proving). Communications of the ACM. 5 (7): 394–397. 
    - DPLL, also sometimes called DP Backtrack Search.
- Stallman, R. M., & Sussman, G. J. (1977). [Forward reasoning and dependency-directed backtracking in a system for computer-aided circuit analysis](https://scholar.google.com/scholar?q=Forward+reasoning+and+dependency-directed+backtracking+in+a+system+for+computer-aided+circuit+analysis). Artificial intelligence, 9(2), 135-196.
    - Widely credited for its **dependency-directed backtracking**.
- Marques-Silva, J. P., & Sakallah, K. A. (1999). [GRASP: A search algorithm for propositional satisfiability](https://scholar.google.com/scholar?q=GRASP+A+search+algorithm+for+propositional+satisfiability). IEEE Transactions on Computers, 48(5), 506-521. 
    - Introduces conflict-directed backtracking, an application of dependency-directed backtracking to SAT, and conflict analysis. Later this will be called **conflict-driven clause learning**.
- Moskewicz, M. W., Madigan, C. F., Zhao, Y., Zhang, L., & Malik, S. (2001, June). [Chaff: Engineering an efficient SAT solver](https://scholar.google.com/scholar?q=Chaff+Engineering+an+efficient+SAT+solver). In Proceedings of the 38th annual Design Automation Conference (pp. 530-535). 
    - Chaff is widely considered the breakthrough SAT implementation. Section 1.2 also contains a good account of DPLL.


### Modern Developments

- Alouneh, S., Abed, S. E., Al Shayeji, M. H., & Mesleh, R. (2019). A comprehensive study and analysis on SAT-solvers: advances, usages and achievements. Artificial Intelligence Review, 52(4), 2575-2601.
- Froleyks, N., Yu, E., & Biere, A. (2023, October). BIG backbones. In 2023 Formal Methods in Computer-Aided Design (FMCAD) (pp. 162-167). IEEE.
- Heule, M. J., Iser, M., Järvisalo, M., & Suda, M. (2024). [Proceedings of SAT Competition 2024: Solver, Benchmark and Proof Checker Descriptions](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%22SAT+Competition+2024%22+&btnG=). [pdf](https://researchportal.helsinki.fi/files/324666039/sc2024-proceedings.pdf)
- Sun et al. (2025). [Automatically discovering heuristics in a complex SAT solver with large language models](https://arxiv.org/html/2507.22876v1)

## Future Work

In the future, I believe it would be more beneficial for someone to focus more on the real-life applications of SAT solvers. I spent a lot of time on the algorithms and examples of how they are used, which didn't leave me much time to focus on how the SAT solvers apply to real-life.

## Contributers

The author of this chapter is Jake Triester. It was peer reviewed by Jack De Bruyn and Alexander Kurz.




