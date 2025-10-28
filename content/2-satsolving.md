# SAT solving with MiniSat
Author: Jake Triester

## Idea

A theory in propositional logic can be seen as a set of equations in variables that range over truth values $\{0,1\}$. A SAT-solver is a software tool that solves such equations. Even though SAT is NP-complete, modern SAT-solvers can solve propositional theories with millions of variables and tens of millions of clauses (reference?). And, as we know from the [Cook-Levin theorem](https://en.wikipedia.org/wiki/Cook%E2%80%93Levin_theorem) every NP-problem can be encoded in SAT.

## Basic Theory: SAT

Propositional Logic. 

Informal Definition of satisfiability: 
SAT takes a formula and finds a satifying valuation (model).

Formal definition of satisfiability:
Given a boolean formula in propositional logic, does there exist an assignment of truth values to its variables that make this formula true. If so, we say this formula is *satisfiable*. Otherwise, we say this formula is *unsatifiable*.

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

**Exercise:** Encode the following 2x2 Sudoku in conjunctive normal form.
```
[1][?]
[?][?]
```

**Exercise:** Estimate the number of variables and clauses you need to encode a 9x9 Sudoku.

## Tool: MiniSat

Here is what I did for installation on MacOs.
```
brew install minisat
echo "p cnf 2 2
1 2 0
-1 -2 0" | minisat
```
Use `sudo apt install minisat` to install on Linux.

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

**Homework:** Consider a Boolean circuit: (A ∧ B) ∨ (C ∧ ¬D) = True with the additional constraint that exactly 2 of {A,B,C,D} are true. Write this as a `cnf` specification and solve it with MiniSat. Explain your encoding and the solution in detail.

## Introductory Examples

How can we one solve a regular Sudoku with MiniSat?

For an answer see [Solving problems with CNF SAT solvers: The Sudoku example](https://users.aalto.fi/~tjunttil/2020-DP-AUT/notes-sat/solving.html#solving-problems-with-cnf-sat-solvers-the-sudoku-example).


## SAT solvers

Many companies such as Intel have their own SAT solvers, but the cutting edge of SAT-solvers are widely considered to the open source solvers such as:

- [MiniSat](http://minisat.se/) - [@Github](https://github.com/niklasso/minisat) The reference implementation
- [Glucose](https://www.labri.fr/perso/lsimon/glucose/), [@GitHub](https://github.com/audemard/glucose) ... [CaDiCaL](http://fmv.jku.at/cadical/), [@GitHub](https://github.com/arminbiere/cadical), [Lingeling](http://fmv.jku.at/lingeling/), [@GitHub](https://github.com/arminbiere/lingeling) ... [CryptoMiniSat](https://www.msoos.org/cryptominisat5/), [@GitHub](https://github.com/msoos/cryptominisat) are some award winning SAT solvers. 
- Intel SAT Solver, [@Github](https://github.com/alexander-nadel/intel_sat_solver), [pdf](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2022.8)
- [Z3](https://microsoft.github.io/z3guide/), [@GitHub](https://github.com/Z3Prover/z3) is Microsoft's SMT solver with powerful SAT core, [Tutorial](https://theory.stanford.edu/~nikolaj/programmingz3.html)
- [Clasp](https://potassco.org/clasp/), [@GitHub](https://github.com/potassco/clasp), Answer Set Programming solver

The annual [SAT Competition](http://www.satcompetition.org/) tracks the current best performers.

## The Algorithm

### Resolution

[Resolution](https://en.wikipedia.org/wiki/Resolution_(logic)) has only one inference rule:

$$
\frac{p_1\vee\ldots\vee p_m\vee a\quad\quad\quad\quad q_1\vee\ldots\vee q_n\vee \neg a }{p_1\vee\ldots\vee p_m\vee q_1\vee\ldots\vee q_n}
$$

### Davis–Putnam algorithm

The [Davis–Putnam algorithm](https://en.wikipedia.org/wiki/Davis%E2%80%93Putnam_algorithm) uses resolution but has some additional rules to guarantee termination. 

1. Select a variable
2. If the variable appears only positively, replace it by true and remove the clause.
3. If the variable appears only negatively, replace it by false and remove the clause. 
4. If it appears positively and negatively, use resolution to eliminate all occurrences. 
5. Repeat until all variables are eliminated.
6. If the empty clause is derived, then UNSATISFIABLE, else SATISFIABLE.

### Davis–Putnam–Logemann–Loveland (DPLL) algorithm

[Davis–Putnam–Logemann–Loveland (DPLL) algorithm](https://en.wikipedia.org/wiki/DPLL_algorithm) 

DP can generate many new clauses. For example in
```
(a ∨ x₁) ∧ (a ∨ x₂) ∧ (a ∨ x₃) ∧ (a ∨ x₄) ∧
(¬a ∨ y₁) ∧ (¬a ∨ y₂) ∧ (¬a ∨ y₃) ∧ (¬a ∨ y₄)
```
DP resolves every clause with 'a' against every clause with `¬a`
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

**Example Formula:** `(a ∨ b ∨ c) ∧ (¬a ∨ d) ∧ (¬b ∨ d) ∧ (¬c ∨ d) ∧ (¬d)`

### Conflict-driven Clause Learning

[Conflict-driven Clause Learning](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning)
(CDCL) is another algorithm for solving SAT problems that is similar to DPLL but the main difference is that CDCL does not back-jump chronologically. CDCL was proposed by Marques-Silva and Karem A. Sakallah (1996, 1999) and Bayardo and Schrag (1997). The algorithm is as follows:

1. Choose a variable and assign it with either true or false (called the decision state).
2. Apply Unit Propagation (this will be explained below).
3. Construct the Implication Graph (this will also be explained below).
4. If there is any conflict in the graph, do the following:
    a. Determine where in the graph the break that caused the conflict is.
    b. Make a new clause that is the negation of the assignments that caused the conflict.
    c. Backtrack non-chronologically (backjump) to the decision level where the first assigned variable in the conflict was assigned.
5. If there was no conflict, start from step 1 on a new variable until every variable has been assigned.

#### Unit Propagation

Unit propagation is a fairly simply concept. All that it says is that if we have a clause where all but one of its literals is evaluated as False, then the last literal must be True in order for the clause to be True. For example, given the following clause:

$$(A\vee B\vee C)$$

If we have $A =$ False and $B =$ False, then $C$ must be True in order for our clause to be True.


#### Implication Graphs

An implication graph is something that is drawn in step 3 of the CDCL algorithm, and it involves using your arbitrary choices, unit propagation, and implications to determine a satisfiable answer to an algorithm. To show how implication graphs work (and how the entire algorithm works), we will use this example formula:

$$(\neg A\vee B) \wedge (\neg B\vee C) \wedge (\neg C \vee A) \wedge (\neg A\vee \neg B)$$

Step 1 of the algorithm says to choose a variable and assign it either True or False. For this example, we will start by assigning $A =$ True. (A=1)

Now we move on to step 2 of the algorithm, using unit propagation to assign other variables. In the first clause, since we have $A =$ True, we must have $B =$ True. (A=1 -> B=1)

Now since $B =$ True, in the second clause we must have $C =$ True. (A=1 -> B=1 -> C=1)

In the fourth clause, since $A =$ True, $B$ must be False. (A=1 -> (B=0) and (B=1 -> C=1))

Now we have a conflict, since $B$ cannot be both True and False. According to the algorithm, once we have a conflict we must first determine in the graph the break that caused the conflict. In our graph, it is simple to see that the conflict is solely caused by $A =$ True. Thus, according to the algorithm, we must add a new clause that is the negation of the conflict. So, our new formula is:

$$(\neg A\vee B) \wedge (\neg B\vee C) \wedge (\neg C \vee A) \wedge (\neg A\vee \neg B) \wedge (\neg A)$$

Now we backjump back to where our problem was (in this case, the beginning of the graph) and start again. This time, we will assign $A =$ False. (A=0)

Using unit propagation, since $A =$ False, C must be False according to clause 3. (A=0 -> C=0)

Since $C =$ False, $B =$ False according to clause 2. (A=0 -> C=0 -> B=0).

Now we have hit step 5 of the algorithm, there are no conflicts and every variable has been assigned. Thus, our formula is satisfiable.



## Applications in Industry

Typical examples are hardware verification (Intel, AMD, Apple, etc) and dependency resolution in software package installers (Debian Linux).

More generally, SAT-solvers are used as components in SMT-solvers, CSP-solvers, model checkers and model finders. In all these applications, the implementation mainly consists of translating a problem from the input domain to the language of a SAT-solver, then finding a solution for the given problem and translating this solution back to the original domain language.

... tbc ... eg there could be more to say about SAT-solving at Intel and other hardware companies ... and then about applications of SAT to software engineering ...

## Case Studies

...


## References

### Early Work

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

... this needs more work ... here are some references I found ...

- Alouneh, S., Abed, S. E., Al Shayeji, M. H., & Mesleh, R. (2019). A comprehensive study and analysis on SAT-solvers: advances, usages and achievements. Artificial Intelligence Review, 52(4), 2575-2601.
- Froleyks, N., Yu, E., & Biere, A. (2023, October). BIG backbones. In 2023 Formal Methods in Computer-Aided Design (FMCAD) (pp. 162-167). IEEE.
- Heule, M. J., Iser, M., Järvisalo, M., & Suda, M. (2024). [Proceedings of SAT Competition 2024: Solver, Benchmark and Proof Checker Descriptions](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%22SAT+Competition+2024%22+&btnG=). [pdf](https://researchportal.helsinki.fi/files/324666039/sc2024-proceedings.pdf)
- ...




