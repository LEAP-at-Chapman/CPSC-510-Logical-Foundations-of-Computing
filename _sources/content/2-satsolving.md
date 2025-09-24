# SAT solving with MiniSat

# Introduction to SAT and MiniSat

## Theory: SAT

Propositional Logic. Definition of satisfiability. 

SAT takes a formula and finds a satifying valuation (model).

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
Use `sudo apt install minisat`.

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

How can we one solve a regular Sudoku with MiniSat?

---

For an answer see [Solving problems with CNF SAT solvers: The Sudoku example](https://users.aalto.fi/~tjunttil/2020-DP-AUT/notes-sat/solving.html#solving-problems-with-cnf-sat-solvers-the-sudoku-example).

---

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

... tbc ... see the forthcoming book chapter ...

## Applications in Industry

Typical examples are hardware verification (Intel, AMD, Apple, etc) and dependency resolution in software package installers (Debian Linux).

More generally, SAT-solvers are used as components in SMT-solvers, CSP-solvers, model checkers and model finders. In all these applications, the implementation mainly consists of translating a problem from the input domain to the language of a SAT-solver, then finding a solution for the given problem and translating this solution back to the original domain language.

... tbc ... eg there could be more to say about SAT-solving at Intel and other hardware companies ... and then about applications of SAT to software engineering ...


## References

- Davis, Martin; Putnam, Hilary (1960). [A Computing Procedure for Quantification Theory](https://doi.org/10.1145%2F321033.321034). Journal of the ACM. 7 (3): 201–215. 
    - The original resolution based algorithm that also gave rise to Prolog later, via (Robinson 1965).
- Davis, Martin; Logemann, George; Loveland, Donald (1962). [A Machine Program for Theorem Proving](http://portal.acm.org/citation.cfm?doid=368273.368557). Communications of the ACM. 5 (7): 394–397. 
    - DPLL, also sometimes called DP Backtrack Search.
- Stallman, R. M., & Sussman, G. J. (1977). Forward reasoning and dependency-directed backtracking in a system for computer-aided circuit analysis. Artificial intelligence, 9(2), 135-196. [pdf](https://apps.dtic.mil/sti/tr/pdf/ADA035719.pdf)
    - Widely credited for its **dependency-directed backtracking**.
- Marques-Silva, J. P., & Sakallah, K. A. (1999). [GRASP: A search algorithm for propositional satisfiability](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=GRASP%3A+A+search+algorithm+for+propositional+satisfiability&btnG=). IEEE Transactions on Computers, 48(5), 506-521. [pdf](https://ieeexplore.ieee.org/iel5/12/16670/00769433.pdf) 
    - Introduces conflict-directed backtracking, an application of dependency-directed backtracking to SAT, and conflict analysis. Later this will be called **conflict-driven clause learning**.
- Moskewicz, M. W., Madigan, C. F., Zhao, Y., Zhang, L., & Malik, S. (2001, June). [Chaff: Engineering an efficient SAT solver](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Chaff%3A+Engineering+an+efficient+SAT+solver&btnG=). In Proceedings of the 38th annual Design Automation Conference (pp. 530-535). 
    - Chaff is widely considered the breakthrough SAT implementation. Section 1.2 also contains a good account of DPLL.
- These papers should give you a good background to understand the more recent articles on SAT solvers.





