# Short Intro to Logic

This very short introduction to logic does not aim at explaining what logic is or the foundational role that logic plays in computing. As we will see throughout the book, many different answers can be given to these questions. Here, I only want to highlight some big ideas that underpin all these answers.

**Big Ideas of Logic**:

- Validity
- Formal Language
- Decidability
- Satisfiability
- Duality between Syntax and Semantics
- Proof Theory
- Model Theory
- Soundness and Completeness
- Incompleteness

## Validity

An important idea often attributed to [Aristotle](https://plato.stanford.edu/entries/aristotle-logic/) is the following: To check whether an argument is valid, one does not need to understand its content. This surprising insight is at the heart of artificial intelligence.[^ai]



The classic example is:

> All men are mortal.  
> Socrates is a man.  
> Therefore, Socrates is mortal.

Clearly, this is a valid argument ... but how do we *know* that it is valid?

We know that it is valid because of its form, not because we know anything about Socrates, men, or mortality. The form is:

> All X are Y.  
> Z is X.  
> Therefore, Z is Y.

This pattern holds regardless of what X, Y, and Z represent. We can substitute:
- X = "programming languages", Y = "formal systems", Z = "Dafny"
- X = "cities", Y = "locations", Z = "Paris"

The argument remains valid in all cases. This is the power of **formal reasoning**: validity depends only on the structure of the argument, not its content.

## Formal Language

Mathematically, a formal language is the smallest set closed under a finite number rules. Some examples:
- The natural numbers are the smallest set containing "zero" and closed under "plus one". 
- A programming language is the set of strings (or abstract syntax trees) that can be derived by the [context-free grammar](https://en.wikipedia.org/wiki/Abstract_syntax_tree) of the language, a classic example being the [grammar of the C language](https://www.quut.com/c/ANSI-C-grammar-y.html) and we will see later the [grammar of Promela](https://spinroot.com/spin/Man/grammar.html) in  [Chapter 5: Temporal Logic with Spin](05-temporal-logic-spin.md).
- The language of propositional logic is the smallest set containing a given set of atomic propositions (strings) and being closed under the operations AND ($\wedge$), OR ($\vee$), NOT ($\neg$).

Formal languages can be processed by algorithms. In particular, for any given formal language one would expect (terminating, even efficient) algorithms that
- answer the yes-no-question, for any string, whether that string belongs to the language,
- parse a given string into an [abstract syntax tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree).

## Decidability

Some logical questions are **decidable**: There exists an algorithm that, for any input, will eventually halt and give a correct yes-or-no answer. For example, in Chapters [1](01-sat-solving-minisat.md), [3](03-constraints-minizinc.md), [4](04-smt-solving-z3.md), [5](05-temporal-logic-spin.md), [6](06-epistemic-logic-smcdel.md) we will meet software tools based on algorithms that decide the satisfiability problem of various logics.

Other questions are **undecidable**: No algorithm exists that can always provide an answer. Famously, Turing's [Halting Problem](https://en.wikipedia.org/wiki/Halting_problem) shows that there is no algorithm that can decide, for any program, whether that program terminates on all inputs.

## Satisfiability

We remember from school various techniques to solve algebraic equations, maybe most famously [the formula for the solutions of the quadratic equation](https://en.wikipedia.org/wiki/Quadratic_equation). After Aristotle, the next important progress in logic was by [George Boole](https://en.wikipedia.org/wiki/George_Boole) who in his groundbreaking work [Mathematical Analysis of Logic](https://www.gutenberg.org/files/36884/36884-pdf.pdf) (I recommend to read at least the introduction) introduced the idea that we can calculate with logic (and probability) in much the same way we calculate with real numbers in [algebra](https://en.wikipedia.org/wiki/Algebra) and the [infinitesimal calculus](https://en.wikipedia.org/wiki/Calculus).

Maybe this can nowadays best be explained with the help of [Sudoku](https://www.nytimes.com/puzzles/sudoku/easy). To focus on the main idea let us look at a 2x2 Sudoku:

$$
\begin{array}{|c|c|}
\hline
 1 & {\ \ }  \\
\hline
   &   \\
\hline
\end{array}
$$

which has the solution

$$
\begin{array}{|c|c|}
\hline
 1 & 2 \\
\hline
 2 & 1 \\
\hline
\end{array}
$$

We can encode this puzzle using [Boolean logic](https://en.wikipedia.org/wiki/Boolean_algebra) as follows. Let us label the four cells as p, q, r, s:

$$
\begin{array}{|c|c|}
\hline
p & q \\
\hline
r & s \\
\hline
\end{array}
$$

The variables $p, q, r, s$ are bits taking values in $\{0,1\}$.

The intended encoding is as follows. For each cell, let's say the bit is 1 when the cell contains 1, and 0 when it contains 2. In the notation of [propositional logic](0-3-intro-propositional-logic.md), a **specification** of the puzzle can now be expressed as follows.

First, the rules of Sudoku are transformed into the following equations (writing $\vee$ for OR and $\neg$ for NOT) 

$$
\begin{align*}
(p \vee q) &= 1 &\text{first row contains a 1} \\
(\neg p \vee \neg q) &= 1 &\text{first row contains a 2} \\
(p \vee r) &= 1 &\text{first column contains a 1} \\
(\neg p \vee \neg r) &= 1 &\text{first column contains a 2} \\
(q \vee s) &= 1 &\text{second column contains a 1} \\
(\neg q \vee \neg s) &= 1 &\text{second column contains a 2} \\
(r \vee s) &= 1 &\text{second row contains a 1} \\
(\neg r \vee \neg s) &= 1 &\text{second row contains a 2}
\end{align*}
$$

Second, the particular starting position is encoded by

$$
\begin{align*}
p&= 1 &\text{upper left corner is 1}
\end{align*}
$$

Now we encoded the puzzle

$$
\rule{0pt}{2.5ex}
\begin{array}{|c|c|}
\hline
 1 & {\ \ }  \\
\hline
   &   \\
\hline
\end{array}
$$

as a formula in propositional logic finding a solution to the puzzle is the same as finding **an assignment of truth values for the variables satisfying the logical specification** of the puzzle. 

The software tools of Chapters [1](01-sat-solving-minisat.md), [3](03-constraints-minizinc.md), [4](04-smt-solving-z3.md), [5](05-temporal-logic-spin.md), [6](06-epistemic-logic-smcdel.md) are all elaborations of this simple idea of algorithms solving logical equations.

**Remark:** Satisfiability solvers are now used everywhere in software engineering, very much like numerical methods in more traditional areas of engineering. This is a fairly recent development: Only since the beginning of the 21st century, Boole's 1847 vision of "a Calculus of Deductive Reasoning" has become mainstream engineering on a par with Newton's and Leibniz's infinitesimal calculus. 

## Duality of Syntax and Semantics

Satisfiability is a relation between models (semantics) and formulas (syntax). This relation is commonly written in symbolic notation as 

$$
M\models\phi
$$

where $M$ denotes a model and $\phi$ ("phi") a formula. $M\models\phi$ is read as "$M$ satisfies $\phi$" or "$\phi$ is true in $M$" or "$\phi$ holds in $M$". In terms of the Sudoku example, $\phi$ is the specification representing the rules of the game together with a particular starting position and $M$ is the solution (satisfying assignment).

The reason that this is called a *duality* is that adding *more* equations means specifying *fewer* solutions. 

With a little mathematics, we can see that such a duality is a rather general phenomenon. For any relation $R\subseteq X\times A$, there are functions 

```{figure} ./images/2025-10-26-14-31-31.png
:width: 500px
```

between the set $\mathcal PX$ of subsets of $X$ and the set $\mathcal PA$ of subsets of $A$ defined by [^powerset]

[^powerset]: $\mathcal P$ stands for "powerset of".

$$
\begin{gather*}
t(S)=\{a\in A\mid xRa \text{ for all } x\in S\}\\
m(T)=\{x\in X\mid xRa \text{ for all } a\in T\}\\
\end{gather*}
$$

In the example of satisfiability, we read this as follows:
- $t(S)$ is the largest theory satisfied by all models in $S$.
- $m(T)$ is the set of all solutions specified by the theory $T$. 

## Proof Theory

Logic studies truth in general rather than what is true in the world. There are two ways of doing this. 

Proof theory studies truth-preserving transformations: Assuming that my premises are true, which rules of reasoning guarantee that my conclusions will also be true? In particular, can I be sure to never contradict myself if I follow the rules of logic? 

In symbolic notation, one writes

$$
\Gamma\vdash\phi
$$

to indicate that (in a given logical calculus) one can derive $\phi$ from the assumptions in $\Gamma$.

All of the software tools we will look at in this book can be understood as implementing reasoning in a particular calculus. In the next chapter, we will briefly look at Natural Deduction and at Tableaux.

## Model Theory

In model theory one studies truth in all possible models. Roughly speaking, a model $M$ is a mathematical structure that contains enough information in order to define when a formula $\phi$ in a given logic evaluates to true. As we have seen above this is written as $M\models\phi$. Now one can define semantic entailment as

$$
\Gamma\models\phi
$$

if all models that satisfy the assumptions in $\Gamma$ also satisfy the conclusion $\phi$, or, in symbolic notation, $M\models\phi$ if $M\models\psi$ for all $\psi\in\Gamma$.

Many of the tools in this book can be understood from a model theoretic point of view (for example: SAT-solvers, SMT-solvers, Prolog, model checkers).

## Soundness and Completeness

A hallmark of logic are its completeness theorems. For any logic, we would typically like to have a soundness and completeness theorem. While the details can be difficult, we can state soundness and completeness simply as

$$
\Gamma\vdash\phi\ \Leftrightarrow \ \Gamma\models\phi
$$

In other words, a statement is true in all models if and only if it is derivable.

## Incompleteness

Gödel's incompleteness theorem (Gödel, 1931) states that there cannot be a proof system that derives all statements in the language of arithmetic that are true in the model of natural numbers. 

This is a profound result that has ramifications in mathematics, philosophy and, of course, software engineering. A popular introduction is (Hofstadter, 1979).

## References

- Stanford Encyclopedia of Philosophy (2024) [Aristotle's Logic](https://plato.stanford.edu/entries/aristotle-logic/)
- Boole (1847) [The Mathematical Analysis of Logic](https://www.gutenberg.org/files/36884/36884-pdf.pdf)
- Gödel (1931) [Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I](https://scholar.google.com/scholar?q=Gödel+incompleteness+theorem+1931)
- Hofstadter (1979) [Gödel, Escher, Bach: An Eternal Golden Braid](https://scholar.google.com/scholar?q=Gödel+Escher+Bach+Hofstadter) 

[^ai]: This clearly is true for [symbolic AI](https://en.wikipedia.org/wiki/Symbolic_artificial_intelligence) (aka [GOFAI](https://en.wikipedia.org/wiki/GOFAI)). But it is also true for [connectionist](https://en.wikipedia.org/wiki/Connectionism), [neural](https://en.wikipedia.org/wiki/Neural_network_(machine_learning)), statistical-probabilistic-stochastic, subsymbolic AI because the Boolean circuits implemented in our silicon-based hardware are symbolic AI. In a slogan: Neural AI is compiled to symbolic AI.

    Btw, there does not seem to be an established meaning differentiating between statistical, stochastic and probabilistic. Here is Claude-Opus-4 on the topic (edited): 
    
    The terms statistical, stochastic and probabilistic overlap significantly but have slightly different uses:

    **Statistical**. Focuses on **analyzing and learning from data**. Emphasizes patterns, distributions, and inference from samples. 

    **Stochastic**. Emphasizes **randomness in the process itself**. The system's behavior involves random variables or random transitions. "Stochastic gradient descent" uses random samples to update weights. Use when: the algorithm or process has inherent randomness
    
    **Probabilistic**. Focuses on **reasoning about uncertainty**. Models beliefs, likelihood, and uncertainty explicitly using probability theory. Use when: uncertainty quantification is central to the approach
     
    Many AI methods are all three: neural networks learn **statistical** patterns from data, use **stochastic** optimization,  and can output **probabilistic** predictions. 