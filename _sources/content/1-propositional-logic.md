# Propositional Logic

Author: Alexander Kurz

The purpose of this note is to introduce the simplest logic that will appear throughout the book. It is known as [propositional logic](https://en.wikipedia.org/wiki/Propositional_logic), or classical propositional logic (as opposed to variants such as [intuitionistic logic](https://en.wikipedia.org/wiki/Intuitionistic_logic)) or [Boolean logic](https://en.wikipedia.org/wiki/Boolean_algebra) (to honor [George Boole](https://en.wikipedia.org/wiki/George_Boole) and as opposed to other algebraic logics.)

In class, we used mostly the text on [Propositional Logic](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf) by the [Open Logic Project](https://openlogicproject.org/) as our reference. In the following, I will give a quick rundown of the most important concepts.

- [Chapter 1.2](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf#page=4.52): A **formula** is built from **propositional variables** and **logical connectives** such as $\wedge$ (AND), $\vee$ (OR), $\neg$ (NOT).
- [Chapter 1.5](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf#page=9.70): A **valuation** assigns to each propositional variable a **truth value**. (I like to write truth values as $0$ and $1$, in the book it is $\mathbb F$ and $\mathbb T$.) For each connective there is a [truth table](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf#page=10.46), so that one can define inductively the notion of **satisfaction** [of a formula $\phi$ by a valuation](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf#page=11.18).
- [Chapter 1.6](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf#page=11.18): A formula is **satisfiable** if it is satisfied by some valuation and a formula is a **tautology** if it is satisfied by all valuations. 

- [Chapter 4](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf#page=38.24): **Natural deduction** plays a major role in interactive theorem prover such as Lean and Isabelle and more generally in proof theory and type theory. We only skimmed this chapter and came back to it later when discussing the [Lean Intro to Logic](https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic) (which may be the best starting point to learn and practice proofs in the calculus of Natural Deduction).

- [Chapter 5](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf#page=55.24): We spend more time on **tableaux** than on natural deduction because tableaux made there way into many logic-based reasoning tools including SAT-solvers and model checkers. We worked through the [Examples in 5.4](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf#page=58.35).

The [Introduction to Logic](./0-logic.md) contains an overview and summary of the most important big ideas in logic that we need.

## References

- [Open Logic Project](https://openlogicproject.org/) 
  - [Textbooks](https://builds.openlogicproject.org/)
  - [The Open Logic Text, Complete Build](https://builds.openlogicproject.org/open-logic-complete.pdf)
  - [Propositional Logic](https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf)
