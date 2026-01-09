# Modal Logic
$\newcommand{\sem}[1]{[\![#1]\!]}$
Author: Alexander Kurz

## Idea

Modal Logic (ML) is more expressive than propositional logic (PL) and less expressive than first-order logic (FOL), in informal but suggestive notation: 

$$\rm PL \subseteq ML \subseteq FOL$$

This is of interest for various reasons:

- ML-formulas are more succinct, for example, as we will see below, the translation of the ML-formula $\Box p$  to FOL is $\forall v (wRv\Rightarrow Pv)$.[^pP]
- ML is decidable while FOL is undecidable. [^decidable]
- Logical equivalence of ML formalizes an important notion of "observational equivalence" (aka bisimilarity) of computing machines.[^observational] 
- Many problems in philosophy, linguistics and computer science can be analysed from the point of view of ML.[^philosophical]

[^pP]: We follow here a convention in much of the literature to denote atomic propositions in ML by lower case letters and one-place predicates in FOL by upper-case letters. Thus $p$ is translated to $Pv$.

[^decidable]: A logic is decidable if there is an algorithm $A$ that takes formulas $\phi$ of the logic as input and
    - always terminates,
    - returns 1 if $\phi$ is valid,
    - returns 0 if $\phi$ is not valid.
    
[^observational]: Two models $M,M'$ are logically equivalent if for all formulas $\phi$ it holds that $M$ satisfies $\phi$ if and only if $M'$ satisfies $\phi$. If $M,M'$ are models of computation there are various notions of equivalence motivated by computational considerations. Some of these equivalences are called "observational". Roughly speaking, two models are observationally equivalent if they cannot be distinguished by running them and only observing their outputs (as opposed to looking at how they are implemented). 

[^philosophical]: In these notes we only mention the question of the meaning of "necessary" and "possible". For a study of time from the point of view of modal logic, I recommend van Benthem, The Logic of Time. The work of David Lewis on Counterfactuals is another good example. I plan to add more references along these lines in the future ...

## Motivation

Superficially, modal logic adds to the propositional connectives $\wedge$ (and), $\vee$ (or), $\neg$ (not) two new connectives that allow us to take any formula $\phi$ and form two new formulas 

$$
\Box\phi\quad\quad\Diamond\phi.
$$

One of the reasons modal logic has been so important is that there are so many possible interpretations for these connectives. For example,
- $\Box\phi$ means **necessarily** $\phi$ and $\Diamond\phi$ means possibly $\phi$,
- $\Box\phi$ means **always** $\phi$ and $\Diamond\phi$ means sometimes $\phi$,
- $\Box_i\phi$ means agent $i$ **knows** $\phi$ and $\Diamond_i\phi$ means agent $i$ thinks $\phi$ is possible.

**(Temporal and Epistemic Logic)** Each of these interpretations created their own field of research. The first one dominated modal logic in the first half of the 20th century. The second one is known as [temporal logic](05-temporal-logic-spin.md) and has been playing an important role in computer science (verification, model checking) since the 1980s. The third one is known as [epistemic logic](06-epistemic-logic-smcdel.md) and continues to be cutting edge in philosophy, economics, software engineering, AI and other areas.

Besides temporal logic and epistemic logic there is also ... (insert more examples) ...

**(Fragments of First-Order Logic)** Another reason modal logic has been important is as a fragment of first-order logic. As we can see from the examples above, $\Box\phi$ is a universal quantifier (eg always) and $\Diamond\phi$ is an existential quantifier (eg sometimes). Consequently, modal logic is a fragment of first-order logic. In fact, modal logic is a fragment of first-order logic in at least two different but interesting ways:
- Modal logic is a decidable fragment of first-order logic.
- Modal logic is the bisimulation invariant fragment of first-order logic.

The first point has given rise to various generalisations of modal logic, in particular in the area of automated theorem proving. Search for [guarded fragment](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%22guarded+fragment%22+%22modal+logic%22&btnG=) for references. 

In the second point bisimulation refers to a relation of observational or behavioural equivalence of dynamic systems, which are themselves considered as "black boxes". In fact, bisimulation is the natural notion of behavioural equivalence for non-deterministic transition systems in which the states themselves are not observable but choices are. This leads us to the next item.

**(Possible Worlds Semantics)** The idea that something is necessarily true if it is true in all possible worlds is an old one. The turning point for modal logic was the mathematical formalisation of possible world semantics by Kripke:

- Kripke (1959) [A Completeness Theorem in Modal Logic](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Saul+Kripke%3A+A+Completeness+Theorem+in+Modal+Logic.+1959.&btnG=), The Journal of Symbolic Logic.
- Kripke (1963) [Semantical Analysis of Modal Logic I](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Kripke+1963+Semantical+Analysis+of+Modal+Logic+I&btnG=), Zeitschr. f. math. Logik und Grundlagen d. Math., [[pdf]](http://fitelson.org/142/kripke_1.pdf) . I recommend Section 2.1, which also contains the solution to one of the exercises below.
- Kripke (1965) [Semantical Analysis of Modal Logic II](https://scholar.google.com/scholar?q=Kripke+1965+Semantical+Analysis+of+Modal+Logic+II), Zeitschr. f. math. Logik und Grundlagen d. Math. 

There is a lot to say here, but to present the main ideas as quickly as possible I would proceed as follows (see Chapters 3.1 and 3.2 of the book referenced below).

**Definition:** Let $Prop$ be a set of 'propositional variables'. The language of modal logic is the smallest set of 'formulas' containing $Prop$ and closed under $\wedge$ , $\vee$, $\neg$, $\Box$, $\Diamond$.

**Definition:** Let $W$ be a set of 'worlds' and $R\subseteq W\times W$. Let $\sem{-}:Prop\to 2^W$ be a function assigning sets of worlds to each atomic proposition. Define
\begin{align}
\sem{\phi\wedge\phi'} &= \sem{\phi}\cap\sem{\phi'}\\
\sem{\phi\vee\phi'} &= \sem{\phi}\cup\sem{\phi'}\\
\sem{\neg\phi} &= W\setminus \sem{\phi}\\
\sem{\Box\phi} &= \{w\in W\mid \forall v\in W\,.\, wRv \Rightarrow v\in\sem{\phi}\}\\
\sem{\Diamond\phi} &= \{w\in W\mid \exists v\in W\,.\, wRv \Rightarrow v\in\sem{\phi}\}\\
\end{align}
and  

$$
(W,R)\models \phi
$$ 

iff $\sem{\phi}=W$ for all choices of $\sem{-}:Prop\to 2^W$. 

It is convenient to write 

$$
w\Vdash \phi \quad \stackrel{\rm  def}{\Longleftrightarrow} \quad w\in\sem{\phi}.
$$

The following exercise is a straightforward unvraveling of definitions:

**Exercise:** If $R$ is reflexive, then $(W,R)\models \Box p\to p$. 

A crucial observation that lets us glimpse the power of Kripke's approach is that the converse is also true. 

**Prop:** If $(W,R)\models \Box p\to p$, then $R$ is reflexive.

The proof is short once you know the trick. Try to find it for yourself before looking at the footnote.[^proof]

[^proof]: *Proof:* Let $w\in W$. Let $\sem{p}=\{v \mid wRv\}$. We know $w\Vdash\Box p$ by definition of $\sem{\Box p}$ and $w\Vdash \Box p\to p$ by assumption. It follows $w\Vdash p$, which implies $wRw$ by definition of $\sem{p}$.

The proof can be generalised to a method applying to all so-called Sahlqvist formulas and the area of modal logic is known as correspondence theory. We just look at one other basic example:

**Exercise:** $(W,R)\models \Box p\to\Box\Box p$ iff $R$ is transitive.

**Remark:** In the early 20th century modal logics were developed by philosophers from a syntactic and proof theoretic point of view. Axioms such as $\Box p\to p$ and $\Box\phi\to\Box\Box\phi$ were discovered by reading them as "necessarily p implies p" and "necessarily p implies necessarily necessarily p" and modal logics were characterised by axioms and proof rules. As far as I know the history, it came as a surprise that these axioms had such a neat semantic characterisation. 

**Exercise:** Interpret $\Box p\to p$ and $\Box p\to\Box\Box p$ from the point of view of [temporal logic](05-temporal-logic-spin.md) and [epistemic logic](06-epistemic-logic-smcdel.md).

## The Basic Theory

We have seen that modal logic comprises several independent areas (temporal logic, epistemic logic, etc) and has important overlaps with others (concurrency, multi-agent systems, automated reasoning, game theory, etc). My intention here is only to sketch out the basic theory that is important in all these fields.

Actually, instead of writing this out myself, I refer to the book "Modal Logic" by Blackburn, de Rijke, Venema. (The book treats also $n$-ary relations (the "general case", as opposed to binary relations). This generalisation is interesting for some applications but should be skipped on a first reading.)

Here is what I would consider essential for a first run through the basics of modal logic.

- 1.2: Modal Languages 
- 1.3: Models and Frames
- 1.5: Semantic Consequence
- 1.6: Normal Modal Logics
- 2.1: Invariance Results (Def 2.10 and Prop 2.14)
- 2.2: Bisimulations (up to Thm 2.20)
- 2.3: Finite Models (can be skipped on first reading)
- 2.4: The Standard Translation (up to Prop 2.47)
- 3.1: Frame Definability (Example 3.6)
- 3.2: Frame Definability and Second-Order Logic (Example 3.11)


## References

- Halpern and Vardi (1991) [Model Checking v. Theorem Proving: A Manifesto](https://scholar.google.com/scholar?q=Halpern+Vardi+Model+Checking+Theorem+Proving+Manifesto+1991), Artificial Intelligence.

- Blackburn, de Rijke, and Venema (1995) [Modal Logic](https://scholar.google.com/scholar?q=Blackburn+de+Rijke+Venema+Modal+Logic+1995), Cambridge University Press.

- Kripke (1959) [A Completeness Theorem in Modal Logic](https://scholar.google.com/scholar?q=Kripke+Completeness+Theorem+Modal+Logic+1959), The Journal of Symbolic Logic.

- Kripke (1963) [Semantical Analysis of Modal Logic I](https://scholar.google.com/scholar?q=Kripke+Semantical+Analysis+Modal+Logic+I+1963), Zeitschr. f. math. Logik und Grundlagen d. Math.

- Kripke (1965) [Semantical Analysis of Modal Logic II](https://scholar.google.com/scholar?q=Kripke+Semantical+Analysis+Modal+Logic+II+1965), Zeitschr. f. math. Logik und Grundlagen d. Math.

