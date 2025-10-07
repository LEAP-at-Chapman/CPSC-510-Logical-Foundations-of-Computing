---
title: Intro to Modal Logic

---

# Intro to Modal Logic

## Preliminary Remarks

These notes assume that the reader knows the basics of propositional logic (PL) and predicate logic or, more specifically, first-order logic (FOL). Modal Logic (ML) is more expressive than PL and less expressive than FOL, in informal but suggestive notation: 

$$\rm PL \subseteq ML \subseteq FOL$$

This raises the question why we should be interested in modal logic at all. Here are some reasons:

- ML-formulas are more succinct, for example, as we will see below, the translation of the ML-formula $\Box p$  to FOL is $\forall v (wRv\Rightarrow Pv)$.[^pP]
- ML is decidable while FOL is undecidable. [^decidable]
- Logical equivalence of ML formalizes an important notion of "observational equivalence" of computing machines.[^observational] 
- Many philosophical and  linguistic problems can be understood from the point of view of ML.[^philosophical]

[^pP]: We follow here a convention in much of the literature to denote atomic propositions in ML by lower case letters and one-place predicates in FOL by upper-case letters. Thus $p$ is translated to $Pv$.

[^decidable]: A logic is decidable if there is an algorithm $A$ that can takes formulas $\phi$ of the logic as input and
    - always terminates,
    - returns 1 if $\phi$ is valid,
    - returns 0 if $\phi$ is not valid.
    
[^observational]: Two models $M,M'$ are logically equivalent if for all formulas $\phi$ it holds that $M$ satisfies $\phi$ if and only if $M'$ satisfies $\phi$. If $M,M'$ are models of computation there are various notions of equivalence motivated by computational consdirations. Some of these equivalences are called "obserational". Roughly speaking, two models are observationally equivalent if they cannot be distinguished by running them an only observing their outputs (as opposed to looking at how they are implemented). 

[^philosophical]: In this notes we only mention the question of the meaning of "necessary" and "possible". For a study of time from the point of view of modal logic, I recommend van Benthem, The Logic of Time. The work of David Lewis on Counterfactuals is another good example. I plan to add more references along these lines in the future ...

## Modal Logic

### The Idea

We start with ordinary propositional logic augmented by unary connectves, $\Diamond$ and $\Box$. That is, if $\phi$ is a modal formula then so are
$$\Diamond\phi \ \ \ \ \text{ and } \ \ \ \ \Box\phi$$

Modal logic has roots in Aristotle. Where he says "neccessarily $\phi$" we now write $\Box\phi$. Leibniz said that $\phi$ is neccessary if $\phi$ holds in all possible worlds.[^Leibniz] In modern notation, $\Diamond\phi$ holds "here and now" if $\phi$ holds in **some** possible (alternative) world. $\Box\phi$ holds "here and now" if $\phi$ holds in **all** possible (alternative) worlds. 

[^Leibniz]: What is the original source for this claim? I only had a quick look and didnt quite nail it ... [Theodicy](https://gutenberg.org/cache/epub/17147/pg17147-images.html): ![](https://hackmd.io/_uploads/rkV9x04pn.png)

Kripke formalized this idea mathematically. This is known today as possible world semantics or Kripke semantics, which we will now outline. The fundamental idea is to distinguish, for a given formula $\phi$, between the following.

- $\phi$ holds in "the actual" world,
- $\phi$ holds in all "alternative" worlds,
- $\phi$ holds in all worlds.

We start with a set $W$ of 'worlds'. Formulas are evaluated in worlds and we write

$$w\Vdash \phi$$

to say that $\phi$ holds in $w$. (The world $w$ plays the role of what we called "here and now" above and also the "actual" world.)

To define the meaning of $\Diamond$ and $\Box$ we need to formalize "possible". This is done using the idea of alternative worlds:

- $w\Vdash\Diamond\phi$ if there is an alternative $v$ world where $v\Vdash\phi$. 
- $w\Vdash\Box\phi$ if $v\Vdash\phi$ for all alternative worlds $v$. 

Finally, a formula $\phi$ is *valid* if $w\Vdash\phi$ for all $w\in W$. 

The next step is to model mathematically the idea of alternative worlds.

### Kripke Structures

To formalize the idea of alternative worlds, we let $R\subseteq W\times W$ be a relation on $W$. [^relation] We read 

$$wRv$$ 

as $w$ has possible alternative $v$. 

[^relation]:$W\times W$ denotes the set of all pairs (of elemements of $W$). Thus, $R\subseteq W\times W$ says that $R$ is a set of pairs. To say that a particular pair $(w,v)$ is in $R$ we may write one of the following: $(w,v)\in R$, $R(w,v)$, $Rwv$ or $wRv$.

**Remark 1:** (modal logics) One reason this is a powerful concept is that $wRv$ can be interpreted in many different ways. For example one can obtain different logics from reading $\Box\phi$ as "I know $\phi$" or "always $\phi$" or "tomorrow $\phi$" or "neccessarily $\phi$" or "I believe $\phi$" or etc. 

There is one more ingredient missing. We have now a set $W$ of worlds and a relation between worlds $R$. We also need a relation between worlds and atomic propositions to record the facts that hold in each world. For this we use a relation

$$Fact \subseteq W \times AtProp$$

where $AtProp$ is the set of atomic propositions (basic facts). We collect all this data in one structure, a so-called Kripke model,

$$(W,R,Fact)$$

**Example:** Think of every world $w$ as a computer at a given point in time. For each bit in memory we have a fact $p$. $(w,p)\in Fact$ if the value of the bit is $1$ (and $(w,p)\notin Fact$ if the value of the bit is $0$). Starting from this idea, one can build different models of computation depending on how one interprets the accessibility relation $R$. For example: (i) $R$ as time: $wRv$ if the computer starts computing in $w$ and finishes computing in $v$. (ii) $R$ as a network: $wRv$ if computer $w$ can send a message to $v$. (iii) $R$ as indistuingishability: $wRv$ is the user (or programmer) cannot distinguish $w$ and $v$ (for example because the content of the memory is shielded from inspection).

The meaning of $\Diamond$ and $\Box$ can now be defined as follows.

**Definition of $\Vdash$:** Fix a Kripke model $(W,R,Fact)$ and let $p$ range over atomic propositions and let $\phi$ range over modal formulas.

$$ w\Vdash p \quad\Leftrightarrow\quad (w,p) \in Fact$$

$$ w\Vdash \phi\to\psi \quad \Leftrightarrow \quad w\Vdash \phi \textrm{ implies } w\Vdash \psi$$

$$ w\Vdash \neg\phi \quad \Leftrightarrow \quad \textrm{not} (w\Vdash \phi)$$

$$w\Vdash \Diamond\phi \ \ \Leftrightarrow \ \ \text{ there is } v\in W \text{ such that } wRv \text{ and } v\Vdash \phi$$

$$w\Vdash \Box\phi \ \ \Leftrightarrow \ \ \text{ for all } v\in W \text{ if } wRv \text{ then } v\Vdash \phi$$

We say that $\phi$ holds in a Kripke model if 

$$(W,R,Fact)\models \phi \ \ \Leftrightarrow \ \ w\Vdash\phi \textrm{ for all } w\in W$$

We say that $\phi$ holds in $(W,R)$ if 
$$(W,R,Fact)\models \phi \textrm{ for all } Facts$$


**Activity:** We have seen the semantics of atomic propositions and $\Diamond,\Box$. Can you write out the semantics for $\wedge,\vee,\neg,\to$ in this style?

**Remark 2:** (standard translation) Looking again at the definition of the meaning of $\Diamond$ and $\Box$, we can read them as special cases of the quantifiers in predicate logic:

\begin{align}
(\Diamond\phi)(w) & = \exists v . wRv \wedge \phi(v)\\
(\Box\phi)(w) & = \forall v . wRv \to \phi(v)
\end{align}

This is called the standard translation of modal logic to first-order logic.

## Discussion

So what is the deal? Why are we interested in modal logic? There are many reasons, some of which are:

- Modal logic formulas do not have variables, so modal logic, while having some of the expressiveness of predicate logic is much simpler from a syntactic point of view.
- The idea of possible worlds is very powerful and flexible with many applications in philosophy, linguistics, computer science.
- Modal logic is a *decidable* fragment of first-order logic. This means that while there is no algorithm that would decide whether a first-order formula is valid, there is such an algorithm for modal formulas.
- Modal logics have a beautiful *model theory* that is closely related but really quite different from first-order model theory.[^bisimilarity] This model theory has many applications to philosopical logic and to computer science.
- There is a powerful **correspondence theory** that explains when one can use modal formulas to express conditions on the alternative relation $R$. For example, $\Box p \to p$ is valid wrt $(W,R)$ if and only if the relation $R$ is reflexive. Similarly, $\Box p \to \Box\Box p$ is valid wrt $(W,R)$ iff the relation is transitive.[^reflexive] Referring back to the definitions above we can write this as 

    $$(W,R)\models \Box p\to p \ \ \textrm{ iff } \ \ R \textrm{ reflexive}$$

    and similarly for the other case.

[^reflexive]: $R$ is reflexive 

**Activity:** (time) Let $W$ be the natural numbers and let $R$ be $\le$. What is the meaning of $\Diamond,\Box$ in this Kripke model.

**Activity:** (knowledge) Let $W$ be a set and let $R$ be an equivalence relation. Think about a situation where you do not have compete knowledge about the world. Interprete  $wRv$ as saying that your knowledge about the facts does not all you to distinguish between $w$ and $v$. What is the meaning of $\Diamond,\Box$ in this Kripke model?

[^bisimilarity]: A central notion is bisimilarity: Two worlds in a Kripke model are logically indistuinguishable if and only if they are bisimilar. For example, the model that has only one world $w$ with $wRw$ is bisimular to the model that has infinitely many worlds, one for each natural number $n$ and has the relation $n\,R\,n+1$.

