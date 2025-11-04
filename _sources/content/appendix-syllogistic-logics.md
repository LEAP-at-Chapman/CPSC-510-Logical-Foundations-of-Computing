# Syllogistic Logics in Isabelle

## Introduction

The purpose of this tutorial is to give a first introduction to the proof assistant and interactive theorem prover (ITP) Isabelle. 

An ITP is used to help humans to formalize proofs. You can think of an ITP as a programming language in which programs are mathematical proofs. There are many different ITPs and Isabelle is one of the most widely used ones and has been at the cutting edge of the field for many decades. So it is definitely worth seeing an example of Isabelle in practice.

This leaves open the question of what to prove. One typical choice would be to apply Isabelle to proving the correctness of programs. This is a very good way to learn about ITPs in general and Isabelle in particular. For this I recommend the book [Concrete Semantics](http://concrete-semantics.org/).

Here I want to follow another idea. Throughout CPSC-510 Logical Foundations of Computing, we put a lot of emphasis on various software tools. I think it is time to return to their logical foundations. So here I want to apply Isabelle to logic itself. In particular, we will formalize the soundness and completeness proof of a particular logic. 

As we have discussed earlier, soundness and completeness is often the first theorem one wants to prove about any logic. We have seen, but not formally proved, that, for example, the tableaux method is sound and complete for classical propositional logic. Simlarly, there are soundness and completeness theorems for predicate logic, temporal logic, (dynamic) epistemic logic, etc.

Since our aim is a first introduction, the following question arises. What is the simplest meaningful example of a logic for which one can explain (and formalize) soundnessn and completeness?

Fortunately, this question has been asked and answered convincingly by Larry Moss in his work on syllogistic logics. 

## Setting Up

- Download the latest version of [Isabelle](https://isabelle.in.tum.de/), Isabelle 2025 at the time of writing.
- Open [AllPAreQ_noProofs.thy](../src/isabelle/AllPAreQ_noProofs.thy) from the Isabelle IDE.
- Open Moss's book [Logic From Language](../src/isabelle/Logic-From-Language-2014.pdf) and read the introduction.
- See also this [Isabelle Tutorial](../src/isabelle/Isabelle-Tutorial-2014.pdf).
  
## The Completeness Theorem

In this tutorial we will be reading Section 2.1-2.4 of the book while at the same time formally proving its theorems in Isabelle. The logic we will consider has only two rules

![](images/2025-10-30-15-43-25.png)

and the main theorem we are going to prove, the completeness theorem, is

![](images/2025-10-30-15-45-52.png)

### The Idea of the Proof

The strategy of the proof will be the following. Given $\Gamma$, we build a so-called canonical model $M_\Gamma$ from $\Gamma$ which, by construction, will have the properties that [^phi]
- $M_\Gamma\models \Gamma$
- $M_\Gamma\models \phi \Rightarrow \Gamma\vdash\phi$
  
[^phi]: We write $\phi$ instead of "All p are q" not only as an abbreviation but also to indicate that this proof strategy applies to a wide range of other logics.

Then the claim of theorem follows:

> Show: $\Gamma\models\phi \ \Rightarrow \ \Gamma\vdash\phi$
>> Assume: $\Gamma\models\phi$  
>> Show: $\Gamma\vdash\phi$  
>> Have:  $M_\Gamma\models \Gamma$  
>> Have:  $M\models \Gamma \Rightarrow M\models\phi$ for all models $M$  
>> Have:  $M_\Gamma \models \phi$  
>> Have:  $\Gamma\vdash\phi$ 
>
> Have: $\Gamma\models\phi \ \Rightarrow \ \Gamma\vdash\phi$

**Exercise/Activity**: Justify all steps.

**Remark:** Every model of $\Gamma$ satsifies all consequences of $\Gamma$. But the canonical model also refutes everything that is not derivable from $\Gamma$. This is the most important idea for completeness: If $\Gamma\not\vdash\phi$ then find a model $M$ such that $M\models\Gamma$ and $M\not\models\phi$.

### The Details of the Proof

We already showed that it suffices to prove the following.

**Lemma:** Let $\Gamma$ be a set of sentences of the form "All p are q". There is a model $M_\Gamma$ such that 
1. $M_\Gamma\models \Gamma$
2. $M_\Gamma\models \text{All p are q} \ \Rightarrow \ \Gamma\vdash\text{All p are q}$

*Proof:*

> **Define**: $p\le q$ if $\Gamma\vdash \text{All p are q}$
> 
> **Claim**: $\le$ is reflexive and transitive  
> > **Show**: $p\le p$. This follows from AXIOM    
> > **Show**: $p\le q$ and $q\le r$ implies $p\le r$. This follows from BARBARA  
> 
> **Have**: $\le$ is reflexive and transitive
>
> **Define**: $M_\Gamma$ via $[\![p]\!] = \{r \mid r \le p\}$
>
> **Claim**: $M_\Gamma\models \Gamma$
>
>> **Assume**: All p are q in $\Gamma$  
>> **Show**: $M_\Gamma\models \text{All p are q}$  
>> **Show**: $[\![p]\!]\subseteq [\![q]\!]$  
>> **Show**: $r\le p\Rightarrow r\le q$  
>> > **Assume** $r\le p$  
>> > **Have**: $p\le q$  
>> > **Have**: $r\le q$  
>> 
>> **Have**: $r\le p\Rightarrow r\le q$
>
> **Have**: $M_\Gamma\models \Gamma$.
>
> **Claim**: $M_\Gamma\models \text{All p are q} \ \Rightarrow \ \Gamma\vdash \text{All p are q}$
>
>> **Assume**: $M_\Gamma\models \text{All p are q}$  
>> **Show**: $\Gamma\vdash \text{All p are q}$  
>> **Have**: $[\![p]\!]\subseteq [\![q]\!]$  
>> **Have**: $p\in [\![q]\!]$  
>> **Have**: $p\le q$  
>> **Have**: $\Gamma\vdash \text{All p are q}$  
>
> **Have**: $M_\Gamma\models \text{All p are q} \ \Rightarrow \ \Gamma\vdash \text{All p are q}$

## The Formalization 

Since we will implement Chapters 2.1-2.4 of the book in Isabelle, it is a good a idea to arrange the windows on your screen so that you can simultaneously see the book `Logic From Language` and the Isabelle IDE with the theory `AllPAreQ_noProofs.thy` (there is also a theory with the proofs but that would be spoiling it). 

Let us start with the beginning of Chapter 2.1 from `Logic From Language`

![](images/2025-10-30-09-27-20.png) 

which is formalized in the Isabelle/HOL theory `AllPAreQ_noProofs.thy` by 

![](images/2025-10-30-09-42-42.png)

**Explanations:**

- `AllPAreQ_noProofs` is the name of the theory, which must agree with the name of the file. The filename cannot contain `-` (dash or minus).
- `typedecl` introduces a new abstract (uninterpreted) type. It has no constructors or axioms, but is guaranteed non-empty. Use it for “there exists some base set of atoms” without committing to any structure.
- `datatype` introduces an algebraic datatype with constructors (here: one constructor, All). Isabelle generates induction/recursion principles, case-splits, and simplification rules. Use when you need pattern matching, recursion, and structural induction over syntax.
- `("All _ are _ ")` declares "syntactic sugar".
- `type_synonym` does not create a new type. It only gives a shorter, domain-specific name to an existing type expression. Use for readability and conveying intent.
- `definition` introduces a constant by conservative definitional equality. Use for naming predicates and functions defined by equations. The left-hand side cannot pattern-match; use "where" and pattern-match inside the right-hand side (e.g., via let or case).
- `fun` defines functions by pattern matching and (if needed) recursion, generating simplification rules automatically.

**Exercise/Activity:** Add a lemma stating that `M ⊨ All p are q` iff `M p ⊆ M q`. [^lemma-allpareq-solution]

[^lemma-allpareq-solution]: 
    ```
    lemma all_p_are_q:
      fixes M :: "'a model" and p q :: atProp
      shows "(M ⊨  All p are q) ⟷ (M p ⊆ M q)"
      by auto
    ```
    - `fixes` introduces type constraints
    - The unicode characters can by typeset in the IDE with `\<models>` and `\<longleftrightarrow>` 

Let us now continue in the book `Logic From Language` with

![](images/2025-10-30-09-46-10.png)

which is in the Isabelle/HOL theory `AllPAreQ_noProofs.thy` 

![](images/2025-10-30-09-46-50.png)

**Exercise/Activity:** Prove the lemma using sledgehammer.

... tbc ...






