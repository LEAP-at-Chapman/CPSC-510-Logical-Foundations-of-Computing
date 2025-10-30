# Higher-Order Logic with Isabelle/HOL

*Author: Spencer Au*

## Contents

| Section | Title |
|---:|---|
| **10.1** | [Idea](#sec0-10-1) |
| **10.2** | [Basic Theory](#sec0-10-2) |
| **10.3** | [Tool (Installation, First Example, First Exercise)](#sec0-10-3) |
| **10.4** | [Introductory Examples](#sec0-10-4) |
| **10.5** | [The Landscape of Tools](#sec0-10-5) |
| **10.6** | [Algorithms](#sec0-10-6) |
| **10.7** | [Benchmark and Competitions](#sec0-10-7) |
| **10.8** | [Applications in Industry](#sec0-10-8) |
| **10.9** | [Case Studies](#sec0-10-9) |
| **10.10** | [History](#sec0-10-10) |
| **10.11** | [Current Development, Research Challenges, Conferences and Workshops](#sec0-10-11) |
| **10.12** | [References](#sec0-10-12) |
| **10.13** | [Suggestions for Future Work](#sec0-10-13) |

## Topics

- Higher-order logic foundations
- Function types and quantification
- Isabelle/HOL advanced features
- Theorem proving strategies
- Industrial theorem proving

## 10.1 Idea and Introduction {#sec0-10-1}
WIP

This chapter extends to higher-order logic in Isabelle/HOL, showing how to reason about functions as first-class objects and exploring the foundations of modern theorem proving.

Higher-order logic (HOL) extends the capabilities of first-order logic (FOL) by allowing quantifiers (such as $ \forall x $ and $ \exists x $) to range over functions and predicates, not just individual elements. In addition, functions can be passed as arguments to other functions, returned as results, and manipulated just like any other data type. This enables more expressive statements about the properties of functions and their relationships.

## 10.2 Basic Theory {#sec0-10-2}
WIP

<!-- basic setup - need to add much more but this is just basics/scaffolding -->

### 10.2.1 First Order Logic 
WIP
$ \forall x $ and $ \exists x$ where x is a variable/individual element

In higher order logic, we extend this to $ \forall f(x) $ and $ \exists f(x) $, where x is a function that takes x as an input

### 10.2.2 (Explicit) Type System
WIP

<!-- – Andrews (2002) Sections 1–2 (“Type theory basics”)
– Church (1940) A Formulation of the Simple Theory of Types 
Church Text is more relevant to history section-->

### 10.2.3 Lambda Abstraction
WIP

<!-- Read:
– Paulson, Logic and Computation, ch. 2
– Nipkow et al., Concrete Semantics, §2.1–2.3 -->

### 10.2.4 Rules of Inference

The basic rules of inference of $\mathcal{F}^w$, where $\mathcal{F}$ is a system of $\mathcal{w}$-order logic which has all finite order logics as subsystems:

1) **Modus Ponens** From $A$ and $A \to B$ to infer $B$.
2) **Generalization** From $A$ to infer $\forall x\,A$, where x is a variable of any type

<!-- *Adapted from Andrews, 2002*[^andrews2002] using modern logic convention. -->

*Adapted from* {cite}`Andrews2002` using modern logic convention.



### 10.2.5 Axiom Schemata

The axiom schemata of $\mathcal{F}^w$ are:

1) $A \lor A \to A$
2) $A \to (B \lor A)$
3) From $A \to (B \to C)$, infer $ (A \to B) \lor C$
4) **Universal Instantiation**
    $\forall x_\tau\,A \to A[y_\tau / x_\tau]$, where $y_\tau$ is a variable or constant of the same type as the variable $x_\tau$, and $y_\tau$ is free for $x_\tau$ in $A$.
  
    Basically, from $\forall x_\tau\,A$, we may infer $A[y_\tau / x_\tau]$, meaning that if $A$ holds for all $x_\tau$, then it also holds for any particular instance $y_\tau$ of the same type.

5) **Quantifier Distribution**
    $\forall x(A \lor B) \to (A \lor \forall x\,B)$, where $x$ is any variable not free in $A$.

    This means that if $(A \lor B)$ holds for all $x$, and $A$ does not depend on $x$, then either $A$ holds or $B$ holds for all $x$.

6) **Comprehension Axioms**

    - *0-ary case (a proposition/Boolean) that names a theorem/statement*.  
    $ \exists u_{\mathbf{o}}\;[\,u_{\mathbf{o}} \leftrightarrow A\,] $
    where $u_{\mathbf{o}}$ does not occur free in $A$.  
    
    - *n-ary case (a predicate/function of arity n) that names a property/relation*.  
    $\exists u_{(\tau_1\ldots\tau_n)}\;
    \forall v^{1}_{\tau_1}\cdots \forall v^{n}_{\tau_n}\,
    \big[\,u_{(\tau_1\ldots\tau_n)}(v^{1}_{\tau_1},\ldots,v^{n}_{\tau_n})
    \leftrightarrow A\,\big]$
    where $u_{(\tau_1\ldots\tau_n)}$ does not occur free in $A$, and $v^{1}_{\tau_1},\ldots,v^{n}_{\tau_n}$ are distinct variables.

    - These axioms allow us to define new symbols that stand for existing formulas.  
    In the 0-ary case, a new propositional constant $u_{\mathbf{o}}$ can name a statement $A$.  
    In the n-ary case, a new predicate $u_{(\tau_1\ldots\tau_n)}$ can be introduced so that $u(v^1,\ldots,v^n)$ is true exactly when $A$ holds for those arguments.

7) **Axioms of Extensionality**
    - *0-ary case (a proposition/Boolean) that names a theorem/statement*.  
    $(x_{\mathbf{o}} \leftrightarrow y_{\mathbf{o}}) \to (x_{\mathbf{o}} = y_{\mathbf{o}})$

    - *n-ary case (a predicate/function of arity n) that names a property/relation*.  
    $\forall w^{1}_{\tau_1} \ldots \forall w^{n}_{\tau_n} [(x_{(\tau_1 \ldots \tau_n)}w^{1}_{\tau_1}\ldots w^{n}_{\tau_n}) \leftrightarrow (y_{(\tau_1 \dots \tau_n)} w^{1}_{\tau_1} \ldots w^{n}_{\tau_n})] \to (x_{(\tau_1 \ldots \tau_n)} = y_{(\tau_1 \ldots \tau_n)}) $

    - These axioms state that two expressions are equal if and only if they behave identically in that their output result is the same in all evaluations. This formalizes the idea that in higher order logic, equality is extensional (based on meaning and behavior) rather than syntactic (based on form).




<!-- *Adapted from Andrews, 2002*[^andrews2002] using modern logic convention. -->

*Adapted from* {cite}`Andrews2002` using modern logic convention.

<!-- [^andrews2002]: Andrews, *An Introduction to Mathematical Logic and Type Theory*, Springer 2002. [Springer Link](https://link.springer.com/book/10.1007/978-94-015-9934-4) -->



## 10.3 Tool (Installation, First Example, First Exercise) {#sec0-10-3}

### 10.3.1 Installation

<!-- Looks like isabelle is a program we can just download normally via exe/dmg etc instead of messing around with command line or using `apt/brew` -->

[Installation Link for Isabelle](https://isabelle.in.tum.de/)

<!-- probably have detailed walkthrough for windows, macos, and ubuntu with pictures etc all that with pictures and all that pretty stuff (remove if it results in the chapter being too long) -->

Isabelle processes the theory document incrementally in the background, meaning that there is no additional "compile" or "run" step. As you type in lines and commands, the background system will check them and automatically update the proof state and any relevant error reports. Just go line by line, or command by command in order to check the related output.

### 10.3.2 First Example

Create a file called `hello_world.thy`, which will be an introductionary "hello world" type theory to onboard the basics of Isabelle and the HOL language. The beginning of the file should look like this:

```isabelle
theory hello_world 
    imports Main
begin

THEORY BODY

end
```

`theory hello_world` declares the theory name and **must** exactly match the .thy filename. For example, if the file is called test.thy, then you would have `theory test`

`imports Main` tells it to import another theory; in this case that is Main.thy, which includes support for natural numbers, lists, and basic arithmetic

`begin` is the entry point into the theory body, while `end` is the end point of the theory body

In order to declare a constant and assign it a value, we use this general structure:

```isabelle
definition NAME :: TYPE where 
    "NAME = VALUE"
```

In our specific `hello_world.thy`, we will be assigning the value of "Hello World!" to a constant named "greeting" of the type "string".

```isabelle
definition greeting :: string where
    "greeting = ''Hello World!''"
```

In Isabelle, using the `definition` keyword introduce a constant, not a mutable variable. This means that the value of greeting will be fixed, equialent to "Hello World!" and cannot change within this theory.

Next we will declare a new theorem using the `lemma` command. Note that the **lemma** and **theorem** are intechangeable within Isabelle. The general structure of a lemma declaration is:

```isabelle
lemma LEMMA_NAME: "GOAL"
    by (PROOF_METHOD)
```

For our Hello World theory, we will be declaring a theorem called "hello_greeting" that will be proving that the value of "greeting" is indeed "Hello World!"

```isabelle
lemma hello_greeting: "greeting = ''Hello World!''"
    by (simp add: greeting_def)
```

The `simp` command invokes Isabelle's simplify method, which attempts to reduce the goal by using rewrite rules and known equalities. Using `add: greeting_def` tells simp to use the definition theorem greeting_def (automatically generated by the defition declaration of greeting) as an extra rewrite rule to simplify the goal.

The complete theory for hello_world.thy looks like this:

```isabelle
theory hello_world 
    imports Main
begin

definition greeting :: string where
    "greeting = ''Hello World!''"

lemma hello_greeting: "greeting = ''Hello World!''"
    by (simp add: greeting_def)

end
```

### 10.3.3 First Exercise

<!-- do not need to have the explicit answer -->

For the first exercise, we will be proving the associative and commutative properties of a custom `add` function in Isabelle. This exercise comes from Exercise 2.2 of [Concrete Semantics Exercises](http://www.concrete-semantics.org/Exercises/exercises.pdf)
<!-- i need to change this to a footnote or something that links to references at the end -->

WIP - i'm still porting over my code in isabelle and want to refine the explanations as well as make it easy to follow and understand

The custom add function is defined here:
```isabelle
fun add :: "nat ⇒ nat ⇒ nat" where
    "add 0 n = n" |
    "add (Suc m) n = Suc(add m n)"
```

We use 2 lemmas to prove each part of the exercise, namely:
```isabelle
lemma add_assoc: "add (add m n) p = add m (add n p)"
lemma add_comm: "add m n = add n m"
```

#### General Proof Structure for a Proof by Induction

Isabelle provides a general structure for how to approach and construct your proof. For this exercise, we will be using a proof by induction; first by proving a base case, and then by proving the sucessor case by using the induction hypothesis.

We start the proof by adding the command `proof(induction m)` after the `lemma` command. When we examine the output of this, we find that Isabele actually provides us with the overall goal, subgoals (such as the base case and successor cases), and the general proof outline

For example, for the associative property lemma, we get this:
```isabelle
goal (2 subgoals):
 1. add (add 0 n) p = add 0 (add n p)
 2. ⋀m. add (add m n) p = add m (add n p) ⟹ add (add (Suc m) n) p = add (Suc m) (add n p) 
Proof outline with cases:
  case 0
  then show ?case sorry
next
  case (Suc m)
  then show ?case sorry
qed
```

<!-- We first start off by proving the associative property: -->
#### Associative Property Proof

We first start off by proving the associative property of addition, and we do this by declaring the lemma and its goal:
```isabelle
lemma add_assoc: "add (add m n) p = add m (add n p)"
```
We then add the type of proof, which in this case will be a simple induction proof via the `proof` command:
```isabelle
proof (induction m) 
```
We then set the base case with:
```isabelle
  case 0
```
which will set `m = 0` as the base case, and then will update the goal to:
`add (add 0 n) p = add 0 (add n p)`

We then use:
```isabelle
  show ?case by simp
```

in order to simplify that new goal to:
`add n p = add n p`

Next, we perform the inductive step in order to prove that if the associative property holds for m, it must also hold for it's successor of  `Suc m`

We introduce the inductive step:
```isabelle
next
  case (Suc m)
```

This creates 2 things:
  - A goal of: `add (add (Suc m) n) p = add (Suc m) (add n p)`
  -	An induction hypothesis (Suc.IH) that assumes the property holds for m:
    `add (add m n) p = add m (add n p)`

<!-- We then use the recursive definition of add to expand both sides of the equation, and apply the induction hypothesis to simplify the inner equality. This shows that the associative property also holds for the successor case: -->
```isabelle
  show ?case by (simp add: Suc.IH)
```

Here, simp first expands both sides of the equation using the recursive definition
`add (Suc m) n = Suc (add m n)`
This reduces the goal to
`Suc (add (add m n) p) = Suc (add m (add n p))`
The induction hypothesis (Suc.IH) is then applied to replace
`add (add m n) p` with `add m (add n p)`,
making both sides identical.
The expression simplifies to Suc (...) = Suc (...) and completes the inductive step.

The full lemma proof for associativity is here:
```isabelle
lemma add_assoc: "add (add m n) p = add m (add n p)"
proof (induction m) 
  case 0
  show ?case by simp
next
  case (Suc m)
  show ?case by (simp add: Suc.IH)
qed
```


#### Communative Property Proof
Next, to prove the communative property, we will first prove 2 helper lemmas:
```isabelle
lemma add_0_right: "add m 0 = m"
lemma add_Suc_right: "add m (Suc n) = Suc (add m n)"
```

These proofs follow the same general format for induction:
```isabelle
lemma add_0_right: "add m 0 = m"
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  show ?case by (simp add: Suc.IH)
qed

lemma add_Suc_right: "add m (Suc n) = Suc (add m n)"
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  show ?case by (simp add: Suc.IH)
qed
```

With the helper lemmas proven, we will use them to prove the commutative property

```isabelle
lemma add_comm: "add m n = add n m"
proof (induction m)
  case 0
  show ?case
    by (simp add: add_0_right)
next
  case (Suc m)
  show ?case
    by (simp add: Suc.IH add_Suc_right)
qed
```

where we use the add_0_right lemma in the base case and then the add_Suc_right lemma in the inductive step.

*This exercise was provided by Exercise 2.2 in {cite}`concreteSemanticsExercises`*

## 10.4 Introductory Examples {#sec0-10-4}

<!-- need to talk to Kurz about what should be in first exmaple, first exercise, and in introductory examples -->

<!-- show something interesting about tool, logic, etc and can be digested and understood with minimum experience -->


## 10.5 The Landscape of Tools {#sec0-10-5}

WIP

### 10.5.1 Interactive Proof Assistants

HOL4 (classic HOL)

Coq (constructive higher-order/type theory)

Lean 4 (modern dependent/HOL hybrid)


### 10.5.2 Automated Higher Order Prover

Leo III

Satallax



## 10.6 Algorithms {#sec0-10-6}


## 10.7 Benchmark and Competitions {#sec0-10-7}


## 10.8 Applications in Industry {#sec0-10-8}


## 10.9 Case Studies {#sec0-10-9}


## 10.10 History {#sec0-10-10}


## 10.11 Current Development, Research Challenges, Conferences and Workshops {#sec0-10-11}


## 10.12 References {#sec0-10-12}

- [Isabelle/HOL](https://isabelle.in.tum.de/)
- [Concrete Semantics](http://www.concrete-semantics.org/)
- [Concrete Semantics Exercises](http://www.concrete-semantics.org/Exercises/exercises.pdf)
- [Isabelle YouTube Tutorial by FDS 2020](https://www.youtube.com/@FDS-hs2uc/videos)
- [Syllogism Slides from Nate Moss](https://logic.berkeley.edu/colloquium/MossSlides.pdf)

<!-- - [Andrews - An Introduction to Mathematical Logic and Type Theory](https://link.springer.com/book/10.1007/978-94-015-9934-4) -->

<!-- - <a id="ref-andrews2002">[1]</a> Andrews, *An Introduction to Mathematical Logic and Type Theory*, 2002. [Springer Link](https://link.springer.com/book/10.1007/978-94-015-9934-4) -->

[^andrews2002]: Andrews, *An Introduction to Mathematical Logic and Type Theory*, Springer 2002. [Springer Link](https://link.springer.com/book/10.1007/978-94-015-9934-4) -->


## 10.13 Suggestions for Future Work {#sec0-10-13}

