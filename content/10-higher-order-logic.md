# Higher-Order Logic with Isabelle/HOL

*Author: Spencer Au*


<!-- ## Topics

- Higher-order logic foundations
- Function types and quantification
- Isabelle/HOL advanced features
- Theorem proving strategies
- Industrial theorem proving -->

## Idea and Introduction
WIP

Topics

- Higher-order logic foundations
- Function types and quantification
- Isabelle/HOL advanced features
- Theorem proving strategies
- Industrial theorem proving

This chapter extends to higher-order logic in Isabelle/HOL, showing how to reason about functions as first-class objects and exploring the foundations of modern theorem proving.

Higher-order logic (HOL) extends the capabilities of first-order logic (FOL) by allowing quantifiers (such as $ \forall x $ and $ \exists x $) to range over functions and predicates, not just individual elements. In addition, functions can be passed as arguments to other functions, returned as results, and manipulated just like any other data type. This enables more expressive statements about the properties of functions and their relationships.

## Basic Theory

<!-- basic setup - need to add much more but this is just basics/scaffolding -->

### From First Order Logic to HOL

WIP
<!-- 
	•	HOL is typed
	•	Functions are first-class
	•	Quantifiers range over all types
	•	λ-abstraction builds function terms
	•	Application is part of the syntax
	•	Equality at every type
   -->

<!-- Andrews Ch 1-2, https://isabelle.in.tum.de/library/HOL/HOL/document.pdf section 2,  -->


$ \forall x $ and $ \exists x$ where x is a variable/individual element

In higher order logic, we extend this to $ \forall f(x) $ and $ \exists f(x) $, where x is a function that takes x as an input

These are the principal features which are added to first-order logic in order to obtain this formulation of higher-order logic:<sup><a href="#andrews2002">[3]</a></sup>

  1. Variables of arbitrarily high orders

  2. Quantification on variables of all types

  3. Comprehension Axioms

  4. Axioms of Extensionality

conclusion line of how HOL = typed + $\lambda$ + functional programming

### (Explicit) Type System

<!-- – Andrews (2002) Sections 5 (“Type theory basics”)
– Church (1940) A Formulation of the Simple Theory of Types 
Church Text is more relevant to history section-->

*Andrews, 2002 Section 5.1*<sup><a href="#andrews2002">[3]</a></sup> provides us with $Q_0$, which is a modified formalization of Church's simple theory of types<sup><a href="#Church_TypeTheory">[10]</a></sup>, in which equality is taken as the basic primitive notion. The semantics of $Q_0$ describe how types denote sets, how function types denote function spaces, and how terms receive meaning under assignments. 

This section introduces the purely syntactic component of simple type theory:
the formation of types, variables, primitive symbols, and well-formed expressions.

**Type Formation Rules:**

$(\alpha, \beta, \gamma, \ldots )$ are syntactical variables that range over type symbols, defined inductively:
  - $\iota$ is a type symbol for individuals
  - $o$ is a type symbol for truth values
  - If $\alpha$ and $\beta$ are types symbols, then ($\alpha\beta$) is a type symbol denoting the type of functions from elements of type $\beta$ to elements of type $\alpha$

**Variables Indexed by Type:**

  - For each type symbol $\alpha$, a denumerable list of variables of type $\alpha$:
    $f_\alpha, g_\alpha, h_\alpha \ldots x_\alpha, y_\alpha, z_\alpha, f^1_\alpha, g^1_\alpha \ldots z^1_\alpha, f^2_\alpha \ldots$

**Primitive Syntactic Forms (of $Q_0$):**

  - Improper symbols include  [ ] and $\lambda$

  <!-- Andrews $Q_0$ is fairly barebones in terms of logical constants, as he only provides us with 2 main terms: $Q_{((o\alpha)\alpha)}$ and $u_{(\iota(o\iota))}$ where: -->

  - $Q_{((o\alpha)\alpha)}$ is the equality predicate at type $\alpha$, which is a function that takes 2 $\alpha$ arguments and returns a truth value

  - $u_{(\iota(o\iota))}$ is the description/selection operator (also known as the Hilbert $\epsilon$-operator), which returns an element of type $\iota$ that satisfies a predicate $p : \iota \to o$ if one exists

**Nonlogical Constants:**

  - Nonlogical constants of various types may be included depending on the particular formalized language

**Formation of Well-Formed Expressions (wff's):**

A wff$_\alpha$ (a well-formed expression of type $\alpha$) is defined inductively as follows:

  - Any primitive variables or constant of type $\alpha$ is a wff$_\alpha$

  - If $A_{\alpha\beta}$ is a wff of function type ($\beta \to \alpha$) and $B_\beta$ is a wff$_\beta$, then [$A_{\alpha\beta} B_\beta$] is a wff$_\alpha$ (function application).

  - If $A_\alpha$ is a wff and $x_\beta$ is a variable, then $\lambda x_\beta A_\alpha$ is a wff of type $\alpha\beta$ ($\lambda$-abstraction; see Section 10.2.3).

### $\lambda$-Abstraction and Application

$\lambda$-abstraction is the syntax used to define a function by naming its argument. For example, $\lambda x .\; t$ denotes the function that takes an input x as argument input and returns the expression t as output. In other words, it is the function that maps $x$ to $t$, so $x \mapsto t$. Simply put, $\lambda$ is an operator that is used to denote and represent functions.

Another example provided by the Stanford Encyclopedia of Philosophy (SEP)<sup><a href="#Stanford_LambdaCalc_TypeTheory">[12]</a></sup> is more ingrained in natural language and may be easier to understand: $\lambda x .\; x\text{ is a Polish diplomat and } x \text{ is a great pianist}$. If we set the input of x to an arbitrary person, say $x = $ Fred, then this can be read as “Fred is both a Polish diplomat and a great pianist”.

HOL's $\lambda$-abstraction constructs a function. If $x:\alpha$ and $t:\beta$, then $\lambda x .\; t: \alpha \Rightarrow \beta$.
(Basically, If $x$ has type $\alpha$ and $t$ has type $\beta$, then $\lambda x .\; t$ has type $\alpha \Rightarrow \beta$). Function application is typed accordingly. If $f:\alpha \Rightarrow \beta$ and $x:\alpha$, then $f x:\beta$. Applying a function of type $\alpha \Rightarrow \beta$ to an argument of type $\alpha$ produces a result of type $\beta$.

**Andrews uses the notation of $\alpha\beta$, which is equivalent to Isabelle/HOL's notation of $\alpha \Rightarrow \beta$. They both mean the same thing: the type of a function that takes an argument of type $\alpha$ and returns a value of type $\beta$*

In $\beta$-reduction, the idea is that application is the same as substitution.
For example, if we have $[\lambda x . \; x + 1]0$, we apply $\beta$-reduction by substituting in 0 for x, so we get $[\lambda x . \; x + 1]0 \to_\beta 0 + 1 = 1$.<sup><a href="#Kurz_LambdaSemantics">[14]</a></sup>

In a Curried function, we basically turn a multiple argument function by nested single input $\lambda$ functions; this process is referred to as "Currying" the function. For example, if we have a function add(x, y) that takes in both the inputs of x and y, then we Curry the function by turning it into $\lambda x . \; (\lambda y . \; x + y)$<sup><a href="#Kurz_LambdaSemantics">[14]</a></sup>

<!-- (Currying): To replace a function in two arguments by a function that takes one argument and returns a function that takes the second argument is called "currying" after the mathematician and logician Haskell Curry.<sup><a href="#Kurz_LambdaSemantics">[14]</a></sup> -->

**In Isabelle/HOL, $\lambda$-abstraction is written as `%x. t` with a `%` instead of the $\lambda$ symbol.*

**There are a plehtora of resources to find supplementary information about $\lambda$-calculus and abstraction. In addition to the HackMD pages by Alexander Kurz<sup><a href="#Kurz_LambdaSemantics">[14]</a></sup> <sup><a href="#Kurz_LambdaSyntax">[15]</a></sup>, other good references are Chapters 3.1 and 3.2 of **Logic and Computation**<sup><a href="#Paulson_LCF">[11]</a></sup> and the aforementioned Section D.1 of the SEP<sup><a href="#Stanford_LambdaCalc_TypeTheory">[12]</a></sup>*


### Logical Constants in HOL

<!-- https://isabelle.in.tum.de/library/HOL/HOL/document.pdf section 2, Andrews Logical Constants of Q0	•	§51(c): Q_{(αα)o} and u_{(ιo)ι} and the explanations. ￼ -->

<!-- equality: = :: α ⇒ α ⇒ bool

Hilbert choice: ε :: (α ⇒ bool) ⇒ α

standard connectives: ¬, ∧, ∨, ⟶, ↔

quantifiers defined via λ (∀x. P x) -->

Logical constants are built in symbols that define the logical structure of the system and are not defined by the user. Isabelle/HOL provides a standard set of such constants, summarized in Sections 2.1.1 of *Concrete Semantics*.<sup><a href="#ConcreteSemantics">[1]</a></sup> 

<!-- base boolean constants: (true and false) -->
- **Base Boolean Constants**: simplest terms of type bool, representing truth values
  - *True* : bool
  - *False* : bool

<!-- logical connectives (such as not, and, or, ->, etc) -->
- **Logical Connectives**: curried functions that return a Boolean
  - **$\neg$**: $bool \Rightarrow bool$
  - **$\land$**: $bool \Rightarrow bool \Rightarrow bool$
  - **$\lor$**: $bool \Rightarrow bool \Rightarrow bool$
  - **$\to$**: $bool \Rightarrow bool \Rightarrow bool$
<!-- 
Terminology (Currying): To replace a function in two arguments by a function that takes one argument and returns a function that takes the second argument is called "currying" after the mathematician and logician Haskell Curry.

https://hackmd.io/@alexhkurz/H1e4Nv8Bv -->

<!-- equality: = -->
- **Equality**: infix function $=$ of type $\alpha \Rightarrow \alpha \Rightarrow bool$

<!-- quantifiers: $\forall x$ and $\exists x$ -->
- **Quantifiers**: $\forall x. \; Px$ and $\exists x. \; Px$


### Deductive Core of HOL

Natural Deduction Rules
Chapter 5 of *Isabelle/HOL: A Proof Assistant for Higher‑Order Logic* <sup><a href="#Isabelle/HOL_ProofAssistant">[13]</a></sup>

<!-- Introduction and elimination rules for classical connectives and quantifiers. -->

Typed $\lambda$-Calculus
<!-- Terms are built using the simply-typed λ-calculus, with β-reduction and η-conversion (up to extensionality). -->

Equality Rules
<!-- Polymorphic equality with reflexivity + congruence/substitution; includes functional and boolean extensionality. -->

Hilbert $\epsilon$ (Choice) Operator
A choice operator $\varepsilon : (\alpha \Rightarrow bool) \Rightarrow \alpha$ with the choice axiom.

Conservative Definition Principles
<!-- New constants and types may only be introduced via mechanisms Isabelle checks as conservative (no new theorems introduced). -->

Small Trusted Kernel
<!-- Isabelle’s logical kernel is minimal; all automation reduces to this core proof system. -->


WIP
<!-- 
	•	HOL’s small axiom set: classical logic, equality, choice
	•	Isabelle’s kernel uses natural-deduction with λ-calculus + types
	•	All user-introduced definitions are conservative
	•	Isabelle proves everything from this core automatically -->

<!-- The basic rules of inference of $\mathcal{F}^w$, where $\mathcal{F}$ is a system of $\mathcal{w}$-order logic which has all finite order logics as subsystems:

1) **Modus Ponens** From $A$ and $A \to B$ to infer $B$.
2) **Generalization** From $A$ to infer $\forall x\,A$, where x is a variable of any type


*Adapted from Andrews, 2002*<sup><a href="#andrews2002">[3]</a></sup> using modern logic convention.


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

Adapted from *Andrews, 2002*<sup><a href="#andrews2002">[3]</a></sup> using modern logic convention. -->


## Tool (Installation, First Example, First Exercise)

### Installation

[Installation Link for Isabelle](https://isabelle.in.tum.de/)

Isabelle processes the theory document incrementally in the background, meaning that there is no additional "compile" or "run" step. As you type in lines and commands, the background system will check them and automatically update the proof state and any relevant error reports. Just go line by line, or command by command in order to check the related output.

Isabelle uses *.thy (theory) files, and the general structure of the theory files is like this:

```isabelle
theory THEORY_NAME
    imports OTHER_THEORIES

begin

THEORY_BODY

end
```

`theory THEORY_NAME` declares the theory name and **must** exactly match the .thy filename. For example, if the file is called test.thy, then you would have `theory test`

`imports OTHER_THEORIES` tells it to import another theory; for example, one popular theory to import is Main.thy, which includes support for natural numbers, lists, and basic arithmetic

`begin` is the entry point into the theory body, while `end` is the end point of the theory body

More detailed instructions on setup and initial use can be found in Chapters 1 and 2.1.2 of *Concrete Semantics*<sup><a href="#ConcreteSemantics">[1]</a></sup>

### Proof Solving via Sledgehammer

WIP

### First Example - Add Function

For the first example, the goal will be to implement recursive addition via a function called "add". The general form should be:

```isabelle
fun add :: "nat ⇒ nat ⇒ nat" where
    "base case"
    "recursive case"
```

where two natural numbers are added, and the result is a natural number that is the sum of the two input numbers. For example, `sum m n` should return the sum of m and n.

```{dropdown} Show Answer
~~~isabelle
fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc (add m n)" 
~~~
```

For a detailed explanation, [See Section 10.3.2 Exercises](./assets-10/10.3_exercises.md#10.3.2-First-Example)


### First Exercise - Associativity and Communativity of Add

For the first exercise, we will be proving the associative and commutative properties of a custom `add` function in Isabelle. This exercise comes from Exercise 2.2 of [Concrete Semantics Exercises](http://www.concrete-semantics.org/Exercises/exercises.pdf)

The custom add function is defined here:
```{dropdown} Show Answer
~~~isabelle
fun add :: "nat => nat => nat" where
    "add 0 n = n" |
    "add (Suc m) n = Suc(add m n)"
~~~
```

We use 2 lemmas to prove each part of the exercise, namely:
```isabelle
lemma add_assoc: "add (add m n) p = add m (add n p)"
lemma add_comm: "add m n = add n m"
```

The full lemma proof for associativity is here:
```{dropdown} Show Answer
~~~isabelle
lemma add_assoc: "add (add m n) p = add m (add n p)"
proof (induction m) 
  case 0
  show ?case by simp
next
  case (Suc m)
  show ?case by (simp add: Suc.IH)
qed
~~~
```

For a detailed explanation, [See Section 10.3.3 Associative Property](./assets-10/10.3_exercises.md#Associative-Property-Proof)

Next, to prove the communative property, we will first prove 2 helper lemmas:
```isabelle
lemma add_0_right: "add m 0 = m"
lemma add_Suc_right: "add m (Suc n) = Suc (add m n)"
```

The helper lemma proofs for communativity
```{dropdown} Show Answer
~~~isabelle
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
~~~
```

With the helper lemmas proven, we will use them to prove the commutative property

```{dropdown} Show Answer
~~~isabelle
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
~~~
```

For a detailed explanation, [See Section 10.3.3 Communative Property](./assets-10/10.3_exercises.md#Communative-Property-Proof)


## Introductory Examples - Tower of Hanoi or Insertion Sort

<!-- show something interesting about tool, logic, etc and can be digested and understood with minimum experience -->

Tower of Hanoi or Insertion Sort

WIP


## The Landscape of Tools

### Interactive Theorem Provers

**HOL4** is part of the "HOL" family of interactive theorem provers, using classical higher order logic and following the LCF approach to ensure soundness. Developed by Michael J.C. Gordon, the system is implemented in ML, and is a direct descendent of the original HOL88 system. Because HOL4 shares the same underlying logic as Isabelle/HOL, many thoeries and proof patterns are generally portable between the two tools.

**Rocq** (formerly named Coq) is an interactive theorem prover based on the *Calculus of Inductive Constructions*, which is a derivative of the calculus of constructions, and is a higher order typed lambda calculus that adds inductive types. It is mainly implemented in OCaml with some C. Compared with Isabelle/HOL, Rocq uses higher order type theory, which allows it to have greater expressive power.

**Lean (4)** is another proof assistant and, similar to Rocq, is based on dependent type theory, which is a version of the calculus of constructions with inductive types. Lean 4 in particular is mostly implemented in Lean (with some C++), and can have its Lean theorem prover produce C code. Compared to Isabelle/HOL's classic higher order logic, Lean's dependent type theory offers greater expressive power, similar to Rocq.

### Automated Theorem Prover

**Leo III** is an automated theorem prover for classical higher order logic that supports all common TPTP input dialects and is based on paramodulation calculus with ordering constraints for reasoning. Leo III is written in Scala and runs on the JVM (Java Virtual Machine). Compared with ITPs (interactive theorem provers) like Isabelle/HOL, Leo III trades human-guided proof structuring and granular control for full automation, allowing it to rapidly discharge proof obligations.<sup><a href="#LeoIII">[18]</a></sup>


**Satallax** is another automated theorem prover for classical higher order logic and is based on Church's simple type theory with extensionality and choice operators. It is implemented in OCaml and uses the SAT solver MiniSat for its proof search. Basically, Satallax generates propositional clauses corresponding to the rules of a complete tableau calculus and calls MiniSat periodically to test the satisfiability of these clauses.<sup><a href="#Satallax">[19]</a></sup>


## Algorithms

WIP 

<!-- (may need to strip some of the stuff from basic theory for this?) -->


## Benchmark and Competitions


## Applications in Industry (and Academia)

In general, Isabelle/HOL appears to have a wide variety of applcation throughout industry and academia due to the fact that it provides a mathematical assuranace of correctness (rather than testing alone). The tool is particularly suited to safety critical systems, such as avionics, embedded systems, industrial process control, SoC design, etc where fault risk must be minimized and certification standards demand high trust.

### Physical Addressing on Real Hardware

Achermann et al.<sup><a href="#Achermann_physicalAddressing">[4]</a></sup> discuss how to formally model and verify physical memory address translation and remapping hardware (such as MMUs) in SoCs (Systems-on-Chip) using Isabelle/HOL. Specifically, they developed a hardware model that encodes translation units and then prove that standard memory operations preserve system invariants.

<!-- HOL-based systems used to verify hardware modules and FPGA implementations -->

### FOCUS - Stream Processing Components

Spichkova<sup><a href="#Spichkova_FOCUS">[5]</a></sup> proposes a new framework, FOCUS, aimed at formal specification and the application of refinement-based verification of interactive systems. In addition, FOCUS uses a stream processing component, represented by a communication history of a directed channel between components. FOCUS uses Isabelle/HOL with the Isar language with three distinct case studies, namely process control (Steam Boiler System), data transmission (FlexRay communication protocol), memory and processing components (Automotive-Gateway System).

- The first case study is about a generic steam boiler system, which is represented as a distributed system with communicating components. In addition, the system must meet real time requirements such as ensuring water levels stay within bounds and when to appropriately actuate the water pumps. The system is formalised in Isabelle/HOL, translating architecture and component behaviour into higher-order logic while proving the design satisfies timing and safety requirements.

- The second case study is about FlexRay, which is a communication protocol for safety-critical real-time applications, specfically embedded systems in vehicles. FOCUS is used in this case to verify and prove correct static cycles, channel scheduling and properties, and node broadcast behiavor.

- The third case study is about the Automative-Gateway system for the Verisoft project. Basically, if the Gateway receives a vehicle crash signal, then it will initiate a call to the appropriate Emergency Service Center (ESC). The system is modelled in Isabelle/HOL, with the architecture, requirements, and refinement relations all formally specified and proven to ensure that the Gateway design meets its crash signal and data transmission requirements.

### IsaBIL - Verifying (In)Correctness of Binaries

Griffin et al.<sup><a href="#Griffin_IsaBIL">[6]</a></sup> present IsaBIL, a binary analysis framework in Isabelle/HOL that is based on BAP (Binary Analysis Platform). IsaBIL formalizes BAP's intermediate language (BIL) and integrates it with Hoare Logic (for proofs of correctness) and incorrectness logic (for proofs of incorectness). While there is a primary focus is on the RISC-V architecture and C binaries, the authors assert that IsaBIL is a flexible framework that can verify binaries for different languages (C, C++, Rust), toolchains (LLVM, Ghidra), and architectures (x86, RISC-V). The authors prove correctness through some industry level examples such as Lockheed Martin's JSF (Joint Strike Fighter) coding standards and the MITRE ATT&CK database.

### Verlso - Isolation Guarantees of Database Transactions

Ghasemirad et al.<sup><a href="#Ghasemirad_VerIso">[7]</a></sup> present VerIso, a rigorous Isabelle/HOL-based framework for verifying transaction isolation within production level databases. The authors showcase VerIso by modelling the strict two-phase locking (S2PL) protocol and prove that it provides strict serializability (transactions behave as if executed sequentially and that sequential order must match the actual time order of their invocation/commit). In addition, VerIso’s parameterised architecture supports multiple isolation levels and uncovers design-level bugs in protocols such as the TAPIR protocol and its violation of atomic visibility.

### IEEE 754 Floating Point Implementation for MDPs

Kohlen et al.<sup><a href="#Kohlen_float">[8]</a></sup> present a fully verified implementation of the Interval Iteration (II) Algorithm for Markov Decision Processes (MDPs). They model the II algorithm in Isabelle/HOL, use the Isabelle Refinement Framework (IRF) to carry out step-wise refinement down to LLVM bytecode, and extend Isabelle/HOL’s reasoning to support IEEE 754 floating-point arithmetic with directed rounding. Their result is a correct-by-construction floating-point implementation, competitive with industry tools and highly relevant for domains where verified numerical correctness matters, such as embedded systems, SoCs and safety-critical software.

<!-- ### 10.8.6 IsaMini: Isabelle Proof Language for Machine Learning

Xu et al. present MiniLang/IsaMini, a streamlined proof langauge for Isabelle/HOL designed to improve Large Language Model (LLM) integration in formal verification. The authors convert existing Isar proofs, such as those within Isabelle's Archive of Formal Proofs (AFP), into MiniLang and fine-tune LLMs on this new proof representation. They then use the LLM's macro level proof planning alongside Isabelle's automation (such as Sledgehammer, etc) for micro level proof steps to significantly boost proof success rate. Their work is noteworthy because it brings together formal methods and AI-assisted tooling, reducing manual proof effort and enabling more scalable verification.<sup><a href="#Xu_IsaMini">[7]</a></sup> -->

### Autoformalization with Large Language Models

Wu et al.<sup><a href="#Wu_LLM_Autoformat">[9]</a></sup> present WIP

## Case Study - Autoformalization with Large Language Models

WIP

use this one:

https://openreview.net/forum?id=IUikebJ1Bf0

<!-- https://arxiv.org/html/2408.11172v1

https://github.com/xqyww123/Isa-Mini -->

<!-- no code artifact for this paper

trying to find where the actual code etc is?

According to the authors:
*the REPL infrastructure, MiniLang interpreter, translator,
training data, machine learning framework, Sledgehammer,
and parameters of the finetuned models will be open-sourced
and are present in the submitted supplementary materials* -->

<!-- need to talk to Kurz about finding another example; the binary analysis one seems pretty cool -->
<!-- 

DEPRECATED SINCE THIS IS THE BINARY ANALYSIS TOOL

https://gitlab.surrey.ac.uk/isabil/isabil

https://zenodo.org/records/15268251

I added these lines as PATH variables to my zsh on MacOS in order to run the Isabelle CLI tool:
`export ISABELLE_HOME="/Applications/Isabelle2025.app"`
`export PATH="$ISABELLE_HOME/bin:$PATH"`

Make sure you have correct version of the [AFP](https://www.isa-afp.org/download/) downloaded

Unpack the Tar file, put it *somewhere*, and then register it via 
`isabelle components -u PATHNAME`

For example, the pathname for my AFP is: 
`/Users/spencerau/Documents/Isabelle/afp-2025-10-25/thys`

My command is then:
`isabelle components -u /Users/spencerau/Documents/Isabelle/afp-2025-10-25/thys` -->

## History

<!-- Church (1940) A Formulation of the Simple Theory of Types -->

<!-- may include dates at teh beginning of each part, and include citations etc  -->

### Origins of Higher Order Logic

<!-- scaffolding template for now -->

Alonzo Church's work in the 1930s (via $\lambda$-calculus) and 1940s (via type theory) and Leon Henkin's work in the 1950s (on general models semantics) lay the foundation for higher order logic. From their contributions arose an extension of First Order Logic (FOL) that allows quantification over predicates and functions, enabling reasoning about functions as first class entities

In the 1970s, Robert Milner develops LCF (Logic for Computable Functions) at Stanford and later Edinburgh, introducing the idea of an interactive theorem prover. LCF pioneers the use of a tactic-based proof automation and the ML meta language, which is designed to let users safely define proof strategies. ML later evovles into OCaml and Standard ML.

In the early 1980s, Michael J. C. Gordon builds upon LCF in order to create the HOL system, which explicitly uses higher-order logic as its core formalism. This HOL system would become the foundation for hardware verification, paving the way and influencing later provers like HOL4 and Isabelle/HOL.

### Development of Isabelle/HOL

Developed in the late 1980's by Lawrence C. Paulson at Cambridge, Isabelle was created as a generic theorem proving framework capable of supporting multiple logical formalisms under a single meta-logic.

The HOL instantiation of Isabelle (Isabelle/HOL) became the most widely adopted version due to its strong expressiveness and balance between automation and manual control.

Isabelle introduced the Isar prof language in the 2000s, allowing structured and human readable proofs, improving clarity over traditional tactic-based approaches like in LCF.

Integration with automated tools such as Sledgehammer and SMT solvers further extend its power, bridging interactive reasoning and automation.

The creation of the AFP (Archive of Formal Proofs) established a reusable library of formalizd mathematics and computer science, solidifying Isabelle/HOL's role in both academia and industry.

## Current Development, Research Challenges, Conferences and Workshops

### Current Development

AI/LLM stuff with NTP in Isabelle?

### Research Challenges

### Conferences and Workshops

## References

<a id="ConcreteSemantics"></a>
- [1]: Nipkow and Klein (2014) [Concrete Semantics: With Isabelle/HOL](http://www.concrete-semantics.org/index.html), Springer Publishing Company, Incorporated.

<a id="MossSyllogism"></a>
- [2]: Larry Moss (2015) [Natural Logic](https://logic.berkeley.edu/colloquium/MossSlides.pdf), UC Berkeley Logic Seminar.

<a id="andrews2002"></a>
- [3]: Peter B. Andrews (2002) [Introduction to Mathematical Logic and Type Theory: To Truth through Proof (2nd. ed.)](https://dl.acm.org/doi/10.5555/581793#), Kluwer Academic Publishers, USA.

<a id="Achermann_physicalAddressing"></a>
- [4]: Achermann, Humbel, Cock, and Roscoe (2018) [Physical Addressing on Real Hardware in Isabelle/HOL](https://people.inf.ethz.ch/troscoe/pubs/achermann_itp_2018.pdf), Department of Computer Science, ETH Zurich.

<a id="Spichkova_FOCUS"></a>
- [5]: Spichkova (2014) [Stream processing components: Isabelle/HOL formalisation and case studies](https://arxiv.org/abs/1405.1512), arXiv preprint arXiv:1405.1512. 

<a id="Griffin_IsaBIL"></a>
- [6]: Griffin, Dongol, and Raad. (2025) [IsaBIL: A Framework for Verifying (In) correctness of Binaries in Isabelle/HOL (Extended Version)](https://arxiv.org/abs/2504.16775v1), arXiv preprint arXiv:2504.16775.

<a id="Ghasemirad_VerIso"></a>
- [7]: Ghasemirad, et al. (2025) [VerIso: Verifiable isolation guarantees for database transactions.](https://arxiv.org/abs/2503.06284) arXiv preprint arXiv:2503.06284.

<a id="Kohlen_float"></a>
- [8]: Kohlen et al. (2025) [A formally verified IEEE 754 floating-point implementation of interval iteration for MDPs](https://arxiv.org/abs/2501.10127v3), International Conference on Computer Aided Verification, Cham: Springer Nature Switzerland.

<a id="Wu_LLM_Autoformat"></a>
- [9]: Wu et al. (2022) [Autoformalization with Large Language Models](https://openreview.net/forum?id=IUikebJ1Bf0), NeurIPS 2022 Conference.

<a id="Church_TypeTheory"></a>
- [10]: Alonzo Church (1940) [A Formulation of the Simple Theory of Types](https://www.jstor.org/stable/2266170), The Journal of Symbolic Logic, Vol. 5, No. 2 (June, 1940), pp. 56-68 (13 pages).

<a id="Paulson_LCF"></a>
- [11]: Laurence C. Paulson (1987) [Logic and Computation: Interactive Proof with Cambridge LCF](https://assets.cambridge.org/97805213/46320/sample/9780521346320ws.pdf), Cambridge University Press, USA.

<a id="Stanford_LambdaCalc_TypeTheory"></a>
- [12]: Deutsch and Marshall (2025) [D. The λ-Calculus and Type Theory: Supplement to Alonzo Church](https://plato.stanford.edu/entries/church/supplementD.html), The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University.

<a id="Isabelle/HOL_ProofAssistant"></a>
- [13]: Nipkow, Paulson, and Wenzel (2025) [Isabelle/HOL: A Proof Assistant for
Higher-Order Logic](https://isabelle.in.tum.de/doc/tutorial.pdf), Springer-Verlag, Berlin, Heidelberg. 

<a id="Kurz_LambdaSemantics"></a>
- [14]: Alexander Kurz (2023) [Semantics of the Lambda Calculus](https://hackmd.io/@alexhkurz/H1e4Nv8Bv), CPSC 354 - Programming Languages, Chapman University

<a id="Kurz_LambdaSyntax"></a>
- [15]: Alexander Kurz (2023) [Syntax of Lambda Calculus](https://hackmd.io/@alexhkurz/S1D0yP8Bw), CPSC 354 - Programming Languages, Chapman University

<a id="Xu_IsaMini"></a>
- [16]: Xu et al. (2025) [IsaMini: Redesigned Isabelle Proof Language for Machine Learning](https://arxiv.org/abs/2507.18885) arXiv preprint arXiv:2507.18885.

<a id="Teege_IntroIsabelle"></a>
- [17]: Teege (2025) [A Gentle Introduction to Isabelle and Isabelle/HOL](https://github.com/gteege/gentle-isabelle/blob/main/man-isabelle.pdf) Universität der Bundeswehr München

<a id="LeoIII"></a>
- [18]: [Leo III Repository](https://github.com/leoprover/Leo-III) GitHub

<a id="Satallax"></a>
- [19]: Michael Färber, [Satallax](https://satallaxprover.org/) 

https://plato.stanford.edu/entries/logic-higher-order/

https://plato.stanford.edu/entries/reasoning-automated/#HigOrdLog

https://plato.stanford.edu/entries/type-theory-church/

https://www.youtube.com/watch?v=VS_GK-9xUO4

https://www.youtube.com/watch?si=ocR0HnYDEQLAneym&v=TrYosPPCQAY&feature=youtu.be

https://www.youtube.com/watch?v=yAi3XWCBkDo

SEP Category Theory - https://plato.stanford.edu/entries/category-theory/

<!-- https://isabelle.in.tum.de/library/HOL/HOL/document.pdf -->

https://flint.cs.yale.edu/cs428/coq/doc/Reference-Manual006.html




## Suggestions for Future Work

