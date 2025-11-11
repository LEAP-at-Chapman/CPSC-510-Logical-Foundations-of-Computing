# Higher-Order Logic with Isabelle/HOL

*Author: Spencer Au*

## Topics

- Higher-order logic foundations
- Function types and quantification
- Isabelle/HOL advanced features
- Theorem proving strategies
- Industrial theorem proving

## 10.1 Idea and Introduction
WIP

This chapter extends to higher-order logic in Isabelle/HOL, showing how to reason about functions as first-class objects and exploring the foundations of modern theorem proving.

Higher-order logic (HOL) extends the capabilities of first-order logic (FOL) by allowing quantifiers (such as $ \forall x $ and $ \exists x $) to range over functions and predicates, not just individual elements. In addition, functions can be passed as arguments to other functions, returned as results, and manipulated just like any other data type. This enables more expressive statements about the properties of functions and their relationships.

## 10.2 Basic Theory

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

*Adapted from Andrews, 2002*<sup><a href="#andrews2002">[1]</a></sup> using modern logic convention.


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

Adapted from *Andrews, 2002*<sup><a href="#andrews2002">[1]</a></sup> using modern logic convention.


## 10.3 Tool (Installation, First Example, First Exercise)

### 10.3.1 Installation

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

### 10.3.2 Proof Solving via Sledgehammer

### 10.3.3 First Example - Add Function

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

For a detailed explanation, [See Section 10.3.2 Exercises](./ch10_assets/10.3_exercises.md#10.3.2-First-Example)


### 10.3.4 First Exercise - Associativity and Communativity of Add

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

For a detailed explanation, [See Section 10.3.3 Associative Property](./ch10_assets/10.3_exercises.md#Associative-Property-Proof)

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

For a detailed explanation, [See Section 10.3.3 Communative Property](./ch10_assets/10.3_exercises.md#Communative-Property-Proof)


## 10.4 Introductory Examples - Tower of Hanoi or Insertion Sort

<!-- show something interesting about tool, logic, etc and can be digested and understood with minimum experience -->

Tower of Hanoi or Insertion Sort


## 10.5 The Landscape of Tools

WIP

### 10.5.1 Interactive Proof Assistants

HOL4 (classic HOL)

Coq (constructive higher-order/type theory)

Lean 4 (modern dependent/HOL hybrid)

### 10.5.2 Automated Higher Order Prover

Leo III

Satallax


## 10.6 Algorithms


## 10.7 Benchmark and Competitions


## 10.8 Applications in Industry

In general, Isabelle/HOL appears to have a wide variety of applcation throughout industry, due to the fact that it provides a mathematical assuranace of correctness (rather than testing alone). The tool is particularly suited to safety critical systems, such as avionics, embedded systems, industrial process control, SoC design, etc where fault risk must be minimized and certification standards demand high trust.

### 10.8.1 Physical Addressing on Real Hardware

Achermann et al. discuss how to formally model and verify physical memory address translation and remapping hardware (such as MMUs) in SoCs (Systems-on-Chip) using Isabelle/HOL. Specifically, they developed a hardware model that encodes translation units and then prove that standard memory operations preserve system invariants.<sup><a href="#Achermann_physicalAddressing">[2]</a></sup>

<!-- HOL-based systems used to verify hardware modules and FPGA implementations -->

### 10.8.2 FOCUS - Stream Processing Components

Spichkova proposes a new framework, FOCUS, aimed at formal specification and the application of refinement-based verification of interactive systems. In addition, FOCUS uses a stream processing component, represented by a communication history of a directed channel between components. FOCUS uses Isabelle/HOL with the Isar language with three distinct case studies, namely process control (Steam Boiler System), data transmission (FlexRay communication protocol), memory and processing components (Automotive-Gateway System).<sup><a href="#Spichkova_FOCUS">[3]</a></sup>

- The first case study is about a generic steam boiler system, which is represented as a distributed system with communicating components. In addition, the system must meet real time requirements such as ensuring water levels stay within bounds and when to appropriately actuate the water pumps. The system is formalised in Isabelle/HOL, translating architecture and component behaviour into higher-order logic while proving the design satisfies timing and safety requirements.

- The second case study is about FlexRay, which is a communication protocol for safety-critical real-time applications, specfically embedded systems in vehicles. FOCUS is used in this case to verify and prove correct static cycles, channel scheduling and properties, and node broadcast behiavor.

- The third case study is about the Automative-Gateway system for the Verisoft project. Basically, if the Gateway receives a vehicle crash signal, then it will initiate a call to the appropriate Emergency Service Center (ESC). The system is modelled in Isabelle/HOL, with the architecture, requirements, and refinement relations all formally specified and proven to ensure that the Gateway design meets its crash signal and data transmission requirements.

### 10.8.3 IsaBIL - Verifying (In)Correctness of Binaries

Griffin et al. present IsaBIL, a binary analysis framework in Isabelle/HOL that is based on BAP (Binary Analysis Platform). IsaBIL formalizes BAP's intermediate language (BIL) and integrates it with Hoare Logic (for proofs of correctness) and incorrectness logic (for proofs of incorectness). While there is a primary focus is on the RISC-V architecture and C binaries, the authors assert that IsaBIL is a flexible framework that can verify binaries for different languages (C, C++, Rust), toolchains (LLVM, Ghidra), and architectures (x86, RISC-V). The authors prove correctness through some industry level examples such as Lockheed Martin's JSF (Joint Strike Fighter) coding standards and the MITRE ATT&CK database.<sup><a href="#Griffin_IsaBIL">[4]</a></sup>

### 10.8.4 Verlso - Isolation Guarantees of Database Transactions

Ghasemirad et al. present VerIso, a rigorous Isabelle/HOL-based framework for verifying transaction isolation within production level databases. The authors showcase VerIso by modelling the strict two-phase locking (S2PL) protocol and prove that it provides strict serializability (transactions behave as if executed sequentially and that sequential order must match the actual time order of their invocation/commit). In addition, VerIso’s parameterised architecture supports multiple isolation levels and uncovers design-level bugs in protocols such as the TAPIR protocol and its violation of atomic visibility.<sup><a href="#Ghasemirad_VerIso">[5]</a></sup>

### 10.8.5 IEEE 754 Floating Point Implementation for MDPs

Kohlen et al. present a fully verified implementation of the Interval Iteration (II) Algorithm for Markov Decision Processes (MDPs). They model the II algorithm in Isabelle/HOL, use the Isabelle Refinement Framework (IRF) to carry out step-wise refinement down to LLVM bytecode, and extend Isabelle/HOL’s reasoning to support IEEE 754 floating-point arithmetic with directed rounding. Their result is a correct-by-construction floating-point implementation, competitive with industry tools and highly relevant for domains where verified numerical correctness matters, such as embedded systems, SoCs and safety-critical software.<sup><a href="#Kohlen_float">[6]</a></sup>

### 10.8.6 IsaMini: Isabelle Proof Language for Machine Learning

Xu et al. present MiniLang/IsaMini, a streamlined proof langauge for Isabelle/HOL designed to improve Large Language Model (LLM) integration in formal verification. The authors convert existing Isar proofs, such as those within Isabelle's Archive of Formal Proofs (AFP), into MiniLang and fine-tune LLMs on this new proof representation. They then use the LLM's macro level proof planning alongside Isabelle's automation (such as Sledgehammer, etc) for micro level proof steps to significantly boost proof success rate. Their work is noteworthy because it brings together formal methods and AI-assisted tooling, reducing manual proof effort and enabling more scalable verification.<sup><a href="#Xu_IsaMini">[7]</a></sup>

## 10.9 Case Study - Neural Theorem Proving via IsaMini



## 10.10 History

<!-- Church (1940) A Formulation of the Simple Theory of Types -->

<!-- may include dates at teh beginning of each part, and include citations etc  -->

### 10.10.1 Origins of Higher Order Logic

<!-- scaffolding template for now -->

Alonzo Church's work in the 1930s (via $\lambda$-calculus) and Leon Henkin's work in the 1950s (on general models semantics) lay the foundation for higher order logic. From their contributions arose an extension of First Order Logic (FOL) that allows quantification over predicates and functions, enabling reasoning about functions as first class entities

In the 1970s, Robert Milner develops LCF (Logic for Computable Functions) at Stanford and later Edinburgh, introducing the idea of an interactive theorem prover. LCF pioneers the use of a tactic-based proof automation and the ML meta language, which is designed to let users safely define proof strategies. ML later evovles into OCaml and Standard ML.

In the early 1980s, Michael J. C. Gordon builds upon LCF in order to create the HOL system, which explicitly uses higher-order logic as its core formalism. This HOL system would become the foundation for hardware verification, paving the way and influencing later provers like HOL4 and Isabelle/HOL.

### 10.10.2 Development of Isabelle/HOL

Developed in the late 1980's by Lawrence C. Paulson at Cambridge, Isabelle was created as a generic theorem proving framework capable of supporting multiple logical formalisms under a single meta-logic.

The HOL instantiation of Isabelle (Isabelle/HOL) became the most widely adopted version due to its strong expressiveness and balance between automation and manual control.

Isabelle introduced the Isar prof language in the 2000s, allowing structured and human readable proofs, improving clarity over traditional tactic-based approaches like in LCF.

Integration with automated tools such as Sledgehammer and SMT solvers further extend its power, bridging interactive reasoning and automation.

The creation of the AFP (Archive of Formal Proofs) established a reusable library of formalizd mathematics and computer science, solidifying Isabelle/HOL's role in both academia and industry.

## 10.11 Current Development, Research Challenges, Conferences and Workshops


## 10.12 References

- [Isabelle/HOL](https://isabelle.in.tum.de/)
- [Concrete Semantics](http://www.concrete-semantics.org/)
- [Concrete Semantics Exercises](http://www.concrete-semantics.org/Exercises/exercises.pdf)
- [Isabelle YouTube Tutorial by FDS 2020](https://www.youtube.com/@FDS-hs2uc/videos)
- [Syllogism Slides from Nate Moss](https://logic.berkeley.edu/colloquium/MossSlides.pdf)

<a id="andrews2002"></a>
- [1] Andrews, *An Introduction to Mathematical Logic and Type Theory*. Springer, 2002. [Springer Link](https://link.springer.com/book/10.1007/978-94-015-9934-4).

<a id="Achermann_physicalAddressing"></a>
- [2] Achermann, Reto et al. "Physical Addressing on Real Hardware in Isabelle/HOL" Department of Computer Science, ETH Zurich. [Paper Link](https://people.inf.ethz.ch/troscoe/pubs/achermann_itp_2018.pdf)

<a id="Spichkova_FOCUS"></a>
- [3] Spichkova, Maria. “Stream processing components: Isabelle/HOL formalisation and case studies.” arXiv preprint arXiv:1405.1512 (2014). [arxiv Link](https://arxiv.org/abs/1405.1512)

<a id="Griffin_IsaBIL"></a>
- [4] Griffin, Matt, Brijesh Dongol, and Azalea Raad. "IsaBIL: A Framework for Verifying (In) correctness of Binaries in Isabelle/HOL (Extended Version)." arXiv preprint arXiv:2504.16775 (2025). [arixv Link](https://arxiv.org/abs/2504.16775v1)

<a id="Ghasemirad_VerIso"></a>
- [5] Ghasemirad, Shabnam, et al. "VerIso: Verifiable isolation guarantees for database transactions." arXiv preprint arXiv:2503.06284 (2025). [arxiv Link](https://arxiv.org/abs/2503.06284)

<a id="Kohlen_float"></a>
- [6] Kohlen, Bram, et al. "A formally verified IEEE 754 floating-point implementation of interval iteration for MDPs." International Conference on Computer Aided Verification. Cham: Springer Nature Switzerland, 2025. [arxiv Link](https://arxiv.org/abs/2501.10127v3)

<a id="Xu_IsaMini"></a>
- [7] Xu, Qiyuan, et al. "IsaMini: Redesigned Isabelle Proof Language for Machine Learning." arXiv preprint arXiv:2507.18885 (2025). [arxiv Link](https://arxiv.org/abs/2507.18885)



## 10.13 Suggestions for Future Work

