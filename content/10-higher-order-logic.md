# Higher-Order Logic with Isabelle

*Author: Spencer Au*

## Idea and Introduction

Topics

- Higher-order logic foundations
- Function types and quantification
- Isabelle/HOL advanced features
- Theorem proving strategies
- Industrial theorem proving

This chapter extends to higher-order logic in Isabelle/HOL, showing how to reason about functions as first-class objects and exploring the foundations of modern theorem proving.

Higher-order logic (HOL) extends the capabilities of first-order logic (FOL) by allowing quantifiers (such as $ \forall x $ and $ \exists x $) to range over functions and predicates, not just individual elements. In addition, functions can be passed as arguments to other functions, returned as results, and manipulated just like any other data type. This enables more expressive statements about the properties of functions and their relationships.

## Basic Theory

### From First-Order Logic to Higher-Order Logic

First-order logic (FOL) restricts quantification to individual elements of a domain, without quantifying over predicates or functions. Second-order logic extends FOL by allowing quantification over relations, sets, and functions of that domain. Higher-order logic (HOL) generalizes this extension by allowing quantification over predicates and functions of arbitrary finite types, not just individuals or sets.<sup><a href="#SEP_HOL">[7]</a></sup>

### The HOL Type System

In Isabelle/HOL, the underlying higher-order logic is built upon Church's simple type theory<sup><a href="#Church_TypeTheory">[18]</a></sup>, which is a disciplined type system in which every term is assigned a type and compound types are formed using function type constructors. This simple type theory extends first-order logic by classifying individuals, predicates, and functions into an explicit hierarchy of types, enabling quantification over functions and predicates while avoiding the semantic paradoxes of untyped systems, such as an expression that may refer to itself in a problematic way. In HOL, the type system both guarantees well-formed expressions and organizes how functions of any finite type can be combined and applied.<sup><a href="#SEP_ChurchTypeTheory">[8]</a></sup> Church’s type theory is widely adopted in proof assistants implementing HOL, such as Isabelle/HOL, and offers a foundation for formalizing mathematics and computations.<sup><a href="#Isabelle_Logics">[2]</a></sup>

*For further resources about type theory, SEP provides an excellent article on Type Theory<sup><a href="#SEP_TypeTheory">[9]</a></sup>. There is also a solid YouTube video for those that would prefer a different medium.<sup><a href="#TypeTheory_Youtube">[32]</a></sup>*

### Lambda ($\lambda$) Abstraction

In higher-order logic, $\lambda$-abstraction provides a formal way to define anonymous functions by binding variables in expressions. We write this as $\lambda x.\; t$, where x is a parameter and t is the body of the function. A $\lambda$-term defines a function by binding a variable in an expression, and $\beta$-reduction is the rule that implements function application. Basically, when you apply a $\lambda$-term to an argument, you substitute that argument for the bound variable in the function body. For example, the abstraction $\lambda x. \; x * x$ represents the square function, and applying it to an arbitrary number $a$ yields $a * a$ by replacing $x$ with $a$.<sup><a href="#Kurz_LambdaSemantics">[10]</a></sup> <sup><a href="#Kurz_LambdaSyntax">[11]</a></sup>

In Isabelle/HOL, $\lambda$-abstraction is part of the underlying simply typed $\lambda$-calculus, where terms consist of variables, constants, applications, and abstractions. Applying a $\lambda$-term to an argument substitutes the argument for the bound variable in the body, and Isabelle treats the original application and its $\beta$-reduced form as equivalent. This mechanism makes functions first-class citizens in HOL, supports the construction of higher-order functions, and enables logical constructs to be expressed uniformly.<sup><a href="#Isabelle_Logics">[2]</a></sup>

*For supplementary resources about $\lambda$-abstraction and $\lambda$-calculus, SEP again provides some excellent articles.<sup><a href="#Stanford_LambdaCalc_TypeTheory">[12]</a></sup> <sup><a href="#SEP_LambdaCalc">[13]</a></sup> There are also easy to grasp YouTube videos by LigerLearn.<sup><a href="#LigerLearn_LambdaPrimer">[30]</a></sup> <sup><a href="#LigerLearn_LambdaEval">[31]</a></sup>*

### Logical Constants in HOL

In higher-order logic, the logical constants are the primitive symbols that express the core logical operations and quantification. They include propositional connectives such as: 
- Conjunction ($\land$)
- Disjunction ($\lor$)
- Implication ($\to$)
- Negation ($\neg$)
- Equality ($=$)

as well as quantifiers like:
- Universal ($\forall$) 
- Existential ($\exists$)

which operate over objects of any type. In Isabelle/HOL, the full syntax of terms and constants is defined by the grammar of HOL and is treated uniformly alongside function application and $\lambda$-abstraction. This vocabulary is the basis on which more complex formulas are built and manipulated in proof development.<sup><a href="#Isabelle_Logics">[2]</a></sup>

### Deductive Core of HOL

The deductive core of higher-order logic consists of the fundamental inference rules for logical connectives, quantifiers, and equality, including the basic introduction and elimination rules that govern valid reasoning in HOL. In Isabelle/HOL, these primitive rules form the logic’s core inference system, and every derived theorem is justified by a sequence of such sound rule applications. Higher level proof methods and tactics ultimately based on these basic rules make structured proofs possible in practice. Concrete presentations of these inference rules and how they are used in proofs can be found in the Isabelle/HOL Proof Assistant Manual.<sup><a href="#Isabelle/HOL_ProofAssistant">[3]</a></sup>


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

Sledgehammer is an automated theorem prover orchestrator. It dispatches proof obligations to external provers such as Vampire via command line and returns candidate proofs that can be directly applied. Basically, it find proofs by "hammering away" at different sub-goals that would typically be tedious to construct manually. In the Isabelle GUI, Sledgehammer can be accessed by clicking on the *sledgehammer* tab on the bottom left corner of the application: select the target sub-goal, invoke Sledgehammer via apply, and then apply a suggested proof if found. Although *Concrete Semantics 4.3.1*<sup><a href="#ConcreteSemantics">[1]</a></sup> introduces the basic sledgehammer command, the GUI method is generally more convenient. The official Isabelle Sledgehammer documentation page<sup><a href="#Isabelle_Sledgehammer">[35]</a></sup> provides further detail.

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

For a detailed explanation, [See Section 8.3.2 Exercises](./assets-10/8.3_tool/8.3_exercises.md)

### First Exercise - Associativity and Commutativity of Add

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

For a detailed explanation, [See Section 8.3.3 Associative Property](./assets-10/8.3_tool/8.3_exercises.md#associative-property-proof)

Next, to prove the commutative property, we will first prove 2 helper lemmas:
```isabelle
lemma add_0_right: "add m 0 = m"
lemma add_Suc_right: "add m (Suc n) = Suc (add m n)"
```

The helper lemma proofs for commutativity
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

For a detailed explanation, [See Section 8.3.3 Commutative Property](./assets-10/8.3_tool/8.3_exercises.md#communative-property-proof)

*The Isabelle .thy file for this exercise is located [here](../content/assets-10/8.3_tool/exercise_2_2.md)*

*This form is an Isar style proof. The following example will be an older style tactic based proof.*


## Intro Example - Flattening and Length Invariant

<!-- show something interesting about tool, logic, etc and can be digested and understood with minimum experience -->

The List Flattening and Length Preservation exercise is adjusted from [this exercise](https://isabelle.in.tum.de/exercises/lists/sum/sol.pdf). First try the exercise yourself, and if stuck, reference the document linked.

### List Flattening

Define a recursive function `fun flatten :: 'a list list => 'a list` that takes a list of lists as input, flattens it, and returns that flattened list. Flattening is simply turning a multi-dimensional list into a single list by concatenating inner lists. For example, if we have $[[1,2], [3,4], [5]]$, then flattening would yield $[1,2,3,4,5]$.

For the base case, simply check if the input list is empty, and if so, return an empty list. For the recursive case, match a non-empty list with (xs # xss) and concatenate xs (using @) with the result of flattening xss.

```{dropdown} Show Answer
~~~isabelle
fun flatten :: "'a list list => 'a list" where
  "flatten [] = []" |
  "flatten (xs # xss) = xs @ flatten xss"
~~~
```

Use a quick lemma with simp to confirm that the function works:
```isabelle
lemma "flatten [[1::nat, 2], [3,4], [5,6], [7]] = [1,2,3,4,5,6,7]"
  apply simp
  done
```
If there are no errors, then the flatten function is implemented correctly.

### Length Invariant

The next step is to prove that the flatten function implemented is *length invariant*, meaning that the operation doesn't create or lose elements, but instead only performs simple concatenation.

Define a lemma called `lemma length_flatten:`, and check that for all xss, the length of flatten(xss) equals the sum of the lengths of the lists inside xss using.

```isabelle
lemma length_flatten:
  "length (flatten xss) = sum_list (map length xss)"
```

Since this proof is relatively simple, a tactic based approach would be ideal. Set up the tactic based proof by induction by using `apply (induct xss)`

There should now be 2 sub-goals, and from there, simply leverage the Sledgehammer tool to solve proof obligations.

The full proof is here. Isabelle will recognize the lemma as a theorem when all proof obligations have been satisfied.
```{dropdown} Show Answer
~~~isabelle
lemma length_flatten:
  "length (flatten xss) = sum_list (map length xss)"
  apply (induct xss)
    apply simp
  by simp
~~~
```

*The Isabelle .thy file for this exercise is located [here](../content/assets-10/8.4_intro/list_flatten.md)*

*In addition to this exercise, there is also an introduction exercise to syllogistic logic<sup><a href="#MossSyllogism">[34]</a></sup> in Isabelle by Alexander Kurz linked [here](appendix-syllogistic-logics.md).*


## The Landscape of Tools

### Interactive Theorem Provers

**HOL4** is part of the "HOL" family of interactive theorem provers, using classical higher-order logic and following the LCF approach to ensure soundness. Developed by Michael J. C. Gordon, the system is implemented in ML, and is a direct descendent of the original HOL88 system. Because HOL4 shares the same underlying logic as Isabelle/HOL, many theories and proof patterns are generally portable between the two tools.

**Rocq** (formerly Coq) is an interactive theorem prover based on the Calculus of Inductive Constructions (CIC), which is dependently typed $\lambda$-calculus that extends the Calculus of Constructions with inductive types. This extension allow propositions to be represented as types and proofs as programs, enabling highly expressive specifications. Rocq is mainly implemented in OCaml with some C, and it's dependent type theory allows it to have greater expressive power over Isabelle/HOL.

**Lean (4)** is another proof assistant that follows a similar but more modern variant of dependent type theory. Like Rocq, Learn also extends the Calculus of Constructions with inductive types. Lean 4 in particular is mostly implemented in Lean (with some C++), and can have its Lean theorem prover produce C code. Like Rocq, Lean 4's dependent type theory also supports greater expressive power compared to Isabelle/HOL.

### Automated Theorem Provers

**Leo III** is an automated theorem prover for classical higher-order logic that supports all common TPTP input dialects and is based on paramodulation calculus with ordering constraints for reasoning. Leo III is written in Scala and runs on the JVM (Java Virtual Machine). Compared with ITPs (interactive theorem provers) like Isabelle/HOL, Leo III trades human-guided proof structuring and granular control for full automation, allowing it to rapidly discharge proof obligations.<sup><a href="#LeoIII">[28]</a></sup>

**Satallax** is another automated theorem prover for classical higher-order logic and is based on Church's simple type theory with extensionality and choice operators. It is implemented in OCaml and uses the SAT solver MiniSat for its proof search. Basically, Satallax generates propositional clauses corresponding to the rules of a complete tableau calculus and calls MiniSat periodically to test the satisfiability of these clauses.<sup><a href="#Satallax">[16]</a></sup>

### Programming Languages

**F\*** is a dependently typed programming language that integrates program development with proof construction in a single system. It's type system lets you encode precise specifications and it uses SMT solvers to automatically discharge proof obligations while still supporting interactive proof guidance when necessary, similar to Isabelle and its Sledgehammer tool. More information about F* with a web-based tutorial can be found [here](https://fstar-lang.org/tutorial/).


## Algorithms

### Matching and Unification

Matching and unification are core algorithms in Isabelle/HOL that let the system find substitutions for schematic variables so that rules, lemmas, or patterns can be applied to the current proof goal. Introduced in Section 5.8 in *A Proof Assistant for Higher-Order Logic*<sup><a href="#Isabelle/HOL_ProofAssistant">[3]</a></sup>, these processes are essential because they enable Isabelle/HOL to automatically instantiate facts and guide proof search without significant manual effort. In Isabelle/HOL, matching often uses *higher-order pattern unification* because terms can include $\lambda$-abstractions and variables that represent functions, meaning that the algorithm must respect equivalence under various $\lambda$-calculus conversion rules (such as $\beta$-reduction) rather than just syntactic/text-based equality. Basically, higher-order unification must account for the way function application and variable binding behave in the typed $\lambda$-calculus that underlies higher-order logic. In practice, this allows Isabelle/HOL handle the richer structure of higher-order logic, such as functions and bound variables, and apply the resulting substitutions directly in tactics and inference steps during proof construction.


### Simplification & Rewriting

Term simplification, introduced in Section 3.1 in *A Proof Assistant for Higher-Order Logic*<sup><a href="#Isabelle/HOL_ProofAssistant">[3]</a></sup> is a core component of Isabelle/HOL’s rewriting infrastructure. It repeatedly applies equational theorems (theorem that states an equality between two terms) as rewrite rules to transform terms into simpler forms, with these rules typically marked by the simp attribute so that the simplifier can use them automatically in tactics such as **simp**, **auto**, and related methods. The simplifier underpins much of Isabelle's automation by reducing goal terms and sub-goals before other tactics run, enabling the construction and success of more complex proofs without extensive manual effort. The Isabelle/HOL simplifier also supports *conditional rewriting*, where rewrite rules are only applied if their premise conditions can be satisfied, increasing flexibility while still ensuring correctness during proof search. This conditional behavior and the ability to tune which rules are active give users granular control over how goals are simplified when developing formal proofs and help automation focus on relevant proof progress rather than unproductive rewrites.

### Proof Search and External Automation

Proof search and external automation serve as the foundation for Isabelle/HOL’s practical automation layer, combining built-in search procedures with calls to external solvers. Isabelle’s classical reasoner, introduced in Section 5.12 in *A Proof Assistant for Higher-Order Logic*<sup><a href="#Isabelle/HOL_ProofAssistant">[3]</a></sup>, is family of tools that perform proof search automatically by leveraging search and backtracking. While the **blast** method is "the main workhorse" for the classical reasoner, Section 5.13<sup><a href="#Isabelle/HOL_ProofAssistant">[3]</a></sup> also talks about **clarify**, **clarsimp**, **force**, **auto**, **fast**, and **best**. 
This is a general summary provided by the document of the different classical reasoning methods:

- **blast** works automatically and is the fastest
- **clarify** and **clarsimp** perform obvious steps without splitting the goal;
safe even splits goals
- **force** uses classical reasoning and simplification to prove a goal; **auto** is
similar but leaves what it cannot prove
- **fast** and **best** are legacy methods that work well with rules involving unusual features

External automation is typically invoked via the Sledgehammer tool. Sledgehammer works by selecting a set of relevant facts from the current proof context, translates it to a format appropriate for ATPs/SMTs, invokes the tools, and then returns the proof text in an appropriate Isabelle proof format (oftentimes via metis). This method helps preserve trust given that Sledgehammer relies on tools that are outside of the Isabelle/HOL ecosystem. More information about using the tool can be found in [Section 8.3.2](#proof-solving-via-sledgehammer), and the official Sledgehammer tool documentation page<sup><a href="Isabelle_Sledgehammer">[35]</a></sup> provides a breadth of detailed, supplementary information.


## Typical Use Cases

Isabelle/HOL is widely used for formal specification and rigorous proof of both mathematical theorems and system properties. It supports expressing precise logical models and verifying them interactively with automation (via the Sledgehammer tool), making it suitable for a variety of tasks such as formalizing algorithms, verifying software and hardware correctness, and reasoning about programming language semantics and protocols. Isabelle/HOL has been used in many different verification projects, such as through the large body of libraries and developments collected in the Archive of Formal Proofs (AFP)<sup><a href="#AFP_History">[27]</a></sup> and as evidenced by the examples in [Section 8.9](#applications-in-industry-and-academia).

## Benchmarks and Competitions

**miniF2F** is a cross-system benchmark of 488 problem statements drawn from both mathematical competitions (IME, AMC and the International Mathematical Olympiad) and high school and undergraduate level mathematics courses. The benchmark targets theorem provers such as Lean, Metamath, Isabelle, and HOL Light in order to enable cross-system comparison of theorem provers and proof automation tools. The goal is to serve as a benchmark for automated and neural theorem proving systems. A formal problem statement is fed into system and the prover must output a fully machine-verifiable proof.<sup><a href="#MiniF2F">[29]</a></sup>

**TPTP** (Thousands of Problems for Theorem Provers) is a library of test problems for testing and evaluating ATPs. Problems are expressed in a simple text-based format for either first-order logic or higher-order logic. TPTP provides a common benchmark with a single, unambiguous reference set of problems so that different ATP systems can be both evaluated and compared with reproducible results.<sup><a href="#TPTP">[36]</a></sup>

**CASC** (The CADE ATP System Competition) is an annual competition of fully automatic, classical logic, ATP systems. The purpose of CASC is to provide a public evaluation of relative capabilities of ATP systems as well as to stimulate research and development of ATP systems. At CASC, ATP system performance is evaluated in terms of the total number of problems solved with an acceptable solution output within a specified time limit, as well as the average time taken for problems solved. CASC is hosted at each CADE and IJCAR conference, both forums for automated deduction.<sup><a href="#CASC">[37]</a></sup>


## Applications in Industry and Academia

In general, Isabelle/HOL appears to have a wide variety of application throughout industry and academia due to the fact that it provides a mathematical assurance of correctness (rather than testing alone). The tool is particularly suited to safety critical systems, such as avionics, embedded systems, industrial process control, SoC design, etc where fault risk must be minimized and certification standards demand high trust.

### Physical Addressing on Real Hardware

Achermann et al.<sup><a href="#Achermann_physicalAddressing">[19]</a></sup> discuss how to formally model and verify physical memory address translation and remapping hardware (such as MMUs) in SoCs (Systems-on-Chip) using Isabelle/HOL. Specifically, they developed a hardware model that encodes translation units and then prove that standard memory operations preserve system invariants.

### FOCUS - Stream Processing Components

Spichkova<sup><a href="#Spichkova_FOCUS">[20]</a></sup> introduces FOCUS, a framework for formal specification and refinement-based verification of interactive systems. Based on stream-processing semantics that model communication histories over directed channels, FOCUS is supported by Isabelle/HOL using the Isar proof language. FOCUS is evaluated on three case studies:

- a steam boiler control system modelled as a distributed real-time system with proofs that water levels and pump actuations satisfy safety and timing constraints
- the FlexRay automotive communication protocol, where FOCUS verifies correct static schedules, channel behavior, and broadcast properties for safety-critical embedded communication
- an Automotive-Gateway system from the Verisoft project, formally specified and refined with guarantees that crash signals trigger correct emergency-service calls and satisfy required data-handling properties.

### IsaBIL - Verifying (In)Correctness of Binaries

Griffin et al.<sup><a href="#Griffin_IsaBIL">[21]</a></sup> present IsaBIL, a binary analysis framework in Isabelle/HOL that is based on BAP (Binary Analysis Platform). IsaBIL formalizes BAP's intermediate language (BIL) and integrates it with Hoare Logic (for proofs of correctness) and incorrectness logic (for proofs of incorrectness). While there is a primary focus is on the RISC-V architecture and C binaries, the authors assert that IsaBIL is a flexible framework that can verify binaries for different languages (C, C++, Rust), toolchains (LLVM, Ghidra), and architectures (x86, RISC-V). The authors prove correctness through some industry level examples such as Lockheed Martin's JSF (Joint Strike Fighter) coding standards and the MITRE ATT&CK database.

### Verlso - Isolation Guarantees of Database Transactions

Ghasemirad et al.<sup><a href="#Ghasemirad_VerIso">[7]</a></sup> present VerIso, a rigorous Isabelle/HOL-based framework for verifying transaction isolation within production level databases. The authors showcase VerIso by modelling the strict two-phase locking (S2PL) protocol and prove that it provides strict serializability (transactions behave as if executed sequentially and that sequential order must match the actual time order of their invocation/commit). In addition, VerIso’s parameterized architecture supports multiple isolation levels and uncovers design-level bugs in protocols such as the TAPIR protocol and its violation of atomic visibility.

### IEEE 754 Floating Point Implementation for MDPs

Kohlen et al.<sup><a href="#Kohlen_float">[22]</a></sup> present a fully verified implementation of the Interval Iteration (II) Algorithm for Markov Decision Processes (MDPs). They model the II algorithm in Isabelle/HOL, use the Isabelle Refinement Framework (IRF) to carry out step-wise refinement down to LLVM bytecode, and extend Isabelle/HOL’s reasoning to support IEEE 754 floating-point arithmetic with directed rounding. Their result is a correct-by-construction floating-point implementation, competitive with industry tools and highly relevant for domains where verified numerical correctness matters, such as embedded systems, SoCs and safety-critical software.

<!-- ### 10.8.6 IsaMini: Isabelle Proof Language for Machine Learning

Xu et al. present MiniLang/IsaMini, a streamlined proof language for Isabelle/HOL designed to improve Large Language Model (LLM) integration in formal verification. The authors convert existing Isar proofs, such as those within Isabelle's Archive of Formal Proofs (AFP), into MiniLang and fine-tune LLMs on this new proof representation. They then use the LLM's macro level proof planning alongside Isabelle's automation (such as Sledgehammer, etc) for micro level proof steps to significantly boost proof success rate. Their work is noteworthy because it brings together formal methods and AI-assisted tooling, reducing manual proof effort and enabling more scalable verification.<sup><a href="#Xu_IsaMini">[7]</a></sup> -->

### Autoformalization with Large Language Models

Wu et al.<sup><a href="#Wu_LLM_Autoformat">[24]</a></sup> show that large language models are particularly effective at performing autoformalization, which is the process of automatically translating natural language mathematics into formal specifications and proofs. Specifically, they note that 25.3% of mathematical competition problems were translated *perfectly* to formal Isabelle/HOL statements. In addition, by using these autoformalized statements to fine-tune an existing neural theorem prover, they managed to improve achieve a 35.2% proof rate on Mini2F2, compared to a baseline proof rate of 29.6%.


## Case Study - Autoformalization with LLMs

For the case study, we will be playing around with autoformalization with a locally hosted LLM. Neither the provided artifacts Wu et al.<sup><a href="#Wu_LLM_Autoformat">[24]</a></sup> nor Xu et al.<sup><a href="Xu_IsaMini">[25]</a></sup> provide model checkpoints or some kind of a modelfile, but instead simply detail the methods the authors had used to fine-tune the model. As a result, for this example, we will simply be using a baseline model along with some examples from Wu et al.<sup><a href="#Wu_LLM_Autoformat">[24]</a></sup> in order to produce valid Isabelle/HOL proofs from natural language input.
Also, its important to keep in mind that the [3 JSON proof examples](./assets-10/8.10_case_study/Wu_Autoformalizations.md) provided by Wu et al.<sup><a href="#Wu_LLM_Autoformat">[24]</a></sup> use certain keywords like **fixes** and **shows** unlike the examples we worked through together above.

**Natural language statement 1:**
*Prove that for any functions f and g and any list xs, mapping f over the result of mapping g over xs is the same as mapping the composition (f ∘ g) over xs.*

OUTPUT:
```isabelle
  theorem
  fixes f :: "'b ⇒ 'c" and g :: "'a ⇒ 'b" and xs :: "'a list"
  shows "map f (map g xs) = map (f ∘ g) xs"`
```

**Natural language statement 2:**
*Define a custom recursive addition function add on natural numbers (using 0 and Suc). Then prove that add is both associative and commutative.*

OUTPUT:
```isabelle
fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc (add m n)"

theorem add_assoc:
  fixes m n p :: nat
  shows "add (add m n) p = add m (add n p)"

theorem add_comm:
  fixes m n :: nat
  shows "add m n = add n m"
```

**Natural language statement 3:**

*Define a custom recursive function flatten that concatenates a list of lists into a single list, then prove the length-invariance property: for any list of lists xss, length (flatten xss) equals the sum of the lengths of the inner lists (i.e., sum_list (map length xss)).*

OUTPUT:
```isabelle
fun flatten :: "'a list list ⇒ 'a list" where
  "flatten [] = []" |
  "flatten (x # xs) = x @ flatten xs"

theorem flatten_length_invariance:
  fixes xss :: "'a list list"
  shows "length (flatten xss) = sum_list (map length xss)"
```

The code is located [here](./assets-10/8.10_case_study/llm_autoformalize.md).

*Currently, the API endpoint for Ollama is pointed towards the Chapman DGX0 Compute Cluster, and runs a Qwen3:30B model.*

<!-- *As of writing this, the laptop I am using has 16 GB of Apple's unified RAM along with the Apple Silicon architecture. As a result, Ollama (which has natural support for Apple's GPU Metal backend) and Qwen3:4B were appropriate choices compared to something like vLLM and bigger parameter models* -->

<!-- In future iterations of this book, if the class was given access to a compute cluster, it would be fairly trivial to migrate to a compute cluster with a better model, as a user would simply need to swap out the hostname in the API endpoint.

For example, if we had `http://localhost:11434/api/generate` and we wanted to leverage the Chapman DGX0 Cluster, then the adjusted API endpoint would be `http://dgx0.chapman.edu:11434/api/generate`. -->


## History

### Origins of Higher-Order Logic

Alonzo Church's work in the 1930s (via $\lambda$-calculus)<sup><a href="#SEP_D.1_LambdaCalc">[39]</a></sup> and 1940s (via type theory)<sup><a href="#SEP_D.2_TypeTheory">[40]</a></sup> and Leon Henkin's work in the 1950s (on general model/Henkin semantics)<sup><a href="#SEP_HOL">[7]</a></sup> laid the foundation for higher-order logic. From their contributions arose an extension of First-Order Logic (FOL) that allows quantification over predicates and functions, enabling reasoning about functions as first class entities.

In the 1970s, Robert Milner develops LCF (Logic for Computable Functions)<sup><a href="#LCF_HOL_history">[38]</a></sup> at Stanford and later Edinburgh, introducing the idea of an interactive theorem prover. LCF pioneers the use of a tactic-based proof automation and the ML meta language, which is designed to let users safely define proof strategies. ML later evolves into OCaml and Standard ML.

In the early 1980s, Michael J. C. Gordon builds upon LCF in order to create the HOL system<sup><a href="#LCF_HOL_history">[38]</a></sup>, which explicitly uses higher-order logic as its core formalism. This HOL system would become the foundation for hardware verification, paving the way and influencing later provers like HOL4 and Isabelle/HOL.

### Development of Isabelle/HOL

Developed in the late 1980's by Lawrence C. Paulson at Cambridge, Isabelle was created as a generic theorem proving framework capable of supporting multiple logical formalisms under a single meta-logic.<sup><a href="#LCF_Isabelle_History">[26]</a></sup>

The HOL instantiation of Isabelle (Isabelle/HOL) became the most widely adopted version due to its strong expressiveness and balance between automation and manual control.<sup><a href="#LCF_Isabelle_History">[26]</a></sup>

Markus Wenzel proposed and developed the Isar Proof Language<sup><a href="#Isar_History">[17]</a></sup> for Isabelle between 1998 and 2001. Isar allows for more structured and human readable proofs, improving clarity over traditional tactic-based approaches like in LCF.

The creation of the Archive of Formal Proofs (AFP) in 2004 established a large, community-driven library of formalized mathematics and computer science. The establishment of the AFP solidified Isabelle/HOL's role in both academia and industry.<sup><a href="#AFP_History">[27]</a></sup>

The integration of tools such as Sledgehammer and external SMT/ATP solvers in 2007 further extend Isabelle/HOL's proof power. The bridging of interactive reasoning and automation allows user to tackle complex goals with minimal manual effort.<sup><a href="#Isabelle_Sledgehammer">[35]</a></sup>


<!-- ## Formal Methods and AI

Not sure if this section is necessary since there are already sections that deal with NTP, LLMs in formal verification, autoformalization, etc. -->

## Current Events within Isabelle/HOL

### Current Development

Active research is increasingly integrating generative and large language models (LLMs) with interactive theorem proving to reduce manual proof construction. This emerging paradigm, termed *Neural Theorem Proving (NTP)*, augments classic automatic theorem proving (ATP) by integrating generative AI with symbolic proof assistants like Isabelle/HOL to enhance automation, guide proof search, and address complex formal reasoning tasks. Recent work by Xu et al. introduces MiniLang/IsaMini<sup><a href="#Xu_IsaMini">[25]</a></sup>, an intermediate proof language designed to improve LLM performance in Isabelle/HOL and significantly boost success rates on standard proof benchmarks compared to generating Isar scripts directly. NTP and hybrid AI frameworks are also being developed to generate and structure complete formal proofs, fine-tune models for syntactically correct proof output, and integrate verification backends to reduce errors and improve correctness in formal verification tasks. These efforts align with broader trends in formal methods research that explore how LLM reasoning can be combined with rigorous symbolic verification to enhance automation, benchmark performance, and increase formal verification scalability.

### Research Challenges

Despite ongoing advances, substantial research challenges remain in Isabelle/HOL’s ecosystem, particularly at the intersection of formal verification and generative AI. Interactive theorem proving in Isabelle/HOL still depends heavily on human guidance through structured Isar proofs, making large-scale developments both labor-intensive and error-prone. The integration of LLM-based techniques introduces additional difficulties, such as translating model output into Isabelle’s strict proof language, mitigating hallucinations and syntactic errors, and obtaining sufficiently large, high-quality datasets of formal proofs for training. While intermediate languages such as MiniLang/IsaMini<sup><a href="#Xu_IsaMini">[25]</a></sup> can significantly improve LLM performance, they also highlight the sensitivity of proof success to representation choices and data quality. Moreover, bridging the gap between informal specifications and fully formalized Isabelle theories, commonly termed *autoformalization*<sup><a href="#Wu_LLM_Autoformat">[24]</a></sup>, remains a major obstacle, as current LLMs struggle to reliably produce complete, semantically correct formalizations without human intervention.

### Conferences and Workshops

- **[International Conference on Interactive Theorem Proving (ITP)](https://itp-conference.github.io/)** - dedicated to interactive theorem proving and related topics, ranging from theoretical foundations to implementation aspects and applications in program verification, security, and formalization of mathematics.

- **[Isabelle Workshop](https://sketis.net/isabelle/isabelle-workshop-2026)** - a workshop focused on Isabelle where users and developers can present tool developments, formalization projects, and ongoing research papers.

- **[International Joint Conference on Automated Reasoning (IJCAR)](https://ijcar.org//conferences)** - international conference covering automated and interactive reasoning which merges several leading conferences and events, such as the Conference on Automated Deduction (CADE), TABLEAUX, and FroCoS, into a single forum covering foundations, tools, and applications in automated reasoning.

- **[Archive of Formal Proofs (AFP)](https://www.isa-afp.org/)** - while not an explicit conference, the AFP functions like a curated repository and journal for Isabelle/HOL proofs, hosting a large collection of mechanically checked proof libraries and scientific developments that are often associated with conference or journal publications.


## References

<style>
.citation-entry:target {
  background-color: rgba(201, 184, 91, 0.35);
  padding: 4px 8px;
  border-left: 3px solid #e0b400;
  transition: background-color 0.25s ease;
  scroll-margin-top: 3rem;
}
</style>

### eBooks and Textbooks

<ul>

  <li id="ConcreteSemantics" class="citation-entry">
    [1]: Nipkow and Klein (2014)
    <a href="http://www.concrete-semantics.org/index.html">Concrete Semantics: With Isabelle/HOL</a>, Springer Publishing Company, Incorporated.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Isabelle_Logics" class="citation-entry">
    [2]: Nipkow, Paulson, and Wenzel (2009)
    <a href="https://isabelle.in.tum.de/website-Isabelle2009-1/dist/Isabelle/doc/logics-HOL.pdf">Isabelle’s Logics: HOL</a>, Isabelle2009 Documentation.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Isabelle/HOL_ProofAssistant" class="citation-entry">
    [3]: Nipkow, Paulson, and Wenzel (2025)
    <a href="https://isabelle.in.tum.de/doc/tutorial.pdf">Isabelle/HOL: A Proof Assistant for Higher-Order Logic</a>, Springer-Verlag.

  <span style="display:block; height:0.1em;"></span>

  <li id="andrews2002" class="citation-entry">
    [4]: Peter B. Andrews (2002)
    <a href="https://dl.acm.org/doi/10.5555/581793#">Introduction to Mathematical Logic and Type Theory: To Truth through Proof (2nd. ed.)</a>, Kluwer Academic Publishers, USA.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Paulson_LCF" class="citation-entry">
    [5]: Laurence C. Paulson (1987)
    <a href="https://assets.cambridge.org/97805213/46320/sample/9780521346320ws.pdf">Logic and Computation: Interactive Proof with Cambridge LCF</a>, Cambridge University Press, USA.

  <span style="display:block; height:0.1em;"></span>

  <li id="Teege_IntroIsabelle" class="citation-entry">
    [6]: Gunnar Teege (2025)
    <a href="https://github.com/gteege/gentle-isabelle/blob/main/man-isabelle.pdf">A Gentle Introduction to Isabelle and Isabelle/HOL</a>, Universität der Bundeswehr München.

</ul>

### Online Articles

<ul>

  <li id="SEP_HOL" class="citation-entry">
    [7]: Jouko Väänänen (2024)
    <a href="https://plato.stanford.edu/entries/logic-higher-order/">Second-order and Higher-order Logic</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University

  <span style="display:block; height:0.1em;"></span>

  <li id="SEP_ChurchTypeTheory" class="citation-entry">
    [8]: Benzmüller and Andrews (2025)
    <a href="https://plato.stanford.edu/entries/type-theory-church/">Church’s Type Theory</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University.

  <span style="display:block; height:0.1em;"></span>

  <li id="SEP_TypeTheory" class="citation-entry">
    [9]: Thierry Coquand (2022)
    <a href="https://plato.stanford.edu/entries/type-theory/">Type Theory</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University

  <span style="display:block; height:0.1em;"></span>

  <li id="Kurz_LambdaSemantics" class="citation-entry">
    [10]: Alexander Kurz (2023)
    <a href="https://hackmd.io/@alexhkurz/H1e4Nv8Bv">Semantics of the Lambda Calculus</a>, CPSC 354 Programming Languages, Chapman University.

  <span style="display:block; height:0.1em;"></span>

  <li id="Kurz_LambdaSyntax" class="citation-entry">
    [11]: Alexander Kurz (2023)
    <a href="https://hackmd.io/@alexhkurz/S1D0yP8Bw">Syntax of Lambda Calculus</a>, CPSC 354 Programming Languages, Chapman University.

  <span style="display:block; height:0.1em;"></span>

  <li id="Stanford_LambdaCalc_TypeTheory" class="citation-entry">
    [12]: Deutsch and Marshall (2025)
    <a href="https://plato.stanford.edu/entries/church/supplementD.html">Supplement D: The λ-Calculus and Type Theory</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="SEP_D.1_LambdaCalc" class="citation-entry">
    [39]: Deutsch and Marshall (2025)
    <a href="https://plato.stanford.edu/entries/church/supplementD.html#D1ChurLambCalc">D.1 Church’s Lambda Calculus</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University.

  <span style="display:block; height:0.1em;"></span>

  <li id="SEP_D.2_TypeTheory" class="citation-entry">
    [40]: Deutsch and Marshall (2025)
    <a href="https://plato.stanford.edu/entries/church/supplementD.html#D2ChurSimpTheoType">D.2 Church’s Simple Theory of Types</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University.

  <span style="display:block; height:0.1em;"></span>

  <li id="SEP_LambdaCalc" class="citation-entry">
    [13]: Alama and Korbmacher (2023)
    <a href="https://plato.stanford.edu/archives/win2024/entries/lambda-calculus/">The Lambda Calculus</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University.

  <span style="display:block; height:0.1em;"></span>

  <li id="SEP_CategTheory" class="citation-entry">
    [14]: Jean-Pierre Marquis (2023)
    <a href="https://plato.stanford.edu/entries/category-theory/">Category Theory</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University

  <span style="display:block; height:0.1em;"></span>

  <li id="SEP_AutomatedReasoning_HOL" class="citation-entry">
    [15]: Frederic Portoraro (2025)
    <a href="https://plato.stanford.edu/entries/reasoning-automated/#HigOrdLog">Automated Reasoning: Section 3.1 on Higher-Order Logic</a>, The Stanford Encyclopedia of Philosophy, Metaphysics Research Lab, Stanford University.

  <span style="display:block; height:0.1em;"></span>

  <li id="Satallax" class="citation-entry">
    [16]: Chad E. Brown (2012)
    <a href="https://ps.uni-saarland.de/Publications/documents/Brown2012b.pdf">Satallax: An Automatic Higher-Order Prover</a>, Saarland University, Saarbr¨ucken, Germany.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Isar_History" class="citation-entry">
    [17]: Makarius (Markus) Wenzel (1999)
    <a href="https://web.cs.wpi.edu/~dd/resources_isabelle/Isar-TPHOLs99.wenzel.pdf">Isar — a Generic Interpretative Approach to Readable Formal Proof Documents</a>, Theorem Proving in Higher Order Logics (TPHOLs 1999), volume 1690 of Lecture Notes in Computer Science. Springer-Verlag.
  </li>

</ul>

### Research Papers

<ul>

  <li id="Church_TypeTheory" class="citation-entry">
    [18]: Alonzo Church (1940)
    <a href="https://www.jstor.org/stable/2266170">A Formulation of the Simple Theory of Types</a>, The Journal of Symbolic Logic 5(2): 56–68.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Achermann_physicalAddressing" class="citation-entry">
    [19]: Achermann, Humbel, Cock, and Roscoe (2018)
    <a href="https://people.inf.ethz.ch/troscoe/pubs/achermann_itp_2018.pdf">Physical Addressing on Real Hardware in Isabelle/HOL</a>, Department of Computer Science, ETH Zurich.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Spichkova_FOCUS" class="citation-entry">
    [20]: Maria Spichkova (2014)
    <a href="https://arxiv.org/abs/1405.1512">Stream processing components: Isabelle/HOL formalisation and case studies</a>, arXiv preprint arXiv:1405.1512.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Griffin_IsaBIL" class="citation-entry">
    [21]: Griffin, Dongol, and Raad (2025)
    <a href="https://arxiv.org/abs/2504.16775v1">IsaBIL: A Framework for Verifying (In)correctness of Binaries in Isabelle/HOL (Extended Version)</a>, arXiv preprint arXiv:2504.16775.

</ul>

### Research Papers

<ul>

  <li id="Church_TypeTheory" class="citation-entry">
    [18]: Alonzo Church (1940)
    <a href="https://www.jstor.org/stable/2266170">A Formulation of the Simple Theory of Types</a>, The Journal of Symbolic Logic 5(2): 56–68.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Achermann_physicalAddressing" class="citation-entry">
    [19]: Achermann, Humbel, Cock, and Roscoe (2018)
    <a href="https://people.inf.ethz.ch/troscoe/pubs/achermann_itp_2018.pdf">Physical Addressing on Real Hardware in Isabelle/HOL</a>, Department of Computer Science, ETH Zurich.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Spichkova_FOCUS" class="citation-entry">
    [20]: Maria Spichkova (2014)
    <a href="https://arxiv.org/abs/1405.1512">Stream processing components: Isabelle/HOL formalisation and case studies</a>, arXiv preprint arXiv:1405.1512.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Griffin_IsaBIL" class="citation-entry">
    [21]: Griffin, Dongol, and Raad (2025)
    <a href="https://arxiv.org/abs/2504.16775v1">IsaBIL: A Framework for Verifying (In)correctness of Binaries in Isabelle/HOL (Extended Version)</a>, arXiv preprint arXiv:2504.16775.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Ghasemirad_VerIso" class="citation-entry">
    [22]: Ghasemirad et al. (2025)
    <a href="https://arxiv.org/abs/2503.06284">VerIso: Verifiable isolation guarantees for database transactions</a>, arXiv preprint arXiv:2503.06284.

  <span style="display:block; height:0.1em;"></span>

  <li id="Kohlen_float" class="citation-entry">
    [23]: Kohlen et al. (2025)
    <a href="https://arxiv.org/abs/2501.10127v3">A formally verified IEEE 754 floating-point implementation of interval iteration for MDPs</a>, International Conference on Computer Aided Verification, Cham: Springer Nature Switzerland.

  <span style="display:block; height:0.1em;"></span>

  <li id="Wu_LLM_Autoformat" class="citation-entry">
    [24]: Wu et al. (2022)
    <a href="https://openreview.net/forum?id=IUikebJ1Bf0">Autoformalization with Large Language Models</a>, NeurIPS 2022 Conference.

  <span style="display:block; height:0.1em;"></span>

  <li id="Xu_IsaMini" class="citation-entry">
    [25]: Xu et al. (2025)
    <a href="https://arxiv.org/abs/2507.18885">IsaMini: Redesigned Isabelle Proof Language for Machine Learning</a>, arXiv preprint arXiv:2507.18885.

  <span style="display:block; height:0.1em;"></span>

  <li id="LCF_Isabelle_History" class="citation-entry">
    [26]: Paulson, Nipkow, and Wenzel (2019)  
    <a href="https://arxiv.org/abs/1907.02836">From LCF to Isabelle/HOL</a>, Formal Aspects of Computing 31.6 (2019): 675-698.

  <span style="display:block; height:0.1em;"></span>

  <li id="AFP_History" class="citation-entry">
    [27]: Makarius (Markus) Wenzel (2019)
    <a href="https://arxiv.org/abs/1905.07244">Isabelle technology for the Archive of Formal Proofs with application to MMT</a>, arXiv preprint arXiv:1905.07244.

  <span style="display:block; height:0.1em;"></span>

  <li id="LeoIII" class="citation-entry">
    [28]: Steen and Benzmüller (2018)
    <a href="https://arxiv.org/abs/1802.02732">The Higher-Order Prover Leo-III (Extended Version)</a>, IJCAR 2018, Oxford, UK.

  <span style="display:block; height:0.1em;"></span>

  <li id="MiniF2F" class="citation-entry">
    [29]: Zheng, Han, and Polu (2022)
    <a href="https://arxiv.org/abs/2109.00110">MiniF2F: A Cross-System Benchmark for Formal Olympiad-Level Mathematics</a>, ICLR 2022.
  </li>

</ul>

### Videos

<ul>

  <li id="LigerLearn_LambdaPrimer" class="citation-entry">
    [30]: LigerLearn (2023)
    <a href="https://www.youtube.com/watch?v=9MtE5ONrQyk">Lambda (λ) Calculus Primer</a>, YouTube.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="LigerLearn_LambdaEval" class="citation-entry">
    [31]: LigerLearn (2023)
    <a href="https://www.youtube.com/watch?v=VS_GK-9xUO4">Lambda (λ) calculus evaluation rules (δ, β, α, η conversion/reduction)</a>, YouTube.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="TypeTheory_Youtube" class="citation-entry">
    [32]: Mark Jago / Attic Philosophy (2025)
    <a href="https://www.youtube.com/watch?v=TrYosPPCQAY">Type Theory in Computer Science, Linguistics, Logic</a>, YouTube.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Lugg_CategoryTheory" class="citation-entry">
    [33]: Oliver Lugg (2022)
    <a href="https://www.youtube.com/watch?v=yAi3XWCBkDo">A Sensible Introduction to Category Theory</a>, YouTube.
  </li>

</ul>

### Miscellaneous

<ul>

  <li id="MossSyllogism" class="citation-entry">
    [34]: Larry Moss (2015)
    <a href="https://logic.berkeley.edu/colloquium/MossSlides.pdf">Natural Logic</a>, UC Berkeley Logic Seminar.
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="Isabelle_Sledgehammer" class="citation-entry">
    [35]: Blanchette, Desharnais, Paulson, and Bartl (2025)
    <a href="https://isabelle.in.tum.de/doc/sledgehammer.pdf">Hammering Away: A User’s Guide to Sledgehammer for Isabelle/HOL</a>, Isabelle 2025 Documentation
  </li>

  <span style="display:block; height:0.1em;"></span>

  <li id="TPTP" class="citation-entry">
    [36]: Geoff Sutcliffe (2017)
    <a href="https://tptp.org/TPTP/">The TPTP Problem Library and Associated Infrastructure: From CNF to TH0</a>, Journal of Automated Reasoning 59(4): 483–502.

  <span style="display:block; height:0.1em;"></span>

  <li id="CASC" class="citation-entry">
    [37]: Geoff Sutcliffe (2016)
    <a href="https://tptp.org/CASC/">The CADE ATP System Competition – CASC</a>, AI Magazine 37(2): 99–101.

  <span style="display:block; height:0.1em;"></span>

  <li id="LCF_HOL_history" class="citation-entry">
    [38]: Mike Gordon (1996)
    <a href="https://www.cl.cam.ac.uk/archive/mjcg/papers/HolHistory.pdf">From LCF to HOL: a short history</a>

</ul>

<!-- https://isabelle.in.tum.de/library/HOL/HOL/document.pdf -->

<!-- calculus of inductive constants (in coq)
https://flint.cs.yale.edu/cs428/coq/doc/Reference-Manual006.html -->


## Suggestions for Future Work

I definitely agree having an explicit chapter on both first-order logic and theorem provers related to FOL would be helpful, especially as a preceding chapter to the current one about higher-order logic and Isabelle. This chapter should also include popular Automatic Theorem Provers (ATPs) for FOL, and could serve as a nice introduction into theorem proving and "stronger" tools such as Isabelle/HOL and Lean.

It might also be interesting to see different chapters covering automatic theorem provers such as Vampire or Satallax vs interactive theorem provers such as Isabelle/HOL or Lean. In addition, there should be a clear division made between first order logic ATPs such as the aforementioned Vampire and higher-order logic ATPs such as Satallax. In addition, it would also be interesting and useful to either create or find an online Isabelle/HOL program that can run in a web browser, similar to the Lean Game Server. This way users can be quickly onboarded to the tool without having to go through download, setup, version compatibility issues, and other miscellaneous problems that may arise.

It may also be cool to see a more interactive history section, with custom CSS and JS injection that allows for a detailed history timeline of Isabelle/HOL development, and theorem provers in general within the context of higher-order logic. In addition, having some kind of visual aid to see the different relationships between the "major figures" within this space would be helpful as well. For example, Peter Andrews was a doctorate student of Alonzo Church, and while Laurence Paulson was responsible for the development of LCF, we can still see from the citations (where he is often credited alongside Nipkow and Wenzel) that he is still very invovled with the documentation and development of Isabelle/HOL.

## Contributors

Initial Author: Spencer Au

Peer Reviewer: Wayne Chong