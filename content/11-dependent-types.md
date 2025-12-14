# Dependent Type Theory with Lean

*Author: Khoa Nguyen*

## Introduction

This chapter presents dependent type theory with Lean, demonstrating how types can depend on values and enabling "proofs as programs" through the Curry-Howard correspondence.

## Idea

Dependent Type Theory (DTT) is the idea that types can depend on values. In traditional programming languages, types classify values. `Int` describes integers, `Bool` describes True or False, etc... With dependent type theory, a type itself depends on a value. For example, instead of defining a single `array` type, we define `array n A`, meaning “an array of length n whose elements are of type A.” This makes certain properties, like the dimension of an array, part of the type system itself. The compiler can then verify these constraints automatically.

This expressiveness blurs the boundary between proofs and programs. In dependent type theory, writing a function that computes something often simultaneously constructs a proof of its correctness. For instance, a function that returns the sum of two natural numbers can be defined alongside a proof that addition is associative or commutative, proofs that Lean, Coq, or Agda can check mechanically.

Dependent Type Theory(DTT) is a unifying foundation for:
- Formal methematics where theorems and proofs are treated as typed objects.
- Verified programming where correctness is guaranteed by construction.

Think of DTT as the language that connects mathematics, logic, and software engineering. It transforms "what is true" into "what is computed" and vice versa.

Dependenty Type Theory allows us to design systems in which the structure of code mirrors the structure of mathematics. This is the essence of the proofs-as-programs pradigm: a verified program is not something we write after designing an algorithm; it is the algorithm, expressed in a logical language rich enough to verify itself. 

## Basic Theory

To understand DTT, we begin by situating it within the broader landscape of type systems and logical foundation.

Type theory originated as an alternative to set theory, most famously through the work of Bertrand Russell and Alonzo Church. The simply typed lambda calculus provided a framework where every term has a type, and functions are first-class citizens. In this setting, a type may be thought of as a “set of allowable values,” and a program as a “proof that a value exists.”

Dependent types generalize this by allowing types to vary depending on terms. Formally, if `A` is a type and `a : A`, then we may form another type `B a` that depends on `a`. The dependent function type is then written: $(\Pi x:A),B(x)$ which can be read as "for every `x` of type `A`, there exists a term of type `B(x)`." This construct generalizes both functions and universal quantification.

### The Curry-Howard Correspondence

The Curry-Howard Correspondence underlies DTT, establising a deep analogy between logic and computation:

| Logic | Type Theory | Computation |
|---|---|---|
| Proposition | Type | Specification |
| Proof | Term(program) | Implementation |
| Proof normalization | Term reduction | Program execution |

In this view, proving a proposition corresponds to constructing a program of a certain type.
For example:
- A proof of $A \rightarrow B$ corresponds to a function from `A` to `B`.
- A proof of $A \land B$ corresponds to a pair `(a, b)`.
- A proof of $A \lor B$ corresponds to either `inl a` (`a` belongs to left type `A`) or `inr b`(`b` belongs to right type `B`).

Dependent types extend this by allowing logical quantification to range over terms, i.e. a function's return type can be determined by the value of its input, rather than just its type. Thus, "for every `n`, there exists a vector of length `n` sorted in ascending order" can be written as a dependent function type.

The Curry-Howard correspondence unifies programming, mathematics, and logic into a single framework: to prove is to program.

## Tool
The following installation is pull directly from Lean-["Install Lean"](https://lean-lang.org/install/)

- Install VS Code
- Install the official Lean 4 extension in VS Code 
- Complete the extension by following the guideline of Lean 4 extension:
    - Click the "$\forall$" symbol at the top right of the window.
    - Hover down to "Documentation..."
    - Click on "Show Setup Guide"
    - Follow the guide until "Install Lean" option light up
    - Click "Install Lean"

## Introductory Examples

One of the most effective ways to begin learning Lean is through the [Lean Game Server](https://adam.math.hhu.de/). These games remove setup overhead, eliminate the intimidation factor of reading large formal libraries, and instead invite learners to explore Lean through hands-on examples. Two of the most valuable games for beginners are the [Logic Games](https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic) and the [Natural Number Games](https://adam.math.hhu.de/#/g/leanprover-community/nng4). Both games illustrate the power of formal methids in a setting that is playful and intellectually rigorous.

### Logic Game

The Logic Game introduces users to the foundational rules of formal logic such as implication, negation, conjunction, disjunction, quantifiers, etc... through short, progressively challenging proof puzzles. Its educational value comes from several key features:

#### Immediate Feedback Loop

Unlike traditional textbooks, the Logic Game responds instantly to every tactic command:
- If a tactic is correct, Lean advances the goal state.
- If a tactic is wrong, Lean explains why.

This tight feedback loop mirrors the experience of interacting with an automated proof assistant in real industrial or research settings, lowering the learning curve dramatically.

#### The "Mental Model" of Lean

The Logic Game is explicitly designed to teach users how Lean thinks about logic:
- Every tactic corresponds to a precise logical rule.
- Users see how Lean's kernel enforces correctness step by step.

This builds intuition for dependent type theory and Curry–Howard correspondence (propositions-as-types), but without requiring the learner to know any theory beforehand.

#### Encourages Experimentation

Players can try tactics freely without risk. This experimentation fosters:
- pattern recognition
- tactical reasoning
- an understanding of proof search strategies

These habits carry directly over to real software verification tasks.

### Natural Number Game

The Natural Number Game (NNG) has become one of the most popular introductions to Lean worldwide. The educational value stems from how it blends mathematics, computation, and logic.

You will prove fundamental facts such as `0 != succ n`, addition is associative and commutative, `succ` is injective, multiplication distributes over addition, etc...

#### How Mathematics Can Be Built From Axiom

Students are often familiar with these results from prior coursework, but they rarely see how foundational proofs look at the axiomatic level. The NNG demonstrates: 
- How definitions induce computation rules
- How to manipulate inductive types
- How recursion and induction arise naturally

This concreteness demystifies dependent type theory: users experience how a simple inductive type gives rise to a rich structure.

#### Inductive Reasoing Through Direct Interaction

Induction is not merely stated, it is performed repeatedly. Lean forces the user to spell out base cases, induction hypotheses, goals and recursive patterns. This active engagement builds intuition for proof assistants handle recursion and induction which are core tools in both methematics and formal verfication.

#### Motivates Algorithmic Thinking

Because natural number definitions are computational, players quickly see how rewriting works, pattern matching influences evaluation, recursive structures behave algorithmically. This bridges the gap between formal mathematics and computer science practice, showing why proof assistants can serve as both logical frameworks and programming languages.

## The Landscape of Tools

This section presents a landscape view of major tools in the DTT ecosystem as of 2025. It will breakdown their design trade-offs, typical use-cases, and relative strengths or weaknesses.

| Tool/Language | Description & Strengths | Typical Use Cases / Trade-offs |
|-----|-----|-----|
| Lean (Lean 4 + mathlib) | A modern proof assistant + functional programming language based on dependent types (Calculus of Constructions + inductives + universes). Offers a powerful elaboration engine, a small trusted kernel, fast incremental compilation, and support for both interactive tactics and functional proof style. | Great for formal mathematics, verified algorithms, interactive theorem proving, and even practical verification tasks. Its large community and active library (mathlib) make it a go-to for general-purpose verification or mathematics. |
| Coq | One of the oldest and most widely used proof assistants based on DTT (or similar). Supports extraction to programming languages, large body of existing formalization (math, compilers, verified software), powerful tactic languages. | Best for verified software projects, certified compilers (e.g. CompCert), verified algorithms, and academic formalization. Has a steep learning curve, sometimes verbose proof scripts, and a heavier kernel than simpler languages. |
| Agda | A dependently typed programming language/proof assistant more in the “programming + proof as functional style” camp (rather than tactic-based). Similar to MLTT tradition, with strong emphasis on inductive families, totality, and interactive evaluation. | Good for experimental formalizations, teaching type theory, writing dependently typed programs. More suited for small-to-medium proofs; less focused on industrial-scale verification or large libraries. |
| Idris / Idris 2 | A dependently typed programming language with a focus on general-purpose programming, not only proof. Supports effects, code generation (e.g. C, JS), totality checking or partial functions depending on settings. | Good when you want a language with expressive types and runtime code generation for building verified-but-executable programs. Less mature than proof assistants; less library support; proofs may be more manual. |
| Haskell | A general-purpose, functional programming language that is statically typed with type inference and lazy evaluation. Popular in academia and industry | It has practical, industrial-strength functional programming and powerful abstractions, rich ecosystem, compilers (GHC) with pluggable extensions. Typically used in high-assurance and mission-critical systems, data transformation pipelines, and systems that benefit from strong static guarantees. It has a steep learning curve; unpredictable performance due to laziness; smaller ecosystem; harder hiring pipeline; abstract debugging; less ergonomic for low-level systems |

When selecting among tools, you should weigh:
- Expressiveness vs. automation: More expressive systems (Lean, Coq, Agda, Idris) allow rich invariants and proofs but often need manual proof work. Automated or SMT-backed tools trade expressiveness for easier automation.
- Library / ecosystem maturity: Tools like Lean (with mathlib) or Coq have large libraries, others are more experimental. A rich library reduces the need to build basic building blocks from scratch.
- Executable code vs. proof-only: Some tools (Idris, Lean) allow writing code that runs, while also proving properties. Others often focus on proofs and not on extracting executable code, or else code extraction is more ad-hoc.
- User experience / ergonomics: Elaborators, tactic languages, and proof modes dramatically affect productivity. For example, Lean’s elaboration engine is a major advantage for usability. 
- Scalability / maintenance: For large projects, proof maintenance, library design, and modularization become critical. Tools that facilitate factoring, code reuse, automation or tactic writing tend to scale better for big verifications.

## Algorithms

In implementing and using a dependently typed language or proof assistant (like Lean, Coq, Agda, Idris, etc.), a number of non-trivial algorithms lie at the foundation. These algorithms handle typing, type checking/inference, equality checking, unification or normalization, and elaboration. Understanding them gives insight into why dependent types are powerful and why they are hard.

### Bidirectional typechecking / type-inference + type-checking separation

Instead of trying to infer types for all expressions (type inference) or requiring full type annotations everywhere, bidirectional typing splits the typing judgment into two modes:

1. Synthesis (or inference): from a term `t`, compute (synthesize) a type `A`, written informally $t \Rightarrow A$.
2. Checking: given a term `t` and a desired type `A`, check that `t` indeed has type `A`, written $t \Leftarrow A$. 

This matters because full type inference in a dependently typed setting tends to be undecidable or requires heavy annotation, due to types themselves may depend on values. By adopting a bidirectional discipline, one can recover a decidable, predictable algorithmic core for a large class of dependent type theories. ["Generic bidirectional typing for dependent type theories](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Generic+bidirectional+typing+for+dependent+type+theories&btnG=) paper gives a generic account of bidirectional typing for a wide class of dependent type theories, showing that for many theories, a sound and complete bidirectional checker can be derived.

The generic construction yields a type-checking algorithm for a broad class of DTTs, implemented in a prototype tool. This ensures that the type checker for a dependently typed language can remain decidable (under suitable normalization/termination assumptions) while supporting expressive dependent types.

The necessity of type annotations in places where inference is impossible (e.g., lambda abstractions returning dependent types, complex implicit arguments). The complexity of designing good elaboration strategies so that user-facing syntax remains ergonomic even when underlying types are rich and dependent. The burden shifts from runtime safety to compile-time/type-check-time; the user (or tool) must supply sufficient information for checking.

### Equality / Normalization / Conversion / Extensionality Checking

In dependent type theory, type equality (and term equality) is not just "are they syntactically identical?". It often involves computation (normalization), conversion rules ($\beta$-reduction), and user-defined equality/extension rules (e.g., extensionality, definitional equalities). Implementations need an algorithm to decide or check when two types or terms are equal.

The paper [“An extensible equality checking algorithm for dependent type theories”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=An+extensible+equality+checking+algorithm+for+dependent+type+theories&btnG=) introduces a general algorithm combining type-directed extensionality rules with normalization by computation rules, and shows how to classify rules as computational or extensional in a user-definable way. The algorithm is implemented in a proof assistant prototype that supports custom dependent type theories. 
arXiv

Without a robust equality/normalization algorithm, dependent types, especially those involving dependent functions or indexed types,become unwieldy. Many trivial-looking equalities (e.g., rewriting with definitional reduction, simplification) would need to be proven manually. A good algorithm reduces overhead and makes proofs manageable.

### Elaboration

In proof assistants or dependently typed languages, users write code in a friendly high-level syntax (with type annotations optional, implicit arguments, etc.). The elaboration phase translates that syntax into the core type theory: resolves implicit arguments, performs type inference/checking, adds coercions, resolves overloading, etc.

Without a powerful elaboration engine, the user would be burdened with writing full explicit dependent types everywhere. A good elaborator makes dependent typing practical, hiding complexity while retaining guarantees.

The designers of Lean highlight that its "powerful elaboration engine", combined with a small trusted kernel and support for mixed declarative and tactic proof style, make it a mature system for real-world development. 

### Combined algorithmic stack → Decidability + Trust

Bidirectional typing + equality/normalization + elaboration + a small trusted kernel yields a system where:
- Type checking and proof checking remain decidable (modulo normalization / termination constraints),
- User code can stay readable / ergonomic,
- Proof objects are small and checkable (trusted kernel),
- Automation (tactics, tactics + automation, decision procedures) can build on top to ease formalization.

This is the algorithmic backbone that makes modern DTT-based proof assistants usable beyond toy examples.

## Benchmarks and Competitions
- 

## Applications in Industry

In recent years, formally grounded methods for specifying and verifying software and hardware systems have undergone significant uptake. The combination of dependable "symbolic" reasoning, (i.e. logic, type-theory, theorem-proving, etc...) with the explosion of AI-driven development like machine learning, generative models, is opening up new directions for improvements. Here are briefs summaries of recent influential applications. 

### Historical and Influencial Application

- Tokeneer ID Station (NSA smart-card project) is one of the early industrial successes of the "Correctness by Construction" methodology. The case is described by Janet Barnes in [“Experiences in the Industrial use of Formal Methods”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Experiences+in+the+Industrial+use+of+Formal+Methods&btnG=). This article reports on industrial deployment of formal methods under the “Correctness by Construction (CbyC)” approach at Altran Praxis, including the case of the Tokeneer ID Station project for the US NSA. The work describes how formal specification in Z, refinement to code in SPARK with proof of absence of run-time errors, and proof of system-level properties were applied. The project found only five errors post-release and is cited as a rare “success story” of formal methods in industry. The article also candidly discusses challenges: training, tool usability, industrial adoption, and scaling.

- [“Symbolic QED Pre-silicon Verification for Automotive Microcontroller Cores: Industrial Case Study”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CSymbolic+QED+Pre-silicon+Verification+for+Automotive+Microcontroller+Cores%3A+Industrial+Case+Study.%E2%80%9D&btnG=) presents an industrial case study applying the “Symbolic Quick Error Detection (Symbolic QED)” technique in the pre-silicon verification of automotive microcontroller cores (~1,800 flip-flops, ~70,000 logic gates). Symbolic QED detected all logic bugs found by previous industrial verification flows, plus additional ones. It significantly reduced verification effort (e.g., an 8× reduction for a new design, and up to ~60× for subsequent designs). Runtime of bug detection improved dramatically (20 seconds or less) with short counterexamples (≤10 instructions).

- [“Formal methods in dependable systems engineering: a survey of professionals from Europe and North America"](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Formal+methods+in+dependable+systems+engineering%3A+a+survey+of+professionals+from+Europe+and+North+America&btnG=) presents survey results from mission-critical software engineering practitioners, investigating how they use formal methods, their intentions to use them, and perceived challenges. Intrinsic motivation drives use more than regulation. Experienced practitioners plan to use more extensively. Major obstacles remain such as: scalability, skills, education, process compatibility, tool reputation. The survey highlights that despite promising case studies, broad industrial adoption remains constrained.

- [“Industrial-Strength Verification of Solid State Interlocking Programs”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CIndustrial-Strength+Verification+of+Solid+State+Interlocking+Programs.%E2%80%9D&btnG=) describes a tool used on 26 real-world interlockings and used to aument existing testing/inspection processes. It describes an end-to-end workflow that consumes engineering artefacts as produced by signalling designers, automatically encodes safety properties, runs automated theorm provers and SMT solvers, then produces diagnostics so the results are actionable.

### Recent & Emerging Directions

- The paper [“Machine learning and logic: a new frontier in artificial intelligence”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CMachine+learning+and+logic%3A+a+new+frontier+in+artificial+intelligence.%E2%80%9D&btnG=) shows how ML/AI and formal methods (logic, automated reasoning) are increasingly tightly coupled. Both foundational pillars have largely developed independently, but novel and grand challenges demand their integration. The author identify three key paradigms:
    1. Using learning methods for proof-rule selection, solver heuristic and initialization.
    2. Combining inductive learning and deductive reasoning for programming-by-example, synthesis, and verification.
    3. Using solver feedback as corrective layers for ML models to improve accuracy, generalizability and trustworthiness.
They posit that this convergent direction will have major impact on future AI and verification.

- [“Application of AI to formal methods — an analysis of current trends”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CApplication+of+AI+to+formal+methods+%E2%80%94+an+analysis+of+current+trends.%E2%80%9D&btnG=) is a systematic mapping of how AI techniques (including generative models) are being applied to formal methods (and vice versa). It charts emerging directions such as automated invariant generation via ML, proof-assistant tactic synthesis using neural networks, and formal verification of AI/ML system themselves. The analysis highlights both promise of increased automation and reduced annotation and caution. 

- Special issue [“Formal Methods for Industrial Critical Systems”](https://scholar.google.com/scholar?q=%E2%80%9CFormal+Methods+for+Industrial+Critical+Systems%E2%80%9D&hl=en&as_sdt=0%2C5&as_ylo=2024&as_yhi=) compile recent tools and experience reports from industry/critical systems. The issue contributions cover a range of domains and emphasize the needs of improving formal tools and publishing empirical experience showing how formal methods integrate with industrial processes. 

- [VeriBench: End-to-End Formal Verification Benchmark for AI Code Generation in Lean](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&as_ylo=2024&q=%22VeriBench%3A+End-to-End+formal+verification+benchmark+for+AI+code+generation+in+Lean+4%22&btnG=) presents a benchmark suite called VeriBench, designed to evaluate how well large language models (LLMs) can generate complete formal verification artifacts in Lean 4. The experiments show that current frontier LLMs compile and pass only a small fraction of these tasks out of the box. It explicitly highlights how Lean 4’s dependent-type system enables encoding deep invariants. The author argues
that such benchmarks are essential to meaningful progress in automated code verification & provably correct code generation, especially as generative AI becomes more widely used in software engineering.

## Case Study

Let's formalise and verify a transformation pipline for 3-D points in world space. Let's look at a small example where we perform a rotation in place, follow by a translation (moving the point to a different coordinate). This case study will show how dependent types and theorem proving is utilized in computer graphics, like graphical engines utilized in games, movies, animation, etc...

The following case study demonstrates how Lean uses dependent type system to ensures mathematical and computational correctness. By encoding vector dimensions in types and proving geometric invariants such as norm preservation, we move from abstract theory to executable verification. This approach mirrors how formal methods are being integratated into the wider industry.

## History

Type theory and the idea of types as a foundation for mathematics and computation have a long pedigree that connects philosophical logic, lambda calculus, and modern proof assistants.

The story begins with early efforts to avoid paradoxes in naive set theory and logic (Russell, Frege), which motivated ramified and then simple type theories in the first half of the 20th century. Alonzo Church’s formulation of the simple theory of types and the simply-typed lambda calculus provided the computational backbone that later researchers built on. ([Wiki](https://en.wikipedia.org/wiki/History_of_type_theory))

A decisive shift toward dependent types occurred with Per Martin-Löf’s intuitionistic type theory (1970s–1980s). Martin-Löf introduced dependent function ($\Pi$) and dependent pair ($\Sigma$) types, giving a constructive foundation in which types can quantify over values. This made it possible to represent propositions as types and proofs as programs in a very expressive way. The Curry–Howard correspondence, the observation that proofs correspond to programs and propositions to types, fused logic and computation and underpins modern dependently-typed systems. ([See here](https://plato.stanford.edu/entries/type-theory)) 

In the 1980s and 1990s the field consolidated around a handful of influential calculi and systems. The Calculus of Constructions (Coquand & Huet) and the later Calculus of Inductive Constructions became the basis for the Coq proof assistant; Agda and other systems explored dependently typed programming more directly; and the so-called lambda-cube classified a spectrum of type systems. Over the last two decades these theoretical advances have been implemented in robust systems (Coq, Agda, Lean, Idris) and large collaborative libraries (e.g., Lean’s mathlib), enabling both deep mathematical formalization and practical verification projects. ([See here](https://plato.stanford.edu/entries/type-theory))

## Formal Methods and AI

## Current Development

## Resources

- [Lean4 Installation](https://lean-lang.org/install/)

- [Lean Game Logic](https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic)

- ["Install Lean"](https://lean-lang.org/install/). Lean (2025).

- Felicissimo, T. (2025). ["Generic bidirectional typing for dependent type theories"](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Generic+bidirectional+typing+for+dependent+type+theories&btnG=). ACM Transactions on Programming Languages and Systems, 47(1), 1-42.

- Bauer, A., & Komel, A. P. (2022). ["An extensible equality checking algorithm for dependent type theories"](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=An+extensible+equality+checking+algorithm+for+dependent+type+theories&btnG=#d=gs_cit&t=1764487303518&u=%2Fscholar%3Fq%3Dinfo%3AGG4bRcIQJBgJ%3Ascholar.google.com%2F%26output%3Dcite%26scirp%3D0%26hl%3Den). Logical Methods in Computer Science, 18.

- Wadler, Philip. “Propositions as Types.” Communications of the ACM, Vol. 58, No. 12 (Dec. 2015), pp. 75-84. Available as PDF [here](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf)

- [“Intuitionistic Type Theory (Stanford Encyclopedia of Philosophy).”](https://plato.stanford.edu/entries/type-theory-intuitionistic/) Entry by (various) updated Sep. 23 2024.

- Barnes, J. [“Experiences in the Industrial use of Formal Methods.”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Experiences+in+the+Industrial+use+of+Formal+Methods&btnG=) ECEASST 46 (2011).

- Singh, E. et al. [“Symbolic QED Pre-silicon Verification for Automotive Microcontroller Cores: Industrial Case Study.”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CSymbolic+QED+Pre-silicon+Verification+for+Automotive+Microcontroller+Cores%3A+Industrial+Case+Study.%E2%80%9D&btnG=) arXiv (2019).

- Iliasov, A. et al. [“Industrial-Strength Verification of Solid State Interlocking Programs.”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CIndustrial-Strength+Verification+of+Solid+State+Interlocking+Programs.%E2%80%9D&btnG=) arXiv (2021).

- Gleirscher, M., Marmsoler, D. [“Formal methods in dependable systems engineering: a survey of professionals from Europe and North America”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Formal+methods+in+dependable+systems+engineering%3A+a+survey+of+professionals+from+Europe+and+North+America&btnG=) Empir Software Eng 25 (2020).

- Ganesh, V., Seshia, S. A., Jha, S. [“Machine learning and logic: a new frontier in artificial intelligence.”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CMachine+learning+and+logic%3A+a+new+frontier+in+artificial+intelligence.%E2%80%9D&btnG=) Formal Methods Systems Design 60 (2022).

- Stock, S., Dunkelau, J., Mashkoor, A. [“Application of AI to formal methods — an analysis of current trends.”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CApplication+of+AI+to+formal+methods+%E2%80%94+an+analysis+of+current+trends.%E2%80%9D&btnG=) Empir Software Eng (2025). 

- Groote, J. F., Huisman, M. [“Formal Methods for Industrial Critical Systems.”](https://scholar.google.com/scholar?q=%E2%80%9CFormal+Methods+for+Industrial+Critical+Systems%E2%80%9D&hl=en&as_sdt=0%2C5&as_ylo=2024&as_yhi=) Int J Softw Tools Technol Transfer 26 (2024). 

- Miranda et al. ["VeriBench: End-to-End formal verification benchmark for AI code generation in Lean 4"](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&as_ylo=2024&q=%22VeriBench%3A+End-to-End+formal+verification+benchmark+for+AI+code+generation+in+Lean+4%22&btnG=). In Proceedings of the 42nd International Conference on Machine Learning, Vancouver, Canada (PMLR 267) (2025). 

- Wikipedia contributors. (2025, November 28). [History of Type Theory](https://en.wikipedia.org/wiki/History_of_type_theory). Wikipedia. 

- [Type Theory (Stanford Encyclopedia of Philosophy)]( https://plato.stanford.edu/entries/type-theory). (2022, September 6).

## Suggestions for Future Works
