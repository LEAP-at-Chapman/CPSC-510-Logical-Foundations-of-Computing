# Type Theory with Lean

Author: *Khoa Nguyen*

## Introduction

This chapter presents dependent type theory with Lean, demonstrating how types can depend on values and enabling "proofs as programs" through the Curry-Howard correspondence.

## Idea

Dependent Type Theory (DTT) is the idea that types can depend on values. In traditional programming languages, types classify values. `Int` describes integers, `Bool` describes True or False, etc... With dependent type theory, a type itself depends on a value. For example, instead of defining a single `array` type, we define `array n A`, meaning “an array of length n whose elements are of type A.” This makes certain properties, like the dimension of an array, part of the type system itself. The compiler can then verify these constraints automatically.

This expressiveness blurs the boundary between proofs and programs. In dependent type theory, writing a function that computes something often simultaneously constructs a proof of its correctness. For instance, a function that returns the sum of two natural numbers can be defined alongside a proof that addition is associative or commutative, proofs that Lean, Coq, or Agda can check mechanically.

Dependent Type Theory(DTT) is a unifying foundation for:
- Formal mathematics where theorems and proofs are treated as typed objects.
- Verified programming where correctness is guaranteed by construction.

Think of DTT as the language that connects mathematics, logic, and software engineering. It transforms "what is true" into "what is computed" and vice versa.

Dependent Type Theory allows us to design systems in which the structure of code mirrors the structure of mathematics. This is the essence of the proofs-as-programs paradigm: a verified program is not something we write after designing an algorithm; it is the algorithm, expressed in a logical language rich enough to verify itself. 

## Basic Theory

To understand DTT, we begin by situating it within the broader landscape of type systems and logical foundation.

Type theory originated as an alternative to set theory, most famously through the work of Bertrand Russell and Alonzo Church. The simply typed lambda calculus provided a framework where every term has a type, and functions are first-class citizens. In this setting, a type may be thought of as a “set of allowable values,” and a program as a “proof that a value exists.”

Dependent types generalize this by allowing types to vary depending on terms. Formally, if `A` is a type and `a : A`, then we may form another type `B a` that depends on `a`. The dependent function type is then written: $(\Pi x:A),B(x)$ which can be read as "for every `x` of type `A`, there exists a term of type `B(x)`." This construct generalizes both functions and universal quantification.

### The Curry-Howard Correspondence

The Curry-Howard Correspondence underlies DTT, establishing a deep analogy between logic and computation:

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
The following installation is pulled directly from the official Lean installation instructions - ["Install Lean"](https://lean-lang.org/install/)

- Install VS Code
- Install the official Lean 4 extension in VS Code 
- Complete the extension by following the guideline of Lean 4 extension:
    - Click the "$\forall$" symbol at the top right of the window.
    - Hover down to "Documentation..."
    - Click on "Show Setup Guide"
    - Follow the guide until "Install Lean" option light up
    - Click "Install Lean"

To verify that the installation is successful, create a `test.lean` file and enter the following:
- `#eval 1 + 1`
- `#check id`
- `#eval Lean.versionString`

One sign that Lean has been installed correctly is that `#eval` and `#check` turn blue. A screen called `Lean InfoView` appeared with the appropriate results.

## Introductory Examples

One of the most effective ways to begin learning Lean is through the [Lean Game Server](https://adam.math.hhu.de/). These games remove setup overhead, eliminate the intimidation factor of reading large formal libraries, and instead invite learners to explore Lean through hands-on examples. Two of the most valuable games for beginners are the [Logic Games](https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic) and the [Natural Number Games](https://adam.math.hhu.de/#/g/leanprover-community/nng4). Both games illustrate the power of formal methods in a setting that is playful and intellectually rigorous.

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

Induction is not merely stated, it is performed repeatedly. Lean forces the user to spell out base cases, induction hypotheses, goals and recursive patterns. This active engagement builds intuition for how proof assistants handle recursion and induction, which are core tools in both mathematics and formal verification.

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

In implementing and using a dependently typed language or proof assistant (like Lean, Coq, Agda, Idris, etc.), a number of non-trivial algorithms lie at the foundation. These algorithms handle typing, type checking and inference, equality checking, unification or normalization, and elaboration. Understanding them gives insight into why dependent types are powerful and why they present unique computational challenges. This section examines the key algorithmic components that make modern dependent type theory systems both powerful and practical.

### Bidirectional typechecking / type-inference + type-checking separation

Instead of trying to infer types for all expressions (type inference) or requiring full type annotations everywhere, bidirectional typing splits the typing judgment into two modes:

1. Synthesis (or inference): from a term `t`, compute (synthesize) a type `A`, written informally $t \Rightarrow A$.
2. Checking: given a term `t` and a desired type `A`, check that `t` indeed has type `A`, written $t \Leftarrow A$. 

This matters because full type inference in a dependently typed setting tends to be undecidable or requires heavy annotation, due to types themselves may depend on values. By adopting a bidirectional discipline, one can recover a decidable, predictable algorithmic core for a large class of dependent type theories. [Generic bidirectional typing for dependent type theories](https://scholar.google.com/scholar?q=Generic+bidirectional+typing+for+dependent+type+theories+Felicissimo) (Felicissimo et al., 2024) paper gives a generic account of bidirectional typing for a wide class of dependent type theories, showing that for many theories, a sound and complete bidirectional checker can be derived.

The generic construction yields a type-checking algorithm for a broad class of DTTs, implemented in a prototype tool. This ensures that the type checker for a dependently typed language can remain decidable (under suitable normalization/termination assumptions) while supporting expressive dependent types.

The necessity of type annotations in places where inference is impossible (e.g., lambda abstractions returning dependent types, complex implicit arguments). The complexity of designing good elaboration strategies so that user-facing syntax remains ergonomic even when underlying types are rich and dependent. The burden shifts from runtime safety to compile-time/type-check-time; the user (or tool) must supply sufficient information for checking.

### Equality / Normalization / Conversion / Extensionality Checking

In dependent type theory, type equality (and term equality) is not just "are they syntactically identical?". It often involves computation (normalization), conversion rules ($\beta$-reduction), and user-defined equality/extension rules (e.g., extensionality, definitional equalities). Implementations need an algorithm to decide or check when two types or terms are equal.

The paper [“An extensible equality checking algorithm for dependent type theories”](https://scholar.google.com/scholar?q=An+extensible+equality+checking+algorithm+for+dependent+type+theories+Bauer+Komel) (Bauer and Komel, 2022) introduces a general algorithm combining type-directed extensionality rules with normalization by computation rules, and shows how to classify rules as computational or extensional in a user-definable way. The algorithm is implemented in a proof assistant prototype that supports custom dependent type theories. 

Without a robust equality/normalization algorithm, dependent types, especially those involving dependent functions or indexed types,become unwieldy. Many trivial-looking equalities (e.g., rewriting with definitional reduction, simplification) would need to be proven manually. A good algorithm reduces overhead and makes proofs manageable.

### Elaboration

In proof assistants or dependently typed languages, users write code in a friendly high-level syntax (with type annotations optional, implicit arguments, etc.). The elaboration phase translates that syntax into the core type theory: resolves implicit arguments, performs type inference/checking, adds coercions, resolves overloading, etc.

Elaboration is an overloaded term in Lean. It can refer both to the overall process of translating high-level syntax to core expressions and to the specific process of taking a partially-specified expression and inferring what is left implicit (Lean Community, n.d.). When users enter expressions like `λ x y z, f (x + y) z`, they leave information implicit: types must be inferred from context, overloaded notation must be resolved, and implicit arguments need to be filled in.

The elaboration process involves several distinct phases. During parsing, Lean matches strings of code to declared syntax rules to produce `Syntax` objects, after which macros transform `Syntax` into new `Syntax` recursively until no more macros apply (Lean Community, n.d.). Finally, the system finds an elaborator matched to the appropriate syntax rule that returns an `Expr` object, completing the elaboration step before the expression is converted to executable code during evaluation.

Without a powerful elaboration engine, users would face the burden of writing explicit dependent types everywhere. Good elaboration makes dependent typing practical by hiding complexity while retaining formal guarantees. As the Lean developers emphasize, the combination of a powerful elaboration engine, a small trusted kernel, and support for mixed declarative and tactic proof styles makes Lean a mature system for real-world development.


### Combined algorithmic stack: Decidability + Trust

The integration of bidirectional typing, equality checking through normalization, elaboration, and a small trusted kernel yields a system where:

- **Type checking and proof checking remain decidable** (modulo normalization and termination constraints), ensuring that verification terminates
- **User code stays readable and ergonomic**, with implicit arguments and convenient notation resolved automatically
- **Proof objects are small and checkable** by a trusted kernel, providing strong correctness guarantees
- **Automation builds naturally on top**, with tactics, decision procedures, and AI-assisted reasoning extending the core system

This algorithmic backbone enables modern dependent type theory-based proof assistants to scale from toy examples to libraries containing hundreds of thousands of formalized theorems. The careful balance between decidability, expressiveness, and usability represents decades of research in type theory, programming languages, and automated reasoning.

## Benchmarks and Competitions

The development of dependent type theory systems, particularly Lean, has been significantly shaped by various benchmarks and competitions that provide standardized evaluation frameworks for automated theorem proving and mathematical reasoning. These benchmarks serve multiple purposes: they enable objective comparison of different systems and approaches, drive progress in the field, and establish concrete goals for researchers working on AI-assisted theorem proving.

### Mathematical Competition Benchmarks

One of the most influential benchmarks in the theorem proving community is **miniF2F** (mini Formal-to-Formal), introduced by Zheng, Han, and Polu in 2021. This cross-system benchmark consists of 488 formal mathematical problem statements drawn from the American Invitational Mathematics Examination (AIME), American Mathematics Competitions (AMC), and the International Mathematical Olympiad (IMO), as well as material from high-school and undergraduate mathematics courses (Zheng et al., 2021). The benchmark targets multiple proof assistants including Lean, Metamath, Isabelle, and HOL Light, making it particularly valuable for comparing systems across different foundations. Problems are divided into validation and test sets of 244 problems each, allowing researchers to tune their systems while maintaining held-out data for final evaluation.

Building on miniF2F, researchers have developed more specialized benchmarks. The LeanGeo benchmark, introduced in 2025, comprises 122 geometry problems including all IMO geometry problems since 2000, providing the first formalized geometric problem benchmark in Lean 4 with human-readable proofs (Team et al., 2025). PutnamBench presents problems from the William Lowell Putnam Mathematical Competition and is notable for supporting Lean 4, Isabelle, and Coq, representing undergraduate-level mathematics of considerable difficulty (Tsoukalas et al., 2024).

For research-level mathematics, ProofNet provides 371 examples of undergraduate-level pure mathematics, each consisting of a formal theorem statement in Lean 3, a natural language statement, and a natural language proof. The problems span real and complex analysis, linear algebra, abstract algebra, and topology, creating a bridge between competition mathematics and university coursework (Azerbayev et al., 2023).

### The IMO Grand Challenge

Perhaps the most ambitious goal in automated mathematical reasoning is the **IMO Grand Challenge**, which aims to build an AI system capable of winning a gold medal at the International Mathematical Olympiad. The formal-to-formal variant of this challenge requires the AI to receive problems in formal Lean representation and produce machine-checkable proofs within specified time constraints (IMO Grand Challenge, n.d.). This challenge has inspired significant research and development efforts.

In 2024, Google DeepMind achieved a major milestone when their AlphaProof and AlphaGeometry 2 systems solved four out of six problems from the IMO 2024, earning 28 out of 42 points and achieving silver-medal-level performance (Google DeepMind, 2024). AlphaProof uses reinforcement learning to train itself to prove mathematical statements in Lean, coupling a pre-trained language model with the AlphaZero algorithm. In 2025, progress continued with an advanced version of Gemini Deep Think achieving gold-medal-level performance by solving five out of six IMO problems and earning 35 points (Google DeepMind, 2025).

The FIMO (Formal IMO) dataset contains 149 IMO-level challenging formal statements in Lean along with corresponding informal statements and proofs, specifically targeting the difficulty level that makes the IMO Grand Challenge so formidable (Liu et al., 2023).

### Classical Automated Theorem Proving Competitions

While much recent attention has focused on interactive theorem provers like Lean, the field has a longer tradition of competitions for fully automated systems. The CADE ATP System Competition (CASC) is the annual evaluation of fully automatic, classical logic automated theorem proving systems, held at each Conference on Automated Deduction (CADE) and International Joint Conference on Automated Reasoning (IJCAR) (Sutcliffe, 2016). First held in 1996 at Rutgers University, CASC evaluates systems for first-order and higher-order classical logic, providing standardized problem sets and time constraints for objective comparison.

CASC differs fundamentally from benchmarks focused on interactive theorem provers: it targets systems that operate without human guidance, using resolution, superposition, and other automated reasoning techniques. The competition has driven development of systems like E, Vampire, and SETHEO, which excel at different problem classes within first-order logic.

### Recent Developments and AI Integration

The landscape of benchmarks continues to evolve with advances in large language models and AI-assisted proving. Recent work has introduced ProverBench, a collection of 325 formalized problems including problems from the 2024-2025 American Invitational Mathematics Examination (DeepSeek, 2025). The FATE-M (Formal Algebra Theorem Evaluation-Medium) benchmark focuses on graduate-level abstract algebra, testing systems on advanced algebraic structures such as groups, rings, and fields.

These benchmarks have revealed both progress and remaining challenges. State-of-the-art systems achieve success rates ranging from approximately 24% on ProofNet to 57% on specialized benchmarks like FATE-M, indicating substantial room for improvement (Wang et al., 2025). The gap between performance on curated benchmarks and research-level mathematics remains significant, highlighting the continued need for advances in automated reasoning, proof search strategies, and integration of formal and informal mathematical knowledge.

## Applications in Industry

In recent years, formally grounded methods for specifying and verifying software and hardware systems have undergone significant uptake. The combination of dependable "symbolic" reasoning, (i.e. logic, type-theory, theorem-proving, etc...) with the explosion of AI-driven development like machine learning, generative models, is opening up new directions for improvements. Here are briefs summaries of recent influential applications. 

### Historical and Influencial Application

- Tokeneer ID Station (NSA smart-card project) is one of the early industrial successes of the "Correctness by Construction" methodology. The case is described by Janet Barnes in [“Experiences in the Industrial use of Formal Methods”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Experiences+in+the+Industrial+use+of+Formal+Methods&btnG=). This article reports on industrial deployment of formal methods under the “Correctness by Construction (CbyC)” approach at Altran Praxis, including the case of the Tokeneer ID Station project for the US NSA. The work describes how formal specification in Z, refinement to code in SPARK with proof of absence of run-time errors, and proof of system-level properties were applied. The project found only five errors post-release and is cited as a rare “success story” of formal methods in industry. The article also candidly discusses challenges: training, tool usability, industrial adoption, and scaling.

- [“Symbolic QED Pre-silicon Verification for Automotive Microcontroller Cores: Industrial Case Study”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CSymbolic+QED+Pre-silicon+Verification+for+Automotive+Microcontroller+Cores%3A+Industrial+Case+Study.%E2%80%9D&btnG=) presents an industrial case study applying the “Symbolic Quick Error Detection (Symbolic QED)” technique in the pre-silicon verification of automotive microcontroller cores (~1,800 flip-flops, ~70,000 logic gates). Symbolic QED detected all logic bugs found by previous industrial verification flows, plus additional ones. It significantly reduced verification effort (e.g., an 8× reduction for a new design, and up to ~60× for subsequent designs). Runtime of bug detection improved dramatically (20 seconds or less) with short counterexamples (≤10 instructions).

- [“Formal methods in dependable systems engineering: a survey of professionals from Europe and North America"](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Formal+methods+in+dependable+systems+engineering%3A+a+survey+of+professionals+from+Europe+and+North+America&btnG=) presents survey results from mission-critical software engineering practitioners, investigating how they use formal methods, their intentions to use them, and perceived challenges. Intrinsic motivation drives use more than regulation. Experienced practitioners plan to use more extensively. Major obstacles remain such as: scalability, skills, education, process compatibility, tool reputation. The survey highlights that despite promising case studies, broad industrial adoption remains constrained.

- [“Industrial-Strength Verification of Solid State Interlocking Programs”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CIndustrial-Strength+Verification+of+Solid+State+Interlocking+Programs.%E2%80%9D&btnG=) describes a tool used on 26 real-world interlockings and used to augment existing testing/inspection processes. It describes an end-to-end workflow that consumes engineering artefacts as produced by signalling designers, automatically encodes safety properties, runs automated theorem provers and SMT solvers, then produces diagnostics so the results are actionable.

### Recent & Emerging Directions

- The paper [“Machine learning and logic: a new frontier in artificial intelligence”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CMachine+learning+and+logic%3A+a+new+frontier+in+artificial+intelligence.%E2%80%9D&btnG=) shows how ML/AI and formal methods (logic, automated reasoning) are increasingly tightly coupled. Both foundational pillars have largely developed independently, but novel and grand challenges demand their integration. The authors identify three key paradigms:
    1. Using learning methods for proof-rule selection, solver heuristic and initialization.
    2. Combining inductive learning and deductive reasoning for programming-by-example, synthesis, and verification.
    3. Using solver feedback as corrective layers for ML models to improve accuracy, generalizability and trustworthiness.
They posit that this convergent direction will have major impact on future AI and verification.

- [“Application of AI to formal methods — an analysis of current trends”](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%E2%80%9CApplication+of+AI+to+formal+methods+%E2%80%94+an+analysis+of+current+trends.%E2%80%9D&btnG=) is a systematic mapping of how AI techniques (including generative models) are being applied to formal methods (and vice versa). It charts emerging directions such as automated invariant generation via ML, proof-assistant tactic synthesis using neural networks, and formal verification of AI/ML system themselves. The analysis highlights both promise of increased automation and reduced annotation and caution. 

- Special issue [“Formal Methods for Industrial Critical Systems”](https://scholar.google.com/scholar?q=%E2%80%9CFormal+Methods+for+Industrial+Critical+Systems%E2%80%9D&hl=en&as_sdt=0%2C5&as_ylo=2024&as_yhi=) compiles recent tools and experience reports from industry/critical systems. The issue contributions cover a range of domains and emphasize the needs of improving formal tools and publishing empirical experience showing how formal methods integrate with industrial processes. 

- [VeriBench: End-to-End Formal Verification Benchmark for AI Code Generation in Lean](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&as_ylo=2024&q=%22VeriBench%3A+End-to-End+formal+verification+benchmark+for+AI+code+generation+in+Lean+4%22&btnG=) presents a benchmark suite called VeriBench, designed to evaluate how well large language models (LLMs) can generate complete formal verification artifacts in Lean 4. The experiments show that current frontier LLMs compile and pass only a small fraction of these tasks out of the box. It explicitly highlights how Lean 4’s dependent-type system enables encoding deep invariants. The authors argue
that such benchmarks are essential to meaningful progress in automated code verification & provably correct code generation, especially as generative AI becomes more widely used in software engineering.

## Case Study

Let's formalise and verify a transformation pipline for 3-D points in world space. Let's look at a small example where we perform a rotation in place, follow by a translation (moving the point to a different coordinate). This case study will show how dependent types and theorem proving is utilized in computer graphics, like graphical engines utilized in games, movies, animation, etc...

The following case study demonstrates how Lean uses dependent type system to ensures mathematical and computational correctness. By encoding vector dimensions in types and proving geometric invariants such as norm preservation, we move from abstract theory to executable verification. This approach mirrors how formal methods are being integratated into the wider industry.

To initialize a Lean project, run the following line:
````bash
lake new my_project math
````
Feel free to replace ``my_project`` with any name. 

**3D Point Transformation Pipeline**
This module demonstrates how dependent types and theorem proving can be used
to verify geometric transformations in computer graphics applications.

We implement:
- 3D vectors with dimension encoded in the type system
- Rotation matrices (orthogonal transformations)
- Translation operations
- A transformation pipeline that composes rotation and translation
- Formal proofs of geometric invariants (norm preservation)

We declared the structures for 3D points, the rotation matrix and the translation matrix. Each elements of each structures is of type Real numbers.

````lean
namespace Graphics3D

/-- A 3D point represented as three real coordinates -/
structure Point3D where
  x : ℝ
  y : ℝ
  z : ℝ

/-- A 3x3 rotation matrix -/
structure RotationMatrix where
  m00 : ℝ
  m01 : ℝ
  m02 : ℝ
  m10 : ℝ
  m11 : ℝ
  m12 : ℝ
  m20 : ℝ
  m21 : ℝ
  m22 : ℝ

/-- A translation vector -/
structure Translation where
  dx : ℝ
  dy : ℝ
  dz : ℝ
````

We defined below some common formulas and transformation matrixes that will be used to verify our theorems later.

````lean
/-- Apply a rotation matrix to a 3D point -/
def rotate (R : RotationMatrix) (p : Point3D) : Point3D :=
  { x := R.m00 * p.x + R.m01 * p.y + R.m02 * p.z,
    y := R.m10 * p.x + R.m11 * p.y + R.m12 * p.z,
    z := R.m20 * p.x + R.m21 * p.y + R.m22 * p.z }

/-- Apply a translation to a 3D point -/
def translate (t : Translation) (p : Point3D) : Point3D :=
  { x := p.x + t.dx,
    y := p.y + t.dy,
    z := p.z + t.dz }

/-- Compute the squared norm (length squared) of a 3D point -/
def normSquared (p : Point3D) : ℝ :=
  p.x * p.x + p.y * p.y + p.z * p.z

/-- Compute the norm (length) of a 3D point -/
noncomputable def norm (p : Point3D) : ℝ :=
  Real.sqrt (normSquared p)

/-- A rotation matrix is orthogonal if its columns form an orthonormal basis.
    This is a key property that ensures rotations preserve distances. -/
def isOrthogonal (R : RotationMatrix) : Prop :=
  -- Column 1 · Column 1 = 1
  R.m00 * R.m00 + R.m10 * R.m10 + R.m20 * R.m20 = 1 ∧
  -- Column 2 · Column 2 = 1
  R.m01 * R.m01 + R.m11 * R.m11 + R.m21 * R.m21 = 1 ∧
  -- Column 3 · Column 3 = 1
  R.m02 * R.m02 + R.m12 * R.m12 + R.m22 * R.m22 = 1 ∧
  -- Column 1 · Column 2 = 0
  R.m00 * R.m01 + R.m10 * R.m11 + R.m20 * R.m21 = 0 ∧
  -- Column 1 · Column 3 = 0
  R.m00 * R.m02 + R.m10 * R.m12 + R.m20 * R.m22 = 0 ∧
  -- Column 2 · Column 3 = 0
  R.m01 * R.m02 + R.m11 * R.m12 + R.m21 * R.m22 = 0

/-- The identity rotation (no rotation) -/
def identityRotation : RotationMatrix :=
  { m00 := 1, m01 := 0, m02 := 0,
    m10 := 0, m11 := 1, m12 := 0,
    m20 := 0, m21 := 0, m22 := 1 }

/-- Rotation around the Z-axis by angle θ (in the XY plane) -/
noncomputable def rotationZ (θ : ℝ) : RotationMatrix :=
  { m00 := Real.cos θ, m01 := -Real.sin θ, m02 := 0,
    m10 := Real.sin θ, m11 :=  Real.cos θ, m12 := 0,
    m20 := 0,           m21 :=  0,          m22 := 1 }

/-- A transformation pipeline that first rotates, then translates -/
def transformPipeline (R : RotationMatrix) (t : Translation) (p : Point3D) : Point3D :=
  translate t (rotate R p)
````
We now define our theorems to verify the integrity of our 3D points after applying Rotation and Transformation.

```lean
/--
THEOREM: Orthogonal transformations preserve the squared norm.
This is a fundamental property in computer graphics: rotations don't change
the distance of a point from the origin.
-/

theorem rotation_preserves_norm_squared (R : RotationMatrix) (p : Point3D)
    (h : isOrthogonal R) :
    normSquared (rotate R p) = normSquared p := by
  unfold normSquared rotate isOrthogonal at *
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  -- The proof: expand the LHS and use orthogonality conditions
  calc (R.m00 * p.x + R.m01 * p.y + R.m02 * p.z) * (R.m00 * p.x + R.m01 * p.y + R.m02 * p.z) +
       (R.m10 * p.x + R.m11 * p.y + R.m12 * p.z) * (R.m10 * p.x + R.m11 * p.y + R.m12 * p.z) +
       (R.m20 * p.x + R.m21 * p.y + R.m22 * p.z) * (R.m20 * p.x + R.m21 * p.y + R.m22 * p.z)
    _ = p.x * p.x * (R.m00 * R.m00 + R.m10 * R.m10 + R.m20 * R.m20) +
        p.y * p.y * (R.m01 * R.m01 + R.m11 * R.m11 + R.m21 * R.m21) +
        p.z * p.z * (R.m02 * R.m02 + R.m12 * R.m12 + R.m22 * R.m22) +
        2 * p.x * p.y * (R.m00 * R.m01 + R.m10 * R.m11 + R.m20 * R.m21) +
        2 * p.x * p.z * (R.m00 * R.m02 + R.m10 * R.m12 + R.m20 * R.m22) +
        2 * p.y * p.z * (R.m01 * R.m02 + R.m11 * R.m12 + R.m21 * R.m22) := by ring
    _ = p.x * p.x * 1 + p.y * p.y * 1 + p.z * p.z * 1 +
        2 * p.x * p.y * 0 + 2 * p.x * p.z * 0 + 2 * p.y * p.z * 0 := by
          rw [h1, h2, h3, h4, h5, h6]
    _ = p.x * p.x + p.y * p.y + p.z * p.z := by ring

/--
THEOREM: Translation changes position but preserves relative distances.
The norm changes by a predictable amount based on the translation vector.
-/
theorem translation_norm_relation (t : Translation) (p : Point3D) :
    normSquared (translate t p) =
    normSquared p + 2 * (t.dx * p.x + t.dy * p.y + t.dz * p.z)
    + normSquared ⟨t.dx, t.dy, t.dz⟩ := by
  unfold normSquared translate
  ring

/--
THEOREM: The identity rotation leaves points unchanged.
-/
theorem identity_rotation_is_identity (p : Point3D) :
    rotate identityRotation p = p := by
  unfold rotate identityRotation
  simp

/--
THEOREM: The identity rotation is orthogonal.
-/
theorem identity_is_orthogonal : isOrthogonal identityRotation := by
  unfold isOrthogonal identityRotation
  simp

/--
THEOREM: Rotation around the Z-axis is orthogonal for any angle θ.
This uses the fundamental trigonometric identity: cos²θ + sin²θ = 1
-/
theorem rotationZ_is_orthogonal (θ : ℝ) : isOrthogonal (rotationZ θ) := by
  unfold isOrthogonal rotationZ
  constructor
  · simp; ring_nf; exact Real.cos_sq_add_sin_sq θ
  constructor
  · simp; ring_nf; rw [Real.sin_sq, Real.cos_sq]; ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring
```

**Properties That Can Be Verified**

The type system and proof system together ensure:
1. **Type Safety**: We can't accidentally mix 2D and 3D operations
2. **Geometric Correctness**: Rotations preserve norms (proved formally)
3. **Composition Correctness**: Transformations compose as expected
4. **No Silent Failures**: Invalid operations are caught at compile time

This approach is increasingly important in:
- Game engines (e.g., Unreal Engine, Unity)
- CAD/CAM software
- Robotics and autonomous vehicles
- Scientific visualization
- Virtual/Augmented reality systems

By formally verifying these properties, we can guarantee correctness
before any graphics are rendered or simulations are run.

**Example Usage**

Below we demonstrate the transformation pipeline with concrete values.

````lean
/-- Example: A point at (1, 0, 0) -/
def examplePoint : Point3D := ⟨1, 0, 0⟩

/-- Example: Rotate 90 degrees around Z-axis -/
noncomputable def rotate90Z : RotationMatrix := rotationZ (Real.pi / 2)

/-- Example: Translate by (5, 3, 2) -/
def exampleTranslation : Translation := ⟨5, 3, 2⟩

/-- Apply the transformation pipeline -/
noncomputable def transformedPoint : Point3D :=
  transformPipeline rotate90Z exampleTranslation examplePoint
````

**Why This Matters:**

This example shows how dependent types ensure:

- **Compile-time correctness**: Can't mix incompatible dimensions
- **Mathematical guarantees**: Formal proofs of geometric properties
- **Industry relevance**: Same techniques used in game engines, robotics, CAD software

The code is ready to use in Lean 4 with Mathlib imported. Feel free to extend it with additional rotations (X, Y axes), compose multiple rotations, or add more complex transformations! The entire code file is available [here](../src/lean/CaseStudy.lean)!

## History

Type theory and the idea of types as a foundation for mathematics and computation have a long pedigree that connects philosophical logic, lambda calculus, and modern proof assistants.

The story begins with early efforts to avoid paradoxes in naive set theory and logic (Russell, Frege), which motivated ramified and then simple type theories in the first half of the 20th century. Alonzo Church’s formulation of the simple theory of types and the simply-typed lambda calculus provided the computational backbone that later researchers built on. ([Wikipedia](https://en.wikipedia.org/wiki/History_of_type_theory))

A decisive shift toward dependent types occurred with Per Martin-Löf’s intuitionistic type theory (1970s–1980s). Martin-Löf introduced dependent function ($\Pi$) and dependent pair ($\Sigma$) types, giving a constructive foundation in which types can quantify over values. This made it possible to represent propositions as types and proofs as programs in a very expressive way. The Curry–Howard correspondence, the observation that proofs correspond to programs and propositions to types, fused logic and computation and underpins modern dependently-typed systems. ([See here](https://plato.stanford.edu/entries/type-theory)) 

In the 1980s and 1990s the field consolidated around a handful of influential calculi and systems. The Calculus of Constructions (Coquand & Huet) and the later Calculus of Inductive Constructions became the basis for the Coq proof assistant; Agda and other systems explored dependently typed programming more directly; and the so-called lambda-cube classified a spectrum of type systems. Over the last two decades these theoretical advances have been implemented in robust systems (Coq, Agda, Lean, Idris) and large collaborative libraries (e.g., Lean’s mathlib), enabling both deep mathematical formalization and practical verification projects. ([See here](https://plato.stanford.edu/entries/type-theory))

## Formal Methods and AI

The integration of artificial intelligence with Lean and dependent type theory represents one of the most promising frontiers in automated reasoning. This convergence combines the rigor and certainty of formal verification with the pattern-matching and generalization capabilities of modern machine learning systems, creating powerful new approaches to mathematical theorem proving and software verification.

### Infrastructure for AI-Driven Theorem Proving

A critical challenge in applying machine learning to theorem proving is the gap between the Python-based machine learning ecosystem and the specialized environments of proof assistants. LeanDojo addresses this by providing foundational infrastructure that bridges Python-based machine learning with the Lean prover, extracting rich datasets from Lean repositories including abstract syntax trees, file dependencies, proof states, tactics, and fine-grained premise annotations (Yang et al., 2023). The tool transforms Lean into a gym-like environment where AI agents can programmatically observe proof states, submit tactics, and receive feedback, which is indispensable for evaluation, deployment, and reinforcement learning.

The LeanDojo project also introduced substantial benchmarks for training machine learning models. The original LeanDojo Benchmark contains 98,734 theorems and proofs with 217,776 tactics extracted from Mathlib, while the Lean 4 version includes 122,517 theorems with 259,580 tactics (Yang et al., 2023). A key innovation is the challenging data split design, which requires models to generalize to theorems relying on novel premises never used in training, rather than simply memorizing similar proofs (Yang et al., 2023).

### Retrieval-Augmented Language Models

One of the key bottlenecks in automated theorem proving is premise selection—identifying relevant existing lemmas and definitions from vast mathematical libraries to apply in proofs. ReProver (Retrieval-Augmented Prover) represents a significant advance, combining language models with retrieval mechanisms for selecting premises from large mathematics libraries, requiring only one GPU week of training (Yang et al., 2023). The retrieval component leverages LeanDojo's program analysis to identify accessible premises and hard negative examples, making retrieval substantially more effective than baseline approaches.

More recently, researchers have developed methods for generating massive training datasets. LeanNavigator generates new theorems by exploring state transition graphs of existing Lean theorems, producing 4.7 million theorems totaling 1 billion tokens from Mathlib4, surpassing previous datasets by more than an order of magnitude (Li et al., 2025). Models trained on this expanded dataset outperform previous state-of-the-art systems like ReProver in theorem-proving benchmarks.

### Integration with Large Language Models

The emergence of powerful large language models has opened new possibilities for human-AI collaboration in formal mathematics. Lean Copilot allows large language models to be used natively in Lean for proof automation, suggesting tactics and premises and searching for proofs using built-in models from LeanDojo or custom models running locally or remotely (Song et al., 2024). This integration enables more natural interaction patterns where AI systems can interleave informal mathematical reasoning with formal proof steps.

Commercial and research applications are proliferating. In 2022, OpenAI and Meta AI independently created AI models to generate proofs of high-school-level olympiad problems in Lean, demonstrating that large language models can interface effectively with formal proof environments ([Wikipedia](https://scholar.google.com/scholar?q=Lean+proof+assistant), 2024). More recently, systems like AlphaProof from Google DeepMind have achieved silver-medal performance at the International Mathematical Olympiad using reinforcement learning trained on Lean (Google DeepMind, 2024).

### Challenges and Future Directions

Despite significant progress, substantial challenges remain. Formalizing real-world knowledge or large codebases in Lean remains labor-intensive, and Lean requires precise problem specification, which isn't straightforward for messy real-world scenarios. Auto-formalization efforts—where AI converts informal specifications into Lean code—are underway but not yet seamless.

The trajectory, however, is promising. As one analysis notes, every improvement in AI reasoning capabilities—better chain-of-thought reasoning, specialized training on formal tasks—directly boosts Lean integration performance (VentureBeat AI, 2024). The convergence of human expertise, community knowledge, and AI assistance hints at a collaborative future for formal methods where mathematical superintelligence becomes achievable through the synergy of human insight and machine verification.

## Current Development
Lean and its ecosystem continue to evolve rapidly, driven by both community contributions and institutional support. The development landscape encompasses advances in the core language, expansion of mathematical libraries, organizational infrastructure, and high-profile mathematical formalization projects.

### Institutional Support and the Lean FRO

In July 2023, the Lean Focused Research Organization (FRO) was established as a non-profit under Convergent Research, pursuing a focused 5-year mission to improve Lean's critical systems through enhanced scalability, usability, documentation, and proof automation (Lean FRO, 2024). The FRO is led by Chief Architect Leonardo de Moura, who created Lean in 2013, alongside Head of Engineering Sebastian Ullrich, and is funded by the Alfred P. Sloan Foundation, Simons Foundation International, Richard Merkin Foundation, and private donors including Alex Gerko.

In its first year of operation, the FRO achieved measurable progress across key metrics: monthly active users increased 49%, the number of packages grew 372%, and the number of courses using Lean increased 89% year-over-year (Lean FRO, 2024). The organization hired eleven team members, established governance structures, and secured sufficient funding to ensure Lean's path toward self-sufficiency. Focus areas included improving compilation speed, enhancing documentation, developing proof automation tools like the omega tactic for integer and natural number reasoning, and launching Reservoir, Lean's package repository.

### Mathlib4 Development

The community-maintained Mathlib library represents one of the most comprehensive formalizations of mathematics in any proof assistant. As of May 2025, Mathlib had formalized over 210,000 theorems and 100,000 definitions in Lean, spanning areas from undergraduate mathematics through research-level topics ([Wikipedia](https://scholar.google.com/scholar?q=Lean+proof+assistant), 2025).

The transition from Lean 3 to Lean 4 required porting the entire Mathlib library—a massive community effort. July 2023 marked the completion of the project to port Lean's mathematics library from Lean 3 to Lean 4, enabling the community to focus on expansion rather than migration (Buzzard, 2024). Lean 4's redesigned typeclass inference system, which incorporated insights from Mathlib development, eliminated the need for many typeclass linters that were necessary in Lean 3 (Baanen et al., 2022).

Managing a library of this scale presents unique challenges. The community employs sophisticated tooling including automated continuous integration, code quality linters, a deprecation system for managing breaking changes, and the bors merge bot to ensure the main branch always passes all tests (Baanen et al., 2022). Development is coordinated through GitHub and the Lean Zulip chat, where contributors at all expertise levels participate in design discussions and receive guidance.

### High-Profile Formalization Projects

Several ambitious mathematical formalization projects have demonstrated Lean's capabilities and attracted attention from prominent mathematicians. In 2023, Fields Medalist Terence Tao led a collaborative project to formalize the proof of the Polynomial Freiman-Ruzsa (PFR) conjecture in Lean 4, completed within weeks of the original paper's release (Tao, 2023). The project utilized Patrick Massot's Blueprint tool, which links human-readable proof outlines to formal Lean code, facilitating large-scale collaboration.

Tao has continued his engagement with Lean formalization. In May 2025, Tao released a Lean companion to his textbook "Analysis I," formalizing foundational real analysis topics including constructions of number systems, sequences, series, continuity, differentiation, and integration (Tao, 2025). The formalization serves dual purposes: as an annotated companion to the textbook and as an introduction to relevant portions of Mathlib, gradually transitioning from textbook definitions to Mathlib conventions.

Other major ongoing projects include the Fermat's Last Theorem formalization project, established in December 2023, which aims to formalize one of mathematics' most complex proofs (Lean FRO, 2024). In 2021, researchers used Lean to verify Peter Scholze's proof in condensed mathematics, garnering attention for formalizing cutting-edge mathematical research ([Wikipedia](https://scholar.google.com/scholar?q=Lean+proof+assistant), 2024).

### Commercial and Research Ecosystem

The Lean ecosystem has expanded beyond academia into commercial applications. In June 2024, Harmonic launched as the first startup based on Lean, covered in The New York Times, focusing on reducing AI hallucinations through formal verification (Lean FRO, 2024). Other recent developments include Velvet, a verifier for imperative programs released in October 2025, and Axiom, which aims to build quantitative superintelligence using formal methods.

The Lean VS Code development environment surpassed 100,000 installations in September 2025, indicating growing adoption (Lean FRO, 2024). Academic partnerships continue to deepen, with institutions like Carnegie Mellon University's Hoskinson Center and L3 Lab at the University of Washington conducting research at the intersection of Lean and AI.

### Recognition and Future Outlook

In 2025, the ACM SIGPLAN Programming Languages Software Award was awarded to Gabriel Ebner, Soonho Kong, Leonardo de Moura, and Sebastian Ullrich for Lean, recognizing its significant impact on mathematics, hardware and software verification, and AI ([Wikipedia](https://scholar.google.com/scholar?q=Lean+proof+assistant), 2025). This recognition reflects Lean's evolution from an academic research project into a platform with broad impact across multiple domains.

Looking forward, the Lean FRO's roadmap emphasizes continued investment in scalability, improved tooling for diverse user communities from mathematicians to verification engineers, and deeper integration with AI-assisted reasoning systems. The community's ambitious formalization projects, combined with growing institutional support and commercial interest, position Lean as a central platform for the formal verification revolution in both mathematics and computer science.

## Resources

- [Lean4 Installation](https://lean-lang.org/install/)

- [Lean Game Logic](https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic)

- Barnes (2011) [Experiences in the Industrial use of Formal Methods](https://scholar.google.com/scholar?q=Experiences+in+the+Industrial+use+of+Formal+Methods+Barnes), ECEASST 46

- Ganesh, Seshia, and Jha (2022) [Machine learning and logic: a new frontier in artificial intelligence](https://scholar.google.com/scholar?q=Machine+learning+and+logic+a+new+frontier+in+artificial+intelligence+Ganesh+Seshia+Jha), Formal Methods Systems Design 60

- Gleirscher and Marmsoler (2020) [Formal methods in dependable systems engineering: a survey of professionals from Europe and North America](https://scholar.google.com/scholar?q=Formal+methods+in+dependable+systems+engineering+a+survey+of+professionals+Gleirscher+Marmsoler), Empir Software Eng 25

- Groote and Huisman (2024) [Formal Methods for Industrial Critical Systems](https://scholar.google.com/scholar?q=%E2%80%9CFormal+Methods+for+Industrial+Critical+Systems%E2%80%9D&hl=en&as_sdt=0%2C5&as_ylo=2024&as_yhi=), Int J Softw Tools Technol Transfer 26

- Iliasov et al. (2021) [Industrial-Strength Verification of Solid State Interlocking Programs](https://scholar.google.com/scholar?q=Industrial-Strength+Verification+of+Solid+State+Interlocking+Programs+Iliasov), arXiv

- Miranda et al. (2025) [VeriBench: End-to-End formal verification benchmark for AI code generation in Lean 4](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&as_ylo=2024&q=%22VeriBench%3A+End-to-End+formal+verification+benchmark+for+AI+code+generation+in+Lean+4%22&btnG=), Proceedings of ICML 2025

- Singh et al. (2019) [Symbolic QED Pre-silicon Verification for Automotive Microcontroller Cores: Industrial Case Study](https://scholar.google.com/scholar?q=Symbolic+QED+Pre-silicon+Verification+for+Automotive+Microcontroller+Cores+Singh), arXiv

- Stanford Encyclopedia of Philosophy (2022) [Type Theory](https://plato.stanford.edu/entries/type-theory), Stanford Encyclopedia of Philosophy

- Stanford Encyclopedia of Philosophy (2024) [Intuitionistic Type Theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/), Stanford Encyclopedia of Philosophy

- Stock, Dunkelau, and Mashkoor (2025) [Application of AI to formal methods — an analysis of current trends](https://scholar.google.com/scholar?q=Application+of+AI+to+formal+methods+an+analysis+of+current+trends+Stock+Dunkelau+Mashkoor), Empir Software Eng

- Wadler (2015) [Propositions as Types](https://scholar.google.com/scholar?q=Propositions+as+Types+Wadler), Communications of the ACM 58(12)

- Bauer and Komel (2020) [Equality checking for general type theories in Andromeda 2](https://scholar.google.com/scholar?q=Equality+checking+for+general+type+theories+in+Andromeda+2+Bauer+Komel), International Conference on Interactive Theorem Proving

- Bauer and Komel (2022) [An extensible equality checking algorithm for dependent type theories](https://scholar.google.com/scholar?q=An+extensible+equality+checking+algorithm+for+dependent+type+theories+Bauer+Komel), Logical Methods in Computer Science

- de Moura et al. (2021) [The Lean 4 theorem prover and programming language](https://scholar.google.com/scholar?q=The+Lean+4+theorem+prover+and+programming+language+de+Moura), International Conference on Automated Deduction

- Dunfield and Krishnaswami (2021) [Bidirectional typing](https://scholar.google.com/scholar?q=Bidirectional+typing+Dunfield+Krishnaswami), ACM Computing Surveys

- Ebner et al. (2017) [A metaprogramming framework for formal verification](https://scholar.google.com/scholar?q=A+metaprogramming+framework+for+formal+verification+Ebner), Proceedings of the ACM on Programming Languages

- Felicissimo (2024) [Artifact report: Generic bidirectional typing for dependent type theories](https://scholar.google.com/scholar?q=Generic+bidirectional+typing+for+dependent+type+theories+artifact+Felicissimo), ESOP 2024

- Felicissimo et al. (2024) [Generic bidirectional typing for dependent type theories](https://scholar.google.com/scholar?q=Generic+bidirectional+typing+for+dependent+type+theories+Felicissimo), ESOP 2024

- Ko and Gibbons (2024) [A formal treatment of bidirectional typing](https://scholar.google.com/scholar?q=A+formal+treatment+of+bidirectional+typing+Ko+Gibbons), ESOP 2024

- Lean Community (n.d.) [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/), Online documentation

- Azerbayev et al. (2023) [ProofNet: Autoformalizing and formally proving undergraduate-level mathematics](https://scholar.google.com/scholar?q=ProofNet+Autoformalizing+and+formally+proving+undergraduate-level+mathematics+Azerbayev), arXiv

- DeepSeek (2025) [DeepSeek-Prover-V2: Retrieval augmented Lean prover for mathematical reasoning](https://scholar.google.com/scholar?q=DeepSeek-Prover-V2+Retrieval+augmented+Lean+prover+DeepSeek), arXiv

- Google DeepMind (2024) [AI achieves silver-medal standard solving International Mathematical Olympiad problems](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/), Blog post

- Google DeepMind (2025) [Advanced version of Gemini with Deep Think officially achieves gold-medal standard at the International Mathematical Olympiad](https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/), Blog post

- IMO Grand Challenge (n.d.) [IMO Grand Challenge for Artificial Intelligence](https://imo-grand-challenge.github.io/), Project website

- Liu et al. (2023) [FIMO: A challenge formal dataset for automated theorem proving](https://scholar.google.com/scholar?q=FIMO+A+challenge+formal+dataset+for+automated+theorem+proving+Liu), arXiv

- Sutcliffe (2016) [The CADE ATP system competition—CASC](https://scholar.google.com/scholar?q=The+CADE+ATP+system+competition+CASC+Sutcliffe), AI Magazine

- Team et al. (2025) [LeanGeo: Formalizing competitional geometry problems in Lean](https://scholar.google.com/scholar?q=LeanGeo+Formalizing+competitional+geometry+problems+in+Lean+Team), arXiv

- Tsoukalas et al. (2024) [PutnamBench: Evaluating neural theorem-provers](https://scholar.google.com/scholar?q=PutnamBench+Evaluating+neural+theorem-provers+Tsoukalas), NeurIPS 2024

- Wang et al. (2025) [REAL-Prover: Retrieval augmented Lean prover for mathematical reasoning](https://scholar.google.com/scholar?q=REAL-Prover+Retrieval+augmented+Lean+prover+Wang), arXiv

- Zheng, Han, and Polu (2021) [MiniF2F: A cross-system benchmark for formal Olympiad-level mathematics](https://scholar.google.com/scholar?q=MiniF2F+A+cross-system+benchmark+for+formal+Olympiad-level+mathematics+Zheng+Han+Polu), ICLR 2022

- Li et al. (2025) [Generating millions of Lean theorems with proofs by exploring state transition graphs](https://scholar.google.com/scholar?q=Generating+millions+of+Lean+theorems+with+proofs+by+exploring+state+transition+graphs+Li), arXiv

- Song, Yang, and Anandkumar (2024) [Lean Copilot: Large language models as copilots for theorem proving in Lean](https://scholar.google.com/scholar?q=Lean+Copilot+Large+language+models+as+copilots+for+theorem+proving+Song+Yang+Anandkumar), arXiv

- VentureBeat AI (2024) [Lean4: How the theorem prover is revolutionizing AI and mathematics](https://beamstart.com/news/lean4-how-the-theorem-prover-17638530282056), Article

- Yang et al. (2023) [LeanDojo: Theorem proving with retrieval-augmented language models](https://scholar.google.com/scholar?q=LeanDojo+Theorem+proving+with+retrieval-augmented+language+models+Yang), NeurIPS 2023

- Baanen et al. (2022) [Growing Mathlib: Maintenance of a large scale mathematical library](https://scholar.google.com/scholar?q=Growing+Mathlib+Maintenance+of+a+large+scale+mathematical+library+Baanen), Intelligent Computer Mathematics

- Buzzard (2024) [Lean in 2024](https://xenaproject.wordpress.com/2024/01/20/lean-in-2024/), Xena Project blog

- Lean FRO (2024) [About the Lean FRO](https://lean-fro.org/about/), Organization website

- Lean FRO (2024) [Lean FRO year 1 in review](https://lean-lang.org/blog/2024-8-13-lean-fro-year-1-in-review/), Blog post

- Tao (2023) [Formalizing the proof of PFR in Lean4 using Blueprint: A short tour](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/), What's New blog

- Tao (2025) [A Lean companion to "Analysis I"](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/), What's New blog

## Future Work
For future work, find more relevant sources, specifically to Lean, for Applications in Industry. Additionally, include more algorithms and properties of Dependent Type Theory. Please extend and explore more in depth any topics that were not thoroughly covered in this chapter. Finally, include additional different case studies for Lean to demonstrate how Lean can be applied to different fields.