# SMT Solving and Z3

## Idea

SMT, satisfiability modulo theories, extends propositional satisfiability (SAT) by adding interpreted functions and predicates from various decidable first-order theories. For example, instead of just Boolean variables, we can have:

- Linear arithmetic: variables like `x`, `y` with constraints `x + y > 10`, `2x - 3y ≤ 5`
- Bit-vectors: variables like `a`, `b` with bitwise operations `a & b = 0xFF`, `a << 2 = b`
- Arrays: array variables `A`, `B` with operations `A[i] = B[j]`, `store(A, i, v)`
- Uninterpreted functions: function symbols `f`, `g` with constraints `f(x) = g(y)`, `f(f(x)) = x`

**Remark:** This looks very similar to constraint programming. So what is the difference? MiniZinc can call Z3 as a backend and SMT-solvers are used in CP competitions. The answer to the question may well be how different communities in computer science research evolved historically. We should add a section that explores this history.

## Basic Theory

First-order logic is not decidable, but it does contain some decidable theories. SMT leverages special solvers for decidable first-order theories. Moreover, under certain conditions different decidable theories can be combined into larger ones. 

### Decidable First-Order Theories

Typically, decidability requires that the formulas have to by quantifier-free (QF) but there are exceptions, most famously the theory of real closed fields.

**Real Closed Fields** (RCF) have a decidable theory due to Tarski's quantifier elimination (1930s) which shows that any first-order formula over reals can be reduced to a quantifier-free formula:
- *Variables*: Real numbers
- *Operations*: `+`, `-`, `*`, `/`, `<`, `≤`, `>`, `≥`, `=`, quantifiers `∀`, `∃`
- *Example*: `∀x∀y. x² + y² = 1 → x > 0 ∨ x < 0` (every point on unit circle is not zero)

**Linear Arithmetic** (QFLRA/QFLIA) can be solved using simplex algorithm or Fourier-Motzkin elimination:
- *Variables*: Rationals (QFLRA) or Integers (QFLIA) 
- *Operations*: `+`, `-`, `<`, `≤`, `>`, `≥`, `=`
- *Example*: `x + 2y ≤ 10 ∧ x > 0`

**Equality with Uninterpreted Functions** (EUF) can be solved with the congruence closure algorithm (1970s):
- *Variables*: Any domain, with function symbols `f`, `g`, etc.
- *Operations*: Function application, equality
- *Example*: `f(x) = g(y) ∧ f(f(x)) = x`

**Arrays** (QF_A) can be reduced to EUF + axioms
- **Variables**: Arrays `A`, `B`, indices `i`, `j`, values `v`
- **Operations**: `select(A, i)`, `store(A, i, v)`
- **Example**: `select(store(A, i, v), j) = select(A, j) ∧ i ≠ j`

**Bit-vectors** (QF_BV) can be reduced to SAT or solved with specialized algorithms:
- *Variables*: Fixed-width integers (e.g., 32-bit)
- *Operations*: Bitwise (`&`, `|`, `^`, `~`), arithmetic (`+`, `*`), shifts (`<<`, `>>`)
- *Example*: `x & y = 0 ∧ x | y = 0xFF`

**Difference Logic** (QF_IDL/QF_RDL) can be solved using shortest path algorithms
- *Variables*: Integers or Reals
- *Operations*: Differences `x - y ≤ c`, equality `x = y`
- *Example*: `x - y ≤ 5 ∧ y - z ≤ 3 ∧ z - x ≤ -10`

### Theory Combination: The Nelson-Oppen Method

See Martin's [Lecture Notes on SMT Solving: Nelson-Oppen](https://www.cs.cmu.edu/~15414/s24/lectures/18-smt-solving.pdf).

## Z3

[Z3 Tutorial](https://microsoft.github.io/z3guide/docs/logic/intro/)

There are different ways to use Z3. We start with the playground and then learn how to call Z3 from Python.

### Z3 Playground 

#### Array bounds

Read the following program written in [SMT-LIB](https://smt-lib.org/language.shtml). For background, I recommend to read Chapter 2 as well as pages 22, 55-56, 76 of the [SMT-LIB Standard](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf).

```
(declare-const i Int)
(declare-const array_size Int)

; Set values
(assert (= array_size 10))
(assert (= i 15))

; Check if bounds can be violated
(assert (not (and (<= 0 i) (< i array_size))))

(check-sat)
(get-model)
```
Paste the code into the [Z3 Playground](https://microsoft.github.io/z3guide/docs/logic/intro/). How do you interpret the result? 

Answer the question by keep changing the code and predicting the results you expect.

#### Guessing a number

Here's a more interesting example where we let Z3 find values for variables:

```
(declare-const x Int)
(declare-const y Int)

(assert (= (+ x y) 15))
(assert (= (- x y) 5))

(check-sat)
(get-model)
```
**Exercise:** Create your own "guessing the number" puzzle.

### More Solvers

**SMT-LIB** is a standardized language used by many SMT solvers, not just Z3. Try the programs above with:

- [CVC4/CVC5](https://cvc4.github.io/app/): Carnegie Mellon University

Other SMT-solvers that accept SMT-LIB are:
- [Yices](https://yices.csl.sri.com/): SRI International  
- [MathSAT](http://mathsat.fbk.eu/): University of Trento
- [Boolector](https://boolector.github.io/): Johannes Kepler University
- [OpenSMT](https://verify.inf.usi.ch/opensmt/): University of Lugano


### Z3 in Python

Interactive Z3 examples are available below via Colab or Binder or download a copy [here](https://github.com/LEAP-at-Chapman/CPSC-510-Logical-Foundations-of-Computing/blob/main/z3/z3-examples.ipynb).

**Try it interactively:** 

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/LEAP-at-Chapman/CPSC-510-Logical-Foundations-of-Computing/blob/main/z3/z3-examples.ipynb) **🚀 Google Colab (Recommended - Fast & Reliable)**

[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/LEAP-at-Chapman/CPSC-510-Logical-Foundations-of-Computing/main?filepath=content%2Frequirements.txt&labpath=../z3%2Fz3-examples.ipynb) **🐳 Binder (Alternative)**

Practical Examples:

i) Prove that array access is always within bounds in a loop:
  ```
  (declare-fun i () Int)
  (declare-fun n () Int)
  (assert (and (>= i 0) (< i n)))   ; loop invariant
  (assert (not (< i n)))            ; try to violate it
  (check-sat)
  ```

  Explanation: Z3 can prove safety properties like “no out-of-bounds access occurs”. This connects to static analysis and model checking.

  ## Applications in the Industry

  **Cloud security & compliance (billions of SMT checks at Amazon Web Services)**
  
  Zelkova, AWS’s policy-analysis engine, encodes IAM/S3 policies into SMT and answers safety queries at cloud scale (e.g., “Can anything make this bucket public?”). Peer-reviewed accounts report   millions to billions of SMT queries daily, and describe how abstractions and portfolio solving (including Z3) make the service production-grade and latency-predictable.

  **Software security at Microsoft (whitebox fuzzing)**

  SAGE pioneered whitebox fuzzing: path-constraint solving with SMT to generate inputs that drive binaries down new paths. Deployed across Windows and other products, SAGE and its successors  
  (SAGAN/JobCenter) found numerous high-impact bugs and established SMT-backed fuzzing as an industrial norm. 

  **Compiler correctness (translation validation for LLVM)**
  
  Alive2 checks that optimizations preserve semantics by asking SMT queries over the pre/post IR. Recent work blends LLMs with Alive2 to flag transformations likely to be unsound, then uses   
  fuzzing to seek counterexamples—an early example of neuro-symbolic validation in a mature compiler toolchain.

  **Smart-contract analysis (blockchains)**

  Tools like Mythril symbolically execute EVM bytecode and discharge path constraints to Z3 to expose reentrancy, arithmetic, and permission bugs before deployment—now routine in audits and CI 
  for DeFi systems.

  **Network correctness (pre-deployment verification)**

  Industrial network verifiers translate control-plane configs (BGP/OSPF/etc.) into logical models and use SMT to validate reachability, isolation, and failure scenarios before rollout—e.g.,
  Minesweeper/Batfish (research-to-product trajectory) and later scalable systems.

  **Safety-critical AI (neural-network verification)**

  The Reluplex line of work and the Marabou framework brought SMT into DNN certification (ACAS Xu case study, bound-tightening, piecewise-linear reasoning). This has shaped standards 
  conversations for autonomy and perception stacks.


  ## Generative AI and Formal Methods: What's Changing

  **1. LLMs assisting proof and spec**
    LeanDojo/ReProver shows that retrieval-augmented LLMs can select premises and generate Lean proofs; the suite provides datasets, tooling, and reproducible baselines, catalyzing rapid 
    progress in ML-for-theorem-proving.
    A 2025 survey reviews how LLMs help author formal specifications from natural-language requirements (Dafny/C/Java), with promising accuracy on assertion synthesis and “assertion completion.”
    

  **2. Neuro-symbolic invariant synthesis for verification**
    Fresh results show LLMs can propose loop invariants that an SMT-based checker validates/refines (e.g., ASE’24 neuro-symbolic bounded model checking; 2025 benchmark studies). The emerging 
    recipe: LLM proposes → SMT/solver checks → counterexample-guided repair.

  **3. Hybrid validation pipelines in compilers and systems**
    For LLVM, LLMs triage “hard” optimizations while Alive2 (SMT) proves the rest, using fuzzing to chase suspected unsound cases—concrete neuro-symbolic workflows shipping into compiler 
    validation. Expect similar “LLM-first, SMT-confirm” loops in optimizers, static analyzers, and decompilers.

  **4. Formal analysis of AI systems themselves**
    Neural-network verification continues to integrate SMT with domain-specific relaxations and bound-propagation; Marabou 2.0 documents architecture and roles for solver-in-the-loop bound 
    tightening. Coupled with LLM systems, this points to spec-driven safety cases for perception and policy components.

  **5. Research directions to watch**
    - Auto-formalization: LLMs converting NL requirements/tests into templates that SMT tools check (assertion mining and refinement).
    - Proof-search copilots: Retrieval + tool APIs (Lean/Isabelle/Coq) to keep LLM steps sound via solver or kernel checks.
    - Verifier-in-the-loop tooling: LLM planning; SMT establishes truth; counterexamples feed self-repair—already prototyped in compilers and invariant synthesis.
## References

- [Reuben Martins](https://sat-group.github.io/ruben/) (part of a course on [Bug Catching: Bug Catching: Automated Program Verification](https://www.cs.cmu.edu/~15414/s22/s21/lectures/) )
  - [Lecture Notes on SMT Solving](https://www.cs.cmu.edu/~15414/s22/s21/lectures/16-smt.pdf)
  - [Lecture Notes on SMT Theories](https://www.cs.cmu.edu/~15414/s21/lectures/17-smt-theories.pdf)
  - [Lecture Notes on SMT Encodings](https://www.cs.cmu.edu/~15414/s21/lectures/18-smt-encodings.pdf)
  - [Lecture Notes on DPLL(T) & SMT Encodings](https://www.cs.cmu.edu/~15414/s24/lectures/19-smt-encodings.pdf)
  - [Lecture Notes on SMT Solving: Nelson-Oppen](https://www.cs.cmu.edu/~15414/s24/lectures/18-smt-solving.pdf)
- Howe, J. M., & King, A. (2012). [A pearl on SAT and SMT solving in Prolog](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=A+Pearl+on+SAT+and+SMT+Solving+in+Prolog&btnG=). Theoretical Computer Science, 435, 43-55. [pdf](https://www.staff.city.ac.uk/~jacob/solver/tcs.pdf) - - - I only read the intro and do not claim that I understand that paper. It is of interest to because it combines ideas from SAT, Prolog and SMT.
