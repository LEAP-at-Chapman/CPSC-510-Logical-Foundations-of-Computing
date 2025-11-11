# Dependent Type Theory with Lean

*Author: Khoa Nguyen*

## Introduction

This chapter presents dependent type theory with Lean, demonstrating how types can depend on values and enabling "proofs as programs" through the Curry-Howard correspondence.

## Idea

Dependent Type Theory (DTT) is the idea that types can depend on values. This enable us to rstablish precise relationships between data and the logical propositions that describes it.

In traditional programming languages, types classify values. Int describes integers, Bool describes True or False, etc... With dependent type theory, a type itself depends on a value. For example, instead of defining a single “array” type, we define array n A, meaning “an array of length n whose elements are of type A.” This makes certain properties, like the dimension of an array, part of the type system itself. The compiler can then verify these constraints automatically.

This expressiveness blurs the boundary between proofs and programs. In dependent type theory, writing a function that computes something often simultaneously constructs a proof of its correctness. For instance, a function that returns the sum of two natural numbers can be defined alongside a proof that addition is associative or commutative, proofs that Lean, Coq, or Agda can check mechanically.


## Basic Theory

## Tool

## Introductory Examples

## The landscape of Tools

## Algorithms

## Benchmarks and Competitions

## Applications in Industry

In recent years, formally grounded methods for specifying and verifying software and hardware systems have undergone significant uptake. The combination of dependable "symbolic" reasoning, (i.e. logic, type-theory, theorem-proving, etc...) with the explosion of AI-driven development like machine learning, generative models, is opening up new directions for improvements. Here are briefs summaries of recent influential applications.

### 1. Historical and Influencial Application

- Tokeneer ID Station (NSA smart-card project) is one of the early industrial successes of the "Correctness by Construction" methodology. The case is described by Janet Barnes in [“Experiences in the Industrial use of Formal Methods.”](https://eceasst.org/index.php/eceasst/article/view/1885). This article reports on industrial deployment of formal methods under the “Correctness by Construction (CbyC)” approach at Altran Praxis, including the case of the Tokeneer ID Station project for the US NSA. The work describes how formal specification in Z, refinement to code in SPARK with proof of absence of run-time errors, and proof of system-level properties were applied. The project found only five errors post-release and is cited as a rare “success story” of formal methods in industry. The article also candidly discusses challenges: training, tool usability, industrial adoption, and scaling.

- [“Symbolic QED Pre-silicon Verification for Automotive Microcontroller Cores: Industrial Case Study”](https://arxiv.org/abs/1902.01494) presents an industrial case study applying the “Symbolic Quick Error Detection (Symbolic QED)” technique in the pre-silicon verification of automotive microcontroller cores (~1,800 flip-flops, ~70,000 logic gates). Symbolic QED detected all logic bugs found by previous industrial verification flows, plus additional ones. It significantly reduced verification effort (e.g., an 8× reduction for a new design, and up to ~60× for subsequent designs). Runtime of bug detection improved dramatically (20 seconds or less) with short counterexamples (≤10 instructions).

- [“Formal methods in dependable systems engineering: a survey of professionals from Europe and North America"](https://link.springer.com/article/10.1007/s10664-020-09836-5) presents survey results from mission-critical software engineering practitioners, investigating how they use formal methods, their intentions to use them, and perceived challenges. Intrinsic motivation drives use more than regulation. Experienced practitioners plan to use more extensively. Major obstacles remain such as: scalability, skills, education, process compatibility, tool reputation. The survey highlights that despite promising case studies, broad industrial adoption remains constrained.

- [“Industrial-Strength Verification of Solid State Interlocking Programs”](https://arxiv.org/abs/2108.10091) describes a tool used on 26 real-world interlockings and used to aument existing testing/inspection processes. It describes an end-to-end workflow that consumes engineering artefacts as produced by signalling designers, automatically encodes safety properties, runs automated theorm provers and SMT solvers, then produces diagnostics so the results are actionable.

### 2. Recent & Emerging Directions

- The paper [“Machine learning and logic: a new frontier in artificial intelligence”](https://par.nsf.gov/servlets/purl/10471546) shows how ML/AI and formal methods (logic, automated reasoning) are increasingly tightly coupled. Both foundational pillars have largely developed independently, but novel and grand challenges demand their integration. The author identify three key paradigms:
    1. Using learning methods for proof-rule selection, solver heuristic and initialization.
    2. Combining inductive learning and deductive reasoning for programming-by-example, synthesis, and verification.
    3. Using solver feedback as corrective layers for ML models to improve accuracy, generalizability and trustworthiness.
They posit that this convergent direction will have major impact on future AI and verification.

- [“Application of AI to formal methods — an analysis of current trends”](https://link.springer.com/article/10.1007/s10664-025-10729-8) is a systematic mapping of how AI techniques (including generative models) are being applied to formal methods (and vice versa). It charts emerging directions such as automated invariant generation via ML, proof-assistant tactic synthesis using neural networks, and formal verification of AI/ML system themselves. The analysis highlights both promise of increased automation and reduced annotation and caution. 

- Special issue [“Formal Methods for Industrial Critical Systems”](https://link.springer.com/article/10.1007/s10009-024-00744-3) compile recent tools and experience reports from industry/critical systems. The issue contributions cover a range of domains and emphasize the needs of improving formal tools and publishing empirical experience showing how formal methods integrate with industrial processes. 

- [VeriBench: End-to-End Formal Verification Benchmark for AI Code Generation in Lean](https://openreview.net/pdf?id=rWkGFmnSNl) presents a benchmark suite called VeriBench, designed to evaluate how well large language models (LLMs) can generate complete formal verification artifacts in Lean 4. The experiments show that current frontier LLMs compile and pass only a small fraction of these tasks out of the box. It explicitly highlights how Lean 4’s dependent-type system enables encoding deep invariants. The author argues
that such benchmarks are essential to meaningful progress in automated code verification & provably correct code generation, especially as generative AI becomes more widely used in software engineering.

## Case Study

Let's formalise and verify a transformation pipline for 3-D points in world space. Let's look at a small example where we perform a rotation in place, follow by a translation (moving the point to a different coordinate).   

## History

## Formal Methods and AI

## Current Development

## Resources

- [Lean4 Installation](https://lean-lang.org/install/)

- [Lean Game Logic](https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic)

- Wadler, Philip. “Propositions as Types.” Communications of the ACM, Vol. 58, No. 12 (Dec. 2015), pp. 75-84. Available as PDF at https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf

- “Intuitionistic Type Theory (Stanford Encyclopedia of Philosophy).” Entry by (various) updated Sep. 23 2024. https://plato.stanford.edu/entries/type-theory-intuitionistic/


-Barnes, J. “Experiences in the Industrial use of Formal Methods.” ECEASST 46 (2011). https://eceasst.org/index.php/eceasst/article/view/1885 

- Singh, E. et al. “Symbolic QED Pre-silicon Verification for Automotive Microcontroller Cores: Industrial Case Study.” arXiv (2019). https://arxiv.org/abs/1902.01494


Iliasov, A. et al. “Industrial-Strength Verification of Solid State Interlocking Programs.” arXiv (2021).https://arxiv.org/abs/2108.10091

- Gleirscher, M., Marmsoler, D. “Formal methods in dependable systems engineering: a survey of professionals from Europe and North America” Empir Software Eng 25 (2020). https://doi.org/10.1007/s10664-020-09836-5
 

- Ganesh, V., Seshia, S. A., Jha, S. “Machine learning and logic: a new frontier in artificial intelligence.” Formal Methods Systems Design 60 (2022). https://doi.org/10.1007/s10703-023-00430-1

- Stock, S., Dunkelau, J., Mashkoor, A. “Application of AI to formal methods — an analysis of current trends.” Empir Software Eng (2025). https://doi.org/10.1007/s10664-025-10729-8

- Groote, J. F., Huisman, M. “Formal Methods for Industrial Critical Systems.” Int J Softw Tools Technol Transfer 26 (2024). https://doi.org/10.1007/s10009-024-00744-3

- Miranda, B., Zhou, Z., Nie, A., Obbad, E., Aniva, L., Fronsdal, K., Kirk, W., Soylu, D., Yu, A., Li, Y., & Koyejo, S. (2025). VeriBench: End-to-End formal verification benchmark for AI code generation in Lean 4. In Proceedings of the 42nd International Conference on Machine Learning, Vancouver, Canada (PMLR 267). https://openreview.net/pdf?id=rWkGFmnSNl
 

## Suggestions for Future Works
