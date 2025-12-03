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

## Case Study Code: Diet Planner

    # diet_planner.py
    # Z3 calorie & macro planner 
    # Hard constraints: nonnegative servings, availability bounds
    # Soft/Optimization: hit calorie + macro targets (L1 deviation)
    # Units are 1/2 servings 

    import argparse
    from typing import Dict, Tuple, Set
    from z3 import *
    
    # CONFIG
    # Per serving: (Protein g, Carbs g, Fat g, Cost, MaxServings, Vegetarian?)
    FOODS: Dict[str, Tuple[int, int, int, float, int, bool]] = {
        "Bread":     (7,  25,  1, 0.4, 6,  True),
        "Rice":      (4,  45,  0, 0.3, 6,  True),
        "Pasta":     (7,  42,  1, 0.4, 6,  True),
        "Oats":      (6,  27,  3, 0.5, 6,  True),
        "Chicken":   (31, 0,   3, 1.8, 6,  False),
        "Beef":      (26, 0,  15, 2.0, 4,  False),
        "Tofu":      (18, 5,   6, 0.8, 6,  True),
        "Eggs":      (12, 1,  10, 0.6, 6,  True),
        "Beans":     (9,  27,  1, 0.4, 6,  True),
        "GreekYog":  (17, 6,   0, 0.9, 6,  True),   #Greek Yogurt
        "Milk":      (8,  12,  5, 0.5, 6,  True),
        "PB":        (8,  6,  16, 0.5, 4,  True),   # Peanut Butter
        "OliveOil":  (0,  0,  14, 0.7, 6,  True),
        "Avocado":   (3,  9,  15, 1.0, 4,  True),
    }
    MEATY = [name for name, (*_, veg) in FOODS.items() if not veg]
    
    def parse_args() -> argparse.Namespace:
        ap = argparse.ArgumentParser(description="Z3 Diet Planner / Calorie Counter")
        ap.add_argument("--calories", type=int, default=2200, help="Target kcal")
        ap.add_argument("--protein",  type=int, default=140,  help="Target protein grams")
        ap.add_argument("--carbs",    type=int, default=230,  help="Target carbohydrate grams")
        ap.add_argument("--fat",      type=int, default=70,   help="Target fat grams")
        ap.add_argument("--cal-tol",  type=int, default=75,   help="±kcal window (soft unless --hard-calories)")
        ap.add_argument("--unit",     type=float, default=0.5, help="serving granularity (e.g., 0.5 = half-serving)")
        ap.add_argument("--vegetarian", action="store_true", help="disallow meat items")
        ap.add_argument("--exclude",  type=str, default="", help="comma-separated foods to exclude")
        ap.add_argument("--include-only", type=str, default="", help="comma-separated list; only these allowed")
        ap.add_argument("--pareto", action="store_true", help="use Pareto priority among objectives")
        ap.add_argument("--hard-calories", action="store_true", help="enforce calorie window as hard constraint")
        return ap.parse_args()
    
    def select_allowed_foods(args: argparse.Namespace) -> Set[str]:
        allowed = set(FOODS.keys())
        if args.vegetarian:
            allowed -= set(MEATY)
        if args.exclude:
            allowed -= {f.strip() for f in args.exclude.split(",") if f.strip()}
        if args.include_only:
            allowed = {f.strip() for f in args.include_only.split(",") if f.strip()}
        if not allowed:
            raise SystemExit("No foods remain after filtering; relax filters or lists.")
        return allowed
    
    def R(x: float) -> ArithRef:
        """Safe RealVal from float/string for exact Z3 arithmetic."""
        return RealVal(str(x))
    
    
    # Z3 MODEL
    
    
    class ModelParts:
        """Container to pass around Z3 pieces."""
        def __init__(self):
            self.opt: Optimize = None
            self.x: Dict[str, IntNumRef] = {}
            self.y: Dict[str, IntNumRef] = {}
            self.totP: ArithRef = None
            self.totC: ArithRef = None
            self.totF: ArithRef = None
            self.cal: ArithRef  = None
            self.total_cost: ArithRef = None
            self.in_window: BoolRef = None
    
    def build_model(args: argparse.Namespace, allowed: Set[str]) -> ModelParts:
        mp = ModelParts()
        mp.opt = Optimize()
        if args.pareto:
            mp.opt.set(priority='pareto')

    # Decision variables: integer counts in units of `unit` servings
    unit = args.unit
    mp.x = {f: Int(f"x_{f}") for f in allowed}      # quantity in units
    mp.y = {f: Int(f"use_{f}") for f in allowed}    # 0/1 usage indicator
    BIG_M = 1000

    # Hard constraints: bounds and linking x -> y
    for f in allowed:
        P, C, F, cost, max_serv, veg = FOODS[f]
        max_units = int(round(max_serv / unit))
        mp.opt.add(mp.x[f] >= 0, mp.x[f] <= max_units)
        mp.opt.add(mp.y[f] >= 0, mp.y[f] <= 1)
        mp.opt.add(mp.x[f] <= mp.y[f] * BIG_M)

    # Totals and cost
    mp.totP = Sum([mp.x[f] * R(FOODS[f][0] * unit) for f in allowed])
    mp.totC = Sum([mp.x[f] * R(FOODS[f][1] * unit) for f in allowed])
    mp.totF = Sum([mp.x[f] * R(FOODS[f][2] * unit) for f in allowed])
    mp.total_cost = Sum([mp.x[f] * R(FOODS[f][3] * unit) for f in allowed])

    # Calories from macros (exact by definition)
    mp.cal = 4*mp.totP + 4*mp.totC + 9*mp.totF

    # Calorie window
    mp.in_window = And(mp.cal >= R(args.calories - args.cal_tol),
                       mp.cal <= R(args.calories + args.cal_tol))
    return mp


    # DEVIATIONS (L1 absolute deviations for targets)
    
    
    def add_abs_deviation(opt: Optimize, expr: ArithRef, target: float, tag: str) -> ArithRef:
        """Encodes |expr - target| via pos/neg slack: expr - target = pos - neg, pos,neg >= 0"""
        pos = Real(f"{tag}_pos")
        neg = Real(f"{tag}_neg")
        opt.add(pos >= 0, neg >= 0, expr - R(target) == pos - neg)
        return pos + neg
    
    # 4) OBJECTIVES

    class SolveResult:
        def __init__(self, model: ModelRef, mp: ModelParts, allowed: Set[str], unit: float, args: argparse.Namespace):
            self.m = model
            self.mp = mp
            self.allowed = allowed
            self.unit = unit
            self.args = args
    
    def add_objectives_and_solve(args: argparse.Namespace, mp: ModelParts, allowed: Set[str]) -> SolveResult:
        # Primary: minimize macro & calorie deviations
        W_CAL, W_PRO, W_CAR, W_FAT = 1.0, 2.0, 1.0, 1.0
        dev_cal = add_abs_deviation(mp.opt, mp.cal,  args.calories, "cal")
        dev_pro = add_abs_deviation(mp.opt, mp.totP, args.protein,  "pro")
        dev_car = add_abs_deviation(mp.opt, mp.totC, args.carbs,    "car")
        dev_fat = add_abs_deviation(mp.opt, mp.totF, args.fat,      "fat")
        primary_loss = W_CAL*dev_cal + W_PRO*dev_pro + W_CAR*dev_car + W_FAT*dev_fat
        h1 = mp.opt.minimize(primary_loss)

    # Secondary: maximize variety (#foods used)
    h2 = mp.opt.maximize(Sum([mp.y[f] for f in allowed]))

    # Tertiary: minimize cost
    h3 = mp.opt.minimize(mp.total_cost)

    # Calorie window: soft or hard
    if args.hard_calories:
        mp.opt.add(mp.in_window)  # hard
    else:
        mp.opt.add_soft(mp.in_window, weight=5, id_="calorie_window")  # soft

    # Solve
    res = mp.opt.check()
    if res != sat:
        raise SystemExit(f"Model returned {res}. Try relaxing bounds, filters, or tolerance.")
    return SolveResult(mp.opt.model(), mp, allowed, args.unit, args)


    # REPORTING
    
    def as_float(m: ModelRef, expr: ArithRef) -> float:
        s = m.eval(expr, model_completion=True).as_decimal(10)
        return float(s if "?" not in s else s[:s.index("?")])
    
    def report(sr: SolveResult) -> None:
        m, mp, allowed, unit, args = sr.m, sr.mp, sr.allowed, sr.unit, sr.args

    tot_p = as_float(m, mp.totP)
    tot_c = as_float(m, mp.totC)
    tot_f = as_float(m, mp.totF)
    tot_kcal = as_float(m, mp.cal)
    cost_val = as_float(m, mp.total_cost)

    print("\n=== Z3 Diet Plan (units = {:.2f} serving) ===".format(unit))
    print("Targets: {} kcal | P {} g, C {} g, F {} g (cal tol ±{})".format(
        args.calories, args.protein, args.carbs, args.fat, args.cal_tol
    ))
    print("Dietary style: {}".format("Vegetarian" if args.vegetarian else "Any"))
    if args.include_only:
        print("Include-only: {}".format(", ".join(sorted(allowed))))
    elif args.exclude:
        print("Excluded: {}".format(args.exclude))

    print("\nServings:")
    any_food = False
    for f in sorted(allowed):
        q = m.eval(mp.x[f]).as_long()
        if q > 0:
            any_food = True
            servings = q * unit
            P, C, F, cost, *_ = FOODS[f]
            print(f"  {f:<10} {servings:>4.1f}  (per serving: P{P} C{C} F{F}, cost {cost:.2f})")
    if not any_food:
        print("  (no food selected)")

    print("\nTotals:")
    print(f"  Calories : {tot_kcal:.0f} kcal (from macros: 4P + 4C + 9F)")
    print(f"  Protein  : {tot_p:.0f} g")
    print(f"  Carbs    : {tot_c:.0f} g")
    print(f"  Fat      : {tot_f:.0f} g")
    print(f"  Cost     : {cost_val:.2f}")

    print("\nDeviations (absolute):")
    print(f"  |Cal-Target| ~ {abs(tot_kcal - args.calories):.0f}")
    print(f"  |Pro-Target| ~ {abs(tot_p   - args.protein):.0f}")
    print(f"  |Car-Target| ~ {abs(tot_c   - args.carbs):.0f}")
    print(f"  |Fat-Target| ~ {abs(tot_f   - args.fat):.0f}")

    # Main
    
    def main():
        args = parse_args()
        allowed = select_allowed_foods(args)
        mp = build_model(args, allowed)
        sr = add_objectives_and_solve(args, mp, allowed)
        report(sr)
    
    if __name__ == "__main__":
        main()

    
    


## References

- [Reuben Martins](https://sat-group.github.io/ruben/) (part of a course on [Bug Catching: Bug Catching: Automated Program Verification](https://www.cs.cmu.edu/~15414/s22/s21/lectures/) )
  - [Lecture Notes on SMT Solving](https://www.cs.cmu.edu/~15414/s22/s21/lectures/16-smt.pdf)
  - [Lecture Notes on SMT Theories](https://www.cs.cmu.edu/~15414/s21/lectures/17-smt-theories.pdf)
  - [Lecture Notes on SMT Encodings](https://www.cs.cmu.edu/~15414/s21/lectures/18-smt-encodings.pdf)
  - [Lecture Notes on DPLL(T) & SMT Encodings](https://www.cs.cmu.edu/~15414/s24/lectures/19-smt-encodings.pdf)
  - [Lecture Notes on SMT Solving: Nelson-Oppen](https://www.cs.cmu.edu/~15414/s24/lectures/18-smt-solving.pdf)
- Howe, J. M., & King, A. (2012). [A pearl on SAT and SMT solving in Prolog](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=A+Pearl+on+SAT+and+SMT+Solving+in+Prolog&btnG=). Theoretical Computer Science, 435, 43-55. [pdf](https://www.staff.city.ac.uk/~jacob/solver/tcs.pdf) - - - I only read the intro and do not claim that I understand that paper. It is of interest to because it combines ideas from SAT, Prolog and SMT.
- Backes, Bolignano, Cook, et al. (2018) [Semantic-based Automated Reasoning for AWS Access Policies using SMT](https://ieeexplore.ieee.org/abstract/document/8602994)
, FMCAD.
- Rungta, N. [A Billion SMT Queries a Day](https://link.springer.com/chapter/10.1007/978-3-031-13185-1_1) Amazon Science (invited), 2022.
- Godefroid, P., Levin, M., Molnar, D. [SAGE: Whitebox Fuzzing for Security Testing](https://queue.acm.org/detail.cfm?id=2094081&ref=fullrss) CACM 2012.
- Bounimova, E., Godefroid, P., Molnar, D. [Billions and Billions of Constraints: Whitebox Fuzz Testing at Microsoft](https://ieeexplore.ieee.org/abstract/document/6606558) ICSE 2011/Tech Report.
- Wang, Y., Xie, F. [Enhancing Translation Validation of Compiler Transformations with Large Language Models](https://www.worldscientific.com/doi/abs/10.1142/S0218194024500475) arXiv:2401.16797 (2024).
- Cadar, C., Dunbar, D., Engler, D. [KLEE: Unassisted and Automatic Generation of High-Coverage Tests for Complex Systems Programs](https://www.usenix.org/legacy/event/osdi08/tech/full_papers/cadar/cadar.pdf) OSDI 2008.
- Beckett, R., et al. [A General Approach to Network Configuration Verification (Minesweeper)](https://dl.acm.org/doi/abs/10.1145/3098822.3098834) SIGCOMM 2017.
- Brown, M., et al. [Lessons from the Evolution of the Batfish Configuration Analysis Tool](https://dl.acm.org/doi/abs/10.1145/3603269.3604866) SIGCOMM 2023 (Experience).
- Prabhu, S., et al. [Plankton: Scalable Network Configuration Verification](https://www.usenix.org/conference/nsdi20/presentation/prabhu) NSDI 2020.
- Katz, G., Barrett, C., Dill, D., Julian, K., Kochenderfer, M. [Reluplex: An Efficient SMT Solver for Verifying Deep Neural Networks](https://link.springer.com/chapter/10.1007/978-3-319-63387-9_5) CAV 2017 / arXiv:1702.01135.
- Katz, G., et al. [The Marabou Framework for Verification and Analysis of Deep Neural Networks](https://link.springer.com/chapter/10.1007/978-3-031-65630-9_13) CAV 2019 / LNCS; Marabou 2.0 (2024).
- Yang, K., et al. [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models (ReProver)](https://proceedings.neurips.cc/paper_files/paper/2023/hash/4441469427094f8873d0fecb0c4e1cee-Abstract-Datasets_and_Benchmarks.html) NeurIPS 2023 (paper & dataset).
- Beg, A., et al. [A Short Survey on Formalising Software Requirements with LLMs](https://arxiv.org/abs/2506.11874) arXiv:2506.11874 (2025).
- Wu, G., et al. [LLM Meets Bounded Model Checking: Neuro-symbolic Loop Invariant Inference](https://ieeexplore.ieee.org/abstract/document/10628461) ASE 2024.
- Wei, A., et al. [InvBench: Can LLMs Accelerate Program Verification with Invariant Synthesis?](https://arxiv.org/abs/2509.21629) arXiv:2509.21629 (2025).
