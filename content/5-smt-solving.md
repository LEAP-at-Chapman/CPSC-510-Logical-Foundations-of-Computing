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

### A Short History & the CP/SAT/SMT Landscape

SMT grew out of the SAT revolution of the late 1990s–2000s, which itself traces back to the Davis–Putnam procedure and DPLL search (Davis & Putnam, 1960; Davis, Logemann & Loveland, 1962). SMT’s key move was to keep SAT’s conflict-driven search but delegate theory reasoning (arithmetic, arrays, bit-vectors, EUF) to specialized engines, yielding scalable checking for software/hardware constraints (Barrett & Tinelli, 2018). In parallel, Constraint Programming (CP) developed rich global constraints and propagation; the two communities cross-pollinate today, as CP often uses SAT/SMT back ends, while SMT borrows CP-style modeling tricks (Hooker, 2006). Community infrastructure (the SMT-LIB language and SMT-COMP benchmark competition) standardized formats and drove rapid solver progress (Barrett, Stump & Tinelli, 2010; Barrett, Stump & Tinelli, 2005).

### How Modern SMT Solvers Work (DPLL(T) in Practice)
Most production SMT solvers implement DPLL(T): a SAT solver maintains a Boolean abstraction of the formula while theory solvers (T) check and explain conflicts; conflicts become learned clauses, powering the next SAT decisions (Nieuwenhuis, Oliveras & Tinelli, 2006). When a formula spans multiple theories, Nelson–Oppen combines disjoint, stably-infinite theories by exchanging equalities between them (Nelson & Oppen, 1979); Shostak’s method offers an alternative for certain signatures (Shostak, 1984). Z3’s architecture exemplifies this integration, adding practical engines for arithmetic (including BV/FP), arrays, and quantifiers with techniques such as E-matching and model-based quantifier instantiation (de Moura & Bjørner, 2008; Ge & de Moura, 2009). In short: CDCL for Boolean search, theory solvers for domain facts, and careful combination glue the system together.

### Optimization Modulo Theories (Max-SMT & OMT)
Beyond yes/no, many real problems want the best model—fewest violated preferences, minimum cost, maximum slack. Max-SMT treats selected clauses as soft with weights; the solver finds a model minimizing total penalty (Marques-Silva, Planes & Kutz, 2008). Optimization Modulo Theories (OMT) generalizes this to numeric objectives over theory variables (e.g., LRA/LIA), enabling lexicographic or Pareto multi-objective search (Sebastiani & Tomasi, 2015). Z3 exposes both patterns (add_soft, Optimize), which is exactly what your diet planner case study demonstrates—hard feasibility + soft calorie window + multi-objective macro fit/variety/cost.

### Practical Limits & Modeling Pitfalls (and How to Avoid Them)
SMT shines on quantifier-free linear arithmetic, bit-vectors, arrays, and EUF; performance can degrade with nonlinear integer arithmetic (undecidable in general) or heavy quantifiers (Barrett & Tinelli, 2018). Decidability lines are sharp: Presburger arithmetic is decidable, Diophantine (NIA) is not (Matiyasevich, 1970), while real closed fields are decidable but costly in practice despite Tarski’s elimination (Tarski, 1951). Modeling tips: (i) pick the right theory (bit-vectors for word-level hardware; LRA/LIA for scheduling), (ii) add bounds and symmetry breaking, (iii) encode choices as soft when possible (Max-SMT/OMT), and (iv) prefer arrays+EUF over ad-hoc encodings when modeling memory (de Moura & Bjørner, 2008; Barrett & Tinelli, 2018).

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

Interactive Z3 examples are available below via Colab or Binder or download a copy [here](https://github.com/LEAP-at-Chapman/CPSC-510-Logical-Foundations-of-Computing/blob/main/notebooks/z3/z3-examples.ipynb).

**Try it interactively:** 

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/LEAP-at-Chapman/CPSC-510-Logical-Foundations-of-Computing/blob/main/notebooks/z3/z3-examples.ipynb) 

[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/LEAP-at-Chapman/CPSC-510-Logical-Foundations-of-Computing/main?filepath=notebooks/z3/z3-examples.ipynb) 

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
    progress in ML-for-theorem-proving. (Yang et al., 2023)
    A 2025 survey reviews how LLMs help author formal specifications from natural-language requirements (Dafny/C/Java), with promising accuracy on assertion synthesis and “assertion completion” (Beg, O’Donoghue & Monahan, 2025).
    

  **2. Neuro-symbolic invariant synthesis for verification**
    Fresh results show LLMs can propose loop invariants that an SMT-based checker validates/refines (e.g., ASE’24 neuro-symbolic bounded model checking; 2025 benchmark studies). The emerging 
    recipe: LLM proposes → SMT/solver checks → counterexample-guided repair. (Wu et al., 2024; Pirzada et al., 2024; Wei et al., 2025).

  **3. Hybrid validation pipelines in compilers and systems**
    For LLVM, LLMs triage “hard” optimizations while Alive2 (SMT) proves the rest, using fuzzing to chase suspected unsound cases—concrete neuro-symbolic workflows shipping into compiler 
    validation. Expect similar “LLM-first, SMT-confirm” loops in optimizers, static analyzers, and decompilers. (Wang & Xie, 2024; Lopes et al., 2021).

  **4. Formal analysis of AI systems themselves**
    Neural-network verification continues to integrate SMT with domain-specific relaxations and bound-propagation; Marabou 2.0 documents architecture and roles for solver-in-the-loop bound 
    tightening. Coupled with LLM systems, this points to spec-driven safety cases for perception and policy components. (Wu et al., 2024; Katz et al., 2019).

  **5. Research directions to watch**
    - Auto-formalization: LLMs converting NL requirements/tests into templates that SMT tools check (assertion mining and refinement).
    - Proof-search copilots: Retrieval + tool APIs (Lean/Isabelle/Coq) to keep LLM steps sound via solver or kernel checks.
    - Verifier-in-the-loop tooling: LLM planning; SMT establishes truth; counterexamples feed self-repair—already prototyped in compilers and invariant synthesis (Beg, O’Donoghue & Monahan, 2025; Yang et al., 2023; Wu et al., 2024).

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

### Potential Possibilities with Z3: Running Z3 in the Browser (No Server) as a Puzzle Solver

You can run Z3 entirely client-side via WebAssembly and the official TypeScript/JavaScript bindings published as z3-solver. This gives you a self-contained puzzle solver (e.g., Sudoku, Kakuro, cryptarithms) that ships as a static page—no backend required. The Z3 team’s Online Z3 Guide shows working JS examples (including Sudoku) and links to the npm package; the Z3 repository also documents the WebAssembly build.

#### Two ways to ship it statically
1. Official JS/TS bindings (z3-solver) – The npm package bundles a WebAssembly build of Z3 and an ergonomic JS API (Context, Solver, Int, Bool, etc.). Modern browsers load the .wasm and run Z3 locally. For maximum performance, the package uses WebAssembly threads, which require cross-origin isolation (serve with COOP/COEP headers); several static hosts let you set these headers (z3-solver maintainers, 2025; Easton, 2024).
2. Community “z3.wasm” builds – Prior to z3-solver, community builds compiled Z3 to one .wasm with a small JS shim. They’re handy for experiments or minimal demos (Claudel, 2018–2024; Zucker, 2021).

#### Minimal “static page” example (cryptarithm)
The Online Z3 Guide provides browser examples (including Sudoku) you can adapt: load Z3, build expressions (Int.const, Distinct, arithmetic/bit-vector ops), add constraints, then check() and read a model (Z3Prover Team, 2025).This example solves the classic SEND + MORE = MONEY puzzle in a single HTML file. You can drop it into a static host. If your host supports custom headers, enable COOP/COEP  for best performance.

    <!DOCTYPE html>
    <html>
    <head>
      <meta charset="utf-8" />
      <title>Z3 in the Browser — SEND+MORE=MONEY</title>
      <!-- If your static host lets you set headers, add:
           Cross-Origin-Opener-Policy: same-origin
           Cross-Origin-Embedder-Policy: require-corp
           (These are response headers; some hosts let you configure them in a _headers file.) -->
      <style>
        body { font-family: system-ui, sans-serif; max-width: 720px; margin: 2rem auto; }
        pre { background: #f6f6f6; padding: 1rem; border-radius: 8px; overflow:auto; }
        button { padding: 0.6rem 1rem; border-radius: 8px; border: 1px solid #ccc; }
      </style>
    </head>
    <body>
      <h1>Z3 in the Browser — SEND + MORE = MONEY</h1>
      <p>Click run to solve the cryptarithm using Z3 compiled to WebAssembly.</p>
      <button id="run">Run solver</button>
      <pre id="out">(waiting)</pre>
    
      <script type="module">
        // Load the official JS bindings + WASM from a CDN.
        // Pin a version that exists for your chapter; 4.12+ is fine. Example below uses 4.15.1 per Z3Guide footer.
        import initZ3 from "https://cdn.jsdelivr.net/npm/z3-solver@4.15.1/dist/index.js";
    
        const out = document.getElementById('out');
        const log = (...xs) => out.textContent += xs.join(' ') + "\n";
    
        document.getElementById('run').addEventListener('click', async () => {
          out.textContent = "Loading Z3.wasm…\n";
          const { Context } = await initZ3();              // boots wasm + returns constructors
          const { Z3, Bool, Int, Solver, Distinct, And } = new Context("main");
    
          // Digits: S,E,N,D,M,O,R,Y are 0..9; S and M nonzero; all distinct
          const [S,E,N,D,M,O,R,Y] = "S,E,N,D,M,O,R,Y".split(",").map(n => Int.const(n));
          const digits = [S,E,N,D,M,O,R,Y];
          const zeroToNine = digits.map(d => d.ge(Int.val(0))).concat(digits.map(d => d.le(Int.val(9))));
          const nonZero    = [ S.ge(Int.val(1)), M.ge(Int.val(1)) ];
    
          // Helper: form a number from digits
          const num = (a,b,c,d) =>
            Int.val(1000).mul(a).add(Int.val(100).mul(b)).add(Int.val(10).mul(c)).add(d);
          const num5 = (a,b,c,d,e) =>
            Int.val(10000).mul(a).add(Int.val(1000).mul(b)).add(Int.val(100).mul(c)).add(Int.val(10).mul(d)).add(e);
    
          // SEND + MORE = MONEY
          const SEND  = num(S,E,N,D);
          const MORE  = num(M,O,R,E);
          const MONEY = num5(M,O,N,E,Y);
    
          const s = new Solver();
          s.add(And(...zeroToNine));
          s.add(And(...nonZero));
          s.add(Distinct(...digits));
          s.add(SEND.add(MORE).eq(MONEY));
    
          const r = await s.check();
          if (r === "sat") {
            const m = s.model();
            log("sat");
            log("Assignment:");
            for (const v of digits) log(`${v}:`, m.get(v).toString());
            log(`SEND  = ${m.eval(SEND).toString()}`);
            log(`MORE  = ${m.eval(MORE).toString()}`);
            log(`MONEY = ${m.eval(MONEY).toString()}`);
          } else {
            log(r);
          }
        });
      </script>
    </body>
    </html>

Here the z3-solver package ships a WebAssembly build of Z3 and TypeScript/JS bindings; browsers fetch the .wasm and run the solver locally. The JS API mirrors the standard Z3 concepts (contexts, solvers, sorts, expressions), and the Z3 Guide includes more examples (arrays, bit-vectors, Sudoku).The official Z3 JavaScript page also includes a Sudoku demo you can study and adapt to your other puzzles; it’s a concise template for finite-domain modeling in the browser.

###### How to use this
1. create a file named z3-puzzle.html and paste the above code
2. open it from a local server (or any static host)
3. click Run solver
4. (optional) if your host supports headers, add Cross-Origin-Opener-Policy: same-origin and Cross-Origin-Embedder-Policy: require-corp to enable WASM threads


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
- Barrett and Tinelli [Satisfiability Modulo Theories, Handbook of Model Checking](https://link.springer.com/chapter/10.1007/978-3-319-10575-8_11) (2018). 
- Barrett, Stump and Tinelli The SMT-LIB Standard: Version 2.0, SMT-LIB (2010).
- Davis and Putnam [A Computing Procedure for Quantification Theory](https://dl.acm.org/doi/abs/10.1145/321033.321034), Journal of the ACM (1960).
- Davis, Logemann and Loveland (1962) [A Machine Program for Theorem-Proving](https://dl.acm.org/doi/abs/10.1145/368273.368557),  Communications of the ACM(1962).
- de Moura and Bjørner [Z3: An Efficient SMT Solver](https://link.springer.com/chapter/10.1007/978-3-540-78800-3_24), TACAS(2008).
- Ge and de Moura [Complete Instantiation for Quantified Formulas in SMT](https://link.springer.com/chapter/10.1007/978-3-642-02658-4_25), CAV (2009).
- Hooker [Integrated Methods for Optimization](https://link.springer.com/chapter/10.1007/978-0-387-38274-6_4), Springer (2006).
- Nelson and Oppen [Simplification by Cooperating Decision Procedures](https://dl.acm.org/doi/abs/10.1145/357073.357079), ACM TOPLAS (1979).
- Nieuwenhuis, Oliveras and Tinelli [Solving SAT and SAT Modulo Theories: From an Abstract DPLL Procedure to DPLL(T)](https://dl.acm.org/doi/abs/10.1145/1217856.1217859), Journal of the ACM (2006).
- Sebastiani and Tomasi [Optimization Modulo Theories with Linear Rational/Integer Arithmetic](https://dl.acm.org/doi/abs/10.1145/2699915), ACM Transactions on Computational Logic (2015).
- Shostak (1984) [Deciding Combinations of Theories](https://dl.acm.org/doi/pdf/10.1145/2422.322411), Journal of the ACM (1984).
- Z3Prover Team (2025) [Z3 JavaScript Examples](https://microsoft.github.io/z3guide/programming/Z3%20JavaScript%20Examples), Online Z3 Guide (2025).
- Z3Prover [Z3 repository: WebAssembly / TypeScript notes](https://github.com/Z3Prover/z3), GitHub (see “WebAssembly / TypeScript / JavaScript”) (2025).
- z3-solver [TypeScript/JavaScript bindings](https://www.npmjs.com/package/z3-solver)_ (WebAssembly), npm package page (2025).
- Easton [z3-solver & WebAssembly notes](https://fletcheaston.com/software/packages/z3-solver), Blog (2024).
- Claudel (maintainer) [z3.wasm: WASM builds of Z3](https://github.com/cpitclaudel/z3.wasm), GitHub (alternative build route) (2019–2024).
- Zucker [Replicating Rise4Fun Z3 with z3-wasm](https://www.philipzucker.com/replacing-rise4fun/), Blog & demo (2021).
