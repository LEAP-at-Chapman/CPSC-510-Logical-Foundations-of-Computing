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


## Introductory Example: Array Bounds Checking

```python
from z3 import *

# Problem: Is array access A[i] safe when i comes from user input?
def verify_array_access(array_size, user_input):
    i = Int('i')
    s = Solver()
    
    # User input constraint
    s.add(i = user_input)
    
    # Array bounds check
    s.add(0 <= i)           # Lower bound
    s.add(i < array_size)   # Upper bound
    
    # Check if bounds can be violated
    s.add(Not(And(0 <= i, i < array_size)))
    
    if s.check() == unsat:
        print("Array access is safe!")
    else:
        print("Array access may be unsafe!")
        print("Counterexample:", s.model())

# Example usage
verify_array_access(10, 5)  # Safe
verify_array_access(10, 15) # Unsafe!
```

Arrays bounds checking is decidable because we are using linear arithmetic theory plus uninterpreted functions, not general first-order logic.

## References

- [Reuben Martins](https://sat-group.github.io/ruben/) (part of a course on [Bug Catching: Bug Catching: Automated Program Verification](https://www.cs.cmu.edu/~15414/s22/s21/lectures/) )
  - [Lecture Notes on SMT Solving](https://www.cs.cmu.edu/~15414/s22/s21/lectures/16-smt.pdf)
  - [Lecture Notes on SMT Theories](https://www.cs.cmu.edu/~15414/s21/lectures/17-smt-theories.pdf)
  - [Lecture Notes on SMT Encodings](https://www.cs.cmu.edu/~15414/s21/lectures/18-smt-encodings.pdf)
  - [Lecture Notes on DPLL(T) & SMT Encodings](https://www.cs.cmu.edu/~15414/s24/lectures/19-smt-encodings.pdf)
  - [Lecture Notes on SMT Solving: Nelson-Oppen](https://www.cs.cmu.edu/~15414/s24/lectures/18-smt-solving.pdf)
- Howe, J. M., & King, A. (2012). [A pearl on SAT and SMT solving in Prolog](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=A+Pearl+on+SAT+and+SMT+Solving+in+Prolog&btnG=). Theoretical Computer Science, 435, 43-55. [pdf](https://www.staff.city.ac.uk/~jacob/solver/tcs.pdf) - - - I only read the intro and do not claim that I understand that paper. It is of interest to our class because it combines ideas from SAT, Prolog and SMT.

# Appendix: Links to Explore

(LLM generated)

## Further References

### Theories in SMT
SMT solvers work with various **decidable theories** such as:
- **Linear arithmetic** (integers/reals) - [Google Scholar: "SMT linear arithmetic"](https://scholar.google.com/scholar?q=%22SMT%22+%22linear+arithmetic%22)
- **Bit-vectors** - [Google Scholar: "SMT bit vector theory"](https://scholar.google.com/scholar?q=%22SMT%22+%22bit+vector%22+theory)
- **Arrays** - [Google Scholar: "SMT array theory"](https://scholar.google.com/scholar?q=%22SMT%22+%22array+theory%22+satisfiability)
- **Uninterpreted functions** - [Google Scholar: "SMT uninterpreted functions"](https://scholar.google.com/scholar?q=%22SMT%22+%22uninterpreted+functions%22)
- **Strings** - [Google Scholar: "SMT string theory"](https://scholar.google.com/scholar?q=%22SMT%22+%22string+theory%22+solver)

### DPLL(T) Architecture
Most modern SMT solvers use the **DPLL(T)** architecture, which combines:
- A **SAT solver** for Boolean reasoning
- **Theory solvers** for domain-specific reasoning
- [Google Scholar: "DPLL(T) SMT"](https://scholar.google.com/scholar?q=%22DPLL%28T%29%22+SMT)

## Z3 Theorem Prover

**Z3** is a high-performance SMT solver developed at Microsoft Research by Leonardo de Moura and Nikolaj Bjørner. Key features:

### Architecture & Algorithms
- Implements DPLL(T) with advanced optimizations
- **Conflict-driven clause learning** (CDCL)
- **Theory combination** via Nelson-Oppen framework
- [Google Scholar: "Z3 theorem prover"](https://scholar.google.com/scholar?q=%22Z3+theorem+prover%22)

### Key Innovations
- **E-matching** for quantifier instantiation
- **Model-based quantifier instantiation (MBQI)**
- **Efficient theory solvers** for arithmetic, bit-vectors, arrays
- [Google Scholar: "Z3 quantifier instantiation"](https://scholar.google.com/scholar?q=%22Z3%22+%22quantifier+instantiation%22)

## Applications

### Software Verification
- **Symbolic execution** - [Google Scholar: "SMT symbolic execution"](https://scholar.google.com/scholar?q=%22SMT%22+%22symbolic+execution%22)
- **Program verification** - [Google Scholar: "SMT program verification"](https://scholar.google.com/scholar?q=%22SMT%22+%22program+verification%22)
- **Static analysis** - [Google Scholar: "SMT static analysis"](https://scholar.google.com/scholar?q=%22SMT+solver%22+%22static+analysis%22)

### Hardware Verification
- **Bounded model checking** - [Google Scholar: "SMT bounded model checking"](https://scholar.google.com/scholar?q=%22SMT%22+%22bounded+model+checking%22)
- **Equivalence checking**
- **Property verification**

### Security & Cryptography
- **Protocol verification** - [Google Scholar: "SMT protocol verification"](https://scholar.google.com/scholar?q=%22SMT%22+%22protocol+verification%22)
- **Side-channel analysis**
- **Cryptographic analysis**

## Important Research Areas

### Performance & Scalability
- **Incremental solving** - [Google Scholar: "incremental SMT solving"](https://scholar.google.com/scholar?q=%22incremental%22+%22SMT+solving%22)
- **Parallel SMT solving** - [Google Scholar: "parallel SMT solving"](https://scholar.google.com/scholar?q=%22parallel%22+%22SMT+solving%22)
- **SMT competition results** - [Google Scholar: "SMT-COMP competition"](https://scholar.google.com/scholar?q=%22SMT-COMP%22+competition)

### Theory Development
- **Combination of theories** - [Google Scholar: "Nelson-Oppen SMT"](https://scholar.google.com/scholar?q=%22Nelson-Oppen%22+SMT)
- **Quantifier handling** - [Google Scholar: "SMT quantifier reasoning"](https://scholar.google.com/scholar?q=%22SMT%22+%22quantifier+reasoning%22)
- **Non-linear arithmetic** - [Google Scholar: "SMT non-linear arithmetic"](https://scholar.google.com/scholar?q=%22SMT%22+%22non-linear+arithmetic%22)

## Foundational Papers & Resources

### Seminal Works
- **Original DPLL(T) paper** - [Google Scholar: "Nieuwenhuis Oliveras Tinelli DPLL(T)"](https://scholar.google.com/scholar?q=Nieuwenhuis+Oliveras+Tinelli+%22DPLL%28T%29%22)
- **Z3 system description** - [Google Scholar: "de Moura Bjorner Z3"](https://scholar.google.com/scholar?q=%22de+Moura%22+%22Bjorner%22+%22Z3%22)

### Survey Papers
- [Google Scholar: "SMT solving survey"](https://scholar.google.com/scholar?q=%22SMT+solving%22+survey)
- [Google Scholar: "satisfiability modulo theories survey"](https://scholar.google.com/scholar?q=%22satisfiability+modulo+theories%22+survey)

## Getting Started

## Resources for Further Learning

- **Z3 Online Tutorial**: https://rise4fun.com/z3/tutorial
- **Z3 Python API**: https://z3prover.github.io/api/html/python/z3.html
- **SMT-LIB**: Standard format for SMT problems
- **Competitions**: SMT-COMP (annual SMT solver competition)

## Next Steps

1. Install Z3 and try the examples above
2. Experiment with different theories (arrays, bit-vectors)
3. Try solving some verification problems
4. Explore Z3's quantifier reasoning capabilities

# Appendix: SMT vs Constraint Programming

(LLM generated)

**Key Differences:**
- **SMT**: Focuses on **satisfiability** (finding any solution) using **theory combination**
- **CP**: Focuses on **optimization** (finding best solution) using **constraint propagation**

**SMT Strengths:**
- Excellent for **verification** (proving properties hold)
- Handles **infinite domains** (integers, reals)
- Strong **theory combination** (mixing different mathematical theories)
- Used in **software/hardware verification**

**CP Strengths:**
- Excellent for **optimization problems** (scheduling, planning)
- Handles **finite domains** efficiently
- Rich **global constraints** (all_different, cumulative)
- Used in **operations research**

**When to use which:**
- Use **SMT** for: program verification, model checking, theorem proving
- Use **CP** for: scheduling, resource allocation, puzzle solving, optimization

## MiniZinc vs Z3: A Direct Comparison

| Aspect | MiniZinc | Z3 |
|--------|----------|-----|
| **Language** | Declarative modeling language | API-based (Python, C++, etc.) |
| **Syntax** | High-level, readable constraints | Low-level, programmatic |
| **Example** | `constraint x + y = 10;` | `s.add(x + y == 10)` |
| **Domains** | Finite domains (1..9, {red,blue}) | Infinite domains (integers, reals) |
| **Constraints** | Global constraints (`all_different`) | Theory-specific constraints |
| **Optimization** | Built-in (`solve minimize cost;`) | Manual (iterative solving) |
| **Output** | Formatted solutions | Programmatic model access |
| **Learning Curve** | Easy for beginners | Requires programming knowledge |

### MiniZinc Example (Sudoku):
```
array[1..9, 1..9] of var 1..9: grid;
constraint forall(i in 1..9) (all_different([grid[i,j] | j in 1..9]));
solve satisfy;
```

### Z3 Example (Same Problem):
```python
from z3 import *
grid = [[Int(f"x_{i}_{j}") for j in range(9)] for i in range(9)]
s = Solver()
for i in range(9):
    s.add(Distinct([grid[i][j] for j in range(9)]))
```

**Choose MiniZinc when:** You want to quickly model optimization problems with finite domains
**Choose Z3 when:** You need program verification, infinite domains, or integration with other code

## Under the Hood: Common Backend Architecture

You're absolutely correct! Both MiniZinc and Z3 are **frontend interfaces** that compile to backend solvers, and they share deep algorithmic roots:

### Shared Backend Solvers
- **MiniZinc** → FlatZinc → Gecode, Chuffed, OR-Tools, CPLEX, **Z3**, etc.
- **Z3** → Internal SMT solver (which includes a SAT core + theory solvers)

### Common Algorithmic Heritage
Both ultimately trace back to **Davis-Putnam**:
- **MiniZinc/CP**: Davis-Putnam + **constraint propagation** + **global constraints**
- **Z3/SMT**: Davis-Putnam + **theory combination** + **conflict-driven clause learning**

### The Real Differences
The differences aren't in the underlying algorithms, but in:

1. **Problem Modeling Philosophy:**
   - **MiniZinc**: Declarative constraint modeling (like Prolog)
   - **Z3**: Programmatic theorem proving (like formal verification)

2. **Target Applications:**
   - **MiniZinc**: Operations research, optimization, scheduling
   - **Z3**: Software verification, model checking, theorem proving

3. **Theory Integration:**
   - **MiniZinc**: Finite domain constraints, global constraints
   - **Z3**: Infinite theories (arithmetic, arrays, bit-vectors)

### Convergence in Practice
Modern systems are converging:
- **MiniZinc** can call **Z3** as a backend solver
- **Z3** can solve many constraint programming problems
- Both use similar **DPLL(T)** architectures under the hood

So you're right - the fundamental algorithmic differences are minimal. The choice often comes down to **modeling style** and **application domain** rather than solver capabilities.

## The Social Divide: Why Two Communities?

You're absolutely right to notice this! The SMT vs CP divide is largely a **historical accident** and **social phenomenon**:

### Historical Origins
- **CP Community**: Emerged from **Operations Research** (1980s-90s)
  - Focus: Scheduling, resource allocation, optimization
  - Venues: CP conference, OR journals, industry applications
  - Culture: Practical problem-solving, efficiency metrics

- **SMT Community**: Emerged from **Formal Methods** (2000s)
  - Focus: Program verification, theorem proving, model checking
  - Venues: CAV, TACAS, formal methods conferences
  - Culture: Theoretical foundations, correctness guarantees

### The Artificial Divide
Both communities essentially solve the same problem: **"Find values that satisfy constraints"**

**What they share:**
- DPLL(T) algorithmic foundations
- Constraint satisfaction core
- Similar solver architectures
- Overlapping problem domains

**What separates them:**
- **Different conferences** (CP vs CAV/TACAS)
- **Different terminology** ("constraints" vs "theories")
- **Different benchmarks** (MiniZinc vs SMT-LIB)
- **Different cultures** (optimization vs verification)



